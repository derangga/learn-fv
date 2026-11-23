package mutants

import (
	"fmt"
	"math/rand/v2"
	"reflect"
	"slices"
	"sort"
	"strings"
	"testing"

	"github.com/derangga/learn-formal-verification/internal/uc2/core"
)

// machine hides the state type so M4 (extra field) and the others share one checker.
type machine struct {
	name  string
	extra bool // draw the mutant-only events ReserveCheck and ReserveCommit
	init  func(skus []core.StockInit) any
	step  func(any, core.Event) (any, []core.Effect)
	proj  func(any) core.State
}

func plain(name string, f func(core.State, core.Event) (core.State, []core.Effect)) machine {
	return machine{name, false,
		func(k []core.StockInit) any { return core.Init(k) },
		func(s any, e core.Event) (any, []core.Effect) { return f(s.(core.State), e) },
		func(s any) core.State { return s.(core.State) }}
}

func m4Machine() machine {
	return machine{"M4", true,
		func(k []core.StockInit) any { return InitM4(k) },
		func(s any, e core.Event) (any, []core.Effect) { return StepM4(s.(M4State), e) },
		func(s any) core.State { return s.(M4State).State }}
}

func machines() []machine {
	return []machine{plain("core", core.Step), plain("M1", StepM1), plain("M1b", StepM1b), plain("M2", StepM2),
		plain("M3", StepM3), plain("M3b", StepM3b), m4Machine(), plain("M5", StepM5), plain("M5a", StepM5a),
		plain("M6", StepM6), plain("M7", StepM7)}
}

// checkNames is the column order of the kill matrix: P1 to P4b, A1, A2, S0 to S11
// (S2 to S7 and S0, S1, S8, S9 are core.Step comparisons by case, see pinCase),
// and the mutant-only commit pin.
var checkNames = []string{"P1", "P1b", "P2", "P3", "P3b", "P4", "P4a", "P4b", "A1", "A2",
	"S0", "S1", "S2", "S3", "S4", "S5", "S6", "S7", "S8", "S9", "S10", "S11", "M4-only"}

// section5 is the "Killed by" column of properties/UC2.md section 5, verbatim.
var section5 = map[string][]string{
	"M1":  {"P4a", "P4b", "S5"},
	"M1b": {"S6", "S7"},
	"M2":  {"P3", "A1", "S7", "S11"},
	"M3":  {"P4", "P3", "P4a", "P4b", "A1", "S5"},
	"M4":  {"P1", "P1b", "P2"},
	"M5":  {"P2", "P1b", "S3"},
	"M5a": {"P1", "P2", "P1b", "S3"},
	"M6":  {"P2", "A1", "S6"},
	"M7":  {"A2", "S3", "S11"},
}

// verdict maps a check name to its first failure message.
type verdict map[string]string

func (v verdict) fail(name, msg string) {
	if _, ok := v[name]; !ok {
		v[name] = msg
	}
}

func (v verdict) names() []string {
	var ns []string
	for k := range v {
		ns = append(ns, k)
	}
	sort.Slice(ns, func(i, j int) bool { return slices.Index(checkNames, ns[i]) < slices.Index(checkNames, ns[j]) })
	return ns
}

func kindName(k core.Kind) string {
	switch k {
	case ReserveCheck:
		return "ReserveCheck"
	case ReserveCommit:
		return "ReserveCommit"
	}
	return k.String()
}

// accepts is the S2 guard, written out independently of Step.
func accepts(s core.State, e core.Event) bool {
	k := findStock(s, e.Sku)
	return e.Qty >= 1 && e.Ttl >= 1 && k >= 0 && findRes(s, e.ID) < 0 && e.Qty <= s.Stocks[k].Available
}

// pinCase names the pin (S0 to S9) that governs event e in state s, per properties/UC2.md section 4.
func pinCase(s core.State, e core.Event) string {
	if !s.Up && e.Kind != core.Tick && e.Kind != core.Restart {
		return "S0"
	}
	ri := findRes(s, e.ID)
	switch e.Kind {
	case core.Tick:
		return "S1"
	case core.Crash:
		return "S8"
	case core.Restart:
		return "S9"
	case core.Reserve:
		if accepts(s, e) {
			return "S2"
		}
		return "S3"
	case core.Confirm:
		if ri >= 0 && s.Res[ri].Status == core.Held && !core.Due(s, s.Res[ri]) {
			return "S4"
		}
		return "S5"
	case core.Expire:
		if ri >= 0 && s.Res[ri].Status == core.Held && core.Due(s, s.Res[ri]) {
			return "S6"
		}
		return "S7"
	}
	return "M4-only"
}

// stable is S10: stocks keep identity and total, records keep id, sku, qty,
// expiresAt, order, and a Confirmed or Expired record keeps its status.
func stable(s, s2 core.State) bool {
	if len(s2.Stocks) != len(s.Stocks) || len(s2.Res) < len(s.Res) {
		return false
	}
	for i, k := range s.Stocks {
		if s2.Stocks[i].Total != k.Total || s2.Stocks[i].Sku != k.Sku {
			return false
		}
	}
	for i, r := range s.Res {
		r2 := s2.Res[i]
		if r2.ID != r.ID || r2.Sku != r.Sku || r2.Qty != r.Qty || r2.ExpiresAt != r.ExpiresAt ||
			r.Status != core.Held && r2.Status != r.Status {
			return false
		}
	}
	return true
}

func stateEq(a, b core.State) bool { return reflect.DeepEqual(a, b) }

// checkStep applies every property and pin check to one step. ms2 is the
// mutant's raw state after the step (needed for S11); all is every effect
// emitted since Init, including this step's.
func (m machine) checkStep(v verdict, ms any, e core.Event, ms2 any, fx, all []core.Effect) {
	s, s2 := m.proj(ms), m.proj(ms2)
	ev := fmt.Sprintf("%s{id=%d sku=%d qty=%d ttl=%d}", kindName(e.Kind), e.ID, e.Sku, e.Qty, e.Ttl)
	if !core.NonNegativeAvailable(s2) {
		v.fail("P1", fmt.Sprintf("after %s: %+v", ev, s2.Stocks))
	}
	if !core.NoOversell(s, e, s2, fx) {
		v.fail("P1b", fmt.Sprintf("%s: stock taken without an accepted Reserve: %+v -> %+v", ev, s.Stocks, s2.Stocks))
	}
	if !core.Conservation(s2) {
		v.fail("P2", fmt.Sprintf("after %s: %+v", ev, s2.Stocks))
	}
	if !core.ExpiredReturnedOnce(s2) {
		v.fail("P3", fmt.Sprintf("after %s: %+v", ev, s2.Res))
	}
	if !core.ReleasedMatchesReturned(s2, all) {
		v.fail("P3b", fmt.Sprintf("after %s: released effects disagree with returned", ev))
	}
	if !core.ExpiredNeverConfirmed(s, s2) {
		v.fail("P4", fmt.Sprintf("%s revived an Expired record", ev))
	}
	if !core.ConfirmedBeforeDue(s2) {
		v.fail("P4a", fmt.Sprintf("after %s: %+v", ev, s2.Res))
	}
	if !core.ConfirmOnlyBeforeDue(s, s2) {
		v.fail("P4b", fmt.Sprintf("%s confirmed a non-Held or Due record (clock %d)", ev, s.Clock))
	}
	if !core.CountersMatchRecords(s2) {
		v.fail("A1", fmt.Sprintf("after %s: %+v %+v", ev, s2.Stocks, s2.Res))
	}
	if !core.UniqueIdsKnownSku(s2) {
		v.fail("A2", fmt.Sprintf("after %s: %+v", ev, s2.Res))
	}
	if !stable(s, s2) {
		v.fail("S10", fmt.Sprintf("%s changed an identity field or revived a closed record", ev))
	}
	if e.Kind == core.Reserve || e.Kind == core.Confirm || e.Kind == core.Expire {
		ms3, _ := m.step(ms2, e)
		if !stateEq(s2, m.proj(ms3)) {
			v.fail("S11", fmt.Sprintf("second delivery of %s changed state: %+v -> %+v", ev, s2, m.proj(ms3)))
		}
	}
	// Pins S0 to S9: same case, same result as core.Step, which core's own tests pin to section 4.
	want, wfx := core.Step(s, e)
	if !stateEq(s2, want) || !slices.Equal(fx, wfx) {
		v.fail(pinCase(s, e), fmt.Sprintf("%s at clock %d on %+v: got %+v %v, want %+v %v",
			ev, s.Clock, s.Res, s2.Stocks, fx, want.Stocks, wfx))
	}
}

// runList folds events through the machine from Init, running every check on each step.
func (m machine) runList(v verdict, skus []core.StockInit, events []core.Event) {
	ms := m.init(skus)
	var all []core.Effect
	for _, e := range events {
		before := m.proj(ms)
		ms2, fx := m.step(ms, e)
		all = append(all, fx...)
		m.checkStep(v, ms, e, ms2, fx, all)
		if !stateEq(before, m.proj(ms)) {
			v.fail("input-mutated", fmt.Sprintf("step mutated its input on %v", e))
		}
		ms = ms2
	}
}

// genEvents draws one seeded event list: sku may be unknown, qty and ttl may
// be 0, and earlier events are re-sent (duplicate and reorder) 20% of the time.
// With extra, 12% each of ReserveCheck and ReserveCommit are drawn too.
func genEvents(r *rand.Rand, nsku, maxT int64, extra bool) []core.Event {
	var evs []core.Event
	for j, l := 0, r.IntN(151); j < l; j++ {
		if len(evs) > 0 && r.IntN(100) < 20 {
			evs = append(evs, evs[r.IntN(len(evs))])
			continue
		}
		e := core.Event{ID: int64(1 + r.IntN(6)), Sku: int64(r.IntN(int(nsku) + 1)),
			Qty: int64(r.IntN(int(maxT) + 2)), Ttl: int64(r.IntN(4))}
		n := r.IntN(100)
		if extra && n >= 76 {
			e.Kind = ReserveCheck
			if n >= 88 {
				e.Kind = ReserveCommit
			}
			evs = append(evs, e)
			continue
		}
		switch {
		case n < 30:
			e.Kind = core.Reserve
		case n < 50:
			e.Kind = core.Confirm
		case n < 70:
			e.Kind = core.Expire
		case n < 90:
			e.Kind = core.Tick
		case n < 94:
			e.Kind = core.Crash
		default:
			e.Kind = core.Restart
		}
		evs = append(evs, e)
	}
	return evs
}

// directedM4 is the section 5 sequence [Check 1, Check 2, Commit 1, Commit 2]
// on one stock of total 3 with both requests for qty 2: both pass the check
// (2 <= 3), both commit, available ends at -1.
func directedM4() ([]core.StockInit, []core.Event) {
	return []core.StockInit{{Sku: 0, Total: 3}}, []core.Event{
		{Kind: ReserveCheck, ID: 1, Sku: 0, Qty: 2, Ttl: 2}, {Kind: ReserveCheck, ID: 2, Sku: 0, Qty: 2, Ttl: 2},
		{Kind: ReserveCommit, ID: 1}, {Kind: ReserveCommit, ID: 2}}
}

// allChecks runs 2000 seeded random lists (1 to 3 stocks, totals 1 to 6) and, for M4, the directed list.
func allChecks(m machine) verdict {
	v := verdict{}
	r := rand.New(rand.NewPCG(1, 1^0x9e3779b97f4a7c15))
	for i := 0; i < 2000; i++ {
		nsku := int64(1 + r.IntN(3))
		in := make([]core.StockInit, nsku)
		for k := range in {
			in[k] = core.StockInit{Sku: int64(k), Total: int64(1 + r.IntN(6))}
		}
		m.runList(v, in, genEvents(r, nsku, 6, m.extra))
	}
	if m.extra {
		in, evs := directedM4()
		d := verdict{}
		m.runList(d, in, evs)
		for n, msg := range d {
			v.fail(n, msg)
		}
		v["directed"] = strings.Join(d.names(), ",")
	}
	return v
}

// expect lists, per mutant, the exact set of checks that fail (every other
// check must pass). It is the full set found on the first run, pinned so any change is
// noticed. Section 5 differences (M1b S7, M4 P2, M5a P2 and P1b) are logged
// by the matrix below and written up in docs/results/uc2-mutants.md.
var expect = map[string]struct{ fail []string }{
	"core": {nil},
	"M1":   {[]string{"P4a", "P4b", "S5"}},
	"M1b":  {[]string{"S6"}},
	"M2":   {[]string{"P3", "A1", "S7", "S10", "S11"}},
	"M3":   {[]string{"P3", "P4", "P4a", "P4b", "A1", "S5", "S10", "S11"}},
	"M3b":  {[]string{"P4a", "P4b", "S5"}},
	"M4":   {[]string{"P1", "P1b", "P3b", "A2", "M4-only"}},
	"M5":   {[]string{"P1b", "P2", "S3"}},
	"M5a":  {[]string{"P1", "S3"}},
	"M6":   {[]string{"P2", "A1", "S6"}},
	"M7":   {[]string{"P3b", "A2", "S3", "S11"}},
}

func TestMutantsRejectedByChecks(t *testing.T) {
	ms := machines()
	got := make([]verdict, len(ms))
	for i, m := range ms {
		got[i] = allChecks(m)
		delete(got[i], "directed")
	}
	for i, m := range ms {
		v := got[i]
		t.Logf("%s: failing checks: %v", m.name, v.names())
		for _, n := range v.names() {
			t.Logf("  %-8s first failure: %s", n, v[n])
		}
		if m.name != "core" && len(v) == 0 {
			t.Errorf("%s survived every check", m.name)
		}
		if m.name == "core" && len(v) != 0 {
			t.Errorf("control core.Step fails %v", v.names())
		}
		if ex, ok := expect[m.name]; ok {
			if want := slices.Clone(ex.fail); !slices.Equal(sortBy(want), v.names()) {
				t.Errorf("%s: failing checks %v, pinned %v", m.name, v.names(), sortBy(want))
			}
		}
	}
	// Kill matrix.
	var b strings.Builder
	fmt.Fprintf(&b, "\nkill matrix (X = check fails on the mutant; core is the control)\n%-5s", "")
	for _, n := range checkNames {
		fmt.Fprintf(&b, " %s", n)
	}
	b.WriteString("\n")
	for i, m := range ms {
		fmt.Fprintf(&b, "%-5s", m.name)
		for _, n := range checkNames {
			c := "."
			if _, ok := got[i][n]; ok {
				c = "X"
			}
			fmt.Fprintf(&b, " %*s", len(n), c)
		}
		b.WriteString("\n")
	}
	// Comparison with section 5.
	b.WriteString("\nsection 5 'Killed by' vs actual\n")
	for i, m := range ms {
		claimed, ok := section5[m.name]
		if !ok {
			continue
		}
		var missing, extra []string
		for _, n := range claimed {
			if _, f := got[i][n]; !f {
				missing = append(missing, n)
			}
		}
		for _, n := range got[i].names() {
			if !slices.Contains(claimed, n) {
				extra = append(extra, n)
			}
		}
		fmt.Fprintf(&b, "%-4s claimed-but-passes=%v fails-but-not-claimed=%v\n", m.name, missing, extra)
	}
	t.Log(b.String())
}

func sortBy(ns []string) []string {
	sort.Slice(ns, func(i, j int) bool { return slices.Index(checkNames, ns[i]) < slices.Index(checkNames, ns[j]) })
	return ns
}

// TestM4DirectedOversell pins the section 5 directed list: after
// [Check 1, Check 2, Commit 1, Commit 2] on total 3 the stock is available -1.
func TestM4DirectedOversell(t *testing.T) {
	in, evs := directedM4()
	m := InitM4(in)
	for _, e := range evs {
		m, _ = StepM4(m, e)
	}
	if got := m.Stocks[0].Available; got != -1 {
		t.Fatalf("available = %d, want -1", got)
	}
	v := verdict{}
	m4Machine().runList(v, in, evs)
	t.Logf("directed list fails: %v", v.names())
	for _, n := range []string{"P1", "P1b"} {
		if _, ok := v[n]; !ok {
			t.Errorf("directed list should fail %s", n)
		}
	}
	if _, ok := v["P2"]; ok {
		t.Errorf("P2 fails on M4 with signed counters, section 5 says Bend only")
	}
	s := core.Init(in)
	for _, e := range evs { // core.Step ignores the mutant-only events
		s, _ = core.Step(s, e)
	}
	if s.Stocks[0].Available != 3 || len(s.Res) != 0 {
		t.Fatalf("core.Step reacted to a mutant-only event: %+v", s)
	}
}

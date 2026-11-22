package mutants

import (
	"fmt"
	"math/rand/v2"
	"reflect"
	"slices"
	"sort"
	"testing"

	"github.com/derangga/learn-formal-verification/internal/uc1/core"
)

// machine hides the state type so M3 (extra field) and the others share one checker.
type machine struct {
	name  string
	extra bool // draw the mutant-only event ProvApplyCharge
	init  func(n uint32) any
	step  func(any, core.Event) (any, []core.Effect)
	proj  func(any) core.State
}

func plain(name string, f func(core.State, core.Event) (core.State, []core.Effect)) machine {
	return machine{name, false,
		func(n uint32) any { return core.Init(n) },
		func(s any, e core.Event) (any, []core.Effect) { return f(s.(core.State), e) },
		func(s any) core.State { return s.(core.State) }}
}

func m3Machine() machine {
	return machine{"M3", true,
		func(n uint32) any { return InitM3(n) },
		func(s any, e core.Event) (any, []core.Effect) { return StepM3(s.(M3State), e) },
		func(s any) core.State { return s.(M3State).State }}
}

func randEvent(r *rand.Rand, n uint32, extra bool) core.Event {
	k := int(core.Restart) + 1
	if extra {
		k++
	}
	return core.Event{
		Kind: core.Kind(r.IntN(k)),
		O:    uint32(r.IntN(int(n) + 2)),
		A:    []uint32{0, 1, 5, 7}[r.IntN(4)],
		D:    core.Decision(r.IntN(2)),
		Svc:  core.Service(r.IntN(2)),
	}
}

func kn(k core.Kind) string {
	if k == ProvApplyCharge {
		return "ProvApplyCharge"
	}
	return k.String()
}

func legal(a, b core.Status) bool {
	return a == b || (a == core.None && b == core.AwaitingPayment) ||
		(a == core.AwaitingPayment && (b == core.Paid || b == core.Failed)) || (a == core.Paid && b == core.Refunded)
}

func hasEffect(fx []core.Effect, k core.EffectKind, o uint32) bool {
	for _, f := range fx {
		if f.Kind == k && f.O == o {
			return true
		}
	}
	return false
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
	sort.Strings(ns)
	return ns
}

// checkTransition applies the transition and state checks to one step (s, e, s2, fx).
func checkTransition(v verdict, s core.State, e core.Event, s2 core.State, fx []core.Effect) {
	if !core.Inv(s2) {
		v.fail("Inv", fmt.Sprintf("after %v o=%d", kn(e.Kind), e.O))
	}
	for o := uint32(0); o < uint32(len(s.Slots))+2; o++ {
		a, b := core.Pr(s, o), core.Pr(s2, o)
		if b.ChargeCount > 1 {
			v.fail("P1", fmt.Sprintf("after %v: order %d chargeCount=%d", kn(e.Kind), o, b.ChargeCount))
		}
		if b.RefundCount > b.ChargeCount {
			v.fail("P2a", fmt.Sprintf("after %v: order %d refund %d > charge %d", kn(e.Kind), o, b.RefundCount, b.ChargeCount))
		}
		if core.St(s, o) != core.Refunded && core.St(s2, o) == core.Refunded && core.St(s, o) != core.Paid {
			v.fail("P2b(a)", fmt.Sprintf("%v order %d: %v -> Refunded", kn(e.Kind), o, core.St(s, o)))
		}
		if !core.Od(s, o).OutRefund && core.Od(s2, o).OutRefund && core.St(s, o) != core.Paid {
			v.fail("P2b(b)", fmt.Sprintf("%v order %d: outRefund set from %v", kn(e.Kind), o, core.St(s, o)))
		}
		if hasEffect(fx, core.WireRefundReq, o) && core.St(s, o) != core.Refunded {
			v.fail("P2b(c)", fmt.Sprintf("%v order %d", kn(e.Kind), o))
		}
		if hasEffect(fx, core.Refund, o) && a.Rec != core.Approved {
			v.fail("P2b(d)", fmt.Sprintf("%v order %d", kn(e.Kind), o))
		}
		if core.IsTerminal(core.St(s, o)) &&
			(core.St(s2, o) != core.St(s, o) || core.Od(s2, o).Amount != core.Od(s, o).Amount) {
			v.fail("P3", fmt.Sprintf("%v changed terminal order %d: %v -> %v", kn(e.Kind), o, core.Od(s, o), core.Od(s2, o)))
		}
		if !legal(core.St(s, o), core.St(s2, o)) {
			v.fail("A12", fmt.Sprintf("%v order %d: %v -> %v", kn(e.Kind), o, core.St(s, o), core.St(s2, o)))
		}
		if a.Rec != b.Rec && !(a.Rec == core.NoRec && (b.Rec == core.Approved || b.Rec == core.Declined)) {
			v.fail("A13", fmt.Sprintf("%v order %d: rec %v -> %v", kn(e.Kind), o, a.Rec, b.Rec))
		}
		if b.ChargeCount < a.ChargeCount || b.RefundCount < a.RefundCount {
			v.fail("A13", fmt.Sprintf("%v order %d: counts decreased", kn(e.Kind), o))
		}
	}
}

// runChecks runs the seeded random runs (P1, P2a, P2b, P3, Inv, A12, A13), with
// the per-order Charge-effect count of P1, from Init.
func runChecks(m machine, seed uint64, v verdict) {
	r := rand.New(rand.NewPCG(seed, seed^0x9e3779b97f4a7c15))
	for i := 0; i < 1000; i++ {
		n := uint32(2 + r.IntN(2))
		s := m.init(n)
		charges := map[uint32]int{}
		for j, l := 0, r.IntN(201); j < l; j++ {
			e := randEvent(r, n, m.extra)
			s2, fx := m.step(s, e)
			checkTransition(v, m.proj(s), e, m.proj(s2), fx)
			for _, f := range fx {
				if f.Kind == core.Charge {
					charges[f.O]++
					if charges[f.O] > 1 {
						v.fail("P1", fmt.Sprintf("order %d has %d Charge effects after %v", f.O, charges[f.O], kn(e.Kind)))
					}
				}
			}
			s = s2
		}
	}
}

// pinChecks is the pin check A1 to A11: from every slot state in a small
// enumerated space (slot 1 of 2, other slot default), for all four up/down
// combinations and every contract event on order 1 (a in {0,5}, d both), the
// mutant step must equal core.Step, which core's tests pin to A1 to A11.
func pinChecks(m machine, v verdict) {
	name := map[core.Kind]string{
		core.PlaceOrder: "A1", core.RetryTimeout: "A2", core.FlushChargeReq: "A3", core.FlushRefundReq: "A7",
		core.PaymentApproved: "A4", core.PaymentDeclined: "A5", core.RefundOrder: "A6",
		core.ChargeReqRecv: "A8", core.RefundReqRecv: "A10", core.FlushReply: "A9",
		core.Crash: "A11", core.Restart: "A11",
		ProvApplyCharge: "ProvApplyCharge (mutant-only; core.Step ignores it)",
	}
	bools := []bool{false, true}
	for st := core.None; st <= core.Refunded; st++ {
		for _, am := range []uint32{0, 5} {
			for _, oc := range bools {
				for _, orf := range bools {
					for rec := core.NoRec; rec <= core.Declined; rec++ {
						for cc := uint32(0); cc <= 2; cc++ {
							for rc := uint32(0); rc <= 2; rc++ {
								for _, amt := range []uint32{0, 5} {
									for _, rp := range bools {
										sl := core.Slot{
											Ord:  core.OrdRec{Status: st, Amount: am, OutCharge: oc, OutRefund: orf},
											Prov: core.ProvRec{Rec: rec, ChargeCount: cc, RefundCount: rc, Amt: amt, OutReply: rp},
										}
										for _, ou := range bools {
											for _, pu := range bools {
												s := core.Init(2)
												s.Slots[1] = sl
												s.OrderUp, s.ProvUp = ou, pu
												pinOne(m, v, name, s)
											}
										}
									}
								}
							}
						}
					}
				}
			}
		}
	}
}

func pinOne(m machine, v verdict, name map[core.Kind]string, s core.State) {
	last := core.Restart
	if m.extra {
		last = ProvApplyCharge
	}
	for k := core.PlaceOrder; k <= last; k++ {
		for _, a := range []uint32{0, 5} {
			for _, d := range []core.Decision{core.Approve, core.Decline} {
				for _, o := range []uint32{1, 7} {
					e := core.Event{Kind: k, O: o, A: a, D: d, Svc: core.Provider}
					ms := m.init(2)
					if m.extra {
						ms = M3State{State: s, Pending: []uint32{0, 1}} // pending 1 on slot 1 so ProvApplyCharge acts
					} else {
						ms = s
					}
					got, gfx := m.step(ms, e)
					want, wfx := core.Step(s, e)
					if !reflect.DeepEqual(m.proj(got), want) || !slices.Equal(gfx, wfx) {
						v.fail(name[k], fmt.Sprintf("%v o=%d a=%d d=%v on %+v: got %+v %v want %+v %v",
							k, o, a, d, s.Slots[1], m.proj(got).Slots[1], gfx, want.Slots[1], wfx))
					}
				}
			}
		}
	}
}

func allChecks(m machine) verdict {
	v := verdict{}
	runChecks(m, 1, v)
	pinChecks(m, v)
	return v
}

// expect lists the checks that must fail (killers, section 5 "Killed by" plus
// whatever else actually fails, pinned so a change is noticed) and, for each
// mutant, the checks that must NOT fail.
var expect = map[string]struct{ fail, pass []string }{
	"core": {nil, []string{"Inv", "P1", "P2a", "P2b(a)", "P2b(b)", "P2b(c)", "P2b(d)", "P3", "A12", "A13",
		"A1", "A2", "A3", "A4", "A5", "A6", "A7", "A8", "A9", "A10", "A11"}},
	"M1":  {[]string{"Inv", "P1", "A8", "A13"}, []string{"P2a", "P3", "A12"}},
	"M2a": {[]string{"P2b(a)", "P2b(b)", "P3", "A6", "A12"}, []string{"P1", "Inv"}},
	"M2b": {[]string{"P2a", "A10"}, []string{"P1", "P3", "A12"}},
	"M3":  {[]string{"Inv", "P1", "A8", "A13", "ProvApplyCharge (mutant-only; core.Step ignores it)"}, []string{"P2a", "P3", "A12"}},
	"M4":  {[]string{"P3", "A4", "A12", "Inv", "P2b(c)"}, []string{"P1", "P2a", "A13"}},
	"M5":  {[]string{"A8", "A13"}, []string{"Inv", "P1", "P2a", "P2b(a)", "P2b(b)", "P2b(c)", "P2b(d)", "P3", "A12"}},
}

func machines() []machine {
	return []machine{plain("core", core.Step), plain("M1", StepM1), plain("M2a", StepM2a),
		plain("M2b", StepM2b), m3Machine(), plain("M4", StepM4), plain("M5", StepM5)}
}

func TestMutantsRejectedByChecks(t *testing.T) {
	for _, m := range machines() {
		m := m
		t.Run(m.name, func(t *testing.T) {
			t.Parallel()
			v := allChecks(m)
			ex := expect[m.name]
			t.Logf("%s: failing checks: %v", m.name, v.names())
			for _, n := range v.names() {
				t.Logf("  %-7s first failure: %s", n, v[n])
			}
			for _, n := range ex.fail {
				if _, ok := v[n]; !ok {
					t.Errorf("%s: check %s should fail but passed", m.name, n)
				}
			}
			for _, n := range ex.pass {
				if msg, ok := v[n]; ok {
					t.Errorf("%s: check %s should pass but failed: %s", m.name, n, msg)
				}
			}
			if m.name != "core" && len(v) == 0 {
				t.Errorf("%s survived every check", m.name)
			}
		})
	}
}

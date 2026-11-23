// Package uc2conformance runs the same event sequences through a Go step
// function and through the compiled Bend port (bend/uc2/main.bend) and
// compares the final states. The Bend proofs are about the Bend port, so this
// is the only link to the Go core. A mutant core can be checked by passing its
// step function to Find or Run.
package uc2conformance

import (
	"bytes"
	"context"
	"fmt"
	"math/rand"
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"strconv"
	"strings"
	"sync"
	"testing"
	"time"

	"github.com/derangga/learn-formal-verification/internal/uc2/core"
)

// StepFn has the signature of core.Step. Mutants plug in here.
type StepFn func(core.State, core.Event) (core.State, []core.Effect)

// runTimeout bounds one run of the Bend binary (a hung stdin read never returns).
const runTimeout = 20 * time.Second

// buildTimeout bounds the one-time compile of main.bend.
const buildTimeout = 2 * time.Minute

// Big is the one large value the generator uses (Bend Nat is unary; main.bend
// rejects anything above 100000). It stays far below 2^31.
const Big = 100000

var (
	buildOnce sync.Once
	builtBin  string
	buildErr  error
)

// RepoRoot returns the repository root, found from this source file.
func RepoRoot() string {
	_, file, _, _ := runtime.Caller(0)
	return filepath.Join(filepath.Dir(file), "..", "..")
}

// BuildBend compiles bend/uc2/main.bend once per test process (into a
// temporary directory that is not removed) and returns the binary path. It
// skips the test when bend is not on PATH and fails it when the compile fails
// or exceeds buildTimeout.
func BuildBend(t testing.TB) string {
	t.Helper()
	if _, err := exec.LookPath("bend"); err != nil {
		t.Skip("bend not on PATH (run `source .nix/env.sh`); skipping the Bend conformance harness")
	}
	buildOnce.Do(func() {
		dir, err := os.MkdirTemp("", "uc2-conformance-")
		if err != nil {
			buildErr = err
			return
		}
		bin := filepath.Join(dir, "uc2.bin")
		ctx, cancel := context.WithTimeout(context.Background(), buildTimeout)
		defer cancel()
		cmd := exec.CommandContext(ctx, "bend", "bend/uc2/main.bend", "-o", bin)
		cmd.Dir = RepoRoot()
		cmd.WaitDelay = time.Second
		if out, err := cmd.CombinedOutput(); err != nil {
			buildErr = fmt.Errorf("bend compile failed: %v\n%s", err, out)
			return
		}
		builtBin = bin
	})
	if buildErr != nil {
		t.Fatalf("%v", buildErr)
	}
	return builtBin
}

// GenEvents returns a seeded random sequence of 1..maxLen events and the
// initial total of the one stock (sku 0). Ids come from a small pool (0..9
// plus 10 and 11 as ids never reserved often) so duplicates, unknown ids and
// reordering are frequent; sku is 0 except one event in eight (sku 1 is
// unknown); qty and ttl include 0 (BadRequest) and one large value.
func GenEvents(seed int64, maxLen int) (int64, []core.Event) {
	r := rand.New(rand.NewSource(seed))
	var total int64
	switch r.Intn(10) {
	case 0:
		total = 0
	case 1:
		total = Big
	default:
		total = int64(1 + r.Intn(8))
	}
	evs := make([]core.Event, 1+r.Intn(maxLen))
	for i := range evs {
		var e core.Event
		switch k := r.Intn(20); {
		case k < 6:
			e.Kind = core.Reserve
		case k < 10:
			e.Kind = core.Confirm
		case k < 14:
			e.Kind = core.Expire
		case k < 18:
			e.Kind = core.Tick
		case k < 19:
			e.Kind = core.Crash
		default:
			e.Kind = core.Restart
		}
		switch e.Kind {
		case core.Reserve, core.Confirm, core.Expire:
			e.ID = int64(r.Intn(12))
		}
		if e.Kind == core.Reserve {
			if r.Intn(8) == 0 {
				e.Sku = 1
			}
			switch r.Intn(12) {
			case 0:
				e.Qty = 0
			case 1:
				e.Qty = Big
			default:
				e.Qty = int64(1 + r.Intn(4))
			}
			switch r.Intn(12) {
			case 0:
				e.Ttl = 0
			case 1:
				e.Ttl = Big
			default:
				e.Ttl = int64(1 + r.Intn(4))
			}
		}
		evs[i] = e
	}
	return total, evs
}

// Encode writes the stdin text for the Bend binary: the total, then five
// numbers per event (kind id sku qty ttl), single spaces, final newline.
func Encode(total int64, evs []core.Event) string {
	var b strings.Builder
	b.WriteString(strconv.FormatInt(total, 10))
	for _, e := range evs {
		fmt.Fprintf(&b, " %d %d %d %d %d", e.Kind, e.ID, e.Sku, e.Qty, e.Ttl)
	}
	b.WriteByte('\n')
	return b.String()
}

// Tally slots: 0 FxReserved, 1 FxConfirmed, 2 FxReleased, 3+r FxRejected with reason r.
const nTally = 3 + 8

var tallyNames = [nTally]string{"FxReserved", "FxConfirmed", "FxReleased",
	"BadRequest", "UnknownSku", "DuplicateId", "InsufficientStock",
	"UnknownReservation", "NotHeld", "TooLate", "NotYet"}

// Totals is the per-slot tally: how many, and the wrapping uint32 sums of the
// id, the qty and the expiresAt. main.bend computes the same.
type Totals [nTally]struct{ N, SumID, SumQty, SumExp uint32 }

func slot(f core.Effect) int {
	if f.Kind == core.FxRejected {
		return 3 + int(f.Reason)
	}
	return int(f.Kind) // FxReserved 0, FxConfirmed 1, FxReleased 2
}

func (t *Totals) add(fx []core.Effect) {
	for _, f := range fx {
		x := &t[slot(f)]
		x.N++
		x.SumID += uint32(f.ID)
		// Go only fills Qty and ExpiresAt for the kinds that use them; Bend
		// passes 0 for the others. Reserved: qty, exp. Released: qty.
		switch f.Kind {
		case core.FxReserved:
			x.SumQty += uint32(f.Qty)
			x.SumExp += uint32(f.ExpiresAt)
		case core.FxReleased:
			x.SumQty += uint32(f.Qty)
		}
	}
}

// GoRun folds step over evs from core.Init (one stock, sku 0, this total) and
// serialises the final state and effect tallies the way main.bend does.
func GoRun(step StepFn, total int64, evs []core.Event) string {
	s := core.Init([]core.StockInit{{Sku: 0, Total: total}})
	var tot Totals
	for _, e := range evs {
		var fx []core.Effect
		s, fx = step(s, e)
		tot.add(fx)
	}
	return Serialise(s, tot)
}

func b2i(b bool) int {
	if b {
		return 1
	}
	return 0
}

// Serialise renders a state as the single key=value line main.bend prints.
// Status numbers: Held 0, Confirmed 1, Expired 2.
func Serialise(s core.State, tot Totals) string {
	var b strings.Builder
	k := s.Stocks[0]
	fmt.Fprintf(&b, "up=%d clock=%d stock.sku=%d stock.total=%d stock.available=%d stock.reserved=%d stock.sold=%d",
		b2i(s.Up), s.Clock, k.Sku, k.Total, k.Available, k.Reserved, k.Sold)
	for i, r := range s.Res {
		fmt.Fprintf(&b, " r%[1]d.id=%[2]d r%[1]d.sku=%[3]d r%[1]d.qty=%[4]d r%[1]d.status=%[5]d"+
			" r%[1]d.expiresAt=%[6]d r%[1]d.confirmedAt=%[7]d r%[1]d.returned=%[8]d",
			i, r.ID, r.Sku, r.Qty, uint8(r.Status), r.ExpiresAt, r.ConfirmedAt, r.Returned)
	}
	for i, name := range tallyNames {
		fmt.Fprintf(&b, " tally.%[1]s=%[2]d tally.%[1]s.id=%[3]d tally.%[1]s.qty=%[4]d tally.%[1]s.exp=%[5]d",
			name, tot[i].N, tot[i].SumID, tot[i].SumQty, tot[i].SumExp)
	}
	return b.String()
}

// BendRun feeds the encoded events to the compiled binary and returns its
// output line. Stdin is a pipe that is written then closed; the run has a
// timeout; a nonzero exit is an error.
func BendRun(bin string, total int64, evs []core.Event) (string, error) {
	ctx, cancel := context.WithTimeout(context.Background(), runTimeout)
	defer cancel()
	cmd := exec.CommandContext(ctx, bin)
	cmd.Stdin = strings.NewReader(Encode(total, evs))
	var out, errb bytes.Buffer
	cmd.Stdout, cmd.Stderr = &out, &errb
	cmd.WaitDelay = time.Second
	if err := cmd.Run(); err != nil {
		return "", fmt.Errorf("bend binary: %v (stderr %q, stdout %q)", err, errb.String(), out.String())
	}
	line := strings.TrimSuffix(out.String(), "\n")
	if strings.Contains(line, "\n") || line == "" {
		return "", fmt.Errorf("bend binary: expected one output line, got %q", out.String())
	}
	return line, nil
}

// Divergence describes the first disagreement found for one seed.
type Divergence struct {
	Seed     int64
	Total    int64
	Len      int // length of the full sequence
	Prefix   int // length of the first failing prefix (all shorter prefixes agree)
	Event    core.Event
	BendLine string // Bend output for the failing prefix
	GoLine   string // Go output for the failing prefix
	Prev     string // Bend state after Prefix-1 events (they agree)
}

// Index is the index of the first divergent event in the sequence.
func (d *Divergence) Index() int { return d.Prefix - 1 }

func (d *Divergence) String() string {
	return fmt.Sprintf("divergence: seed=%d total=%d sequence length=%d\n"+
		"first failing prefix: %d events (every shorter prefix agrees); the divergent event is index %d = %+v (%v)\n"+
		"state before: %s\nbend: %s\ngo:   %s",
		d.Seed, d.Total, d.Len, d.Prefix, d.Index(), d.Event, d.Event.Kind, d.Prev, d.BendLine, d.GoLine)
}

// Compare runs one sequence through both and returns the two lines.
func Compare(bin string, step StepFn, total int64, evs []core.Event) (bendLine, goLine string, err error) {
	bendLine, err = BendRun(bin, total, evs)
	return bendLine, GoRun(step, total, evs), err
}

// Find checks one seed. It returns nil when Go and Bend agree on the final
// state, a Divergence (with a scanned prefix) when they differ, and an error
// when the Bend binary fails.
func Find(bin string, step StepFn, seed int64, maxLen int) (*Divergence, error) {
	total, evs := GenEvents(seed, maxLen)
	bl, gl, err := Compare(bin, step, total, evs)
	if err != nil {
		return nil, fmt.Errorf("seed %d: %w", seed, err)
	}
	if bl == gl {
		return nil, nil
	}
	// Linear scan for the first failing prefix: the true first divergence of
	// the final-state comparison (about len runs of the binary, only on failure).
	prev := ""
	for l := 1; l <= len(evs); l++ {
		b, g, err := Compare(bin, step, total, evs[:l])
		if err != nil {
			return nil, fmt.Errorf("seed %d prefix %d: %w", seed, l, err)
		}
		if b != g {
			return &Divergence{Seed: seed, Total: total, Len: len(evs), Prefix: l, Event: evs[l-1], BendLine: b, GoLine: g, Prev: prev}, nil
		}
		prev = b
	}
	return nil, fmt.Errorf("seed %d: full run differs but no prefix does (nondeterministic run?)", seed)
}

// FindFirst tries seeds 1..seeds and returns the first Divergence, or nil if
// Go (with step) and Bend agree on all of them.
func FindFirst(bin string, step StepFn, seeds, maxLen int) (*Divergence, error) {
	for seed := int64(1); seed <= int64(seeds); seed++ {
		d, err := Find(bin, step, seed, maxLen)
		if err != nil || d != nil {
			return d, err
		}
	}
	return nil, nil
}

// Coverage counts what the generated sequences exercised (Go side, using the
// step function under test to track the state).
type Coverage struct {
	Effects        [4]int // by core.EffectKind
	Rejects        [8]int // by core.Reason
	Crashes        int
	Restarts       int
	Ticks          int
	EventsDown     int // Reserve, Confirm or Expire delivered while down
	QtyZero        int // Reserve with qty 0
	TtlZero        int // Reserve with ttl 0
	SkuOther       int // Reserve for sku 1
	ConfirmAtDue   int // Confirm of a Held record with expiresAt == clock
	ExpireAtDue    int // Expire of a Held record with expiresAt == clock
	DuplicateTries int // Reserve of an id that already has a record
}

func (c *Coverage) add(total int64, evs []core.Event, step StepFn) {
	s := core.Init([]core.StockInit{{Sku: 0, Total: total}})
	for _, e := range evs {
		c.note(s, e)
		var fx []core.Effect
		s, fx = step(s, e)
		for _, f := range fx {
			c.Effects[f.Kind]++
			if f.Kind == core.FxRejected {
				c.Rejects[f.Reason]++
			}
		}
	}
}

func (c *Coverage) note(s core.State, e core.Event) {
	switch e.Kind {
	case core.Crash:
		c.Crashes++
		return
	case core.Restart:
		c.Restarts++
		return
	case core.Tick:
		c.Ticks++
		return
	}
	if !s.Up {
		c.EventsDown++
		return
	}
	var rec *core.Res
	for i := range s.Res {
		if s.Res[i].ID == e.ID {
			rec = &s.Res[i]
			break
		}
	}
	switch e.Kind {
	case core.Reserve:
		if e.Qty == 0 {
			c.QtyZero++
		}
		if e.Ttl == 0 {
			c.TtlZero++
		}
		if e.Sku != 0 {
			c.SkuOther++
		}
		if rec != nil {
			c.DuplicateTries++
		}
	case core.Confirm:
		if rec != nil && rec.Status == core.Held && rec.ExpiresAt == s.Clock {
			c.ConfirmAtDue++
		}
	case core.Expire:
		if rec != nil && rec.Status == core.Held && rec.ExpiresAt == s.Clock {
			c.ExpireAtDue++
		}
	}
}

// Result counts what a Run compared.
type Result struct {
	Sequences int
	Events    int
	Cover     Coverage
}

// Run checks seeds 1..seeds and calls t.Fatalf on the first divergence.
func Run(t testing.TB, bin string, step StepFn, seeds, maxLen int) Result {
	t.Helper()
	var res Result
	for seed := int64(1); seed <= int64(seeds); seed++ {
		d, err := Find(bin, step, seed, maxLen)
		if err != nil {
			t.Fatalf("%v", err)
		}
		if d != nil {
			t.Fatalf("%s", d)
		}
		total, evs := GenEvents(seed, maxLen)
		res.Sequences++
		res.Events += len(evs)
		res.Cover.add(total, evs, step)
	}
	return res
}

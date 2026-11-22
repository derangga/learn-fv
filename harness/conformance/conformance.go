// Package conformance runs the same event sequences through a Go step
// function and through the compiled Bend port (bend/uc1/main.bend) and
// compares the final states. The Bend proofs are about the Bend port, so this
// is the only link to the Go core. A mutant core can be checked by passing its
// step function to Find or Run.
package conformance

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

	"github.com/derangga/learn-formal-verification/internal/uc1/core"
)

// StepFn has the signature of core.Step. Mutants plug in here.
type StepFn func(core.State, core.Event) (core.State, []core.Effect)

// runTimeout bounds one run of the Bend binary (a hung stdin read never returns).
const runTimeout = 20 * time.Second

// buildTimeout bounds the one-time compile of main.bend.
const buildTimeout = 2 * time.Minute

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

// BuildBend compiles bend/uc1/main.bend once per test process (into a
// temporary directory that is not removed) and returns the binary path. It
// skips the test when bend is not on PATH and fails it when the compile fails
// or exceeds buildTimeout.
func BuildBend(t testing.TB) string {
	t.Helper()
	if _, err := exec.LookPath("bend"); err != nil {
		t.Skip("bend not on PATH (run `source .nix/env.sh`); skipping the Bend conformance harness")
	}
	buildOnce.Do(func() {
		dir, err := os.MkdirTemp("", "uc1-conformance-")
		if err != nil {
			buildErr = err
			return
		}
		bin := filepath.Join(dir, "uc1.bin")
		ctx, cancel := context.WithTimeout(context.Background(), buildTimeout)
		defer cancel()
		cmd := exec.CommandContext(ctx, "bend", "bend/uc1/main.bend", "-o", bin)
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

// GenEvents returns a seeded random sequence of 1..maxLen events and the slot
// count N (2 or 3). Order ids reach N+1 so out-of-range ids are exercised;
// amounts include 0 and one large value.
func GenEvents(seed int64, maxLen int) (uint32, []core.Event) {
	r := rand.New(rand.NewSource(seed))
	n := uint32(2 + r.Intn(2))
	evs := make([]core.Event, 1+r.Intn(maxLen))
	for i := range evs {
		e := core.Event{
			Kind: core.Kind(r.Intn(int(core.Restart) + 1)),
			O:    uint32(r.Intn(int(n) + 2)),
			D:    core.Decision(r.Intn(2)),
			Svc:  core.Service(r.Intn(2)),
		}
		switch r.Intn(8) {
		case 0:
			e.A = 0
		case 1:
			e.A = 100000
		default:
			e.A = uint32(1 + r.Intn(4))
		}
		if e.Kind != core.PlaceOrder && e.Kind != core.ChargeReqRecv {
			e.A = 0
		}
		if e.Kind != core.ChargeReqRecv {
			e.D = core.Approve
		}
		if e.Kind != core.Crash && e.Kind != core.Restart {
			e.Svc = core.OrderSvc
		}
		switch e.Kind {
		case core.Crash, core.Restart:
			e.O = 0
		}
		evs[i] = e
	}
	return n, evs
}

// Encode writes the stdin text for the Bend binary: N, then five numbers per
// event (kind o a d svc), single spaces, final newline.
func Encode(n uint32, evs []core.Event) string {
	var b strings.Builder
	b.WriteString(strconv.FormatUint(uint64(n), 10))
	for _, e := range evs {
		fmt.Fprintf(&b, " %d %d %d %d %d", e.Kind, e.O, e.A, e.D, e.Svc)
	}
	b.WriteByte('\n')
	return b.String()
}

// Totals is the per-effect-kind tally: how many, and the wrapping uint32 sums
// of the order id and of the amount. main.bend computes the same.
type Totals [6]struct{ N, SumO, SumA uint32 }

// GoRun folds step over evs from core.Init(n) and serialises the final state
// and effect totals the way main.bend does.
func GoRun(step StepFn, n uint32, evs []core.Event) string {
	s := core.Init(n)
	var tot Totals
	for _, e := range evs {
		var fx []core.Effect
		s, fx = step(s, e)
		for _, f := range fx {
			x := &tot[f.Kind]
			x.N++
			x.SumO += f.O
			x.SumA += f.A
		}
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
func Serialise(s core.State, tot Totals) string {
	var b strings.Builder
	fmt.Fprintf(&b, "orderUp=%d provUp=%d", b2i(s.OrderUp), b2i(s.ProvUp))
	for i, sl := range s.Slots {
		o, p := sl.Ord, sl.Prov
		fmt.Fprintf(&b, " s%[1]d.status=%[2]d s%[1]d.amount=%[3]d s%[1]d.outCharge=%[4]d s%[1]d.outRefund=%[5]d"+
			" s%[1]d.rec=%[6]d s%[1]d.chargeCount=%[7]d s%[1]d.refundCount=%[8]d s%[1]d.amt=%[9]d s%[1]d.outReply=%[10]d",
			i, o.Status, o.Amount, b2i(o.OutCharge), b2i(o.OutRefund),
			p.Rec, p.ChargeCount, p.RefundCount, p.Amt, b2i(p.OutReply))
	}
	names := [6]core.EffectKind{core.WireChargeReq, core.WireRefundReq, core.WireApproved, core.WireDeclined, core.Charge, core.Refund}
	for _, k := range names {
		fmt.Fprintf(&b, " fx.%[1]s=%[2]d fx.%[1]s.o=%[3]d fx.%[1]s.a=%[4]d", k, tot[k].N, tot[k].SumO, tot[k].SumA)
	}
	return b.String()
}

// BendRun feeds the encoded events to the compiled binary and returns its
// output line. Stdin is a pipe that is written then closed; the run has a
// timeout; a nonzero exit is an error.
func BendRun(bin string, n uint32, evs []core.Event) (string, error) {
	ctx, cancel := context.WithTimeout(context.Background(), runTimeout)
	defer cancel()
	cmd := exec.CommandContext(ctx, bin)
	cmd.Stdin = strings.NewReader(Encode(n, evs))
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
	N        uint32
	Len      int // length of the full sequence
	Prefix   int // length of the first failing prefix (all shorter prefixes agree)
	Event    core.Event
	BendLine string // Bend output for the failing prefix
	GoLine   string // Go output for the failing prefix
	Prev     string // Bend state after Prefix-1 events (they agree)
}

func (d *Divergence) String() string {
	return fmt.Sprintf("divergence: seed=%d N=%d sequence length=%d\n"+
		"first failing prefix: %d events (every shorter prefix agrees); the divergent event is index %d = %+v (%v)\n"+
		"state before: %s\nbend: %s\ngo:   %s",
		d.Seed, d.N, d.Len, d.Prefix, d.Prefix-1, d.Event, d.Event.Kind, d.Prev, d.BendLine, d.GoLine)
}

// Compare runs one sequence through both and returns the two lines.
func Compare(bin string, step StepFn, n uint32, evs []core.Event) (bendLine, goLine string, err error) {
	bendLine, err = BendRun(bin, n, evs)
	return bendLine, GoRun(step, n, evs), err
}

// Find checks one seed. It returns nil when Go and Bend agree on the final
// state, a Divergence (with a bisected prefix) when they differ, and an error
// when the Bend binary fails.
func Find(bin string, step StepFn, seed int64, maxLen int) (*Divergence, error) {
	n, evs := GenEvents(seed, maxLen)
	bl, gl, err := Compare(bin, step, n, evs)
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
		b, g, err := Compare(bin, step, n, evs[:l])
		if err != nil {
			return nil, fmt.Errorf("seed %d prefix %d: %w", seed, l, err)
		}
		if b != g {
			return &Divergence{Seed: seed, N: n, Len: len(evs), Prefix: l, Event: evs[l-1], BendLine: b, GoLine: g, Prev: prev}, nil
		}
		prev = b
	}
	// The full sequence differed but every prefix agreed: not deterministic.
	return nil, fmt.Errorf("seed %d: full run differs but no prefix does (nondeterministic run?)", seed)
}

// Coverage counts what the generated sequences exercised (Go side, using the
// step function under test to track which services are up).
type Coverage struct {
	OutOfRangeO     int // events with an order id >= N (order and provider events)
	ZeroAmount      int // PlaceOrder or ChargeReqRecv with a = 0
	Crash, Restart  [2]int
	DeliveredDown   int // order or provider event whose receiver was down
	ChargeReplay    int // ChargeReqRecv (a > 0, in range, provider up) with rec != NoRec
	Declines        int // ChargeReqRecv with Decline
	EffectsProduced int
}

func (c *Coverage) add(n uint32, evs []core.Event, step StepFn) {
	s := core.Init(n)
	for _, e := range evs {
		switch e.Kind {
		case core.Crash:
			c.Crash[e.Svc]++
		case core.Restart:
			c.Restart[e.Svc]++
		default:
			if e.O >= n {
				c.OutOfRangeO++
			}
			if (e.Kind == core.PlaceOrder || e.Kind == core.ChargeReqRecv) && e.A == 0 {
				c.ZeroAmount++
			}
			prov := e.Kind >= core.ChargeReqRecv
			if (prov && !s.ProvUp) || (!prov && !s.OrderUp) {
				c.DeliveredDown++
			}
			if e.Kind == core.ChargeReqRecv {
				if e.D == core.Decline {
					c.Declines++
				}
				if s.ProvUp && e.A > 0 && e.O < n && s.Slots[e.O].Prov.Rec != core.NoRec {
					c.ChargeReplay++
				}
			}
		}
		var fx []core.Effect
		s, fx = step(s, e)
		c.EffectsProduced += len(fx)
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
		n, evs := GenEvents(seed, maxLen)
		res.Sequences++
		res.Events += len(evs)
		res.Cover.add(n, evs, step)
	}
	return res
}

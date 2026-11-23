package uc2conformance

import (
	"context"
	"errors"
	"flag"
	"os/exec"
	"strings"
	"testing"

	"github.com/derangga/learn-formal-verification/internal/uc2/core"
)

var (
	seeds  = flag.Int("seeds", 500, "number of seeded sequences (seeds 1..seeds)")
	maxLen = flag.Int("len", 300, "maximum events per sequence")
)

func TestConformanceUC2(t *testing.T) {
	bin := BuildBend(t)
	res := Run(t, bin, core.Step, *seeds, *maxLen)
	t.Logf("compared %d sequences, %d events: Go core and Bend agree", res.Sequences, res.Events)
	c := res.Cover
	t.Logf("coverage: %+v", c)
	cov := map[string]int{
		"crash": c.Crashes, "restart": c.Restarts, "tick": c.Ticks, "events while down": c.EventsDown,
		"qty 0": c.QtyZero, "ttl 0": c.TtlZero, "sku 1": c.SkuOther,
		"confirm at due": c.ConfirmAtDue, "expire at due": c.ExpireAtDue, "duplicate reserve": c.DuplicateTries,
	}
	for k := core.EffectKind(0); int(k) < len(c.Effects); k++ {
		cov["effect "+k.String()] = c.Effects[k]
	}
	for r := core.Reason(0); int(r) < len(c.Rejects); r++ {
		cov["reject "+r.String()] = c.Rejects[r]
	}
	for name, n := range cov {
		// small ad-hoc runs (-seeds 1 -len 1) cannot be expected to cover everything
		if n == 0 && res.Events >= 10000 {
			t.Errorf("coverage: %s never exercised", name)
		}
	}
}

// stepM1 is a local copy of the M1 bug: Confirm accepts a Held record at
// clock == expiresAt (the check is clock <= expiresAt instead of the correct
// expiresAt <= clock rejecting). It runs core.Step one clock tick earlier for
// that one case and then fixes the ghost field.
func stepM1(s core.State, e core.Event) (core.State, []core.Effect) {
	if s.Up && e.Kind == core.Confirm {
		for _, r := range s.Res {
			if r.ID == e.ID && r.Status == core.Held && r.ExpiresAt == s.Clock {
				back := s
				back.Clock--
				s2, fx := core.Step(back, e)
				s2.Clock++
				for i := range s2.Res {
					if s2.Res[i].ID == e.ID && s2.Res[i].Status == core.Confirmed {
						s2.Res[i].ConfirmedAt = s2.Clock
					}
				}
				return s2, fx
			}
		}
	}
	return core.Step(s, e)
}

func TestHarnessCatchesLocalM1(t *testing.T) {
	bin := BuildBend(t)
	d, err := FindFirst(bin, stepM1, *seeds, *maxLen)
	if err != nil {
		t.Fatal(err)
	}
	if d == nil {
		t.Fatalf("local M1 not caught in %d sequences: the harness is vacuous", *seeds)
	}
	if d.Prefix < 1 || d.Prefix > d.Len || d.BendLine == d.GoLine || d.Event.Kind != core.Confirm {
		t.Fatalf("bad divergence report: %s", d)
	}
	t.Logf("local M1 caught:\n%s", d)
}

// The Bend binary must exit nonzero on malformed input, never print a state.
func TestBendRejectsMalformedInput(t *testing.T) {
	bin := BuildBend(t)
	for _, in := range []string{
		"", "x\n", "-1\n", "+2\n", "4294967296\n", "5 0 0 0 1\n", "5 6 0 0 0 0\n", "5 0 0 0 1 1 1\n",
		"5 0 100001 0 1 1\n", "5  0 0 0 1 1\n", "5 0 0 0 1 1\r\n", "5\n6\n", "5\t0 0 0 1 1\n", "100001\n",
	} {
		ctx, cancel := context.WithTimeout(context.Background(), runTimeout)
		cmd := exec.CommandContext(ctx, bin)
		cmd.Stdin = strings.NewReader(in)
		out, err := cmd.Output()
		timedOut := ctx.Err() != nil
		cancel()
		var ee *exec.ExitError
		if timedOut || !errors.As(err, &ee) || ee.ExitCode() <= 0 {
			t.Errorf("input %q: err=%v timedOut=%v output %q; want a clean nonzero exit", in, err, timedOut, out)
		}
	}
}

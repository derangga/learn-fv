package conformance

import (
	"context"
	"errors"
	"flag"
	"os/exec"
	"strings"
	"testing"

	"github.com/derangga/learn-formal-verification/internal/uc1/core"
	mutants "github.com/derangga/learn-formal-verification/mutants/uc1"
)

var (
	seeds  = flag.Int("seeds", 500, "number of seeded sequences (seeds 1..seeds)")
	maxLen = flag.Int("len", 300, "maximum events per sequence")
)

func TestConformanceUC1(t *testing.T) {
	bin := BuildBend(t)
	res := Run(t, bin, core.Step, *seeds, *maxLen)
	t.Logf("compared %d sequences, %d events: Go core and Bend agree", res.Sequences, res.Events)
	c := res.Cover
	t.Logf("coverage: %+v", c)
	for name, n := range map[string]int{
		"out-of-range o": c.OutOfRangeO, "a=0": c.ZeroAmount, "crash OrderSvc": c.Crash[core.OrderSvc],
		"crash Provider": c.Crash[core.Provider], "restart OrderSvc": c.Restart[core.OrderSvc],
		"restart Provider": c.Restart[core.Provider], "delivered while down": c.DeliveredDown,
		"ChargeReqRecv replay": c.ChargeReplay, "effects": c.EffectsProduced,
	} {
		// small ad-hoc runs (-seeds 1 -len 1) cannot be expected to cover everything
		if n == 0 && res.Events >= 10000 {
			t.Errorf("coverage: %s never exercised", name)
		}
	}
}

func TestHarnessCatchesM1(t *testing.T) {
	bin := BuildBend(t)
	for seed := int64(1); seed <= int64(*seeds); seed++ {
		d, err := Find(bin, mutants.StepM1, seed, *maxLen)
		if err != nil {
			t.Fatal(err)
		}
		if d != nil {
			if d.Prefix < 1 || d.Prefix > d.Len || d.BendLine == d.GoLine {
				t.Fatalf("bad divergence report: %s", d)
			}
			t.Logf("mutant M1 caught:\n%s", d)
			return
		}
	}
	t.Fatalf("mutant M1 not caught in %d sequences: the harness is vacuous", *seeds)
}

// The Bend binary must exit nonzero on malformed input, never print a state.
func TestBendRejectsMalformedInput(t *testing.T) {
	bin := BuildBend(t)
	for _, in := range []string{
		"", "x\n", "-1\n", "+2\n", "4294967296\n", "2 0 0 5 0\n", "2 12 0 0 0 0\n", "2 0 0 5 2 0\n",
		"2 0 0 5 0 2\n", "2 0 100001 5 0 0\n", "2  0 0 5 0 0\n", "2 0 0 5 0 0\r\n", "2\n3\n", "2\t0 0 5 0 0\n",
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

package mutants

import (
	"flag"
	"testing"

	"github.com/derangga/learn-formal-verification/harness/conformance"
	"github.com/derangga/learn-formal-verification/internal/uc1/core"
)

var (
	seeds  = flag.Int("seeds", 500, "seeds tried per mutant (seeds 1..seeds)")
	maxLen = flag.Int("len", 300, "maximum events per sequence")
)

// The Bend side is the correct port, so a divergence means the conformance
// harness rejects the mutant. M3 runs through StepM3Contract: the contract
// alphabet only, so ProvApplyCharge is never sent (the correct Bend runner
// cannot receive it) and the divergence is the deferral of the charge, not
// the race itself.
func TestHarnessRejectsMutants(t *testing.T) {
	bin := conformance.BuildBend(t)
	for _, c := range []struct {
		name string
		step conformance.StepFn
	}{
		{"M1", StepM1}, {"M2a", StepM2a}, {"M2b", StepM2b},
		{"M3 (contract events only)", StepM3Contract}, {"M4", StepM4}, {"M5", StepM5},
	} {
		caught := false
		for seed := int64(1); seed <= int64(*seeds) && !caught; seed++ {
			d, err := conformance.Find(bin, c.step, seed, *maxLen)
			if err != nil {
				t.Fatal(err)
			}
			if d != nil {
				caught = true
				t.Logf("%s: harness rejects: seed=%d first divergent event index %d = %+v (%v)\n%s",
					c.name, d.Seed, d.Prefix-1, d.Event, d.Event.Kind, d)
			}
		}
		if !caught {
			t.Errorf("%s: survived %d seeds", c.name, *seeds)
		}
	}
	// control: the real core never diverges on the same seeds
	for seed := int64(1); seed <= 20; seed++ {
		if d, err := conformance.Find(bin, core.Step, seed, *maxLen); err != nil || d != nil {
			t.Fatalf("control diverged: %v %v", d, err)
		}
	}
}

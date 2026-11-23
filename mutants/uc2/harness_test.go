package mutants

import (
	"flag"
	"strings"
	"testing"

	conf "github.com/derangga/learn-formal-verification/harness/uc2conformance"
	"github.com/derangga/learn-formal-verification/internal/uc2/core"
)

var (
	seeds  = flag.Int("seeds", 500, "seeds tried per mutant (seeds 1..seeds)")
	maxLen = flag.Int("len", 300, "maximum events per sequence")
)

// diffKeys lists the key=value pairs on which two output lines differ.
func diffKeys(bend, goLine string) string {
	g := map[string]string{}
	for _, kv := range strings.Fields(goLine) {
		k, v, _ := strings.Cut(kv, "=")
		g[k] = v
	}
	var out []string
	for _, kv := range strings.Fields(bend) {
		k, v, _ := strings.Cut(kv, "=")
		if g[k] != v {
			out = append(out, k+": bend "+v+", go "+g[k])
		}
	}
	return strings.Join(out, "; ")
}

// The Bend side is the correct port, so a divergence means the conformance
// harness rejects the mutant. Every mutant here uses contract events only.
// M4 needs the mutant-only events ReserveCheck and ReserveCommit, which the
// Bend runner cannot receive (kind > 5 is an input error), so it is not run
// with them; StepM4Contract (contract alphabet only) equals core.Step and
// must not diverge.
func TestHarnessRejectsMutants(t *testing.T) {
	bin := conf.BuildBend(t)
	for _, c := range []struct {
		name string
		step conf.StepFn
	}{
		{"M1", StepM1}, {"M1b", StepM1b}, {"M2", StepM2}, {"M3", StepM3}, {"M3b", StepM3b},
		{"M5", StepM5}, {"M5a", StepM5a}, {"M6", StepM6}, {"M7", StepM7},
	} {
		d, err := conf.FindFirst(bin, c.step, *seeds, *maxLen)
		if err != nil {
			t.Fatal(err)
		}
		if d == nil {
			t.Errorf("%s: NOT caught by the harness in %d sequences", c.name, *seeds)
			continue
		}
		if d.Event.Kind > core.Restart {
			t.Errorf("%s: divergent event is not a contract event: %+v", c.name, d.Event)
		}
		t.Logf("%s: harness rejects: seed=%d first divergent event index %d = %+v (%v); differing keys: %s",
			c.name, d.Seed, d.Index(), d.Event, d.Event.Kind, diffKeys(d.BendLine, d.GoLine))
	}
}

// M4 cannot be sent to the Bend runner: its events are outside the contract
// alphabet. Its contract-alphabet view is core.Step, so the harness sees no bug.
func TestHarnessCannotSeeM4(t *testing.T) {
	bin := conf.BuildBend(t)
	d, err := conf.FindFirst(bin, StepM4Contract, *seeds, *maxLen)
	if err != nil {
		t.Fatal(err)
	}
	if d != nil {
		t.Fatalf("M4 (contract alphabet only) diverged, but it should equal core.Step: %s", d)
	}
	t.Logf("M4: not catchable by this harness: the bug needs ReserveCheck/ReserveCommit, which are not contract events (kind %d and %d; main.bend exits 1 on kind > 5); %d sequences agree",
		ReserveCheck, ReserveCommit, *seeds)
}

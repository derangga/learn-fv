package tlcreplay

import (
	"os"
	"path/filepath"
	"sort"
	"strings"
	"testing"

	"github.com/derangga/learn-formal-verification/internal/uc1/core"
)

const dir = "testdata"

func names(t *testing.T, prefix string) []string {
	m, err := filepath.Glob(filepath.Join(dir, prefix+"*.json"))
	if err != nil || len(m) == 0 {
		t.Fatalf("no %s fixtures in %s (run go generate ./harness/tlcreplay): %v", prefix, dir, err)
	}
	sort.Strings(m)
	for i := range m {
		m[i] = strings.TrimSuffix(filepath.Base(m[i]), ".json")
	}
	return m
}

func run(t *testing.T, name string) (*Trace, *Result) {
	tr, err := Load(dir, name)
	if err != nil {
		t.Fatal(err)
	}
	res, err := Replay(tr, t.TempDir())
	if err != nil {
		t.Fatal(err)
	}
	return tr, res
}

// Every reach witness is a legal behaviour of the correct model: the correct
// service must follow it with equal state and equal in-flight messages.
func TestReplayReach(t *testing.T) {
	for _, name := range names(t, "reach_") {
		t.Run(name, func(t *testing.T) {
			tr, res := run(t, name)
			if res.FirstDiv >= 0 {
				s := res.Steps[res.FirstDiv]
				t.Fatalf("diverges at step %d %s: %s", s.I, s.Event, s.Diff)
			}
			for i, s := range res.Snaps {
				if !core.Inv(s) {
					t.Fatalf("service state %d violates core.Inv", i)
				}
			}
			t.Logf("%d steps replayed, all states and in-flight bags equal (%s)", len(res.Steps), tr.Violation)
		})
	}
}

// First step at which the correct service leaves each buggy model's trace.
// Pinned: TLC traces are deterministic with -workers 1.
var wantDiv = map[string]int{
	"buggy": 5, "buggy_m2a": 1, "buggy_m2b": 10, "buggy_m3": 4, "buggy_m4": 8, "buggy_m5": 5,
}

// A buggy-model counterexample replayed on the correct service: the service
// leaves the trace at some step and the property TLC reported is never violated.
func TestReplayBuggy(t *testing.T) {
	for _, name := range names(t, "buggy") {
		t.Run(name, func(t *testing.T) {
			tr, res := run(t, name)
			prop := tr.ViolatedProperty()
			// the checker must flag the buggy TLA+ trace itself, or it proves nothing
			if v := Violation(prop, TLASnaps(tr), nil); v == "" {
				t.Fatalf("checker for %s does not flag the TLA+ trace", prop)
			}
			if res.FirstDiv < 0 {
				t.Fatalf("service followed the buggy trace to the end (%s)", tr.Violation)
			}
			s := res.Steps[res.FirstDiv]
			t.Logf("TLC: %s; first divergence at step %d %s: %s", tr.Violation, s.I, s.Event, s.Diff)
			if want, ok := wantDiv[name]; ok && s.I != want {
				t.Errorf("first divergence at step %d, want %d", s.I, want)
			}
			if v := Violation(prop, res.Snaps, res.Ledger); v != "" {
				t.Fatalf("service violates %s: %s", prop, v)
			}
			if !core.Inv(res.Snaps[len(res.Snaps)-1]) {
				t.Fatal("service final state violates core.Inv")
			}
		})
	}
}

// The comparison must not be vacuous: a tampered reach trace must diverge.
func TestReplayDetectsTamper(t *testing.T) {
	tr, err := Load(dir, "reach_paid")
	if err != nil {
		t.Fatal(err)
	}
	last := &tr.States[len(tr.States)-1]
	sl := last.Slots["0"]
	sl.Prov.ChargeCount++
	last.Slots["0"] = sl
	res, err := Replay(tr, t.TempDir())
	if err != nil {
		t.Fatal(err)
	}
	if res.FirstDiv != len(res.Steps)-1 {
		t.Fatalf("tampered last state: FirstDiv=%d, want %d", res.FirstDiv, len(res.Steps)-1)
	}
}

func TestFixturesPresent(t *testing.T) {
	for _, n := range []string{"buggy", "buggy_m2a", "buggy_m2b", "buggy_m3", "buggy_m4", "buggy_m5", "reach_paid", "reach_crash"} {
		if _, err := os.Stat(filepath.Join(dir, n+".json")); err != nil {
			t.Errorf("missing fixture %s: %v", n, err)
		}
	}
}

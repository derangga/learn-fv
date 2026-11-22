package sim

import (
	"fmt"
	"math/rand/v2"
)

// CrashPoint forces a crash at the Nth (1-based) ShouldCrash call for
// (Svc, Point).
type CrashPoint struct {
	Svc, Point string
	Nth        int
}

// CrashConfig configures a Crasher. The zero value never crashes.
type CrashConfig struct {
	Prob       float64      // chance a non-scripted ShouldCrash call crashes
	MaxCrashes int          // per-service budget (TLA+ MaxCrashes), scripted crashes included
	Script     []CrashPoint // forced crashes
}

// Crasher tracks which services are up and decides crashes.
type Crasher struct {
	cfg     CrashConfig
	rng     *rand.Rand
	trace   *Trace
	seen    map[[2]string]int
	down    map[string]bool
	crashes map[string]int
}

func NewCrasher(seed uint64, cfg CrashConfig, trace *Trace) *Crasher {
	return &Crasher{
		cfg: cfg, rng: rand.New(rand.NewPCG(seed, 0xc4a5)), trace: trace,
		seen: map[[2]string]int{}, down: map[string]bool{}, crashes: map[string]int{},
	}
}

func (c *Crasher) Up(svc string) bool { return !c.down[svc] }

// ShouldCrash is called by a service at a named point. It returns true (and
// has crashed svc) when the script or the seeded RNG says so and budget
// remains. A down service never crashes again. The RNG is drawn only for
// non-scripted calls with Prob > 0 and budget left, so the draw sequence
// depends only on the call sequence.
func (c *Crasher) ShouldCrash(svc, point string) bool {
	if c.down[svc] {
		return false
	}
	k := [2]string{svc, point}
	c.seen[k]++
	for _, s := range c.cfg.Script {
		if s.Svc == svc && s.Point == point && s.Nth == c.seen[k] {
			return c.Crash(svc)
		}
	}
	if c.cfg.Prob > 0 && c.crashes[svc] < c.cfg.MaxCrashes && c.rng.Float64() < c.cfg.Prob {
		return c.Crash(svc)
	}
	return false
}

// Crash takes svc down. It returns false if svc is already down or its
// budget is spent.
func (c *Crasher) Crash(svc string) bool {
	if c.down[svc] {
		c.trace.add("crash-denied", svc, "already down")
		return false
	}
	if c.crashes[svc] >= c.cfg.MaxCrashes {
		c.trace.add("crash-denied", svc, "budget spent")
		return false
	}
	c.down[svc] = true
	c.crashes[svc]++
	c.trace.add("crash", svc, fmt.Sprintf("n=%d", c.crashes[svc]))
	return true
}

// Restart brings svc back up. Durable state is the caller's concern.
func (c *Crasher) Restart(svc string) {
	if c.down[svc] {
		c.down[svc] = false
		c.trace.add("restart", svc, "")
		return
	}
	c.trace.add("restart-noop", svc, "already up")
}

// Crashes is how many times svc has crashed.
func (c *Crasher) Crashes(svc string) int { return c.crashes[svc] }

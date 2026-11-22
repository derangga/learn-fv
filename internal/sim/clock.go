// Package sim is the seeded, single-threaded fault layer shared by UC1-UC4.
// It has no goroutines and no sleeps: every fault is a decision drawn from a
// seed or forced by a script, and every decision lands in a Trace.
//
// Semantics worth knowing:
//   - MaxCrashes gates every crash: random, scripted and direct Crash(). A zero
//     CrashConfig means no crash at all, even if Script is set.
//   - A scripted CrashPoint's Nth counts only ShouldCrash calls made while the
//     service is up; calls while it is down are not counted.
//   - The duplicate bound (Faults.MaxDup) is per Send, i.e. per original copy.
//     TLA+ UC1 counts dup[m] per message value, so Go random runs may duplicate
//     more than TLC allowed. This is deliberate: Go explores a superset.
//   - Refused actions are traced (crash-denied, dup-denied, restart-noop).
//     Scripted calls with an out-of-range index return ok=false and trace
//     nothing, so a replay can report a mismatch instead of panicking.
//   - A nil *Trace is valid and discards entries.
package sim

import "time"

// Clock is the injectable time source.
type Clock interface {
	Now() time.Time
}

// Real reads the wall clock.
type Real struct{}

func (Real) Now() time.Time { return time.Now() }

// Fake moves only on Advance or Set. Set may go backwards. A paused process
// (UC3) is modelled by the caller keeping an old Now() value.
type Fake struct{ t time.Time }

func NewFake(start time.Time) *Fake { return &Fake{t: start} }

func (f *Fake) Now() time.Time          { return f.t }
func (f *Fake) Advance(d time.Duration) { f.t = f.t.Add(d) }
func (f *Fake) Set(t time.Time)         { f.t = t }

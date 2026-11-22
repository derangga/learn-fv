# UC1 sim: injectable clock and seeded fault transport

Start: (session start not recorded; package written just before) 2026-11-22T10:12:10Z
End: 2026-11-22T10:12:11Z

Package `internal/sim`, standard library only, no goroutines, no sleeps.

## API

- `Clock{Now()}`; `Real{}`; `NewFake(t)` with `Advance(d)`, `Set(t)` (may go backwards; a UC3 pause is a caller holding a stale `Now()`).
- `Trace{Entries, OnEntry}` and `TraceEntry{Seq, Kind, Svc, Detail}`; `Strings()` renders the schedule. One Trace is shared by a Net and its Crasher.
- `NewCrasher(seed, CrashConfig{Prob, MaxCrashes, Script []CrashPoint{Svc, Point, Nth}}, trace)`: `ShouldCrash(svc, point)`, `Crash`, `Restart`, `Up`, `Crashes`.
- `NewNet[M](seed, Faults{Drop, Dup, MaxDup, Reorder}, crasher, trace)`: `Send(to, m)`, `Next()`, scripted `InFlight()`, `Deliver(i) (Delivery, ok)`, `Drop(i) ok`, `Duplicate(i) ok`. An out-of-range `i` returns ok=false and traces nothing (a replay reports a mismatch instead of panicking).
- `Delivery[M]{To, Body, Lost}`.

## Design decisions

- Zero `Faults` is reliable and FIFO (oldest first). `Reorder: true` delivers a random in-flight copy; that is how delay and reorder are modelled (a message waits while others pass it).
- `Next` rolls drop/dup until a delivery happens; it returns false only when nothing is in flight. A duplicate bumps a per-original counter shared by all copies, so `MaxDup` bounds total duplicates per original (TLA+ `DupMax`). A duplicate refused at the bound falls through to a delivery.
- Delivery to a down service consumes the copy and sets `Lost` (UC1.md section 2). A nil crasher means every service is up.
- `Send` does not know the sender, so "nothing can be sent while down" is the service's job (check `Crasher.Up`).
- Crash budget is per service and also limits scripted crashes (TLA+ `MaxCrashes`); a refused scripted crash is traced as `crash-denied`. Zero `CrashConfig` never crashes.
- Net and Crasher have separate PCG streams from the same seed, so crash rolls do not shift network rolls. Determinism holds for an identical call sequence.
- `MaxCrashes` gates every crash: random, scripted and direct `Crash()`. A zero `CrashConfig` means no crash at all, even if `Script` is set.
- A scripted `Nth` counts only `ShouldCrash` calls made while the service is up.
- The duplicate bound is per `Send` (per original copy). TLA+ UC1 counts `dup[m]` per message value, so Go random runs may duplicate more than TLC allowed. Deliberate: Go explores a superset; per-Send accounting kept.
- Refused actions are traced: `dup-denied` (scripted and inside `Next`), `crash-denied` (already down or budget spent), `restart-noop` (already up).
- A nil `*Trace` is valid: entries are discarded. Constructors accept nil.

## Checks

`gofmt -l internal/sim` printed nothing; `go vet ./internal/sim/...` printed nothing (OK). `go test ./internal/sim/... -count=1 -v`:

```
=== RUN   TestFakeClock
--- PASS: TestFakeClock (0.00s)
=== RUN   TestDeterministic
--- PASS: TestDeterministic (0.00s)
=== RUN   TestDrop
--- PASS: TestDrop (0.00s)
=== RUN   TestDupBound
--- PASS: TestDupBound (0.00s)
=== RUN   TestReorderHappens
--- PASS: TestReorderHappens (0.00s)
=== RUN   TestScripted
--- PASS: TestScripted (0.00s)
=== RUN   TestDeliveryToDownIsLost
--- PASS: TestDeliveryToDownIsLost (0.00s)
=== RUN   TestCrashBudgetAndScript
--- PASS: TestCrashBudgetAndScript (0.00s)
=== RUN   TestCrashRandomRespectsBudget
--- PASS: TestCrashRandomRespectsBudget (0.00s)
=== RUN   TestDupDenied
--- PASS: TestDupDenied (0.00s)
=== RUN   TestCrashDenied
--- PASS: TestCrashDenied (0.00s)
=== RUN   TestScriptedOutOfRange
--- PASS: TestScriptedOutOfRange (0.00s)
=== RUN   TestNilTrace
--- PASS: TestNilTrace (0.00s)
PASS
ok  	github.com/derangga/learn-formal-verification/internal/sim	0.008s
```

Line counts (`wc -l internal/sim/*.go`):

```
   39 internal/sim/clock.go
   91 internal/sim/crash.go
  141 internal/sim/net.go
  267 internal/sim/sim_test.go
   46 internal/sim/trace.go
  584 total
```

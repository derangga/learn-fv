# UC2 service: inventory over SQLite outbox + HTTP

Authoring time (estimate, no timer kept): about 35 minutes including the fault-run tests. Failed iterations: 1 (test config, see Friction). Wall hit: none.

Package `services/inventory`. Pure Go, `modernc.org/sqlite` v1.62.0, `CGO_ENABLED=0`. No change to `go.mod` or `go.sum`.

## Design

- `store.go` (133 lines): schema and `load` / `save` / `outbox`. One file `inventory.db`: `meta(up, clock)`, `stock(pos, sku, total, available, reserved, sold)`, `res(pos, id, sku, qty, status, expires_at, confirmed_at, returned)` (ordered by `pos`, so insertion order round-trips), `outbox(seq, kind, id, sku, qty, expires_at, reason, sent)`. `load` reads the whole `core.State`; `save` writes it and appends the effects to `outbox`, in one transaction.
- `service.go` (289 lines): `Service`. `apply(e)` is the whole logic: `tx{load; core.Step; save state + outbox rows}`, commit, log the event, then return `ErrDown` if the service was down and the event was not Tick or Restart (Step already dropped it, rule S0; the durable state is unchanged). `post` sends an event through the chi handler (httptest recorder, no sockets), then asks the crasher for the `after-commit` crash point: state and outbox rows are committed, no reply has left.
  - Transport: requests cross `sim.Net[core.Event]` (`Submit`, `Next`, `DeliverIndex`, `Drop`, `Duplicate`); a copy for a crashed service is `Lost`. `Flush` moves unsent outbox rows to `sim.Net[core.Effect]` and sets `sent=1`, in one transaction, and returns `ErrDown` while crashed. `NextReply` delivers a reply copy to the client. Effects in flight are lost on crash; outbox rows are durable.
  - Clock: `SyncClock` sends as many `Tick` events as the injected `sim.Clock` has advanced (in units of `TickEvery`) since `New`. `Tick` applies up or down, as in S1. Tests use `sim.Fake`.
  - Crash and restart: `Crash` (`sim.Crasher`, budget `MaxCrashes`) applies the `Crash` event, so `up = false` is durable, then closes and reopens the SQLite file (a process restart). `Restart` reopens the file and applies the `Restart` event. Core's own `Up` flag is the one that drops events (S0); the crasher only gates the wire and the budget.
  - `Snapshot()`, `Log()` (applied events including Crash, Restart, Tick), `Effects()` (every outbox row, sent or not), `Replies()`.
- `http.go` (72 lines): chi router, `POST /reserve /confirm /expire /tick`, JSON `{"id","sku","qty","ttl"}`. 200 returns the effects as JSON, 503 when down, 400 on bad JSON. `ListenLocal` serves on `127.0.0.1` only and refuses other hosts (same as UC1).

Seeds: `Config.Seed` drives the crasher and both nets; the test drivers draw their own actions from a PCG of the same seed.

## Tests (`service_test.go`, 368 lines)

- Directed: `TestReserveConfirmFlow`, `TestExpiryByInjectedClock` (NotYet, then TooLate, then Expire with the fake clock), `TestCrashAfterCommitBeforeReply` (scripted crash after commit: state durable, `Flush` refused, a delivered `Confirm` lost, `Tick` applied while down, restart, outbox flushed, retried `Confirm` works), `TestHTTPBadRequestsAndDown` (400, 404, 200, 503), `TestListenLocalOnly` (one real socket).
- `TestInvUnderFaultRuns`: 150 seeds x 150 actions (drop 0.15, dup 0.15, MaxDup 2, reorder, crash probability 0.05 at after-commit plus direct `Crash`/`Restart`, `MaxCrashes` 3). After every action, on the persisted state: P1, P2 and `Inv`, and P3b (`ReleasedMatchesReturned` over every outbox row).
- `TestDifferentialAgainstCoreFold`: 100 seeds x 150 actions; the persisted state equals the fold of `core.Step` over `Log()` from `core.Init`, and the outbox rows equal the folded effects.
- Both fault tests count what they exercised and `t.Fatalf` if any counter is zero.

## Commands and output

```
$ source .nix/env.sh; go vet ./... && go test ./internal/uc2/... ./services/inventory/... -count=1
ok  	github.com/derangga/learn-formal-verification/internal/uc2/core	6.486s
ok  	github.com/derangga/learn-formal-verification/services/inventory	34.678s

$ go test ./services/inventory/ -count=1 -v   (earlier run, same code apart from one directed test's config)
--- PASS: TestReserveConfirmFlow (0.01s)
--- PASS: TestExpiryByInjectedClock (0.01s)
--- PASS: TestCrashAfterCommitBeforeReply (0.01s)
--- PASS: TestListenLocalOnly (0.00s)
    coverage: {dup:1304 drop:1327 lost:2524 crash:356 restart:297 tickDown:1008 reserved:325 confirmed:30 released:57 dedupe:190 tooLate:78 notYet:31 insufficient:213 replyDelivered:611}
--- PASS: TestInvUnderFaultRuns (14.85s)
    coverage: {dup:853 drop:893 lost:1847 crash:242 restart:209 tickDown:697 reserved:201 confirmed:24 released:36 dedupe:113 tooLate:29 notYet:16 insufficient:113 replyDelivered:362}
--- PASS: TestDifferentialAgainstCoreFold (7.77s)

$ go test ./... -count=1   (tail)
ok  	github.com/derangga/learn-formal-verification/internal/sim	0.007s
ok  	github.com/derangga/learn-formal-verification/internal/uc1/core	0.452s
ok  	github.com/derangga/learn-formal-verification/internal/uc2/core	4.531s
ok  	github.com/derangga/learn-formal-verification/mutants/uc1	57.324s
ok  	github.com/derangga/learn-formal-verification/services/inventory	17.139s
ok  	github.com/derangga/learn-formal-verification/services/payment	135.221s
```
(`dedupe` = rejections NotHeld or DuplicateId; `lost` = request copies delivered to a crashed service; `tickDown` = clock syncs issued while the service was down; counts are summed over each test's runs and come from the outbox rows and the sim trace.)

## Caveats

- (a) `synchronous=OFF`, and a "crash" is a clean close and reopen of the file: durable for a process crash, not for power loss or a crash in the middle of a transaction.
- (b) Delivery is in-process: `sim.Net` plus direct handler calls. A real socket appears only in `TestListenLocalOnly`.
- (c) Core's `up` flag is persisted and is what drops events; the crasher's down flag gates only the wire (`Lost`), `Flush`, and the crash budget. The two are set together by `Crash` and `Restart`.
- (d) A dropped-while-down direct HTTP request is still appended to `Log()`; Step maps it to a no-op, so the fold is unaffected. Requests lost on the wire are not logged.
- (e) The `Expire` timer is a client of the same wire (`Submit` of an `Expire` event); there is no in-service timer.
- (f) The whole state is loaded and rewritten per request. Fine for a handful of rows; it would not scale.
- (g) `confirmed:30` of 150 runs is low: random runs rarely land a `Confirm` before its `Due` for a `Held` record. The directed tests cover that path.

## Friction

- Failed iteration 1: `TestHTTPBadRequestsAndDown` called `Crash()` with a zero crash budget, which is refused (`MaxCrashes` 0), so the 503 check got 200. Fixed by giving that test `MaxCrashes: 1`.
- `go test ./services/...` needs a module cache; the sandbox has no network, so I used the existing one with `GOMODCACHE=/tmp/claude-1001/gomodcache GOPROXY=off`.
- Because the contract has a durable `up` flag and `Tick` applies while down, the service cannot just refuse requests while down (UC1 did). It must run `Step` for Tick and Restart. `apply` runs `Step` for every event and maps "was down and not Tick/Restart" to `ErrDown`.
- The UC1 `Net.Duplicate` bound is per original Send, so Go runs duplicate more than TLC's bound would. Same as UC1.

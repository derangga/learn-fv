# UC1 services: order and payment provider over outbox + HTTP

Start: 2026-11-22T12:03:00Z
End: 2026-11-22T12:08:00Z (approx; last `date -u` taken after the final test run was 12:07:27Z)

Package `services/payment` (one package, two service types). Pure Go, `modernc.org/sqlite` v1.62.0, `CGO_ENABLED=0`.

## Design

- `store.go`: `base` shared by both services. `apply(e, load, save)` is the whole service logic: refuse if down (`ErrDown`), open a transaction, load slot `o` into a `core.Init(N)` state, call `core.Step`, `save` the result and ledger/outbox rows, commit, then hand each `Wire*` effect to the transport hook and log the event. Core's own `OrderUp`/`ProvUp` stay true in the call; a down service is refused before Step, which is Step's rule D. An `o >= N` event runs Step (a no-op) and writes nothing.
- `order.go`: `OrderSvc` with its half of the slot (`Ord`) in `order.db`. `provider.go`: `ProvSvc` with `Prov` in `provider.db`, plus the `Issuer` interface (`SeededIssuer`, `ScriptIssuer`; default always Approve). The issuer is asked once per `/charge` request, only when the provider is up.
- `http.go`: chi routers, `POST` JSON `{"o":..,"a":..}`. Order: `/place /retry /refund /flush/charge /flush/refund /approved /declined`. Provider: `/charge /refund /flush/reply`. 200 returns the effects as JSON, 503 when crashed, 400 on bad JSON. `ListenLocal` serves on `127.0.0.1` only and refuses other hosts.
- `cluster.go`: single-threaded, deterministic driver. Cluster calls handlers **directly in-process** (`httptest` recorder, no sockets, no goroutines); `ListenLocal` is exercised by one real-socket test. `Wire*` effects go to `sim.Net[core.Effect]` via `Send`; `DeliverIndex(i)` / `Next()` take a copy out and POST it to the destination handler. `Delivery.Lost` (destination down) is dropped with no effect.
- Crash and restart: `sim.Crasher` decides; `Crash` closes the SQLite handle, `Restart` reopens the file (schema is `CREATE IF NOT EXISTS`). Crash point `AfterCommit = "after-commit"` is checked via `Crasher.ShouldCrash` after every applied request, so a crash lands between the outbox write and the flush (or between a delivery's commit and the next step).
- `Snapshot()` reads both files into a `core.State`; a crashed service's file is read through a temporary handle. `Log()` is the applied event sequence (Crash/Restart included); folding `core.Step` over it from `core.Init(N)` must equal Snapshot.

## Schema

order.db: `ord(o PK, status, amount)`, `outbox(o, kind, PK(o,kind))` with kind `charge` or `refund`; row present = flag true.
provider.db: `prov(o PK, rec, amt)`, `ledger(id AUTOINCREMENT, o, kind, amount)` (kind = core.Charge or core.Refund), `outbox(o, kind)` with kind `reply`. `ChargeCount` and `RefundCount` are not stored; they are counts of ledger rows, so P1 is checked on real rows.

## Commands and output

`go mod tidy` offline: updated go.mod (sqlite now direct, chi kept) but printed lookup errors for test-only deps of modernc.org/libc (`goabi0: module lookup disabled by GOPROXY=off`); build and tests work.

```
$ go vet ./...
(no output)
$ go test ./services/... -count=1 -v
--- PASS: TestHappyPathToPaid (0.01s)
--- PASS: TestRefundFlow (0.01s)
--- PASS: TestDeclineGoesFailed (0.00s)
--- PASS: TestCrashAfterCommitBeforeSend (0.01s)
--- PASS: TestDeliveryToCrashedProviderIsLost (0.00s)
--- PASS: TestHTTPBadRequests (0.00s)
--- PASS: TestListenLocalOnly (0.00s)
--- PASS: TestP1NoDoubleCharge (12.42s)
    payment_test.go:272: crashes=222 charged=34
--- PASS: TestDifferentialAgainstCoreFold (6.22s)
PASS
ok  	github.com/derangga/learn-formal-verification/services/payment	18.674s
$ just test   (tail)
ok  	github.com/derangga/learn-formal-verification/harness/conformance	9.051s
ok  	github.com/derangga/learn-formal-verification/internal/sim	(cached)
ok  	github.com/derangga/learn-formal-verification/internal/uc1/core	(cached)
ok  	github.com/derangga/learn-formal-verification/mutants/uc1	34.803s
ok  	github.com/derangga/learn-formal-verification/services/payment	26.797s
```

Fault runs (review round): 200 seeds x 150 steps (drop 0.15, dup 0.15, MaxDup 2, reorder, crash prob 0.08 + direct Crash/Restart, MaxCrashes 3 per service, seeded issuer declining 30%). After each step: P1 and P2a on ledger rows, `core.Inv` on Snapshot. Differential test: 100 seeds x 150 steps, Snapshot == fold of Step over the log. Both tests count what they exercised and `t.Fatalf` if any counter is zero:

```
TestP1NoDoubleCharge:   {dupDelivered:43 drops:152 crashOrder:494 crashProv:411 dedupe:71 declinedAtProv:56 declinedApplied:19 refundRows:8 refundOrderApplied:30 charges:120 paid:43}   (42.8s)
TestDifferentialAgainstCoreFold: {dupDelivered:16 drops:68 crashOrder:240 crashProv:210 dedupe:29 declinedAtProv:31 declinedApplied:11 refundRows:2 refundOrderApplied:9 charges:55 paid:19}   (33.2s)
ok  	github.com/derangga/learn-formal-verification/services/payment	76.066s
```
(`dedupe` = ChargeReqRecv with rec != NoRec; `paid` = PaymentApproved applied while AwaitingPayment. Counts are trace "crash" entries, summed over runs (the budget caps each service at 3 per run; scripted and direct crashes share it).) A directed test, `TestProviderCrashAfterCommitBeforeReply`, crashes the provider after it commits Approved + reply outbox, restarts, checks the reply row survived, flushes it and reaches Paid.

Line counts: see `wc -l services/payment/*.go` at the end of the run.

## Caveats stated

- (a) `synchronous=OFF` is only durable for the simulated process crash (a clean `Close`, then reopen). It does not model power loss or a crash in the middle of a transaction.
- (b) Service-to-service delivery is in-process: `sim.Net` plus direct handler calls. Real sockets appear only in `TestListenLocalOnly`.
- (c) `apply` rejects requests while down (`ErrDown`) before `Step`. This duplicates rule D's up check, because the services build `State` with both up flags true.
- (d) The issuer is consulted on every `ChargeReqRecv` (when the provider is up), even when `Step` ignores `d` because a record exists.
- Restart opens the file first; on failure it returns the error and the service stays down with the log unchanged.

## Friction

- Flush atomicity: a Flush commits the cleared flag and then hands the message to `Net.Send` in-process. A crash between those two (message lost with the flag cleared) is not reachable here, matching the TLA+ Flush event, which is atomic. The reachable crash is "after commit, before flush".
- Crash points are checked in the Cluster after each request, not inside the service, because the service has no hook between its own commit and the response.
- `Net.Duplicate` bound is per original Send (sim doc), so Go runs may duplicate more than TLC's DupMax.
- SQLite opened with `synchronous=OFF` for test speed (process-level close/reopen, no power loss modelled). Snapshot and Ledger per step open a temporary handle while a service is down, which dominates test time (about 12 s for 200 seeds).
- Snapshot returns `(core.State, error)` rather than a bare state.
- Charge count 34 in 100 differential runs is modest; random runs rarely reach Paid and Refunded together. The scripted tests cover those paths.

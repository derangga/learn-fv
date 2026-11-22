# UC1: replaying TLC traces against the Go payment service (y6a.9)

Start 2026-11-22 12:10:05 UTC, end 2026-11-22 12:17 UTC (about 7 min; about 3.5 min of that was TLC generating fixtures, twice). Best effort, as the brief says. Tool: TLC 2.18. Code: `harness/tlcreplay/` (`tlcreplay.go`, `tlcreplay_test.go`, `gen.sh`, `testdata/`). No TLA+ spec, service or core file was changed.

## How the traces were obtained

TLC 2.18 supports `-dumpTrace json <file>`: it writes the counterexample as a JSON array, one object per state, with every variable (`slots`, `orderUp`, `provUp`, `net`, `dup`, `crashes`, `retries`, `lastEvent`, `lastFx`). Bags and functions come out as JSON objects. The `net` and `dup` keys are TLA+ record values rendered as TLC strings, for example `"[o |-> 0, t |-> \"ChargeReq\", a |-> 5]"`, so the replay parses them with three regexes. No text-trace parsing was needed.

`harness/tlcreplay/gen.sh` (run with `source .nix/env.sh && go generate ./harness/tlcreplay`) runs TLC with `-noGenerateSpecTE -workers 1` on every `spec/tla/UC1_reach_*.cfg` (module `UC1`) and `spec/tla/UC1_buggy*.cfg` (module = cfg stem), accepts exit 12 (invariant) or 13 (action property), and writes `testdata/<reach_X|buggy|buggy_mN>.json` plus a `.violation` file with TLC's `Error: ... is violated.` line. Result: 21 traces, 42 files, about 170 KB, committed so the tests do not need TLC. Running the script twice gave byte-identical JSON (checked for the 15 reach traces and `buggy`; the M2a to M5 files were produced by the second run only). Bounds are the cfg bounds: N=2, Amounts={5}, DupMax=2, MaxCrashes=1, MaxRetries=2.

## Mapping: TLA+ action to Cluster call

The action comes from `lastEvent.kind`. Before each step the replay builds a `ScriptIssuer` script: the provider asks the issuer on every charge request it receives while up (`route` calls `Decide` before `apply`), so the script holds one `d` per `ChargeReqRecv` step whose pre-state has `provUp`.

| TLA+ action (`lastEvent.kind`) | Cluster call | Notes |
|---|---|---|
| `PlaceOrder(o,a)` | `PlaceOrder(o,a)` | |
| `RetryTimeout(o)` | `RetryTimeout(o)` | |
| `RefundOrder(o)` | `RefundOrder(o)` | |
| `FlushChargeReq(o)` | `FlushCharge(o)` | |
| `FlushRefundReq(o)` | `FlushRefund(o)` | |
| `FlushReply(o)` | `FlushReply(o)` | |
| `ChargeReqRecv(o,a,d)` | `DeliverIndex(i)`, i = any in-flight copy equal to `WireChargeReq(o,a)` | `d` from the ScriptIssuer script |
| `RefundReqRecv(o)` | `DeliverIndex(i)`, copy equal to `WireRefundReq(o)` | |
| `PaymentApproved(o)` | `DeliverIndex(i)`, copy equal to `WireApproved(o)` | |
| `PaymentDeclined(o)` | `DeliverIndex(i)`, copy equal to `WireDeclined(o)` | |
| `Drop` | `Drop(i)`, copy = the net key whose count fell by 1 | `lastEvent` has no message |
| `Duplicate` | `Duplicate(i)`, copy = the net key whose count rose by 1 | needs the sim bound lifted, see below |
| `Crash(svc)` | `Crash(svc)` | |
| `Restart(svc)` | `Restart(svc)` | |
| `ProvApplyCharge` (M3 only) | none | mutant-only action, reported as "not applied" |

A client or flush call on a service that TLA+ has down must return `ErrDown` (rule D: no-op); the replay accepts exactly that and nothing else.

What is compared after every step: `Cluster.Snapshot()` against the TLA+ `slots` (all nine fields of every order: status, amount, outCharge, outRefund, rec, chargeCount, refundCount, amt, outReply), `orderUp` and `provUp`; and `Cluster.InFlight()` as a multiset of (kind, o, a) against the TLA+ `net` bag, which is the message-identity mapping (a TLA+ message is a value, the sim holds copies, any copy with the same value is picked). Not compared: `dup`, `crashes`, `retries` (the Cluster does not expose them; TLC enforced them already), `lastFx` (wire effects show up in the net bag, `Charge`/`Refund` in the ledger counts) and the SQLite outbox rows beyond what `Snapshot` reads back.

## Results

Run: `go test ./harness/tlcreplay -count=1 -v` (also part of `go test ./harness/...` and `just harness`, both pass). Every test is deterministic: no clock, no seed-driven faults, scripted issuer, `t.TempDir()` databases.

### Reach witnesses (correct model): 15 of 15 replay with all states equal

`reach_crash` (1 step), `provdown` (1), `orderdown` (1), `persistednotsent` (2), `duplicate` (3), `replayflag` (3), `wiredeclined` (4), `paid` (5), `failed` (5), `replay` (5), `dupreplay` (5), `wirerefundreq` (7), `refundcount` (8), `refundfx` (8), `refunded` (6). In each: slots, up flags and the in-flight bag equal the TLA+ state after every step, and `core.Inv` holds on every service snapshot. This covers duplicate delivery, a drop-free replay, provider decline, a crash and the refund path. No reach trace restarts a service after a crash or drops a message, so those two mappings are exercised only by the code path, not by a replayed trace (see "How hard").

### Buggy traces (mutants M1 to M5) replayed on the correct service

For each trace the replay reports the first step where the service state or bag differs from the buggy model, then keeps applying the remaining steps and checks the violated property on the service's own trajectory. Before that, the property checker is run on the TLA+ trace itself and must flag it (else it would prove nothing).

| Trace | TLC verdict | First divergence (step, TLA+ action) | Service vs buggy model | Property on the service |
|---|---|---|---|---|
| `buggy` (M1) | `Invariant NoDoubleCharge` | 5, `ChargeReqRecv(o=0,a=5,d=Approve)` (second request) | `chargeCount` 1 (service) vs 2 (model) | not violated (also the ledger has one Charge) |
| `buggy_m2a` | `Action property RefundedOnlyFromPaid` | 1, `RefundOrder(o=0)` | status `None` (service) vs `Refunded` with `outRefund` (model) | not violated (clauses a and b of P2b) |
| `buggy_m2b` | `Invariant RefundNeverExceedsCharge` | 10, `RefundReqRecv(o=0)` | `refundCount` 1 vs 2 | not violated |
| `buggy_m3` | `Invariant NoDoubleCharge` | 4, first `ChargeReqRecv(Approve)` | service records the charge at once (`rec=Approved`, count 1), the model only adds to its mutant-only `pending` | not violated; the two `ProvApplyCharge` steps (6, 7) have no Cluster call and are skipped |
| `buggy_m4` | `Action property TerminalStable` | 8, `PaymentApproved(o=0)` | status `Refunded` (service) vs `Paid` (model) | not violated |
| `buggy_m5` | `Action property PinProvRecStable` | 5, `ChargeReqRecv(o=0,a=5,d=Approve)` | `rec` stays `Declined` (service) vs `Approved` (model) | not violated |

The first divergence is always the step that exercises the mutated branch, which is what one wants from a replay. The service is correct, so in all six the property TLC reported is not violated. The action properties are checked on the service by transition predicates in `Violation` (P2b a and b, P3, A13), not by running TLC on the service, so they restate the contract rather than reuse the TLA+ definitions. `TestReplayDetectsTamper` changes one field of a reach trace and requires the replay to flag exactly that step, so "all equal" is not vacuous.

## How hard was it

Time: about 7 min wall for this piece, of which TLC fixture generation was about 3.5 min (21 runs at about 5 s plus JVM start; run twice because the first script rejected exit code 13). Writing the replay and tests took one pass; the first full run passed.

What made it easy: `-dumpTrace json` exists in TLC 2.18 and gives complete states; the UC1 spec already carries `lastEvent` with the event fields, so action identification needed no inference; the Cluster already exposes `InFlight`, `DeliverIndex`, `Drop`, `Duplicate`, `Crash`, `Restart` and `Snapshot`, which map one to one.

Friction and modelling mismatches:

- Bag against copies. TLA+ `net` is a function from message value to count; the sim holds individual copies. Mapping by value (any copy with an equal body) is enough because every service action depends only on the value. `Drop` and `Duplicate` carry no message in `lastEvent`, so the message is recovered from the net diff.
- DupMax per value against per original. TLA+ bounds duplicates per message value (`dup[m] < DupMax`), the sim per original send (`Faults.MaxDup`). Replaying a value-bounded trace can ask the sim for a duplicate of a copy whose original is already at its bound (for example a duplicate of a duplicate, or of a second flush of the same value). The replay sets `MaxDup` and `MaxCrashes` very high and relies on TLC having enforced the real bounds. So the replay does not test the sim bound; and a service configured with `MaxDup = DupMax` is strictly more restrictive than the model, which is a modelling gap, not a bug.
- The issuer is asked on every charge request, not only the first. TLA+ draws `d` on every `ChargeReqRecv` but it only matters at `NoRec`; the service calls `Decide` on every charge delivery while up. The ScriptIssuer script therefore has one entry per such step (including replays and the M5 re-request), and none for deliveries to a down provider (the route does not draw then). This couples the script to the trace shape; any extra or missing draw would shift every later decision.
- Crash. TLA+ `Crash` is an action; in the service a crash normally comes from a crash point after commit, `Cluster.Crash` is the direct hook and works. Rule D matches: calls on a crashed service return `ErrDown`, deliveries to it are consumed (`Lost`). `Restart` reopens the SQLite file. The 15 reach traces contain a crash only in `reach_crash` (one step, no restart), so crash-then-recover with in-flight messages is not exercised by a TLC witness. A trace aimed at that would need a new reach cfg.
- Flush atomicity. A flush is one step in TLA+ (clear flag and put the message on `net`); in the service it is one HTTP call, one SQLite transaction, then `send` after commit. In the single-threaded Cluster the two are indistinguishable, so no mismatch showed. The crash point between commit and send (`AfterCommit`) exists in the service but not in the model: a crash there would lose a wire message that the model has already queued. The replay never uses that point, so it cannot see this gap.
- State not visible. The Cluster does not expose `dup`, `crashes`, `retries` or `lastFx`, so those are not compared. Wire effects are checked indirectly through the net bag.
- Mutant-only actions. M3 adds `ProvApplyCharge` and a `pending` field. The service has neither; the step is reported as "not applied" and counts as a divergence. This is the expected outcome for a race-window mutant, not a replay defect.
- Only the first counterexample per cfg. TLC stops at the first violation, so each buggy cfg gives one short trace (2 to 10 steps). Longer or all counterexamples would need `-continue` or simulation mode.

Verdict: cheap, because the model and the service share the event vocabulary and the Cluster was built with injection hooks. The remaining gaps are structural (per-value against per-original duplication bound, the after-commit crash point, hidden counters), and are listed above, not hidden by the replay.

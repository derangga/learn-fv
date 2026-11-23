# UC1 in TLA+ (TLC): lossy network, duplication, reordering, crash/restart

Date: 2026-11-22. Authoring start 10:07:12 UTC, end about 11:20 UTC (about 73 min, of which about 62 min were the UC1.cfg run). Tool: TLC 2.18 (OpenJDK 21.0.13.1), machine as in `phase0-tlc.md` (2 cores, about 1.9 GB RAM).

Status: **PARTIAL. The spec parses, every reachability witness and the M1 mutant behave as required, but TLC did not finish UC1.cfg at the contract bounds.** I stopped it after 62 min with 9.08 M distinct states and a still-growing queue (a wall, see "Result" and "Friction"). No `ALL CLEAR` claim is made for UC1.cfg at N=2. A complete pass exists only for a smaller bound that is NOT the contract's (N=1, scratch cfg), reported separately and labelled.

Update 2026-11-23: the user approved **N = 1 as the checked bound** and N = 2 as a recorded wall. `spec/tla/UC1.cfg` now has `N = 1` (other bounds unchanged) and is what `just check-tla` runs. The N = 2 contract bounds are kept unchanged in `spec/tla/UC1_wall_n2.cfg`, which `check-tla` skips. See "Checked bound (N = 1)" below. The N = 2 sections that follow are the original record; where they say `UC1.cfg` they mean the N = 2 file, now `UC1_wall_n2.cfg`.

## What was built

| File | Content |
|---|---|
| `spec/tla/UC1.tla` | Module `UC1`. Nine variables `slots, orderUp, provUp, net, dup, crashes, retries, lastEvent, lastFx`, `vars` = all nine. `Step(s,e)` returns `[state, fx]` with every event of the table (A1 to A11), rule D and frame F. Actions `ClientAction` (PlaceOrder, RetryTimeout, RefundOrder), `OutboxFlush` (the three Flush events), `Deliver` (any message in `net`, remove one copy, run `Step`; `ChargeReqRecv` explores both `d`), `Drop`, `Duplicate` (at most `DupMax` per message), `Crash`, `Restart`. All of them go through `DoStep(e, net0)`, which runs `Step`, sets `lastEvent`/`lastFx` and calls `AddWire(fx)`. `Spec == Init /\ [][Next]_vars`. |
| `spec/tla/UC1.cfg` | `SPECIFICATION Spec`; INVARIANT `TypeOK, Inv, NoDoubleCharge, RefundNeverExceedsCharge`; PROPERTY `RefundedOnlyFromPaid, TerminalStable` and the 13 pins `PinPlaceOrder ... PinProvRecStable`. Bounds below. No CONSTRAINT, no SYMMETRY. |
| `spec/tla/UC1_buggy.tla`, `UC1_buggy.cfg` | Mutant M1. |
| `spec/tla/UC1_reach_<what>.cfg` (11 files) | Reachability witnesses, reuse `UC1.tla`; each names a deliberately false invariant `Reach*` defined at the end of `UC1.tla`. |

Names as the contract: invariants `TypeOK`, `Inv`, `NoDoubleCharge` (P1), `RefundNeverExceedsCharge` (P2a); action properties `RefundedOnlyFromPaid` (P2b a to d), `TerminalStable` (P3 with amount), `PinPlaceOrder`, `PinRetryTimeout`, `PinFlushChargeReq`, `PinPaymentApproved`, `PinPaymentDeclined`, `PinRefundOrder`, `PinFlushRefundReq`, `PinChargeReqRecv`, `PinFlushReply`, `PinRefundReqRecv`, `PinCrashRestart`, `PinLegalTransitions`, `PinProvRecStable`. Each pin restates its Result from section 4 independently of `Step` (full equality of the next `S` and of `lastFx'`, including the "any other case: F" and rule D cases). Counters are `Int` in `Step`; `TypeOK` (tightened after review) types `amount` and `amt` as `{0} \cup Amounts`, `chargeCount`/`refundCount` as `Nat` (deliberately not 0..1, so `TypeOK` does not restate P1/P2a, which `Inv`/`NoDoubleCharge` check), statuses and records in their sets, and bounds the bags (`net` by `MaxRetries + 1 + 2*DupMax`, a derived bound used only by `TypeOK`).

Design choices (nothing in the contract settles them): `lastEvent` is a record with `kind` (`Init`, the 11 event kinds, `Drop`, `Duplicate`); `Drop`/`Duplicate` set `lastFx = <<>>`, so a stale effect never lingers. Client events (PlaceOrder, RetryTimeout, RefundOrder) and the three Flush events are enabled in every state, also when `Step` makes them a no-op (frame F, rule D); this keeps the "any other case: F" clauses of the pins exercised. `RetryTimeout(o)` consumes the per-order budget `retries[o] < MaxRetries` whatever the order status. `Crash(svc)` needs the service up and `crashes[svc] < MaxCrashes`; `Restart(svc)` needs it down.

## Bounds (`spec/tla/UC1.cfg`, exactly UC1.md section 6 Q11)

`N = 2`, `Amounts = {5}`, `DupMax = 2`, `MaxCrashes = 1` (per service), `MaxRetries = 2` (per order), both `d` values explored. No CONSTRAINT, no SYMMETRY, no assumption added. Not bounds, but run settings: `JAVA_TOOL_OPTIONS` extended with `-Xmx700m` and `-workers 2` (default heap was 274 MB).

## Result at the contract bounds: no completion (wall)

Command (stopped by me, so no summary block):

```bash
source .nix/env.sh
export JAVA_TOOL_OPTIONS="$JAVA_TOOL_OPTIONS -Xmx700m"
mkdir -p $TMPDIR/uc1
tlc -workers 2 -metadir $TMPDIR/uc1 -config spec/tla/UC1.cfg spec/tla/UC1.tla
```

Start 10:16:37 UTC, last progress line (verbatim), stopped about 11:18 UTC (62 min wall):

```text
Progress(16) at 2026-11-22 11:17:41: 80,850,928 states generated (1,092,014 s/min), 9,079,945 distinct states found (104,777 ds/min), 4,644,890 states left on queue.
```

- No `Error:` line in the whole output (56 progress lines): no invariant, pin, `TypeOK` or deadlock violation among the 80.9 M generated states. This is "no violation found yet", not "verified".
- The BFS was still on level 16 for the last 40 min (level 15 alone is above 50 M generated). Final distinct states, depth and wall time: not recorded, the run did not finish. The queue grew 3.3 M to 4.6 M over the last 30 min at about 100 K distinct states/min.
- The first attempt (10:10 to 10:13) produced no output because the process was killed with its shell (my tooling mistake, not a spec result); it is not counted as a failed iteration.

### Context: same spec, N = 1 (NOT the contract bound, complete)

Scratch cfg `$TMPDIR/n1/UC1.cfg` = `UC1.cfg` with `N = 1`, nothing else changed (not committed, not a replacement for the N=2 run):

```bash
sed 's/N = 2/N = 1/' spec/tla/UC1.cfg > $TMPDIR/n1/UC1.cfg
tlc -noGenerateSpecTE -workers 1 -metadir $TMPDIR/n1m -config $TMPDIR/n1/UC1.cfg spec/tla/UC1.tla
```

```text
Model checking completed. No error has been found.
  Estimates of the probability that TLC did not check all reachable states
  because two distinct states had the same fingerprint:
  calculated (optimistic):  val = 7.5E-7
  based on the actual fingerprints:  val = 6.9E-8
13071033 states generated, 1156996 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 34.
The average outdegree of the complete state graph is 1 (minimum is 0, the maximum 18 and the 95th percentile is 10).
Finished in 19min 35s at (2026-11-22 11:11:46)
```

(1 worker, 250 MB heap, shared the 2 cores with the N=2 run, so the time is inflated.) All invariants and all 15 action properties held for one order. Two orders share the crash budget and the clock but not the messages, so N=2 is roughly the square of this. The figure "order 10^11 to 10^12 distinct states" is an UNMEASURED estimate (a back-of-envelope square of the N=1 count, not a TLC result): out of reach on this machine, not a modelling accident I can prune away.

## Checked bound (N = 1), approved 2026-11-23

Decision: the user chose "N = 1 checked, N = 2 wall" from the options in "Friction and walls". No other bound, CONSTRAINT, SYMMETRY or VIEW was added. The reach witnesses and the buggy cfgs keep N = 2 because TLC finds their violations quickly there.

Bounds (`spec/tla/UC1.cfg`): `N = 1`, `Amounts = {5}`, `DupMax = 2`, `MaxCrashes = 1` per service, `MaxRetries = 2` per order.

Command and output (2 workers, default 274 MB heap, 2026-11-23):

```bash
tlc -noGenerateSpecTE -workers auto -metadir $TMPDIR/n1/meta2 -config UC1.cfg UC1.tla
```

```text
Model checking completed. No error has been found.
  Estimates of the probability that TLC did not check all reachable states
  because two distinct states had the same fingerprint:
  calculated (optimistic):  val = 7.5E-7
  based on the actual fingerprints:  val = 3.9E-8
13071033 states generated, 1156996 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 34.
The average outdegree of the complete state graph is 1 (minimum is 0, the maximum 18 and the 95th percentile is 10).
Finished in 05min 01s at (2026-11-23 01:06:59)
```

What N = 1 does not check: anything that needs two orders at once. That covers two orders' messages interleaved in the network, two orders sharing one crash budget, and rule D for one order while another order's messages are in flight. The Bend laws have no bound on `N`, and the Go tests run 2 or 3 slots, so those tools still cover two orders. TLC does not.

## Non-vacuity: reachability witnesses (TLC must violate each)

There are 15 witnesses. After the TypeOK tightening all of them and `UC1_buggy` were re-run: the verdicts, distinct states and depths of the first 11 are unchanged, and `UC1_buggy` still gives `Error: Invariant NoDoubleCharge is violated.`, 6-state trace, 2340 distinct, depth 6. A 150 s run of UC1.cfg with the tightened `TypeOK` showed no error through 1,791,168 generated states (Progress(11)); it is a partial run only. Command per witness (`-noGenerateSpecTE` only stops TLC writing trace specs into `spec/tla`):

```bash
tlc -noGenerateSpecTE -workers 1 -metadir $TMPDIR/r -config spec/tla/UC1_reach_<what>.cfg spec/tla/UC1.tla
```

| cfg | Witness | Violation line (verbatim) | Distinct states | Depth |
|---|---|---|---|---|
| `UC1_reach_paid` | an order reaches `Paid` | `Error: Invariant ReachPaid is violated.` | 2223 | 6 |
| `UC1_reach_refunded` | an order reaches `Refunded` | `Error: Invariant ReachRefunded is violated.` | 6948 | 7 |
| `UC1_reach_failed` | an order reaches `Failed` | `Error: Invariant ReachFailed is violated.` | 2268 | 6 |
| `UC1_reach_replay` | a delivered charge request finds `rec = Approved`, no `Charge` effect (a true provider replay) | `Error: Invariant ReachReplay is violated.` | 2340 | 6 |
| `UC1_reach_replayflag` | `outReply` set while `rec # NoRec` (also true right after a first request, so weaker than `replay`) | `Error: Invariant ReachReplayFlag is violated.` | 148 | 4 |
| `UC1_reach_dupreplay` | that replay while every `retries[o] = 0`: the second request must come from `Duplicate` | `Error: Invariant ReachDupReplay is violated.` | 2340 | 6 |
| `UC1_reach_duplicate` | a `Duplicate` step | `Error: Invariant ReachDuplicate is violated.` | 151 | 4 |
| `UC1_reach_crash` | a crash (`crashes` incremented) | `Error: Invariant ReachCrash is violated.` | 14 | 2 |
| `UC1_reach_provdown` | provider down | `Error: Invariant ReachProvDown is violated.` | 15 | 2 |
| `UC1_reach_orderdown` | order service down | `Error: Invariant ReachOrderDown is violated.` | 14 | 2 |
| `UC1_reach_refundcount` | provider `refundCount > 0` (A10 fired) | `Error: Invariant ReachRefundCount is violated.` | 55119 | 9 |
| `UC1_reach_refundfx` | a `Refund` effect in `lastFx` | `Error: Invariant ReachRefundFx is violated.` | 55119 | 9 |
| `UC1_reach_wirerefundreq` | a `WireRefundReq` effect in `lastFx` | `Error: Invariant ReachWireRefundReq is violated.` | 20250 | 8 |
| `UC1_reach_wiredeclined` | a `WireDeclined` effect in `lastFx` | `Error: Invariant ReachWireDeclined is violated.` | 638 | 5 |
| `UC1_reach_persistednotsent` | `outCharge` pending while the order service is down | `Error: Invariant ReachPersistedNotSent is violated.` | 27 | 3 |

All exit code 12. "Duplicate delivery" is covered by `dupreplay` (a request delivered a second time after one `Duplicate`, no retry involved).

## Mutant M1 (`UC1_buggy`)

How: `UC1_buggy.tla` is a copy of `UC1.tla` with the module name changed and the `ChargeReqRecv` branch of `Step` reordered so that `d = Approve` is tested before `rec` and no longer looks at it (adds 1 to `chargeCount`, emits `Charge` every time). `diff spec/tla/UC1.tla spec/tla/UC1_buggy.tla` shows only the header comment, the module line and that branch (the pins and reach definitions are unchanged). Same bounds as UC1.cfg. `UC1_buggy.cfg` has `INVARIANT NoDoubleCharge` and `INVARIANT Inv` only.

```bash
tlc -noGenerateSpecTE -workers 1 -metadir $TMPDIR/b -config spec/tla/UC1_buggy.cfg spec/tla/UC1_buggy.tla
```

```text
Error: Invariant NoDoubleCharge is violated.
...
9804 states generated, 2340 distinct states found, 1670 states left on queue.
The depth of the complete state graph search is 6.
Finished in 05s at (2026-11-22 10:50:55)
```

Trace length 6 states: `PlaceOrder`, `Flush(FlushChargeReq)`, `Duplicate`, `Deliver` (ChargeReqRecv Approve), `Deliver` (second ChargeReqRecv Approve), ending with `chargeCount = 2` for order 0. Exit 12. Extra check (scratch cfg with `PROPERTY PinChargeReqRecv` instead of the invariants): `Error: Action property PinChargeReqRecv is violated.`, 2340 distinct states, same depth 6, so the A8 pin is not vacuous either. M2a to M5 are not part of this task.

## Timing

Hyperfine for UC1.cfg: not run. One run takes over 30 s by orders of magnitude and does not finish, so there is no run to time. Cold and warm: not recorded (the 62 min partial run is the only measurement). Reach and buggy runs are 4 to 6 s each, JVM start-up included (single `time` of the first buggy run: real 6.1 s); not benchmarked with hyperfine.

## Ambiguities (most literal reading taken)

0. Rule D has two halves (service down, `o` out of range). TLA+ only generates `o` in `OrdIds` (actions quantify over `OrdIds` and `MsgSet`), so the out-of-range half of rule D is not exercised by TLC; the Go and Bend work covers it. `Step` itself does implement it.

1. UC1.md says client events and `Flush*` are events of `Step`, but not when an action may fire. I enabled them in all states (no-ops included). This costs states (every `lastEvent` variant is a distinct state) but removes any silent pruning.
2. `RetryTimeout` budget `MaxRetries` is "per order"; I count every fired timeout against it, also when `Step` makes it a no-op.
3. `Duplicate` bound `DupMax` is per distinct message value `m` over the whole run (counter `dup[m]`), not per copy in flight.
4. `lastEvent` for `Drop`/`Duplicate` is `[kind |-> ...]` with no message field; the contract only needs a `kind` tag.
5. P2b (c) reads `st(s,o) = Refunded` on the PRE-state, as written; implemented with pre-state `S`.
6. Replay witness: the contract wording "`outReply` set while `rec # NoRec`" is also true after the first request, so I added `ReachReplay` (needs a `ChargeReqRecv` that produced no `Charge`) and `ReachDupReplay`.

## Authoring effort

- Start 10:07:12 UTC, end about 11:20 UTC. Wall of the time includes about 62 min of waiting for the UC1.cfg run and about 19 min for the N=1 scratch run (in parallel).
- AI iterations on the spec: 1 write, 1 syntax/precedence fix of `PinCrashRestart` (applied before the first run).
- Failed iterations (failed model check on UC1.cfg or parse/semantic error): 0. The spec parsed and ran first time; the first run was lost to my shell handling, not a failed check. Stop rule (2 h or 15 failed iterations) was not reached; the wall is the state space.
- Size: `UC1.tla` 438 lines, `UC1.cfg` 26 lines, `UC1_buggy.tla` 441 lines, 12 other small cfgs.

## Friction and walls

- **State-space wall at the contract bounds.** Cause: two orders, a message bag with up to `MaxRetries + 1 + 2*DupMax` copies per message, `dup` counters, the crash and retry budgets, and `lastEvent`/`lastFx` kept in the state (the contract needs them). Even N=1 is 1.16 M states, depth 34. TLC spills to disk (`MSBDiskFPSet`, `DiskStateQueue`); the throughput fell from 1.5 M to 0.1 M distinct states/min. Options for the user (none applied, all would change bounds or add pruning, which needs approval): a symmetry set on `OrdIds` (halves N=2 at best), N=1 as the checked bound, a smaller `DupMax`/`MaxRetries`, or a `VIEW` that drops `lastEvent`/`lastFx` (not sound for the action properties as written). A bigger machine would also help (this one has 1.9 GB RAM and 2 cores).
- A TLC run started with `&` in the shell dies when the tool call ends; it must run as the foreground command of a background task.
- `tlc` by default writes `*_TTrace_*.tla`/`.bin` trace specs next to the spec on a violation; use `-noGenerateSpecTE` or they land in `spec/tla` (I deleted the one my first buggy run made).
- `java` is not visible to `ps` inside the sandbox, so progress is read from the output file.

## Log entry (for experiment-log.md)

- Date and time: 2026-11-22, about 10:07 to 11:20 UTC.
- Tool: TLA+ (TLC 2.18, OpenJDK 21.0.13.1).
- Use case: UC1.
- What was done: `UC1.tla` (nine variables, `Step` A1 to A11 with rule D and frame F, lossy network with drop, duplicate, reorder, crash/restart), `UC1.cfg` at the contract bounds, 11 reachability cfgs, mutant M1 `UC1_buggy`.
- Bounds (TLC only), state count, distinct states, wall time: `N=2, Amounts={5}, DupMax=2, MaxCrashes=1 per service, MaxRetries=2 per order`. UC1.cfg did not finish: stopped after 62 min at 80,850,928 generated, 9,079,945 distinct, 4,644,890 on queue, level 16, no violation seen (wall). Context only, N=1: 13,071,033 generated, 1,156,996 distinct, depth 34, 19 min 35 s, no error.
- Authoring time (spec or proof), AI iterations and how many, failed iterations: about 15 min to write plus 1 fix; 2 AI iterations; 0 failed iterations. The rest was waiting on TLC.
- Machine time (hyperfine), cold: not recorded (UC1.cfg does not finish).
- Machine time (hyperfine), warm: not recorded.
- Result: not a pass at the contract bounds. All 11 witnesses violated as required; M1 violates `NoDoubleCharge` in a 6-state trace; N=1 passes all properties.
- Size (lines): `UC1.tla` 438, `UC1.cfg` 26, `UC1_buggy.tla` 441.
- Friction or walls hit: state-space wall at N=2 (above); shell-backgrounded TLC dies with the tool call; TTrace files written into `spec/tla`.
- Details: `docs/results/uc1-tla.md`.

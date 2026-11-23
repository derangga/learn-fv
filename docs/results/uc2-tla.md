# UC2 in TLA+ (TLC): stock reservation with lossy network, duplicates, reorder, crash/restart, logical clock

Date: 2026-11-23. Authoring start about 03:30 UTC, end about 05:25 UTC (about 115 min, of which most was TLC waiting). Tool: TLC 2.18 (OpenJDK 21), machine as in `phase0-tlc.md` (2 cores, about 1.9 GB RAM).

Status: **PARTIAL. The spec, the reachability witnesses and mutant M1 behave as required, but TLC does not finish the contract bounds (60 min measured wall) of `properties/UC2.md` section 6 item 8 on this machine.** `spec/tla/UC2.cfg` holds the exact contract bounds, unchanged. **`just check-tla` will not finish on `UC2.cfg` until the user approves a bound.** Smaller bounds are proposed in `spec/tla/UC2_proposed.cfg` and `UC2_proposed_dup.cfg` (both labelled pending user approval; `just check-tla` skips `*_proposed*` (justfile)). When the user approves one, the swap is done as in UC1 (`experiment-log.md` 4.14): the approved constants move into `UC2.cfg` and the contract bounds into a `UC2_wall_*.cfg`. No "verified at the contract bound" claim is made anywhere in this file.

## What was built

| File | Content |
|---|---|
| `spec/tla/UC2.tla` (428 lines) | Module `UC2`. Ten variables `stocks, res, up, clock, net, made, crashes, emitted, lastEvent, lastFx`. `Step(s,e)` returns `[state, fx]` with S0 to S9 (`Reserve`, `Confirm`, `Expire` are the S2 to S7 operators). Actions: `Send(m)`, `Drop(m)`, `Duplicate(m)`, `Deliver(m)` (all over `MsgSet`), `Tick`, `Crash`, `Restart`, plus a stutter disjunct. `DoStep(e, net0)` runs `Step`, sets `lastEvent`/`lastFx` and logs `FxReleased` into `emitted`. `Spec == Init /\ [][Next]_vars`. |
| `spec/tla/UC2.cfg` | The contract bounds (below). INVARIANT `TypeOK, NonNegativeAvailable, Conservation, ExpiredReturnedOnce, ReleasedMatchesReturned, ConfirmedBeforeDue, CountersMatchRecords, UniqueIdsKnownSku`; PROPERTY `ExpiredNeverConfirmed, NoOversell, ConfirmOnlyBeforeDue, PinDown, PinTick, PinReserveOk, PinReserveRejected, PinConfirmOk, PinConfirmRejected, PinExpireOk, PinExpireRejected, PinCrash, PinRestart, FieldsStable`. No CONSTRAINT, no SYMMETRY, no VIEW. |
| `spec/tla/UC2_proposed.cfg`, `UC2_proposed_dup.cfg` | PROPOSED smaller bounds, pending user approval, same properties. |
| `spec/tla/UC2_buggy.tla`, `UC2_buggy.cfg` | Mutant M1 (`diff UC2.tla UC2_buggy.tla` shows the header and the one Confirm guard). Contract bounds. |
| `spec/tla/UC2_reach_*.cfg` (30 files) | Reachability witnesses over `UC2.tla`; each names a deliberately false invariant `Reach*` at the end of `UC2.tla`. |

`DupFollowsFromPins` (S11) is derived from S2 to S7 and is not checked in TLA+ (the contract says so); the spec carries a comment.

Counters (`total, available, reserved, sold`) are `Int`; `TypeOK` types them `Int`, not `Nat` and not `0..Total`, so it does not restate P1 or P2. Each pin restates its S-row independently of `Step` (full equality of `S'` and `lastFx'`). `lastEvent` is a record with `kind` (`Init`, `Send`, `Drop`, `Duplicate`, `Tick`, `Crash` (extra field `lost`), `Restart`, and the delivered message itself for `Reserve`/`Confirm`/`Expire`).

## Bounds

Contract (UC2.md section 6 item 8, `UC2.cfg`): `Ids = 1..3`, `EvSkus = {0, 1}` (stock exists for sku 0 only; sku 1 events get `UnknownSku`), `Qtys = 1..3`, `Ttls = 1..2`, `Total = 3`, `MaxClock = 4`, `MaxCrashes = 1`, `MaxCopies = 2` (each message delivered at most twice), drop and reorder always possible. That is 42 distinct messages (36 Reserve, 3 Confirm, 3 Expire).

**Proposed, pending user approval (`UC2_proposed.cfg`, NOT approved):** `Ids = {1, 2}`, `EvSkus = {0}`, `Qtys = {1, 2}`, `Ttls = {1}`, `Total = 2`, `MaxClock = 2`, `MaxCrashes = 1`, `MaxCopies = 1` (no duplicate delivery). 8 messages.

Run settings, not bounds: `-workers 2`, default heap.

## Result at the proposed bound (`UC2_proposed.cfg`)

```bash
source .nix/env.sh
hyperfine --runs 1 --warmup 0 --show-output "tlc -noGenerateSpecTE -workers 2 -metadir $TMPDIR/hfm -config spec/tla/UC2_proposed.cfg spec/tla/UC2.tla"
```

```text
Model checking completed. No error has been found.
  Estimates of the probability that TLC did not check all reachable states
  because two distinct states had the same fingerprint:
  calculated (optimistic):  val = 1.6E-6
  based on the actual fingerprints:  val = 2.4E-7
16640898 states generated, 2055926 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 20.
The average outdegree of the complete state graph is 1 (minimum is 0, the maximum 18 and the 95th percentile is 6).
Finished in 05min 48s at (2026-11-23 05:01:04)
  Time (abs ≡):        348.943 s               [User: 658.117 s, System: 2.874 s]
```

One hyperfine run, cores otherwise idle (a cold run; more runs would cost 6 min each). All 8 invariants and all 14 properties held. Re-run after the cfg move (2026-11-23 06:31, `-workers 2`, nothing else running):

```text
Model checking completed. No error has been found.
16640898 states generated, 2055926 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 20.
Finished in 05min 32s at (2026-11-23 06:31:29)
```

An earlier `just check-tla` (before the cfg move, when `UC2.cfg` held this bound) printed `check-tla: 3 spec(s) passed`. After the move `just check-tla` runs the contract `UC2.cfg` and will not finish until a bound is approved (the justfile skips `*_proposed*`).

### What the proposed bound does not check

- Duplicate delivery (`MaxCopies = 1` in `UC2_proposed.cfg`): a Reserve/Confirm/Expire delivered twice and the "Expire rejected `NotHeld` after a duplicate" case are not covered by that cfg. Duplicate delivery is covered by a second proposed cfg, `spec/tla/UC2_proposed_dup.cfg` (pending approval; `Ids={1}, EvSkus={0}, Qtys={1}, Ttls={1,2}, Total=1, MaxClock=3, MaxCrashes=1, MaxCopies=2`):

```bash
tlc -noGenerateSpecTE -workers 2 -metadir $TMPDIR/m -config spec/tla/UC2_proposed_dup.cfg spec/tla/UC2.tla
```

```text
Model checking completed. No error has been found.
2037539 states generated, 312995 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 21.
Finished in 41s at (2026-11-23 06:25:55)
```

All invariants and properties held. It has one id, so it checks no interplay of two records.
- `EvSkus = {0}`: no event for an unknown sku, so `UnknownSku` and the sku frame are never exercised at the checked bound. The witness `UC2_reach_unknownsku` (contract bounds) shows the branch is reachable in the spec.
- `Ttls = {1}`, `MaxClock = 2`: expiry boundaries only for ttl 1; ttl 2 and clocks 3 and 4 are not reached. `Total = 2`, `Qtys = 1..2`: at most two concurrent holds; a third record and `qty = 3` are not checked.
- Two ids: A2 uniqueness is exercised on two records only.
- `BadRequest` (`qty = 0` or `ttl = 0`): **not reachable even at the contract bounds**, because section 6 item 8 gives `qty` in 1..3 and `ttl` in 1..2. `Step` implements it and the pins define it, but TLC never fires it. Go and Bend cover it (like UC1's rule D, out-of-range half).
- Crash is generated only while up and Restart only while down, so the "already down" half of S8, the "already up" half of S9 and the Crash case of `PinDown` are not exercised.

Witnesses that matter for UC2 (an oversell attempt `qty = available + 1` rejected `InsufficientStock`, `DuplicateId`, `TooLate`, `NotYet`, Confirm and Expire accepted) also hit **at the proposed bound** (scratch cfgs = UC2_proposed.cfg constants plus one `Reach*` invariant, `workers 1`):

```text
ReachInsufficient    Error: Invariant ReachInsufficient is violated.    2277 distinct
ReachOversellPlusOne Error: Invariant ReachOversellPlusOne is violated. 2277 distinct
ReachDuplicateId     Error: Invariant ReachDuplicateId is violated.     2266 distinct
ReachConfirmTooLate  Error: Invariant ReachConfirmTooLate is violated.  4718 distinct
ReachExpireNotYet    Error: Invariant ReachExpireNotYet is violated.    1391 distinct
ReachExpireOk        Error: Invariant ReachExpireOk is violated.        6521 distinct
ReachConfirmOk       Error: Invariant ReachConfirmOk is violated.       943 distinct
ReachReserveExact    Error: Invariant ReachReserveExact is violated.    58 distinct
ReachConfirmNotHeld  Error: Invariant ReachConfirmNotHeld is violated.  48171 distinct
ReachExpireNotHeld   Error: Invariant ReachExpireNotHeld is violated.   15009 distinct
```

## Wall at the contract bounds (measured)

Command (`UC2.cfg` is the contract cfg; a background run, killed by `timeout 3600`; nothing else ran in parallel; `-workers auto` = 2 cores; default heap, TLC spills to disk):

```bash
timeout 3600 tlc -noGenerateSpecTE -workers auto -metadir $TMPDIR/w60 -config spec/tla/UC2.cfg spec/tla/UC2.tla
```

Start 05:25:07 UTC, stopped 06:25:08 UTC (60 min wall, exit 124 from `timeout`, so no summary block). Last progress line, verbatim:

```text
Progress(8) at 2026-11-23 06:24:12: 80,574,460 states generated (1,425,445 s/min), 25,051,664 distinct states found (395,222 ds/min), 23,427,502 states left on queue.
```

- Level 8 (BFS depth) after 60 min, 80.6 M generated, 25.05 M distinct, 23.4 M still on the queue (93 percent of the distinct states are unexplored).
- No `Error:` line in the whole output (60 progress lines): no invariant, property or TypeOK violation among the states checked. This is "no violation found yet", not "verified".
- Final distinct states, depth and wall time to completion: not recorded, the run did not finish. The proposed bound needs depth 20 and 2.06 M states in total; the contract run has 25 M after 8 levels.

Earlier supporting evidence (final spec or its predecessor, differs only by the stutter disjunct): the M1 run at these bounds had 701,932 distinct at depth 6 with 664,874 queued; five reduced scratch bounds, each at or below the contract in every dimension, did not finish either:

| Constants (Ids / EvSkus / Qtys / Ttls / Total / MaxClock / MaxCopies) | Last progress line when stopped |
|---|---|
| {1} / {0,1} / {1,2} / {1,2} / 2 / 3 / 2 | level 10, 15,004,200 generated, 3,692,249 distinct, 2,695,584 on queue |
| {1,2} / {0} / {1} / {1,2} / 1 / 3 / 2 | level 10, 8,019,377 generated, 1,930,628 distinct, 1,296,423 on queue |
| {1,2} / {0} / {1} / {1} / 2 / 2 / 2 | level 15, 26,185,050 generated, 4,437,767 distinct, 1,627,939 on queue |
| {1,2} / {0} / {1} / {1,2} / 1 / 2 / 2 | level 14, 17,156,586 generated, 2,855,446 distinct, 1,064,111 on queue |
| {1,2} / {0} / {1} / {1} / 1 / 2 / 2 | level 14, 18,523,716 generated, 3,027,552 distinct, 1,104,747 on queue |

Cause: `net` and `made` give each of the 42 messages 6 states (made 0 to 2, in flight 0 to 2), and `lastEvent`/`lastFx` stay in the state because the contract needs them. No SYMMETRY or VIEW is allowed.

Options for the user (none applied, all change bounds or add pruning, which needs approval): approve `UC2_proposed.cfg` (2.06 M distinct, 5.5 min) and/or `UC2_proposed_dup.cfg`; approve a different reduced bound (copies 2 with two ids does not finish in 15 min); allow a VIEW that drops `lastEvent`/`lastFx` (not sound for the action properties as written); or a larger machine.

## Non-vacuity: reachability witnesses (TLC must violate each)

30 witnesses. Command per witness (final sweep, `workers 1`, 2026-11-23 05:01 to 05:19, run in parallel with other jobs, so the wall times are inflated):

```bash
tlc -noGenerateSpecTE -workers 1 -metadir $TMPDIR/r -config spec/tla/UC2_reach_<what>.cfg spec/tla/UC2.tla
```

Tier C = contract bounds (`UC2.cfg` constants). Tier M = reduced constants because the witness is deep (8 or more states with a duplicate) and did not hit within 150 s at the contract bounds: `Ids = {1,2}, EvSkus = {0,1}, Qtys = {1,2}, Ttls = {1}, Total = 3, MaxClock = 2, MaxCrashes = 1, MaxCopies = 2`. Every constant there is a subset of or equal to the contract value, so a trace there is a trace at the contract bounds. All exit code 12 and print `Error: Invariant <Name> is violated.` (the violated name is the Witness column).

| cfg | Tier | Witness (invariant TLC violates) | Distinct states | Depth | Wall |
|---|---|---|---|---|---|
| `UC2_reach_reserveok` | C | `ReachReserveOk` | 309 | 3 | 2s |
| `UC2_reach_reserveexact` | C | `ReachReserveExact` | 463 | 3 | 2s |
| `UC2_reach_unknownsku` | C | `ReachUnknownSku` | 876 | 3 | 2s |
| `UC2_reach_duplicateid` | C | `ReachDuplicateId` | 189085 | 5 | 35s |
| `UC2_reach_insufficient` | C | `ReachInsufficient` | 190368 | 5 | 39s |
| `UC2_reach_oversellplusone` | C | `ReachOversellPlusOne` | 190368 | 5 | 40s |
| `UC2_reach_confirmok` | C | `ReachConfirmOk` | 37016 | 5 | 13s |
| `UC2_reach_confirmunknown` | C | `ReachConfirmUnknown` | 48 | 3 | 4s |
| `UC2_reach_confirmtoolate` | C | `ReachConfirmTooLate` | 701932 | 6 | 143s |
| `UC2_reach_expireok` | C | `ReachExpireOk` | 1204950 | 6 | 227s |
| `UC2_reach_expireunknown` | C | `ReachExpireUnknown` | 94 | 3 | 4s |
| `UC2_reach_expirenotyet` | C | `ReachExpireNotYet` | 65988 | 5 | 14s |
| `UC2_reach_reservedup` | C | `ReachReserveDupRejected` | 189085 | 5 | 27s |
| `UC2_reach_expiredrecord` | C | `ReachExpiredRecord` | 1204950 | 6 | 171s |
| `UC2_reach_confirmedrecord` | C | `ReachConfirmedRecord` | 37016 | 5 | 11s |
| `UC2_reach_tick` | C | `ReachTick` | 44 | 2 | 3s |
| `UC2_reach_tickdown` | C | `ReachTickDown` | 1203 | 3 | 3s |
| `UC2_reach_crash` | C | `ReachCrash` | 45 | 2 | 3s |
| `UC2_reach_restart` | C | `ReachRestart` | 1204 | 3 | 4s |
| `UC2_reach_deliverdown` | C | `ReachDeliverDown` | 27010 | 4 | 9s |
| `UC2_reach_crashlost` | C | `ReachCrashLost` | 91 | 3 | 4s |
| `UC2_reach_heldaftercrash` | C | `ReachHeldAfterCrash` | 8570 | 4 | 5s |
| `UC2_reach_duplicated` | C | `ReachDuplicated` | 47 | 3 | 3s |
| `UC2_reach_dropped` | C | `ReachDropped` | 46 | 3 | 3s |
| `UC2_reach_releasedemitted` | C | `ReachReleasedEmitted` | 1204950 | 6 | 171s |
| `UC2_reach_confirmnotheld` | M | `ReachConfirmNotHeld` | 96141 | 7 | 13s |
| `UC2_reach_expirenotheld` | M | `ReachExpireNotHeld` | 107295 | 7 | 14s |
| `UC2_reach_expiredupnotheld` | M | `ReachExpireDupNotHeld` | 886654 | 8 | 77s |
| `UC2_reach_confirmdupnotheld` | M | `ReachConfirmDupNotHeld` | 96141 | 7 | 12s |
| `UC2_reach_expirenotheldconfirm` | M | `ReachExpireNotHeldAfterConfirm` | 107295 | 7 | 13s |

Meaning: `ReserveOk` a Reserve accepted; `ReserveExact` accepted with `qty == available` (available 0 after); `UnknownSku`, `DuplicateId`, `Insufficient` each reject reason; `OversellPlusOne` an `InsufficientStock` reject with `qty == available + 1`; `ConfirmOk`, `ConfirmUnknown`, `ConfirmNotHeld`, `ConfirmTooLate`; `ExpireOk`, `ExpireUnknown`, `ExpireNotYet`, `ExpireNotHeld`; `ExpireDupNotHeld` Expire rejected `NotHeld` on a message with 2 copies made after the record is `Expired`; `ConfirmDupNotHeld` the same for Confirm; `ReserveDupRejected` a second copy of a Reserve rejected `DuplicateId`; `ExpireNotHeldAfterConfirm`; `ExpiredRecord`, `ConfirmedRecord`; `Tick`, `TickDown` (Tick while down), `Crash`, `Restart`, `DeliverDown` (a Reserve, Confirm or Expire delivered while down), `CrashLost` (a Crash that dropped at least one in-flight copy), `HeldAfterCrash`, `Duplicated`, `Dropped`, `ReleasedEmitted` (`emitted` nonzero). `BadRequest` has no witness: it is unreachable at the contract bounds (see above). Antecedents of the action properties: `PinReserveOk`/`NoOversell` (ReserveOk), `PinReserveRejected` (3 reasons), `PinConfirmOk`, `PinConfirmRejected` (3 reasons), `PinExpireOk`, `PinExpireRejected` (3 reasons), `PinDown` (DeliverDown), `PinTick`, `PinCrash`, `PinRestart`, `ExpiredNeverConfirmed` (ExpiredRecord), `ConfirmOnlyBeforeDue` (ConfirmedRecord), `FieldsStable` (any step).

## Mutant M1 (`UC2_buggy`)

`UC2_buggy.tla` = `UC2.tla` with the Confirm guard `Due(s, r)` replaced by `s.clock > r.expiresAt` (accepts when `clock <= expiresAt`). `UC2_buggy.cfg`: contract bounds, `INVARIANT ConfirmedBeforeDue` and `Conservation`.

```bash
tlc -noGenerateSpecTE -workers 1 -metadir $TMPDIR/b -config spec/tla/UC2_buggy.cfg spec/tla/UC2_buggy.tla
```

```text
Error: Invariant ConfirmedBeforeDue is violated.
State 1: <Initial predicate>
State 2: <Send ...>
State 3: <Send ...>
State 4: <Deliver ...>
State 5: <Tick ...>
State 6: <Deliver ...>
1812091 states generated, 701932 distinct states found, 664874 states left on queue.
The depth of the complete state graph search is 6.
Finished in 02min 36s at (2026-11-23 05:04:10)
```

Trace length 6 states: send `Reserve` (ttl 1), send `Confirm`, deliver the Reserve (`expiresAt = 1`), `Tick` (`clock = 1`), deliver the Confirm: accepted at `clock == expiresAt`, so `confirmedAt = expiresAt`. Exit 12. Wall time 2 min 36 s with other jobs running; 53 s alone (earlier run). Two scratch cfgs (same constants, `PROPERTY` instead of the invariants) show that the contract's other killers also fire: `Error: Action property ConfirmOnlyBeforeDue is violated.` and `Error: Action property PinConfirmRejected is violated.`, both 701,932 distinct states, depth 6, exit 13.

```text
== tlc (expect violation) UC2_buggy
Error: Invariant ConfirmedBeforeDue is violated.
check-tla-buggy: 7 buggy spec(s) rejected as expected
real	1m50.838s
```

(`just check-tla-buggy` with `XDG_RUNTIME_DIR=$TMPDIR`; `just` cannot write its runtime dir on the read-only `/run/user`.) M1b to M7 are not part of this task.

## Timing

Hyperfine, 1 run (`UC2_proposed.cfg`, 2 workers): mean 348.9 s, user 658 s, system 2.9 s. Cold and warm are not separated: there is no cache beyond the JVM, and repeating a 6 minute run was not worth the budget. Reach and buggy runs: 2 s to 4 min, JVM start-up included, not hyperfine-timed.

## Modelling choices not fixed by UC2.md (for the checkpoint)

1. Each message value is `Send`-able once (`made[m] = 0`); `Duplicate` makes a second copy only while one is in flight; `made` never exceeds `MaxCopies`, so deliveries per value stay at most `MaxCopies`. Crash clears `net` but not `made`, so a lost message is not resent.
2. `Crash` needs `up` and `crashes < MaxCrashes`; `Restart` needs `~up`. `Step` still implements the already-down and already-up cases.
3. `Tick` is enabled while `clock < MaxClock`, up or down.
4. Stutter disjunct `\/ UNCHANGED vars` in `Next`. Bounded runs end in states with no other step, and TLC reports "Deadlock reached" (`-deadlock` is not in the `just` recipe). It hides a true deadlock; the alternative is a cfg-level deadlock switch, which TLC has only on the command line.
5. `emitted` is a bag of `FxReleased` effects only (keyed by `[id, qty]`), not of every effect. P3b needs nothing else and the full bag multiplies the state count.
6. `lastEvent` for `Send`, `Drop`, `Duplicate` carries only `kind`; `Crash` has an extra `lost` count (copies in flight when it fired) for a witness; delivered events carry the message itself.
7. `stocks` is a function over `{0}`; `res` is a sequence (append order kept).
8. `PinDown` covers `Reserve`, `Confirm`, `Expire` and `Crash` when `~up`.
9. `TypeOK` bounds `expiresAt` by `MaxClock + max ttl` only so TLC can enumerate `EffSet`.
10. Proposed bound (above) is a choice, pending approval.

## Authoring effort

- About 115 min wall (03:30 to 05:25 UTC); about 25 min of authoring the spec, the rest was TLC runs and waiting.
- Failed model checks on the good spec: 2 (the first run died on an un-enumerable `expiresAt : Nat` in `TypeOK`'s `EffSet`; the second reported "Deadlock reached", fixed with the stutter disjunct). Under the stop rule (15). No parse errors otherwise.
- Size: `UC2.tla` 428 lines, `UC2.cfg` 33, `UC2_buggy.tla` 430, `UC2_buggy.cfg` 13, `UC2_proposed.cfg` 33, `UC2_proposed_dup.cfg` 33, 30 small reach cfgs.

## Friction

- State explosion from the message model (above). The honest alternative that makes the checked bound larger (lazy delivery without an in-flight set) gives the same event lists but is not what the brief asks for; not built.
- `just` needs `XDG_RUNTIME_DIR` set to a writable dir in this sandbox.
- A TLC process started with a plain `&` dies with the tool call; run it as a background task. `pkill -f` on a pattern also kills the calling shell.
- `tlc` with `-workers 2` on 2 cores while other jobs run: wall times from the final sweep are not comparable with the earlier uncontended ones (53 s vs 2 min 36 s for the same M1 run).

## Log entry (for experiment-log.md)

See `experiment-log.md` section 4.18.

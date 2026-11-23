# UC2 mutants (M1, M1b, M2, M3, M3b, M4, M5, M5a, M6, M7)

Contract: `properties/UC2.md` section 5 (frozen, not edited). Each mutant is the same bug in Go (`mutants/uc2`), Bend (`bend/uc2/mutants/<mid>`) and TLA+ (`spec/tla/UC2_buggy*.tla`), with the exceptions below. M1 in TLA+ is the existing `UC2_buggy.tla` (written by another task, rerun here). M5a has no Bend counterpart (`Nat` truncates). Harness results: see `uc2-harness.md`. Nothing in `properties/`, `internal/`, `LAWS.bend`, `spec.bend`/`code.bend`/`PROOF.bend` of `bend/uc2`, `UC2.tla` or `UC2*.cfg` was edited.

Bounds. TLA+: every `UC2_buggy_m*.cfg` uses the UC2.cfg contract constants (`Ids={1,2,3}`, `EvSkus={0,1}`, `Qtys={1,2,3}`, `Ttls={1,2}`, `Total=3`, `MaxClock=4`, `MaxCrashes=1`, `MaxCopies=2`) and lists every UC2.cfg invariant and property, so TLC reports whichever it meets first. Exception: `UC2_buggy.cfg` (M1, from the TLA+ spec task) lists only `ConfirmedBeforeDue` and `Conservation`; P4b and S5 on M1 were shown by scratch runs recorded in `uc2-tla.md`. Go: 2000 seeded random event lists (seed 1, up to 150 events, 1 to 3 stocks, totals 1 to 6, ids 1..6, unknown sku, qty 0..7, ttl 0..3, 20% resent events), plus for M4 the directed list. Bend: no bound. The Bend gate is plain `bend PROOF.bend` (`--verdict` cannot run here).

## Result table

| Mutant | Go checks that fail (all) | Bend gate: first failing lemma | TLA+ first violation (trace length in states) | Harness |
|---|---|---|---|---|
| M1 `Confirm` accepts at `clock <= expiresAt` | P4a, P4b, S5 | `inv_conf1` | `ConfirmedBeforeDue` (P4a), 6 states (`UC2_buggy`) | diverges: seed 19, event 7 (Confirm) |
| M1b `Expire` needs `clock > expiresAt` | S6 | `inv_exp1` | `PinExpireOk` (S6), 6 states | diverges: seed 7, event 108 (Expire) |
| M2 double release | P3, A1, S7, S10, S11 | `inv_exp2` | none at the contract bound in 15 min (wall); scratch run at the proposed_dup bound: `CountersMatchRecords` (A1), 8 states | diverges: seed 2, event 120 (Expire) |
| M3 `Confirm` needs only the record | P3, P4, P4a, P4b, A1, S5, S10, S11 | `inv_conf1` | `ConfirmedBeforeDue` (P4a), 6 states | diverges: seed 2, event 11 (Confirm) |
| M3b `Confirm` checks Held, not Due | P4a, P4b, S5 | `inv_conf2` | `ConfirmedBeforeDue` (P4a), 6 states | diverges: seed 2, event 11 (Confirm) |
| M4 check-then-act | P1, P1b, P3b, A2, mutant-only commit pin (directed list: P1, P1b) | `Laws.inv_step` (see M4 note: stateless port) | `NoOversell` (P1b), 4 states | not catchable: needs non-contract events (`StepM4Contract` agrees on 500 sequences) |
| M5 truncated unguarded subtraction | P1b, P2, S3 | `inv_rsv` | `Conservation` (P2), 5 states | diverges: seed 1, event 79 (Reserve) |
| M5a plain unguarded subtraction | P1, S3 | (no Bend counterpart) | `NonNegativeAvailable` (P1), 5 states | diverges: seed 1, event 79 (Reserve; Go goes negative, Bend Nat cannot) |
| M6 leak | P2, A1, S6 | `inv_exp2` | `Conservation` (P2), 6 states | diverges: seed 2, event 93 (Expire) |
| M7 duplicate Reserve id accepted | P3b, A2, S3, S11 | `inv_rsv` | `UniqueIdsKnownSku` (A2), 5 states | diverges: seed 1, event 73 (Reserve) |

No mutant survived Go or Bend. In TLA+ one mutant (M2) survived the 15 minute cap at the contract bound (no violation found, not proved safe) and was killed in a scratch run at a proposed bound.

## Comparison with the section 5 "Killed by" column

Every Go set below is asserted by `expect` in `checker_test.go` (exact set of failing checks), and the test logs the diff to section 5.

| Mutant | Section 5 | Go actual | Difference |
|---|---|---|---|
| M1 | P4a, P4b, S5 (not P4) | P4a, P4b, S5 | none |
| M1b | S6, S7 | S6 | **S7 does not fail.** The boundary case (`Held` and `clock == expiresAt`) is `Due`, so it belongs to S6 (accepted Expire); the mutant rejects it with `NotYet`, which is a wrong S6 result, never an S7 case. S7 only covers events that core also rejects. TLA+ agrees: `PinExpireOk` fires, not `PinExpireRejected` |
| M2 | P3, A1, S7, S11 | P3, A1, S7, S10, S11 | extra S10 (a `Confirmed` record is turned `Expired`; the status of a closed record changes) |
| M3 | P4, P3, P4a, P4b, A1, S5 (P2 Bend only) | P3, P4, P4a, P4b, A1, S5, S10, S11 | extra S10 and S11; P2 holds in Go as the contract says |
| M3b | P4a, P4b, S5 | P4a, P4b, S5 | none |
| M4 | P1 (TLA+, Go), P1b, P2 | P1, P1b, P3b, A2, commit pin | **P2 does not fail** with signed counters (`available - qty` and `reserved + qty` cancel). Extras: A2 (the commit takes no duplicate-id check) and P3b |
| M5 | P2, P1b, S3 (not P1) | P1b, P2, S3 | none |
| M5a | P1, P2, P1b, S3 | P1, S3 | **P2 and P1b do not fail**, as the issue anticipated. The take is `available - qty` and `reserved + qty` (P2 holds), and the one `FxReserved` effect with the exact qty is emitted (P1b holds). Only P1 and S3 kill it, matching `uc2-core.md` |
| M6 | P2, A1, S6 | P2, A1, S6 | none |
| M7 | A2, S3, S11 | P3b, A2, S3, S11 | extra P3b (found by the random runs; not analysed further) |

TLA+ first-violation names are a function of TLC's BFS order, not a kill set: TLC stops at the first violated invariant or action property, so the table above lists one name per mutant. M5 shows `Conservation`, not P1b, at depth 5 even though P1b also breaks.

Kill matrix printed by the test (X = fails):

```
      P1 P1b P2 P3 P3b P4 P4a P4b A1 A2 S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 M4-only
core   .   .  .  .   .  .   .   .  .  .  .  .  .  .  .  .  .  .  .  .   .   .       .
M1     .   .  .  .   .  .   X   X  .  .  .  .  .  .  .  X  .  .  .  .   .   .       .
M1b    .   .  .  .   .  .   .   .  .  .  .  .  .  .  .  .  X  .  .  .   .   .       .
M2     .   .  .  X   .  .   .   .  X  .  .  .  .  .  .  .  .  X  .  .   X   X       .
M3     .   .  .  X   .  X   X   X  X  .  .  .  .  .  .  X  .  .  .  .   X   X       .
M3b    .   .  .  .   .  .   X   X  .  .  .  .  .  .  .  X  .  .  .  .   .   .       .
M4     X   X  .  .   X  .   .   .  .  X  .  .  .  .  .  .  .  .  .  .   .   .       X
M5     .   X  X  .   .  .   .   .  .  .  .  .  .  X  .  .  .  .  .  .   .   .       .
M5a    X   .  .  .   .  .   .   .  .  .  .  .  .  X  .  .  .  .  .  .   .   .       .
M6     .   .  X  .   .  .   .   .  X  .  .  .  .  .  .  .  X  .  .  .   .   .       .
M7     .   .  .  .   X  .   .   .  .  X  .  .  .  X  .  .  .  .  .  .   .   X       .
```

## Go (`mutants/uc2`)

`mutants.go` (241 lines): `StepM1`, `StepM1b`, `StepM2`, `StepM3`, `StepM3b`, `StepM5`, `StepM5a`, `StepM6`, `StepM7`, each with core.Step's signature, handling only its own bug and delegating the rest to `core.Step`. M2 is literal: any `Due` record, whatever its status, gets all of S6 again (a `Confirmed` and `Due` record becomes `Expired`). M5 is `if a >= q { a - q } else { 0 }`; M5a plain int64. M7 accepts a duplicate id only when `qty <= available`. M4 needs `M4State{core.State; Approved []core.Event}`, `InitM4`, `StepM4(M4State, Event)`, and the mutant-only kinds `ReserveCheck = Restart+1`, `ReserveCommit = Restart+2`. `StepM4Contract` is the stateless projection (Approved dropped; equals `core.Step`). `ReserveCheck` approves when up, `qty >= 1`, `ttl >= 1`, the stock exists and `qty <= available`. `ReserveCommit{id}` applies S2 for the first approved request with that id, with no duplicate-id check and no `qty <= available` check. Decision beyond section 5: the check includes the BadRequest and UnknownSku parts, so approved requests are well formed.

`checker_test.go` (412 lines): the checker re-implements, over every step, P1, P1b, P2, P3, P3b, P4, P4a, P4b, A1, A2, S10 and S11 with the exported core predicates, and attributes pins S0 to S9 by case (`pinCase`) against `core.Step`, which core's own tests pin to section 4. `core.Step` is the control and fails nothing. Every mutant must fail something and its exact failing set is pinned.

```
$ go test ./mutants/uc2/ -run 'Checks|Directed' -v | grep -E 'failing checks|^(ok|---)|directed'
core: failing checks: []
M1: failing checks: [P4a P4b S5]
M1b: failing checks: [S6]
M2: failing checks: [P3 A1 S7 S10 S11]
M3: failing checks: [P3 P4 P4a P4b A1 S5 S10 S11]
M3b: failing checks: [P4a P4b S5]
M4: failing checks: [P1 P1b P3b A2 M4-only]
M5: failing checks: [P1b P2 S3]
M5a: failing checks: [P1 S3]
M6: failing checks: [P2 A1 S6]
M7: failing checks: [P3b A2 S3 S11]
--- PASS: TestMutantsRejectedByChecks (8.48s)
directed list fails: [P1 P1b M4-only]
--- PASS: TestM4DirectedOversell (0.00s)
ok  	github.com/derangga/learn-formal-verification/mutants/uc2	8.488s
```

Verbatim first failures: M5a `P1`: `after Reserve{id=6 sku=0 qty=2 ttl=1}: [{Sku:0 Total:1 Available:-1 Reserved:2 Sold:0} ...]`; M1b `S6`: `Expire{id=4 ...} at clock 1 ... got [... Available:0 Reserved:5 ...] [{FxRejected 4 ... NotYet}], want [... Available:2 Reserved:3 ...] [{FxReleased 4 ... Qty 2}]`; M2 `P3`: `after Expire{id=4}: [{ID:4 ... Status:Expired ... Returned:2} ...]`.

The directed list `[Check 1 (qty 2), Check 2 (qty 2), Commit 1, Commit 2]` on total 3 ends with `available = -1` (`TestM4DirectedOversell`), failing P1 and P1b but not P2.

## Bend (`bend/uc2/mutants/<mid>`, `bash bend/uc2/mutants/run.sh`)

Layout and `run.sh` follow UC1. Every `LAWS.bend` is byte-identical to `bend/uc2/LAWS.bend` (run.sh checks it).

```
$ bash bend/uc2/mutants/run.sh; echo rc=$?
m1     PASS rejected as expected (Location: inv_conf1)
m1b    PASS rejected as expected (Location: inv_exp1)
m2     PASS rejected as expected (Location: inv_exp2)
m3     PASS rejected as expected (Location: inv_conf1)
m3b    PASS rejected as expected (Location: inv_conf2)
m4     PASS rejected as expected (Location: Laws.inv_step)
m5     PASS rejected as expected (Location: inv_rsv)
m6     PASS rejected as expected (Location: inv_exp2)
m7     PASS rejected as expected (Location: inv_rsv)
rc=0
```

`just prove-bend` passes: three `ALL PROOFS CHECK` (smoke, uc1, uc2), the probes, the UC1 and UC2 mutant runs (output above).

Changes in `code.bend` (everything else identical; each is the whole diff):

| Mutant | Change | Lines changed |
|---|---|---|
| m1 | `conf1`: `Nat.is_le(exp, clock)` became `Nat.is_lt(exp, clock)` for the Due flag passed to `conf2` | 2 |
| m1b | `exp1`: the same change for `exp2` | 2 |
| m2 | `exp2`: `Confirmed` and `Expired` with `due == True` call `expire_acc` (split from the `_ ` cases) | 8 |
| m3 | `conf1`: the `Got` case calls `confirm_acc` directly | 2 |
| m3b | `conf2`: `Held` and Due calls `confirm_acc` instead of rejecting TooLate | 2 |
| m5 | `rsv`: the `InsufficientStock` case calls `reserve_acc` (`Nat.sub(av, qty)` truncates) | 2 |
| m6 | `expire_acc`: `Nat.sub(rv, qty)` became `rv` | 2 |
| m7 | `rsv`: `Got{_}` with `g4 == True` calls `reserve_acc`; with `False` still `DuplicateId` | 4 |
| m4 | see below | `code.bend` 10, `spec.bend` 2, `PROOF.bend` 4 |

Each failure is a hand proof that no longer checks because the code it was written against changed (gate messages `expected`/`observed` differ in the guard argument or the counter expression), not a counterexample to a law. Same caveat as UC1 M5: a proof that stops checking shows the proof does not survive the change, which is the contract of "rejected" here.

**M4 in Bend is a stateless approximation.** `State` has four fields in the frozen `LAWS.bend` (it builds `State{...}` explicitly in six laws), so an `approved` list cannot be stored. The port adds `ReserveCheck{id,sku,qty,ttl}` (a no-op, `(s, [])`) and `ReserveCommit{id,sku,qty,ttl}` (carrying the request; after the up gate it runs `rsv` with the BadRequest and UnknownSku checks but with the duplicate lookup forced to `NoRes` and `g4` forced to `True`). That is the "act" half with the check taken as already done; the check-then-act ordering is not expressible. Go and TLA+ keep the real `approved` list. `spec.bend` gets the two constructors in `Ev`. Every `match` on `Ev` in `PROOF.bend` becomes non-exhaustive; the unedited proof fails first with `this match doesn't cover spec.ReserveCheck, spec.ReserveCommit` at `Laws.inv_step`, which is not the bug. The one edit: two cases added to `Laws.inv_step` (`ReserveCheck` is `h`; `ReserveCommit` reuses the Reserve proof `inv_gr`). Then the gate fails on the commit case, naming `rsv(..., NoRes{}, True{}, ...)` against `rsv(..., find_res(rs, id), Nat.is_le(qty, av), ...)`. The other seven `match`es on `Ev` in that `PROOF.bend` were not edited; the gate stops at the first error, so they are untested for M4. EXPECT lines: `Location: Laws.inv_step` and `Spec.ReserveCommit`.

## TLA+ (`spec/tla/UC2_buggy_m*.tla`)

Each `.tla` is `UC2.tla` with a minimal diff; each `.cfg` is the contract constants and every UC2.cfg invariant and property. Changed lines (diff `<`/`>` count against `UC2.tla`): m1b 6, m2 11, m3 9, m3b 6, m5 8, m5a 8, m6 6, m7 7, m4 61 (new variable `approved`, `ReserveApply`, `ReserveCheck`, `ReserveCommit`, a `Step` branch, `TypeOK` and `EventSet` entries, `approved` added to every `UNCHANGED`). Header lines add 3 to each. In M4, `ReserveCheck(m)` consumes a copy of a Reserve message from `net` (so `approved` stays finite), requires up, `qty >= 1`, `ttl >= 1`, a known sku and `qty <= available`, and appends it; `ReserveCommit(id)` removes the first approved request with that id and runs `ReserveApply` (S2 with no checks). Each run: `tlc -noGenerateSpecTE -metadir $TMPDIR/meta-<n> -config spec/tla/<n>.cfg spec/tla/<n>.tla`, `timeout 900`, one job at a time, metadir deleted after each job.

| Mutant | TLC output | States generated / distinct | Trace (states), actions | Wall |
|---|---|---|---|---|
| M1 (`UC2_buggy`) | `Invariant ConfirmedBeforeDue is violated.` | 1,812,091 / 701,932 | 6 | 47 s |
| M1b | `Action property PinExpireOk is violated.` | 3,252,194 / 1,204,950 | 6: Send, Send, Deliver, Tick, Deliver | 3 min 29 s |
| M2 | no violation | 13,228,678 / 4,546,849 at the cap (depth 6 not finished, queue 4,279,252) | none | killed at 15 min (rc 124) |
| M3 | `Invariant ConfirmedBeforeDue is violated.` | 1,812,091 / 701,932 | 6: Send, Send, Deliver, Tick, Deliver | 2 min 04 s |
| M3b | `Invariant ConfirmedBeforeDue is violated.` | 1,812,091 / 701,932 | 6 (same trace shape) | 2 min 02 s |
| M4 | `Action property NoOversell is violated.` | 16,849 / 9,666 | 4: Send, ReserveCheck, ReserveCommit | 6 s |
| M5 | `Invariant Conservation is violated.` | 419,231 / 190,368 | 5: Send, Deliver, Send, Deliver | 36 s |
| M5a | `Invariant NonNegativeAvailable is violated.` | 419,231 / 190,368 | 5: same shape | 34 s |
| M6 | `Invariant Conservation is violated.` | 3,252,194 / 1,204,950 | 6: Send, Send, Deliver, Tick, Deliver | 3 min 15 s |
| M7 | `Invariant UniqueIdsKnownSku is violated.` | 416,715 / 189,085 | 5: Send, Duplicate, Deliver, Deliver | 32 s |

M4 reports `NoOversell` (P1b) at 4 states because `ReserveCommit` takes stock and is not a `Reserve`, so the very first commit violates P1b. The true oversell (P1) needs two checks and two commits (6 states); not run separately, the Go directed list covers P1.

**M2 wall and scratch run.** At the contract bound TLC did not find the double release in 15 minutes (the double `Expire` needs a duplicated `Expire` copy, so the trace is longer than depth 6). This is a wall, not a pass. Scratch run, clearly marked as the **proposed bound** (`spec/tla/UC2_proposed_dup.cfg` constants, same `UC2_buggy_m2.tla`, not committed as a cfg because it is not the contract bound):

```
$ tlc -config spec/tla/UC2_proposed_dup.cfg spec/tla/UC2_buggy_m2.tla
Error: Invariant CountersMatchRecords is violated.
State 1..8: Init, Send, Send, Send, Deliver, Deliver, Tick, Deliver
32981 states generated, 11017 distinct states found.   Finished in 03s
```

The trace is 8 states. `UC2_proposed.cfg` (MaxCopies 1) cannot reach the bug at all, as it forbids duplicate delivery. A1 breaks because a second `Expire` subtracts `qty` from `reserved` again.

**`just check-tla-buggy` was not run.** It runs every `*_buggy*.cfg` with no timeout, and `UC2_buggy_m2.cfg` does not finish at the contract bound (killed at 15 min, 13.2M states), so the recipe would not terminate. Without m2 the other nine runs sum to about 16 minutes. The committed `UC2_buggy_m2.cfg` is kept at the contract constants as the brief says; the user must either approve a bound for it or exempt it from the recipe.

## Times, sizes, friction

- Authoring: about 1.5 h wall for all three tools including TLC waits (Go about 20 min, Bend about 25 min, TLA+ about 25 min plus runs). Within the 2 h limit per tool.
- Failed iterations (runs failing for a reason other than the bug): Go 0 (the first run only pinned the expected sets). Bend 1 (M4: non-exhaustive match, fixed by the `PROOF.bend` edit above). TLA+ 3: a `gen.py` syntax error, and two infrastructure failures. Under the 15 limit.
- **Disk-full incident.** The first TLC batch (all mutants in one background loop) ran when `/tmp/claude-1001` was full. m1b died at level 5 with `Error: when writing the disk (StatePoolWriter.run)` leaving a 381 MB metadir; m3 to m7 and m2 then failed at once (m2 with `Module-Table lookup failure`, which was the disk, not the header, all nine `MODULE` headers match their file names). Fix: after space was freed, one job at a time with a `df` check (stop under 1.5 GB), `timeout 900`, metadir deleted after each job, and only the `.out` kept. An earlier version of the cleanup glob also deleted the failed `.out` files, which held nothing useful.
- Background loops started with `&` inside a Bash call are killed when the call returns; use `run_in_background`.
- TLC cost is the state count at depth 6 (1.2M distinct states for the clock-and-expiry mutants, 3 min), not the mutation. M2 needs a duplicated message and more depth than the contract bound allows in the cap.
- Bend: about 0.7 s per mutant, 6.5 s for the nine. LAWS were not touched; the same frozen-arity limit that forced UC1 M3's encoding forced M4's stateless port.

## Evidence re-run by the orchestrator (2026-11-23)

`just prove-bend` (exit 0): `ALL PROOFS CHECK` for `bend/smoke`, `bend/uc1`, `bend/uc2`; `prove-bend: 3 proof file(s) checked`; probes 14 PASS; UC1 mutants m1-m5 PASS; UC2 mutants:

```text
== bend/uc2/mutants/run.sh
m1     PASS rejected as expected (Location: inv_conf1)
m1b    PASS rejected as expected (Location: inv_exp1)
m2     PASS rejected as expected (Location: inv_exp2)
m3     PASS rejected as expected (Location: inv_conf1)
m3b    PASS rejected as expected (Location: inv_conf2)
m4     PASS rejected as expected (Location: Laws.inv_step)
m5     PASS rejected as expected (Location: inv_rsv)
m6     PASS rejected as expected (Location: inv_exp2)
m7     PASS rejected as expected (Location: inv_rsv)
```

`go vet ./... && go test -count=1 ./mutants/uc2/ ./harness/uc2conformance/`: `ok .../mutants/uc2 17.114s`, `ok .../harness/uc2conformance 6.781s`.

TLC excerpts from the saved run outputs (grep of `is violated`, `states generated`, `Finished in`; M2 shows its last progress lines before the 15 min timeout):

```text
== out-m1.txt
Progress(4) at 2026-11-23 07:22:05: 51,689 states generated (51,689 s/min), 25,971 distinct states found (25,971 ds/min), 24,904 states left on queue.
Error: Invariant ConfirmedBeforeDue is violated.
1812091 states generated, 701932 distinct states found, 664874 states left on queue.
== out-UC2_buggy_m1b.txt
Progress(4) at 2026-11-23 06:53:01: 11,724 states generated (11,724 s/min), 6,915 distinct states found (6,915 ds/min), 6,671 states left on queue.
Progress(5) at 2026-11-23 06:54:01: 875,852 states generated (864,128 s/min), 367,491 distinct states found (360,576 ds/min), 349,595 states left on queue.
Progress(6) at 2026-11-23 06:55:01: 1,859,600 states generated (983,748 s/min), 722,126 distinct states found (354,635 ds/min), 684,143 states left on queue.
== out-UC2_buggy_m2.txt
Progress(4) at 2026-11-23 06:56:32: 5,157 states generated (5,157 s/min), 3,177 distinct states found (3,177 ds/min), 3,069 states left on queue.
Progress(5) at 2026-11-23 06:57:32: 809,890 states generated (804,733 s/min), 344,779 distinct states found (341,602 ds/min), 328,244 states left on queue.
Progress(6) at 2026-11-23 06:58:32: 1,796,746 states generated (986,856 s/min), 696,639 distinct states found (351,860 ds/min), 659,900 states left on queue.
== out-UC2_buggy_m3b.txt
Progress(4) at 2026-11-23 07:13:37: 10,676 states generated (10,676 s/min), 6,140 distinct states found (6,140 ds/min), 5,917 states left on queue.
Progress(5) at 2026-11-23 07:14:37: 891,409 states generated (880,733 s/min), 372,421 distinct states found (366,281 ds/min), 354,203 states left on queue.
Error: Invariant ConfirmedBeforeDue is violated.
== out-UC2_buggy_m3.txt
Progress(4) at 2026-11-23 07:11:32: 5,984 states generated (5,984 s/min), 3,597 distinct states found (3,597 ds/min), 3,472 states left on queue.
Progress(5) at 2026-11-23 07:12:32: 843,182 states generated (837,198 s/min), 356,399 distinct states found (352,802 ds/min), 339,177 states left on queue.
Error: Invariant ConfirmedBeforeDue is violated.
== out-UC2_buggy_m4.txt
Progress(4) at 2026-11-23 07:20:39: 9,239 states generated (9,239 s/min), 5,502 distinct states found (5,502 ds/min), 5,310 states left on queue.
Error: Action property NoOversell is violated.
16849 states generated, 9666 distinct states found, 9320 states left on queue.
== out-UC2_buggy_m5a.txt
Progress(4) at 2026-11-23 07:16:17: 8,988 states generated (8,988 s/min), 5,289 distinct states found (5,289 ds/min), 5,102 states left on queue.
Error: Invariant NonNegativeAvailable is violated.
419231 states generated, 190368 distinct states found, 181824 states left on queue.
== out-UC2_buggy_m5.txt
Progress(4) at 2026-11-23 07:15:40: 5,533 states generated (5,533 s/min), 3,398 distinct states found (3,398 ds/min), 3,281 states left on queue.
Error: Invariant Conservation is violated.
419231 states generated, 190368 distinct states found, 181824 states left on queue.
== out-UC2_buggy_m6.txt
Progress(4) at 2026-11-23 07:16:51: 12,920 states generated (12,920 s/min), 7,437 distinct states found (7,437 ds/min), 7,169 states left on queue.
Progress(5) at 2026-11-23 07:17:51: 960,973 states generated (948,053 s/min), 394,473 distinct states found (387,036 ds/min), 374,812 states left on queue.
Progress(6) at 2026-11-23 07:18:51: 1,992,494 states generated (1,031,521 s/min), 774,892 distinct states found (380,419 ds/min), 734,267 states left on queue.
== out-UC2_buggy_m7.txt
Progress(4) at 2026-11-23 07:20:08: 11,810 states generated (11,810 s/min), 6,958 distinct states found (6,958 ds/min), 6,715 states left on queue.
Error: Invariant UniqueIdsKnownSku is violated.
416715 states generated, 189085 distinct states found, 180594 states left on queue.
== out-m2-proposed.txt
Error: Invariant CountersMatchRecords is violated.
32981 states generated, 11017 distinct states found, 6846 states left on queue.
Finished in 03s at (2026-11-23 07:20:58)
== out-UC2_buggy_m1b.txt
Error: Action property PinExpireOk is violated.
Finished in 03min 29s
== out-UC2_buggy_m6.txt
Error: Invariant Conservation is violated.
Finished in 03min 15s
== out-UC2_buggy_m2.txt (last progress line before timeout 900)
Progress(6) at 2026-11-23 07:10:32: 13,228,678 states generated (902,512 s/min), 4,546,849 distinct states found (293,619 ds/min), 4,279,252 states left on queue.
```

## Review findings left open

- The Go checker tests pins S0-S9 by comparing each mutant with `core.Step`, not by asserting each section 4 row on its own. It shows that a mutant differs from core in the case a pin governs. Core's own tests pin the rows (`internal/uc2/core/core_test.go`).
- The harness compares effects as tallies (count and sums of id, qty, expiresAt), not as an ordered list, and does not tally `FxReserved.sku`. Each step emits at most one effect and the full state is compared, so no divergence is known to hide there.
- The harness has no coverage counter for the mutant trigger cases (Expire on a non-Held Due record, Confirm on a non-Held record, duplicate Reserve with stock). Every mutant is still caught by seed 19.
- `just check-tla-buggy` does not finish while `UC2_buggy_m2.cfg` is at the contract bound (see the wall above).

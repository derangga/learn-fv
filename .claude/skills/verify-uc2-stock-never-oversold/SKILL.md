---
name: verify-uc2-stock-never-oversold
description: Use when a change touches UC2 inventory code, meaning stock reservation, confirm and expiry in internal/uc2/core, spec/tla/UC2.tla, bend/uc2, mutants/uc2, harness/uc2conformance or services/inventory. Runs the checks that show stock is never oversold (properties P1, P1b, P2) and tells you how to read a failure.
---

# Verify UC2: stock is never oversold

**Property.** For every SKU, `available + reserved + sold == total` (P2), `available` never drops below zero (P1), and `available` goes down only on an accepted `Reserve`, by exactly its `qty` (P1b). The contract is `properties/UC2.md` sections 3 and 4. The same run also checks P3 (an expired hold returns its stock exactly once), P4, P4a, P4b, A1, A2 and the step pins S0 to S11, because one broken rule usually breaks several of them.

**Harm if it breaks.** The shop sells stock it does not have, or a hold that expired keeps stock locked or releases it twice, so the stock count drifts from reality.

**The rule that keeps it true.** `Reserve` takes stock only after the check `qty <= available`, and it moves `qty` from `available` to `reserved` in one step. `Confirm` moves `qty` from `reserved` to `sold`. `Expire` moves it from `reserved` back to `available`, once, and only while the record is `Held`.

## Run it

From any directory:

```bash
nix develop --command bash .claude/skills/verify-uc2-stock-never-oversold/check.sh          # all stages
nix develop --command bash .claude/skills/verify-uc2-stock-never-oversold/check.sh quick    # skips TLC
```

The tools are pinned by `flake.lock`: TLC 2.18 (nixpkgs `tlaplus-1.8.0`), bend 2.0.40, go 1.26.10. Exit code 0 and the last line `ALL UC2 STOCK CHECKS PASS` mean every stage passed. `quick` took 9 s and the full run took 72 s on a MacBook M4 on 2026-11-23. Use `quick` while editing Go or Bend. Use the full run before you hand off, and always when you touch `spec/tla/UC2*.tla`.

Never run `spec/tla/UC2_wall_contract.cfg` or `UC2_wall_m2.cfg`. They are the contract bounds, a recorded wall: 60 minutes, 25 million distinct states, no violation seen and no completion. TLC metadirs at those bounds have filled a disk before. `check.sh` wraps each TLC call in `timeout` and deletes its scratch directory. Do not use `just check-tla-buggy` either. It runs every buggy cfg with no timeout, and `UC2_buggy_m2.cfg` never finishes.

## Which check reads which file

TLC and Bend never read `internal/uc2/core/core.go`. Each tool checks its own copy of the rule. Only the Go tests and the conformance harness look at the real Go code. A break in `core.go` shows up only in the Go stage.

| Stage in `check.sh` | Reads | Fails when |
|---|---|---|
| Bend proofs | `bend/uc2/PROOF.bend`, `LAWS.bend`, `spec.bend`, `code.bend` | `ALL PROOFS CHECK` is missing. The error names the lemma, for example `inv_rsv`, `p1b_take_step` or `p2_conservation_step`. |
| Bend mutants | `bend/uc2/mutants/*`, run by `mutants/run.sh` | A mutant is accepted, or rejected for another reason than its `EXPECT` file says. |
| Go tests | `internal/uc2/core` (`TestP1bNoOversell`, `TestP2Conservation`, `TestInvHolds`, the `TestPin*` tests), `mutants/uc2`, `harness/uc2conformance` (Go core against compiled Bend), `services/inventory` (`TestInvUnderFaultRuns`, `TestDifferentialAgainstCoreFold`) | A test fails. A conformance failure means the Go core and the Bend port disagree. |
| TLC, `UC2.cfg` | `spec/tla/UC2.tla` | Any invariant or property is violated. |
| TLC, `UC2_dup.cfg` | `spec/tla/UC2.tla` | Same, with duplicate delivery. |
| TLC, `UC2_buggy.cfg`, `_m4`, `_m5`, `_m5a`, `_m7` | `UC2_buggy*.tla`, mutants M1, M4, M5, M5a, M7 | They do NOT violate the property named in the stage header: `ConfirmedBeforeDue`, `NoOversell`, `Conservation`, `NonNegativeAvailable`, `UniqueIdsKnownSku`. These runs must fail. |

## Coverage record

Confirmed against the code at commit `8131d4d870f66e3f8ee3113bd3ab40472b445fe8` (2026-11-23). The covered paths had no uncommitted changes then. Line numbers are as of that commit.

| What | Where |
|---|---|
| Go rule | `internal/uc2/core/core.go`: `Step` (173), `reserve` (199, the guard and the `-=` at 215 and 216), `confirm` (222), `expire` (247), `Inv` (349) |
| TLA+ rule | `spec/tla/UC2.tla`: `Reserve` (43), `Confirm` (57), `Expire` (72), `Step` (87). Invariants `NonNegativeAvailable` (232), `Conservation` (233); action property `NoOversell` (265); pin `PinReserveOk` (289). Bounds in `spec/tla/UC2.cfg` and `UC2_dup.cfg`. |
| Bend rule | `bend/uc2/code.bend`: `reserve_acc` (20), `rsv` (27), `reserve` (40), `confirm` (68), `expire` (96), `step` (100) |
| Bend laws | `bend/uc2/LAWS.bend` (29 laws): `inv_step` (17), `p1b_take_step` (31), `p2_conservation_step` (39), `p2_conservation_run` (46), `pin_reserve_ok` (152), `pin_reserve_rejected` (170). Proofs in `PROOF.bend`. |
| Mutants of the same bug | Go `mutants/uc2/mutants.go` (M1 to M7, the M4 race as a check-then-act event pair). TLA+ `UC2_buggy*.tla`. Bend `bend/uc2/mutants/m1` to `m7`. |
| Production path | `services/inventory/service.go`, `apply` (116) calls `core.Step`. All business logic is `core.Step`. |

Checked bounds for TLC, approved on 2026-11-23, reduced from the contract:

- `UC2.cfg`: ids `{1, 2}`, one SKU, `qty` in `{1, 2}`, `ttl = 1`, `total = 2`, clock up to 2, one `Crash`, each message delivered once. 2,055,926 distinct states at depth 20, no error.
- `UC2_dup.cfg`: one id, `qty = 1`, `ttl` in `{1, 2}`, `total = 1`, clock up to 3, one `Crash`, each message delivered at most twice. 312,995 distinct states at depth 21, no error.

Quote the bounds with every TLC result you report. The buggy cfgs use the larger contract constants and stop at the first violation.

## When a stage fails

1. **A Go unit test fails** (`TestP1bNoOversell`, `TestP2Conservation`, `TestInvHolds`, a `TestPin*`). The change broke `core.Step`. This is a real bug. Fix the code.
2. **Conformance fails, unit tests pass.** The Go core and `code.bend` disagree on some event list. Compare both with sections 3 and 4 of `properties/UC2.md`. Fix the side that departs from the contract.
3. **A Bend proof fails, conformance passes.** The proof or the Bend port is stale. The failing lemma name says which law. Fix `code.bend` or the proof. Do not edit the law.
4. **TLC `UC2.cfg` or `UC2_dup.cfg` reports a violation.** Read the counterexample with the `anak-intern:statechart` skill. It gives the shortest path as steps in plain words. Then feed the same events to `core.Step` in a Go test. If the Go core also breaks the property, it is a real bug in the rule. If only the model does, the spec drifted from the code or the contract, which is a modeling error. Fix the spec and say so.
5. **A mutant is no longer rejected.** The check has lost its teeth. Someone changed a bound, a property or a mutant. The signs differ by tool:
   - Bend: `mutants/run.sh` prints `FAIL accepted a mutant` or `FAIL wrong reason`.
   - TLC: one of the five buggy runs ends with no violation of the named property.
   - Go: `TestMutantsRejectedByChecks` or `TestHarnessRejectsMutants` fails on a mutant subtest while the `internal/uc2/core` tests pass. If a `core` test fails as well, a change to `core.go` is the likelier cause.

   Stop and ask the user. Do not make it fail again by editing the mutant.

Read every TLC result with `anak-intern:statechart`, passes included. A pass gets a chart of how the system moves between states.

## When the change is meant to alter the rule

- `properties/UC2.md`, the approved `bend/uc2/LAWS.bend` and the bounds in `.cfg` files are frozen. If the intended change needs one of them, stop and ask the user. Do not edit them yourself.
- Change the Go core, `UC2.tla` and `code.bend` together, so the three copies of the rule stay equal. If the change moves a rule that a mutant copies, update the matching mutant files in all three tools too, and keep `bend/uc2/mutants/*/DIFFERS` accurate.
- Log the result in `experiment-log.md` using the entry template in section 6, with the command and its pasted output.
- Do not commit unless the user tells you to.

## What this does not cover

- TLC covers the reduced bounds above only. The contract bound is a wall: 60 minutes, no violation seen, no completion. That is not a proof.
- P1 (non-negative `available`) cannot fail in Bend, because Bend numbers are `Nat`. Bend covers it through P1b, P2 and mutant M5. Only TLC and Go use signed counters.
- `BadRequest` (`qty = 0` or `ttl = 0`) is unreachable in TLC at any approved or contract bound. The checked bound has no event for an unknown SKU either, and only one stock, so the frame over several SKUs is tested in Go only.
- TLC runs only five of the ten mutants. M1b, M3, M3b and M6 need 2 to 3.5 minutes each, and M2 does not finish at its cfg bound. Go rejects all ten, and Bend rejects nine (M5a needs signed counters). Run those TLC cfgs by hand if you change the rule they copy, with `timeout`.
- Bend's M4 (the check-then-act race) is a stateless approximation, because the frozen `State` has no room for an `approved` list.
- No test here runs real concurrent requests against the real SQLite store. `services/inventory` is covered where it calls `core.Step` and by the seeded fault runs in its tests.
- Liveness is out of scope: a dropped `Expire` leaves stock reserved, which is not a violation.

## Keep it in step with the code

Before you rely on this skill, list what changed since the sync commit:

```bash
P="internal/uc2 spec/tla/UC2*.tla spec/tla/UC2*.cfg bend/uc2 mutants/uc2 harness/uc2conformance services/inventory properties/UC2.md"
git diff --stat 8131d4d870f66e3f8ee3113bd3ab40472b445fe8 HEAD -- $P
git status --short -- $P
```

Empty output means the coverage record still matches. If there is output, read the diff against the coverage table, run the full check, and confirm that each row still describes the code. Only then replace the commit hash in this file with `git rev-parse HEAD`, and update the line numbers. If covered files have uncommitted changes, leave the hash alone and tell the user. They decide when to commit.

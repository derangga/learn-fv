---
name: verify-uc1-idempotent-charge
description: Use when a change touches UC1 payment code, meaning the provider's charge handling and idempotency record in internal/uc1/core, spec/tla/UC1.tla, bend/uc1, mutants/uc1 or services/payment. Runs the checks that show an order is never charged twice (property P1) and tells you how to read a failure.
---

# Verify UC1: an order is never charged twice

**Property (P1).** For every order, the provider's ledger holds at most one "money taken" row: `pr(s,o).chargeCount <= 1`. The contract is `properties/UC1.md` section 3.

**Harm if it breaks.** A customer is charged twice when a payment request is retried, duplicated or replayed after a crash.

**The rule that keeps it true.** On `ChargeReqRecv`, the provider charges only when the idempotency record is `NoRec`. Any other record only queues a replay of the stored result.

## Run it

Inside the Nix dev shell, from any directory:

```bash
nix develop --command bash .claude/skills/verify-uc1-idempotent-charge/check.sh          # all stages
nix develop --command bash .claude/skills/verify-uc1-idempotent-charge/check.sh quick    # skips TLC
```

The tools are pinned by `flake.lock`: TLC 2.18 (nixpkgs `tlaplus-1.8.0`), bend 2.0.40, go 1.26.10. Exit code 0 and the last line `ALL UC1 P1 CHECKS PASS` mean every stage passed. A full run took 47 s on a MacBook M4 on 2026-11-23. Use `quick` while editing Go or Bend. Use the full run before you hand off, and always when you touch `spec/tla/UC1.tla`.

Do not run `spec/tla/UC1_wall_n2.cfg`. It is the N=2 contract bound, it did not finish in 62 minutes, and TLC metadirs at contract bounds have filled a disk before (86 GB on the UC2 run). `check.sh` wraps each TLC call in `timeout` and deletes its scratch directory.

## Which check reads which file

TLC and Bend never read `internal/uc1/core/core.go`. Each tool checks its own copy of the rule. Only the Go tests and the conformance harness look at the real Go code. A break in `core.go` shows up only in the Go stage.

| Stage in `check.sh` | Reads | Fails when |
|---|---|---|
| Bend proofs | `bend/uc1/PROOF.bend`, `LAWS.bend`, `spec.bend`, `code.bend` | `ALL PROOFS CHECK` is missing. The error names the lemma, for example `p1_step` or `inv_step`. |
| Bend mutants | `bend/uc1/mutants/*`, run by `mutants/run.sh` | A mutant is accepted, or rejected for another reason than its `EXPECT` file says. |
| Go tests | `internal/uc1/core` (`TestP1NoDoubleCharge`, `TestInv`, `TestPinChargeReqRecv`), `mutants/uc1`, `services/payment` (`TestP1NoDoubleCharge`), `harness/conformance` (Go core against compiled Bend), `harness/tlcreplay` (stored TLC traces replayed through Go) | A test fails. A conformance failure means the Go core and the Bend port disagree. |
| TLC, `UC1.cfg` | `spec/tla/UC1.tla` at N=1 | Any invariant or property is violated. |
| TLC, `UC1_buggy.cfg` and `UC1_buggy_m3.cfg` | `spec/tla/UC1_buggy.tla` (M1, no idempotency check) and `UC1_buggy_m3.tla` (M3, check-then-act race) | They do NOT violate `NoDoubleCharge`. These runs must fail. |

## Coverage record

Confirmed against the code at commit `8131d4d870f66e3f8ee3113bd3ab40472b445fe8` (2026-11-23). The covered paths had no uncommitted changes then. Line numbers are as of that commit.

| What | Where |
|---|---|
| Go rule | `internal/uc1/core/core.go`, `Step`, case `ChargeReqRecv` (lines 297-309) |
| TLA+ rule | `spec/tla/UC1.tla`, `Step`, rule A8 (lines 94-102). Property `NoDoubleCharge` (line 281), `Inv` (274), pin `PinChargeReqRecv` (360). Bounds in `spec/tla/UC1.cfg`. |
| Bend rule | `bend/uc1/code.bend`, `charge_recv` (lines 57-68) and the `step` chain that calls it |
| Bend laws | `bend/uc1/LAWS.bend`: `init_inv`, `inv_step`, `inv_run`, `p1_step`, `p1_run`, and the A8 pin law. Proofs in `PROOF.bend`. |
| Mutants of the same bug | Go `mutants/uc1/mutants.go` (`StepM1`, `StepM3`). TLA+ `UC1_buggy.tla`, `UC1_buggy_m3.tla`. Bend `bend/uc1/mutants/m1`, `m3`. |
| Production path | `services/payment/store.go` calls `core.Step` inside `apply`. All business logic is `core.Step`. |

Checked bounds for TLC: `N = 1`, `Amounts = {5}`, `DupMax = 2`, `MaxCrashes = 1`, `MaxRetries = 2` per order. At N=1 TLC found 1,156,996 distinct states at depth 34 and no error. Quote the bounds with every TLC result you report.

## When a stage fails

1. **Go unit test fails** (`TestP1NoDoubleCharge`, `TestInv`, `TestPinChargeReqRecv`). The change broke `core.Step`. This is a real bug. Fix the code.
2. **Conformance fails, unit tests pass.** The Go core and `code.bend` disagree on some event list. Compare both with section 4 (rule A8) of `properties/UC1.md`. Fix the side that departs from the contract.
3. **A Bend proof fails, conformance passes.** The proof or the Bend port is stale. The failing lemma name says which law. Fix `code.bend` or the proof. Do not edit the law.
4. **TLC `UC1.cfg` reports a violation.** Read the counterexample with the `anak-intern:statechart` skill. It gives the shortest path as steps in plain words. Then feed the same events to `core.Step` in a Go test. If the Go core also reaches `chargeCount = 2`, it is a real bug in the rule. If only the model does, the spec drifted from the code or the contract, which is a modeling error. Fix the spec and say so. The package `harness/tlcreplay` can do the replay for a trace dumped with `tlc -dumpTrace json`: `Load(dir, name)` reads `<name>.json` plus `<name>.violation`, and `Replay` runs the steps through the payment service and reports the first step where service and model differ. Its tests read only `harness/tlcreplay/testdata`, and this recipe was not exercised on a `UC1.cfg` trace, so you would write a small test that points `Load` at a scratch directory.
5. **A mutant is no longer rejected.** The check has lost its teeth. Someone changed a bound, a property or a mutant. The signs differ by tool:
   - Bend: `mutants/run.sh` prints `FAIL accepted a mutant` or `FAIL wrong reason`.
   - TLC: `UC1_buggy.cfg` or `UC1_buggy_m3.cfg` ends with no `NoDoubleCharge` violation.
   - Go: `TestMutantsRejectedByChecks` or `TestHarnessRejectsMutants` fails on a mutant subtest while the `internal/uc1/core` tests pass. These two tests are green when the mutants are rejected, which is the healthy state. If a `core` test fails as well, a change to `core.go` is the likelier cause (for example, the M5 subtest fails when the real rule changes), not a weak mutant check.

   Stop and ask the user. Do not make it fail again by editing the mutant.

Read every TLC result with `anak-intern:statechart`, passes included. A pass gets a chart of how the system moves between states.

## When the change is meant to alter the rule

- `properties/UC1.md`, the approved `bend/uc1/LAWS.bend` and the bounds in `.cfg` files are frozen. If the intended change needs one of them, stop and ask the user. Do not edit them yourself.
- Change the Go core, `UC1.tla` and `code.bend` together, so the three copies of the rule stay equal. Then run the full check.
- After you change `spec/tla/UC1.tla` or any `UC1_reach_*` or `UC1_buggy*` cfg, regenerate the stored TLC traces with `nix develop --command go generate ./harness/tlcreplay` (it runs `harness/tlcreplay/gen.sh`, about 5 s per cfg). It rewrites files under `harness/tlcreplay/testdata`, so review that diff. Until you regenerate, `TestReplay*` replays the old traces and stays green, so that stage does not see your spec change.
- Log the result in `experiment-log.md` using the entry template in section 6, with the command and its pasted output.
- Do not commit unless the user tells you to.

## What this does not cover

- TLC covers N=1 only. N=2 is a recorded wall: after 62 minutes, 9,079,945 distinct states, no violation seen. That is not a proof.
- Bend runs the plain gate. `bend` prints `Use --verdict for mathematical validity`, and `check.sh` does not run it. Bend's event lists include messages that were never sent, so its model is stronger than TLC's network.
- P1 counts rows in the provider's ledger as the model sees them. M3 models a race as an extra event. No test here runs real concurrent requests against the real ledger.
- A charge on an order that already `Failed` (mutant M5) does not break P1. Only pins A8 and A13 catch it.
- The HTTP, storage and outbox code in `services/payment` is covered only where it calls `core.Step`, and by the seeded `TestP1NoDoubleCharge` in `services/payment`.
- Cross-side properties such as "`Paid` implies the provider charged" are not checked anywhere (`properties/UC1.md` section 6, Q7).

## Keep it in step with the code

Before you rely on this skill, list what changed since the sync commit:

```bash
P="internal/uc1 spec/tla/UC1*.tla spec/tla/UC1*.cfg bend/uc1 mutants/uc1 harness/conformance harness/tlcreplay services/payment properties/UC1.md"
git diff --stat 8131d4d870f66e3f8ee3113bd3ab40472b445fe8 HEAD -- $P
git status --short -- $P
```

Empty output means the coverage record still matches. If there is output, read the diff against the coverage table, run the full check, and confirm that each row still describes the code. Only then replace the commit hash in this file with `git rev-parse HEAD`, and update the line numbers. If covered files have uncommitted changes, leave the hash alone and tell the user. They decide when to commit.

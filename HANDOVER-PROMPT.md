# Handover prompt for the next session

Paste the section "Prompt" into a new Claude Code session at the repo root. It was written on 2026-11-23 at the end of the UC2 run, before the move from the VPS to a MacBook.

## Prompt

You are continuing a research project that verifies one small system with TLA+ (TLC) and Bend 2 over four use cases. Read `CLAUDE.md`, `README.md`, `docs/handover.md` and `experiment-log.md` first. Their rules bind you. Every property, law and bound changes only with the user's approval. Every "verified" or "proved" claim needs the command and its pasted output. Update `experiment-log.md` after every task.

### Where things stand

- Branch `master` at `479d54d` (or later) holds everything. `phase0-toolchain`, `phase1-uc1` and `phase2-uc2` are older points on the same line.
- UC1 is done and approved (checkpoint 3).
- UC2 is built but **not approved**. Bead `learn-formal-verification-8q3.5` (checkpoint 4) and epic `8q3` are open. 8q3.1 to 8q3.4 are closed.
- UC3 (epic `dao`) and UC4 (epic `fxn`) are not started. They are blocked by checkpoint 4.
- Beads: if `bd list` is empty on this machine, run `bd import .beads/export-full-2026-11-23.jsonl`.
- The last run's ledger is in `.git/orchestrate-batch/beads-epic-8q3.md`. It holds every question and answer from the run.

### Step 0: set up the new machine

1. Run `nix develop`. On macOS, `.nix/env.sh` is not needed. Confirm that `go version`, `tlc`, `bend --version` (2.0.40) and `just --list` all work. Record the machine (CPU, cores, RAM) in `experiment-log.md` §2. Every TLC and Bend timing so far came from a 2-core VPS, so new timings are not comparable without that note.
2. Run `go test ./...` and `just prove-bend`. Both must pass, as they did on the VPS. Paste the output into the log.
3. Do not run `just check-tla` or `just check-tla-buggy` until a UC2 bound is approved (see decision 1). Each hangs on a UC2 contract-bound cfg.

### Step 1: get the user's decisions for checkpoint 4

Ask the user for these decisions. Do not decide them yourself. Each is written up in `experiment-log.md` 4.15 to 4.20 and in `docs/results/uc2-*.md`.

1. **TLC checked bound for UC2.** At the contract bounds, `spec/tla/UC2.cfg` did not finish in 60 min (25,051,664 distinct states, level 8, no violation seen). The options are:
   - approve `UC2_proposed.cfg`, or `UC2_proposed_dup.cfg`, or both;
   - allow SYMMETRY on ids;
   - re-run the contract bound on the faster machine and see whether it finishes.

   Mutant M2 (`UC2_buggy_m2.cfg`) is killed only at the dup bound. After approval, swap the cfgs as UC1 did (`experiment-log.md` 4.14). The approved bound goes into `UC2.cfg`, and the contract bound moves to a `UC2_wall_*.cfg`. Handle M2 the same way, so `just check-tla-buggy` finishes.
2. **Bend law text.** Ask the user to approve `bend/uc2/LAWS.bend` and `spec.bend`, including the departures in `docs/results/uc2-bend.md` §6.
3. **Contract §5 kill table.** Three rows of `properties/UC2.md` §5 are contradicted by the tools:
   - M5a and M4 do not break P2 or P1b with signed counters.
   - M1b never triggers S7.

   The file is frozen, so ask whether to amend it or keep it and record the gap.
4. **TLA+ modelling choices** in `docs/results/uc2-tla.md`. Three need a decision:
   - Crash fires only while up, and Restart only while down, so the already-down and already-up halves of S8 and S9 are never exercised.
   - A stutter disjunct in `Next` hides deadlocks.
   - 5 reach witnesses use reduced constants.
5. **Bend M4** is a stateless half of the check-then-act race, because `LAWS.bend` fixes the `State` arity. Ask whether that is acceptable.

When the user approves, close `8q3.5` and `8q3` with the approval date in the reason. Then start UC3.

### Step 2: open findings worth fixing (only with the user's go-ahead)

These came out of the code reviews and were left open. Each is small.

- **Go mutant checker pins** (`mutants/uc2/checker_test.go`). Pins S0-S9 are checked by comparing each mutant with `core.Step`. Assert each §4 row on its own instead, so that the control could fail too.
- **Harness effect comparison** (`harness/uc2conformance`, `bend/uc2/main.bend`). Effects are compared as tallies (count and sums), not as an ordered list, and `FxReserved.sku` is not tallied. Add an ordered effect digest.
- **Harness coverage counters.** There are no counters for the mutant trigger cases: Expire on a non-Held Due record, Confirm on a non-Held record, and a duplicate Reserve with stock available. Add them, and require each to fire.
- **TLA+ M1 cfg** (`spec/tla/UC2_buggy.cfg`). It lists only 2 invariants. The other mutant cfgs list every invariant and property. Make it consistent.
- **Services have no `main`.** `services/payment` and `services/inventory` run only inside Go tests. If the user wants to run them by hand, add a small `cmd/<svc>` over `inventory.New` / `payment.NewCluster` with `ListenLocal`. That is scope the user must ask for.
- **Disk.** TLC metadirs grow to hundreds of MB and once filled `/tmp`. Run TLC jobs one at a time with `timeout`, and delete each metadir afterwards.

### Step 3: UC3 and UC4

Follow the same pipeline that UC1 and UC2 used, one bead at a time, with review and a commit per issue:

1. Go core plus its service.
2. The TLA+ spec, its buggy variant and its reach witnesses.
3. The Bend port. Commit the law text first and prove it after.
4. The mutants in all three tools, plus the harness.
5. A checkpoint report: a short summary, the log table and the surprises. Then stop and wait for the user.

`bd ready` shows what is unblocked. UC3 must show that a lease without fencing lets a stale holder write. UC4 is liveness. Read `docs/agent/tla.md` "Liveness" and `properties/UC4.md` §3-4 before you touch fairness.

### Lessons from UC2 to reuse

- Put the contract bounds in `UCn.cfg` from the start. Put any smaller bound in `UCn_proposed*.cfg`; `just check-tla` skips those. Never present a proposed bound as approved.
- Measure a TLC wall with one clean 60 min run, with nothing else running, and record the last progress line.
- Have Bend implementers stop after `LAWS.bend` parses. Commit the law text, then prove.
- Check that every Bend law is at least as strong as the contract wording. For example, P3b first came back stated by id and had to be restated over every record.
- Name the files each implementer owns. `experiment-log.md` has one writer, the orchestrator.

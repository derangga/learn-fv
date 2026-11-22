# CLAUDE.md

## Why

Research project: verify one small system with two tools, TLA+ (the TLC model checker) and Bend 2 (a proof checker), over four use cases: UC1 idempotent payment, UC2 stock reservation, UC3 lease with fencing token, UC4 liveness on the UC1 flow. Each use case checks the same properties in both tools, then records what each tool cost and where it broke. Hypotheses H1-H3 are in `docs/handover.md` §1; test them, never assume them. A failed proof or an unprovable property is a result: record it.

## What

- `docs/handover.md`: the full brief and source of truth, including the target repo layout (§4).
- `properties/UCn.md`: the frozen contract per use case. It holds the shared state model, each property mapped to a TLA+ name, a Bend law and a Go test, and the mutants.
- `spec/tla/`: TLA+ specs and `.cfg` files. `bend/`: Bend ports and proofs, with `bend/probes/` holding the soundness probes.
- `docs/results/`: one write-up per task. `experiment-log.md`: entries plus the summary table by use case and tool.
- Planned: `internal/<uc>/core/` (the pure `Step`), `internal/sim/`, `services/`, `harness/`, `mutants/`.

## How

Run `source .nix/env.sh` first in every shell. It puts the pinned tools on PATH: go, tlc, bend 2.0.40, just, hyperfine, jq and sqlite3. `nix develop` cannot run in this sandbox, so this file stands in for it. After a `flake.lock` change, ask the user to rebuild `.nix/dev` and regenerate `env.sh`. Scratch files and TLC metadirs go in `$TMPDIR`. Work without sudo and leave the system NixOS configuration alone.

Checks:

- TLC: `tlc -metadir $TMPDIR/<run> -config spec/tla/<X>.cfg spec/tla/<X>.tla`
- Bend: `bend bend/<dir>/PROOF.bend`. A law counts as proved only when this prints `ALL PROOFS CHECK`.
- Soundness probes: `bash bend/probes/run.sh`. It must exit 0.

Read the matching doc before you start a task:

- Bend port, laws or proofs: `docs/agent/bend.md`
- TLA+ spec or a TLC run: `docs/agent/tla.md`
- Go core, services, sim, mutants or harness: `docs/agent/go.md`
- Logging a result: the entry template in `experiment-log.md` §6

## Integrity rules

These apply to every task.

- Keep every property, law and invariant exactly as the user approved it. `properties/UCn.md` and approved `LAWS.bend` files are frozen. If one looks wrong, stop and ask.
- Bounds live in the `.cfg` files, and every result report states them. Change a bound or add an assumption only with the user's approval, and log it.
- Back every "verified" or "proved" claim with the command and its pasted output.
- Each use case keeps at least three mutants. Each mutant is the same bug in every tool. TLA+, Bend, and the harness where possible must each reject it, and you record what each tool says.
- If Bend ever accepts a false statement, record it at the top of `experiment-log.md`.

## Process

There are five phases: 0 toolchain, then 1-4 for UC1-UC4. Stop at each checkpoint and wait for the user's approval:

1. End of Phase 0.
2. All four `properties/UCn.md` files written. No TLA+, Bend or harness work starts on any use case before this approval.
3. Each use case done in both tools, including its mutants and the harness.

A checkpoint report is a short summary, the log table, and what surprised you. Update `experiment-log.md` after every task.

Stop rule, per use case and tool: 2 hours of authoring or 15 failed iterations, whichever comes first. Then record the wall and move on. A failed iteration is a failed model check for TLA+ and a failed proof for Bend.

Commit messages name no issue-tracker ids.

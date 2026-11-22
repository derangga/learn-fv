# CLAUDE.md

## Purpose

Research project: check one small system with two tools, TLA+ (TLC model checker) and Bend 2 (proof checker), over four use cases of rising difficulty (UC1 idempotent payment, UC2 stock reservation, UC3 lease with fencing token, UC4 liveness on the UC1 flow). Verify the same properties in both tools, then record what each tool cost and where it broke. Source of truth: `docs/handover.md`.

Hypotheses to test, not to assume:

- H1: Bend can cover the use cases TLA+ covers. Measure the price and find where it stops working.
- H2: Bend's checker is faster per run, but authoring cost (writing proofs) dominates the total. TLC may reach a result sooner on small models because it needs no proof.
- H3: Bend proves a claim for all event sequences, while TLC only covers the bounds we set.

A failed proof or an unprovable property is a valid result. Record it. Do not hide it.

## Environment

- Run `source .nix/env.sh` before any tool (go, gopls, sqlite3, tlc, just, hyperfine, jq, bend 2.0.40). It puts the pinned devShell tools on PATH. It is hand-built from the devShell derivation because `nix develop` cannot run in Claude's sandbox (no Nix daemon socket, cache.nixos.org blocked).
- `.nix/dev` is a GC root the user created with `nix build .#devShells.x86_64-linux.default -o .nix/dev`. After any `flake.lock` change the user re-runs that command outside the sandbox, and `.nix/env.sh` must be regenerated from the new devShell's inputs. Tell the user; do not edit `flake.lock` silently.
- Never use sudo. Never touch the system NixOS configuration. Bind 127.0.0.1 only; expose nothing beyond localhost.
- Scratch files go in `$TMPDIR`. Set the TLC metadir under `$TMPDIR`. `env.sh` sets `JAVA_TOOL_OPTIONS=-Djava.io.tmpdir=$TMPDIR` because the JVM default `/tmp` is read-only in the sandbox.
- Bend 2 is new; do not guess syntax. Read `docs/bend-guide.txt` (guide for 2.0.40).

## Integrity rules

- Never weaken, delete, or rewrite a property, law, or invariant to make a check pass. If one looks wrong, stop and ask.
- Laws: draft them in `LAWS.bend` only as a faithful translation of the approved `properties/UCn.md`. The user approves them; after approval `LAWS.bend` is frozen like the properties. Never edit an approved law to make it pass; stop and ask.
- Never shrink TLC bounds or add assumptions silently. Bounds live in the `.cfg` files; every result report states them.
- Never call something verified without showing the command and its output.
- Keep a mutant corpus: at least three buggy variants per use case, for example removing the idempotency check, a check-then-act race, an off-by-one in reservation expiry, a lease without fencing, a refund without a status check. Each mutant is the same bug expressed in each tool: TLA+ variants are `spec/tla/UCn_buggy*.tla`, Go mutants live in `mutants/<uc>/`, Bend mutants in `bend/ucN/mutants/`. Each must be rejected by the TLA+ model, by the Bend port, and by the harness where possible. Record what each tool says.
- Keep the soundness probes in `bend/probes/`. If Bend ever accepts a false statement, record it at the top of `experiment-log.md`.

### Bend proofs

In Bend, close no proof with any axiom, hole, or escape hatch. The 2.0.40 guide names these; none may appear in anything a proof depends on:

- `@unsafe` on a def (skips the termination check) and its sugar `def f?(...)`.
- Open holes: `?TODO` and `?name`. Use `?name` only to inspect a goal, and remove it before the proof counts.
- A law without a def: every law in `LAWS.bend` needs a def of the same name in `PROOF.bend`. An open claim means not proved.
- Foreign code: `import "./x.c"` or `import "./x.js"` effect defs.

A Bend claim counts as proved only when `bend PROOF.bend` prints `ALL PROOFS CHECK`. Paste the real output in `experiment-log.md`. `SOME PROOFS FAIL` means not proved.

`bend PROOF.bend --verdict` rechecks with a small kernel proven in Lean. Whether it works offline here is recorded in `docs/results/phase0-bend-guide.md`; read that before relying on it.

You write `PROOF.bend` and the Bend port.

## Repo layout

Target layout; directories are created as phases reach them.

```
flake.nix  justfile  CLAUDE.md  experiment-log.md
docs/handover.md         the full brief
docs/bend-guide.txt      Bend 2.0.40 guide
docs/bend-base.txt, docs/bend-guide-effects.txt   Base library and effects guide
docs/results/            per-task result write-ups; feed experiment-log.md
properties/UC1.md ...    plain-English properties, frozen after approval
spec/tla/                UCn.tla, UCn.cfg, UCn_buggy variants
bend/ucN/                LAWS.bend, PROOF.bend, the Bend port of the core logic
bend/probes/             soundness probes
services/payment/        order and payment (UC1, UC4)
services/inventory/      stock reservation (UC2)
services/lease/          lease manager and worker (UC3)
internal/<uc>/core/      pure logic: Step(state, event) -> (state, effects)
internal/sim/            injectable clock, fault-injecting transport
harness/                 conformance tests
mutants/                 deliberately buggy variants
```

Design rules:

- Go with `chi`. SQLite through `modernc.org/sqlite`, `CGO_ENABLED=0`.
- Each service is a few hundred lines with its own SQLite file. Never share one SQLite file between services.
- No message broker. Outbox table plus HTTP.
- All business logic lives in the pure `core` package. HTTP and database code stay thin. The TLA+ model and the Bend port both mirror `Step`.
- Inject the clock and the transport. The transport drops, duplicates, delays, and reorders messages and crashes a service at chosen points, all driven by a seed so every run reproduces. SQLite serializes writes and hides races, so never rely on natural timing.
- `just` recipes: `check-tla`, `prove-bend`, `harness`, `test`, `all`.
- The Bend proof covers the Bend port, not the Go service. The harness closes the gap: same seeded event sequences through the Go core and the compiled Bend program, compare final states; replay TLC counterexample traces against the Go service as tests (best effort, record how hard it was).

## Process

Phases: 0 toolchain, 1 UC1, 2 UC2, 3 UC3, 4 UC4. Stop and report at each checkpoint, then wait for approval:

1. End of Phase 0.
2. Properties written for all four use cases (`properties/UC1.md` to `UC4.md`, each property mapped to a TLA+ invariant, a Bend law, and a Go test). Frozen after approval.

No verification work (TLA+ specs, Bend ports or proofs, harness) on any use case before the user approves `properties/UC1-UC4.md`.
3. UC1 done in both tools, including mutants and harness.
4. Each later use case.

A report is a short summary, the log table, and what surprised you.

Update `experiment-log.md` after every task. Each entry records:

- date and time, tool, use case, what was done.
- authoring time (spec or proof, including AI iterations and how many).
- machine time: cold start and warm run, from `hyperfine`.
- result, size in lines, friction or walls hit.
- TLC runs: bounds, state count, distinct states, wall time.

Keep a summary table by use case and tool. Stop rule per tier (one use case) and tool: 2 hours of authoring or 15 failed iterations, whichever comes first. A failed iteration is a failed spec or model-check iteration for TLA+, a failed proof iteration for Bend. Then record the wall and move on. The user may set different limits.

## Git

Commit only when asked. Branch first if on master. Never add a `Co-Authored-By:` trailer or any AI/model attribution to commit messages. Do not mention issue-tracker ids in commits.

# Learn formal verification: TLA+ and Bend 2

## What this is

A research project. It verifies one small system with two tools: TLA+ (checked by the TLC model checker) and Bend 2 (a proof checker). It does this over two use cases:

- UC1: idempotent payment.
- UC2: stock reservation.

Each use case checks the same properties in both tools. We then record what each tool cost and where it broke. A failed proof or an unprovable property is a result, so we record it.

The hypotheses H1 to H3 are in `docs/handover.md` section 1. We test them. We do not assume them.

Status:

| Use case | Status |
|---|---|
| UC1 | Done. TLA+, Bend, mutants and harness are checked. TLC is checked at N=1; N=2 is a recorded wall. |
| UC2 | Done, approved at checkpoint 4 (2026-11-23). Go core and inventory service, Bend proofs (29 laws), TLA+ spec, 10 mutants and the Go vs Bend harness. TLC is checked at reduced bounds (`UC2.cfg`, `UC2_dup.cfg`); the contract bound is a recorded wall (`UC2_wall_contract.cfg`). |

## Project structure

```text
.
├── README.md, CLAUDE.md, AGENTS.md   Project guide, agent rules, beads agent notes
├── experiment-log.md                 Log entries and the summary table by use case and tool
├── docs/
│   ├── handover.md                   The brief and source of truth
│   ├── agent/                        How-to notes: bend.md, tla.md, go.md
│   ├── results/                      One write-up per task (phase0-*, uc1-*, uc2-*)
│   ├── bend-*.txt                    Saved Bend language guide and Base library listing
│   └── comparison-bend-vs-tla.md, article-bend-vs-tla.md   Write-ups of the comparison
├── properties/
│   ├── UC1.md                        Frozen contract: idempotent payment
│   └── UC2.md                        Frozen contract: stock reservation
├── spec/tla/                         TLA+ specs and cfgs: Smoke, UC1, UC2, *_buggy*, *_reach_*, *_wall_*
├── bend/
│   ├── uc1/, uc2/                    code.bend, spec.bend, LAWS.bend, PROOF.bend, main.bend; mutants/ with run.sh
│   ├── probes/                       False laws that Bend must reject
│   └── smoke/, io/                   Phase 0 smoke proof and I/O spike
├── internal/
│   ├── uc1/core/, uc2/core/          The pure Step(state, event) -> (state, effects), with its tests
│   └── sim/                          Seeded fake clock, fault network and crasher
├── services/
│   ├── payment/                      UC1 order and provider services, SQLite outbox, HTTP
│   └── inventory/                    UC2 inventory service, same shape
├── mutants/uc1/, uc2/                Go mutants and the tests that must reject them
├── harness/
│   ├── conformance/, uc2conformance/ Go core against the compiled Bend port
│   └── tlcreplay/                    Replay of stored TLC traces through the service
├── .claude/skills/                   verify-uc1-idempotent-charge, verify-uc2-stock-never-oversold
├── .beads/                           Issue tracker (bd)
├── justfile                          Check recipes
└── flake.nix, flake.lock             Pinned toolchain
```

## Repo layout

| Path | What is in it |
|---|---|
| `docs/handover.md` | The full brief and source of truth. |
| `docs/agent/` | Short how-to notes: `bend.md`, `tla.md`, `go.md`. |
| `docs/results/` | One write-up per task. |
| `experiment-log.md` | Log entries and the summary table by use case and tool. |
| `properties/UCn.md` | The frozen contract per use case. |
| `spec/tla/` | TLA+ specs and their `.cfg` files. |
| `bend/ucN/` | Bend ports (`code.bend`, `spec.bend`), laws (`LAWS.bend`), proofs (`PROOF.bend`). |
| `bend/ucN/mutants/` | Bend mutants and their runner `run.sh`. |
| `bend/probes/` | Soundness probes: false laws that Bend must reject. |
| `bend/smoke/`, `bend/io/` | Phase 0 smoke proof and I/O spike. |
| `internal/ucN/core/` | The pure `Step(state, event) -> (state, effects)`. |
| `internal/sim/` | Fake clock, fault network and crasher, all seeded. |
| `services/payment/`, `services/inventory/` | The UC1 and UC2 services (Go packages). |
| `mutants/ucN/` | Go mutants. |
| `harness/` | Conformance harness (Go core vs compiled Bend) and TLC trace replay. |
| `justfile` | The check recipes. |
| `flake.nix`, `flake.lock` | The pinned toolchain. `.nix/env.sh` (git-ignored) is generated only for the Claude sandbox. |
| `.claude/skills/` | One verify skill per use case: a single `check.sh` that runs every check and explains how to read a failure. |

## Setup

Where it works, run `nix develop`. It gives you go, gopls, sqlite, TLC (tlaplus 1.8.0), just, hyperfine, jq and bend 2.0.40. On the MacBook it works, and then `.nix/env.sh` and the sandbox quirks below do not apply.

In the Claude sandbox `nix develop` cannot run. Use this in every shell instead:

```bash
source .nix/env.sh
```

It puts the pinned go, gopls, sqlite3, tlc, just, hyperfine, jq and bend on PATH. It also sets `CGO_ENABLED=0` and points the JVM temp dir at `$TMPDIR`. After a `flake.lock` change, rebuild `.nix/dev` and regenerate `env.sh`.

Sandbox quirks (from `experiment-log.md`):

- `just` writes recipe scripts under `XDG_RUNTIME_DIR`, which is read-only. Run `export XDG_RUNTIME_DIR=$TMPDIR`.
- The Go cache dirs are read-only. Run `export GOCACHE=$TMPDIR/gocache GOMODCACHE=<writable dir> GOPROXY=off`. Without a populated module cache, drop `GOPROXY=off` and let Go download.
- `/tmp` is read-only for the JVM. Put TLC metadirs in `$TMPDIR` (`-metadir $TMPDIR/<run>`).
- `~/.bend` is read-only and `bend-lang.com:443` is blocked. `bend` still runs.
- Do not use sudo. Do not change the system configuration.

## Running checks

### Just recipes

Run `source .nix/env.sh` first (and the quirks above). List the recipes with `just`.

| Recipe | What it does |
|---|---|
| `just test` | `go test ./...`. |
| `just check-tla` | TLC on every cfg in `spec/tla/` except `*_buggy*`, `*_reach*`, `*_wall*` and `*_proposed*`. |
| `just check-tla-buggy` | TLC on every `*_buggy*` cfg. Each must produce a counterexample. It fails if one passes. |
| `just prove-bend` | `bend` on `bend/smoke/PROOF.bend` and `bend/uc*/PROOF.bend` (each must print `ALL PROOFS CHECK`), then the probes, then every `bend/uc*/mutants/run.sh`. |
| `just harness` | `go test ./harness/...`. |
| `just all` | `test`, `check-tla`, `check-tla-buggy`, `prove-bend`, `harness`, in that order. |

`just check-tla-buggy` runs `UC2_buggy_m2.cfg` with no timeout, and that cfg uses the UC2 contract bounds, so it never finishes. Run the UC2 buggy cfgs by hand with `timeout`, or use the verify skills in `.claude/skills/`, which skip it.

### TLC

```bash
tlc -metadir $TMPDIR/<run> -config spec/tla/<X>.cfg spec/tla/<X>.tla
```

Example, the cheap smoke spec:

```bash
tlc -metadir $TMPDIR/smoke -config spec/tla/Smoke.cfg spec/tla/Smoke.tla
rm -rf $TMPDIR/smoke
```

The cfg name tells you what the run is for. The module is the part before the first suffix, except for buggy variants, which have their own `.tla`.

| Cfg name | Meaning |
|---|---|
| `UCn.cfg` | The good spec. It must pass. |
| `UCn_buggy*.cfg` | A mutant (`UCn_buggy_m3.tla` and so on). TLC must report a violation. |
| `UCn_reach_*.cfg` | A reachability witness. It asserts a state is never reached, so TLC must violate it. This shows a property is not vacuous. |
| `UCn_wall_*.cfg` | A recorded wall: the contract bounds that did not finish. |

Warnings:

- `UC2.cfg` and `UC2_dup.cfg` are the approved reduced bounds (2,055,926 and 312,995 distinct states, no error). `UC2_wall_contract.cfg` is the contract bound and does not finish: 60 min stopped at 25 M distinct states with no violation seen. Do not run it, and do not move bounds without approval.
- `UC1.cfg` is the approved N=1 bound (about 5 min on a 2-core VPS, 23 s on the MacBook). `UC1_wall_n2.cfg` is the contract bound and does not finish.
- TLC can fill the disk. It spills states to the metadir. Remove each run's metadir when it ends: `rm -rf $TMPDIR/<run>`.
- Every run costs about 1.5 s of JVM start-up.

More: `docs/agent/tla.md`.

### Bend

```bash
bend bend/uc1/PROOF.bend
bend bend/uc2/PROOF.bend
bend bend/smoke/PROOF.bend
```

A law counts as proved only when the output says `ALL PROOFS CHECK`. `SOME PROOFS FAIL` means it is not proved. `PROOF.bend` must not use `@unsafe`, `?` holes, an open law or a foreign import.

Other Bend checks:

```bash
bash bend/probes/run.sh          # 14 false laws; each must be rejected; exit 0
bash bend/uc1/mutants/run.sh     # each mutant must be rejected for the expected reason
bash bend/uc2/mutants/run.sh
```

- `bend <file> --verdict` (the Lean kernel recheck) cannot run here: no Lean, and `~/.bend` is read-only. Every `ALL PROOFS CHECK` is from the plain gate only. Say so in reports.
- To compile a port for the harness: `bend bend/uc1/main.bend -o $TMPDIR/uc1bin`. The harness does this itself, pipes events on stdin and parses one `key=value` line.

More: `docs/agent/bend.md`, and the guide in `docs/bend-guide.txt`.

### Go

```bash
export GOCACHE=$TMPDIR/gocache GOMODCACHE=<writable dir> GOPROXY=off
go test ./...                    # everything
go test ./internal/uc1/... ./internal/uc2/...
go test ./internal/sim/...
go test ./services/payment/...
go test ./services/inventory/...
go test ./mutants/...
go test ./harness/...
```

The harness tests compile Bend ports, so they need `bend` on PATH and take longer (the UC1 run compiles in about 8 s).

## Running the services

There is no standalone binary yet. `services/payment` (UC1) and `services/inventory` (UC2) are Go packages with no `main`. They run inside Go tests, on top of `internal/sim`: a seeded fault network (drop, duplicate, delay, reorder), a fake clock and a crasher. Each service owns a SQLite file (pure-Go `modernc.org/sqlite`) with an outbox table. They talk over HTTP and no message broker is used.

`ListenLocal` in each package serves a handler on a loopback address only (`127.0.0.1:0` picks any port). `TestListenLocalOnly` checks it.

Commands that drive the services:

```bash
go test ./services/payment/...  -run TestHappyPathToPaid -v
go test ./services/payment/...  -run 'TestP1NoDoubleCharge|TestDifferentialAgainstCoreFold' -v
go test ./services/inventory/... -run TestInvUnderFaultRuns -v
go test ./services/inventory/... -run TestDifferentialAgainstCoreFold -v
```

- Flow tests: `TestHappyPathToPaid`, `TestRefundFlow`, `TestReserveConfirmFlow`, `TestExpiryByInjectedClock`.
- Crash tests: `TestCrashAfterCommitBeforeSend`, `TestProviderCrashAfterCommitBeforeReply`, `TestCrashAfterCommitBeforeReply`.
- Fault runs over many seeds: `TestP1NoDoubleCharge` (payment) and `TestInvUnderFaultRuns` (inventory, seeds 1 to 150). They check the invariants after every step.
- Differential check: `TestDifferentialAgainstCoreFold` in both packages. The persisted state must equal a fold of `core.Step` over the events the service applied.
- Replay of TLC traces against the service: `go test ./harness/tlcreplay/...`.

To try a service by hand you would write a small `main` over `inventory.New` (or `payment.NewCluster`) and `ListenLocal`. That does not exist in the repo.

More: `docs/agent/go.md`, `docs/results/uc1-services.md`, `docs/results/uc2-services.md`.

## Working guidelines

The rules are in `CLAUDE.md` and `docs/handover.md` sections 7 to 9. In short:

- **Frozen properties.** `properties/UCn.md` and approved `LAWS.bend` files are frozen. Never weaken, delete or rewrite a property, law or invariant to make a check pass. If one looks wrong, stop and ask.
- **Bounds.** Bounds live only in `.cfg` files. Change a bound or add an assumption only with approval, and log it. Every result report states its bounds, states generated, distinct states and wall time.
- **Evidence.** Back every "verified" or "proved" claim with the command and its pasted output.
- **Mutants.** Each use case keeps at least three mutants. Each is the same bug in every tool. TLA+, Bend and the harness (where possible) must reject it. Record what each tool says.
- **Soundness alert.** If Bend ever accepts a false statement, record it at the top of `experiment-log.md` (section 1). Keep the probes in `bend/probes/` passing.
- **Checkpoints.** There are three phases: 0 toolchain, then UC1 and UC2. Stop and wait for the user's approval at: the end of Phase 0; both `properties/UCn.md` written (no TLA+, Bend or harness work before this); each use case done in both tools with mutants and harness.
- **Stop rule.** Per use case and tool: 2 hours of authoring or 15 failed iterations, whichever comes first. Then record the wall and move on. A failed iteration is a failed model check (TLA+) or a failed proof (Bend).
- **Log after each task.** Update `experiment-log.md` using the entry template in its section 6. Add a write-up in `docs/results/`.
- **Commits.** Commit only when asked. Branch first if on `main`. Commit messages name no issue ids.
- **Issues.** The issue tracker is beads: use `bd` (state lives in `.beads/`).

Read the matching doc before a task: `docs/agent/bend.md` for Bend, `docs/agent/tla.md` for TLA+ and TLC, `docs/agent/go.md` for Go, services, sim, mutants and the harness.

## Where the results are

- `experiment-log.md`: soundness alerts, setup, the summary table and one entry per task.
- `docs/results/`: the evidence per task, for example `uc1-tla.md`, `uc2-bend.md`, `uc2-harness.md`.

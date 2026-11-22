# Handover: TLA+ vs Bend verification experiment

Read this whole file first. Then do Phase 0 only, report, and wait for my go-ahead before Phase 1.

## 1. Goal

I am researching formal verification in the age of AI. We are building one small project that checks the same system with two tools, TLA+ (TLC model checker) and Bend 2 (proof checker), and we compare them head to head.

The project has four use cases of rising difficulty. For each one we verify the same properties in both tools, then we record what each tool cost and where it broke.

Hypotheses to test, not to assume:

- H1: Bend can cover the use cases TLA+ covers. We measure the price and find where it stops working.
- H2: Bend's checker is faster per run, but authoring cost (writing proofs) dominates the total. TLC may reach a result sooner on small models because it needs no proof.
- H3: Bend proves a claim for all event sequences, while TLC only covers the bounds we set.

A failed proof or an unprovable property is a valid result. Record it. Do not hide it.

## 2. Environment

- NixOS VPS. Work only inside a project flake with `devShells.default`. Do not touch the system NixOS configuration. Do not use sudo.
- Services listen on localhost only. Open no ports.
- Language: Go with `chi`. SQLite through `modernc.org/sqlite` (pure Go, no CGO), so builds stay simple under Nix.

### Tool installation facts I found (verify before relying on them)

- Bend 2: the release notes list three install routes: the curl script from bend-lang.com, Homebrew, and Nix with `nix profile install github:bendlang/bend`. The repository likely has a flake. Check with `nix flake show github:bendlang/bend`. Use it as a flake input and let `flake.lock` pin the exact revision.
- Do not pipe `curl | sh`. If the flake route fails, download `install.sh` into a new empty directory, read it fully, and tell me what it fetches before running anything.
- Search results for "bend cargo install" describe the older Bend 1 (HVM). Ignore them.
- TLA+: nixpkgs has `tlaplus` and `tlaplus18`, which provide `tlc`, `pcal`, and `tlasany`. The tools need Java 11 or newer. Check which attribute exists in the pinned nixpkgs with `nix search nixpkgs tlaplus`.
- Use the nixpkgs branch the VPS runs (`nixos-version` tells you).

Unverified starting point for `flake.nix`. Fix whatever does not evaluate:

```nix
{
  description = "verifylab: TLA+ vs Bend";
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/<branch the VPS runs>";
    flake-utils.url = "github:numtide/flake-utils";
    bend.url = "github:bendlang/bend";
  };
  outputs = { self, nixpkgs, flake-utils, bend }:
    flake-utils.lib.eachDefaultSystem (system:
      let pkgs = nixpkgs.legacyPackages.${system};
      in {
        devShells.default = pkgs.mkShell {
          packages = [
            pkgs.go pkgs.gopls pkgs.sqlite
            pkgs.tlaplus pkgs.jdk17
            pkgs.just pkgs.hyperfine pkgs.jq
            bend.packages.${system}.default   # confirm the output name
          ];
        };
      });
}
```

### Bend 2 is new

Bend 2 launched in September 2026. Your training knowledge probably does not cover it. Do not guess its syntax. Learn it from `bend guide`, and follow whatever AGENTS.md integration the guide describes. Save the guide output to `docs/bend-guide.txt` and record the Bend version in the log, so we know exactly what we tested.

## 3. Phase 0: toolchain gate

Do this and stop.

1. Create the flake and the devShell. Confirm `nix develop` works.
2. TLA+: run `tlc` on a trivial spec. Record cold-start and warm-start wall time with `hyperfine`.
3. Bend: run `bend guide`. Write one trivial law in `LAWS.bend` and its proof in `PROOF.bend`, and run `bend PROOF.bend`.
4. Soundness probe: try to prove a clearly false statement. The checker must reject it. Keep these in `bend/probes/` and record the real output.
5. Find out how a Bend program takes input and prints output (stdin, arguments, or none). The conformance harness depends on it.
6. Write `CLAUDE.md` with the integrity rules from section 7 and the repo conventions.
7. Create `experiment-log.md`.

Go/no-go: if Bend cannot be installed or run, stop and report exactly what failed. Do not continue to Phase 1.

## 4. Repository layout

```
flake.nix  justfile  CLAUDE.md  experiment-log.md
docs/                    bend-guide.txt, notes
properties/UC1.md ...    plain-English properties, frozen after my approval
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

- Each service is small, a few hundred lines. Each service has its own SQLite file. Never share one SQLite file between services.
- No message broker. Use an outbox table plus HTTP.
- All business logic lives in the pure `core` package. HTTP and database code stay thin. The TLA+ model and the Bend port both mirror this `Step` function.
- Inject the clock and the transport. The transport can drop, duplicate, delay, and reorder messages, and crash a service at chosen points, all driven by a seed so every run is reproducible. SQLite serializes writes and can hide races, so do not rely on natural timing.
- `just` recipes: `check-tla`, `prove-bend`, `harness`, `test`, `all`.

## 5. Use cases and properties

Write each property in plain English in `properties/UCn.md`, mapped to a TLA+ invariant, a Bend law, and a Go test. Stop for my approval before starting verification work. After approval these files are frozen.

Proposed properties (refine them, then ask me):

UC1, idempotent payment (order service and payment service, with retries):
- P1: an order is never charged more than once, even with retries and duplicate messages.
- P2: a refund happens only on an order that was paid.
- P3: terminal order states never change.

UC2, stock reservation:
- P1: available stock never goes below zero.
- P2: available + reserved + sold always equals the total.
- P3: an expired reservation returns its stock exactly once.
- P4: a reservation cannot be confirmed after it expired.

UC3, lease with fencing token:
- P1: every grant gets a strictly larger fencing token than the previous grant.
- P2: the protected resource never accepts a write with a token lower than one it has already seen.
- Expected finding: a lease without fencing allows a stale holder to write after a pause. The spec for the buggy variant must show this. The fenced variant must not.

UC4, liveness on the UC1 payment flow:
- L1: every payment that succeeded at the provider is eventually recorded in the order service.
- State the fairness assumptions explicitly (retries keep happening, services eventually restart). TLC liveness checking is subtle and easy to get wrong. Explain each assumption.

## 6. Verification tracks

### TLA+

- Model the network with loss, duplication, and reordering, and model service crash and restart.
- Put TLC constants in the `.cfg`. Write the bounds in the log and in every result report. Never change bounds silently.
- Each use case has a buggy variant that must produce a counterexample.
- Record state count, distinct states, and wall time per run.

### Bend

- Port the core `Step` function to Bend. Write the laws in `LAWS.bend` and the proofs in `PROOF.bend`.
- Prove that every event preserves the invariant, then prove it for any list of events. Faults are modeled as arbitrary event lists.
- Expect UC2 to need arithmetic lemmas the standard library may not have. Record exactly what is missing and how much work each lemma takes.
- Start with the smallest version of each law and grow it.

### Conformance harness

The Bend proof is about the Bend port, not the Go service. The harness closes that gap:

- Run the same seeded random event sequences through the Go core and the compiled Bend program. Compare the final states. If Bend programs cannot take input, generate Bend programs with the events embedded.
- Replay TLC counterexample traces against the Go service as tests. Best effort. Record how hard this was.

## 7. Integrity rules (also put these in CLAUDE.md)

- Never weaken, delete, or rewrite a property, law, or invariant to make a check pass. If one looks wrong, stop and ask me.
- Never shrink TLC bounds or add assumptions silently.
- In Bend, do not close a proof with any axiom, hole, or escape hatch. Check the guide for what exists. Never call something proved unless `bend PROOF.bend` ran clean. Paste the real output in the log.
- Never call something verified without showing the command and its output.
- Keep a mutant corpus: at least three buggy variants per use case, for example removing the idempotency check, a check-then-act race, an off-by-one in reservation expiry, a lease without fencing, a refund without a status check. Each mutant must be rejected by the TLA+ model, by the Bend port, and by the harness where possible. Record what each tool says.
- Keep the soundness probes. If a false statement is ever accepted by Bend, record it at the top of the log.

## 8. Experiment log

Update `experiment-log.md` after every task. For each entry record:

- date and time, tool, use case, and what was done.
- authoring time (spec or proof, including AI iterations and how many).
- machine time: cold start and warm run, from `hyperfine`.
- result, size in lines, and friction or walls hit.

Keep a summary table by use case and tool. Defaults for stop rules per tier and tool: 2 hours of authoring or 15 failed proof iterations, whichever comes first. Then record the wall and move on. Tell me if you want different limits.

## 9. Checkpoints

Stop and report at each of these, then wait:

1. End of Phase 0.
2. Properties written (approval needed).
3. UC1 done in both tools, including mutants and harness.
4. Each later use case.

Phase order: Phase 1 is UC1, Phase 2 is UC2, Phase 3 is UC3, Phase 4 is UC4. A report is a short summary, the log table, and what surprised you.

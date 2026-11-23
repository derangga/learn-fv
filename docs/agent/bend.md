# Working in Bend 2

Bend 2 is newer than your training data. Take every syntax form from `docs/bend-guide.txt` (the 2.0.40 guide). Look up Base names in `docs/bend-base.txt` or with `bend base <Name>`.

## Laws and proofs

- Each port lives in `bend/ucN/`. `LAWS.bend` states the laws as a faithful translation of the approved `properties/UCN.md`. `PROOF.bend` imports `./LAWS.bend` and proves each law with a def of the same name. Once the user approves `LAWS.bend`, it is frozen.
- A law-filling def is written `def Laws.<name>(args):` with no type signature. Adding a signature is a parse error.
- A proof uses only real evidence. None of these may appear in anything a proof depends on:
  - `@unsafe`, or its sugar `def f?(...)`.
  - The holes `?TODO` and `?name`. You may use `?name` to inspect a goal, but remove it before the proof counts.
  - A law with no def. An open claim is not proved.
  - Foreign effect defs: `import "./x.c"` or `import "./x.js"`.
- `bend PROOF.bend` is the gate. Paste its real output into the log.
- `--verdict` (the recheck by the Lean-proven kernel) needs Lean 4.34.0. In the sandbox it cannot run: Lean is not installed and `~/.bend` is read-only, so an `ALL PROOFS CHECK` from there is the plain gate only. On the MacBook the flake supplies Lean: `nix develop --command bend bend/<dir>/PROOF.bend --verdict`. The first run builds the kernel into `~/.bend/bendtt`. Say in every report which gate ran. UC1 and UC2 passed `--verdict` on 2026-11-23 (log 4.27). Details: `docs/results/phase0-bend-guide.md`.

## Lessons from Phase 0

- **Termination.** The termination check reads arguments from left to right, so the shrinking argument goes first. Example: `run(events, s)`, not `run(s, events)`.
- **Aliases and names.** Import aliases are local to each file, so `PROOF.bend` imports the code module itself as well. Base already defines `Event`, so pick another name.
- **Reuse.** A variable used twice needs `+` in the law (`for +s: Nat`) and in the pattern (`case +e <> t:`).
- **Numbers.** F32 is opaque to proofs, so model with `Nat` or `U32`. `Nat` subtraction truncates at zero, so state laws in additive form.
- **Law strength.** A law that only bounds the state lets wrong step functions pass. Pin what each event does as well. See `docs/results/phase0-bend-smoke.md` §5.
- **Unreachable states.** Laws quantify over every state and every event list, including ones the system can never reach. That is the H3 difference from TLC. Record where it helps (a mutant killed) and where it blocks you (a cross-service invariant that needs a "was sent" hypothesis).
- **Running for the harness.** Compile once with `bend x.bend -o <bin>`, pipe events on stdin, and parse a single `key=value` line. Requirements: `docs/results/phase0-bend-io.md` §9.

Bend mutants live in `bend/ucN/mutants/`.

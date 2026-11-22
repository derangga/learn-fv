# Phase 0: Bend guide, version, proof conventions, escape hatches

All commands ran after `source .nix/env.sh`. Line numbers ("guide:N", "base:N", "effects:N") refer to
`docs/bend-guide.txt`, `docs/bend-base.txt`, `docs/bend-guide-effects.txt` as saved in this commit.

## 1. Captured files

| File | Source command | Size |
|---|---|---|
| `docs/bend-guide.txt` | `bend guide` | 678 lines. Regenerated; byte-identical to the file that was already there (`diff` empty). |
| `docs/bend-guide-effects.txt` | `bend guide effects` | 171 lines. Effects in Bend (C and JS side of custom effects). |
| `docs/bend-base.txt` | `bend base` | 3433 lines, 87,698 bytes. The whole Base library. |

`bend guide shaders` was not captured (GPU shader tutorial, not relevant; guide:671-674).

## 2. Version and install

```
$ bend version
bend 2.0.40
$ command -v bend
/nix/store/9xnqfsjii1ix743x7wfqfjxj3h2l3bdw-bend-2.0.40/bin/bend
$ readlink -f "$(command -v bend)"
/nix/store/9xnqfsjii1ix743x7wfqfjxj3h2l3bdw-bend-2.0.40/bin/bend
```

Installed through the Nix flake `github:bendlang/bend` (pinned in the repo's devShell, `.nix/env.sh`),
version 2.0.40, store path above. Locked input from `jq '.nodes.bend.locked' flake.lock`:

```
{
  "lastModified": 1795025138,
  "narHash": "sha256-gQdsY8fxOgZPiEUJ3qB4foFIeIlXt4GixDCxxj6+SIo=",
  "owner": "bendlang",
  "repo": "bend",
  "rev": "0e2f38f759cc830849e489307f3d256a7d148288",
  "type": "github"
}
```
 The guide's own install route is `curl -fsSL
https://bend-lang.com/install.sh | sh` (guide:23); we do not use it. `bend update` also does a
`curl | sh` (see `bend --help`); do not run it, it would leave the pin.

Side observation: a normal `bend` run tries to reach `bend-lang.com:443` (daily version check; the
sandbox log reported `deny network-outbound bend-lang.com:443`). The run still succeeded, and it
cached `{"ver":"2.0.40","notice":""}` in `$HOME/.bend/check.json`. It also wants to create
`$HOME/.bend/`, which is read-only in this sandbox (see section 5).

## 3. The LAWS.bend / PROOF.bend convention (guide:319-332)

Verbatim:

> By convention, a project keeps its laws in two files at its root. `LAWS.bend`
> imports the code and states the laws, each an open claim: the human writes it,
> the AI does not touch it. `PROOF.bend` imports `LAWS.bend` and proves each law
> with a def of the same name (`law sorted` is proven by `def Laws.sorted`): the
> AI writes it, along with the code. `bend PROOF.bend` is the gate: it prints
> SOME PROOFS FAIL while any law is open or false, and ALL PROOFS CHECK once every
> law holds.
> bend refuses a `PROOF.bend` that sits beside a `LAWS.bend` without importing it.

> `bend PROOF.bend --verdict` checks the proofs a second time, with a small kernel
> that has a proof in Lean: it prints ALL PROOFS CHECK only when every def outside
> Base is a valid proof, which bend2 and the kernel both accept, and which relies
> on no `@unsafe` or foreign code. `-o PROOF.bendtt` writes the translation the
> kernel reads; the translation has no proof, so read it to confirm a law.

What I observed (bend 2.0.40), using the guide's `add_zero` law (section 5 has the files):

| Command | Result |
|---|---|
| `bend PROOF.bend`, proof correct | `ALL PROOFS CHECK` then `Use --verdict for mathematical validity.` (rc 0) |
| `bend PROOF.bend`, law open / `?TODO` | `SOME PROOFS FAIL` then `Error: 1 TODO found.` and `The code is incomplete, and not a valid proof yet.` (rc 1) |
| `bend PROOF.bend`, wrong proof | `SOME PROOFS FAIL`, then `expected`/`observed` terms, `Context:`, source location (rc 1) |
| `bend PROOF.bend` without `import ./LAWS.bend` | `SOME PROOFS FAIL` / `Error: PROOF.bend must import ./LAWS.bend` (rc 1) |
| `bend PROOF.bend --verdict` | Adds a second check by the Lean-proven BendTT kernel. Unavailable here, see section 5. |

Notes on syntax I verified: a def that fills a law takes the law's name (`def Laws.add_zero(x):`) and
**no signature or return type** (`def Laws.absurd() -> {...}:` is a parse error: `expected ':'`).
The plain (non-`--verdict`) pass prints "Use --verdict for mathematical validity" itself, which
confirms the guide's two-tier design: `ALL PROOFS CHECK` from the bend2 checker alone is not the final word.

## 4. Escape hatches (ways a proof closes or a check weakens without real evidence)

"Detection" column, three values only: **PROOFS FAIL** = `bend PROOF.bend` prints `SOME PROOFS FAIL`; **verdict** = rejected
by `--verdict` per the guide (no hatch is listed with `verdict` alone, because the kernel cannot be built here); **not detected** = no mechanical signal. "Tested" means I ran it in
bend 2.0.40 in `$TMPDIR/hatch/` (outputs quoted); "guide only" means I only have the guide's claim.

| # | Hatch | Guide / base line | Detection |
|---|---|---|---|
| 1 | **`@unsafe` def** (skips termination check; may loop, so can "prove" anything) | guide:117-120: "A `def` marked `@unsafe` recurses freely ... but falls outside Bend's proof guarantees: `bend` runs it, but a check prints SOME PROOFS FAIL and names every def that relies on it." Also guide:587, 330-331 | PROOFS FAIL (verdict rejection is per the guide, untested). Tested: `@unsafe def Laws.absurd(): Laws.absurd()` for false law `{1n == 0n : Nat}` gives `SOME PROOFS FAIL` / `1 def relies on unsafe or foreign code:` / `defs that depend on @unsafe: LAWS.absurd`. |
| 2 | **`def f?` sugar** (same as `@unsafe`) | guide:588 "the same, as a sugar" | PROOFS FAIL (verdict rejection untested, as 1). Tested: `def Laws.absurd?():` gives the same `defs that depend on @unsafe` message. (Note: the `?` is only valid on the def name; `Laws.absurd?()` in a body is a parse error.) |
| 3 | **`?TODO` hole** | guide:340-341 "`?TODO` leaves it open"; guide:614 | PROOFS FAIL. Tested: `Error: 1 TODO found.` / `The code is incomplete, and not a valid proof yet.` |
| 4 | **`?name` hole** (prints the goal) | guide:340-341 "`?name` prints the goal", guide:614 | PROOFS FAIL, via an expected/observed mismatch (not the `1 TODO found` message of `?TODO`). Tested with true law `{Nat.add(0n, x) == x : Nat}` and body `?goal`: `SOME PROOFS FAIL` / `- expected : {x == x : Nat}` / `- observed : ?goal` / `Context:` `- x : Nat` / `Location: Laws.zero_add` (rc 1). Full output in 4.2. |
| 5 | **Law with no def = open claim** | guide:320-321 ("each an open claim"), 340-341 "a law with no def is an open claim" | PROOFS FAIL. Tested: gives the same `1 TODO found` message as `?TODO`. Same for a plain (non-PROOF) file: `bend a.bend` with an open law and a `main` prints `SOME PROOFS FAIL` and does not run `main` (rc 1). |
| 6 | **Foreign code**: a def whose body is `import "./x.c"` / `import "./x.js"` | guide:408-411 ("proofs, termination and the GPU never touch host code"), 589-591; effects:7-20 | PROOFS FAIL (verdict rejection per guide:330-331, untested). Applies to user foreign defs, even when no law uses them. Tested: `defs that depend on foreign effects: LAWS.Clock.now` + `Hint: no law or proof uses these defs. Move them to a file this proof does not import`. Foreign defs are `IO(R)`-typed, so they cannot directly inhabit an equality, but the proof gate still refuses any imported file containing them. **Base's own foreign effects are exempt** (see 12). Tested: a def calling `IO.print` still gives `ALL PROOFS CHECK`. |
| 7 | **Dead-mode code** (types, erased `-x` args, equations may loop or inhabit `Empty`) | guide:656-658 "Dead code may loop forever or inhabit `Empty`, but nothing dead ever counts as live evidence" | **not detected** (by design the live/dead wall and `bendtt.lean`, which the guide says proves no accepted def has type `Empty`, are what keep it sound; there is no user-visible signal). Guide only, could not demonstrate. My attempt to write a non-terminating `-n` type-level def was rejected (`expected : a call smaller than Loop(n)`), so I could not demonstrate dead-mode divergence. |
| 8 | **`Type : Type`, no positivity check** (guide's own words; makes the theory inconsistent without the live/dead wall) | guide:654-656 "one universe and no positivity check: `Type : Type` holds, and a datatype may recurse on the left of an arrow. What keeps this consistent is a wall between two checking modes." | **not detected** (not a user-level switch; safety rests on 7 and on `--verdict`'s kernel, guide:659-661). Guide only, could not demonstrate. |
| 9 | **Weakened or wrong law text** (vacuous claim, an extra `where`, the AI editing `LAWS.bend`) | guide:319-320 "the human writes it, the AI does not touch it"; guide:331-332 "the translation has no proof, so read it to confirm a law" | **not detected.** The convention is social: nothing stops `PROOF.bend` / the AI from changing `LAWS.bend`. Mitigation for us: keep `LAWS.bend` under review and diff it. Also `bend PROOF.bend` does not check that every law in `LAWS.bend` is *meaningful*, only that it holds. |
| 10 | **Proof beside LAWS not importing it** | guide:326 | PROOFS FAIL: `Error: PROOF.bend must import ./LAWS.bend`. Tested. |
| 11 | **`bend` default pass vs `--verdict`**: `ALL PROOFS CHECK` from the plain gate | guide:328-330 | **not detected** by the plain gate (it prints "Use --verdict for mathematical validity"; `--verdict` is the pass meant to cover the bend2 checker's own bugs). **Cannot run `--verdict` in this sandbox** (section 5), so every result here is the plain gate only. |
| 12 | **Everything in Base is trusted** ("every def outside Base") | guide:329-330; base list below | PROOFS FAIL for a user def calling a Base `@unsafe` def (tested: `Array.fork` gives `defs that depend on @unsafe: LAWS.dup`); **not detected** for a user def calling Base's foreign `IO.print` (tested: `ALL PROOFS CHECK`) or for Base's open laws and foreign effects themselves. `--verdict` explicitly excludes Base (guide:329-330). |
| 13 | **Equality of values is opaque for host-primitive ops** | guide:635 "Equality of values is a call, `T.is_eq(a, b)`; `==` is only the type" | PROOFS FAIL on any attempted proof (not a hole). Tested: `F32.add(1.0, 2.0) == 3.0` by `{==}` is rejected (`expected : F32.add(1.0, 2.0)`, `observed : 3.0`), so F32 arithmetic cannot be reasoned about (and cannot be "proved" wrongly). Relevant when choosing a model type: use `Nat`/`U32`, not `F32`. |

**Verdict rejection of hatches 1, 2 and 6 is untested**: the BendTT kernel cannot be built in this sandbox
(section 5). The guide (guide:330-331) says `--verdict` rejects them; I only observed the plain gate rejecting them.

### 4.1 Search of docs/bend-base.txt

Command: `grep -n -i -E 'unsafe|axiom|trust|admit|sorry|believe|postulate|TODO|assume|cheat|hack|fake|FIXME|WONTFIX|skip|unchecked' docs/bend-base.txt`

Hits (all):

- `@unsafe` at base:2667 (`Array.fork`) and base:2671 (`Array.join`): `Array.fork` duplicates an
  affine array (`(a, a)`); `Array.join` drops one copy. Comment at base:2661-2664: "Both read and write the
  same cells, so racing writes go through the atomics".
- `@unsafe` at base:2769 (`Array.get_unchecked`), comment at base:2768: "skips the wrap mask. @unsafe, like Array.fork; only reads."
- No hit for `axiom`, `trust`, `admit`, `sorry`, `believe`, `postulate`, `TODO`, `FIXME`, `WONTFIX`, `assume`,
  `cheat`, `fake`, `skip`. (`bend2/` source may have more; this is `bend base` output only.)

Axiom-like items that the grep does not find by name (found by cross-checking every `law` against a `def` of
the same name; 53 of 76 laws have no def). Reproduce with (run from the repo root; outputs in comments):

```bash
B=docs/bend-base.txt
grep -c '^law ' $B                                   # 76 laws
grep -c '^@unsafe' $B                                # 3 @unsafe defs
grep -E '^law ' $B | sed 's/^law \(.*\):$/\1/' | sort > laws.txt
grep -E '^(@unsafe )?def ' $B | sed -E 's/^(@unsafe )?def ([^(]*)\(.*/\2/' | sort -u > defs.txt
comm -23 laws.txt defs.txt | wc -l                   # 53 laws without a def
comm -23 laws.txt defs.txt | grep -c -E '^(F32\.|U32\.to_f32$)'          # 38 F32-related
comm -23 laws.txt defs.txt | grep -c -E '^(File|Socket|Listener|Window|Audio|Chan)$'  # 6 handles
comm -23 laws.txt defs.txt | grep -c '^Array\.atomic\.'                 # 9 atomics
awk '/^def /{d=$0} /import "\.\/effs\/.*\.c"/{print d}' $B | wc -l      # 61 foreign effect defs
grep -c 'import "\./effs/.*\.js"' $B                                   # 61 (the .js twins)
```
(38 + 6 + 9 = 53.)

- 6 opaque handles, **open `law` with no def**: `File`, `Socket`, `Listener`, `Window`, `Audio` (base:137-149)
  and `Chan` (base:153). Comment base:135-136: "A handle is opaque, a law with no constructor and no field,
  so no program forges one, and linear (Type), so none copies or reuses one." These are intentional axioms
  (postulated types).
- 38 F32-related open laws (the `F32.*` laws, which include `F32.to_u32` and `F32.from_nat`, plus `U32.to_f32`), from base:1756 to
  base:1993, for example `law F32.add` at base:1764. Postulated operations: `F32.add` does not compute, so no
  equation about floats can be proved by `{==}` (tested, hatch 13). base:1992 comment: "The full Nat conversion
  is intrinsic on every backend".
- 9 `Array.atomic.*` open laws (`add min max and or xor exch cas fadd`), base:2675-2724.
- **61 foreign effect defs** (122 `import "./effs/...c|js"` lines, first at base:203, e.g. `IO.print`
  base:202-204, `Process.run` base:238-239, `IO.sleep` base:265-267, `IO.now` base:269-271, `IO.spawn` base:261-263, TCP/UDP/File/Window/Audio
  effects). The guide says (guide:408-411) "Every effect in Base is a def whose body is `import "./x.js"` plus a
  `.c` twin". All outside the proof system.
- `Empty.absurd` (base:619-622) is the normal ex-falso; fine.
- `type Empty is Data:` (base:7) has no constructors, as expected.

None of these is a way for a user proof to close a law. They are the trusted base. Count of `law` forms in Base: 76;
53 have no def (open), the rest are proved (e.g. `Equal.cong`, `Equal.sym`, base:582-605).

### 4.2 `?goal` hole, full output

`$TMPDIR/hatch/tQ/`: `LAWS.bend` has true law `zero_add` (`{Nat.add(0n, x) == x : Nat}`), `PROOF.bend` is
`def Laws.zero_add(x):` with body `?goal`.
```
$ bend PROOF.bend
SOME PROOFS FAIL
Error:
- expected : {x == x : Nat}
- observed : ?goal
Context:
- x : Nat
Location: Laws.zero_add
4 | def Laws.zero_add(x):
5>|   ?goal
  |   ^^^^^
6 |
(rc 1)
```

## 5. `bend PROOF.bend --verdict` in this sandbox

Files (`$TMPDIR/verdict-trial/`), copied from the guide's `add_zero` law (guide:286-300):

`LAWS.bend`
```python
import Base

# LAW: "for every x, x plus 0 equals x"
law add_zero:
  for x: Nat
  {Nat.add(x, 0n) == x : Nat}
```

`PROOF.bend`
```python
import Base
import ./LAWS.bend as Laws

def Laws.add_zero(x):
  match x:
    case 0n:
      {==}
    case 1n+p:
      %Laws.add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}
```

Plain gate:
```
$ bend PROOF.bend
ALL PROOFS CHECK
Use --verdict for mathematical validity.
(rc 0)
```

Verdict, re-run on 2026-11-22 ~01:55 UTC, as-is (default `HOME=/home/claude`, read-only in the sandbox):
```
$ bend PROOF.bend --verdict
Error: EROFS: read-only file system, mkdir '/home/claude/.bend'
(rc 1)
```
That is a sandbox filesystem write block, not a download failure: `bend` keeps its kernel build cache under
`~/.bend/bendtt/`.

Verdict, same re-run, `HOME=$TMPDIR/fakehome2` (a fresh writable scratch HOME; I only moved the cache
directory, the network was not touched or bypassed):
```
$ HOME=$TMPDIR/fakehome2 bend PROOF.bend --verdict
Error: BendTT infrastructure: the kernel did not build (lean: Executable not found in $PATH: "lean"); --verdict needs Lean v4.34.0 (elan toolchain leanprover/lean4:v4.34.0), or $BENDTT set to a built kernel
(rc 1; ~0.6 s)
```
Sandbox log: the batch of commands that contained both re-runs ended with
`<sandbox_violations> deny network-outbound bend-lang.com:443 (the organization's managed allowlist does not include this host, and only managed settings can add it) </sandbox_violations>`.
The log is per tool call, not per command, so I cannot attribute it to one of the two runs; both printed the
errors above. A reviewer who sees the network error instead of the `lean` error is hitting the same
`bend-lang.com:443` block (bend's version check, the only host the sandbox log names); which message surfaces
may depend on the cache state of the HOME used. Either way `--verdict` fails.

**Untested because the kernel cannot be built here:** that `--verdict` rejects hatches 1 (`@unsafe`), 2 (`def f?`)
and 6 (foreign code), and that it accepts a correct proof. Those are the guide's claims (guide:328-332), not
observations.

Conclusion: **`--verdict` does not work in this sandbox.** There is no `lean`, `lake` or `clang` on PATH, `elan` is
absent, and the Nix devShell does not include Lean. The error itself names two ways out: install the elan
toolchain `leanprover/lean4:v4.34.0`, or set `$BENDTT` to a prebuilt kernel. I did not attempt either (the
brief says not to work around network blocks; github.com is reachable but the elan install path was out of
scope). **For Phase 1+ the plain `bend PROOF.bend` gate is the only mechanical check available here.** To
get `--verdict` later, either add Lean v4.34.0 (and whatever else `bend2/bendtt.lean` needs) to the
flake, or build the kernel on an unsandboxed machine and set `BENDTT`.

## 6. AGENTS.md integration

- `docs/bend-guide.txt`, `docs/bend-guide-effects.txt`: no mention of AGENTS (`grep -n -i AGENTS` empty).
- `bend --help`: no mention (`bend --help | grep -i agents` empty). The help ends "Read the guide (`bend guide`) before writing Bend code."
- Upstream `bendlang/bend` `AGENTS.md` (fetched from `api.github.com/repos/bendlang/bend/contents/AGENTS.md`
  with `Accept: application/vnd.github.raw`; 51 lines) is a contributor map of the Bend repository: file
  layout (`bend2/bend.ts` = "the language ... human-written: do not edit it", `comp.ts`, `safe.ts`,
  `bendtt.lean`, `base.bend`, `gates/*`, `bench/*`), plus how tests are written (each test ends in `#|` lines)
  and that `gates/repo.ts` token caps are changed only by the maintainer. It contains nothing addressed to Bend
  users and no prescribed user-project AGENTS.md. Two facts are mildly useful for us, neither normative:
  `bend2/safe.ts` does `--verdict` and `-o <out>.bendtt`, and `--verdict` "builds its CLI once, with Lean
  v4.34.0". That matches the guide and the error in section 5.
- The guide's AI workflow (guide:306-317, 319-324) is the only user-facing agent guidance: the human owns
  `LAWS.bend`, the AI writes `PROOF.bend` and the code, `bend PROOF.bend` is the gate.

## 7. Takeaways for the experiment

1. The plain gate flags 1, 2, 3, 4, 5, 6 and 10 above (all print `SOME PROOFS FAIL`; 3 and 5 as `1 TODO found`, 4 as an expected/observed mismatch). Verdict-level rejection is untested. Gaps: 9 (the law text itself) is not detected, and 12
   (Base is trusted) is by design.
2. Treat `ALL PROOFS CHECK` from the plain gate as provisional until `--verdict` runs; it cannot run here.
3. In Base, F32 and the handle/channel/atomic laws are axioms; model with `Nat`/`U32` and avoid F32 so proofs
   remain checkable.
4. A law-filling def has the law's name and **no signature**; the checker reports the goal and mismatch.
5. Failed proofs of a plain `.bend` file with an open law stop `main` from running (rc 1), so
   proof state and execution are coupled in the default `bend file.bend` command.

## 8. Log entry (handover section 8 fields)

- Date/time: 2026-11-22, ~01:55 UTC.
- Tool: Bend 2 (2.0.40).
- Use case: Phase 0 (toolchain, guide and Base capture, proof-convention and escape-hatch survey).
- What was done: regenerated `bend guide`; saved `bend guide effects` and `bend base`; recorded version and flake
  lock; read the guide and searched Base for axiom-like items; ran the `--verdict` trial; tested escape hatches
  (`@unsafe`, `def f?`, `?TODO`, `?goal`, open law, foreign import, PROOF without LAWS import); fetched the upstream AGENTS.md.
- Authoring time (honest estimate): about 1 hour including research, for the add_zero trial itself about 5 minutes
  (copied from the guide).
- AI iterations (estimate): 2 for the add_zero trial (first law-filling def attempts had a signature, a parse
  error; then correct). About 8 small experiments for the hatches.
- Machine time, one `bend PROOF.bend` run on the add_zero trial, `hyperfine --warmup 2 --runs 10 -N 'bend PROOF.bend'`:
  mean 385.4 ms +/- 15.7 ms (user 627.5 ms, system 54.3 ms; range 361.7 to 406.7 ms; 10 runs). The warmup runs
  are the warm case; no separate cold run was measured.
- Result: add_zero proof checks with the plain gate (`ALL PROOFS CHECK`); `--verdict` could not run (no Lean).
- Size: LAWS.bend 6 lines, PROOF.bend 10 lines.
- Friction: `~/.bend` is read-only in the sandbox (`EROFS`); no `lean`/`lake`/`clang` so no BendTT kernel and no
  `--verdict`; `bend-lang.com:443` is blocked (version check); a law-filling def takes no signature (`def Laws.x() -> T:`
  is a parse error); `def f?` and calls to `f?` differ (the `?` is valid only on the def name).

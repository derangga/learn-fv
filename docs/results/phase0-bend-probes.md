# Phase 0: Bend soundness probes

All commands ran after `source .nix/env.sh` (bend 2.0.40), from the repo root. Plain gate only: `--verdict` cannot
run here (see `docs/results/phase0-bend-guide.md` section 5), so a rejection below is the bend2 checker refusing,
and nothing here tests the Lean kernel.

## Headline

**No false statement was accepted.** 14 probe dirs (the 9 requested kinds, with the multi-route ones split), each states a false law and
each `bend PROOF.bend` printed `SOME PROOFS FAIL`. `bash bend/probes/run.sh` exits 0.

Files: `bend/probes/<name>/LAWS.bend` (false law) and `PROOF.bend` (attempt), plus `bend/probes/run.sh`.
Twelve probes are rejected on the merits (equality, affine, kind, termination, or the dead/live wall). Two
(`unsafe_false`, `open_false`) are rejections by the escape-hatch detector, kept as regressions. See
"Weak probes" for what each rejection does and does not show.

## Probes

Verdict = what the gate printed. Class: **M** = rejected on the merits (the checker refused the false claim or the
trick the attempt needs), **H** = rejected by the escape-hatch detector (known, by design).

| Probe | False claim | Technique | Gate verdict | Class | Key output line |
|---|---|---|---|---|---|
| `false_eq` | `{1n == 0n : Nat}` | `{==}` | SOME PROOFS FAIL | M | `expected : 1n` / `observed : 0n` |
| `succ_eq` | `for n: Nat, {1n+n == n : Nat}` | induction on `n`, `{==}` and a rewrite by the IH | SOME PROOFS FAIL | M | `expected : 1n` / `observed : 0n` (base case) |
| `bad_rec` | same as `succ_eq` | "induction" whose recursive call passes the same `n` | SOME PROOFS FAIL | M | `expected : a call smaller than Laws.bad_rec(0n) (arguments are read left to right...)` |
| `empty_loop` | `{1n == 0n : Nat}` | def calling itself, no decreasing argument | SOME PROOFS FAIL | M | `expected : a call smaller than Laws.empty_loop` |
| `negative_type` | `{1n == 0n : Nat}` | `type Bad is Type: MkBad{f: Bad -> Empty}`, `omega(b) = app(b, b)` (Russell/Curry) | SOME PROOFS FAIL | M | `b (consumed more than once)` at `omega` |
| `negative_type_fix` | `{1n == 0n : Nat}` | same `Bad`, but self-application through a fresh `mk()` per use so nothing is copied; needs `mk` to call itself | SOME PROOFS FAIL | M | `expected : a call smaller than mk` |
| `negative_type_data` | `{1n == 0n : Nat}` | declare `Bad is Data` so it can be copied | SOME PROOFS FAIL | M | `expected : Data` / `observed : Type` at the `f: Bad -> Empty` field |
| `type_in_type` | `{1n == 0n : Nat}` | Russell over `V : Type` with `Sup{A: Type, f: A -> V}` (uses `Type : Type`); membership proof rebuilt from its pieces | SOME PROOFS FAIL | M | `eq (consumed more than once)` at `lem1` |
| `type_in_type_fix` | `{1n == 0n : Nat}` | same `V`; `lem1` fed to itself through the top-level def | SOME PROOFS FAIL | M | `expected : a call smaller than lem1(((v, nh), eq))` |
| `dead_mode_leak` | `{1n == 0n : Nat}` | erased `-e: Empty` (built by the paradox term in dead mode) returned as a live `Empty` | SOME PROOFS FAIL | M | `expected : -e` / `observed : e` at `leak` |
| `dead_mode_leak_match` | `{1n == 0n : Nat}` | live `match e:` (no cases) on an erased `Empty` to get the false equation | SOME PROOFS FAIL | M | `a live scrutinee (a - scrutinee matches only in a dead region)` |
| `wrong_witness` | `exs y: Nat, {1n+y == 0n : Nat}` | witness `0n`, proof `{==}` | SOME PROOFS FAIL | M | `expected : 1n` / `observed : 0n` at `{==}` |
| `unsafe_false` | `{1n == 0n : Nat}` | `@unsafe def` that loops | SOME PROOFS FAIL | H | `defs that depend on @unsafe: LAWS.unsafe_false` |
| `open_false` | `{1n == 0n : Nat}` | law with no def | SOME PROOFS FAIL | H | `1 TODO found.` |

## Output of `bash bend/probes/run.sh`

Run 2026-11-22T02:09Z (after the EXPECT change). Each probe dir has an `EXPECT` file: substrings (one per line,
26 lines over 14 dirs) of the first error that show the attack itself was refused, such as `observed : 0n`,
`consumed more than once`, `a call smaller than`, `observed : Type`, `a live scrutinee`, `depend on @unsafe`,
`TODO found`, each paired with the `Location:` def. `run.sh` prints PASS only when `SOME PROOFS FAIL` and every
EXPECT line appear in the output. Anything else is FAIL: `ALL PROOFS CHECK` (accepted), no `SOME PROOFS FAIL`,
a missing EXPECT file, or `FAIL wrong reason` (the gate rejected, but not for the expected reason; the first error
lines are printed). So a parse error or a missing import is no longer a PASS. Exit status is nonzero on any FAIL.

```
$ source .nix/env.sh && bash bend/probes/run.sh
bad_rec                PASS rejected as expected
dead_mode_leak         PASS rejected as expected
dead_mode_leak_match   PASS rejected as expected
empty_loop             PASS rejected as expected
false_eq               PASS rejected as expected
negative_type          PASS rejected as expected
negative_type_data     PASS rejected as expected
negative_type_fix      PASS rejected as expected
open_false             PASS rejected as expected
succ_eq                PASS rejected as expected
type_in_type           PASS rejected as expected
type_in_type_fix       PASS rejected as expected
unsafe_false           PASS rejected as expected
wrong_witness          PASS rejected as expected
$ echo $?
0
```

Negative control: a copy in `$TMPDIR` with `false_eq/PROOF.bend` broken to `def Laws.false_eq( :` and
`succ_eq/PROOF.bend` given `import ./nope.bend as N`. Both still print `SOME PROOFS FAIL`, and `run.sh` reports them as FAIL:

```
false_eq               FAIL wrong reason (missing 'observed : 0n'): Error: - expected : a name
succ_eq                FAIL wrong reason (missing 'observed : 0n'): Error: - message  : no such file: .../succ_eq/nope.bend
(run.sh exit status 1)
```

## What the probes show

- **Positivity check is absent, as the guide says.** `type Bad is Type: MkBad{f: Bad -> Empty}` is accepted
  (`negative_type_fix` passes `Bad` and `app` and fails later, at `mk`). Also `type Bad is Kind(&0)` with the same
  field is accepted (scratch test, not kept: it has no live values).
- **Soundness here rests on affinity, kinds and termination, as the guide claims.** The Russell self-application
  needs a copy of a function-holding value (affine check refuses: `negative_type`, `type_in_type`), a `Data` kind for
  it (refused: `negative_type_data`), or a recursion to build the second copy (termination check refuses:
  `negative_type_fix`, `type_in_type_fix`). Top-level defs are the only freely callable things, and they cannot
  recurse without a smaller argument.
- **`Type : Type` is accepted.** `V : Type` with a field `A: Type`, and `In` (membership by a dependent pair over `A`),
  type-check (`type_in_type` passes up to `cast`, which uses a rewrite, and only then fails at `lem1`). Two things show
  the argument was typed correctly and that the rejection is the wall, not a typo: `cast` (the equality transport
  `In(Rus, Rus) -> In(v, v)`) is accepted, and `lem1` fails only on the use count / recursion.
- **Dead mode really does accept the paradox term.** In an erased argument the Russell term is accepted. Scratch test:

```
import Base
type Bad is Type:
  MkBad{f: Bad -> Empty}
def app(b: Bad, x: Bad) -> Empty:
  match b:
    case MkBad{f}:
      f(x)
def sink(-e: Empty) -> U32:
  0
def main() -> U32:
  sink(app(MkBad{x => app(x, x)}, MkBad{x => app(x, x)}))
$ bend u.bend
0
```

  (`x` is copied there, and the term has type `Empty`; it was not evaluated, `main` only passes it erased.) So an
  `Empty`-typed dead term can be written, matching the guide ("dead code may inhabit `Empty`"). The two
  `dead_mode_leak*` probes then try to turn it into live evidence and are refused by the wall: an erased variable cannot be returned live,
  and an erased value cannot be a live scrutinee. I found no other dead to live path (erased vars in live positions
  are always rejected, e.g. `def conv(-n: Nat) -> Nat: n` gives `expected : -n` / `observed : n`; a type-level def that
  loops is rejected by the same termination check, `expected : a call smaller than L`).
- Controls for syntax (`$TMPDIR` copies). True variants of `false_eq` (`{1n == 1n : Nat}`) and `wrong_witness`
  (`1n+y == 1n`, witness `0n`) print `ALL PROOFS CHECK`. Stronger one for `succ_eq`: the probe's own induction
  `PROOF.bend` (byte-identical, `diff` empty) against the true law `{1n+n == 1n+n : Nat}` also prints `ALL PROOFS CHECK`,
  so the induction body is well-formed and only the false law makes it fail:

```
$ diff bend/probes/succ_eq/LAWS.bend $TMPDIR/sctl/LAWS.bend
6c6
<   {1n+n == n : Nat}
---
>   {1n+n == 1n+n : Nat}
$ diff bend/probes/succ_eq/PROOF.bend $TMPDIR/sctl/PROOF.bend && echo identical
identical
$ bend $TMPDIR/sctl/PROOF.bend
ALL PROOFS CHECK
Use --verdict for mathematical validity.
rc=0
```

  The other 11 probes (everything except `false_eq`, `succ_eq`, `wrong_witness`) have no true control. For them, that
  the attempt is well-formed up to the rejection point is argued from the earlier defs being accepted
  (for instance `Bad`, `app`, `V`, `In`, `NotSelf`, `Rus`, `cast` all pass before the failing def), not shown by a
  passing variant. The EXPECT check now pins the error to the intended def and message, which rules out a parse error
  as the reason.

## Weak probes and limits (honest notes)

Each probe's EXPECT file pins the rejection to the intended error, so a parse or name error is reported FAIL (I fixed such errors during authoring: e.g. defs must come before use, `Rus.proj` before `Rus`). Remaining limits:

- **The checker reports the first error only.** Rejection shows the first failing def, not that every part is wrong.
  `succ_eq` stops at the base case `1n == 0n`; the step case is never examined. `type_in_type` names `eq` as consumed
  twice; `nh` and `v` are also used twice, but the report names one. `dead_mode_leak*` stop at `leak`, so the call site
  with the dead paradox term in them is never reached (the same term is shown accepted in dead position above).
- **`type_in_type*` are Russell-style, not a full Girard/Hurkens paradox.** The full paradox needs far more
  encoding (impredicative-style higher-order terms with heavy copying); I stopped at the Russell tree version. The
  rejection is the affine and termination checks, which is the guide's claim, and a full paradox would need the same
  copying. This probe does not exclude a clever construction.
- **`unsafe_false` and `open_false` are detector regressions (H), not checker-soundness tests.** They show the gate
  names `@unsafe` and open laws, not that the type theory refuses anything.
- **Plain gate only.** `--verdict` (the Lean kernel) cannot run here, so none of these runs test it. The guide says
  the kernel proves no accepted def has type `Empty`; that is not checked here.
- **Not shown:** that no false statement is accepted by any means. The probes show the specific known attacks
  are refused; they are not a proof of soundness.

## Per-probe raw output

Each block is `bend bend/probes/<name>/PROOF.bend` from the repo root and its exit code.

### bad_rec

```
$ bend bend/probes/bad_rec/PROOF.bend
SOME PROOFS FAIL
Error:
- expected : a call smaller than Laws.bad_rec(0n) (arguments are read left to right: each passed unchanged until one shrinks)
- observed : Laws.bad_rec(0n)
Location: Laws.bad_rec
 8 |     case 0n:
 9>|       Laws.bad_rec(0n)
   |       ^^^^^^^^^^^^
10 |     case 1n+p:
rc=1
```

### dead_mode_leak

```
$ bend bend/probes/dead_mode_leak/PROOF.bend
SOME PROOFS FAIL
Error:
- expected : -e
- observed : e
Location: leak
13 | # copied there). Attempt: return an erased Empty as live Empty, then use it.
14>| def leak(-e: Empty) -> Empty:
   |           ^
15 |   e
rc=1
```

### dead_mode_leak_match

```
$ bend bend/probes/dead_mode_leak_match/PROOF.bend
SOME PROOFS FAIL
Error:
- message  : a live scrutinee (a - scrutinee matches only in a dead region)
Location: leak
14 | def leak(-e: Empty) -> {1n == 0n : Nat}:
15>|   match e:
   |   ^^^^^^^^
16 | 
rc=1
```

### empty_loop

```
$ bend bend/probes/empty_loop/PROOF.bend
SOME PROOFS FAIL
Error:
- expected : a call smaller than Laws.empty_loop (arguments are read left to right: each passed unchanged until one shrinks)
- observed : Laws.empty_loop
Location: Laws.empty_loop
6 | def Laws.empty_loop():
7>|   Laws.empty_loop()
  |   ^^^^^^^^^^^^^^^
8 | 
rc=1
```

### false_eq

```
$ bend bend/probes/false_eq/PROOF.bend
SOME PROOFS FAIL
Error:
- expected : 1n
- observed : 0n
Location: Laws.false_eq
5 | def Laws.false_eq():
6>|   {==}
  |   ^^^^
7 | 
Note: the left side of the equality is the expected, the right side is the observed.
rc=1
```

### negative_type

```
$ bend bend/probes/negative_type/PROOF.bend
SOME PROOFS FAIL
Error:
- expected : b
- observed : b (consumed more than once)
Location: omega
13 | # omega = app(b, b) needs b twice.
14>| def omega(b: Bad) -> Empty:
   |           ^
15 |   app(b, b)
rc=1
```

### negative_type_data

```
$ bend bend/probes/negative_type_data/PROOF.bend
SOME PROOFS FAIL
Error:
- expected : Data
- observed : Type
Location: MkBad
6 | type Bad is Data:
7>|   MkBad{f: Bad -> Empty}
  |            ^^^^^^^^^^^^
8 | 
rc=1
```

### negative_type_fix

```
$ bend bend/probes/negative_type_fix/PROOF.bend
SOME PROOFS FAIL
Error:
- expected : a call smaller than mk (arguments are read left to right: each passed unchanged until one shrinks)
- observed : mk
Context:
- x : Bad
Location: mk
17 | def mk() -> Bad:
18>|   MkBad{x => app(x, mk())}
   |                     ^^
19 | 
rc=1
```

### open_false

```
$ bend bend/probes/open_false/PROOF.bend
SOME PROOFS FAIL
Error: 1 TODO found.
The code is incomplete, and not a valid proof yet.
rc=1
```

### succ_eq

```
$ bend bend/probes/succ_eq/PROOF.bend
SOME PROOFS FAIL
Error:
- expected : 1n
- observed : 0n
Location: Laws.succ_eq
7 |     case 0n:
8>|       {==}
  |       ^^^^
9 |     case 1n+p:
Note: the left side of the equality is the expected, the right side is the observed.
rc=1
```

### type_in_type

```
$ bend bend/probes/type_in_type/PROOF.bend
SOME PROOFS FAIL
Error:
- expected : eq
- observed : eq (consumed more than once)
Context:
- v  : V
- nh : @_:In(v, v) -> Empty
Location: lem1
32 | def lem1(i: In(Rus(), Rus())) -> Empty:
33>|   (x, eq) = i
   |       ^^
34 |   (v, nh) = x
rc=1
```

### type_in_type_fix

```
$ bend bend/probes/type_in_type_fix/PROOF.bend
SOME PROOFS FAIL
Error:
- expected : a call smaller than lem1(((v, nh), eq)) (arguments are read left to right: each passed unchanged until one shrinks)
- observed : lem1
Context:
- v  : V
- nh : @_:In(v, v) -> Empty
- eq : {Sup{Sigma<&1, &1, V, v => @_:In(v, v) -> Empty>, p => Rus.proj(p)} == v : V}
Location: lem1
34 |   (v, nh) = x
35>|   nh(cast(v, eq, ((Rus(), lem1), {==})))
   |                           ^^^^
36 | 
rc=1
```

### unsafe_false

```
$ bend bend/probes/unsafe_false/PROOF.bend
SOME PROOFS FAIL
Error: 1 def relies on unsafe or foreign code:
defs that depend on @unsafe: LAWS.unsafe_false
rc=1
```

### wrong_witness

```
$ bend bend/probes/wrong_witness/PROOF.bend
SOME PROOFS FAIL
Error:
- expected : 1n
- observed : 0n
Location: Laws.wrong_witness
5 | def Laws.wrong_witness():
6>|   (0n, {==})
  |        ^^^^
7 | 
Note: the left side of the equality is the expected, the right side is the observed.
rc=1
```

## Log entry (handover section 8 fields)

- Date/time: 2026-11-22, ~02:11 UTC (final run).
- Tool: Bend 2 (2.0.40), plain gate.
- Use case: Phase 0 soundness probes (step 4).
- What was done: 14 probe dirs (false law, genuine proof attempt), `run.sh` to run them all and classify
  PASS (rejected) / FAIL (accepted); scratch controls for syntax and for dead-mode acceptance.
- Authoring time (honest estimate): about 45 minutes of wall time, including reading the guide, plus about 10
  minutes for the EXPECT rework. Iterations: about 25 `bend` runs while writing; the Russell attempt
  (`type_in_type`) took about 10 of them and about 15 minutes of wall time, inside the 30-minute cap for the
  Girard/Hurkens-style attempt (the cap was not reached; I stopped at the Russell version for the reasons in
  "Weak probes", not because of time). Its snags: defs-before-use, a stuck `In(v, v)` solved by `cast`, an
  `(x, +eq)` pattern that errors with `cannot infer`.
- Machine time: two sessions of `hyperfine --warmup 1 --runs 5 'bash bend/probes/run.sh'`. Before the EXPECT change:
  mean 7.973 s +/- 2.379 s (noisy, other agents running). Final, after the EXPECT change:
  mean 5.550 s ±  0.290 s, range 5.318 s …  6.004 s    5 runs.
  Per probe that is 5.550 s / 14 = about 0.40 s (final), and 7.973 s / 14 = about 0.57 s (noisy session). The
  minimum of the noisy session, 5.546 s / 14 = 0.40 s, matches the final one; the larger mean is load.

```
$ hyperfine --warmup 1 --runs 5 'bash bend/probes/run.sh'      # final
Benchmark 1: bash bend/probes/run.sh
  Time (mean ± σ):      5.550 s ±  0.290 s    [User: 8.607 s, System: 0.932 s]
  Range (min … max):    5.318 s …  6.004 s    5 runs
$ hyperfine --warmup 1 --runs 5 'bash bend/probes/run.sh'      # earlier, noisy
Benchmark 1: bash bend/probes/run.sh
  Time (mean ± σ):      7.973 s ±  2.379 s    [User: 9.301 s, System: 0.993 s]
  Range (min … max):    5.546 s … 11.504 s    5 runs
```

- Result: all 14 false laws rejected; `run.sh` exits 0. **No false statement accepted.**
- Size: `bend/probes/**/*.bend` 306 lines (14 `LAWS.bend` + 14 `PROOF.bend`), `run.sh` 22 lines, 14 `EXPECT` files 26 lines (`wc -l`).
- Friction: no proof-assistant tactics so every attempt is hand-written term syntax; `Rus` before `Rus.proj` is an error
  ("defs are checked in file order"); `(x, +eq) = i` gives `an annotated term (cannot infer)`; `In(v, v)` for a free
  `v` is stuck, so the equality needs a rewrite (`cast`) first; the checker prints one error at a time.

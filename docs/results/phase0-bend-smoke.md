# Phase 0: Bend smoke test (trivial law and proof)

All commands ran after `source .nix/env.sh` (bend 2.0.40), from the repo root. Files: `bend/smoke/code.bend`,
`bend/smoke/LAWS.bend`, `bend/smoke/PROOF.bend`. Plain gate only; `--verdict` cannot run here (see
`docs/results/phase0-bend-guide.md` section 5), so `ALL PROOFS CHECK` below is provisional.

## 1. Code and laws in brief

`code.bend`: a saturating counter. State is a `Nat`; events are `Ev = Inc | Reset` (not `Event`: Base already
declares `Event`, see friction). `step(s, e)`: `Inc` gives `Nat.min(1n+s, 3n)` (saturates at cap 3), `Reset` gives
`0n`. `run(events, s)` folds `step` over the list, head first.

`LAWS.bend` (imports `./code.bend as Code`):

| Law | Statement | Role |
|---|---|---|
| `reset_zero` | for all `s`, `step(s, Reset) == 0` | the trivial law |
| `step_preserves` | for all `s`, `e`, if `is_le(s, 3)` then `is_le(step(s, e), 3)` | per-event invariant preservation |
| `run_preserves` | for all `events`, `s`, if `is_le(s, 3)` then `is_le(run(events, s), 3)` | invariant over any event list |

`PROOF.bend` (imports `./code.bend as Code` and `./LAWS.bend as Laws`) has `def Laws.reset_zero`,
`def Laws.step_preserves`, `def Laws.run_preserves`, no signatures. `reset_zero` is `{==}` (both sides compute).
`step_preserves` is one `match s e:` with 5 cases (s = 0, 1, 2, 3+r for `Inc`; any `s` for `Reset`), each `{==}`.
`run_preserves` is induction on the list: `Nil` returns the hypothesis `h`; `e <> t` calls itself on `t` with the new
state `step(s, e)` and the proof from `step_preserves`.

Honest note on strength: for `Inc` the `min` already bounds the result by 3 for any `s`, so the hypothesis `h`
of `step_preserves` is not used by that law's proof. `h` is needed only at the `Nil` case of `run_preserves`
(`run([], s) = s`). The induction over the list is real; the saturating step is a weak invariant case.

Escape-hatch scan (empty means none found, grep exit 1):

```
$ grep -n -E '@unsafe|\?|import "' bend/smoke/*.bend
(no output)
```

## 2. Passing run

From the repo root and from the directory both work (imports resolve relative to the file).

```
$ bend bend/smoke/PROOF.bend
ALL PROOFS CHECK
Use --verdict for mathematical validity.
$ cd bend/smoke && bend PROOF.bend
ALL PROOFS CHECK
Use --verdict for mathematical validity.
```
Both rc 0.

## 3. Timing

First run on a fresh copy of the dir (`cp -r bend/smoke $TMPDIR/smoke_cold`). Not a cold-start measurement: the
binary is already in the OS page cache. I looked for a proof cache: `~/.bend` does not exist (it cannot be
created in this sandbox, see phase0-bend-guide.md), and after a run `find $HOME $TMPDIR <repo> -newer <marker>`
showed no file written by `bend` (the only newer files belonged to other processes). So no on-disk cache was
observed; an in-memory or other cache is not ruled out.

```
$ time bend $TMPDIR/smoke_cold/PROOF.bend
ALL PROOFS CHECK
Use --verdict for mathematical validity.

real	0m0.397s
user	0m0.643s
sys	0m0.054s
```

`hyperfine --warmup 2 --runs 10 -N 'bend bend/smoke/PROOF.bend'`, two sessions. Other agents were running on the
machine at the same time, so both are noisy; the first has an outlier warning.

```
Benchmark 1: bend bend/smoke/PROOF.bend
  Time (mean ± σ):     510.2 ms ± 217.6 ms    [User: 627.7 ms, System: 62.8 ms]
  Range (min … max):   357.7 ms … 994.0 ms    10 runs
  Warning: Statistical outliers were detected.

Benchmark 1: bend bend/smoke/PROOF.bend
  Time (mean ± σ):     781.4 ms ±  87.7 ms    [User: 745.2 ms, System: 71.4 ms]
  Range (min … max):   646.3 ms … 885.8 ms    10 runs
```

A second single run of the real files, same day:

```
$ time bend bend/smoke/PROOF.bend
ALL PROOFS CHECK
Use --verdict for mathematical validity.

real	0m0.396s
user	0m0.617s
sys	0m0.063s
```

Reference: the add_zero trial in `phase0-bend-guide.md` measured 385.4 ms +/- 15.7 ms on a quiet machine.
Minimum observed here (357.7 ms; single `time` runs 396 ms and 397 ms) matches that, so the smoke proof costs about the
same as add_zero; the larger means are load, not proof size.

## 4. The gate rejects broken input

Broken proof step, in `$TMPDIR/smoke_broken` (copy of `bend/smoke`): in `run_preserves`, pass `h` instead of the
`step_preserves` proof.

```
--- bend/smoke/PROOF.bend
+++ $TMPDIR/smoke_broken/PROOF.bend
@@ -23,4 +23,4 @@
     case Nil{}:
       h
     case +e <> t:
-      Laws.run_preserves(t, Code.step(s, e), Laws.step_preserves(s, e, h))
+      Laws.run_preserves(t, Code.step(s, e), h)
$ bend PROOF.bend
SOME PROOFS FAIL
Error:
- expected : {Cmp.is_le(Nat.cmp(Code.step(s, e), 3n)) == True{} : Bool}
- observed : {Cmp.is_le(Nat.cmp(s, 3n)) == True{} : Bool}
Context:
- e : Code.Ev
- t : List<&1, Code.Ev>
- s : Nat
- h : {Cmp.is_le(Nat.cmp(s, 3n)) == True{} : Bool}
Location: Laws.run_preserves
25 |     case +e <> t:
26>|       Laws.run_preserves(t, Code.step(s, e), h)
   |                                              ^
27 |
rc=1
```

Extra: broken code, in `$TMPDIR/smoke_mut` (cap in `step` changed from 3 to 4, proofs and laws untouched). The
law is then false and the checker refuses the `Inc` case at `s = 3`:

```
-      Nat.min(1n+s, 3n)
+      Nat.min(1n+s, 4n)
$ bend PROOF.bend
SOME PROOFS FAIL
Error:
- expected : False{}
- observed : True{}
Context:
- r : Nat
- h : {Cmp.is_le(Nat.cmp(r, 0n)) == True{} : Bool}
Location: Laws.step_preserves
18 |     case 1n+1n+1n+r Code.Inc{}:
19>|       {==}
   |       ^^^^
20 |
Note: the left side of the equality is the expected, the right side is the observed.
rc=1
```

## 5. Law strength: which mutants of `step` the laws catch

The laws only state an upper bound (`is_le(.., 3)`) plus `Reset -> 0`. I mutated the `Inc` line of `step` in
`$TMPDIR` copies (`mut_a` to `mut_d`; proofs and laws untouched) and ran `bend PROOF.bend` on each.

| Mutant of `Inc` | Result |
|---|---|
| (a) `0n` (Inc resets) | **ALL PROOFS CHECK (survives)** |
| (b) `Nat.min(1n+s, 2n)` (cap 2, not 3) | **ALL PROOFS CHECK (survives)** |
| (c) `s` (Inc is identity) | SOME PROOFS FAIL (rejected, but see below) |
| (d) `1n+s` (no cap) | SOME PROOFS FAIL (rejected) |
| earlier: cap 4 (section 4) | SOME PROOFS FAIL (rejected) |

```
=== (a) Inc = 0n
11c11
<       Nat.min(1n+s, 3n)
---
>       0n
ALL PROOFS CHECK
Use --verdict for mathematical validity.
rc=0
=== (b) cap 2
11c11
<       Nat.min(1n+s, 3n)
---
>       Nat.min(1n+s, 2n)
ALL PROOFS CHECK
Use --verdict for mathematical validity.
rc=0
=== (c) Inc = identity
11c11
<       Nat.min(1n+s, 3n)
---
>       s
SOME PROOFS FAIL
Error:
- expected : Cmp.is_le(Nat.cmp(r, 0n))
- observed : True{}
Context:
- r : Nat
- h : {Cmp.is_le(Nat.cmp(r, 0n)) == True{} : Bool}
Location: Laws.step_preserves
18 |     case 1n+1n+1n+r Code.Inc{}:
19>|       {==}
   |       ^^^^
20 | 
Note: the left side of the equality is the expected, the right side is the observed.
rc=1
=== (d) no cap
11c11
<       Nat.min(1n+s, 3n)
---
>       1n+s
SOME PROOFS FAIL
Error:
- expected : False{}
- observed : True{}
Context:
- r : Nat
- h : {Cmp.is_le(Nat.cmp(r, 0n)) == True{} : Bool}
Location: Laws.step_preserves
18 |     case 1n+1n+1n+r Code.Inc{}:
19>|       {==}
   |       ^^^^
20 | 
Note: the left side of the equality is the expected, the right side is the observed.
rc=1
```

Reading:

- (a) and (b) satisfy every law: the bound still holds and Reset still gives 0. The laws do not say that Inc
  counts up, or that the cap is exactly 3. The proof gate checks that the proofs fit the laws, not that the laws
  say enough, so a passing run says nothing about those behaviours.
- (c) is true under the hypothesis `h` (identity keeps `s <= 3`), yet it is rejected. The reason is brittleness of
  proof-by-cases, not strength of the laws: the proof closes the `3n+r` case with `{==}`, which cannot use `h`
  (`r` is stuck, `h` says `r <= 0`). A correct mutant fails closed here. The proof is tied to the exact shape of
  `step` and would need rewriting for any equivalent-under-`h` implementation. That is the safe direction
  (false rejection, not false acceptance), but it is not evidence that the law excludes (c).
- Lesson for UC1 to UC3: an invariant law alone does not pin behaviour. The mutant corpus will contain mutants of
  type (a) and (b) (a weaker or different step that still satisfies the bound), so each use case needs laws that
  pin the step's effect, such as `step(s, Inc) == min(s+1, cap)` or `Inc` increases when below the cap, and not
  only a bound. Every mutant must be run through the gate, and a surviving mutant is a finding about the laws.

## 6. Log entry (handover section 8 fields)

- Date/time: 2026-11-22, ~01:58 UTC (final run).
- Tool: Bend 2 (2.0.40), plain gate.
- Use case: Phase 0 smoke (step 3: trivial law and proof).
- What was done: wrote a saturating-counter module (`step`, `run`), three laws (trivial, per-event, over any
  event list), proved them with the LAWS/PROOF convention; checked the gate with a broken proof step and a broken
  code variant.
- Authoring time (honest estimate): about 10 minutes of wall time, including reading the guide.
- Failed proof iterations: **5** (counted by the stop rule: failed `bend` runs in the proofs before
  `ALL PROOFS CHECK`). Not counted: 2 `code.bend` compile/termination failures (friction items 1 and 2) and the
  deliberate broken-input and mutant runs in sections 4 and 5. The first run of the trivial law alone passed;
  the stretch laws first passed on the 8th run overall (7 failures in total).
- Machine time: single runs 0.397 s and 0.396 s (`time`, both pasted above); hyperfine mean 510.2 ms +/- 217.6 ms and 781.4 ms +/- 87.7 ms
  (10 runs, 2 warmups, noisy machine), minimum 357.7 ms.
- Result: `ALL PROOFS CHECK` with all three laws proved, no escape hatch; the gate rejects a broken proof step and
  several false variants of the code, but mutants (a) Inc=0 and (b) cap 2 survive (section 5). `--verdict` not run (no Lean).
- Size: `code.bend` 21 lines, `LAWS.bend` 21 lines, `PROOF.bend` 26 lines (`wc -l`).
- Friction / walls:
  1. `type Event` is rejected: Base already declares `Event` (`duplicate declaration: Event`). Renamed to `Ev`.
  2. Termination: `run(s, events)` calling `run(step(s, e), t)` is rejected ("a call smaller than ...; arguments are
     read left to right"). The shrinking list has to be the leftmost parameter, so the signature is `run(events, s)`.
  3. `LAWS.bend`'s import alias is local to it; `PROOF.bend` must also `import ./code.bend as Code` to name
     `Code.Inc` in patterns (`unknown: Code.Inc`).
  4. Match order: `match e:` then `match s:` is rejected ("'s' can't be matched in this position"); scrutinees follow
     binder order, so the proof matches both at once with `match s e:` and nested patterns `1n+1n+1n+r`.
  5. Affine usage: `run_preserves` uses `s` and `e` twice (in the recursive call's state and in the
     `step_preserves` proof). Fixes: `for +s: Nat` in the law (a `+s` in the def parameters is a parse error,
     `expected ':'`) and `case +e <> t:` in the pattern. The `+` on `s` is a quantity annotation in the law text.
  6. Hypotheses are law parameters (`for h: {...}`); `h` can be returned directly as the proof at the `Nil` case.
  7. The checker prints the goal in unfolded form (`Cmp.is_le(Nat.cmp(...))`) rather than `Nat.is_le(...)`.
  8. Law-filling defs again take no signature; the quantity `+` could not be put on them.

# UC2 Bend port and proofs (`bend/uc2`)

Tool: Bend 2 (bend 2.0.40), plain gate only. `--verdict` was not run (no Lean here, see `docs/results/phase0-bend-guide.md`), so every
`ALL PROOFS CHECK` below is provisional. All commands ran after `source .nix/env.sh`, from the repo root.

`bend/uc2/LAWS.bend` and `bend/uc2/spec.bend` are **draft pending user approval**. They were committed as 5c5c144 so that the proofs could start, and they
were not edited afterwards. `code.bend` was not edited after the commit either. Departures from the literal contract text are in section 10.

## 1. Timeline

| Event | Time (UTC, `date -u`) |
|---|---|
| Start (stop-rule clock) | 2026-11-23 03:59:49 |
| spec.bend, code.bend, LAWS.bend written and parsed (29 TODOs), question report | about 04:07 |
| P3b restated as a fold over every record (coordinator request), re-parsed | about 04:09 |
| Law text committed as 5c5c144, `PROOF.bend` started | about 04:09 |
| Gate first printed `ALL PROOFS CHECK` | 04:49:33 |
| Final verification (gate, probes, `just prove-bend`, hyperfine, two mutation runs) | 04:50 to 04:55 |

About 50 minutes of wall time, 14 failed proof iterations (limit 15). The stop rule did not trigger, but only one failure was left.
The later failures were typos in generated text (section 5), not proof ideas that did not work.

## 2. Files and what changed after the freeze

| File | Lines | Role |
|---|---|---|
| `bend/uc2/spec.bend` | 550 | draft, committed in 5c5c144, pending user approval: types, projections, `find_res`, `put_res`, `qty_sum`, `uniq`, `all_rec`, `inv`, `released_ok`, `stable`, rejection reasons |
| `bend/uc2/LAWS.bend` | 258 | draft, committed in 5c5c144, pending user approval: 29 laws |
| `bend/uc2/code.bend` | 128 | `step`, `run`, `run_fx` |
| `bend/uc2/PROOF.bend` | 2209 (1828 non-blank) | 29 `def Laws.<name>` plus 298 lemma defs |

`git diff -- bend/uc2/spec.bend bend/uc2/LAWS.bend bend/uc2/code.bend` against 5c5c144 is empty. `PROOF.bend` and this file are the only files this task
added. `main.bend` and `mutants/` belong to a later issue and were not created.

## 3. Law status (29 of 29 proved)

Gate output, verbatim:

```
$ bend bend/uc2/PROOF.bend
ALL PROOFS CHECK
Use --verdict for mathematical validity.
$ echo rc=$?
rc=0
```

Escape-hatch scan (`grep -n -E '@unsafe|\?|import "'` over PROOF, code, spec, LAWS, comment lines excluded): no hits. No `?TODO`, no `?name`, no `def f?`, no
foreign import. `grep -c '^law '` on LAWS is 29 and `grep -c '^def Laws\.'` on PROOF is 29.

| Law(s) | Status | Route |
|---|---|---|
| `init_inv` | proved | `init_inv_l`: five parts joined by `i_mk`. P2 needs `a == a + 0` twice (`Nat.add(Nat.add(t, 0n), 0n)` is stuck for abstract `t`); the other four parts are `{==}` |
| `inv_step` | proved | `match s e`; `inv_gr/gc/ge` split on `up`; `inv_rsv` (5 arms), `inv_conf1/2`, `inv_exp1/2` are generic in the guard Bools; three accept lemmas `inv_r_acc`, `inv_c_acc`, `inv_e_acc` |
| `inv_run` | proved | list induction over `inv_step` |
| `p2_conservation_step`/`_run`, `p3_once_*`, `p4a_before_due_*`, `a1_counters_*`, `a2_unique_*` | proved | extractors `i_p2`, `i_p3`, `i_p4a`, `i_a1`, `i_a2` applied to `inv_step`; each `_run` has its own induction (events used twice otherwise) |
| `p1b_take_step` | proved | `p1b_rsv` (guards generic), `lt_conf1/2`, `lt_exp1/2` (`a + b < a` is false), `eff_self` |
| `p4_expired_stays_step` | proved | `si_snoc`, `si_put` (case split on `is_eq(j, id)`), `find_put_ne`, `find_put_eq` |
| `p4b_confirm_guard_step` | proved | `p4b_*` family, `find_snoc`, `find_put_ne`, `find_put_eq`, `got_inj`; Reserve and Expire are refuted, Confirm gives the pair |
| `p3b_released_count_run` | proved | generalised induction `gen2` with accumulated effects: `pq` = `w_ok` (every `FxReleased` in the accumulator matches a record) and `released_ok2`; `pq_step` per event; `fxd_app`, `app2_assoc`, `app2_nil` |
| `pin_tick`, `pin_crash`, `pin_restart` | proved | `{==}` (code and law state the same projections) |
| `pin_down` | proved | `gate_f` (3 gated events), `pd_crash`, two absurd arms (`Tick`, `Restart`) |
| `pin_reserve_ok`, `pin_confirm_ok`, `pin_expire_ok` | proved | `Equal.trans` chain (`trP`): `gate_t`, a transport lemma generic in the guards (`rsv_ok_full`, `conf2_ok`, `exp2_ok`), `sub_wit` for the witness `a2` or `r2` |
| `pin_reserve_rejected`, `pin_confirm_rejected`, `pin_expire_rejected` | proved | `rsv_rej_full` (16 arms), `conf2_rej`, `exp2_rej`, `contra` |
| `pin_stable` | proved | `rs_refl`, `rs_snoc`, `rs_put`, `rstab`, `find_id` |
| `pin_dup_idempotent` | proved | `dup_rej` and `dup_acc` (two rewrites each), `bcase` on `reserve_ok_g`/`confirm_ok_g`/`expire_ok_g`, `find_snoc_new`, `find_put_eq` |

Hypothesis use: no pin, `p1b_take_step`, `p4_expired_stays_step` or `p4b_confirm_guard_step` uses its `h` (they hold for every state). The proofs that
really use `inv(s)`: `inv_step` (A1 is the guard for both `Nat.sub` calls on `reserved`; A2 gives the sku match and unique ids), the Confirm and Expire
parts of `pin_dup_idempotent` (the same guard), and `p3b_released_count_run` (A2's `uniq` for the Expire step, through `Laws.inv_step` in `gen2`).

## 4. Lemmas Base lacks (cost table)

Base (`bend base`) has no arithmetic lemma for `Nat.add` or `Nat.sub`, no `List.append` lemma, and no list-sum lemma. Its only laws near this are
`Nat.ge_refl`, `Nat.max_ge_l`, `Nat.max_ge_r`, `Equal.cong`, `Equal.sym`, `Equal.trans`, and commutativity for `U32` and `Word` (not `Nat`). Every lemma
below was written here. Minutes are wall time between the previous passing run and the run where the lemma first checked (so they include the lemmas
written in the same chunk); lines are the lemma's own lines. "Fail" is the number of failed `bend PROOF.bend` runs charged to the lemma (section 5).

The four lemmas that UC2.md predicted:

| Predicted by UC2.md | In Base? | Lemma written | Statement | Lines | Fail | Minutes |
|---|---|---|---|---|---|---|
| `a + b == c` gives `c - b == a` | no | `sub_add_cancel`, `sub_wit`, `le_sub_add` | `(a + b) - b == a`; from `a + b == x`, `x - b == a`; `a <= b` gives `(b - a) + a == b` | 8, 3, 13 | 0 | about 3 (with the next row) |
| `+` commutative and associative | no (only `U32.add_comm`, `Word.add_comm`) | `ac`, `aa`, with `az`, `as_` | `a + b == b + a`; `a + (b + c) == (a + b) + c`; `a == a + 0`; `1 + (a + b) == a + (1 + b)` | 8, 7, 7, 7 | 0 | about 3 |
| `a <= a + b` | no | `le_add_l`, `lt_add_false`, `le_via` | `b <= a + b`; `a + b < a` is false; `x + q == rv` gives `q <= rv` | 7, 8, 3 | 0 | about 2 |
| a list sum split at one element | no | `qs_put` (with `qp_pick`, `qs_snoc`, `qs_cons`, `sp_cn`, `qsn_pick`) | `qty_sum(put_res(rs, id, x)) + cn(r) == qty_sum(rs) + cn(x)` for the record `r` found at `id`; and the same for an appended record | 6 + 14, 6, 2, 7, 7 | 0 | about 5 |

All other lemmas, grouped (line counts are sums over the group):

| Group | Statements (shortened) | Lines | Fail | Minutes |
|---|---|---|---|---|
| Bool and Nat plumbing | `Disc`, `ft_absurd`, `tf_absurd`, `and_l/r/i`, `trN`, `symN`, `cong_add_l/r`, `sub_zero`, `eq_refl`, `eq_prop` (`is_eq(a,b)` true gives `a == b`), `eq_back`, `eq_sym_b`, `lt_of_not_le`, `lt_irrefl`, `add_cancel_r`, `not_f`, `not_t`, `or_ff`, `or_f_l/r`, `or_f`, `or_assoc`, `and_f_r`, `contra`, `bcase`, `symB`, `trB`, `trP`, `trL`, `symL`, `trE`, `symE` | about 330 | 0 | about 6 |
| Nat shuffles for P2 | `sw`, `add_sw3`, `p2_rsv`, `p2_conf`, `p2_exp` (the new sum equals the old sum, one per event) | 5, 9, 3, 5, 3 | 1 (argument order of `symN`) | about 3 |
| Record-list folds | `all_snoc`, `all_put`, `all_find` (one fold for P3, P4a, A2-sku, selected by `Facet`) | 6 each | 0 | about 3 |
| Ids | `hid_snoc`, `hid_snoc_f`, `uniq_snoc`, `hid_put`, `uniq_put`, `fn_hid` (`find` gives none, so `has_id` is false) | 8, 6, 6, 6, 6, 6 | 0 | about 4 |
| Counter parts of A1 | `cn_hit`, `cn_miss`, `held_put`, `held_split`, `sold_put_c`, `sold_put_e`, `ret_one` | about 30 | 1 (unbalanced parenthesis in a generated line) | about 4 |
| Inv parts and accept lemmas | `i_p2` .. `i_mk`, `inv_r_acc`, `inv_c_acc`, `inv_e_acc`, `inv_rsv`, `inv_conf1/2`, `inv_exp1/2`, `inv_g*` | about 150 | 3 (undefined name `hk`; affine copy of `clk`; `match` order) | about 12 |
| Find, put and snoc | `find_put_ne`, `find_put_eq`, `find_snoc`, `find_snoc_new`, `find_id`, `got_inj`, `sis_false`, `lis_false`, `si_snoc`, `si_put` | 6 each (`si_put` 2 + helpers) | 1 (wrong goal in a `Nil` case) | about 5 |
| P4, P4b, P1b | `p4_*`, `p4b_*`, `p1b_*`, `lt_conf*`, `lt_exp*` | about 200 | 3 (missing `: Bool`; missing match arm; wrong variable name) | about 10 |
| Pins | `gate_t`, `gate_f`, `rsv_ok_full`, `conf2_ok`, `exp2_ok`, `step_*_ok`, `*_rej_full`, `conf2_rej`, `exp2_rej`, `step_*_rej` | about 190 | 0 | about 6 |
| Stable | `so_refl`, `rec_refl`, `rs_refl`, `rs_snoc`, `rs_put`, `rstab`, `stable_*` | about 110 | 2 (`match` order; `{==}` on `is_eq(sku, sku)`) | about 6 |
| Duplicate delivery | `dup_rej`, `dup_acc`, `dup_rsv*`, `dup_conf*`, `dup_exp*`, `el_id`, `ca_conf`, `ea_exp`, `and_fl`, `and_fr`, `look_none_f` | about 120 | 0 | about 5 |
| P3b | `sne`, `rc_sne`, `qok_sne`, `rcp_comb`, `w_sne`, `count0`, `qok0`, `ro_nr`, `ro_snoc`, `ro_find`, `ro_put_gen`, `ro_keep`, `ro_exp`, `w_put`, `w_snoc_rs`, `pq_*`, `fxd_app`, `app2_assoc`, `app2_nil`, `gen2` | about 450 | 3 (rewrite in the wrong direction; missing `Spec.` prefix; `+` on a plain list) | about 20 |

## 5. Failed iterations (14 of 15)

I count every `bend PROOF.bend` run that printed `SOME PROOFS FAIL` with an error other than the open-law TODO count. The compile errors in `code.bend` and
`spec.bend` before the law text was committed (about 7 runs: affine copies, def order) are not counted, as in UC1. Most of `PROOF.bend` was generated by
small throwaway Python scripts (templates over the three events, not committed), so most failures were typos in the generator, not proof ideas.

| # | Where | What failed |
|---|---|---|
| 1 | `p2_rsv` | `symN(a, b, e)` takes `e : {a == b}`; I passed the arguments swapped |
| 2 | `held_put` | an unbalanced parenthesis in a hand-written chain of 9 nested `trN`; replaced by a builder function |
| 3 | `reserve_mk` | `clk` used twice without `+` |
| 4 | `inv_c_acc` | `hk` used in the generated text of the Confirm lemma but never bound |
| 5 | `Laws.inv_step` | `match u` after `match e` is rejected (`u` bound by the earlier `match s`); `match s e` plus helper defs that match `u` |
| 6 | `lt_conf1` | generated return type missing `: Bool` |
| 7 | `find_snoc` | wrong goal type in the `Nil` case (`find_res(snoc(Nil, x), id)` is not `NoRes`) |
| 8 | `p4_conf2` | generator emitted the `Held False` arm twice and no `Held True` arm |
| 9 | `Laws.p4b_confirm_guard_step` | generated `j` in the three trivial arms, the law's name is `id` |
| 10 | `rstab` | scrutinees must follow binder order (`x` before `r`) |
| 11 | `stable_conf2` | `{==}` used for `is_eq(sku, sku) == True`; stuck for abstract `sku`, needs `eq_refl` |
| 12 | `lq_put_t` | last rewrite had the wrong direction (goal and `P` did not match) |
| 13 | `pq_conf2` | `fx_data` is in Spec: missing `Spec.` prefix |
| 14 | `fxd_app` | `+f1` on a plain `List<Effect>`: a list of non-Data effects is not Data, so it cannot carry `+` |

After run 14 one more latent error was found by reading (not by a run): in `gen2` the plain list `t` would have been consumed twice, through the live
arguments of `fxd_app` and `app2_assoc`. I made `R`, `b` and `c` erased (`-R`, `-b`, `-c`) before the next run, and that run printed `ALL PROOFS CHECK`.

Families that passed first time: the Nat shuffles (except #1), `all_*`, `uniq_*`, `qs_put`, the three inv accept lemmas, all 12 pins, `rs_put`, the whole
duplicate-delivery family (9 lemmas that rewrite `step(s, e)` twice), `ro_exp`.

## 6. Command output

Probes (soundness of the checker against known-false inputs), after the final `PROOF.bend`:

```
$ bash bend/probes/run.sh
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
probes_rc=0
```

`just prove-bend` (with `XDG_RUNTIME_DIR=$TMPDIR`) exits 0: it checks `bend/uc*/PROOF.bend` (UC1 and UC2), then the probes, then the UC1 mutants.

Gate is not vacuous. Two deliberate runs on copies in `$TMPDIR` (laws and proofs unchanged), not counted above and not the mutant corpus (that belongs to
`bend/uc2/mutants/`, a later issue):

- `expire_acc` with `Nat.add(ret, 2n)` instead of `Nat.add(ret, 1n)`: `SOME PROOFS FAIL`, expected `... Nat.add(ret, 2n) ...`, observed `... Nat.add(ret, 1n) ...`, in the `inv_e_acc` family.
- `confirm`'s due test `Nat.is_le(exp, clock)` changed to `Nat.is_lt`: `SOME PROOFS FAIL`, expected `Cmp.is_lt(Nat.cmp(exp, clk))`, observed `Cmp.is_le(Nat.cmp(exp, clk))`.

## 7. Timing

`time bend bend/uc2/PROOF.bend`: real 2.246 s. Hyperfine (warm, under the 30 s threshold, 10 runs):

```
$ hyperfine --warmup 1 --runs 10 -N 'bend bend/uc2/PROOF.bend'
  Time (mean ± σ):      2.358 s ±  0.143 s    [User: 2.098 s, System: 0.169 s]
  Range (min … max):    2.226 s …  2.693 s    10 runs
```

No cold run (no on-disk proof cache observed, as in UC1). The 2200-line UC2 file checks in a third of the time of UC1's 2600-line file (6.5 s), because
UC2's proofs are generic in the guard Bools instead of enumerating slot shapes.

## 8. Size

`wc -l`: `spec.bend` 550, `code.bend` 128, `LAWS.bend` 258, `PROOF.bend` 2209. Proof to code ratio about 17 to 1 (lemmas 298, laws 29). The port itself
is smaller than UC1's, the proof is not.

## 9. Observations

**H1 (P1 holds by type in `Nat`).** There is no `p1` law, and no proof ever had to establish `available >= 0`: every number field is `Nat`. What does not go
away is truncation. `Nat.sub` appears three times in `code.bend` (reserve, confirm, expire) and each is only correct under a guard:
- Reserve: the guard `qty <= available` is a runtime test, so `le_sub_add` turns it into `(available - qty) + qty == available`.
- Confirm and Expire: the guard is a *theorem*, `reserved >= qty` for a `Held` record. It follows from A1 (`reserved == HeldQty`) and the split lemma
  `qs_put` / `held_split`, so `Inv` had to be an invariant strong enough to carry A1 (and A2 for the sku match) before the first `Nat.sub` could be proved.
So in Bend the non-negativity obligation moved from the type to the guard proof. This costs the arithmetic lemmas of section 4 (about 130 lines for the
Nat part, about 160 for the list sums, ids and record folds). TLC pays nothing for the same fact, because it checks the guard on reachable states only.

**H3 (laws quantify over every state and event list).**
- Helped: no bound anywhere (any `total`, any ids, any list length). The same step lemmas serve `_step` and `_run`.
- Cost: P3b needs a generalised induction (accumulated effects, `w_ok`, `released_ok2`, uniqueness of ids) because the contract text says "every record",
  not "the record with this id": the by-id form would have been weaker (coordinator decision). It is the largest family (about 450 lines, 3 failures).
- Law strength: every pin states the full equality over `step(s, e)` (Frame plus exact `fx`); none was weakened to a bound. The two deliberate runs of
  section 6 were refuted at the corresponding `inv_*` proof, not at an invariant statement.

## 10. Departures from the literal UC2.md text

1. One stock: `State.stock` is a single `Stock`, not `List<Stock>` (UC2.md section 6.7 says the Bend port uses exactly one stock). `init(sku, total)` sets the sku;
   events for another sku get `UnknownSku`. Accepted by the coordinator.
2. `run` and `run_fx` live in `code.bend`, `st` and `fx` in `spec.bend` (code imports spec). Accepted.
3. Pins quantify over the new counter: `a2` with `a2 + qty == available`, `r2` with `r2 + qty == reserved`; no law contains `-`. Accepted.
4. Rejection pins use the spec functions `reserve_reason`, `confirm_reason`, `expire_reason` (first failing check in contract order) and assume
   `reserve_ok_g == False` (etc.). The `*_reason` functions return a junk reason when the event would be accepted; the hypothesis excludes that case. Accepted.
5. P4, P4b by id; P3b as a fold over every record of the final state (`released_ok`), not by id (departure 7 of the first report, fixed by the coordinator).
   `released_ok` converts its plain effect list with `fx_data` so a record fold can reuse it (`List<Effect>` is not Data).
6. `Nat.add(clock, 1n)` and `Nat.add(ret, 1n)` are written literally in code and laws (an abstract `clock` makes the sum stuck, but code and law agree).
7. In the code the guards are Bools passed to helpers that match them (Bend cannot match a computed value). Behaviour is the same as `core.go` (checked by
   reading: check order, effects and Frame; the conformance harness compares them later).

## 11. Friction (Bend specific)

1. No arithmetic in Base. Every sum shuffle is a hand chain of `%` rewrites; I got the orientation right on the first try only after fixing a rule:
   `%e : P` replaces occurrences of the *right* side `b` by the left side `a`, so every helper equation had to be oriented "simple == compound".
2. Everything is affine, proofs included. `+h` for a proof used twice, `+` on a list needs a Data element type (`List<Effect>` is not Data and cannot be
   `+`), and a live argument that mentions a non-Data variable consumes it, so an *erased* parameter (`-R`) is the way to mention a list only in a type.
3. No `match` on a computed value, so every guard became a lemma generic in a variable `g` with a hypothesis `{computed == g}`. This cost no extra proof
   length: one lemma serves all arms, and the call site passes `{==}`.
4. `match a b` scrutinee order must follow binder order; a `match` after another `match` on a later binder rejects variables bound by the first one.
5. Error messages are good (expected and observed terms), but the gate reports one error per run, so a bug in a generator costs one iteration per bug.
6. Termination: `run(events, s)` with the shrinking list first worked; `gen2` needed the same.

## 12. Plain gate only

"Plain gate only, `--verdict` not run." `LAWS.bend` and `spec.bend` are draft pending user approval.

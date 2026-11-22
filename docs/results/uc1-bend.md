# UC1 Bend port and proofs (`bend/uc1`)

Tool: Bend 2 (bend 2.0.40), plain gate only. `--verdict` cannot run here (no Lean, see `docs/results/phase0-bend-guide.md`), so every
`ALL PROOFS CHECK` below is provisional. All commands ran after `source .nix/env.sh`, from the repo root.

## 1. Timeline

| Event | Time (UTC, `date -u`) |
|---|---|
| Start (stop-rule clock) | 2026-11-22 10:13:09 |
| Stage 1 done (port, spec, LAWS, first report) | about 10:19 |
| LAWS + spec frozen by the orchestrator (commit dc3d570) | after 10:22 |
| Gate first printed `ALL PROOFS CHECK` | about 10:44 |
| Final verification (gate, probes, hyperfine) | 10:45 to 10:48 |

About 35 minutes of wall time, 12 failed proof iterations (limit 15). The stop rule did not trigger.

## 2. Files and what changed after the freeze

| File | Lines | Role |
|---|---|---|
| `bend/uc1/spec.bend` | 390 | frozen: types, projections, `get/st/pr/od/set/has/init/inv`, `put_ord`, `put_prov`, `legal`, `rec_stable`, event classifiers |
| `bend/uc1/LAWS.bend` | 433 | frozen: 46 laws |
| `bend/uc1/code.bend` | 203 | executable `step` machinery (`go`, `slot_step`, per-event helpers, `recv`, `step`, `run`, `fst`, `snd`) |
| `bend/uc1/PROOF.bend` | 2634 | 46 `def Laws.<name>` plus 162 lemma defs |

Edits to `code.bend` after the freeze (commit dc3d570): none. `git diff -- bend/uc1/spec.bend bend/uc1/LAWS.bend bend/uc1/code.bend` is empty.
`PROOF.bend` is the only file this task changed in `bend/uc1` after the freeze. The other `bend/uc1` files (`main.bend`, `mutants/`) belong to other tasks.

## 3. Law status (all 46 proved)

Gate output, verbatim:

```
$ bend bend/uc1/PROOF.bend
ALL PROOFS CHECK
Use --verdict for mathematical validity.
$ echo rc=$?
rc=0
```

Escape-hatch scan (`grep -n -E '@unsafe|\?|import "'` over PROOF, code, spec, LAWS, comment lines excluded): no hits, no `?TODO`, no `?name`,
no `def f?`, no foreign import, no open law. `grep -c '^law '` on LAWS is 46 and `grep -c '^def Laws\.'` on PROOF is 46.

| Law(s) | Status | Route |
|---|---|---|
| `init_inv` | proved | `{==}` (inv of the 2 default slots computes) |
| `inv_step`, `inv_run` | proved | `inv_set`, `inv_get`, `sok_step` (per-helper `opk`/`ppk` lemmas); `inv_run` by list induction |
| `p1_step`, `p1_run`, `p2a_step`, `p2a_run` | proved | from `inv`: `inv_get`, then `p1_pv`, `p2a_pv`; `_run` by their own list induction (see friction 8) |
| `pin_place_order`, `_other` | proved | `pin_full` / `pin_same` plus a per-slot lemma `ps_place`, `ps_place_other` |
| `pin_retry_timeout`, `_other` | proved | same pattern |
| `pin_flush_charge_req`, `_other` | proved | same pattern |
| `pin_payment_approved`, `_other`, `pin_payment_declined`, `_other` | proved | same pattern |
| `pin_refund_order`, `_other`, `pin_flush_refund_req`, `_other` | proved | same pattern |
| `pin_charge_req_recv_approve`, `_decline`, `_replay_approved`, `_replay_declined`, `_zero` | proved | same pattern |
| `pin_flush_reply_approved`, `_declined`, `_other` | proved | same pattern |
| `pin_refund_req_recv`, `_other` | proved | `ps_a10`, `ps_a10_other` through `rp_core`, `rpo_core` (a lemma generic in the guard Bool `g`) |
| `pin_crash_restart_crash_order`, `_crash_prov`, `_restart_order`, `_restart_prov` | proved | `match s: {==}` |
| `pin_rule_d_order_down`, `_prov_down`, `_range` | proved | `recv_down`, `recv_range` (via `go_range`), 12 event arms |
| `pin_legal_transitions` (A12), `pin_prov_rec_stable` (A13) | proved | relation `rel` (see 4), `rel_step` |
| `p2b_a` | proved | from A12 (`pin_legal_transitions`) and `p2b_a_st` (25-arm status table) |
| `p2b_b` | proved | `rel_ro` and `p2b_b_od` (`orfrule` conjunct of `ro3`) |
| `p2b_c`, `p2b_d` | proved | `fx_step` / `go_fx` (an emitted effect came from `slot_step` of slot `ev_idx(e)`), then `wr_slot`/`wd_slot`, then `wr_fin`/`wd_fin`; `p2b_c` also uses `inv_get` |
| `p3_step`, `p3_run` | proved | `p3_od` (from `ro3`), `p3_state`, and an own induction `p3_run_l` |

Not stated: nothing from the contract was left out. Sub-law splits approved in Stage 1: A8 five-way, A9 and A11 splits, the `_other` laws, and the
7 rule-D and guard-fail laws.

Hypothesis use: no pin uses its `h`. `p2b_a`, `p2b_b`, `p2b_d`, `p3_step`, A12 and A13 do not use `h` either, so they hold for every state, reachable or
not. `p3_run` passes its `h` only to `inv_step` so that its recursion keeps the same shape. Only `inv_*`, P1, P2a and P2b(c) need `inv`.

## 4. Proof architecture (lemmas written)

Roughly in file order. Effort is wall time at the keyboard, including the generator scripts, not CPU time.

| Group | Lemmas | Size | Notes |
|---|---|---|---|
| Bool plumbing | `Disc`, `ft_absurd`, `Disc2`, `tf_absurd`, `empty_elim`, `and_l/r/i` | about 50 lines | `False == True` eliminated by a rewrite through a motive that sends `False` to `Unit` and `True` to the goal (the guide's `disc` trick) |
| inv machinery | `inv_get`, `inv_set`, `fl`, `fs`, `go_fst`, `ws_inv`, `inv_go`, `inv_recv`, `inv_step`, `inv_run` | about 90 lines | `go_fst` states `set(l,o,fs(slot_step(get_l(l,o),k,e))) == fl(go(l,o,k,e))` by induction on list and index |
| `slot_ok` preservation | `opk`, `ppk`, `sok_split`, `sok_join`, `sok_wo`, `sok_wp`, `lt_le`, `nle_zero`, 7 `op_*` lemmas (generated, 20 leaves each), `pp_flush_reply`, `pp_charge_recv`, `pp_rp`, `sok_step` | about 440 lines | `slot_ok` splits as `and(ppk(pv), opk(od))`; the order helpers touch only `opk`, the provider helpers only `ppk` |
| P1, P2a | `p1_pv`, `p2a_pv`, `p1_slot`, `p2a_slot`, `p1_state`, `p2a_state` | about 45 lines | |
| Pin infrastructure | `seq`, `seq_refl`, `st_true`, `st_ne` (25 arms), `rseq`, `rec_true`, `set_get`, `mkl`, `cons_tail_mkl`, `cons_slot_mkl`, `go_eq`, `pin_gen`, `pin_full`, `pin_same` | about 190 lines | `pin_full` turns a slot-level fact `(xn, fx) == slot_step(get_l(sl,i), i, e)` into the state-level pin. Status/Res hypotheses are converted to Bool tests (`seq`, `rseq`) so that the case split computes |
| Pins | 20 `ps_*` slot lemmas (generated, one arm per relevant slot shape) and their `def Laws.pin_*`; `rp_core`, `rpo_core`, `ps_a10`, `ps_a10_other` by hand | about 900 lines | all generated by a throwaway script from a table of (event, guard, new slot, effects) |
| Rule D | `recv_down`, `go_range`, `recv_range`, three laws with 12 arms each | about 100 lines | |
| Relation `rel` | `fL`, `fF`, `fT`, `ro3`, `rpc`, `rel`, `rel_refl`, `ro_*` (7, generated), `rp_*` (3), `rel_wo`, `rel_wp`, `rel_slot_step`, `rel_set`, `ws_get`, `rel_recv`, `rel_step` | about 650 lines | one Bool relation covering legal status moves, "outRefund false-to-true only from Paid", "a terminal order keeps its amount", `rec` stability and non-decreasing counts. `rel_set` lifts it from slot `o` to any slot `q` (this is the "other index" case that the laws' independent `o` needs) |
| P2b(a), (b), P3 | `p2b_a_st`, `seq_to_eq` (25 arms each), `p2b_b_od`, `p3_st`, `p3_st2`, `nat_eq_true`, `imp_t`, `p3_od`, `p3_ht`, `p3_state`, `p3_ht_state`, `p3_run_l` | about 190 lines | |
| P2b(c), (d) | `go_fx`, `fx_ws`, `fx_recv`, `fx_step`, `wr_rp`, `wd_rp`, `wr_slot`, `wd_slot` (about 60 absurd arms each), `wr_fin`, `wd_fin`, `p2b_c_l`, `p2b_d_l` | about 320 lines | |

About 70 percent of `PROOF.bend` was produced by small throwaway Python scripts that enumerate slot shapes (status 5 x flags 2 x 2, rec 3,
`a` zero or successor) and emit the arms. The scripts are not committed. Which arm is `{==}`, a hypothesis, or a `ft_absurd`/`tf_absurd` was decided
by a small model in the script; a wrong model would have shown up as a failed arm, and none did.

## 5. Failed iterations (12 of 15)

I count every `bend PROOF.bend` run that printed `SOME PROOFS FAIL` with an error other than the open-law TODO count. Definition-level errors
(termination, affine use, parse) are included to be conservative. The Stage 1 compile errors in `code.bend` (affine copies, `None` clash, def order,
about 9 runs) are not counted, as in Phase 0.

| # | Where | What failed |
|---|---|---|
| 1 | `Disc` | erased `-G` used live: parameter must be a normal `G: Type` |
| 2 | `and_l` | a match on an erased `-a`: "live scrutinee"; made `a` and `b` plain `+a`, `+b` |
| 3 | `and_i` | rewrite in the wrong direction (`%ha`); replaced by a match on `a` |
| 4 | `inv_set` | `hh` consumed more than once; lemma proof parameters need `+hh` |
| 5 | `go_fst` | `_` is not accepted as an explicit argument of `Equal.sym`; replaced by two rewrites |
| 6 | `pp_charge_recv` | `match cc rc` after other binders is rejected; moved the numbers into the top-level patterns |
| 7 | `p1_state` | `match (Spec.get_l(sl, q))`: no match on a computed value; added slot-level lemmas that match their parameter |
| 8 | `Laws.p1_run` | `events` used twice in the law's call (the law's `events` is not `+`, and a list of non-Data effects cannot be copied); each `_run` law got its own induction |
| 9 | `st_ne` | `case _ _` does not refine `y`, so `seq(NoOrder, y)` stayed stuck; enumerated all 25 pairs |
| 10 | `ps_charge_zero` | `charge_recv(pv, k, 0n, d)` does not reduce until `pv` and `d` are matched; added the 6 arms |
| 11 | `p2b_a_st` | a `+` hypothesis whose type is a function (`x != y`): not Data, so no `+` |
| 12 | `wr_fin` | same, for a pair of proofs |

After run 12 the gate printed `ALL PROOFS CHECK`. Lemma families that passed first time: `sok_step` and its 140 generated arms, `go_eq`/`pin_gen`,
all 20 generated pin lemmas, the `rel` machinery, `p3_*`, and the 60-arm `wr_slot`/`wd_slot`.

## 6. Command output

Probes (soundness of the checker against known-false inputs), after the final PROOF.bend:

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

Gate is not vacuous: a mutated copy of `code.bend` in `$TMPDIR/mut1` (the `NoRec/Approve` result gets `1n+1n+cc` instead of `1n+cc`; laws and proofs
unchanged) gives `SOME PROOFS FAIL` at `pp_charge_recv` (expected `False{}`, observed `True{}`). This was one deliberate run, not counted above.
The full mutant corpus belongs to another task (`bend/uc1/mutants/`).

## 7. Timing

`time bend bend/uc1/PROOF.bend` (first run after the warmup of the earlier probes): real 6.974 s, user 5.797 s. Hyperfine, 5 runs of about 6.5 s each
(under the 30 s threshold, so `--runs 5`):

```
$ hyperfine --warmup 1 --runs 5 -N 'bend bend/uc1/PROOF.bend'
  Time (mean ± σ):      6.484 s ±  0.099 s    [User: 5.600 s, System: 0.367 s]
  Range (min … max):    6.411 s …  6.624 s    5 runs
```

Cold: no separate cold run (the binary is in the page cache, and Bend keeps no on-disk proof cache that I could observe, as in Phase 0). The first
single run was 6.97 s, which is the closest figure.

## 8. Size

`wc -l`: `spec.bend` 390, `code.bend` 203, `LAWS.bend` 433, `PROOF.bend` 2634. Proof to code ratio about 13 to 1 (lemmas 162, laws 46).

## 9. Friction and walls (Bend specific)

1. A constructor cannot be named `None` (Base's `Maybe` owns it): `Status.None` is `NoOrder`. `Event` is also taken: `Ev`.
2. Everything is affine, proofs included. A proof parameter used twice needs `+h`; a law parameter cannot be changed (frozen), so a law whose body
   needs a hypothesis twice must hand it to a lemma that has `+h`. A hypothesis whose type is a function (`x != y`) or a pair of proofs is not
   Data, so it can never be `+`: it must be consumed exactly once. `events: List<Ev>` cannot be `+`: laws about `run` need their own induction.
3. `match` only on parameters or pattern-bound variables, never on a computed value. Every computed Bool or Nat used as a case split needs a helper
   def that takes it as a parameter (`refund_pick(pv, k, g)`, `rp_core`, `ro3_mk`).
4. A case split must give the reducer constructors: `case _ _` does not refine the other column (friction 9 in section 5); stuck terms like
   `seq(NoOrder, y)` or `charge_recv(pv, k, 0n, d)` need the pattern spelled out (all status pairs, `pv` and `d`). The proofs are therefore long
   enumerations. I generated them by script.
5. Rewrites: `%e : P` converts a goal containing `b` into one containing `a`, so the orientation of every helper equation (`go_fst`, `ws_get`,
   `cons_tail_mkl`) had to be chosen from the use site. Wrong orientation is the most common error; there is no `Equal.sym` shortcut because
   `_` is not accepted for erased arguments.
6. Absurd cases need a type argument: `ft_absurd(G, h)` where `G` is the whole goal, written out each time (generated).
7. No definitional unfolding of Base's `Bool.and` with a stuck first argument: `and(PP, X)` with abstract `PP` does not reduce, so the invariant is
   split with `and_l`/`and_r`/`and_i`, never matched.
8. Checking time is small: 6.5 s for 2.6 k lines.
9. Error messages are good for type mismatches (expected and observed terms plus context), poor for the first error only: the gate reports one
   error per run, so a family of generated arms with one bug costs one iteration per bug.

## 10. Ambiguities and deviations (all from the frozen contract; none changed)

1. Rule D: the range check is the `Nil` case of `go`; equivalent to `o < length(slots)`. The laws state it with `List.length` and `hr`.
2. A8 split in five laws, `_other` laws, rule-D laws, A11 split: orchestrator approved them in Stage 1.
3. `chargeCount + 1` is written `1n+cc` in code and in the laws (`Nat.add(cc, 1n)` would not compute for abstract `cc`).
4. `pin_flush_reply_other` (A9, `outReply` true and `rec = NoRec` gives F) is state-reachable under `Inv` (the contract does not exclude it) and is
   proved as a law with the same literal reading as Go.
5. No disagreement with Go's resolved ambiguities (`docs/results/uc1-core.md`).

## 11. H3 note (quantifying over every state and event list)

- Helped: the laws hold for arbitrary `s` and arbitrary event lists, so there is nothing to bound. The same proof that handles `[]` handles any `run`
  by one induction. A12, A13, P2b(a), P2b(b), P3 and every pin go through with no reachability argument at all (the `h` is unused for them).
  `inv` is needed only for P1, P2a and P2b(c), where the order-side conjunct "`outRefund` implies `Refunded`" is exactly what stops a
  flush of a never-requested refund from being a counterexample (an unreachable state would otherwise break P2b(c): `outRefund` true with status
  `Paid` is a legal tuple of fields but not reachable). The `Inv` conjuncts that the contract added (the order half) were therefore necessary,
  not decoration.
- Blocked or costly: the price of quantifying over every state is the case analysis. Every claim reduces to an enumeration of slot shapes
  (about 500 generated arms for `Inv` and pins alone). TLC pays this by exploring reachable states; Bend pays it in proof text. Two-slot or larger
  `N` costs nothing extra in Bend because the laws are index-polymorphic, but they need the `rel_set` and `go_fst` list lemmas, which TLC never
  needs.
- Cross-service: no law here needs a "was sent" hypothesis because UC1's contract is single-service per property (Q7). Under the default, none of the
  cross-side invariants (`PaidImpliesCharged`, `NoChargeOnFailed`) were stated, so H3's hardest case (an invariant that depends on a network sent-ness)
  was not exercised by this use case.
- Law strength: the pins pin each event's exact result, with rule D and guard-fail F laws added. One mutant run (section 6) was rejected at the proof of
  the corresponding pin lemma, not at the invariant. The full mutant corpus (M1, M2a, M2b, M3, M4, M5) is another task's.

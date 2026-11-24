# UC2 laws in mathematical notation

This page restates the 29 laws of `bend/uc2/LAWS.bend` as formulas. It is a reading aid. `LAWS.bend` is the frozen source and the only text the checker proves. No tool checks this page, so if the two ever disagree, `LAWS.bend` wins.

Proof status of the laws as written in `LAWS.bend`: `bend bend/uc2/PROOF.bend` and `bend bend/uc2/PROOF.bend --verdict` both print `ALL PROOFS CHECK` (log 4.27, run on 2026-11-23).

## Notation

| Symbol | Meaning in the Bend source |
|---|---|
| s | a `Spec.State` = ⟨up, clock, stock, res⟩ |
| stock | ⟨sku, total, avail, rsv, sold⟩ (`k_sku`, `k_total`, `k_avail`, `k_rsv`, `k_sold`) |
| res | the list of reservation records ⟨id, sku, qty, status, exp, confirmedAt, returned⟩ |
| status | Held, Confirmed or Expired |
| e, es | an event, a list of events |
| step(s, e) = ⟨s′, fx⟩ | `Code.step`: the next state and the list of effects emitted |
| run(es, s) | `Code.run`: fold `step` over the list |
| Inv(s) | `Spec.inv(s) == True`, which is P2 ∧ P3 ∧ P4a ∧ A1 ∧ A2 below |
| [ ] | the empty effect list (`Nil`) |
| s[…] | s with only the named fields replaced; unnamed fields are kept |

Every law below also assumes Inv(s), except `init_inv` and `p3b_released_count_run`. This is the hypothesis `h` in `LAWS.bend`.

## The five parts of the invariant

| Name | Formula |
|---|---|
| P2: stock adds up | avail + rsv + sold = total |
| P3: returned once | ∀ r ∈ res. returned(r) = 1 if status(r) = Expired, else 0 |
| P4a: confirmed before due | ∀ r ∈ res. status(r) = Confirmed ⇒ confirmedAt(r) < exp(r) |
| A1: counters match records | rsv = HeldQty(res, sku) ∧ sold = ConfirmedQty(res, sku) |
| A2: unique ids | ids in res are pairwise distinct ∧ every record's sku is the stock's sku |

`HeldQty` and `ConfirmedQty` are `held_qty` and `confirmed_qty` in `bend/uc2/spec.bend`. They total the quantities of the Held and the Confirmed records. Inv(s) is the conjunction of all five.

## Invariant and per-property laws

Each of P2, P3, P4a, A1 and A2 has a one-event law and an any-event-list law, where s′ := run(es, s).

| Law | Formula |
|---|---|
| `init_inv` | ∀ sku t. Inv(init(sku, t)) |
| `inv_step` | ∀ s e. Inv(s) ⇒ Inv(s′) |
| `inv_run` | ∀ es s. Inv(s) ⇒ Inv(run(es, s)) |
| `p2_conservation_step`, `_run` | Inv(s) ⇒ avail′ + rsv′ + sold′ = total′ |
| `p3_once_step`, `_run` | Inv(s) ⇒ P3(s′) |
| `p4a_before_due_step`, `_run` | Inv(s) ⇒ P4a(s′) |
| `a1_counters_step`, `_run` | Inv(s) ⇒ A1(s′) |
| `a2_unique_step`, `_run` | Inv(s) ⇒ A2(s′) |

## Properties about what changes

| Law | Formula |
|---|---|
| `p1b_take_step` (P1b) | Inv(s) ∧ avail(s′) < avail(s) ⇒ P1b(s, e, ⟨s′, fx⟩). The comment says: available drops only by an accepted Reserve, by exactly qty, with the one FxReserved. |
| `p4_expired_stays_step` (P4) | Inv(s) ∧ status(s, id) = Expired ⇒ status(s′, id) = Expired. No Confirm revives an expired record. |
| `p4b_confirm_guard_step` (P4b) | Inv(s) ∧ find(res(s), id) = r ∧ status(r) ≠ Confirmed ∧ status(s′, id) = Confirmed ⇒ status(r) = Held ∧ ¬(exp(r) ≤ clock(s)) |
| `p3b_released_count_run` (P3b) | ∀ es sku t. released_ok(res(run(es, init(sku,t))), fx(es, init(sku,t))) |

P3b has no Inv hypothesis. It starts from `init`, and `fx(es, …)` is `Code.run_fx`, the effects emitted over the whole run. The comment says: for every record of the final state, `returned` equals the number of `FxReleased` effects emitted for that record, each with the record's qty.

## Pins: the exact effect of each event

These laws state the whole result of a step, not just a bound. They are the ones that stop a mutant from slipping through. Each row is an equation ⟨s′, fx⟩ = step(s, e). Unless a row says otherwise, the condition includes up(s).

| Pin | Event | Condition | s′ | fx |
|---|---|---|---|---|
| S0 | any event except Tick and Restart | ¬up(s) | s | [ ] |
| S1 | Tick | any (up or down) | s[clock := clock + 1] | [ ] |
| S2 | Reserve(id, sku, qty, ttl) | qty > 0 ∧ ttl > 0 ∧ sku = stock sku ∧ id not in res ∧ qty ≤ avail; a₂ + qty = avail | s[avail := a₂, rsv := rsv + qty, res := res ++ [⟨id, sku, qty, Held, clock + ttl, 0, 0⟩]] | [FxReserved(id, sku, qty, clock + ttl)] |
| S3 | Reserve(id, sku, qty, ttl) | any of the S2 checks fails | s | [FxRejected(id, reason)], reason = the first failing check |
| S4 | Confirm(id) | record is Held ∧ ¬(exp ≤ clock); r₂ + qty = rsv | s[rsv := r₂, sold := sold + qty, record := Confirmed with confirmedAt = clock] | [FxConfirmed(id)] |
| S5 | Confirm(id) | the S4 checks fail | s | [FxRejected(id, reason)], reason ∈ {UnknownReservation, NotHeld, TooLate} |
| S6 | Expire(id) | record is Held ∧ exp ≤ clock; r₂ + qty = rsv | s[avail := avail + qty, rsv := r₂, record := Expired with returned := returned + 1] | [FxReleased(id, qty)] |
| S7 | Expire(id) | the S6 checks fail | s | [FxRejected(id, reason)], reason ∈ {UnknownReservation, NotHeld, NotYet} |
| S8 | Crash | any (also when already down) | s[up := false] | [ ] |
| S9 | Restart | any (also when already up) | s[up := true] | [ ] |

The reasons for S3 are, in check order, BadRequest, UnknownSku, DuplicateId and InsufficientStock.

The laws write counter changes in additive form: the new value is a variable (a₂, r₂) with a₂ + qty = avail, never a subtraction. This is what the header comment of `LAWS.bend` says.

### Shape of the whole transition

| Pin | Formula |
|---|---|
| S10 | ∀ s e. Inv(s) ⇒ stable(s, s′). The comment says: total, id, sku, qty and expiresAt never change, and Confirmed and Expired records keep their status. |
| S11 | ∀ s e. Inv(s) ∧ dupable(e) ⇒ state(step(state(step(s, e)), e)) = state(step(s, e)). The comment says: delivering a Reserve, Confirm or Expire twice equals delivering it once. |

## Count check

17 laws before the pins (3 invariant, 1 P1b, 2 P2, 2 P3, 2 P4a, 2 A1, 2 A2, 1 P4, 1 P3b, 1 P4b) plus 12 pins (S0 to S11) make 29, which matches the 29 laws in `LAWS.bend`.

## What this page does not tell you

- The helper predicates (`p1b`, `stable`, `released_ok`, `dupable`) are defined in `bend/uc2/spec.bend`. The one-line readings above come from the comments in `LAWS.bend`, not from the definitions.
- It does not say the laws are the right ones. The user approved them on 2026-11-23, and a pass only means the code meets these laws.
- The proofs cover the Bend port in `bend/uc2/code.bend`, not the Go service.

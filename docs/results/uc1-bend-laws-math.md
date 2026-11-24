# UC1 laws in mathematical notation

This page restates the 46 laws of `bend/uc1/LAWS.bend` as formulas. It is a reading aid. `LAWS.bend` is the frozen source and the only text the checker proves. No tool checks this page, so if the two ever disagree, `LAWS.bend` wins.

Proof status of the laws as written in `LAWS.bend`: `bend bend/uc1/PROOF.bend` and `bend bend/uc1/PROOF.bend --verdict` both print `ALL PROOFS CHECK` (log 4.27, run on 2026-11-23).

## Notation

| Symbol | Meaning in the Bend source |
|---|---|
| s, s′ | a `Spec.State`; s′ = fst(step(s, e)) |
| e, es | an event, a list of events |
| step(s, e) = ⟨s′, fx⟩ | `Code.step`: the next state and the list of effects emitted |
| run(es, s) | `Code.run`: fold `step` over the list |
| Inv(s) | `Spec.inv(s) == True`; defined by `inv_slots` in `bend/uc1/spec.bend` |
| o, x, a | an order id, a refund amount, a charge amount (all `Nat`) |
| st(s,o), amt(s,o) | status and amount of order o on the order side |
| rec(s,o) | the provider's idempotency record for o: NoRec, Approved or Declined |
| cc(s,o), rc(s,o) | `charge_count`, `refund_count` of the provider record for o |
| \|slots\| | `List.length(slots_of(s))`, the number of order slots |
| s[o.ord := …] | s with only the order-side record of o replaced (`put_ord`) |
| s[o.prov := …] | s with only the provider-side record of o replaced (`put_prov`) |
| [ ] | the empty effect list (`Nil`) |

Every law below also assumes Inv(s). This is the hypothesis `h` in `LAWS.bend`.

## Invariant

| Law | Formula |
|---|---|
| `init_inv` | Inv(init(N)) |
| `inv_step` | ∀ s e. Inv(s) ⇒ Inv(s′) |
| `inv_run` | ∀ es s. Inv(s) ⇒ Inv(run(es, s)) |

## Safety properties

Written once for one event, then over any list of events.

| Law | One event | Any event list |
|---|---|---|
| P1: never charged twice | ∀ s e o. Inv(s) ⇒ cc(s′,o) ≤ 1 | ∀ es s o. Inv(s) ⇒ cc(run(es,s),o) ≤ 1 |
| P2a: refunds never exceed charges | ∀ s e o. Inv(s) ⇒ rc(s′,o) ≤ cc(s′,o) | the same with s′ := run(es, s) |
| P3: terminal status is final | ∀ s e o. Inv(s) ∧ terminal(st(s,o)) ⇒ (st(s′,o), amt(s′,o)) = (st(s,o), amt(s,o)) | the same with s′ := run(es, s) |

P2b has four clauses. Clauses (c) and (d) talk about the effects the step emits, so the conclusion is about s, not s′.

| Law | Formula |
|---|---|
| `p2b_a` | Inv(s) ∧ st(s,o) ≠ Refunded ∧ st(s′,o) = Refunded ⇒ st(s,o) = Paid |
| `p2b_b` | Inv(s) ∧ ¬outRefund(s,o) ∧ outRefund(s′,o) ⇒ st(s,o) = Paid |
| `p2b_c` | Inv(s) ∧ WireRefundReq(o) ∈ fx ⇒ st(s,o) = Refunded |
| `p2b_d` | Inv(s) ∧ Refund(o,x) ∈ fx ⇒ rec(s,o) = Approved |

## Pins: the exact effect of each event

These laws state the whole result of a step, not just a bound. They are the ones that stop a mutant from slipping through. Each row is an equation ⟨s′, fx⟩ = step(s, e).

Unless a row says otherwise, the conditions also include: the service that receives the event is up (orderUp or provUp), and o < \|slots\|. The laws with `_other` in their name say the event does nothing, step(s, e) = ⟨s, [ ]⟩, when the stated condition fails.

### Order service

| Pin | Event | Condition | s′ | fx |
|---|---|---|---|---|
| A1 | PlaceOrder(o,a) | a > 0 ∧ st(s,o) = NoOrder | s[o.ord := ⟨AwaitingPayment, a, outCharge = true, outRefund kept⟩] | [ ] |
| A1 `_other` | PlaceOrder(o,a) | ¬(a > 0 ∧ st(s,o) = NoOrder) | s | [ ] |
| A2 | RetryTimeout(o) | st(s,o) = AwaitingPayment | s[o.ord := outCharge = true, rest kept] | [ ] |
| A2 `_other` | RetryTimeout(o) | st(s,o) ≠ AwaitingPayment | s | [ ] |
| A3 | FlushChargeReq(o) | outCharge(s,o) | s[o.ord := outCharge = false, rest kept] | [WireChargeReq(o, amt(s,o))] |
| A3 `_other` | FlushChargeReq(o) | ¬outCharge(s,o) | s | [ ] |
| A4 | PaymentApproved(o) | st(s,o) = AwaitingPayment | s[o.ord := st = Paid, rest kept] | [ ] |
| A4 `_other` | PaymentApproved(o) | st(s,o) ≠ AwaitingPayment | s | [ ] |
| A5 | PaymentDeclined(o) | st(s,o) = AwaitingPayment | s[o.ord := st = Failed, rest kept] | [ ] |
| A5 `_other` | PaymentDeclined(o) | st(s,o) ≠ AwaitingPayment | s | [ ] |
| A6 | RefundOrder(o) | st(s,o) = Paid | s[o.ord := st = Refunded, outRefund = true, rest kept] | [ ] |
| A6 `_other` | RefundOrder(o) | st(s,o) ≠ Paid | s | [ ] |
| A7 | FlushRefundReq(o) | outRefund(s,o) | s[o.ord := outRefund = false, rest kept] | [WireRefundReq(o)] |
| A7 `_other` | FlushRefundReq(o) | ¬outRefund(s,o) | s | [ ] |

### Payment provider

For the provider record, "outReply := true" means the provider queues the stored answer to be sent.

| Pin | Event | Condition | s′ | fx |
|---|---|---|---|---|
| A8 approve | ChargeReqRecv(o,a,Approve) | a > 0 ∧ rec(s,o) = NoRec | s[o.prov := ⟨Approved, cc+1, rc, a, outReply = true⟩] | [Charge(o,a)] |
| A8 decline | ChargeReqRecv(o,a,Decline) | a > 0 ∧ rec(s,o) = NoRec | s[o.prov := ⟨Declined, cc, rc, amt kept, outReply = true⟩] | [ ] |
| A8 replay | ChargeReqRecv(o,a,d) for any d | a > 0 ∧ rec(s,o) = Approved | s[o.prov := record kept, outReply = true] | [ ] |
| A8 replay | ChargeReqRecv(o,a,d) for any d | a > 0 ∧ rec(s,o) = Declined | s[o.prov := record kept, outReply = true] | [ ] |
| A8 zero | ChargeReqRecv(o,0,d) | any | s | [ ] |
| A9 approved | FlushReply(o) | outReply ∧ rec(s,o) = Approved | s[o.prov := outReply = false] | [WireApproved(o)] |
| A9 declined | FlushReply(o) | outReply ∧ rec(s,o) = Declined | s[o.prov := outReply = false] | [WireDeclined(o)] |
| A9 `_other` | FlushReply(o) | ¬(outReply ∧ rec(s,o) ≠ NoRec) | s | [ ] |
| A10 | RefundReqRecv(o) | rec(s,o) = Approved ∧ rc < cc | s[o.prov := rc + 1, rest kept] | [Refund(o, amt)] |
| A10 `_other` | RefundReqRecv(o) | ¬(rec(s,o) = Approved ∧ rc < cc) | s | [ ] |

The two replay rows are the idempotency rule. A repeated charge request with an existing record adds no ledger row and emits no `Charge`.

### Crash, restart and out-of-range events

| Pin | Event | s′ | fx |
|---|---|---|---|
| A11 | Crash(OrderSvc) | orderUp := false, rest kept | [ ] |
| A11 | Crash(Provider) | provUp := false, rest kept | [ ] |
| A11 | Restart(OrderSvc) | orderUp := true, rest kept | [ ] |
| A11 | Restart(Provider) | provUp := true, rest kept | [ ] |

Rule D: an event does nothing, step(s, e) = ⟨s, [ ]⟩, in three cases.

| Pin | Condition |
|---|---|
| D, order down | e is an order-service event ∧ ¬orderUp |
| D, provider down | e is a provider event ∧ ¬provUp |
| D, range | e is not Crash or Restart ∧ \|slots\| ≤ index(e) |

### Shape of the whole transition

| Pin | Formula |
|---|---|
| A12 | ∀ s e o. Inv(s) ⇒ legal_transition(s, s′, o). The comment says: `st` changes only along the four legal arrows. |
| A13 | ∀ s e o. Inv(s) ⇒ rec_stable(s, s′, o). The comment says: `rec` changes only from NoRec to Approved or Declined, and the counts never decrease. |

The definitions of `legal_transition` and `rec_stable` are in `bend/uc1/spec.bend`.

## Count check

13 laws before the pins (3 invariant, 2 P1, 2 P2a, 4 P2b, 2 P3) plus 33 pins make 46, which matches the 46 laws in `LAWS.bend`.

## What this page does not tell you

- It does not say what Inv(s) contains. See `inv_slots` in `bend/uc1/spec.bend` and `properties/UC1.md` section 2.
- It does not say the laws are the right ones. The user approved them on 2026-11-23, and a pass only means the code meets these laws.
- The proofs cover the Bend port in `bend/uc1/code.bend`, not the Go service.

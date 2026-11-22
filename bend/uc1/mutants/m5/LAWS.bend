import Base
import ./spec.bend as Spec
import ./code.bend as Code

# Init satisfies Inv.
law init_inv:
  {Spec.inv(Spec.init(Spec.N())) == True{} : Bool}

# Inv is preserved by every event.
law inv_step:
  for +s: Spec.State
  for +e: Spec.Ev
  for h: {Spec.inv(s) == True{} : Bool}
  {Spec.inv(Code.fst(Code.step(s, e))) == True{} : Bool}

# Inv is preserved by any event list.
law inv_run:
  for events: List<Spec.Ev>
  for +s: Spec.State
  for h: {Spec.inv(s) == True{} : Bool}
  {Spec.inv(Code.run(events, s)) == True{} : Bool}

# P1: an order is never charged more than once (one event).
law p1_step:
  for +s: Spec.State
  for +e: Spec.Ev
  for +o: Nat
  for h: {Spec.inv(s) == True{} : Bool}
  {Nat.is_le(Spec.charge_count(Spec.pr(Code.fst(Code.step(s, e)), o)), 1n) == True{} : Bool}

# P1 over any event list.
law p1_run:
  for events: List<Spec.Ev>
  for +s: Spec.State
  for +o: Nat
  for h: {Spec.inv(s) == True{} : Bool}
  {Nat.is_le(Spec.charge_count(Spec.pr(Code.run(events, s), o)), 1n) == True{} : Bool}

# P2a: refundCount <= chargeCount (one event).
law p2a_step:
  for +s: Spec.State
  for +e: Spec.Ev
  for +o: Nat
  for h: {Spec.inv(s) == True{} : Bool}
  {Nat.is_le(Spec.refund_count(Spec.pr(Code.fst(Code.step(s, e)), o)), Spec.charge_count(Spec.pr(Code.fst(Code.step(s, e)), o))) == True{} : Bool}

# P2a over any event list.
law p2a_run:
  for events: List<Spec.Ev>
  for +s: Spec.State
  for +o: Nat
  for h: {Spec.inv(s) == True{} : Bool}
  {Nat.is_le(Spec.refund_count(Spec.pr(Code.run(events, s), o)), Spec.charge_count(Spec.pr(Code.run(events, s), o))) == True{} : Bool}

# P2b(a): a status change to Refunded comes from Paid.
law p2b_a:
  for +s: Spec.State
  for +e: Spec.Ev
  for +o: Nat
  for h: {Spec.inv(s) == True{} : Bool}
  for hn: {Spec.st(s, o) != Spec.Refunded{} : Spec.Status}
  for hs: {Spec.st(Code.fst(Code.step(s, e)), o) == Spec.Refunded{} : Spec.Status}
  {Spec.st(s, o) == Spec.Paid{} : Spec.Status}

# P2b(b): outRefund false->true happens only on a Paid order.
law p2b_b:
  for +s: Spec.State
  for +e: Spec.Ev
  for +o: Nat
  for h: {Spec.inv(s) == True{} : Bool}
  for hn: {Spec.out_refund(Spec.od(s, o)) == False{} : Bool}
  for hs: {Spec.out_refund(Spec.od(Code.fst(Code.step(s, e)), o)) == True{} : Bool}
  {Spec.st(s, o) == Spec.Paid{} : Spec.Status}

# P2b(c): WireRefundReq(o) in fx implies the order is Refunded.
law p2b_c:
  for +s: Spec.State
  for +e: Spec.Ev
  for +o: Nat
  for h: {Spec.inv(s) == True{} : Bool}
  for hw: {Spec.has(Code.snd(Code.step(s, e)), Spec.WireRefundReq{o}) == True{} : Bool}
  {Spec.st(s, o) == Spec.Refunded{} : Spec.Status}

# P2b(d): Refund(o,x) in fx implies the provider record is Approved.
law p2b_d:
  for +s: Spec.State
  for +e: Spec.Ev
  for +o: Nat
  for +x: Nat
  for h: {Spec.inv(s) == True{} : Bool}
  for hw: {Spec.has(Code.snd(Code.step(s, e)), Spec.Refund{o, x}) == True{} : Bool}
  {Spec.rec_of(Spec.pr(s, o)) == Spec.Approved{} : Spec.Res}

# P3: a terminal status (and its amount) never changes (one event).
law p3_step:
  for +s: Spec.State
  for +e: Spec.Ev
  for +o: Nat
  for h: {Spec.inv(s) == True{} : Bool}
  for ht: {Spec.is_terminal(Spec.st(s, o)) == True{} : Bool}
  {(Spec.st(Code.fst(Code.step(s, e)), o), Spec.amount_of(Spec.od(Code.fst(Code.step(s, e)), o))) == (Spec.st(s, o), Spec.amount_of(Spec.od(s, o))) : Spec.Status & Nat}

# P3 over any event list.
law p3_run:
  for events: List<Spec.Ev>
  for +s: Spec.State
  for +o: Nat
  for h: {Spec.inv(s) == True{} : Bool}
  for ht: {Spec.is_terminal(Spec.st(s, o)) == True{} : Bool}
  {(Spec.st(Code.run(events, s), o), Spec.amount_of(Spec.od(Code.run(events, s), o))) == (Spec.st(s, o), Spec.amount_of(Spec.od(s, o))) : Spec.Status & Nat}

# A1: PlaceOrder(o,a), a>0, st=None.
law pin_place_order:
  for +s: Spec.State
  for +o: Nat
  for +a: Nat
  for h: {Spec.inv(s) == True{} : Bool}
  for hu: {Spec.order_up(s) == True{} : Bool}
  for hr: {Nat.is_lt(o, List.length(&2, Spec.Slot, Spec.slots_of(s))) == True{} : Bool}
  for hp: {Nat.is_lt(0n, a) == True{} : Bool}
  for hn: {Spec.st(s, o) == Spec.NoOrder{} : Spec.Status}
  {Code.step(s, Spec.PlaceOrder{o, a}) == (Spec.put_ord(s, o, Spec.OrdRec{Spec.AwaitingPayment{}, a, True{}, Spec.out_refund(Spec.od(s, o))}), Nil{}) : Spec.State & List<Spec.Effect>}

# A2: RetryTimeout with st=AwaitingPayment sets outCharge.
law pin_retry_timeout:
  for +s: Spec.State
  for +o: Nat
  for h: {Spec.inv(s) == True{} : Bool}
  for hu: {Spec.order_up(s) == True{} : Bool}
  for hr: {Nat.is_lt(o, List.length(&2, Spec.Slot, Spec.slots_of(s))) == True{} : Bool}
  for hn: {Spec.st(s, o) == Spec.AwaitingPayment{} : Spec.Status}
  {Code.step(s, Spec.RetryTimeout{o}) == (Spec.put_ord(s, o, Spec.OrdRec{Spec.st(s, o), Spec.amount_of(Spec.od(s, o)), True{}, Spec.out_refund(Spec.od(s, o))}), Nil{}) : Spec.State & List<Spec.Effect>}

# A2 (any other status: F).
law pin_retry_timeout_other:
  for +s: Spec.State
  for +o: Nat
  for h: {Spec.inv(s) == True{} : Bool}
  for hu: {Spec.order_up(s) == True{} : Bool}
  for hr: {Nat.is_lt(o, List.length(&2, Spec.Slot, Spec.slots_of(s))) == True{} : Bool}
  for hn: {Spec.st(s, o) != Spec.AwaitingPayment{} : Spec.Status}
  {Code.step(s, Spec.RetryTimeout{o}) == (s, Nil{}) : Spec.State & List<Spec.Effect>}

# A3: FlushChargeReq with outCharge=true clears it and sends WireChargeReq(o, amount).
law pin_flush_charge_req:
  for +s: Spec.State
  for +o: Nat
  for h: {Spec.inv(s) == True{} : Bool}
  for hu: {Spec.order_up(s) == True{} : Bool}
  for hr: {Nat.is_lt(o, List.length(&2, Spec.Slot, Spec.slots_of(s))) == True{} : Bool}
  for hn: {Spec.out_charge(Spec.od(s, o)) == True{} : Bool}
  {Code.step(s, Spec.FlushChargeReq{o}) == (Spec.put_ord(s, o, Spec.OrdRec{Spec.st(s, o), Spec.amount_of(Spec.od(s, o)), False{}, Spec.out_refund(Spec.od(s, o))}), Spec.WireChargeReq{o, Spec.amount_of(Spec.od(s, o))} <> Nil{}) : Spec.State & List<Spec.Effect>}

# A4: PaymentApproved with st=AwaitingPayment sets Paid.
law pin_payment_approved:
  for +s: Spec.State
  for +o: Nat
  for h: {Spec.inv(s) == True{} : Bool}
  for hu: {Spec.order_up(s) == True{} : Bool}
  for hr: {Nat.is_lt(o, List.length(&2, Spec.Slot, Spec.slots_of(s))) == True{} : Bool}
  for hn: {Spec.st(s, o) == Spec.AwaitingPayment{} : Spec.Status}
  {Code.step(s, Spec.PaymentApproved{o}) == (Spec.put_ord(s, o, Spec.OrdRec{Spec.Paid{}, Spec.amount_of(Spec.od(s, o)), Spec.out_charge(Spec.od(s, o)), Spec.out_refund(Spec.od(s, o))}), Nil{}) : Spec.State & List<Spec.Effect>}

# A4 (any other status: F).
law pin_payment_approved_other:
  for +s: Spec.State
  for +o: Nat
  for h: {Spec.inv(s) == True{} : Bool}
  for hu: {Spec.order_up(s) == True{} : Bool}
  for hr: {Nat.is_lt(o, List.length(&2, Spec.Slot, Spec.slots_of(s))) == True{} : Bool}
  for hn: {Spec.st(s, o) != Spec.AwaitingPayment{} : Spec.Status}
  {Code.step(s, Spec.PaymentApproved{o}) == (s, Nil{}) : Spec.State & List<Spec.Effect>}

# A5: PaymentDeclined with st=AwaitingPayment sets Failed.
law pin_payment_declined:
  for +s: Spec.State
  for +o: Nat
  for h: {Spec.inv(s) == True{} : Bool}
  for hu: {Spec.order_up(s) == True{} : Bool}
  for hr: {Nat.is_lt(o, List.length(&2, Spec.Slot, Spec.slots_of(s))) == True{} : Bool}
  for hn: {Spec.st(s, o) == Spec.AwaitingPayment{} : Spec.Status}
  {Code.step(s, Spec.PaymentDeclined{o}) == (Spec.put_ord(s, o, Spec.OrdRec{Spec.Failed{}, Spec.amount_of(Spec.od(s, o)), Spec.out_charge(Spec.od(s, o)), Spec.out_refund(Spec.od(s, o))}), Nil{}) : Spec.State & List<Spec.Effect>}

# A5 (any other status: F).
law pin_payment_declined_other:
  for +s: Spec.State
  for +o: Nat
  for h: {Spec.inv(s) == True{} : Bool}
  for hu: {Spec.order_up(s) == True{} : Bool}
  for hr: {Nat.is_lt(o, List.length(&2, Spec.Slot, Spec.slots_of(s))) == True{} : Bool}
  for hn: {Spec.st(s, o) != Spec.AwaitingPayment{} : Spec.Status}
  {Code.step(s, Spec.PaymentDeclined{o}) == (s, Nil{}) : Spec.State & List<Spec.Effect>}

# A6: RefundOrder with st=Paid sets Refunded and outRefund.
law pin_refund_order:
  for +s: Spec.State
  for +o: Nat
  for h: {Spec.inv(s) == True{} : Bool}
  for hu: {Spec.order_up(s) == True{} : Bool}
  for hr: {Nat.is_lt(o, List.length(&2, Spec.Slot, Spec.slots_of(s))) == True{} : Bool}
  for hn: {Spec.st(s, o) == Spec.Paid{} : Spec.Status}
  {Code.step(s, Spec.RefundOrder{o}) == (Spec.put_ord(s, o, Spec.OrdRec{Spec.Refunded{}, Spec.amount_of(Spec.od(s, o)), Spec.out_charge(Spec.od(s, o)), True{}}), Nil{}) : Spec.State & List<Spec.Effect>}

# A6 (any other status: F).
law pin_refund_order_other:
  for +s: Spec.State
  for +o: Nat
  for h: {Spec.inv(s) == True{} : Bool}
  for hu: {Spec.order_up(s) == True{} : Bool}
  for hr: {Nat.is_lt(o, List.length(&2, Spec.Slot, Spec.slots_of(s))) == True{} : Bool}
  for hn: {Spec.st(s, o) != Spec.Paid{} : Spec.Status}
  {Code.step(s, Spec.RefundOrder{o}) == (s, Nil{}) : Spec.State & List<Spec.Effect>}

# A7: FlushRefundReq with outRefund=true clears it and sends WireRefundReq(o).
law pin_flush_refund_req:
  for +s: Spec.State
  for +o: Nat
  for h: {Spec.inv(s) == True{} : Bool}
  for hu: {Spec.order_up(s) == True{} : Bool}
  for hr: {Nat.is_lt(o, List.length(&2, Spec.Slot, Spec.slots_of(s))) == True{} : Bool}
  for hn: {Spec.out_refund(Spec.od(s, o)) == True{} : Bool}
  {Code.step(s, Spec.FlushRefundReq{o}) == (Spec.put_ord(s, o, Spec.OrdRec{Spec.st(s, o), Spec.amount_of(Spec.od(s, o)), Spec.out_charge(Spec.od(s, o)), False{}}), Spec.WireRefundReq{o} <> Nil{}) : Spec.State & List<Spec.Effect>}

# A8 (rec=NoRec, d=Approve, a>0): new charge.
law pin_charge_req_recv_approve:
  for +s: Spec.State
  for +o: Nat
  for +a: Nat
  for h: {Spec.inv(s) == True{} : Bool}
  for hu: {Spec.prov_up(s) == True{} : Bool}
  for hr: {Nat.is_lt(o, List.length(&2, Spec.Slot, Spec.slots_of(s))) == True{} : Bool}
  for hp: {Nat.is_lt(0n, a) == True{} : Bool}
  for hn: {Spec.rec_of(Spec.pr(s, o)) == Spec.NoRec{} : Spec.Res}
  {Code.step(s, Spec.ChargeReqRecv{o, a, Spec.Approve{}}) == (Spec.put_prov(s, o, Spec.ProvRec{Spec.Approved{}, 1n+Spec.charge_count(Spec.pr(s, o)), Spec.refund_count(Spec.pr(s, o)), a, True{}}), Spec.Charge{o, a} <> Nil{}) : Spec.State & List<Spec.Effect>}

# A8 (rec=NoRec, d=Decline, a>0): record Declined, no charge.
law pin_charge_req_recv_decline:
  for +s: Spec.State
  for +o: Nat
  for +a: Nat
  for h: {Spec.inv(s) == True{} : Bool}
  for hu: {Spec.prov_up(s) == True{} : Bool}
  for hr: {Nat.is_lt(o, List.length(&2, Spec.Slot, Spec.slots_of(s))) == True{} : Bool}
  for hp: {Nat.is_lt(0n, a) == True{} : Bool}
  for hn: {Spec.rec_of(Spec.pr(s, o)) == Spec.NoRec{} : Spec.Res}
  {Code.step(s, Spec.ChargeReqRecv{o, a, Spec.Decline{}}) == (Spec.put_prov(s, o, Spec.ProvRec{Spec.Declined{}, Spec.charge_count(Spec.pr(s, o)), Spec.refund_count(Spec.pr(s, o)), Spec.amt_of(Spec.pr(s, o)), True{}}), Nil{}) : Spec.State & List<Spec.Effect>}

# A8 (rec=Approved, a>0): replay only, outReply := true, no new charge.
law pin_charge_req_recv_replay_approved:
  for +s: Spec.State
  for +o: Nat
  for +a: Nat
  for +d: Spec.Dec
  for h: {Spec.inv(s) == True{} : Bool}
  for hu: {Spec.prov_up(s) == True{} : Bool}
  for hr: {Nat.is_lt(o, List.length(&2, Spec.Slot, Spec.slots_of(s))) == True{} : Bool}
  for hp: {Nat.is_lt(0n, a) == True{} : Bool}
  for hn: {Spec.rec_of(Spec.pr(s, o)) == Spec.Approved{} : Spec.Res}
  {Code.step(s, Spec.ChargeReqRecv{o, a, d}) == (Spec.put_prov(s, o, Spec.ProvRec{Spec.Approved{}, Spec.charge_count(Spec.pr(s, o)), Spec.refund_count(Spec.pr(s, o)), Spec.amt_of(Spec.pr(s, o)), True{}}), Nil{}) : Spec.State & List<Spec.Effect>}

# A8 (rec=Declined, a>0): replay only, outReply := true, no new charge.
law pin_charge_req_recv_replay_declined:
  for +s: Spec.State
  for +o: Nat
  for +a: Nat
  for +d: Spec.Dec
  for h: {Spec.inv(s) == True{} : Bool}
  for hu: {Spec.prov_up(s) == True{} : Bool}
  for hr: {Nat.is_lt(o, List.length(&2, Spec.Slot, Spec.slots_of(s))) == True{} : Bool}
  for hp: {Nat.is_lt(0n, a) == True{} : Bool}
  for hn: {Spec.rec_of(Spec.pr(s, o)) == Spec.Declined{} : Spec.Res}
  {Code.step(s, Spec.ChargeReqRecv{o, a, d}) == (Spec.put_prov(s, o, Spec.ProvRec{Spec.Declined{}, Spec.charge_count(Spec.pr(s, o)), Spec.refund_count(Spec.pr(s, o)), Spec.amt_of(Spec.pr(s, o)), True{}}), Nil{}) : Spec.State & List<Spec.Effect>}

# A8 (a=0): F.
law pin_charge_req_recv_zero:
  for +s: Spec.State
  for +o: Nat
  for +d: Spec.Dec
  for h: {Spec.inv(s) == True{} : Bool}
  for hu: {Spec.prov_up(s) == True{} : Bool}
  for hr: {Nat.is_lt(o, List.length(&2, Spec.Slot, Spec.slots_of(s))) == True{} : Bool}
  {Code.step(s, Spec.ChargeReqRecv{o, 0n, d}) == (s, Nil{}) : Spec.State & List<Spec.Effect>}

# A9 (outReply=true, rec=Approved): clears outReply and sends WireApproved(o).
law pin_flush_reply_approved:
  for +s: Spec.State
  for +o: Nat
  for h: {Spec.inv(s) == True{} : Bool}
  for hu: {Spec.prov_up(s) == True{} : Bool}
  for hr: {Nat.is_lt(o, List.length(&2, Spec.Slot, Spec.slots_of(s))) == True{} : Bool}
  for hn: {Spec.out_reply(Spec.pr(s, o)) == True{} : Bool}
  for hq: {Spec.rec_of(Spec.pr(s, o)) == Spec.Approved{} : Spec.Res}
  {Code.step(s, Spec.FlushReply{o}) == (Spec.put_prov(s, o, Spec.ProvRec{Spec.Approved{}, Spec.charge_count(Spec.pr(s, o)), Spec.refund_count(Spec.pr(s, o)), Spec.amt_of(Spec.pr(s, o)), False{}}), Spec.WireApproved{o} <> Nil{}) : Spec.State & List<Spec.Effect>}

# A9 (outReply=true, rec=Declined): clears outReply and sends WireDeclined(o).
law pin_flush_reply_declined:
  for +s: Spec.State
  for +o: Nat
  for h: {Spec.inv(s) == True{} : Bool}
  for hu: {Spec.prov_up(s) == True{} : Bool}
  for hr: {Nat.is_lt(o, List.length(&2, Spec.Slot, Spec.slots_of(s))) == True{} : Bool}
  for hn: {Spec.out_reply(Spec.pr(s, o)) == True{} : Bool}
  for hq: {Spec.rec_of(Spec.pr(s, o)) == Spec.Declined{} : Spec.Res}
  {Code.step(s, Spec.FlushReply{o}) == (Spec.put_prov(s, o, Spec.ProvRec{Spec.Declined{}, Spec.charge_count(Spec.pr(s, o)), Spec.refund_count(Spec.pr(s, o)), Spec.amt_of(Spec.pr(s, o)), False{}}), Spec.WireDeclined{o} <> Nil{}) : Spec.State & List<Spec.Effect>}

# A10: RefundReqRecv with rec=Approved and refundCount < chargeCount refunds once.
law pin_refund_req_recv:
  for +s: Spec.State
  for +o: Nat
  for h: {Spec.inv(s) == True{} : Bool}
  for hu: {Spec.prov_up(s) == True{} : Bool}
  for hr: {Nat.is_lt(o, List.length(&2, Spec.Slot, Spec.slots_of(s))) == True{} : Bool}
  for hn: {Spec.rec_of(Spec.pr(s, o)) == Spec.Approved{} : Spec.Res}
  for hl: {Nat.is_lt(Spec.refund_count(Spec.pr(s, o)), Spec.charge_count(Spec.pr(s, o))) == True{} : Bool}
  {Code.step(s, Spec.RefundReqRecv{o}) == (Spec.put_prov(s, o, Spec.ProvRec{Spec.Approved{}, Spec.charge_count(Spec.pr(s, o)), 1n+Spec.refund_count(Spec.pr(s, o)), Spec.amt_of(Spec.pr(s, o)), Spec.out_reply(Spec.pr(s, o))}), Spec.Refund{o, Spec.amt_of(Spec.pr(s, o))} <> Nil{}) : Spec.State & List<Spec.Effect>}

# A10 (otherwise F).
law pin_refund_req_recv_other:
  for +s: Spec.State
  for +o: Nat
  for h: {Spec.inv(s) == True{} : Bool}
  for hu: {Spec.prov_up(s) == True{} : Bool}
  for hr: {Nat.is_lt(o, List.length(&2, Spec.Slot, Spec.slots_of(s))) == True{} : Bool}
  for hn: {Bool.and(Spec.is_approved(Spec.rec_of(Spec.pr(s, o))), Nat.is_lt(Spec.refund_count(Spec.pr(s, o)), Spec.charge_count(Spec.pr(s, o)))) == False{} : Bool}
  {Code.step(s, Spec.RefundReqRecv{o}) == (s, Nil{}) : Spec.State & List<Spec.Effect>}

# A11: Crash(OrderSvc) sets orderUp := False{}; rule D does not apply.
law pin_crash_restart_crash_order:
  for +s: Spec.State
  for h: {Spec.inv(s) == True{} : Bool}
  {Code.step(s, Spec.Crash{Spec.OrderSvc{}}) == (Spec.State{Spec.slots_of(s), False{}, Spec.prov_up(s)}, Nil{}) : Spec.State & List<Spec.Effect>}

# A11: Crash(Provider) sets provUp := False{}; rule D does not apply.
law pin_crash_restart_crash_prov:
  for +s: Spec.State
  for h: {Spec.inv(s) == True{} : Bool}
  {Code.step(s, Spec.Crash{Spec.Provider{}}) == (Spec.State{Spec.slots_of(s), Spec.order_up(s), False{}}, Nil{}) : Spec.State & List<Spec.Effect>}

# A11: Restart(OrderSvc) sets orderUp := True{}; rule D does not apply.
law pin_crash_restart_restart_order:
  for +s: Spec.State
  for h: {Spec.inv(s) == True{} : Bool}
  {Code.step(s, Spec.Restart{Spec.OrderSvc{}}) == (Spec.State{Spec.slots_of(s), True{}, Spec.prov_up(s)}, Nil{}) : Spec.State & List<Spec.Effect>}

# A11: Restart(Provider) sets provUp := True{}; rule D does not apply.
law pin_crash_restart_restart_prov:
  for +s: Spec.State
  for h: {Spec.inv(s) == True{} : Bool}
  {Code.step(s, Spec.Restart{Spec.Provider{}}) == (Spec.State{Spec.slots_of(s), Spec.order_up(s), True{}}, Nil{}) : Spec.State & List<Spec.Effect>}

# A12: st changes only along the four legal arrows.
law pin_legal_transitions:
  for +s: Spec.State
  for +e: Spec.Ev
  for +o: Nat
  for h: {Spec.inv(s) == True{} : Bool}
  {Spec.legal_transition(s, Code.fst(Code.step(s, e)), o) == True{} : Bool}

# A13: rec changes only NoRec->Approved/Declined; counts never decrease.
law pin_prov_rec_stable:
  for +s: Spec.State
  for +e: Spec.Ev
  for +o: Nat
  for h: {Spec.inv(s) == True{} : Bool}
  {Spec.rec_stable(s, Code.fst(Code.step(s, e)), o) == True{} : Bool}

# Rule D: an order-service event while the order service is down gives (s, []).
law pin_rule_d_order_down:
  for +s: Spec.State
  for +e: Spec.Ev
  for h: {Spec.inv(s) == True{} : Bool}
  for he: {Spec.is_order_event(e) == True{} : Bool}
  for hu: {Spec.order_up(s) == False{} : Bool}
  {Code.step(s, e) == (s, Nil{}) : Spec.State & List<Spec.Effect>}

# Rule D: a provider event while the provider is down gives (s, []).
law pin_rule_d_prov_down:
  for +s: Spec.State
  for +e: Spec.Ev
  for h: {Spec.inv(s) == True{} : Bool}
  for he: {Spec.is_prov_event(e) == True{} : Bool}
  for hu: {Spec.prov_up(s) == False{} : Bool}
  {Code.step(s, e) == (s, Nil{}) : Spec.State & List<Spec.Effect>}

# Rule D: a non-Crash/Restart event whose o >= length(slots) gives (s, []).
law pin_rule_d_range:
  for +s: Spec.State
  for +e: Spec.Ev
  for h: {Spec.inv(s) == True{} : Bool}
  for he: {Spec.is_crash_restart(e) == False{} : Bool}
  for hr: {Nat.is_le(List.length(&2, Spec.Slot, Spec.slots_of(s)), Spec.ev_idx(e)) == True{} : Bool}
  {Code.step(s, e) == (s, Nil{}) : Spec.State & List<Spec.Effect>}

# A1 (a = 0 or st != None): F.
law pin_place_order_other:
  for +s: Spec.State
  for +o: Nat
  for +a: Nat
  for h: {Spec.inv(s) == True{} : Bool}
  for hu: {Spec.order_up(s) == True{} : Bool}
  for hr: {Nat.is_lt(o, List.length(&2, Spec.Slot, Spec.slots_of(s))) == True{} : Bool}
  for hn: {Bool.and(Nat.is_lt(0n, a), Spec.is_noorder(Spec.st(s, o))) == False{} : Bool}
  {Code.step(s, Spec.PlaceOrder{o, a}) == (s, Nil{}) : Spec.State & List<Spec.Effect>}

# A3 (outCharge = false): F.
law pin_flush_charge_req_other:
  for +s: Spec.State
  for +o: Nat
  for h: {Spec.inv(s) == True{} : Bool}
  for hu: {Spec.order_up(s) == True{} : Bool}
  for hr: {Nat.is_lt(o, List.length(&2, Spec.Slot, Spec.slots_of(s))) == True{} : Bool}
  for hn: {Spec.out_charge(Spec.od(s, o)) == False{} : Bool}
  {Code.step(s, Spec.FlushChargeReq{o}) == (s, Nil{}) : Spec.State & List<Spec.Effect>}

# A7 (outRefund = false): F.
law pin_flush_refund_req_other:
  for +s: Spec.State
  for +o: Nat
  for h: {Spec.inv(s) == True{} : Bool}
  for hu: {Spec.order_up(s) == True{} : Bool}
  for hr: {Nat.is_lt(o, List.length(&2, Spec.Slot, Spec.slots_of(s))) == True{} : Bool}
  for hn: {Spec.out_refund(Spec.od(s, o)) == False{} : Bool}
  {Code.step(s, Spec.FlushRefundReq{o}) == (s, Nil{}) : Spec.State & List<Spec.Effect>}

# A9 (outReply = false, or rec = NoRec): F.
law pin_flush_reply_other:
  for +s: Spec.State
  for +o: Nat
  for h: {Spec.inv(s) == True{} : Bool}
  for hu: {Spec.prov_up(s) == True{} : Bool}
  for hr: {Nat.is_lt(o, List.length(&2, Spec.Slot, Spec.slots_of(s))) == True{} : Bool}
  for hn: {Bool.and(Spec.out_reply(Spec.pr(s, o)), Bool.not(Spec.is_norec(Spec.rec_of(Spec.pr(s, o))))) == False{} : Bool}
  {Code.step(s, Spec.FlushReply{o}) == (s, Nil{}) : Spec.State & List<Spec.Effect>}

import Base
import ./spec.bend as Spec

# UC1 executable step machinery. Everything the laws read lives in spec.bend.

# ------------------------------------------------------------ order-side steps
def place(od: Spec.OrdRec, a: Nat) -> Spec.OrdRec & List<Spec.Effect>:
  match od a:
    case Spec.OrdRec{Spec.NoOrder{}, am, oc, orf} 1n+pa:
      (Spec.OrdRec{Spec.AwaitingPayment{}, 1n+pa, True{}, orf}, Nil{})
    case _ _:
      (od, Nil{})

def retry(od: Spec.OrdRec) -> Spec.OrdRec & List<Spec.Effect>:
  match od:
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, oc, orf}:
      (Spec.OrdRec{Spec.AwaitingPayment{}, am, True{}, orf}, Nil{})
    case _:
      (od, Nil{})

def flush_charge(od: Spec.OrdRec, k: Nat) -> Spec.OrdRec & List<Spec.Effect>:
  match od:
    case Spec.OrdRec{x, +am, True{}, orf}:
      (Spec.OrdRec{x, am, False{}, orf}, Spec.WireChargeReq{k, am} <> Nil{})
    case _:
      (od, Nil{})

def flush_refund(od: Spec.OrdRec, k: Nat) -> Spec.OrdRec & List<Spec.Effect>:
  match od:
    case Spec.OrdRec{x, am, oc, True{}}:
      (Spec.OrdRec{x, am, oc, False{}}, Spec.WireRefundReq{k} <> Nil{})
    case _:
      (od, Nil{})

def pay_ok(od: Spec.OrdRec) -> Spec.OrdRec & List<Spec.Effect>:
  match od:
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, oc, orf}:
      (Spec.OrdRec{Spec.Paid{}, am, oc, orf}, Nil{})
    case _:
      (od, Nil{})

def pay_no(od: Spec.OrdRec) -> Spec.OrdRec & List<Spec.Effect>:
  match od:
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, oc, orf}:
      (Spec.OrdRec{Spec.Failed{}, am, oc, orf}, Nil{})
    case _:
      (od, Nil{})

def refund_order(od: Spec.OrdRec) -> Spec.OrdRec & List<Spec.Effect>:
  match od:
    case Spec.OrdRec{x, am, oc, orf}:
      (Spec.OrdRec{Spec.Refunded{}, am, oc, True{}}, Nil{})
    case _:
      (od, Nil{})

# ---------------------------------------------------------- provider-side steps
def charge_recv(pv: Spec.ProvRec, k: Nat, +a: Nat, d: Spec.Dec) -> Spec.ProvRec & List<Spec.Effect>:
  match pv a d:
    case _ 0n _:
      (pv, Nil{})
    case Spec.ProvRec{Spec.NoRec{}, cc, rc, am, orr} 1n+pa Spec.Approve{}:
      (Spec.ProvRec{Spec.Approved{}, 1n+cc, rc, 1n+pa, True{}}, Spec.Charge{k, 1n+pa} <> Nil{})
    case Spec.ProvRec{Spec.NoRec{}, cc, rc, am, orr} 1n+pa Spec.Decline{}:
      (Spec.ProvRec{Spec.Declined{}, cc, rc, am, True{}}, Nil{})
    case Spec.ProvRec{Spec.Approved{}, cc, rc, am, orr} 1n+pa _:
      (Spec.ProvRec{Spec.Approved{}, cc, rc, am, True{}}, Nil{})
    case Spec.ProvRec{Spec.Declined{}, cc, rc, am, orr} 1n+pa _:
      (Spec.ProvRec{Spec.Declined{}, cc, rc, am, True{}}, Nil{})

def flush_reply(pv: Spec.ProvRec, k: Nat) -> Spec.ProvRec & List<Spec.Effect>:
  match pv:
    case Spec.ProvRec{Spec.Approved{}, cc, rc, am, True{}}:
      (Spec.ProvRec{Spec.Approved{}, cc, rc, am, False{}}, Spec.WireApproved{k} <> Nil{})
    case Spec.ProvRec{Spec.Declined{}, cc, rc, am, True{}}:
      (Spec.ProvRec{Spec.Declined{}, cc, rc, am, False{}}, Spec.WireDeclined{k} <> Nil{})
    case _:
      (pv, Nil{})

# guard is `refundCount < chargeCount`, passed as a Bool so it can be matched
def refund_pick(pv: Spec.ProvRec, k: Nat, g: Bool) -> Spec.ProvRec & List<Spec.Effect>:
  match pv g:
    case Spec.ProvRec{Spec.Approved{}, cc, rc, +am, orr} True{}:
      (Spec.ProvRec{Spec.Approved{}, cc, 1n+rc, am, orr}, Spec.Refund{k, am} <> Nil{})
    case _ _:
      (pv, Nil{})

def refund_recv(+pv: Spec.ProvRec, k: Nat) -> Spec.ProvRec & List<Spec.Effect>:
  refund_pick(pv, k, Nat.is_lt(Spec.refund_count(pv), Spec.charge_count(pv)))

# ------------------------------------------------------------------ slot, list
def with_ord(r: Spec.OrdRec & List<Spec.Effect>, pv: Spec.ProvRec) -> Spec.Slot & List<Spec.Effect>:
  match r:
    case (od, fx):
      (Spec.Slot{od, pv}, fx)

def with_prov(r: Spec.ProvRec & List<Spec.Effect>, od: Spec.OrdRec) -> Spec.Slot & List<Spec.Effect>:
  match r:
    case (pv, fx):
      (Spec.Slot{od, pv}, fx)

def slot_step(sl: Spec.Slot, k: Nat, e: Spec.Ev) -> Spec.Slot & List<Spec.Effect>:
  match sl e:
    case Spec.Slot{od, pv} Spec.PlaceOrder{_, a}:
      with_ord(place(od, a), pv)
    case Spec.Slot{od, pv} Spec.RetryTimeout{_}:
      with_ord(retry(od), pv)
    case Spec.Slot{od, pv} Spec.FlushChargeReq{_}:
      with_ord(flush_charge(od, k), pv)
    case Spec.Slot{od, pv} Spec.FlushRefundReq{_}:
      with_ord(flush_refund(od, k), pv)
    case Spec.Slot{od, pv} Spec.PaymentApproved{_}:
      with_ord(pay_ok(od), pv)
    case Spec.Slot{od, pv} Spec.PaymentDeclined{_}:
      with_ord(pay_no(od), pv)
    case Spec.Slot{od, pv} Spec.RefundOrder{_}:
      with_ord(refund_order(od), pv)
    case Spec.Slot{od, pv} Spec.ChargeReqRecv{_, a, d}:
      with_prov(charge_recv(pv, k, a, d), od)
    case Spec.Slot{od, pv} Spec.RefundReqRecv{_}:
      with_prov(refund_recv(pv, k), od)
    case Spec.Slot{od, pv} Spec.FlushReply{_}:
      with_prov(flush_reply(pv, k), od)
    case _ _:
      (sl, Nil{})

def cons_slot(x: Spec.Slot, r: +List<Spec.Slot> & List<Spec.Effect>) -> +List<Spec.Slot> & List<Spec.Effect>:
  match r:
    case (t, fx):
      (x <> t, fx)

def cons_tail(r: Spec.Slot & List<Spec.Effect>, t: +List<Spec.Slot>) -> +List<Spec.Slot> & List<Spec.Effect>:
  match r:
    case (x, fx):
      (x <> t, fx)

# Walk to slot o (k is the original index, for effects). Out of range: no change.
def go(slots: +List<Spec.Slot>, o: Nat, k: Nat, e: Spec.Ev) -> +List<Spec.Slot> & List<Spec.Effect>:
  match slots o:
    case Nil{} _:
      (Nil{}, Nil{})
    case h <> t 0n:
      cons_tail(slot_step(h, k, e), t)
    case h <> t 1n+p:
      cons_slot(h, go(t, p, k, e))

def with_state(r: +List<Spec.Slot> & List<Spec.Effect>, ou: Bool, pu: Bool) -> Spec.State & List<Spec.Effect>:
  match r:
    case (sl, fx):
      (Spec.State{sl, ou, pu}, fx)

# rule D for a receiving service: down gives F with no effects
def recv(slots: +List<Spec.Slot>, up: Bool, ou: Bool, pu: Bool, +e: Spec.Ev) -> Spec.State & List<Spec.Effect>:
  match up:
    case False{}:
      (Spec.State{slots, ou, pu}, Nil{})
    case True{}:
      with_state(go(slots, Spec.ev_idx(e), Spec.ev_idx(e), e), ou, pu)

def crash(s: Spec.State, svc: Spec.Svc, v: Bool) -> Spec.State:
  match s svc:
    case Spec.State{sl, ou, pu} Spec.OrderSvc{}:
      Spec.State{sl, v, pu}
    case Spec.State{sl, ou, pu} Spec.Provider{}:
      Spec.State{sl, ou, v}

def step1(sl: +List<Spec.Slot>, +ou: Bool, +pu: Bool, +e: Spec.Ev) -> Spec.State & List<Spec.Effect>:
  match e:
    case Spec.Crash{svc}:
      (crash(Spec.State{sl, ou, pu}, svc, False{}), Nil{})
    case Spec.Restart{svc}:
      (crash(Spec.State{sl, ou, pu}, svc, True{}), Nil{})
    case Spec.ChargeReqRecv{_, _, _}:
      recv(sl, pu, ou, pu, e)
    case Spec.RefundReqRecv{_}:
      recv(sl, pu, ou, pu, e)
    case Spec.FlushReply{_}:
      recv(sl, pu, ou, pu, e)
    case _:
      recv(sl, ou, ou, pu, e)

def step(s: Spec.State, +e: Spec.Ev) -> Spec.State & List<Spec.Effect>:
  match s e:
    case Spec.State{sl, ou, pu} +e1:
      step1(sl, ou, pu, e1)

def fst(p: Spec.State & List<Spec.Effect>) -> Spec.State:
  match p:
    case (a, b):
      a

# events come first: the checker wants the shrinking argument leftmost.
def run(events: List<Spec.Ev>, s: Spec.State) -> Spec.State:
  match events:
    case Nil{}:
      s
    case e <> t:
      run(t, fst(step(s, e)))

# ------------------------------------------- shapes used only by LAWS.bend
def snd(p: Spec.State & List<Spec.Effect>) -> List<Spec.Effect>:
  match p:
    case (a, b):
      b

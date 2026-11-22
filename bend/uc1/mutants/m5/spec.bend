import Base


# UC1 port of properties/UC1.md sections 2 to 4.
# Deviations (all literal-equivalent, see docs/results/uc1-bend.md):
#  - Status constructor `None` is `NoOrder` (Base's Maybe already owns `None`).
#  - Base owns `Event`, so the event type is `Ev`.
#  - rule D's `o < length(slots)` check is the Nil case of `go`, which walks
#    the list once (get, update and range check in one pass).

type Status is Data:
  NoOrder{}
  AwaitingPayment{}
  Paid{}
  Failed{}
  Refunded{}

type Res is Data:
  NoRec{}
  Approved{}
  Declined{}

type Dec is Data:
  Approve{}
  Decline{}

type Svc is Data:
  OrderSvc{}
  Provider{}

type OrdRec is Data:
  OrdRec{status: Status, amount: Nat, outCharge: Bool, outRefund: Bool}

type ProvRec is Data:
  ProvRec{rec: Res, chargeCount: Nat, refundCount: Nat, amt: Nat, outReply: Bool}

type Slot is Data:
  Slot{ord: OrdRec, prov: ProvRec}

type State is Data:
  State{slots: +List<Slot>, orderUp: Bool, provUp: Bool}

type Ev is Data:
  PlaceOrder{o: Nat, a: Nat}
  RetryTimeout{o: Nat}
  FlushChargeReq{o: Nat}
  FlushRefundReq{o: Nat}
  PaymentApproved{o: Nat}
  PaymentDeclined{o: Nat}
  RefundOrder{o: Nat}
  ChargeReqRecv{o: Nat, a: Nat, d: Dec}
  RefundReqRecv{o: Nat}
  FlushReply{o: Nat}
  Crash{svc: Svc}
  Restart{svc: Svc}

type Effect is Data:
  WireChargeReq{o: Nat, a: Nat}
  WireRefundReq{o: Nat}
  WireApproved{o: Nat}
  WireDeclined{o: Nat}
  Charge{o: Nat, a: Nat}
  Refund{o: Nat, a: Nat}

def N() -> Nat:
  2n

# ---------------------------------------------------------------- projections
def slots_of(s: State) -> +List<Slot>:
  match s:
    case State{sl, ou, pu}:
      sl

def order_up(s: State) -> Bool:
  match s:
    case State{sl, ou, pu}:
      ou

def prov_up(s: State) -> Bool:
  match s:
    case State{sl, ou, pu}:
      pu

def ord_of(sl: Slot) -> OrdRec:
  match sl:
    case Slot{od, pv}:
      od

def prov_of(sl: Slot) -> ProvRec:
  match sl:
    case Slot{od, pv}:
      pv

def status_of(od: OrdRec) -> Status:
  match od:
    case OrdRec{x, a, oc, orf}:
      x

def amount_of(od: OrdRec) -> Nat:
  match od:
    case OrdRec{x, a, oc, orf}:
      a

def out_charge(od: OrdRec) -> Bool:
  match od:
    case OrdRec{x, a, oc, orf}:
      oc

def out_refund(od: OrdRec) -> Bool:
  match od:
    case OrdRec{x, a, oc, orf}:
      orf

def rec_of(pv: ProvRec) -> Res:
  match pv:
    case ProvRec{r, cc, rc, am, orr}:
      r

def charge_count(pv: ProvRec) -> Nat:
  match pv:
    case ProvRec{r, cc, rc, am, orr}:
      cc

def refund_count(pv: ProvRec) -> Nat:
  match pv:
    case ProvRec{r, cc, rc, am, orr}:
      rc

def amt_of(pv: ProvRec) -> Nat:
  match pv:
    case ProvRec{r, cc, rc, am, orr}:
      am

def out_reply(pv: ProvRec) -> Bool:
  match pv:
    case ProvRec{r, cc, rc, am, orr}:
      orr

# --------------------------------------------------------------------- helpers
def default_slot() -> Slot:
  Slot{OrdRec{NoOrder{}, 0n, False{}, False{}}, ProvRec{NoRec{}, 0n, 0n, 0n, False{}}}

def get_l(slots: +List<Slot>, o: Nat) -> Slot:
  match slots o:
    case Nil{} _:
      default_slot()
    case h <> t 0n:
      h
    case h <> t 1n+p:
      get_l(t, p)

def get(s: State, o: Nat) -> Slot:
  get_l(slots_of(s), o)

def st(s: State, o: Nat) -> Status:
  status_of(ord_of(get(s, o)))

def pr(s: State, o: Nat) -> ProvRec:
  prov_of(get(s, o))

def od(s: State, o: Nat) -> OrdRec:
  ord_of(get(s, o))

def is_terminal(x: Status) -> Bool:
  match x:
    case Failed{}:
      True{}
    case Refunded{}:
      True{}
    case _:
      False{}

# Replace slot o (no-op when o is out of range). Used by the laws to say what
# the new state is; `step` itself uses `go`.
def set(slots: +List<Slot>, o: Nat, x: Slot) -> +List<Slot>:
  match slots o:
    case Nil{} _:
      Nil{}
    case h <> t 0n:
      x <> t
    case h <> t 1n+p:
      h <> set(t, p, x)

def eff_eq(a: Effect, b: Effect) -> Bool:
  match a b:
    case WireChargeReq{o1, a1} WireChargeReq{o2, a2}:
      Bool.and(Nat.is_eq(o1, o2), Nat.is_eq(a1, a2))
    case WireRefundReq{o1} WireRefundReq{o2}:
      Nat.is_eq(o1, o2)
    case WireApproved{o1} WireApproved{o2}:
      Nat.is_eq(o1, o2)
    case WireDeclined{o1} WireDeclined{o2}:
      Nat.is_eq(o1, o2)
    case Charge{o1, a1} Charge{o2, a2}:
      Bool.and(Nat.is_eq(o1, o2), Nat.is_eq(a1, a2))
    case Refund{o1, a1} Refund{o2, a2}:
      Bool.and(Nat.is_eq(o1, o2), Nat.is_eq(a1, a2))
    case _ _:
      False{}

def has(fx: List<Effect>, +ef: Effect) -> Bool:
  match fx:
    case Nil{}:
      False{}
    case x <> t:
      Bool.or(eff_eq(x, ef), has(t, ef))

def init_slots(n: Nat) -> +List<Slot>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      default_slot() <> init_slots(p)

def init(n: Nat) -> State:
  State{init_slots(n), True{}, True{}}

def ev_idx(e: Ev) -> Nat:
  match e:
    case PlaceOrder{o, a}:
      o
    case RetryTimeout{o}:
      o
    case FlushChargeReq{o}:
      o
    case FlushRefundReq{o}:
      o
    case PaymentApproved{o}:
      o
    case PaymentDeclined{o}:
      o
    case RefundOrder{o}:
      o
    case ChargeReqRecv{o, a, d}:
      o
    case RefundReqRecv{o}:
      o
    case FlushReply{o}:
      o
    case _:
      0n

# -------------------------------------------------------------------- invariant
def imp(a: Bool, b: Bool) -> Bool:
  Bool.or(Bool.not(a), b)

def is_noorder(x: Status) -> Bool:
  match x:
    case NoOrder{}:
      True{}
    case _:
      False{}

def is_refunded(x: Status) -> Bool:
  match x:
    case Refunded{}:
      True{}
    case _:
      False{}

def cc_ok(r: Res, cc: Nat) -> Bool:
  match r:
    case Approved{}:
      Nat.is_eq(cc, 1n)
    case _:
      Nat.is_eq(cc, 0n)

def slot_ok(sl: Slot) -> Bool:
  match sl:
    case Slot{OrdRec{+x, am, oc, orf}, ProvRec{r, +cc, rc, am2, orr}}:
      Bool.and(Bool.and(cc_ok(r, cc), Nat.is_le(rc, cc)), Bool.and(imp(orf, is_refunded(x)), imp(oc, Bool.not(is_noorder(x)))))

def inv_slots(slots: +List<Slot>) -> Bool:
  match slots:
    case Nil{}:
      True{}
    case h <> t:
      Bool.and(slot_ok(h), inv_slots(t))

def inv(s: State) -> Bool:
  inv_slots(slots_of(s))

# s with the order half of slot o replaced (no-op when o is out of range)
def put_ord(+s: State, +o: Nat, x: OrdRec) -> State:
  State{set(slots_of(s), o, Slot{x, pr(s, o)}), order_up(s), prov_up(s)}

# s with the provider half of slot o replaced (no-op when o is out of range)
def put_prov(+s: State, +o: Nat, x: ProvRec) -> State:
  State{set(slots_of(s), o, Slot{od(s, o), x}), order_up(s), prov_up(s)}

def is_approved(r: Res) -> Bool:
  match r:
    case Approved{}:
      True{}
    case _:
      False{}

# A12: st changes only None->AwaitingPayment, AwaitingPayment->Paid,
# AwaitingPayment->Failed, Paid->Refunded (staying put is allowed)
def legal(a: Status, b: Status) -> Bool:
  match a b:
    case NoOrder{} NoOrder{}:
      True{}
    case AwaitingPayment{} AwaitingPayment{}:
      True{}
    case Paid{} Paid{}:
      True{}
    case Failed{} Failed{}:
      True{}
    case Refunded{} Refunded{}:
      True{}
    case NoOrder{} AwaitingPayment{}:
      True{}
    case AwaitingPayment{} Paid{}:
      True{}
    case AwaitingPayment{} Failed{}:
      True{}
    case Paid{} Refunded{}:
      True{}
    case _ _:
      False{}

def legal_transition(+s: State, +s2: State, +o: Nat) -> Bool:
  legal(st(s, o), st(s2, o))

# A13: rec changes only NoRec->Approved or NoRec->Declined; counts never decrease
def rec_ok(a: Res, b: Res) -> Bool:
  match a b:
    case NoRec{} NoRec{}:
      True{}
    case Approved{} Approved{}:
      True{}
    case Declined{} Declined{}:
      True{}
    case NoRec{} Approved{}:
      True{}
    case NoRec{} Declined{}:
      True{}
    case _ _:
      False{}

def rec_stable(+s: State, +s2: State, +o: Nat) -> Bool:
  Bool.and(rec_ok(rec_of(pr(s, o)), rec_of(pr(s2, o))), Bool.and(Nat.is_le(charge_count(pr(s, o)), charge_count(pr(s2, o))), Nat.is_le(refund_count(pr(s, o)), refund_count(pr(s2, o)))))

# ---------------------------------------- event classes (rule D pins in LAWS.bend)
def is_order_event(e: Ev) -> Bool:
  match e:
    case PlaceOrder{_, _}:
      True{}
    case RetryTimeout{_}:
      True{}
    case FlushChargeReq{_}:
      True{}
    case FlushRefundReq{_}:
      True{}
    case PaymentApproved{_}:
      True{}
    case PaymentDeclined{_}:
      True{}
    case RefundOrder{_}:
      True{}
    case _:
      False{}

def is_prov_event(e: Ev) -> Bool:
  match e:
    case ChargeReqRecv{_, _, _}:
      True{}
    case RefundReqRecv{_}:
      True{}
    case FlushReply{_}:
      True{}
    case _:
      False{}

def is_crash_restart(e: Ev) -> Bool:
  match e:
    case Crash{_}:
      True{}
    case Restart{_}:
      True{}
    case _:
      False{}

def is_norec(r: Res) -> Bool:
  match r:
    case NoRec{}:
      True{}
    case _:
      False{}

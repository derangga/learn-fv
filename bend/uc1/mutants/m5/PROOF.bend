import Base
import ./spec.bend as Spec
import ./code.bend as Code
import ./LAWS.bend as Laws

# ---------------------------------------------------------------- Bool lemmas
def Disc(b: Bool, G: Type) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      G

# False == True is absurd: elimination into any type G.
def ft_absurd(-G: Type, h: {False{} == True{} : Bool}) -> G:
  %h : Disc(_, G)
  Unit{}

def and_l(+a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case False{}:
      ft_absurd({False{} == True{} : Bool}, h)
    case True{}:
      {==}

def and_r(+a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case False{}:
      ft_absurd({b == True{} : Bool}, h)
    case True{}:
      h

def and_i(+a: Bool, +b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case False{}:
      ft_absurd({Bool.and(False{}, b) == True{} : Bool}, ha)
    case True{}:
      hb

# ------------------------------------------------------------------ tiny laws
def Laws.pin_crash_restart_crash_order(s, h):
  match s:
    case Spec.State{sl, ou, pu}:
      {==}

def Laws.pin_crash_restart_crash_prov(s, h):
  match s:
    case Spec.State{sl, ou, pu}:
      {==}

def Laws.pin_crash_restart_restart_order(s, h):
  match s:
    case Spec.State{sl, ou, pu}:
      {==}

def Laws.pin_crash_restart_restart_prov(s, h):
  match s:
    case Spec.State{sl, ou, pu}:
      {==}

def Laws.init_inv():
  {==}

# --------------------------------------------------------------- Nat lemmas
def nle_refl(+n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      nle_refl(p)

# ------------------------------------------------------ inv over slot lists
def inv_get(+l: +List<Spec.Slot>, +q: Nat, hh: {Spec.inv_slots(l) == True{} : Bool}) -> {Spec.slot_ok(Spec.get_l(l, q)) == True{} : Bool}:
  match l q:
    case Nil{} _:
      {==}
    case +h <> +t 0n:
      and_l(Spec.slot_ok(h), Spec.inv_slots(t), hh)
    case +h <> +t 1n+p:
      inv_get(t, p, and_r(Spec.slot_ok(h), Spec.inv_slots(t), hh))

def inv_set(+l: +List<Spec.Slot>, +o: Nat, +x: Spec.Slot, +hh: {Spec.inv_slots(l) == True{} : Bool}, hx: {Spec.slot_ok(x) == True{} : Bool}) -> {Spec.inv_slots(Spec.set(l, o, x)) == True{} : Bool}:
  match l o:
    case Nil{} _:
      {==}
    case +h <> +t 0n:
      and_i(Spec.slot_ok(x), Spec.inv_slots(t), hx, and_r(Spec.slot_ok(h), Spec.inv_slots(t), hh))
    case +h <> +t 1n+p:
      and_i(Spec.slot_ok(h), Spec.inv_slots(Spec.set(t, p, x)), and_l(Spec.slot_ok(h), Spec.inv_slots(t), hh), inv_set(t, p, x, and_r(Spec.slot_ok(h), Spec.inv_slots(t), hh), hx))

# ------------------------------------------------------------- go and set
def fl(r: +List<Spec.Slot> & List<Spec.Effect>) -> +List<Spec.Slot>:
  match r:
    case (a, b):
      a

def fs(r: Spec.Slot & List<Spec.Effect>) -> Spec.Slot:
  match r:
    case (a, b):
      a

def cons_tail_fl(r: Spec.Slot & List<Spec.Effect>, +t: +List<Spec.Slot>) -> {fs(r) <> t == fl(Code.cons_tail(r, t)) : +List<Spec.Slot>}:
  match r:
    case (x, fx):
      {==}

def cons_slot_fl(+x: Spec.Slot, r: +List<Spec.Slot> & List<Spec.Effect>) -> {x <> fl(r) == fl(Code.cons_slot(x, r)) : +List<Spec.Slot>}:
  match r:
    case (t, fx):
      {==}

def go_fst(+l: +List<Spec.Slot>, +o: Nat, +k: Nat, +e: Spec.Ev) -> {Spec.set(l, o, fs(Code.slot_step(Spec.get_l(l, o), k, e))) == fl(Code.go(l, o, k, e)) : +List<Spec.Slot>}:
  match l o:
    case Nil{} _:
      {==}
    case +h <> +t 0n:
      cons_tail_fl(Code.slot_step(h, k, e), t)
    case +h <> +t 1n+p:
      %cons_slot_fl(h, Code.go(t, p, k, e)) : {h <> Spec.set(t, p, fs(Code.slot_step(Spec.get_l(t, p), k, e))) == _ : +List<Spec.Slot>}
      %go_fst(t, p, k, e) : {h <> Spec.set(t, p, fs(Code.slot_step(Spec.get_l(t, p), k, e))) == h <> _ : +List<Spec.Slot>}
      {==}

# ------------------------------------------------------------ inv over step
def fo(r: Spec.OrdRec & List<Spec.Effect>) -> Spec.OrdRec:
  match r:
    case (a, b):
      a

def fp(r: Spec.ProvRec & List<Spec.Effect>) -> Spec.ProvRec:
  match r:
    case (a, b):
      a

# the order half and the provider half of Inv's slot conjunct
def opk(od: Spec.OrdRec) -> Bool:
  match od:
    case Spec.OrdRec{+x, am, oc, orf}:
      Bool.and(Spec.imp(orf, Spec.is_refunded(x)), Spec.imp(oc, Bool.not(Spec.is_noorder(x))))

def ppk(pv: Spec.ProvRec) -> Bool:
  match pv:
    case Spec.ProvRec{r, +cc, rc, am, orr}:
      Bool.and(Spec.cc_ok(r, cc), Nat.is_le(rc, cc))

def sok_split(+od: Spec.OrdRec, +pv: Spec.ProvRec, +hh: {Spec.slot_ok(Spec.Slot{od, pv}) == True{} : Bool}) -> {Bool.and(ppk(pv), opk(od)) == True{} : Bool}:
  match od pv:
    case Spec.OrdRec{+x, am, oc, orf} Spec.ProvRec{r, +cc, rc, am2, orr}:
      hh

def sok_join(+od: Spec.OrdRec, +pv: Spec.ProvRec, +hh: {Bool.and(ppk(pv), opk(od)) == True{} : Bool}) -> {Spec.slot_ok(Spec.Slot{od, pv}) == True{} : Bool}:
  match od pv:
    case Spec.OrdRec{+x, am, oc, orf} Spec.ProvRec{r, +cc, rc, am2, orr}:
      hh

def sp_l(+od: Spec.OrdRec, +pv: Spec.ProvRec, +hh: {Spec.slot_ok(Spec.Slot{od, pv}) == True{} : Bool}) -> {ppk(pv) == True{} : Bool}:
  and_l(ppk(pv), opk(od), sok_split(od, pv, hh))

def sp_r(+od: Spec.OrdRec, +pv: Spec.ProvRec, +hh: {Spec.slot_ok(Spec.Slot{od, pv}) == True{} : Bool}) -> {opk(od) == True{} : Bool}:
  and_r(ppk(pv), opk(od), sok_split(od, pv, hh))

def sok_wo(r: Spec.OrdRec & List<Spec.Effect>, +pv: Spec.ProvRec, +hP: {ppk(pv) == True{} : Bool}, +hO: {opk(fo(r)) == True{} : Bool}) -> {Spec.slot_ok(fs(Code.with_ord(r, pv))) == True{} : Bool}:
  match r:
    case (+od2, fx):
      sok_join(od2, pv, and_i(ppk(pv), opk(od2), hP, hO))

def sok_wp(r: Spec.ProvRec & List<Spec.Effect>, +od: Spec.OrdRec, +hP: {ppk(fp(r)) == True{} : Bool}, +hO: {opk(od) == True{} : Bool}) -> {Spec.slot_ok(fs(Code.with_prov(r, od))) == True{} : Bool}:
  match r:
    case (+pv2, fx):
      sok_join(od, pv2, and_i(ppk(pv2), opk(od), hP, hO))

def nle_zero(+c: Nat) -> {Nat.is_le(0n, c) == True{} : Bool}:
  match c:
    case 0n:
      {==}
    case 1n+p:
      {==}

def lt_le(+r: Nat, +c: Nat, +hg: {Nat.is_lt(r, c) == True{} : Bool}) -> {Nat.is_le(1n+r, c) == True{} : Bool}:
  match r c:
    case 0n 0n:
      ft_absurd({Nat.is_le(1n+0n, 0n) == True{} : Bool}, hg)
    case 0n 1n+c2:
      nle_zero(c2)
    case 1n+r2 0n:
      ft_absurd({Nat.is_le(1n+1n+r2, 0n) == True{} : Bool}, hg)
    case 1n+r2 1n+c2:
      lt_le(r2, c2, hg)

def op_place(+od: Spec.OrdRec, +a: Nat, +ho: {opk(od) == True{} : Bool}) -> {opk(fo(Code.place(od, a))) == True{} : Bool}:
  match od a:
    case Spec.OrdRec{Spec.NoOrder{}, am, True{}, True{}} 0n:
      ft_absurd({opk(fo(Code.place(Spec.OrdRec{Spec.NoOrder{}, am, True{}, True{}}, 0n))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.NoOrder{}, am, True{}, True{}} 1n+pa:
      ft_absurd({opk(fo(Code.place(Spec.OrdRec{Spec.NoOrder{}, am, True{}, True{}}, 1n+pa))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.NoOrder{}, am, True{}, False{}} 0n:
      ft_absurd({opk(fo(Code.place(Spec.OrdRec{Spec.NoOrder{}, am, True{}, False{}}, 0n))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.NoOrder{}, am, True{}, False{}} 1n+pa:
      ft_absurd({opk(fo(Code.place(Spec.OrdRec{Spec.NoOrder{}, am, True{}, False{}}, 1n+pa))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.NoOrder{}, am, False{}, True{}} 0n:
      ft_absurd({opk(fo(Code.place(Spec.OrdRec{Spec.NoOrder{}, am, False{}, True{}}, 0n))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.NoOrder{}, am, False{}, True{}} 1n+pa:
      ft_absurd({opk(fo(Code.place(Spec.OrdRec{Spec.NoOrder{}, am, False{}, True{}}, 1n+pa))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.NoOrder{}, am, False{}, False{}} 0n:
      ho
    case Spec.OrdRec{Spec.NoOrder{}, am, False{}, False{}} 1n+pa:
      {==}
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, True{}, True{}} _:
      ft_absurd({opk(fo(Code.place(Spec.OrdRec{Spec.AwaitingPayment{}, am, True{}, True{}}, 0n))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, True{}, False{}} _:
      ho
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, False{}, True{}} _:
      ft_absurd({opk(fo(Code.place(Spec.OrdRec{Spec.AwaitingPayment{}, am, False{}, True{}}, 0n))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, False{}, False{}} _:
      ho
    case Spec.OrdRec{Spec.Paid{}, am, True{}, True{}} _:
      ft_absurd({opk(fo(Code.place(Spec.OrdRec{Spec.Paid{}, am, True{}, True{}}, 0n))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.Paid{}, am, True{}, False{}} _:
      ho
    case Spec.OrdRec{Spec.Paid{}, am, False{}, True{}} _:
      ft_absurd({opk(fo(Code.place(Spec.OrdRec{Spec.Paid{}, am, False{}, True{}}, 0n))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.Paid{}, am, False{}, False{}} _:
      ho
    case Spec.OrdRec{Spec.Failed{}, am, True{}, True{}} _:
      ft_absurd({opk(fo(Code.place(Spec.OrdRec{Spec.Failed{}, am, True{}, True{}}, 0n))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.Failed{}, am, True{}, False{}} _:
      ho
    case Spec.OrdRec{Spec.Failed{}, am, False{}, True{}} _:
      ft_absurd({opk(fo(Code.place(Spec.OrdRec{Spec.Failed{}, am, False{}, True{}}, 0n))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.Failed{}, am, False{}, False{}} _:
      ho
    case Spec.OrdRec{Spec.Refunded{}, am, True{}, True{}} _:
      ho
    case Spec.OrdRec{Spec.Refunded{}, am, True{}, False{}} _:
      ho
    case Spec.OrdRec{Spec.Refunded{}, am, False{}, True{}} _:
      ho
    case Spec.OrdRec{Spec.Refunded{}, am, False{}, False{}} _:
      ho

def op_retry(+od: Spec.OrdRec, +ho: {opk(od) == True{} : Bool}) -> {opk(fo(Code.retry(od))) == True{} : Bool}:
  match od:
    case Spec.OrdRec{Spec.NoOrder{}, am, True{}, True{}}:
      ft_absurd({opk(fo(Code.retry(Spec.OrdRec{Spec.NoOrder{}, am, True{}, True{}}))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.NoOrder{}, am, True{}, False{}}:
      ft_absurd({opk(fo(Code.retry(Spec.OrdRec{Spec.NoOrder{}, am, True{}, False{}}))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.NoOrder{}, am, False{}, True{}}:
      ft_absurd({opk(fo(Code.retry(Spec.OrdRec{Spec.NoOrder{}, am, False{}, True{}}))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.NoOrder{}, am, False{}, False{}}:
      ho
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, True{}, True{}}:
      ft_absurd({opk(fo(Code.retry(Spec.OrdRec{Spec.AwaitingPayment{}, am, True{}, True{}}))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, True{}, False{}}:
      ho
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, False{}, True{}}:
      ft_absurd({opk(fo(Code.retry(Spec.OrdRec{Spec.AwaitingPayment{}, am, False{}, True{}}))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, False{}, False{}}:
      {==}
    case Spec.OrdRec{Spec.Paid{}, am, True{}, True{}}:
      ft_absurd({opk(fo(Code.retry(Spec.OrdRec{Spec.Paid{}, am, True{}, True{}}))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.Paid{}, am, True{}, False{}}:
      ho
    case Spec.OrdRec{Spec.Paid{}, am, False{}, True{}}:
      ft_absurd({opk(fo(Code.retry(Spec.OrdRec{Spec.Paid{}, am, False{}, True{}}))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.Paid{}, am, False{}, False{}}:
      ho
    case Spec.OrdRec{Spec.Failed{}, am, True{}, True{}}:
      ft_absurd({opk(fo(Code.retry(Spec.OrdRec{Spec.Failed{}, am, True{}, True{}}))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.Failed{}, am, True{}, False{}}:
      ho
    case Spec.OrdRec{Spec.Failed{}, am, False{}, True{}}:
      ft_absurd({opk(fo(Code.retry(Spec.OrdRec{Spec.Failed{}, am, False{}, True{}}))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.Failed{}, am, False{}, False{}}:
      ho
    case Spec.OrdRec{Spec.Refunded{}, am, True{}, True{}}:
      ho
    case Spec.OrdRec{Spec.Refunded{}, am, True{}, False{}}:
      ho
    case Spec.OrdRec{Spec.Refunded{}, am, False{}, True{}}:
      ho
    case Spec.OrdRec{Spec.Refunded{}, am, False{}, False{}}:
      ho

def op_flush_charge(+od: Spec.OrdRec, +k: Nat, +ho: {opk(od) == True{} : Bool}) -> {opk(fo(Code.flush_charge(od, k))) == True{} : Bool}:
  match od:
    case Spec.OrdRec{Spec.NoOrder{}, am, True{}, True{}}:
      ft_absurd({opk(fo(Code.flush_charge(Spec.OrdRec{Spec.NoOrder{}, am, True{}, True{}}, k))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.NoOrder{}, am, True{}, False{}}:
      ft_absurd({opk(fo(Code.flush_charge(Spec.OrdRec{Spec.NoOrder{}, am, True{}, False{}}, k))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.NoOrder{}, am, False{}, True{}}:
      ft_absurd({opk(fo(Code.flush_charge(Spec.OrdRec{Spec.NoOrder{}, am, False{}, True{}}, k))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.NoOrder{}, am, False{}, False{}}:
      ho
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, True{}, True{}}:
      ft_absurd({opk(fo(Code.flush_charge(Spec.OrdRec{Spec.AwaitingPayment{}, am, True{}, True{}}, k))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, True{}, False{}}:
      {==}
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, False{}, True{}}:
      ft_absurd({opk(fo(Code.flush_charge(Spec.OrdRec{Spec.AwaitingPayment{}, am, False{}, True{}}, k))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, False{}, False{}}:
      ho
    case Spec.OrdRec{Spec.Paid{}, am, True{}, True{}}:
      ft_absurd({opk(fo(Code.flush_charge(Spec.OrdRec{Spec.Paid{}, am, True{}, True{}}, k))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.Paid{}, am, True{}, False{}}:
      {==}
    case Spec.OrdRec{Spec.Paid{}, am, False{}, True{}}:
      ft_absurd({opk(fo(Code.flush_charge(Spec.OrdRec{Spec.Paid{}, am, False{}, True{}}, k))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.Paid{}, am, False{}, False{}}:
      ho
    case Spec.OrdRec{Spec.Failed{}, am, True{}, True{}}:
      ft_absurd({opk(fo(Code.flush_charge(Spec.OrdRec{Spec.Failed{}, am, True{}, True{}}, k))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.Failed{}, am, True{}, False{}}:
      {==}
    case Spec.OrdRec{Spec.Failed{}, am, False{}, True{}}:
      ft_absurd({opk(fo(Code.flush_charge(Spec.OrdRec{Spec.Failed{}, am, False{}, True{}}, k))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.Failed{}, am, False{}, False{}}:
      ho
    case Spec.OrdRec{Spec.Refunded{}, am, True{}, True{}}:
      {==}
    case Spec.OrdRec{Spec.Refunded{}, am, True{}, False{}}:
      {==}
    case Spec.OrdRec{Spec.Refunded{}, am, False{}, True{}}:
      ho
    case Spec.OrdRec{Spec.Refunded{}, am, False{}, False{}}:
      ho

def op_flush_refund(+od: Spec.OrdRec, +k: Nat, +ho: {opk(od) == True{} : Bool}) -> {opk(fo(Code.flush_refund(od, k))) == True{} : Bool}:
  match od:
    case Spec.OrdRec{Spec.NoOrder{}, am, True{}, True{}}:
      ft_absurd({opk(fo(Code.flush_refund(Spec.OrdRec{Spec.NoOrder{}, am, True{}, True{}}, k))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.NoOrder{}, am, True{}, False{}}:
      ft_absurd({opk(fo(Code.flush_refund(Spec.OrdRec{Spec.NoOrder{}, am, True{}, False{}}, k))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.NoOrder{}, am, False{}, True{}}:
      ft_absurd({opk(fo(Code.flush_refund(Spec.OrdRec{Spec.NoOrder{}, am, False{}, True{}}, k))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.NoOrder{}, am, False{}, False{}}:
      ho
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, True{}, True{}}:
      ft_absurd({opk(fo(Code.flush_refund(Spec.OrdRec{Spec.AwaitingPayment{}, am, True{}, True{}}, k))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, True{}, False{}}:
      ho
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, False{}, True{}}:
      ft_absurd({opk(fo(Code.flush_refund(Spec.OrdRec{Spec.AwaitingPayment{}, am, False{}, True{}}, k))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, False{}, False{}}:
      ho
    case Spec.OrdRec{Spec.Paid{}, am, True{}, True{}}:
      ft_absurd({opk(fo(Code.flush_refund(Spec.OrdRec{Spec.Paid{}, am, True{}, True{}}, k))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.Paid{}, am, True{}, False{}}:
      ho
    case Spec.OrdRec{Spec.Paid{}, am, False{}, True{}}:
      ft_absurd({opk(fo(Code.flush_refund(Spec.OrdRec{Spec.Paid{}, am, False{}, True{}}, k))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.Paid{}, am, False{}, False{}}:
      ho
    case Spec.OrdRec{Spec.Failed{}, am, True{}, True{}}:
      ft_absurd({opk(fo(Code.flush_refund(Spec.OrdRec{Spec.Failed{}, am, True{}, True{}}, k))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.Failed{}, am, True{}, False{}}:
      ho
    case Spec.OrdRec{Spec.Failed{}, am, False{}, True{}}:
      ft_absurd({opk(fo(Code.flush_refund(Spec.OrdRec{Spec.Failed{}, am, False{}, True{}}, k))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.Failed{}, am, False{}, False{}}:
      ho
    case Spec.OrdRec{Spec.Refunded{}, am, True{}, True{}}:
      {==}
    case Spec.OrdRec{Spec.Refunded{}, am, True{}, False{}}:
      ho
    case Spec.OrdRec{Spec.Refunded{}, am, False{}, True{}}:
      {==}
    case Spec.OrdRec{Spec.Refunded{}, am, False{}, False{}}:
      ho

def op_pay_ok(+od: Spec.OrdRec, +ho: {opk(od) == True{} : Bool}) -> {opk(fo(Code.pay_ok(od))) == True{} : Bool}:
  match od:
    case Spec.OrdRec{Spec.NoOrder{}, am, True{}, True{}}:
      ft_absurd({opk(fo(Code.pay_ok(Spec.OrdRec{Spec.NoOrder{}, am, True{}, True{}}))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.NoOrder{}, am, True{}, False{}}:
      ft_absurd({opk(fo(Code.pay_ok(Spec.OrdRec{Spec.NoOrder{}, am, True{}, False{}}))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.NoOrder{}, am, False{}, True{}}:
      ft_absurd({opk(fo(Code.pay_ok(Spec.OrdRec{Spec.NoOrder{}, am, False{}, True{}}))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.NoOrder{}, am, False{}, False{}}:
      ho
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, True{}, True{}}:
      ft_absurd({opk(fo(Code.pay_ok(Spec.OrdRec{Spec.AwaitingPayment{}, am, True{}, True{}}))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, True{}, False{}}:
      {==}
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, False{}, True{}}:
      ft_absurd({opk(fo(Code.pay_ok(Spec.OrdRec{Spec.AwaitingPayment{}, am, False{}, True{}}))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, False{}, False{}}:
      {==}
    case Spec.OrdRec{Spec.Paid{}, am, True{}, True{}}:
      ft_absurd({opk(fo(Code.pay_ok(Spec.OrdRec{Spec.Paid{}, am, True{}, True{}}))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.Paid{}, am, True{}, False{}}:
      ho
    case Spec.OrdRec{Spec.Paid{}, am, False{}, True{}}:
      ft_absurd({opk(fo(Code.pay_ok(Spec.OrdRec{Spec.Paid{}, am, False{}, True{}}))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.Paid{}, am, False{}, False{}}:
      ho
    case Spec.OrdRec{Spec.Failed{}, am, True{}, True{}}:
      ft_absurd({opk(fo(Code.pay_ok(Spec.OrdRec{Spec.Failed{}, am, True{}, True{}}))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.Failed{}, am, True{}, False{}}:
      ho
    case Spec.OrdRec{Spec.Failed{}, am, False{}, True{}}:
      ft_absurd({opk(fo(Code.pay_ok(Spec.OrdRec{Spec.Failed{}, am, False{}, True{}}))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.Failed{}, am, False{}, False{}}:
      ho
    case Spec.OrdRec{Spec.Refunded{}, am, True{}, True{}}:
      ho
    case Spec.OrdRec{Spec.Refunded{}, am, True{}, False{}}:
      ho
    case Spec.OrdRec{Spec.Refunded{}, am, False{}, True{}}:
      ho
    case Spec.OrdRec{Spec.Refunded{}, am, False{}, False{}}:
      ho

def op_pay_no(+od: Spec.OrdRec, +ho: {opk(od) == True{} : Bool}) -> {opk(fo(Code.pay_no(od))) == True{} : Bool}:
  match od:
    case Spec.OrdRec{Spec.NoOrder{}, am, True{}, True{}}:
      ft_absurd({opk(fo(Code.pay_no(Spec.OrdRec{Spec.NoOrder{}, am, True{}, True{}}))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.NoOrder{}, am, True{}, False{}}:
      ft_absurd({opk(fo(Code.pay_no(Spec.OrdRec{Spec.NoOrder{}, am, True{}, False{}}))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.NoOrder{}, am, False{}, True{}}:
      ft_absurd({opk(fo(Code.pay_no(Spec.OrdRec{Spec.NoOrder{}, am, False{}, True{}}))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.NoOrder{}, am, False{}, False{}}:
      ho
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, True{}, True{}}:
      ft_absurd({opk(fo(Code.pay_no(Spec.OrdRec{Spec.AwaitingPayment{}, am, True{}, True{}}))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, True{}, False{}}:
      {==}
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, False{}, True{}}:
      ft_absurd({opk(fo(Code.pay_no(Spec.OrdRec{Spec.AwaitingPayment{}, am, False{}, True{}}))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, False{}, False{}}:
      {==}
    case Spec.OrdRec{Spec.Paid{}, am, True{}, True{}}:
      ft_absurd({opk(fo(Code.pay_no(Spec.OrdRec{Spec.Paid{}, am, True{}, True{}}))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.Paid{}, am, True{}, False{}}:
      ho
    case Spec.OrdRec{Spec.Paid{}, am, False{}, True{}}:
      ft_absurd({opk(fo(Code.pay_no(Spec.OrdRec{Spec.Paid{}, am, False{}, True{}}))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.Paid{}, am, False{}, False{}}:
      ho
    case Spec.OrdRec{Spec.Failed{}, am, True{}, True{}}:
      ft_absurd({opk(fo(Code.pay_no(Spec.OrdRec{Spec.Failed{}, am, True{}, True{}}))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.Failed{}, am, True{}, False{}}:
      ho
    case Spec.OrdRec{Spec.Failed{}, am, False{}, True{}}:
      ft_absurd({opk(fo(Code.pay_no(Spec.OrdRec{Spec.Failed{}, am, False{}, True{}}))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.Failed{}, am, False{}, False{}}:
      ho
    case Spec.OrdRec{Spec.Refunded{}, am, True{}, True{}}:
      ho
    case Spec.OrdRec{Spec.Refunded{}, am, True{}, False{}}:
      ho
    case Spec.OrdRec{Spec.Refunded{}, am, False{}, True{}}:
      ho
    case Spec.OrdRec{Spec.Refunded{}, am, False{}, False{}}:
      ho

def op_refund_order(+od: Spec.OrdRec, +ho: {opk(od) == True{} : Bool}) -> {opk(fo(Code.refund_order(od))) == True{} : Bool}:
  match od:
    case Spec.OrdRec{Spec.NoOrder{}, am, True{}, True{}}:
      ft_absurd({opk(fo(Code.refund_order(Spec.OrdRec{Spec.NoOrder{}, am, True{}, True{}}))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.NoOrder{}, am, True{}, False{}}:
      ft_absurd({opk(fo(Code.refund_order(Spec.OrdRec{Spec.NoOrder{}, am, True{}, False{}}))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.NoOrder{}, am, False{}, True{}}:
      ft_absurd({opk(fo(Code.refund_order(Spec.OrdRec{Spec.NoOrder{}, am, False{}, True{}}))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.NoOrder{}, am, False{}, False{}}:
      ho
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, True{}, True{}}:
      ft_absurd({opk(fo(Code.refund_order(Spec.OrdRec{Spec.AwaitingPayment{}, am, True{}, True{}}))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, True{}, False{}}:
      ho
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, False{}, True{}}:
      ft_absurd({opk(fo(Code.refund_order(Spec.OrdRec{Spec.AwaitingPayment{}, am, False{}, True{}}))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, False{}, False{}}:
      ho
    case Spec.OrdRec{Spec.Paid{}, am, True{}, True{}}:
      ft_absurd({opk(fo(Code.refund_order(Spec.OrdRec{Spec.Paid{}, am, True{}, True{}}))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.Paid{}, am, True{}, False{}}:
      {==}
    case Spec.OrdRec{Spec.Paid{}, am, False{}, True{}}:
      ft_absurd({opk(fo(Code.refund_order(Spec.OrdRec{Spec.Paid{}, am, False{}, True{}}))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.Paid{}, am, False{}, False{}}:
      {==}
    case Spec.OrdRec{Spec.Failed{}, am, True{}, True{}}:
      ft_absurd({opk(fo(Code.refund_order(Spec.OrdRec{Spec.Failed{}, am, True{}, True{}}))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.Failed{}, am, True{}, False{}}:
      ho
    case Spec.OrdRec{Spec.Failed{}, am, False{}, True{}}:
      ft_absurd({opk(fo(Code.refund_order(Spec.OrdRec{Spec.Failed{}, am, False{}, True{}}))) == True{} : Bool}, ho)
    case Spec.OrdRec{Spec.Failed{}, am, False{}, False{}}:
      ho
    case Spec.OrdRec{Spec.Refunded{}, am, True{}, True{}}:
      ho
    case Spec.OrdRec{Spec.Refunded{}, am, True{}, False{}}:
      ho
    case Spec.OrdRec{Spec.Refunded{}, am, False{}, True{}}:
      ho
    case Spec.OrdRec{Spec.Refunded{}, am, False{}, False{}}:
      ho

def pp_flush_reply(+pv: Spec.ProvRec, +k: Nat, +hp: {ppk(pv) == True{} : Bool}) -> {ppk(fp(Code.flush_reply(pv, k))) == True{} : Bool}:
  match pv:
    case Spec.ProvRec{Spec.NoRec{}, cc, rc, am, orr}:
      hp
    case Spec.ProvRec{Spec.Approved{}, cc, rc, am, True{}}:
      hp
    case Spec.ProvRec{Spec.Approved{}, cc, rc, am, False{}}:
      hp
    case Spec.ProvRec{Spec.Declined{}, cc, rc, am, True{}}:
      hp
    case Spec.ProvRec{Spec.Declined{}, cc, rc, am, False{}}:
      hp

def pp_charge_recv(+pv: Spec.ProvRec, +k: Nat, +a: Nat, +d: Spec.Dec, +hp: {ppk(pv) == True{} : Bool}) -> {ppk(fp(Code.charge_recv(pv, k, a, d))) == True{} : Bool}:
  match pv a d:
    case Spec.ProvRec{Spec.NoRec{}, cc, rc, am, orr} 0n _:
      hp
    case Spec.ProvRec{Spec.NoRec{}, 0n, 0n, am, orr} 1n+pa Spec.Approve{}:
      {==}
    case Spec.ProvRec{Spec.NoRec{}, 0n, 1n+rc2, am, orr} 1n+pa Spec.Approve{}:
      ft_absurd({ppk(fp(Code.charge_recv(Spec.ProvRec{Spec.NoRec{}, 0n, 1n+rc2, am, orr}, k, 1n+pa, Spec.Approve{}))) == True{} : Bool}, hp)
    case Spec.ProvRec{Spec.NoRec{}, 1n+cc2, rc, am, orr} 1n+pa Spec.Approve{}:
      ft_absurd({ppk(fp(Code.charge_recv(Spec.ProvRec{Spec.NoRec{}, 1n+cc2, rc, am, orr}, k, 1n+pa, Spec.Approve{}))) == True{} : Bool}, hp)
    case Spec.ProvRec{Spec.NoRec{}, cc, rc, am, orr} 1n+pa Spec.Decline{}:
      hp
    case Spec.ProvRec{Spec.Approved{}, cc, rc, am, orr} 0n _:
      hp
    case Spec.ProvRec{Spec.Approved{}, cc, rc, am, orr} 1n+pa _:
      hp
    case Spec.ProvRec{Spec.Declined{}, cc, rc, am, orr} 0n _:
      hp
    case Spec.ProvRec{Spec.Declined{}, 0n, 0n, am, orr} 1n+pa Spec.Approve{}:
      {==}
    case Spec.ProvRec{Spec.Declined{}, 0n, 1n+rc2, am, orr} 1n+pa Spec.Approve{}:
      ft_absurd({ppk(fp(Code.charge_recv(Spec.ProvRec{Spec.Declined{}, 0n, 1n+rc2, am, orr}, k, 1n+pa, Spec.Approve{}))) == True{} : Bool}, hp)
    case Spec.ProvRec{Spec.Declined{}, 1n+cc2, rc, am, orr} 1n+pa Spec.Approve{}:
      ft_absurd({ppk(fp(Code.charge_recv(Spec.ProvRec{Spec.Declined{}, 1n+cc2, rc, am, orr}, k, 1n+pa, Spec.Approve{}))) == True{} : Bool}, hp)
    case Spec.ProvRec{Spec.Declined{}, cc, rc, am, orr} 1n+pa Spec.Decline{}:
      hp

def pp_rp(+pv: Spec.ProvRec, +k: Nat, +g: Bool, +hg: {Nat.is_lt(Spec.refund_count(pv), Spec.charge_count(pv)) == g : Bool}, +hp: {ppk(pv) == True{} : Bool}) -> {ppk(fp(Code.refund_pick(pv, k, g))) == True{} : Bool}:
  match pv g:
    case Spec.ProvRec{Spec.NoRec{}, cc, rc, am, orr} _:
      hp
    case Spec.ProvRec{Spec.Declined{}, cc, rc, am, orr} _:
      hp
    case Spec.ProvRec{Spec.Approved{}, cc, rc, am, orr} False{}:
      hp
    case Spec.ProvRec{Spec.Approved{}, cc, rc, am, orr} True{}:
      and_i(Spec.cc_ok(Spec.Approved{}, cc), Nat.is_le(1n+rc, cc), and_l(Spec.cc_ok(Spec.Approved{}, cc), Nat.is_le(rc, cc), hp), lt_le(rc, cc, hg))

def sok_step(+sl: Spec.Slot, +k: Nat, +e: Spec.Ev, +hh: {Spec.slot_ok(sl) == True{} : Bool}) -> {Spec.slot_ok(fs(Code.slot_step(sl, k, e))) == True{} : Bool}:
  match sl e:
    case Spec.Slot{od, pv} Spec.PlaceOrder{_, a}:
      sok_wo(Code.place(od, a), pv, sp_l(od, pv, hh), op_place(od, a, sp_r(od, pv, hh)))
    case Spec.Slot{od, pv} Spec.RetryTimeout{_}:
      sok_wo(Code.retry(od), pv, sp_l(od, pv, hh), op_retry(od, sp_r(od, pv, hh)))
    case Spec.Slot{od, pv} Spec.FlushChargeReq{_}:
      sok_wo(Code.flush_charge(od, k), pv, sp_l(od, pv, hh), op_flush_charge(od, k, sp_r(od, pv, hh)))
    case Spec.Slot{od, pv} Spec.FlushRefundReq{_}:
      sok_wo(Code.flush_refund(od, k), pv, sp_l(od, pv, hh), op_flush_refund(od, k, sp_r(od, pv, hh)))
    case Spec.Slot{od, pv} Spec.PaymentApproved{_}:
      sok_wo(Code.pay_ok(od), pv, sp_l(od, pv, hh), op_pay_ok(od, sp_r(od, pv, hh)))
    case Spec.Slot{od, pv} Spec.PaymentDeclined{_}:
      sok_wo(Code.pay_no(od), pv, sp_l(od, pv, hh), op_pay_no(od, sp_r(od, pv, hh)))
    case Spec.Slot{od, pv} Spec.RefundOrder{_}:
      sok_wo(Code.refund_order(od), pv, sp_l(od, pv, hh), op_refund_order(od, sp_r(od, pv, hh)))
    case Spec.Slot{od, pv} Spec.ChargeReqRecv{_, a, d}:
      sok_wp(Code.charge_recv(pv, k, a, d), od, pp_charge_recv(pv, k, a, d, sp_l(od, pv, hh)), sp_r(od, pv, hh))
    case Spec.Slot{od, pv} Spec.RefundReqRecv{_}:
      sok_wp(Code.refund_recv(pv, k), od, pp_rp(pv, k, Nat.is_lt(Spec.refund_count(pv), Spec.charge_count(pv)), {==}, sp_l(od, pv, hh)), sp_r(od, pv, hh))
    case Spec.Slot{od, pv} Spec.FlushReply{_}:
      sok_wp(Code.flush_reply(pv, k), od, pp_flush_reply(pv, k, sp_l(od, pv, hh)), sp_r(od, pv, hh))
    case Spec.Slot{od, pv} Spec.Crash{_}:
      hh
    case Spec.Slot{od, pv} Spec.Restart{_}:
      hh

def ws_inv(r: +List<Spec.Slot> & List<Spec.Effect>, ou: Bool, pu: Bool, hh: {Spec.inv_slots(fl(r)) == True{} : Bool}) -> {Spec.inv(Code.fst(Code.with_state(r, ou, pu))) == True{} : Bool}:
  match r:
    case (sl, fx):
      hh

def inv_go(+l: +List<Spec.Slot>, +o: Nat, +k: Nat, +e: Spec.Ev, +hh: {Spec.inv_slots(l) == True{} : Bool}) -> {Spec.inv_slots(fl(Code.go(l, o, k, e))) == True{} : Bool}:
  %go_fst(l, o, k, e) : {Spec.inv_slots(_) == True{} : Bool}
  inv_set(l, o, fs(Code.slot_step(Spec.get_l(l, o), k, e)), hh, sok_step(Spec.get_l(l, o), k, e, inv_get(l, o, hh)))

def inv_recv(+sl: +List<Spec.Slot>, up: Bool, +ou: Bool, +pu: Bool, +e: Spec.Ev, +hh: {Spec.inv_slots(sl) == True{} : Bool}) -> {Spec.inv(Code.fst(Code.recv(sl, up, ou, pu, e))) == True{} : Bool}:
  match up:
    case False{}:
      hh
    case True{}:
      ws_inv(Code.go(sl, Spec.ev_idx(e), Spec.ev_idx(e), e), ou, pu, inv_go(sl, Spec.ev_idx(e), Spec.ev_idx(e), e, hh))

def Laws.inv_step(s, e, h):
  match s:
    case Spec.State{sl, ou, pu}:
      match e:
        case Spec.PlaceOrder{o, a}:
          inv_recv(sl, ou, ou, pu, e, h)
        case Spec.RetryTimeout{o}:
          inv_recv(sl, ou, ou, pu, e, h)
        case Spec.FlushChargeReq{o}:
          inv_recv(sl, ou, ou, pu, e, h)
        case Spec.FlushRefundReq{o}:
          inv_recv(sl, ou, ou, pu, e, h)
        case Spec.PaymentApproved{o}:
          inv_recv(sl, ou, ou, pu, e, h)
        case Spec.PaymentDeclined{o}:
          inv_recv(sl, ou, ou, pu, e, h)
        case Spec.RefundOrder{o}:
          inv_recv(sl, ou, ou, pu, e, h)
        case Spec.ChargeReqRecv{o, a, d}:
          inv_recv(sl, pu, ou, pu, e, h)
        case Spec.RefundReqRecv{o}:
          inv_recv(sl, pu, ou, pu, e, h)
        case Spec.FlushReply{o}:
          inv_recv(sl, pu, ou, pu, e, h)
        case Spec.Crash{svc}:
          match svc:
            case Spec.OrderSvc{}:
              h
            case Spec.Provider{}:
              h
        case Spec.Restart{svc}:
          match svc:
            case Spec.OrderSvc{}:
              h
            case Spec.Provider{}:
              h

def Laws.inv_run(events, s, h):
  match events:
    case Nil{}:
      h
    case +e <> t:
      Laws.inv_run(t, Code.fst(Code.step(s, e)), Laws.inv_step(s, e, h))

# ------------------------------------------------------------------ P1, P2a
def p1_pv(+pv: Spec.ProvRec, +hp: {ppk(pv) == True{} : Bool}) -> {Nat.is_le(Spec.charge_count(pv), 1n) == True{} : Bool}:
  match pv:
    case Spec.ProvRec{Spec.NoRec{}, 0n, rc, am, orr}:
      {==}
    case Spec.ProvRec{Spec.NoRec{}, 1n+c, rc, am, orr}:
      ft_absurd({Nat.is_le(Spec.charge_count(Spec.ProvRec{Spec.NoRec{}, 1n+c, rc, am, orr}), 1n) == True{} : Bool}, hp)
    case Spec.ProvRec{Spec.Declined{}, 0n, rc, am, orr}:
      {==}
    case Spec.ProvRec{Spec.Declined{}, 1n+c, rc, am, orr}:
      ft_absurd({Nat.is_le(Spec.charge_count(Spec.ProvRec{Spec.Declined{}, 1n+c, rc, am, orr}), 1n) == True{} : Bool}, hp)
    case Spec.ProvRec{Spec.Approved{}, 0n, rc, am, orr}:
      ft_absurd({Nat.is_le(Spec.charge_count(Spec.ProvRec{Spec.Approved{}, 0n, rc, am, orr}), 1n) == True{} : Bool}, hp)
    case Spec.ProvRec{Spec.Approved{}, 1n+0n, rc, am, orr}:
      {==}
    case Spec.ProvRec{Spec.Approved{}, 1n+1n+c, rc, am, orr}:
      ft_absurd({Nat.is_le(Spec.charge_count(Spec.ProvRec{Spec.Approved{}, 1n+1n+c, rc, am, orr}), 1n) == True{} : Bool}, hp)

def p2a_pv(+pv: Spec.ProvRec, +hp: {ppk(pv) == True{} : Bool}) -> {Nat.is_le(Spec.refund_count(pv), Spec.charge_count(pv)) == True{} : Bool}:
  match pv:
    case Spec.ProvRec{r, +cc, rc, am, orr}:
      and_r(Spec.cc_ok(r, cc), Nat.is_le(rc, cc), hp)

def p1_slot(+sl: Spec.Slot, +hh: {Spec.slot_ok(sl) == True{} : Bool}) -> {Nat.is_le(Spec.charge_count(Spec.prov_of(sl)), 1n) == True{} : Bool}:
  match sl:
    case Spec.Slot{od, pv}:
      p1_pv(pv, sp_l(od, pv, hh))

def p2a_slot(+sl: Spec.Slot, +hh: {Spec.slot_ok(sl) == True{} : Bool}) -> {Nat.is_le(Spec.refund_count(Spec.prov_of(sl)), Spec.charge_count(Spec.prov_of(sl))) == True{} : Bool}:
  match sl:
    case Spec.Slot{od, pv}:
      p2a_pv(pv, sp_l(od, pv, hh))

def p1_state(+s: Spec.State, +q: Nat, +hh: {Spec.inv(s) == True{} : Bool}) -> {Nat.is_le(Spec.charge_count(Spec.pr(s, q)), 1n) == True{} : Bool}:
  match s:
    case Spec.State{sl, ou, pu}:
      p1_slot(Spec.get_l(sl, q), inv_get(sl, q, hh))

def p2a_state(+s: Spec.State, +q: Nat, +hh: {Spec.inv(s) == True{} : Bool}) -> {Nat.is_le(Spec.refund_count(Spec.pr(s, q)), Spec.charge_count(Spec.pr(s, q))) == True{} : Bool}:
  match s:
    case Spec.State{sl, ou, pu}:
      p2a_slot(Spec.get_l(sl, q), inv_get(sl, q, hh))

def Laws.p1_step(s, e, o, h):
  p1_state(Code.fst(Code.step(s, e)), o, Laws.inv_step(s, e, h))

def Laws.p1_run(events, s, o, h):
  match events:
    case Nil{}:
      p1_state(s, o, h)
    case +e <> t:
      Laws.p1_run(t, Code.fst(Code.step(s, e)), o, Laws.inv_step(s, e, h))

def Laws.p2a_step(s, e, o, h):
  p2a_state(Code.fst(Code.step(s, e)), o, Laws.inv_step(s, e, h))

def Laws.p2a_run(events, s, o, h):
  match events:
    case Nil{}:
      p2a_state(s, o, h)
    case +e <> t:
      Laws.p2a_run(t, Code.fst(Code.step(s, e)), o, Laws.inv_step(s, e, h))

# ---------------------------------------------------- more absurd and equality
def Disc2(b: Bool, G: Type) -> Type:
  match b:
    case False{}:
      G
    case True{}:
      Unit

# True == False is absurd: elimination into any type G.
def tf_absurd(-G: Type, h: {True{} == False{} : Bool}) -> G:
  %h : Disc2(_, G)
  Unit{}

def empty_elim(-G: Type, e: Empty) -> G:
  match e:

def seq(x: Spec.Status, y: Spec.Status) -> Bool:
  match x y:
    case Spec.NoOrder{} Spec.NoOrder{}:
      True{}
    case Spec.AwaitingPayment{} Spec.AwaitingPayment{}:
      True{}
    case Spec.Paid{} Spec.Paid{}:
      True{}
    case Spec.Failed{} Spec.Failed{}:
      True{}
    case Spec.Refunded{} Spec.Refunded{}:
      True{}
    case _ _:
      False{}

def seq_refl(+x: Spec.Status) -> {seq(x, x) == True{} : Bool}:
  match x:
    case Spec.NoOrder{}:
      {==}
    case Spec.AwaitingPayment{}:
      {==}
    case Spec.Paid{}:
      {==}
    case Spec.Failed{}:
      {==}
    case Spec.Refunded{}:
      {==}

def st_true(+x: Spec.Status, +y: Spec.Status, h: {x == y : Spec.Status}) -> {seq(x, y) == True{} : Bool}:
  %h : {seq(x, _) == True{} : Bool}
  seq_refl(x)

def st_ne(+x: Spec.Status, +y: Spec.Status, hne: {x != y : Spec.Status}) -> {seq(x, y) == False{} : Bool}:
  match x y:
    case Spec.NoOrder{} Spec.NoOrder{}:
      empty_elim({seq(Spec.NoOrder{}, Spec.NoOrder{}) == False{} : Bool}, hne({==}))
    case Spec.NoOrder{} Spec.AwaitingPayment{}:
      {==}
    case Spec.NoOrder{} Spec.Paid{}:
      {==}
    case Spec.NoOrder{} Spec.Failed{}:
      {==}
    case Spec.NoOrder{} Spec.Refunded{}:
      {==}
    case Spec.AwaitingPayment{} Spec.NoOrder{}:
      {==}
    case Spec.AwaitingPayment{} Spec.AwaitingPayment{}:
      empty_elim({seq(Spec.AwaitingPayment{}, Spec.AwaitingPayment{}) == False{} : Bool}, hne({==}))
    case Spec.AwaitingPayment{} Spec.Paid{}:
      {==}
    case Spec.AwaitingPayment{} Spec.Failed{}:
      {==}
    case Spec.AwaitingPayment{} Spec.Refunded{}:
      {==}
    case Spec.Paid{} Spec.NoOrder{}:
      {==}
    case Spec.Paid{} Spec.AwaitingPayment{}:
      {==}
    case Spec.Paid{} Spec.Paid{}:
      empty_elim({seq(Spec.Paid{}, Spec.Paid{}) == False{} : Bool}, hne({==}))
    case Spec.Paid{} Spec.Failed{}:
      {==}
    case Spec.Paid{} Spec.Refunded{}:
      {==}
    case Spec.Failed{} Spec.NoOrder{}:
      {==}
    case Spec.Failed{} Spec.AwaitingPayment{}:
      {==}
    case Spec.Failed{} Spec.Paid{}:
      {==}
    case Spec.Failed{} Spec.Failed{}:
      empty_elim({seq(Spec.Failed{}, Spec.Failed{}) == False{} : Bool}, hne({==}))
    case Spec.Failed{} Spec.Refunded{}:
      {==}
    case Spec.Refunded{} Spec.NoOrder{}:
      {==}
    case Spec.Refunded{} Spec.AwaitingPayment{}:
      {==}
    case Spec.Refunded{} Spec.Paid{}:
      {==}
    case Spec.Refunded{} Spec.Failed{}:
      {==}
    case Spec.Refunded{} Spec.Refunded{}:
      empty_elim({seq(Spec.Refunded{}, Spec.Refunded{}) == False{} : Bool}, hne({==}))

def set_get(+l: +List<Spec.Slot>, +o: Nat) -> {Spec.set(l, o, Spec.get_l(l, o)) == l : +List<Spec.Slot>}:
  match l o:
    case Nil{} _:
      {==}
    case +h <> +t 0n:
      {==}
    case +h <> +t 1n+p:
      %set_get(t, p) : {h <> Spec.set(t, p, Spec.get_l(t, p)) == h <> _ : +List<Spec.Slot>}
      {==}

# ------------------------------------------- go as a set of slot_step's result
def mkl(+sl: +List<Spec.Slot>, +o: Nat, r: Spec.Slot & List<Spec.Effect>) -> +List<Spec.Slot> & List<Spec.Effect>:
  match r:
    case (x, fx):
      (Spec.set(sl, o, x), fx)

def cons_tail_mkl(r: Spec.Slot & List<Spec.Effect>, +h: Spec.Slot, +t: +List<Spec.Slot>) -> {mkl(h <> t, 0n, r) == Code.cons_tail(r, t) : +List<Spec.Slot> & List<Spec.Effect>}:
  match r:
    case (x, fx):
      {==}

def cons_slot_mkl(r: Spec.Slot & List<Spec.Effect>, +h: Spec.Slot, +t: +List<Spec.Slot>, +p: Nat) -> {mkl(h <> t, 1n+p, r) == Code.cons_slot(h, mkl(t, p, r)) : +List<Spec.Slot> & List<Spec.Effect>}:
  match r:
    case (x, fx):
      {==}

def go_eq(+sl: +List<Spec.Slot>, +o: Nat, +k: Nat, +e: Spec.Ev, +hr: {Nat.is_lt(o, List.length(&2, Spec.Slot, sl)) == True{} : Bool}) -> {mkl(sl, o, Code.slot_step(Spec.get_l(sl, o), k, e)) == Code.go(sl, o, k, e) : +List<Spec.Slot> & List<Spec.Effect>}:
  match sl o:
    case Nil{} 0n:
      ft_absurd({mkl(Nil{}, 0n, Code.slot_step(Spec.get_l(Nil{}, 0n), k, e)) == Code.go(Nil{}, 0n, k, e) : +List<Spec.Slot> & List<Spec.Effect>}, hr)
    case Nil{} 1n+p:
      ft_absurd({mkl(Nil{}, 1n+p, Code.slot_step(Spec.get_l(Nil{}, 1n+p), k, e)) == Code.go(Nil{}, 1n+p, k, e) : +List<Spec.Slot> & List<Spec.Effect>}, hr)
    case +h <> +t 0n:
      cons_tail_mkl(Code.slot_step(h, k, e), h, t)
    case +h <> +t 1n+p:
      %go_eq(t, p, k, e, hr) : {mkl(h <> t, 1n+p, Code.slot_step(Spec.get_l(t, p), k, e)) == Code.cons_slot(h, _) : +List<Spec.Slot> & List<Spec.Effect>}
      cons_slot_mkl(Code.slot_step(Spec.get_l(t, p), k, e), h, t, p)

def pin_gen(+sl: +List<Spec.Slot>, +ou: Bool, +pu: Bool, +o: Nat, +e: Spec.Ev, xn: Spec.Slot, fx: List<Spec.Effect>, +hr: {Nat.is_lt(o, List.length(&2, Spec.Slot, sl)) == True{} : Bool}, +hss: {(xn, fx) == Code.slot_step(Spec.get_l(sl, o), o, e) : Spec.Slot & List<Spec.Effect>}) -> {Code.with_state(Code.go(sl, o, o, e), ou, pu) == (Spec.State{Spec.set(sl, o, xn), ou, pu}, fx) : Spec.State & List<Spec.Effect>}:
  %go_eq(sl, o, o, e, hr) : {Code.with_state(_, ou, pu) == (Spec.State{Spec.set(sl, o, xn), ou, pu}, fx) : Spec.State & List<Spec.Effect>}
  %hss : {Code.with_state(mkl(sl, o, _), ou, pu) == (Spec.State{Spec.set(sl, o, xn), ou, pu}, fx) : Spec.State & List<Spec.Effect>}
  {==}

def pin_full(+sl: +List<Spec.Slot>, up: Bool, +ou: Bool, +pu: Bool, +e: Spec.Ev, xn: Spec.Slot, fx: List<Spec.Effect>, +hu: {up == True{} : Bool}, +hr: {Nat.is_lt(Spec.ev_idx(e), List.length(&2, Spec.Slot, sl)) == True{} : Bool}, +hss: {(xn, fx) == Code.slot_step(Spec.get_l(sl, Spec.ev_idx(e)), Spec.ev_idx(e), e) : Spec.Slot & List<Spec.Effect>}) -> {Code.recv(sl, up, ou, pu, e) == (Spec.State{Spec.set(sl, Spec.ev_idx(e), xn), ou, pu}, fx) : Spec.State & List<Spec.Effect>}:
  match up:
    case False{}:
      ft_absurd({Code.recv(sl, False{}, ou, pu, e) == (Spec.State{Spec.set(sl, Spec.ev_idx(e), xn), ou, pu}, fx) : Spec.State & List<Spec.Effect>}, hu)
    case True{}:
      pin_gen(sl, ou, pu, Spec.ev_idx(e), e, xn, fx, hr, hss)

def pin_same(+sl: +List<Spec.Slot>, up: Bool, +ou: Bool, +pu: Bool, +e: Spec.Ev, +hu: {up == True{} : Bool}, +hr: {Nat.is_lt(Spec.ev_idx(e), List.length(&2, Spec.Slot, sl)) == True{} : Bool}, +hss: {(Spec.get_l(sl, Spec.ev_idx(e)), Nil{}) == Code.slot_step(Spec.get_l(sl, Spec.ev_idx(e)), Spec.ev_idx(e), e) : Spec.Slot & List<Spec.Effect>}) -> {Code.recv(sl, up, ou, pu, e) == (Spec.State{sl, ou, pu}, Nil{}) : Spec.State & List<Spec.Effect>}:
  %set_get(sl, Spec.ev_idx(e)) : {Code.recv(sl, up, ou, pu, e) == (Spec.State{_, ou, pu}, Nil{}) : Spec.State & List<Spec.Effect>}
  pin_full(sl, up, ou, pu, e, Spec.get_l(sl, Spec.ev_idx(e)), Nil{}, hu, hr, hss)

# ---------------------------------------------------------------- A2 trial
def ps_retry(+sl0: Spec.Slot, +o: Nat, +hn: {seq(Spec.status_of(Spec.ord_of(sl0)), Spec.AwaitingPayment{}) == True{} : Bool}) -> {(Spec.Slot{Spec.OrdRec{Spec.status_of(Spec.ord_of(sl0)), Spec.amount_of(Spec.ord_of(sl0)), True{}, Spec.out_refund(Spec.ord_of(sl0))}, Spec.prov_of(sl0)}, Nil{}) == Code.slot_step(sl0, o, Spec.RetryTimeout{o}) : Spec.Slot & List<Spec.Effect>}:
  match sl0:
    case Spec.Slot{Spec.OrdRec{Spec.NoOrder{}, am, oc, orf}, pv}:
      ft_absurd({(Spec.Slot{Spec.OrdRec{Spec.status_of(Spec.ord_of(sl0)), Spec.amount_of(Spec.ord_of(sl0)), True{}, Spec.out_refund(Spec.ord_of(sl0))}, Spec.prov_of(sl0)}, Nil{}) == Code.slot_step(sl0, o, Spec.RetryTimeout{o}) : Spec.Slot & List<Spec.Effect>}, hn)
    case Spec.Slot{Spec.OrdRec{Spec.AwaitingPayment{}, am, oc, orf}, pv}:
      {==}
    case Spec.Slot{Spec.OrdRec{Spec.Paid{}, am, oc, orf}, pv}:
      ft_absurd({(Spec.Slot{Spec.OrdRec{Spec.status_of(Spec.ord_of(sl0)), Spec.amount_of(Spec.ord_of(sl0)), True{}, Spec.out_refund(Spec.ord_of(sl0))}, Spec.prov_of(sl0)}, Nil{}) == Code.slot_step(sl0, o, Spec.RetryTimeout{o}) : Spec.Slot & List<Spec.Effect>}, hn)
    case Spec.Slot{Spec.OrdRec{Spec.Failed{}, am, oc, orf}, pv}:
      ft_absurd({(Spec.Slot{Spec.OrdRec{Spec.status_of(Spec.ord_of(sl0)), Spec.amount_of(Spec.ord_of(sl0)), True{}, Spec.out_refund(Spec.ord_of(sl0))}, Spec.prov_of(sl0)}, Nil{}) == Code.slot_step(sl0, o, Spec.RetryTimeout{o}) : Spec.Slot & List<Spec.Effect>}, hn)
    case Spec.Slot{Spec.OrdRec{Spec.Refunded{}, am, oc, orf}, pv}:
      ft_absurd({(Spec.Slot{Spec.OrdRec{Spec.status_of(Spec.ord_of(sl0)), Spec.amount_of(Spec.ord_of(sl0)), True{}, Spec.out_refund(Spec.ord_of(sl0))}, Spec.prov_of(sl0)}, Nil{}) == Code.slot_step(sl0, o, Spec.RetryTimeout{o}) : Spec.Slot & List<Spec.Effect>}, hn)

def Laws.pin_retry_timeout(s, o, h, hu, hr, hn):
  match s:
    case Spec.State{sl, ou, pu}:
      pin_full(sl, ou, ou, pu, Spec.RetryTimeout{o}, Spec.Slot{Spec.OrdRec{Spec.status_of(Spec.ord_of(Spec.get_l(sl, o))), Spec.amount_of(Spec.ord_of(Spec.get_l(sl, o))), True{}, Spec.out_refund(Spec.ord_of(Spec.get_l(sl, o)))}, Spec.prov_of(Spec.get_l(sl, o))}, Nil{}, hu, hr, ps_retry(Spec.get_l(sl, o), o, st_true(Spec.st(s, o), Spec.AwaitingPayment{}, hn)))

# ----------------------------------------------------------- generated pins
def rseq(x: Spec.Res, y: Spec.Res) -> Bool:
  match x y:
    case Spec.NoRec{} Spec.NoRec{}:
      True{}
    case Spec.NoRec{} Spec.Approved{}:
      False{}
    case Spec.NoRec{} Spec.Declined{}:
      False{}
    case Spec.Approved{} Spec.NoRec{}:
      False{}
    case Spec.Approved{} Spec.Approved{}:
      True{}
    case Spec.Approved{} Spec.Declined{}:
      False{}
    case Spec.Declined{} Spec.NoRec{}:
      False{}
    case Spec.Declined{} Spec.Approved{}:
      False{}
    case Spec.Declined{} Spec.Declined{}:
      True{}

def rseq_refl(+x: Spec.Res) -> {rseq(x, x) == True{} : Bool}:
  match x:
    case Spec.NoRec{}:
      {==}
    case Spec.Approved{}:
      {==}
    case Spec.Declined{}:
      {==}

def rec_true(+x: Spec.Res, +y: Spec.Res, h: {x == y : Spec.Res}) -> {rseq(x, y) == True{} : Bool}:
  %h : {rseq(x, _) == True{} : Bool}
  rseq_refl(x)


def ps_place(+sl0: Spec.Slot, +o: Nat, +a: Nat, +hp: {Nat.is_lt(0n, a) == True{} : Bool}, +hn: {seq(Spec.status_of(Spec.ord_of(sl0)), Spec.NoOrder{}) == True{} : Bool}) -> {(Spec.Slot{Spec.OrdRec{Spec.AwaitingPayment{}, a, True{}, Spec.out_refund(Spec.ord_of(sl0))}, Spec.prov_of(sl0)}, Nil{}) == Code.slot_step(sl0, o, Spec.PlaceOrder{o, a}) : Spec.Slot & List<Spec.Effect>}:
  match sl0 a:
    case Spec.Slot{Spec.OrdRec{Spec.NoOrder{}, am, oc, orf}, pv} 0n:
      ft_absurd({(Spec.Slot{Spec.OrdRec{Spec.AwaitingPayment{}, a, True{}, Spec.out_refund(Spec.ord_of(sl0))}, Spec.prov_of(sl0)}, Nil{}) == Code.slot_step(sl0, o, Spec.PlaceOrder{o, a}) : Spec.Slot & List<Spec.Effect>}, hp)
    case Spec.Slot{Spec.OrdRec{Spec.NoOrder{}, am, oc, orf}, pv} 1n+pa:
      {==}
    case Spec.Slot{Spec.OrdRec{Spec.AwaitingPayment{}, am, oc, orf}, pv} 0n:
      ft_absurd({(Spec.Slot{Spec.OrdRec{Spec.AwaitingPayment{}, a, True{}, Spec.out_refund(Spec.ord_of(sl0))}, Spec.prov_of(sl0)}, Nil{}) == Code.slot_step(sl0, o, Spec.PlaceOrder{o, a}) : Spec.Slot & List<Spec.Effect>}, hp)
    case Spec.Slot{Spec.OrdRec{Spec.AwaitingPayment{}, am, oc, orf}, pv} 1n+pa:
      ft_absurd({(Spec.Slot{Spec.OrdRec{Spec.AwaitingPayment{}, a, True{}, Spec.out_refund(Spec.ord_of(sl0))}, Spec.prov_of(sl0)}, Nil{}) == Code.slot_step(sl0, o, Spec.PlaceOrder{o, a}) : Spec.Slot & List<Spec.Effect>}, hn)
    case Spec.Slot{Spec.OrdRec{Spec.Paid{}, am, oc, orf}, pv} 0n:
      ft_absurd({(Spec.Slot{Spec.OrdRec{Spec.AwaitingPayment{}, a, True{}, Spec.out_refund(Spec.ord_of(sl0))}, Spec.prov_of(sl0)}, Nil{}) == Code.slot_step(sl0, o, Spec.PlaceOrder{o, a}) : Spec.Slot & List<Spec.Effect>}, hp)
    case Spec.Slot{Spec.OrdRec{Spec.Paid{}, am, oc, orf}, pv} 1n+pa:
      ft_absurd({(Spec.Slot{Spec.OrdRec{Spec.AwaitingPayment{}, a, True{}, Spec.out_refund(Spec.ord_of(sl0))}, Spec.prov_of(sl0)}, Nil{}) == Code.slot_step(sl0, o, Spec.PlaceOrder{o, a}) : Spec.Slot & List<Spec.Effect>}, hn)
    case Spec.Slot{Spec.OrdRec{Spec.Failed{}, am, oc, orf}, pv} 0n:
      ft_absurd({(Spec.Slot{Spec.OrdRec{Spec.AwaitingPayment{}, a, True{}, Spec.out_refund(Spec.ord_of(sl0))}, Spec.prov_of(sl0)}, Nil{}) == Code.slot_step(sl0, o, Spec.PlaceOrder{o, a}) : Spec.Slot & List<Spec.Effect>}, hp)
    case Spec.Slot{Spec.OrdRec{Spec.Failed{}, am, oc, orf}, pv} 1n+pa:
      ft_absurd({(Spec.Slot{Spec.OrdRec{Spec.AwaitingPayment{}, a, True{}, Spec.out_refund(Spec.ord_of(sl0))}, Spec.prov_of(sl0)}, Nil{}) == Code.slot_step(sl0, o, Spec.PlaceOrder{o, a}) : Spec.Slot & List<Spec.Effect>}, hn)
    case Spec.Slot{Spec.OrdRec{Spec.Refunded{}, am, oc, orf}, pv} 0n:
      ft_absurd({(Spec.Slot{Spec.OrdRec{Spec.AwaitingPayment{}, a, True{}, Spec.out_refund(Spec.ord_of(sl0))}, Spec.prov_of(sl0)}, Nil{}) == Code.slot_step(sl0, o, Spec.PlaceOrder{o, a}) : Spec.Slot & List<Spec.Effect>}, hp)
    case Spec.Slot{Spec.OrdRec{Spec.Refunded{}, am, oc, orf}, pv} 1n+pa:
      ft_absurd({(Spec.Slot{Spec.OrdRec{Spec.AwaitingPayment{}, a, True{}, Spec.out_refund(Spec.ord_of(sl0))}, Spec.prov_of(sl0)}, Nil{}) == Code.slot_step(sl0, o, Spec.PlaceOrder{o, a}) : Spec.Slot & List<Spec.Effect>}, hn)

def Laws.pin_place_order(s, o, a, h, hu, hr, hp, hn):
  match s:
    case Spec.State{sl, ou, pu}:
      pin_full(sl, ou, ou, pu, Spec.PlaceOrder{o, a}, Spec.Slot{Spec.OrdRec{Spec.AwaitingPayment{}, a, True{}, Spec.out_refund(Spec.ord_of(Spec.get_l(sl, o)))}, Spec.prov_of(Spec.get_l(sl, o))}, Nil{}, hu, hr, ps_place(Spec.get_l(sl, o), o, a, hp, st_true(Spec.st(s, o), Spec.NoOrder{}, hn)))

def ps_place_other(+sl0: Spec.Slot, +o: Nat, +a: Nat, +hn: {Bool.and(Nat.is_lt(0n, a), Spec.is_noorder(Spec.status_of(Spec.ord_of(sl0)))) == False{} : Bool}) -> {(sl0, Nil{}) == Code.slot_step(sl0, o, Spec.PlaceOrder{o, a}) : Spec.Slot & List<Spec.Effect>}:
  match sl0 a:
    case Spec.Slot{Spec.OrdRec{Spec.NoOrder{}, am, oc, orf}, pv} 0n:
      {==}
    case Spec.Slot{Spec.OrdRec{Spec.NoOrder{}, am, oc, orf}, pv} 1n+pa:
      tf_absurd({(sl0, Nil{}) == Code.slot_step(sl0, o, Spec.PlaceOrder{o, a}) : Spec.Slot & List<Spec.Effect>}, hn)
    case Spec.Slot{Spec.OrdRec{Spec.AwaitingPayment{}, am, oc, orf}, pv} 0n:
      {==}
    case Spec.Slot{Spec.OrdRec{Spec.AwaitingPayment{}, am, oc, orf}, pv} 1n+pa:
      {==}
    case Spec.Slot{Spec.OrdRec{Spec.Paid{}, am, oc, orf}, pv} 0n:
      {==}
    case Spec.Slot{Spec.OrdRec{Spec.Paid{}, am, oc, orf}, pv} 1n+pa:
      {==}
    case Spec.Slot{Spec.OrdRec{Spec.Failed{}, am, oc, orf}, pv} 0n:
      {==}
    case Spec.Slot{Spec.OrdRec{Spec.Failed{}, am, oc, orf}, pv} 1n+pa:
      {==}
    case Spec.Slot{Spec.OrdRec{Spec.Refunded{}, am, oc, orf}, pv} 0n:
      {==}
    case Spec.Slot{Spec.OrdRec{Spec.Refunded{}, am, oc, orf}, pv} 1n+pa:
      {==}

def Laws.pin_place_order_other(s, o, a, h, hu, hr, hn):
  match s:
    case Spec.State{sl, ou, pu}:
      pin_same(sl, ou, ou, pu, Spec.PlaceOrder{o, a}, hu, hr, ps_place_other(Spec.get_l(sl, o), o, a, hn))

def ps_retry_other(+sl0: Spec.Slot, +o: Nat, +hn: {seq(Spec.status_of(Spec.ord_of(sl0)), Spec.AwaitingPayment{}) == False{} : Bool}) -> {(sl0, Nil{}) == Code.slot_step(sl0, o, Spec.RetryTimeout{o}) : Spec.Slot & List<Spec.Effect>}:
  match sl0:
    case Spec.Slot{Spec.OrdRec{Spec.NoOrder{}, am, oc, orf}, pv}:
      {==}
    case Spec.Slot{Spec.OrdRec{Spec.AwaitingPayment{}, am, oc, orf}, pv}:
      tf_absurd({(sl0, Nil{}) == Code.slot_step(sl0, o, Spec.RetryTimeout{o}) : Spec.Slot & List<Spec.Effect>}, hn)
    case Spec.Slot{Spec.OrdRec{Spec.Paid{}, am, oc, orf}, pv}:
      {==}
    case Spec.Slot{Spec.OrdRec{Spec.Failed{}, am, oc, orf}, pv}:
      {==}
    case Spec.Slot{Spec.OrdRec{Spec.Refunded{}, am, oc, orf}, pv}:
      {==}

def Laws.pin_retry_timeout_other(s, o, h, hu, hr, hn):
  match s:
    case Spec.State{sl, ou, pu}:
      pin_same(sl, ou, ou, pu, Spec.RetryTimeout{o}, hu, hr, ps_retry_other(Spec.get_l(sl, o), o, st_ne(Spec.st(s, o), Spec.AwaitingPayment{}, hn)))

def ps_flush_charge(+sl0: Spec.Slot, +o: Nat, +hn: {Spec.out_charge(Spec.ord_of(sl0)) == True{} : Bool}) -> {(Spec.Slot{Spec.OrdRec{Spec.status_of(Spec.ord_of(sl0)), Spec.amount_of(Spec.ord_of(sl0)), False{}, Spec.out_refund(Spec.ord_of(sl0))}, Spec.prov_of(sl0)}, Spec.WireChargeReq{o, Spec.amount_of(Spec.ord_of(sl0))} <> Nil{}) == Code.slot_step(sl0, o, Spec.FlushChargeReq{o}) : Spec.Slot & List<Spec.Effect>}:
  match sl0:
    case Spec.Slot{Spec.OrdRec{x, am, True{}, orf}, pv}:
      {==}
    case Spec.Slot{Spec.OrdRec{x, am, False{}, orf}, pv}:
      ft_absurd({(Spec.Slot{Spec.OrdRec{Spec.status_of(Spec.ord_of(sl0)), Spec.amount_of(Spec.ord_of(sl0)), False{}, Spec.out_refund(Spec.ord_of(sl0))}, Spec.prov_of(sl0)}, Spec.WireChargeReq{o, Spec.amount_of(Spec.ord_of(sl0))} <> Nil{}) == Code.slot_step(sl0, o, Spec.FlushChargeReq{o}) : Spec.Slot & List<Spec.Effect>}, hn)

def Laws.pin_flush_charge_req(s, o, h, hu, hr, hn):
  match s:
    case Spec.State{sl, ou, pu}:
      pin_full(sl, ou, ou, pu, Spec.FlushChargeReq{o}, Spec.Slot{Spec.OrdRec{Spec.status_of(Spec.ord_of(Spec.get_l(sl, o))), Spec.amount_of(Spec.ord_of(Spec.get_l(sl, o))), False{}, Spec.out_refund(Spec.ord_of(Spec.get_l(sl, o)))}, Spec.prov_of(Spec.get_l(sl, o))}, Spec.WireChargeReq{o, Spec.amount_of(Spec.ord_of(Spec.get_l(sl, o)))} <> Nil{}, hu, hr, ps_flush_charge(Spec.get_l(sl, o), o, hn))

def ps_flush_charge_other(+sl0: Spec.Slot, +o: Nat, +hn: {Spec.out_charge(Spec.ord_of(sl0)) == False{} : Bool}) -> {(sl0, Nil{}) == Code.slot_step(sl0, o, Spec.FlushChargeReq{o}) : Spec.Slot & List<Spec.Effect>}:
  match sl0:
    case Spec.Slot{Spec.OrdRec{x, am, True{}, orf}, pv}:
      tf_absurd({(sl0, Nil{}) == Code.slot_step(sl0, o, Spec.FlushChargeReq{o}) : Spec.Slot & List<Spec.Effect>}, hn)
    case Spec.Slot{Spec.OrdRec{x, am, False{}, orf}, pv}:
      {==}

def Laws.pin_flush_charge_req_other(s, o, h, hu, hr, hn):
  match s:
    case Spec.State{sl, ou, pu}:
      pin_same(sl, ou, ou, pu, Spec.FlushChargeReq{o}, hu, hr, ps_flush_charge_other(Spec.get_l(sl, o), o, hn))

def ps_pay_ok(+sl0: Spec.Slot, +o: Nat, +hn: {seq(Spec.status_of(Spec.ord_of(sl0)), Spec.AwaitingPayment{}) == True{} : Bool}) -> {(Spec.Slot{Spec.OrdRec{Spec.Paid{}, Spec.amount_of(Spec.ord_of(sl0)), Spec.out_charge(Spec.ord_of(sl0)), Spec.out_refund(Spec.ord_of(sl0))}, Spec.prov_of(sl0)}, Nil{}) == Code.slot_step(sl0, o, Spec.PaymentApproved{o}) : Spec.Slot & List<Spec.Effect>}:
  match sl0:
    case Spec.Slot{Spec.OrdRec{Spec.NoOrder{}, am, oc, orf}, pv}:
      ft_absurd({(Spec.Slot{Spec.OrdRec{Spec.Paid{}, Spec.amount_of(Spec.ord_of(sl0)), Spec.out_charge(Spec.ord_of(sl0)), Spec.out_refund(Spec.ord_of(sl0))}, Spec.prov_of(sl0)}, Nil{}) == Code.slot_step(sl0, o, Spec.PaymentApproved{o}) : Spec.Slot & List<Spec.Effect>}, hn)
    case Spec.Slot{Spec.OrdRec{Spec.AwaitingPayment{}, am, oc, orf}, pv}:
      {==}
    case Spec.Slot{Spec.OrdRec{Spec.Paid{}, am, oc, orf}, pv}:
      ft_absurd({(Spec.Slot{Spec.OrdRec{Spec.Paid{}, Spec.amount_of(Spec.ord_of(sl0)), Spec.out_charge(Spec.ord_of(sl0)), Spec.out_refund(Spec.ord_of(sl0))}, Spec.prov_of(sl0)}, Nil{}) == Code.slot_step(sl0, o, Spec.PaymentApproved{o}) : Spec.Slot & List<Spec.Effect>}, hn)
    case Spec.Slot{Spec.OrdRec{Spec.Failed{}, am, oc, orf}, pv}:
      ft_absurd({(Spec.Slot{Spec.OrdRec{Spec.Paid{}, Spec.amount_of(Spec.ord_of(sl0)), Spec.out_charge(Spec.ord_of(sl0)), Spec.out_refund(Spec.ord_of(sl0))}, Spec.prov_of(sl0)}, Nil{}) == Code.slot_step(sl0, o, Spec.PaymentApproved{o}) : Spec.Slot & List<Spec.Effect>}, hn)
    case Spec.Slot{Spec.OrdRec{Spec.Refunded{}, am, oc, orf}, pv}:
      ft_absurd({(Spec.Slot{Spec.OrdRec{Spec.Paid{}, Spec.amount_of(Spec.ord_of(sl0)), Spec.out_charge(Spec.ord_of(sl0)), Spec.out_refund(Spec.ord_of(sl0))}, Spec.prov_of(sl0)}, Nil{}) == Code.slot_step(sl0, o, Spec.PaymentApproved{o}) : Spec.Slot & List<Spec.Effect>}, hn)

def Laws.pin_payment_approved(s, o, h, hu, hr, hn):
  match s:
    case Spec.State{sl, ou, pu}:
      pin_full(sl, ou, ou, pu, Spec.PaymentApproved{o}, Spec.Slot{Spec.OrdRec{Spec.Paid{}, Spec.amount_of(Spec.ord_of(Spec.get_l(sl, o))), Spec.out_charge(Spec.ord_of(Spec.get_l(sl, o))), Spec.out_refund(Spec.ord_of(Spec.get_l(sl, o)))}, Spec.prov_of(Spec.get_l(sl, o))}, Nil{}, hu, hr, ps_pay_ok(Spec.get_l(sl, o), o, st_true(Spec.st(s, o), Spec.AwaitingPayment{}, hn)))

def ps_pay_ok_other(+sl0: Spec.Slot, +o: Nat, +hn: {seq(Spec.status_of(Spec.ord_of(sl0)), Spec.AwaitingPayment{}) == False{} : Bool}) -> {(sl0, Nil{}) == Code.slot_step(sl0, o, Spec.PaymentApproved{o}) : Spec.Slot & List<Spec.Effect>}:
  match sl0:
    case Spec.Slot{Spec.OrdRec{Spec.NoOrder{}, am, oc, orf}, pv}:
      {==}
    case Spec.Slot{Spec.OrdRec{Spec.AwaitingPayment{}, am, oc, orf}, pv}:
      tf_absurd({(sl0, Nil{}) == Code.slot_step(sl0, o, Spec.PaymentApproved{o}) : Spec.Slot & List<Spec.Effect>}, hn)
    case Spec.Slot{Spec.OrdRec{Spec.Paid{}, am, oc, orf}, pv}:
      {==}
    case Spec.Slot{Spec.OrdRec{Spec.Failed{}, am, oc, orf}, pv}:
      {==}
    case Spec.Slot{Spec.OrdRec{Spec.Refunded{}, am, oc, orf}, pv}:
      {==}

def Laws.pin_payment_approved_other(s, o, h, hu, hr, hn):
  match s:
    case Spec.State{sl, ou, pu}:
      pin_same(sl, ou, ou, pu, Spec.PaymentApproved{o}, hu, hr, ps_pay_ok_other(Spec.get_l(sl, o), o, st_ne(Spec.st(s, o), Spec.AwaitingPayment{}, hn)))

def ps_pay_no(+sl0: Spec.Slot, +o: Nat, +hn: {seq(Spec.status_of(Spec.ord_of(sl0)), Spec.AwaitingPayment{}) == True{} : Bool}) -> {(Spec.Slot{Spec.OrdRec{Spec.Failed{}, Spec.amount_of(Spec.ord_of(sl0)), Spec.out_charge(Spec.ord_of(sl0)), Spec.out_refund(Spec.ord_of(sl0))}, Spec.prov_of(sl0)}, Nil{}) == Code.slot_step(sl0, o, Spec.PaymentDeclined{o}) : Spec.Slot & List<Spec.Effect>}:
  match sl0:
    case Spec.Slot{Spec.OrdRec{Spec.NoOrder{}, am, oc, orf}, pv}:
      ft_absurd({(Spec.Slot{Spec.OrdRec{Spec.Failed{}, Spec.amount_of(Spec.ord_of(sl0)), Spec.out_charge(Spec.ord_of(sl0)), Spec.out_refund(Spec.ord_of(sl0))}, Spec.prov_of(sl0)}, Nil{}) == Code.slot_step(sl0, o, Spec.PaymentDeclined{o}) : Spec.Slot & List<Spec.Effect>}, hn)
    case Spec.Slot{Spec.OrdRec{Spec.AwaitingPayment{}, am, oc, orf}, pv}:
      {==}
    case Spec.Slot{Spec.OrdRec{Spec.Paid{}, am, oc, orf}, pv}:
      ft_absurd({(Spec.Slot{Spec.OrdRec{Spec.Failed{}, Spec.amount_of(Spec.ord_of(sl0)), Spec.out_charge(Spec.ord_of(sl0)), Spec.out_refund(Spec.ord_of(sl0))}, Spec.prov_of(sl0)}, Nil{}) == Code.slot_step(sl0, o, Spec.PaymentDeclined{o}) : Spec.Slot & List<Spec.Effect>}, hn)
    case Spec.Slot{Spec.OrdRec{Spec.Failed{}, am, oc, orf}, pv}:
      ft_absurd({(Spec.Slot{Spec.OrdRec{Spec.Failed{}, Spec.amount_of(Spec.ord_of(sl0)), Spec.out_charge(Spec.ord_of(sl0)), Spec.out_refund(Spec.ord_of(sl0))}, Spec.prov_of(sl0)}, Nil{}) == Code.slot_step(sl0, o, Spec.PaymentDeclined{o}) : Spec.Slot & List<Spec.Effect>}, hn)
    case Spec.Slot{Spec.OrdRec{Spec.Refunded{}, am, oc, orf}, pv}:
      ft_absurd({(Spec.Slot{Spec.OrdRec{Spec.Failed{}, Spec.amount_of(Spec.ord_of(sl0)), Spec.out_charge(Spec.ord_of(sl0)), Spec.out_refund(Spec.ord_of(sl0))}, Spec.prov_of(sl0)}, Nil{}) == Code.slot_step(sl0, o, Spec.PaymentDeclined{o}) : Spec.Slot & List<Spec.Effect>}, hn)

def Laws.pin_payment_declined(s, o, h, hu, hr, hn):
  match s:
    case Spec.State{sl, ou, pu}:
      pin_full(sl, ou, ou, pu, Spec.PaymentDeclined{o}, Spec.Slot{Spec.OrdRec{Spec.Failed{}, Spec.amount_of(Spec.ord_of(Spec.get_l(sl, o))), Spec.out_charge(Spec.ord_of(Spec.get_l(sl, o))), Spec.out_refund(Spec.ord_of(Spec.get_l(sl, o)))}, Spec.prov_of(Spec.get_l(sl, o))}, Nil{}, hu, hr, ps_pay_no(Spec.get_l(sl, o), o, st_true(Spec.st(s, o), Spec.AwaitingPayment{}, hn)))

def ps_pay_no_other(+sl0: Spec.Slot, +o: Nat, +hn: {seq(Spec.status_of(Spec.ord_of(sl0)), Spec.AwaitingPayment{}) == False{} : Bool}) -> {(sl0, Nil{}) == Code.slot_step(sl0, o, Spec.PaymentDeclined{o}) : Spec.Slot & List<Spec.Effect>}:
  match sl0:
    case Spec.Slot{Spec.OrdRec{Spec.NoOrder{}, am, oc, orf}, pv}:
      {==}
    case Spec.Slot{Spec.OrdRec{Spec.AwaitingPayment{}, am, oc, orf}, pv}:
      tf_absurd({(sl0, Nil{}) == Code.slot_step(sl0, o, Spec.PaymentDeclined{o}) : Spec.Slot & List<Spec.Effect>}, hn)
    case Spec.Slot{Spec.OrdRec{Spec.Paid{}, am, oc, orf}, pv}:
      {==}
    case Spec.Slot{Spec.OrdRec{Spec.Failed{}, am, oc, orf}, pv}:
      {==}
    case Spec.Slot{Spec.OrdRec{Spec.Refunded{}, am, oc, orf}, pv}:
      {==}

def Laws.pin_payment_declined_other(s, o, h, hu, hr, hn):
  match s:
    case Spec.State{sl, ou, pu}:
      pin_same(sl, ou, ou, pu, Spec.PaymentDeclined{o}, hu, hr, ps_pay_no_other(Spec.get_l(sl, o), o, st_ne(Spec.st(s, o), Spec.AwaitingPayment{}, hn)))

def ps_refund_order(+sl0: Spec.Slot, +o: Nat, +hn: {seq(Spec.status_of(Spec.ord_of(sl0)), Spec.Paid{}) == True{} : Bool}) -> {(Spec.Slot{Spec.OrdRec{Spec.Refunded{}, Spec.amount_of(Spec.ord_of(sl0)), Spec.out_charge(Spec.ord_of(sl0)), True{}}, Spec.prov_of(sl0)}, Nil{}) == Code.slot_step(sl0, o, Spec.RefundOrder{o}) : Spec.Slot & List<Spec.Effect>}:
  match sl0:
    case Spec.Slot{Spec.OrdRec{Spec.NoOrder{}, am, oc, orf}, pv}:
      ft_absurd({(Spec.Slot{Spec.OrdRec{Spec.Refunded{}, Spec.amount_of(Spec.ord_of(sl0)), Spec.out_charge(Spec.ord_of(sl0)), True{}}, Spec.prov_of(sl0)}, Nil{}) == Code.slot_step(sl0, o, Spec.RefundOrder{o}) : Spec.Slot & List<Spec.Effect>}, hn)
    case Spec.Slot{Spec.OrdRec{Spec.AwaitingPayment{}, am, oc, orf}, pv}:
      ft_absurd({(Spec.Slot{Spec.OrdRec{Spec.Refunded{}, Spec.amount_of(Spec.ord_of(sl0)), Spec.out_charge(Spec.ord_of(sl0)), True{}}, Spec.prov_of(sl0)}, Nil{}) == Code.slot_step(sl0, o, Spec.RefundOrder{o}) : Spec.Slot & List<Spec.Effect>}, hn)
    case Spec.Slot{Spec.OrdRec{Spec.Paid{}, am, oc, orf}, pv}:
      {==}
    case Spec.Slot{Spec.OrdRec{Spec.Failed{}, am, oc, orf}, pv}:
      ft_absurd({(Spec.Slot{Spec.OrdRec{Spec.Refunded{}, Spec.amount_of(Spec.ord_of(sl0)), Spec.out_charge(Spec.ord_of(sl0)), True{}}, Spec.prov_of(sl0)}, Nil{}) == Code.slot_step(sl0, o, Spec.RefundOrder{o}) : Spec.Slot & List<Spec.Effect>}, hn)
    case Spec.Slot{Spec.OrdRec{Spec.Refunded{}, am, oc, orf}, pv}:
      ft_absurd({(Spec.Slot{Spec.OrdRec{Spec.Refunded{}, Spec.amount_of(Spec.ord_of(sl0)), Spec.out_charge(Spec.ord_of(sl0)), True{}}, Spec.prov_of(sl0)}, Nil{}) == Code.slot_step(sl0, o, Spec.RefundOrder{o}) : Spec.Slot & List<Spec.Effect>}, hn)

def Laws.pin_refund_order(s, o, h, hu, hr, hn):
  match s:
    case Spec.State{sl, ou, pu}:
      pin_full(sl, ou, ou, pu, Spec.RefundOrder{o}, Spec.Slot{Spec.OrdRec{Spec.Refunded{}, Spec.amount_of(Spec.ord_of(Spec.get_l(sl, o))), Spec.out_charge(Spec.ord_of(Spec.get_l(sl, o))), True{}}, Spec.prov_of(Spec.get_l(sl, o))}, Nil{}, hu, hr, ps_refund_order(Spec.get_l(sl, o), o, st_true(Spec.st(s, o), Spec.Paid{}, hn)))

def ps_refund_order_other(+sl0: Spec.Slot, +o: Nat, +hn: {seq(Spec.status_of(Spec.ord_of(sl0)), Spec.Paid{}) == False{} : Bool}) -> {(sl0, Nil{}) == Code.slot_step(sl0, o, Spec.RefundOrder{o}) : Spec.Slot & List<Spec.Effect>}:
  match sl0:
    case Spec.Slot{Spec.OrdRec{Spec.NoOrder{}, am, oc, orf}, pv}:
      {==}
    case Spec.Slot{Spec.OrdRec{Spec.AwaitingPayment{}, am, oc, orf}, pv}:
      {==}
    case Spec.Slot{Spec.OrdRec{Spec.Paid{}, am, oc, orf}, pv}:
      tf_absurd({(sl0, Nil{}) == Code.slot_step(sl0, o, Spec.RefundOrder{o}) : Spec.Slot & List<Spec.Effect>}, hn)
    case Spec.Slot{Spec.OrdRec{Spec.Failed{}, am, oc, orf}, pv}:
      {==}
    case Spec.Slot{Spec.OrdRec{Spec.Refunded{}, am, oc, orf}, pv}:
      {==}

def Laws.pin_refund_order_other(s, o, h, hu, hr, hn):
  match s:
    case Spec.State{sl, ou, pu}:
      pin_same(sl, ou, ou, pu, Spec.RefundOrder{o}, hu, hr, ps_refund_order_other(Spec.get_l(sl, o), o, st_ne(Spec.st(s, o), Spec.Paid{}, hn)))

def ps_flush_refund(+sl0: Spec.Slot, +o: Nat, +hn: {Spec.out_refund(Spec.ord_of(sl0)) == True{} : Bool}) -> {(Spec.Slot{Spec.OrdRec{Spec.status_of(Spec.ord_of(sl0)), Spec.amount_of(Spec.ord_of(sl0)), Spec.out_charge(Spec.ord_of(sl0)), False{}}, Spec.prov_of(sl0)}, Spec.WireRefundReq{o} <> Nil{}) == Code.slot_step(sl0, o, Spec.FlushRefundReq{o}) : Spec.Slot & List<Spec.Effect>}:
  match sl0:
    case Spec.Slot{Spec.OrdRec{x, am, oc, True{}}, pv}:
      {==}
    case Spec.Slot{Spec.OrdRec{x, am, oc, False{}}, pv}:
      ft_absurd({(Spec.Slot{Spec.OrdRec{Spec.status_of(Spec.ord_of(sl0)), Spec.amount_of(Spec.ord_of(sl0)), Spec.out_charge(Spec.ord_of(sl0)), False{}}, Spec.prov_of(sl0)}, Spec.WireRefundReq{o} <> Nil{}) == Code.slot_step(sl0, o, Spec.FlushRefundReq{o}) : Spec.Slot & List<Spec.Effect>}, hn)

def Laws.pin_flush_refund_req(s, o, h, hu, hr, hn):
  match s:
    case Spec.State{sl, ou, pu}:
      pin_full(sl, ou, ou, pu, Spec.FlushRefundReq{o}, Spec.Slot{Spec.OrdRec{Spec.status_of(Spec.ord_of(Spec.get_l(sl, o))), Spec.amount_of(Spec.ord_of(Spec.get_l(sl, o))), Spec.out_charge(Spec.ord_of(Spec.get_l(sl, o))), False{}}, Spec.prov_of(Spec.get_l(sl, o))}, Spec.WireRefundReq{o} <> Nil{}, hu, hr, ps_flush_refund(Spec.get_l(sl, o), o, hn))

def ps_flush_refund_other(+sl0: Spec.Slot, +o: Nat, +hn: {Spec.out_refund(Spec.ord_of(sl0)) == False{} : Bool}) -> {(sl0, Nil{}) == Code.slot_step(sl0, o, Spec.FlushRefundReq{o}) : Spec.Slot & List<Spec.Effect>}:
  match sl0:
    case Spec.Slot{Spec.OrdRec{x, am, oc, True{}}, pv}:
      tf_absurd({(sl0, Nil{}) == Code.slot_step(sl0, o, Spec.FlushRefundReq{o}) : Spec.Slot & List<Spec.Effect>}, hn)
    case Spec.Slot{Spec.OrdRec{x, am, oc, False{}}, pv}:
      {==}

def Laws.pin_flush_refund_req_other(s, o, h, hu, hr, hn):
  match s:
    case Spec.State{sl, ou, pu}:
      pin_same(sl, ou, ou, pu, Spec.FlushRefundReq{o}, hu, hr, ps_flush_refund_other(Spec.get_l(sl, o), o, hn))

def ps_charge_approve(+sl0: Spec.Slot, +o: Nat, +a: Nat, +hp: {Nat.is_lt(0n, a) == True{} : Bool}, +hn: {rseq(Spec.rec_of(Spec.prov_of(sl0)), Spec.NoRec{}) == True{} : Bool}) -> {(Spec.Slot{Spec.ord_of(sl0), Spec.ProvRec{Spec.Approved{}, 1n+Spec.charge_count(Spec.prov_of(sl0)), Spec.refund_count(Spec.prov_of(sl0)), a, True{}}}, Spec.Charge{o, a} <> Nil{}) == Code.slot_step(sl0, o, Spec.ChargeReqRecv{o, a, Spec.Approve{}}) : Spec.Slot & List<Spec.Effect>}:
  match sl0 a:
    case Spec.Slot{od, Spec.ProvRec{Spec.NoRec{}, cc, rc, am, orr}} 0n:
      ft_absurd({(Spec.Slot{Spec.ord_of(sl0), Spec.ProvRec{Spec.Approved{}, 1n+Spec.charge_count(Spec.prov_of(sl0)), Spec.refund_count(Spec.prov_of(sl0)), a, True{}}}, Spec.Charge{o, a} <> Nil{}) == Code.slot_step(sl0, o, Spec.ChargeReqRecv{o, a, Spec.Approve{}}) : Spec.Slot & List<Spec.Effect>}, hp)
    case Spec.Slot{od, Spec.ProvRec{Spec.NoRec{}, cc, rc, am, orr}} 1n+pa:
      {==}
    case Spec.Slot{od, Spec.ProvRec{Spec.Approved{}, cc, rc, am, orr}} 0n:
      ft_absurd({(Spec.Slot{Spec.ord_of(sl0), Spec.ProvRec{Spec.Approved{}, 1n+Spec.charge_count(Spec.prov_of(sl0)), Spec.refund_count(Spec.prov_of(sl0)), a, True{}}}, Spec.Charge{o, a} <> Nil{}) == Code.slot_step(sl0, o, Spec.ChargeReqRecv{o, a, Spec.Approve{}}) : Spec.Slot & List<Spec.Effect>}, hp)
    case Spec.Slot{od, Spec.ProvRec{Spec.Approved{}, cc, rc, am, orr}} 1n+pa:
      ft_absurd({(Spec.Slot{Spec.ord_of(sl0), Spec.ProvRec{Spec.Approved{}, 1n+Spec.charge_count(Spec.prov_of(sl0)), Spec.refund_count(Spec.prov_of(sl0)), a, True{}}}, Spec.Charge{o, a} <> Nil{}) == Code.slot_step(sl0, o, Spec.ChargeReqRecv{o, a, Spec.Approve{}}) : Spec.Slot & List<Spec.Effect>}, hn)
    case Spec.Slot{od, Spec.ProvRec{Spec.Declined{}, cc, rc, am, orr}} 0n:
      ft_absurd({(Spec.Slot{Spec.ord_of(sl0), Spec.ProvRec{Spec.Approved{}, 1n+Spec.charge_count(Spec.prov_of(sl0)), Spec.refund_count(Spec.prov_of(sl0)), a, True{}}}, Spec.Charge{o, a} <> Nil{}) == Code.slot_step(sl0, o, Spec.ChargeReqRecv{o, a, Spec.Approve{}}) : Spec.Slot & List<Spec.Effect>}, hp)
    case Spec.Slot{od, Spec.ProvRec{Spec.Declined{}, cc, rc, am, orr}} 1n+pa:
      ft_absurd({(Spec.Slot{Spec.ord_of(sl0), Spec.ProvRec{Spec.Approved{}, 1n+Spec.charge_count(Spec.prov_of(sl0)), Spec.refund_count(Spec.prov_of(sl0)), a, True{}}}, Spec.Charge{o, a} <> Nil{}) == Code.slot_step(sl0, o, Spec.ChargeReqRecv{o, a, Spec.Approve{}}) : Spec.Slot & List<Spec.Effect>}, hn)

def Laws.pin_charge_req_recv_approve(s, o, a, h, hu, hr, hp, hn):
  match s:
    case Spec.State{sl, ou, pu}:
      pin_full(sl, pu, ou, pu, Spec.ChargeReqRecv{o, a, Spec.Approve{}}, Spec.Slot{Spec.ord_of(Spec.get_l(sl, o)), Spec.ProvRec{Spec.Approved{}, 1n+Spec.charge_count(Spec.prov_of(Spec.get_l(sl, o))), Spec.refund_count(Spec.prov_of(Spec.get_l(sl, o))), a, True{}}}, Spec.Charge{o, a} <> Nil{}, hu, hr, ps_charge_approve(Spec.get_l(sl, o), o, a, hp, rec_true(Spec.rec_of(Spec.pr(s, o)), Spec.NoRec{}, hn)))

def ps_charge_decline(+sl0: Spec.Slot, +o: Nat, +a: Nat, +hp: {Nat.is_lt(0n, a) == True{} : Bool}, +hn: {rseq(Spec.rec_of(Spec.prov_of(sl0)), Spec.NoRec{}) == True{} : Bool}) -> {(Spec.Slot{Spec.ord_of(sl0), Spec.ProvRec{Spec.Declined{}, Spec.charge_count(Spec.prov_of(sl0)), Spec.refund_count(Spec.prov_of(sl0)), Spec.amt_of(Spec.prov_of(sl0)), True{}}}, Nil{}) == Code.slot_step(sl0, o, Spec.ChargeReqRecv{o, a, Spec.Decline{}}) : Spec.Slot & List<Spec.Effect>}:
  match sl0 a:
    case Spec.Slot{od, Spec.ProvRec{Spec.NoRec{}, cc, rc, am, orr}} 0n:
      ft_absurd({(Spec.Slot{Spec.ord_of(sl0), Spec.ProvRec{Spec.Declined{}, Spec.charge_count(Spec.prov_of(sl0)), Spec.refund_count(Spec.prov_of(sl0)), Spec.amt_of(Spec.prov_of(sl0)), True{}}}, Nil{}) == Code.slot_step(sl0, o, Spec.ChargeReqRecv{o, a, Spec.Decline{}}) : Spec.Slot & List<Spec.Effect>}, hp)
    case Spec.Slot{od, Spec.ProvRec{Spec.NoRec{}, cc, rc, am, orr}} 1n+pa:
      {==}
    case Spec.Slot{od, Spec.ProvRec{Spec.Approved{}, cc, rc, am, orr}} 0n:
      ft_absurd({(Spec.Slot{Spec.ord_of(sl0), Spec.ProvRec{Spec.Declined{}, Spec.charge_count(Spec.prov_of(sl0)), Spec.refund_count(Spec.prov_of(sl0)), Spec.amt_of(Spec.prov_of(sl0)), True{}}}, Nil{}) == Code.slot_step(sl0, o, Spec.ChargeReqRecv{o, a, Spec.Decline{}}) : Spec.Slot & List<Spec.Effect>}, hp)
    case Spec.Slot{od, Spec.ProvRec{Spec.Approved{}, cc, rc, am, orr}} 1n+pa:
      ft_absurd({(Spec.Slot{Spec.ord_of(sl0), Spec.ProvRec{Spec.Declined{}, Spec.charge_count(Spec.prov_of(sl0)), Spec.refund_count(Spec.prov_of(sl0)), Spec.amt_of(Spec.prov_of(sl0)), True{}}}, Nil{}) == Code.slot_step(sl0, o, Spec.ChargeReqRecv{o, a, Spec.Decline{}}) : Spec.Slot & List<Spec.Effect>}, hn)
    case Spec.Slot{od, Spec.ProvRec{Spec.Declined{}, cc, rc, am, orr}} 0n:
      ft_absurd({(Spec.Slot{Spec.ord_of(sl0), Spec.ProvRec{Spec.Declined{}, Spec.charge_count(Spec.prov_of(sl0)), Spec.refund_count(Spec.prov_of(sl0)), Spec.amt_of(Spec.prov_of(sl0)), True{}}}, Nil{}) == Code.slot_step(sl0, o, Spec.ChargeReqRecv{o, a, Spec.Decline{}}) : Spec.Slot & List<Spec.Effect>}, hp)
    case Spec.Slot{od, Spec.ProvRec{Spec.Declined{}, cc, rc, am, orr}} 1n+pa:
      ft_absurd({(Spec.Slot{Spec.ord_of(sl0), Spec.ProvRec{Spec.Declined{}, Spec.charge_count(Spec.prov_of(sl0)), Spec.refund_count(Spec.prov_of(sl0)), Spec.amt_of(Spec.prov_of(sl0)), True{}}}, Nil{}) == Code.slot_step(sl0, o, Spec.ChargeReqRecv{o, a, Spec.Decline{}}) : Spec.Slot & List<Spec.Effect>}, hn)

def Laws.pin_charge_req_recv_decline(s, o, a, h, hu, hr, hp, hn):
  match s:
    case Spec.State{sl, ou, pu}:
      pin_full(sl, pu, ou, pu, Spec.ChargeReqRecv{o, a, Spec.Decline{}}, Spec.Slot{Spec.ord_of(Spec.get_l(sl, o)), Spec.ProvRec{Spec.Declined{}, Spec.charge_count(Spec.prov_of(Spec.get_l(sl, o))), Spec.refund_count(Spec.prov_of(Spec.get_l(sl, o))), Spec.amt_of(Spec.prov_of(Spec.get_l(sl, o))), True{}}}, Nil{}, hu, hr, ps_charge_decline(Spec.get_l(sl, o), o, a, hp, rec_true(Spec.rec_of(Spec.pr(s, o)), Spec.NoRec{}, hn)))

def ps_replay_approved(+sl0: Spec.Slot, +o: Nat, +a: Nat, +d: Spec.Dec, +hp: {Nat.is_lt(0n, a) == True{} : Bool}, +hn: {rseq(Spec.rec_of(Spec.prov_of(sl0)), Spec.Approved{}) == True{} : Bool}) -> {(Spec.Slot{Spec.ord_of(sl0), Spec.ProvRec{Spec.Approved{}, Spec.charge_count(Spec.prov_of(sl0)), Spec.refund_count(Spec.prov_of(sl0)), Spec.amt_of(Spec.prov_of(sl0)), True{}}}, Nil{}) == Code.slot_step(sl0, o, Spec.ChargeReqRecv{o, a, d}) : Spec.Slot & List<Spec.Effect>}:
  match sl0 a:
    case Spec.Slot{od, Spec.ProvRec{Spec.NoRec{}, cc, rc, am, orr}} 0n:
      ft_absurd({(Spec.Slot{Spec.ord_of(sl0), Spec.ProvRec{Spec.Approved{}, Spec.charge_count(Spec.prov_of(sl0)), Spec.refund_count(Spec.prov_of(sl0)), Spec.amt_of(Spec.prov_of(sl0)), True{}}}, Nil{}) == Code.slot_step(sl0, o, Spec.ChargeReqRecv{o, a, d}) : Spec.Slot & List<Spec.Effect>}, hp)
    case Spec.Slot{od, Spec.ProvRec{Spec.NoRec{}, cc, rc, am, orr}} 1n+pa:
      ft_absurd({(Spec.Slot{Spec.ord_of(sl0), Spec.ProvRec{Spec.Approved{}, Spec.charge_count(Spec.prov_of(sl0)), Spec.refund_count(Spec.prov_of(sl0)), Spec.amt_of(Spec.prov_of(sl0)), True{}}}, Nil{}) == Code.slot_step(sl0, o, Spec.ChargeReqRecv{o, a, d}) : Spec.Slot & List<Spec.Effect>}, hn)
    case Spec.Slot{od, Spec.ProvRec{Spec.Approved{}, cc, rc, am, orr}} 0n:
      ft_absurd({(Spec.Slot{Spec.ord_of(sl0), Spec.ProvRec{Spec.Approved{}, Spec.charge_count(Spec.prov_of(sl0)), Spec.refund_count(Spec.prov_of(sl0)), Spec.amt_of(Spec.prov_of(sl0)), True{}}}, Nil{}) == Code.slot_step(sl0, o, Spec.ChargeReqRecv{o, a, d}) : Spec.Slot & List<Spec.Effect>}, hp)
    case Spec.Slot{od, Spec.ProvRec{Spec.Approved{}, cc, rc, am, orr}} 1n+pa:
      {==}
    case Spec.Slot{od, Spec.ProvRec{Spec.Declined{}, cc, rc, am, orr}} 0n:
      ft_absurd({(Spec.Slot{Spec.ord_of(sl0), Spec.ProvRec{Spec.Approved{}, Spec.charge_count(Spec.prov_of(sl0)), Spec.refund_count(Spec.prov_of(sl0)), Spec.amt_of(Spec.prov_of(sl0)), True{}}}, Nil{}) == Code.slot_step(sl0, o, Spec.ChargeReqRecv{o, a, d}) : Spec.Slot & List<Spec.Effect>}, hp)
    case Spec.Slot{od, Spec.ProvRec{Spec.Declined{}, cc, rc, am, orr}} 1n+pa:
      ft_absurd({(Spec.Slot{Spec.ord_of(sl0), Spec.ProvRec{Spec.Approved{}, Spec.charge_count(Spec.prov_of(sl0)), Spec.refund_count(Spec.prov_of(sl0)), Spec.amt_of(Spec.prov_of(sl0)), True{}}}, Nil{}) == Code.slot_step(sl0, o, Spec.ChargeReqRecv{o, a, d}) : Spec.Slot & List<Spec.Effect>}, hn)

def Laws.pin_charge_req_recv_replay_approved(s, o, a, d, h, hu, hr, hp, hn):
  match s:
    case Spec.State{sl, ou, pu}:
      pin_full(sl, pu, ou, pu, Spec.ChargeReqRecv{o, a, d}, Spec.Slot{Spec.ord_of(Spec.get_l(sl, o)), Spec.ProvRec{Spec.Approved{}, Spec.charge_count(Spec.prov_of(Spec.get_l(sl, o))), Spec.refund_count(Spec.prov_of(Spec.get_l(sl, o))), Spec.amt_of(Spec.prov_of(Spec.get_l(sl, o))), True{}}}, Nil{}, hu, hr, ps_replay_approved(Spec.get_l(sl, o), o, a, d, hp, rec_true(Spec.rec_of(Spec.pr(s, o)), Spec.Approved{}, hn)))

def ps_replay_declined(+sl0: Spec.Slot, +o: Nat, +a: Nat, +d: Spec.Dec, +hp: {Nat.is_lt(0n, a) == True{} : Bool}, +hn: {rseq(Spec.rec_of(Spec.prov_of(sl0)), Spec.Declined{}) == True{} : Bool}) -> {(Spec.Slot{Spec.ord_of(sl0), Spec.ProvRec{Spec.Declined{}, Spec.charge_count(Spec.prov_of(sl0)), Spec.refund_count(Spec.prov_of(sl0)), Spec.amt_of(Spec.prov_of(sl0)), True{}}}, Nil{}) == Code.slot_step(sl0, o, Spec.ChargeReqRecv{o, a, d}) : Spec.Slot & List<Spec.Effect>}:
  match sl0 a:
    case Spec.Slot{od, Spec.ProvRec{Spec.NoRec{}, cc, rc, am, orr}} 0n:
      ft_absurd({(Spec.Slot{Spec.ord_of(sl0), Spec.ProvRec{Spec.Declined{}, Spec.charge_count(Spec.prov_of(sl0)), Spec.refund_count(Spec.prov_of(sl0)), Spec.amt_of(Spec.prov_of(sl0)), True{}}}, Nil{}) == Code.slot_step(sl0, o, Spec.ChargeReqRecv{o, a, d}) : Spec.Slot & List<Spec.Effect>}, hp)
    case Spec.Slot{od, Spec.ProvRec{Spec.NoRec{}, cc, rc, am, orr}} 1n+pa:
      ft_absurd({(Spec.Slot{Spec.ord_of(sl0), Spec.ProvRec{Spec.Declined{}, Spec.charge_count(Spec.prov_of(sl0)), Spec.refund_count(Spec.prov_of(sl0)), Spec.amt_of(Spec.prov_of(sl0)), True{}}}, Nil{}) == Code.slot_step(sl0, o, Spec.ChargeReqRecv{o, a, d}) : Spec.Slot & List<Spec.Effect>}, hn)
    case Spec.Slot{od, Spec.ProvRec{Spec.Approved{}, cc, rc, am, orr}} 0n:
      ft_absurd({(Spec.Slot{Spec.ord_of(sl0), Spec.ProvRec{Spec.Declined{}, Spec.charge_count(Spec.prov_of(sl0)), Spec.refund_count(Spec.prov_of(sl0)), Spec.amt_of(Spec.prov_of(sl0)), True{}}}, Nil{}) == Code.slot_step(sl0, o, Spec.ChargeReqRecv{o, a, d}) : Spec.Slot & List<Spec.Effect>}, hp)
    case Spec.Slot{od, Spec.ProvRec{Spec.Approved{}, cc, rc, am, orr}} 1n+pa:
      ft_absurd({(Spec.Slot{Spec.ord_of(sl0), Spec.ProvRec{Spec.Declined{}, Spec.charge_count(Spec.prov_of(sl0)), Spec.refund_count(Spec.prov_of(sl0)), Spec.amt_of(Spec.prov_of(sl0)), True{}}}, Nil{}) == Code.slot_step(sl0, o, Spec.ChargeReqRecv{o, a, d}) : Spec.Slot & List<Spec.Effect>}, hn)
    case Spec.Slot{od, Spec.ProvRec{Spec.Declined{}, cc, rc, am, orr}} 0n:
      ft_absurd({(Spec.Slot{Spec.ord_of(sl0), Spec.ProvRec{Spec.Declined{}, Spec.charge_count(Spec.prov_of(sl0)), Spec.refund_count(Spec.prov_of(sl0)), Spec.amt_of(Spec.prov_of(sl0)), True{}}}, Nil{}) == Code.slot_step(sl0, o, Spec.ChargeReqRecv{o, a, d}) : Spec.Slot & List<Spec.Effect>}, hp)
    case Spec.Slot{od, Spec.ProvRec{Spec.Declined{}, cc, rc, am, orr}} 1n+pa:
      {==}

def Laws.pin_charge_req_recv_replay_declined(s, o, a, d, h, hu, hr, hp, hn):
  match s:
    case Spec.State{sl, ou, pu}:
      pin_full(sl, pu, ou, pu, Spec.ChargeReqRecv{o, a, d}, Spec.Slot{Spec.ord_of(Spec.get_l(sl, o)), Spec.ProvRec{Spec.Declined{}, Spec.charge_count(Spec.prov_of(Spec.get_l(sl, o))), Spec.refund_count(Spec.prov_of(Spec.get_l(sl, o))), Spec.amt_of(Spec.prov_of(Spec.get_l(sl, o))), True{}}}, Nil{}, hu, hr, ps_replay_declined(Spec.get_l(sl, o), o, a, d, hp, rec_true(Spec.rec_of(Spec.pr(s, o)), Spec.Declined{}, hn)))

def ps_flush_reply_approved(+sl0: Spec.Slot, +o: Nat, +hn: {Spec.out_reply(Spec.prov_of(sl0)) == True{} : Bool}, +hq: {rseq(Spec.rec_of(Spec.prov_of(sl0)), Spec.Approved{}) == True{} : Bool}) -> {(Spec.Slot{Spec.ord_of(sl0), Spec.ProvRec{Spec.Approved{}, Spec.charge_count(Spec.prov_of(sl0)), Spec.refund_count(Spec.prov_of(sl0)), Spec.amt_of(Spec.prov_of(sl0)), False{}}}, Spec.WireApproved{o} <> Nil{}) == Code.slot_step(sl0, o, Spec.FlushReply{o}) : Spec.Slot & List<Spec.Effect>}:
  match sl0:
    case Spec.Slot{od, Spec.ProvRec{Spec.NoRec{}, cc, rc, am, True{}}}:
      ft_absurd({(Spec.Slot{Spec.ord_of(sl0), Spec.ProvRec{Spec.Approved{}, Spec.charge_count(Spec.prov_of(sl0)), Spec.refund_count(Spec.prov_of(sl0)), Spec.amt_of(Spec.prov_of(sl0)), False{}}}, Spec.WireApproved{o} <> Nil{}) == Code.slot_step(sl0, o, Spec.FlushReply{o}) : Spec.Slot & List<Spec.Effect>}, hq)
    case Spec.Slot{od, Spec.ProvRec{Spec.NoRec{}, cc, rc, am, False{}}}:
      ft_absurd({(Spec.Slot{Spec.ord_of(sl0), Spec.ProvRec{Spec.Approved{}, Spec.charge_count(Spec.prov_of(sl0)), Spec.refund_count(Spec.prov_of(sl0)), Spec.amt_of(Spec.prov_of(sl0)), False{}}}, Spec.WireApproved{o} <> Nil{}) == Code.slot_step(sl0, o, Spec.FlushReply{o}) : Spec.Slot & List<Spec.Effect>}, hn)
    case Spec.Slot{od, Spec.ProvRec{Spec.Approved{}, cc, rc, am, True{}}}:
      {==}
    case Spec.Slot{od, Spec.ProvRec{Spec.Approved{}, cc, rc, am, False{}}}:
      ft_absurd({(Spec.Slot{Spec.ord_of(sl0), Spec.ProvRec{Spec.Approved{}, Spec.charge_count(Spec.prov_of(sl0)), Spec.refund_count(Spec.prov_of(sl0)), Spec.amt_of(Spec.prov_of(sl0)), False{}}}, Spec.WireApproved{o} <> Nil{}) == Code.slot_step(sl0, o, Spec.FlushReply{o}) : Spec.Slot & List<Spec.Effect>}, hn)
    case Spec.Slot{od, Spec.ProvRec{Spec.Declined{}, cc, rc, am, True{}}}:
      ft_absurd({(Spec.Slot{Spec.ord_of(sl0), Spec.ProvRec{Spec.Approved{}, Spec.charge_count(Spec.prov_of(sl0)), Spec.refund_count(Spec.prov_of(sl0)), Spec.amt_of(Spec.prov_of(sl0)), False{}}}, Spec.WireApproved{o} <> Nil{}) == Code.slot_step(sl0, o, Spec.FlushReply{o}) : Spec.Slot & List<Spec.Effect>}, hq)
    case Spec.Slot{od, Spec.ProvRec{Spec.Declined{}, cc, rc, am, False{}}}:
      ft_absurd({(Spec.Slot{Spec.ord_of(sl0), Spec.ProvRec{Spec.Approved{}, Spec.charge_count(Spec.prov_of(sl0)), Spec.refund_count(Spec.prov_of(sl0)), Spec.amt_of(Spec.prov_of(sl0)), False{}}}, Spec.WireApproved{o} <> Nil{}) == Code.slot_step(sl0, o, Spec.FlushReply{o}) : Spec.Slot & List<Spec.Effect>}, hn)

def Laws.pin_flush_reply_approved(s, o, h, hu, hr, hn, hq):
  match s:
    case Spec.State{sl, ou, pu}:
      pin_full(sl, pu, ou, pu, Spec.FlushReply{o}, Spec.Slot{Spec.ord_of(Spec.get_l(sl, o)), Spec.ProvRec{Spec.Approved{}, Spec.charge_count(Spec.prov_of(Spec.get_l(sl, o))), Spec.refund_count(Spec.prov_of(Spec.get_l(sl, o))), Spec.amt_of(Spec.prov_of(Spec.get_l(sl, o))), False{}}}, Spec.WireApproved{o} <> Nil{}, hu, hr, ps_flush_reply_approved(Spec.get_l(sl, o), o, hn, rec_true(Spec.rec_of(Spec.pr(s, o)), Spec.Approved{}, hq)))

def ps_flush_reply_declined(+sl0: Spec.Slot, +o: Nat, +hn: {Spec.out_reply(Spec.prov_of(sl0)) == True{} : Bool}, +hq: {rseq(Spec.rec_of(Spec.prov_of(sl0)), Spec.Declined{}) == True{} : Bool}) -> {(Spec.Slot{Spec.ord_of(sl0), Spec.ProvRec{Spec.Declined{}, Spec.charge_count(Spec.prov_of(sl0)), Spec.refund_count(Spec.prov_of(sl0)), Spec.amt_of(Spec.prov_of(sl0)), False{}}}, Spec.WireDeclined{o} <> Nil{}) == Code.slot_step(sl0, o, Spec.FlushReply{o}) : Spec.Slot & List<Spec.Effect>}:
  match sl0:
    case Spec.Slot{od, Spec.ProvRec{Spec.NoRec{}, cc, rc, am, True{}}}:
      ft_absurd({(Spec.Slot{Spec.ord_of(sl0), Spec.ProvRec{Spec.Declined{}, Spec.charge_count(Spec.prov_of(sl0)), Spec.refund_count(Spec.prov_of(sl0)), Spec.amt_of(Spec.prov_of(sl0)), False{}}}, Spec.WireDeclined{o} <> Nil{}) == Code.slot_step(sl0, o, Spec.FlushReply{o}) : Spec.Slot & List<Spec.Effect>}, hq)
    case Spec.Slot{od, Spec.ProvRec{Spec.NoRec{}, cc, rc, am, False{}}}:
      ft_absurd({(Spec.Slot{Spec.ord_of(sl0), Spec.ProvRec{Spec.Declined{}, Spec.charge_count(Spec.prov_of(sl0)), Spec.refund_count(Spec.prov_of(sl0)), Spec.amt_of(Spec.prov_of(sl0)), False{}}}, Spec.WireDeclined{o} <> Nil{}) == Code.slot_step(sl0, o, Spec.FlushReply{o}) : Spec.Slot & List<Spec.Effect>}, hn)
    case Spec.Slot{od, Spec.ProvRec{Spec.Approved{}, cc, rc, am, True{}}}:
      ft_absurd({(Spec.Slot{Spec.ord_of(sl0), Spec.ProvRec{Spec.Declined{}, Spec.charge_count(Spec.prov_of(sl0)), Spec.refund_count(Spec.prov_of(sl0)), Spec.amt_of(Spec.prov_of(sl0)), False{}}}, Spec.WireDeclined{o} <> Nil{}) == Code.slot_step(sl0, o, Spec.FlushReply{o}) : Spec.Slot & List<Spec.Effect>}, hq)
    case Spec.Slot{od, Spec.ProvRec{Spec.Approved{}, cc, rc, am, False{}}}:
      ft_absurd({(Spec.Slot{Spec.ord_of(sl0), Spec.ProvRec{Spec.Declined{}, Spec.charge_count(Spec.prov_of(sl0)), Spec.refund_count(Spec.prov_of(sl0)), Spec.amt_of(Spec.prov_of(sl0)), False{}}}, Spec.WireDeclined{o} <> Nil{}) == Code.slot_step(sl0, o, Spec.FlushReply{o}) : Spec.Slot & List<Spec.Effect>}, hn)
    case Spec.Slot{od, Spec.ProvRec{Spec.Declined{}, cc, rc, am, True{}}}:
      {==}
    case Spec.Slot{od, Spec.ProvRec{Spec.Declined{}, cc, rc, am, False{}}}:
      ft_absurd({(Spec.Slot{Spec.ord_of(sl0), Spec.ProvRec{Spec.Declined{}, Spec.charge_count(Spec.prov_of(sl0)), Spec.refund_count(Spec.prov_of(sl0)), Spec.amt_of(Spec.prov_of(sl0)), False{}}}, Spec.WireDeclined{o} <> Nil{}) == Code.slot_step(sl0, o, Spec.FlushReply{o}) : Spec.Slot & List<Spec.Effect>}, hn)

def Laws.pin_flush_reply_declined(s, o, h, hu, hr, hn, hq):
  match s:
    case Spec.State{sl, ou, pu}:
      pin_full(sl, pu, ou, pu, Spec.FlushReply{o}, Spec.Slot{Spec.ord_of(Spec.get_l(sl, o)), Spec.ProvRec{Spec.Declined{}, Spec.charge_count(Spec.prov_of(Spec.get_l(sl, o))), Spec.refund_count(Spec.prov_of(Spec.get_l(sl, o))), Spec.amt_of(Spec.prov_of(Spec.get_l(sl, o))), False{}}}, Spec.WireDeclined{o} <> Nil{}, hu, hr, ps_flush_reply_declined(Spec.get_l(sl, o), o, hn, rec_true(Spec.rec_of(Spec.pr(s, o)), Spec.Declined{}, hq)))

def ps_flush_reply_other(+sl0: Spec.Slot, +o: Nat, +hn: {Bool.and(Spec.out_reply(Spec.prov_of(sl0)), Bool.not(Spec.is_norec(Spec.rec_of(Spec.prov_of(sl0))))) == False{} : Bool}) -> {(sl0, Nil{}) == Code.slot_step(sl0, o, Spec.FlushReply{o}) : Spec.Slot & List<Spec.Effect>}:
  match sl0:
    case Spec.Slot{od, Spec.ProvRec{Spec.NoRec{}, cc, rc, am, True{}}}:
      {==}
    case Spec.Slot{od, Spec.ProvRec{Spec.NoRec{}, cc, rc, am, False{}}}:
      {==}
    case Spec.Slot{od, Spec.ProvRec{Spec.Approved{}, cc, rc, am, True{}}}:
      tf_absurd({(sl0, Nil{}) == Code.slot_step(sl0, o, Spec.FlushReply{o}) : Spec.Slot & List<Spec.Effect>}, hn)
    case Spec.Slot{od, Spec.ProvRec{Spec.Approved{}, cc, rc, am, False{}}}:
      {==}
    case Spec.Slot{od, Spec.ProvRec{Spec.Declined{}, cc, rc, am, True{}}}:
      tf_absurd({(sl0, Nil{}) == Code.slot_step(sl0, o, Spec.FlushReply{o}) : Spec.Slot & List<Spec.Effect>}, hn)
    case Spec.Slot{od, Spec.ProvRec{Spec.Declined{}, cc, rc, am, False{}}}:
      {==}

def Laws.pin_flush_reply_other(s, o, h, hu, hr, hn):
  match s:
    case Spec.State{sl, ou, pu}:
      pin_same(sl, pu, ou, pu, Spec.FlushReply{o}, hu, hr, ps_flush_reply_other(Spec.get_l(sl, o), o, hn))

def ps_charge_zero(+sl0: Spec.Slot, +o: Nat, +d: Spec.Dec) -> {(sl0, Nil{}) == Code.slot_step(sl0, o, Spec.ChargeReqRecv{o, 0n, d}) : Spec.Slot & List<Spec.Effect>}:
  match sl0 d:
    case Spec.Slot{od, Spec.ProvRec{Spec.NoRec{}, cc, rc, am, orr}} Spec.Approve{}:
      {==}
    case Spec.Slot{od, Spec.ProvRec{Spec.NoRec{}, cc, rc, am, orr}} Spec.Decline{}:
      {==}
    case Spec.Slot{od, Spec.ProvRec{Spec.Approved{}, cc, rc, am, orr}} Spec.Approve{}:
      {==}
    case Spec.Slot{od, Spec.ProvRec{Spec.Approved{}, cc, rc, am, orr}} Spec.Decline{}:
      {==}
    case Spec.Slot{od, Spec.ProvRec{Spec.Declined{}, cc, rc, am, orr}} Spec.Approve{}:
      {==}
    case Spec.Slot{od, Spec.ProvRec{Spec.Declined{}, cc, rc, am, orr}} Spec.Decline{}:
      {==}

def Laws.pin_charge_req_recv_zero(s, o, d, h, hu, hr):
  match s:
    case Spec.State{sl, ou, pu}:
      pin_same(sl, pu, ou, pu, Spec.ChargeReqRecv{o, 0n, d}, hu, hr, ps_charge_zero(Spec.get_l(sl, o), o, d))

def rp_core(+od: Spec.OrdRec, +r: Spec.Res, +cc: Nat, +rc: Nat, +am: Nat, +orr: Bool, +o: Nat, +g: Bool, +hgt: {g == True{} : Bool}, +hq: {rseq(r, Spec.Approved{}) == True{} : Bool}) -> {(Spec.Slot{od, Spec.ProvRec{Spec.Approved{}, cc, 1n+rc, am, orr}}, Spec.Refund{o, am} <> Nil{}) == Code.with_prov(Code.refund_pick(Spec.ProvRec{r, cc, rc, am, orr}, o, g), od) : Spec.Slot & List<Spec.Effect>}:
  match r g:
    case Spec.NoRec{} _:
      ft_absurd({(Spec.Slot{od, Spec.ProvRec{Spec.Approved{}, cc, 1n+rc, am, orr}}, Spec.Refund{o, am} <> Nil{}) == Code.with_prov(Code.refund_pick(Spec.ProvRec{r, cc, rc, am, orr}, o, g), od) : Spec.Slot & List<Spec.Effect>}, hq)
    case Spec.Declined{} _:
      ft_absurd({(Spec.Slot{od, Spec.ProvRec{Spec.Approved{}, cc, 1n+rc, am, orr}}, Spec.Refund{o, am} <> Nil{}) == Code.with_prov(Code.refund_pick(Spec.ProvRec{r, cc, rc, am, orr}, o, g), od) : Spec.Slot & List<Spec.Effect>}, hq)
    case Spec.Approved{} False{}:
      ft_absurd({(Spec.Slot{od, Spec.ProvRec{Spec.Approved{}, cc, 1n+rc, am, orr}}, Spec.Refund{o, am} <> Nil{}) == Code.with_prov(Code.refund_pick(Spec.ProvRec{r, cc, rc, am, orr}, o, g), od) : Spec.Slot & List<Spec.Effect>}, hgt)
    case Spec.Approved{} True{}:
      {==}

def ps_a10(+sl0: Spec.Slot, +o: Nat, +hq: {rseq(Spec.rec_of(Spec.prov_of(sl0)), Spec.Approved{}) == True{} : Bool}, +hl: {Nat.is_lt(Spec.refund_count(Spec.prov_of(sl0)), Spec.charge_count(Spec.prov_of(sl0))) == True{} : Bool}) -> {(Spec.Slot{Spec.ord_of(sl0), Spec.ProvRec{Spec.Approved{}, Spec.charge_count(Spec.prov_of(sl0)), 1n+Spec.refund_count(Spec.prov_of(sl0)), Spec.amt_of(Spec.prov_of(sl0)), Spec.out_reply(Spec.prov_of(sl0))}}, Spec.Refund{o, Spec.amt_of(Spec.prov_of(sl0))} <> Nil{}) == Code.slot_step(sl0, o, Spec.RefundReqRecv{o}) : Spec.Slot & List<Spec.Effect>}:
  match sl0:
    case Spec.Slot{od, Spec.ProvRec{r, cc, rc, am, orr}}:
      rp_core(od, r, cc, rc, am, orr, o, Nat.is_lt(rc, cc), hl, hq)

def Laws.pin_refund_req_recv(s, o, h, hu, hr, hn, hl):
  match s:
    case Spec.State{sl, ou, pu}:
      pin_full(sl, pu, ou, pu, Spec.RefundReqRecv{o}, Spec.Slot{Spec.ord_of(Spec.get_l(sl, o)), Spec.ProvRec{Spec.Approved{}, Spec.charge_count(Spec.prov_of(Spec.get_l(sl, o))), 1n+Spec.refund_count(Spec.prov_of(Spec.get_l(sl, o))), Spec.amt_of(Spec.prov_of(Spec.get_l(sl, o))), Spec.out_reply(Spec.prov_of(Spec.get_l(sl, o)))}}, Spec.Refund{o, Spec.amt_of(Spec.prov_of(Spec.get_l(sl, o)))} <> Nil{}, hu, hr, ps_a10(Spec.get_l(sl, o), o, rec_true(Spec.rec_of(Spec.pr(s, o)), Spec.Approved{}, hn), hl))

def rpo_core(+od: Spec.OrdRec, +r: Spec.Res, +cc: Nat, +rc: Nat, +am: Nat, +orr: Bool, +o: Nat, +g: Bool, +hn: {Bool.and(Spec.is_approved(r), g) == False{} : Bool}) -> {(Spec.Slot{od, Spec.ProvRec{r, cc, rc, am, orr}}, Nil{}) == Code.with_prov(Code.refund_pick(Spec.ProvRec{r, cc, rc, am, orr}, o, g), od) : Spec.Slot & List<Spec.Effect>}:
  match r g:
    case Spec.NoRec{} _:
      {==}
    case Spec.Declined{} _:
      {==}
    case Spec.Approved{} False{}:
      {==}
    case Spec.Approved{} True{}:
      tf_absurd({(Spec.Slot{od, Spec.ProvRec{r, cc, rc, am, orr}}, Nil{}) == Code.with_prov(Code.refund_pick(Spec.ProvRec{r, cc, rc, am, orr}, o, g), od) : Spec.Slot & List<Spec.Effect>}, hn)

def ps_a10_other(+sl0: Spec.Slot, +o: Nat, +hn: {Bool.and(Spec.is_approved(Spec.rec_of(Spec.prov_of(sl0))), Nat.is_lt(Spec.refund_count(Spec.prov_of(sl0)), Spec.charge_count(Spec.prov_of(sl0)))) == False{} : Bool}) -> {(sl0, Nil{}) == Code.slot_step(sl0, o, Spec.RefundReqRecv{o}) : Spec.Slot & List<Spec.Effect>}:
  match sl0:
    case Spec.Slot{od, Spec.ProvRec{r, cc, rc, am, orr}}:
      rpo_core(od, r, cc, rc, am, orr, o, Nat.is_lt(rc, cc), hn)

def Laws.pin_refund_req_recv_other(s, o, h, hu, hr, hn):
  match s:
    case Spec.State{sl, ou, pu}:
      pin_same(sl, pu, ou, pu, Spec.RefundReqRecv{o}, hu, hr, ps_a10_other(Spec.get_l(sl, o), o, hn))


def recv_down(+sl: +List<Spec.Slot>, up: Bool, +ou: Bool, +pu: Bool, +e: Spec.Ev, +hu: {up == False{} : Bool}) -> {Code.recv(sl, up, ou, pu, e) == (Spec.State{sl, ou, pu}, Nil{}) : Spec.State & List<Spec.Effect>}:
  match up:
    case False{}:
      {==}
    case True{}:
      tf_absurd({Code.recv(sl, True{}, ou, pu, e) == (Spec.State{sl, ou, pu}, Nil{}) : Spec.State & List<Spec.Effect>}, hu)

def go_range(+sl: +List<Spec.Slot>, +o: Nat, +k: Nat, +e: Spec.Ev, +hr: {Nat.is_le(List.length(&2, Spec.Slot, sl), o) == True{} : Bool}) -> {(sl, Nil{}) == Code.go(sl, o, k, e) : +List<Spec.Slot> & List<Spec.Effect>}:
  match sl o:
    case Nil{} _:
      {==}
    case +h <> +t 0n:
      ft_absurd({(h <> t, Nil{}) == Code.go(h <> t, 0n, k, e) : +List<Spec.Slot> & List<Spec.Effect>}, hr)
    case +h <> +t 1n+p:
      %go_range(t, p, k, e, hr) : {(h <> t, Nil{}) == Code.cons_slot(h, _) : +List<Spec.Slot> & List<Spec.Effect>}
      {==}

def recv_range(+sl: +List<Spec.Slot>, up: Bool, +ou: Bool, +pu: Bool, +e: Spec.Ev, +hr: {Nat.is_le(List.length(&2, Spec.Slot, sl), Spec.ev_idx(e)) == True{} : Bool}) -> {Code.recv(sl, up, ou, pu, e) == (Spec.State{sl, ou, pu}, Nil{}) : Spec.State & List<Spec.Effect>}:
  match up:
    case False{}:
      {==}
    case True{}:
      %go_range(sl, Spec.ev_idx(e), Spec.ev_idx(e), e, hr) : {Code.with_state(_, ou, pu) == (Spec.State{sl, ou, pu}, Nil{}) : Spec.State & List<Spec.Effect>}
      {==}


def Laws.pin_rule_d_order_down(s, e, h, he, hu):
  match s:
    case Spec.State{sl, ou, pu}:
      match e:
        case Spec.PlaceOrder{o, a}:
          recv_down(sl, ou, ou, pu, e, hu)
        case Spec.RetryTimeout{o}:
          recv_down(sl, ou, ou, pu, e, hu)
        case Spec.FlushChargeReq{o}:
          recv_down(sl, ou, ou, pu, e, hu)
        case Spec.FlushRefundReq{o}:
          recv_down(sl, ou, ou, pu, e, hu)
        case Spec.PaymentApproved{o}:
          recv_down(sl, ou, ou, pu, e, hu)
        case Spec.PaymentDeclined{o}:
          recv_down(sl, ou, ou, pu, e, hu)
        case Spec.RefundOrder{o}:
          recv_down(sl, ou, ou, pu, e, hu)
        case Spec.ChargeReqRecv{o, a, d}:
          ft_absurd({Code.step(s, e) == (s, Nil{}) : Spec.State & List<Spec.Effect>}, he)
        case Spec.RefundReqRecv{o}:
          ft_absurd({Code.step(s, e) == (s, Nil{}) : Spec.State & List<Spec.Effect>}, he)
        case Spec.FlushReply{o}:
          ft_absurd({Code.step(s, e) == (s, Nil{}) : Spec.State & List<Spec.Effect>}, he)
        case Spec.Crash{svc}:
          ft_absurd({Code.step(s, e) == (s, Nil{}) : Spec.State & List<Spec.Effect>}, he)
        case Spec.Restart{svc}:
          ft_absurd({Code.step(s, e) == (s, Nil{}) : Spec.State & List<Spec.Effect>}, he)

def Laws.pin_rule_d_prov_down(s, e, h, he, hu):
  match s:
    case Spec.State{sl, ou, pu}:
      match e:
        case Spec.PlaceOrder{o, a}:
          ft_absurd({Code.step(s, e) == (s, Nil{}) : Spec.State & List<Spec.Effect>}, he)
        case Spec.RetryTimeout{o}:
          ft_absurd({Code.step(s, e) == (s, Nil{}) : Spec.State & List<Spec.Effect>}, he)
        case Spec.FlushChargeReq{o}:
          ft_absurd({Code.step(s, e) == (s, Nil{}) : Spec.State & List<Spec.Effect>}, he)
        case Spec.FlushRefundReq{o}:
          ft_absurd({Code.step(s, e) == (s, Nil{}) : Spec.State & List<Spec.Effect>}, he)
        case Spec.PaymentApproved{o}:
          ft_absurd({Code.step(s, e) == (s, Nil{}) : Spec.State & List<Spec.Effect>}, he)
        case Spec.PaymentDeclined{o}:
          ft_absurd({Code.step(s, e) == (s, Nil{}) : Spec.State & List<Spec.Effect>}, he)
        case Spec.RefundOrder{o}:
          ft_absurd({Code.step(s, e) == (s, Nil{}) : Spec.State & List<Spec.Effect>}, he)
        case Spec.ChargeReqRecv{o, a, d}:
          recv_down(sl, pu, ou, pu, e, hu)
        case Spec.RefundReqRecv{o}:
          recv_down(sl, pu, ou, pu, e, hu)
        case Spec.FlushReply{o}:
          recv_down(sl, pu, ou, pu, e, hu)
        case Spec.Crash{svc}:
          ft_absurd({Code.step(s, e) == (s, Nil{}) : Spec.State & List<Spec.Effect>}, he)
        case Spec.Restart{svc}:
          ft_absurd({Code.step(s, e) == (s, Nil{}) : Spec.State & List<Spec.Effect>}, he)

def Laws.pin_rule_d_range(s, e, h, he, hr):
  match s:
    case Spec.State{sl, ou, pu}:
      match e:
        case Spec.PlaceOrder{o, a}:
          recv_range(sl, ou, ou, pu, e, hr)
        case Spec.RetryTimeout{o}:
          recv_range(sl, ou, ou, pu, e, hr)
        case Spec.FlushChargeReq{o}:
          recv_range(sl, ou, ou, pu, e, hr)
        case Spec.FlushRefundReq{o}:
          recv_range(sl, ou, ou, pu, e, hr)
        case Spec.PaymentApproved{o}:
          recv_range(sl, ou, ou, pu, e, hr)
        case Spec.PaymentDeclined{o}:
          recv_range(sl, ou, ou, pu, e, hr)
        case Spec.RefundOrder{o}:
          recv_range(sl, ou, ou, pu, e, hr)
        case Spec.ChargeReqRecv{o, a, d}:
          recv_range(sl, pu, ou, pu, e, hr)
        case Spec.RefundReqRecv{o}:
          recv_range(sl, pu, ou, pu, e, hr)
        case Spec.FlushReply{o}:
          recv_range(sl, pu, ou, pu, e, hr)
        case Spec.Crash{svc}:
          tf_absurd({Code.step(s, e) == (s, Nil{}) : Spec.State & List<Spec.Effect>}, he)
        case Spec.Restart{svc}:
          tf_absurd({Code.step(s, e) == (s, Nil{}) : Spec.State & List<Spec.Effect>}, he)
# ----------------------------------------------------------- relation over steps
def legal_refl(+x: Spec.Status) -> {Spec.legal(x, x) == True{} : Bool}:
  match x:
    case Spec.NoOrder{}:
      {==}
    case Spec.AwaitingPayment{}:
      {==}
    case Spec.Paid{}:
      {==}
    case Spec.Failed{}:
      {==}
    case Spec.Refunded{}:
      {==}

def rec_ok_refl(+r: Spec.Res) -> {Spec.rec_ok(r, r) == True{} : Bool}:
  match r:
    case Spec.NoRec{}:
      {==}
    case Spec.Approved{}:
      {==}
    case Spec.Declined{}:
      {==}

def nat_eq_refl(+n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      nat_eq_refl(p)

def nle_succ(+n: Nat) -> {Nat.is_le(n, 1n+n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      nle_succ(p)

def fL(od: Spec.OrdRec, od2: Spec.OrdRec) -> Bool:
  Spec.legal(Spec.status_of(od), Spec.status_of(od2))

def fF(+od: Spec.OrdRec, od2: Spec.OrdRec) -> Bool:
  Spec.imp(Bool.and(Bool.not(Spec.out_refund(od)), Spec.out_refund(od2)), seq(Spec.status_of(od), Spec.Paid{}))

def fT(+od: Spec.OrdRec, od2: Spec.OrdRec) -> Bool:
  Spec.imp(Spec.is_terminal(Spec.status_of(od)), Nat.is_eq(Spec.amount_of(od), Spec.amount_of(od2)))

def ro3(+od: Spec.OrdRec, +od2: Spec.OrdRec) -> Bool:
  Bool.and(fL(od, od2), Bool.and(fF(od, od2), fT(od, od2)))

def ro3_mk(+od: Spec.OrdRec, +od2: Spec.OrdRec, +hL: {fL(od, od2) == True{} : Bool}, +hF: {fF(od, od2) == True{} : Bool}, +hT: {fT(od, od2) == True{} : Bool}) -> {ro3(od, od2) == True{} : Bool}:
  and_i(fL(od, od2), Bool.and(fF(od, od2), fT(od, od2)), hL, and_i(fF(od, od2), fT(od, od2), hF, hT))

def ro3_l(+od: Spec.OrdRec, +od2: Spec.OrdRec, +h: {ro3(od, od2) == True{} : Bool}) -> {fL(od, od2) == True{} : Bool}:
  and_l(fL(od, od2), Bool.and(fF(od, od2), fT(od, od2)), h)

def ro3_f(+od: Spec.OrdRec, +od2: Spec.OrdRec, +h: {ro3(od, od2) == True{} : Bool}) -> {fF(od, od2) == True{} : Bool}:
  and_l(fF(od, od2), fT(od, od2), and_r(fL(od, od2), Bool.and(fF(od, od2), fT(od, od2)), h))

def ro3_t(+od: Spec.OrdRec, +od2: Spec.OrdRec, +h: {ro3(od, od2) == True{} : Bool}) -> {fT(od, od2) == True{} : Bool}:
  and_r(fF(od, od2), fT(od, od2), and_r(fL(od, od2), Bool.and(fF(od, od2), fT(od, od2)), h))

def rpc(+pv: Spec.ProvRec, +pv2: Spec.ProvRec) -> Bool:
  Bool.and(Spec.rec_ok(Spec.rec_of(pv), Spec.rec_of(pv2)), Bool.and(Nat.is_le(Spec.charge_count(pv), Spec.charge_count(pv2)), Nat.is_le(Spec.refund_count(pv), Spec.refund_count(pv2))))

def rpc_mk(+pv: Spec.ProvRec, +pv2: Spec.ProvRec, +h1: {Spec.rec_ok(Spec.rec_of(pv), Spec.rec_of(pv2)) == True{} : Bool}, +h2: {Nat.is_le(Spec.charge_count(pv), Spec.charge_count(pv2)) == True{} : Bool}, +h3: {Nat.is_le(Spec.refund_count(pv), Spec.refund_count(pv2)) == True{} : Bool}) -> {rpc(pv, pv2) == True{} : Bool}:
  and_i(Spec.rec_ok(Spec.rec_of(pv), Spec.rec_of(pv2)), Bool.and(Nat.is_le(Spec.charge_count(pv), Spec.charge_count(pv2)), Nat.is_le(Spec.refund_count(pv), Spec.refund_count(pv2))), h1, and_i(Nat.is_le(Spec.charge_count(pv), Spec.charge_count(pv2)), Nat.is_le(Spec.refund_count(pv), Spec.refund_count(pv2)), h2, h3))

def rpc_refl(+pv: Spec.ProvRec) -> {rpc(pv, pv) == True{} : Bool}:
  rpc_mk(pv, pv, rec_ok_refl(Spec.rec_of(pv)), nle_refl(Spec.charge_count(pv)), nle_refl(Spec.refund_count(pv)))

def fF_refl(+od: Spec.OrdRec) -> {fF(od, od) == True{} : Bool}:
  match od:
    case Spec.OrdRec{x, am, oc, True{}}:
      {==}
    case Spec.OrdRec{x, am, oc, False{}}:
      {==}

def fT_refl(+od: Spec.OrdRec) -> {fT(od, od) == True{} : Bool}:
  match od:
    case Spec.OrdRec{Spec.NoOrder{}, am, oc, orf}:
      {==}
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, oc, orf}:
      {==}
    case Spec.OrdRec{Spec.Paid{}, am, oc, orf}:
      {==}
    case Spec.OrdRec{Spec.Failed{}, am, oc, orf}:
      nat_eq_refl(am)
    case Spec.OrdRec{Spec.Refunded{}, am, oc, orf}:
      nat_eq_refl(am)

def ro3_refl(+od: Spec.OrdRec) -> {ro3(od, od) == True{} : Bool}:
  ro3_mk(od, od, legal_refl(Spec.status_of(od)), fF_refl(od), fT_refl(od))

def rel(+a: Spec.Slot, +b: Spec.Slot) -> Bool:
  Bool.and(ro3(Spec.ord_of(a), Spec.ord_of(b)), rpc(Spec.prov_of(a), Spec.prov_of(b)))

def rel_refl(+sl: Spec.Slot) -> {rel(sl, sl) == True{} : Bool}:
  and_i(ro3(Spec.ord_of(sl), Spec.ord_of(sl)), rpc(Spec.prov_of(sl), Spec.prov_of(sl)), ro3_refl(Spec.ord_of(sl)), rpc_refl(Spec.prov_of(sl)))

def rel_ro(+a: Spec.Slot, +b: Spec.Slot, +h: {rel(a, b) == True{} : Bool}) -> {ro3(Spec.ord_of(a), Spec.ord_of(b)) == True{} : Bool}:
  and_l(ro3(Spec.ord_of(a), Spec.ord_of(b)), rpc(Spec.prov_of(a), Spec.prov_of(b)), h)

def rel_rp(+a: Spec.Slot, +b: Spec.Slot, +h: {rel(a, b) == True{} : Bool}) -> {rpc(Spec.prov_of(a), Spec.prov_of(b)) == True{} : Bool}:
  and_r(ro3(Spec.ord_of(a), Spec.ord_of(b)), rpc(Spec.prov_of(a), Spec.prov_of(b)), h)

def rel_wo(+od: Spec.OrdRec, r: Spec.OrdRec & List<Spec.Effect>, +pv: Spec.ProvRec, +hO: {ro3(od, fo(r)) == True{} : Bool}) -> {rel(Spec.Slot{od, pv}, fs(Code.with_ord(r, pv))) == True{} : Bool}:
  match r:
    case (+od2, fx):
      and_i(ro3(od, od2), rpc(pv, pv), hO, rpc_refl(pv))

def rel_wp(+pv: Spec.ProvRec, r: Spec.ProvRec & List<Spec.Effect>, +od: Spec.OrdRec, +hP: {rpc(pv, fp(r)) == True{} : Bool}) -> {rel(Spec.Slot{od, pv}, fs(Code.with_prov(r, od))) == True{} : Bool}:
  match r:
    case (+pv2, fx):
      and_i(ro3(od, od), rpc(pv, pv2), ro3_refl(od), hP)

def rp_flush_reply(+pv: Spec.ProvRec, +k: Nat) -> {rpc(pv, fp(Code.flush_reply(pv, k))) == True{} : Bool}:
  match pv:
    case Spec.ProvRec{Spec.NoRec{}, cc, rc, am, True{}}:
      rpc_mk(pv, fp(Code.flush_reply(pv, k)), {==}, nle_refl(Spec.charge_count(pv)), nle_refl(Spec.refund_count(pv)))
    case Spec.ProvRec{Spec.NoRec{}, cc, rc, am, False{}}:
      rpc_mk(pv, fp(Code.flush_reply(pv, k)), {==}, nle_refl(Spec.charge_count(pv)), nle_refl(Spec.refund_count(pv)))
    case Spec.ProvRec{Spec.Approved{}, cc, rc, am, True{}}:
      rpc_mk(pv, fp(Code.flush_reply(pv, k)), {==}, nle_refl(Spec.charge_count(pv)), nle_refl(Spec.refund_count(pv)))
    case Spec.ProvRec{Spec.Approved{}, cc, rc, am, False{}}:
      rpc_mk(pv, fp(Code.flush_reply(pv, k)), {==}, nle_refl(Spec.charge_count(pv)), nle_refl(Spec.refund_count(pv)))
    case Spec.ProvRec{Spec.Declined{}, cc, rc, am, True{}}:
      rpc_mk(pv, fp(Code.flush_reply(pv, k)), {==}, nle_refl(Spec.charge_count(pv)), nle_refl(Spec.refund_count(pv)))
    case Spec.ProvRec{Spec.Declined{}, cc, rc, am, False{}}:
      rpc_mk(pv, fp(Code.flush_reply(pv, k)), {==}, nle_refl(Spec.charge_count(pv)), nle_refl(Spec.refund_count(pv)))

def rp_charge_recv(+pv: Spec.ProvRec, +k: Nat, +a: Nat, +d: Spec.Dec) -> {rpc(pv, fp(Code.charge_recv(pv, k, a, d))) == True{} : Bool}:
  match pv a d:
    case Spec.ProvRec{Spec.NoRec{}, cc, rc, am, orr} 0n _:
      rpc_mk(pv, fp(Code.charge_recv(pv, k, a, d)), {==}, nle_refl(Spec.charge_count(pv)), nle_refl(Spec.refund_count(pv)))
    case Spec.ProvRec{Spec.NoRec{}, cc, rc, am, orr} 1n+pa Spec.Approve{}:
      rpc_mk(pv, fp(Code.charge_recv(pv, k, a, d)), {==}, nle_succ(Spec.charge_count(pv)), nle_refl(Spec.refund_count(pv)))
    case Spec.ProvRec{Spec.NoRec{}, cc, rc, am, orr} 1n+pa Spec.Decline{}:
      rpc_mk(pv, fp(Code.charge_recv(pv, k, a, d)), {==}, nle_refl(Spec.charge_count(pv)), nle_refl(Spec.refund_count(pv)))
    case Spec.ProvRec{Spec.Approved{}, cc, rc, am, orr} 0n _:
      rpc_mk(pv, fp(Code.charge_recv(pv, k, a, d)), {==}, nle_refl(Spec.charge_count(pv)), nle_refl(Spec.refund_count(pv)))
    case Spec.ProvRec{Spec.Approved{}, cc, rc, am, orr} 1n+pa _:
      rpc_mk(pv, fp(Code.charge_recv(pv, k, a, d)), {==}, nle_refl(Spec.charge_count(pv)), nle_refl(Spec.refund_count(pv)))
    case Spec.ProvRec{Spec.Declined{}, cc, rc, am, orr} 0n _:
      rpc_mk(pv, fp(Code.charge_recv(pv, k, a, d)), {==}, nle_refl(Spec.charge_count(pv)), nle_refl(Spec.refund_count(pv)))
    case Spec.ProvRec{Spec.Declined{}, cc, rc, am, orr} 1n+pa _:
      rpc_mk(pv, fp(Code.charge_recv(pv, k, a, d)), {==}, nle_refl(Spec.charge_count(pv)), nle_refl(Spec.refund_count(pv)))

def rp_rp(+pv: Spec.ProvRec, +k: Nat, +g: Bool) -> {rpc(pv, fp(Code.refund_pick(pv, k, g))) == True{} : Bool}:
  match pv g:
    case Spec.ProvRec{Spec.NoRec{}, cc, rc, am, orr} _:
      rpc_mk(pv, fp(Code.refund_pick(pv, k, g)), {==}, nle_refl(Spec.charge_count(pv)), nle_refl(Spec.refund_count(pv)))
    case Spec.ProvRec{Spec.Declined{}, cc, rc, am, orr} _:
      rpc_mk(pv, fp(Code.refund_pick(pv, k, g)), {==}, nle_refl(Spec.charge_count(pv)), nle_refl(Spec.refund_count(pv)))
    case Spec.ProvRec{Spec.Approved{}, cc, rc, am, orr} False{}:
      rpc_mk(pv, fp(Code.refund_pick(pv, k, g)), {==}, nle_refl(Spec.charge_count(pv)), nle_refl(Spec.refund_count(pv)))
    case Spec.ProvRec{Spec.Approved{}, cc, rc, am, orr} True{}:
      rpc_mk(pv, fp(Code.refund_pick(pv, k, g)), {==}, nle_refl(Spec.charge_count(pv)), nle_succ(Spec.refund_count(pv)))

def ro_place(+od: Spec.OrdRec, +a: Nat) -> {ro3(od, fo(Code.place(od, a))) == True{} : Bool}:
  match od a:
    case Spec.OrdRec{Spec.NoOrder{}, am, True{}, True{}} 0n:
      ro3_mk(od, fo(Code.place(od, a)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.NoOrder{}, am, True{}, True{}} 1n+pa:
      ro3_mk(od, fo(Code.place(od, a)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.NoOrder{}, am, True{}, False{}} 0n:
      ro3_mk(od, fo(Code.place(od, a)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.NoOrder{}, am, True{}, False{}} 1n+pa:
      ro3_mk(od, fo(Code.place(od, a)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.NoOrder{}, am, False{}, True{}} 0n:
      ro3_mk(od, fo(Code.place(od, a)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.NoOrder{}, am, False{}, True{}} 1n+pa:
      ro3_mk(od, fo(Code.place(od, a)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.NoOrder{}, am, False{}, False{}} 0n:
      ro3_mk(od, fo(Code.place(od, a)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.NoOrder{}, am, False{}, False{}} 1n+pa:
      ro3_mk(od, fo(Code.place(od, a)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, True{}, True{}} _:
      ro3_mk(od, fo(Code.place(od, a)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, True{}, False{}} _:
      ro3_mk(od, fo(Code.place(od, a)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, False{}, True{}} _:
      ro3_mk(od, fo(Code.place(od, a)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, False{}, False{}} _:
      ro3_mk(od, fo(Code.place(od, a)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.Paid{}, am, True{}, True{}} _:
      ro3_mk(od, fo(Code.place(od, a)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.Paid{}, am, True{}, False{}} _:
      ro3_mk(od, fo(Code.place(od, a)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.Paid{}, am, False{}, True{}} _:
      ro3_mk(od, fo(Code.place(od, a)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.Paid{}, am, False{}, False{}} _:
      ro3_mk(od, fo(Code.place(od, a)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.Failed{}, am, True{}, True{}} _:
      ro3_mk(od, fo(Code.place(od, a)), {==}, {==}, nat_eq_refl(am))
    case Spec.OrdRec{Spec.Failed{}, am, True{}, False{}} _:
      ro3_mk(od, fo(Code.place(od, a)), {==}, {==}, nat_eq_refl(am))
    case Spec.OrdRec{Spec.Failed{}, am, False{}, True{}} _:
      ro3_mk(od, fo(Code.place(od, a)), {==}, {==}, nat_eq_refl(am))
    case Spec.OrdRec{Spec.Failed{}, am, False{}, False{}} _:
      ro3_mk(od, fo(Code.place(od, a)), {==}, {==}, nat_eq_refl(am))
    case Spec.OrdRec{Spec.Refunded{}, am, True{}, True{}} _:
      ro3_mk(od, fo(Code.place(od, a)), {==}, {==}, nat_eq_refl(am))
    case Spec.OrdRec{Spec.Refunded{}, am, True{}, False{}} _:
      ro3_mk(od, fo(Code.place(od, a)), {==}, {==}, nat_eq_refl(am))
    case Spec.OrdRec{Spec.Refunded{}, am, False{}, True{}} _:
      ro3_mk(od, fo(Code.place(od, a)), {==}, {==}, nat_eq_refl(am))
    case Spec.OrdRec{Spec.Refunded{}, am, False{}, False{}} _:
      ro3_mk(od, fo(Code.place(od, a)), {==}, {==}, nat_eq_refl(am))

def ro_retry(+od: Spec.OrdRec) -> {ro3(od, fo(Code.retry(od))) == True{} : Bool}:
  match od:
    case Spec.OrdRec{Spec.NoOrder{}, am, True{}, True{}}:
      ro3_mk(od, fo(Code.retry(od)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.NoOrder{}, am, True{}, False{}}:
      ro3_mk(od, fo(Code.retry(od)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.NoOrder{}, am, False{}, True{}}:
      ro3_mk(od, fo(Code.retry(od)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.NoOrder{}, am, False{}, False{}}:
      ro3_mk(od, fo(Code.retry(od)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, True{}, True{}}:
      ro3_mk(od, fo(Code.retry(od)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, True{}, False{}}:
      ro3_mk(od, fo(Code.retry(od)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, False{}, True{}}:
      ro3_mk(od, fo(Code.retry(od)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, False{}, False{}}:
      ro3_mk(od, fo(Code.retry(od)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.Paid{}, am, True{}, True{}}:
      ro3_mk(od, fo(Code.retry(od)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.Paid{}, am, True{}, False{}}:
      ro3_mk(od, fo(Code.retry(od)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.Paid{}, am, False{}, True{}}:
      ro3_mk(od, fo(Code.retry(od)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.Paid{}, am, False{}, False{}}:
      ro3_mk(od, fo(Code.retry(od)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.Failed{}, am, True{}, True{}}:
      ro3_mk(od, fo(Code.retry(od)), {==}, {==}, nat_eq_refl(am))
    case Spec.OrdRec{Spec.Failed{}, am, True{}, False{}}:
      ro3_mk(od, fo(Code.retry(od)), {==}, {==}, nat_eq_refl(am))
    case Spec.OrdRec{Spec.Failed{}, am, False{}, True{}}:
      ro3_mk(od, fo(Code.retry(od)), {==}, {==}, nat_eq_refl(am))
    case Spec.OrdRec{Spec.Failed{}, am, False{}, False{}}:
      ro3_mk(od, fo(Code.retry(od)), {==}, {==}, nat_eq_refl(am))
    case Spec.OrdRec{Spec.Refunded{}, am, True{}, True{}}:
      ro3_mk(od, fo(Code.retry(od)), {==}, {==}, nat_eq_refl(am))
    case Spec.OrdRec{Spec.Refunded{}, am, True{}, False{}}:
      ro3_mk(od, fo(Code.retry(od)), {==}, {==}, nat_eq_refl(am))
    case Spec.OrdRec{Spec.Refunded{}, am, False{}, True{}}:
      ro3_mk(od, fo(Code.retry(od)), {==}, {==}, nat_eq_refl(am))
    case Spec.OrdRec{Spec.Refunded{}, am, False{}, False{}}:
      ro3_mk(od, fo(Code.retry(od)), {==}, {==}, nat_eq_refl(am))

def ro_flush_charge(+od: Spec.OrdRec, +k: Nat) -> {ro3(od, fo(Code.flush_charge(od, k))) == True{} : Bool}:
  match od:
    case Spec.OrdRec{Spec.NoOrder{}, am, True{}, True{}}:
      ro3_mk(od, fo(Code.flush_charge(od, k)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.NoOrder{}, am, True{}, False{}}:
      ro3_mk(od, fo(Code.flush_charge(od, k)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.NoOrder{}, am, False{}, True{}}:
      ro3_mk(od, fo(Code.flush_charge(od, k)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.NoOrder{}, am, False{}, False{}}:
      ro3_mk(od, fo(Code.flush_charge(od, k)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, True{}, True{}}:
      ro3_mk(od, fo(Code.flush_charge(od, k)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, True{}, False{}}:
      ro3_mk(od, fo(Code.flush_charge(od, k)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, False{}, True{}}:
      ro3_mk(od, fo(Code.flush_charge(od, k)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, False{}, False{}}:
      ro3_mk(od, fo(Code.flush_charge(od, k)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.Paid{}, am, True{}, True{}}:
      ro3_mk(od, fo(Code.flush_charge(od, k)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.Paid{}, am, True{}, False{}}:
      ro3_mk(od, fo(Code.flush_charge(od, k)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.Paid{}, am, False{}, True{}}:
      ro3_mk(od, fo(Code.flush_charge(od, k)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.Paid{}, am, False{}, False{}}:
      ro3_mk(od, fo(Code.flush_charge(od, k)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.Failed{}, am, True{}, True{}}:
      ro3_mk(od, fo(Code.flush_charge(od, k)), {==}, {==}, nat_eq_refl(am))
    case Spec.OrdRec{Spec.Failed{}, am, True{}, False{}}:
      ro3_mk(od, fo(Code.flush_charge(od, k)), {==}, {==}, nat_eq_refl(am))
    case Spec.OrdRec{Spec.Failed{}, am, False{}, True{}}:
      ro3_mk(od, fo(Code.flush_charge(od, k)), {==}, {==}, nat_eq_refl(am))
    case Spec.OrdRec{Spec.Failed{}, am, False{}, False{}}:
      ro3_mk(od, fo(Code.flush_charge(od, k)), {==}, {==}, nat_eq_refl(am))
    case Spec.OrdRec{Spec.Refunded{}, am, True{}, True{}}:
      ro3_mk(od, fo(Code.flush_charge(od, k)), {==}, {==}, nat_eq_refl(am))
    case Spec.OrdRec{Spec.Refunded{}, am, True{}, False{}}:
      ro3_mk(od, fo(Code.flush_charge(od, k)), {==}, {==}, nat_eq_refl(am))
    case Spec.OrdRec{Spec.Refunded{}, am, False{}, True{}}:
      ro3_mk(od, fo(Code.flush_charge(od, k)), {==}, {==}, nat_eq_refl(am))
    case Spec.OrdRec{Spec.Refunded{}, am, False{}, False{}}:
      ro3_mk(od, fo(Code.flush_charge(od, k)), {==}, {==}, nat_eq_refl(am))

def ro_flush_refund(+od: Spec.OrdRec, +k: Nat) -> {ro3(od, fo(Code.flush_refund(od, k))) == True{} : Bool}:
  match od:
    case Spec.OrdRec{Spec.NoOrder{}, am, True{}, True{}}:
      ro3_mk(od, fo(Code.flush_refund(od, k)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.NoOrder{}, am, True{}, False{}}:
      ro3_mk(od, fo(Code.flush_refund(od, k)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.NoOrder{}, am, False{}, True{}}:
      ro3_mk(od, fo(Code.flush_refund(od, k)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.NoOrder{}, am, False{}, False{}}:
      ro3_mk(od, fo(Code.flush_refund(od, k)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, True{}, True{}}:
      ro3_mk(od, fo(Code.flush_refund(od, k)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, True{}, False{}}:
      ro3_mk(od, fo(Code.flush_refund(od, k)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, False{}, True{}}:
      ro3_mk(od, fo(Code.flush_refund(od, k)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, False{}, False{}}:
      ro3_mk(od, fo(Code.flush_refund(od, k)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.Paid{}, am, True{}, True{}}:
      ro3_mk(od, fo(Code.flush_refund(od, k)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.Paid{}, am, True{}, False{}}:
      ro3_mk(od, fo(Code.flush_refund(od, k)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.Paid{}, am, False{}, True{}}:
      ro3_mk(od, fo(Code.flush_refund(od, k)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.Paid{}, am, False{}, False{}}:
      ro3_mk(od, fo(Code.flush_refund(od, k)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.Failed{}, am, True{}, True{}}:
      ro3_mk(od, fo(Code.flush_refund(od, k)), {==}, {==}, nat_eq_refl(am))
    case Spec.OrdRec{Spec.Failed{}, am, True{}, False{}}:
      ro3_mk(od, fo(Code.flush_refund(od, k)), {==}, {==}, nat_eq_refl(am))
    case Spec.OrdRec{Spec.Failed{}, am, False{}, True{}}:
      ro3_mk(od, fo(Code.flush_refund(od, k)), {==}, {==}, nat_eq_refl(am))
    case Spec.OrdRec{Spec.Failed{}, am, False{}, False{}}:
      ro3_mk(od, fo(Code.flush_refund(od, k)), {==}, {==}, nat_eq_refl(am))
    case Spec.OrdRec{Spec.Refunded{}, am, True{}, True{}}:
      ro3_mk(od, fo(Code.flush_refund(od, k)), {==}, {==}, nat_eq_refl(am))
    case Spec.OrdRec{Spec.Refunded{}, am, True{}, False{}}:
      ro3_mk(od, fo(Code.flush_refund(od, k)), {==}, {==}, nat_eq_refl(am))
    case Spec.OrdRec{Spec.Refunded{}, am, False{}, True{}}:
      ro3_mk(od, fo(Code.flush_refund(od, k)), {==}, {==}, nat_eq_refl(am))
    case Spec.OrdRec{Spec.Refunded{}, am, False{}, False{}}:
      ro3_mk(od, fo(Code.flush_refund(od, k)), {==}, {==}, nat_eq_refl(am))

def ro_pay_ok(+od: Spec.OrdRec) -> {ro3(od, fo(Code.pay_ok(od))) == True{} : Bool}:
  match od:
    case Spec.OrdRec{Spec.NoOrder{}, am, True{}, True{}}:
      ro3_mk(od, fo(Code.pay_ok(od)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.NoOrder{}, am, True{}, False{}}:
      ro3_mk(od, fo(Code.pay_ok(od)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.NoOrder{}, am, False{}, True{}}:
      ro3_mk(od, fo(Code.pay_ok(od)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.NoOrder{}, am, False{}, False{}}:
      ro3_mk(od, fo(Code.pay_ok(od)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, True{}, True{}}:
      ro3_mk(od, fo(Code.pay_ok(od)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, True{}, False{}}:
      ro3_mk(od, fo(Code.pay_ok(od)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, False{}, True{}}:
      ro3_mk(od, fo(Code.pay_ok(od)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, False{}, False{}}:
      ro3_mk(od, fo(Code.pay_ok(od)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.Paid{}, am, True{}, True{}}:
      ro3_mk(od, fo(Code.pay_ok(od)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.Paid{}, am, True{}, False{}}:
      ro3_mk(od, fo(Code.pay_ok(od)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.Paid{}, am, False{}, True{}}:
      ro3_mk(od, fo(Code.pay_ok(od)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.Paid{}, am, False{}, False{}}:
      ro3_mk(od, fo(Code.pay_ok(od)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.Failed{}, am, True{}, True{}}:
      ro3_mk(od, fo(Code.pay_ok(od)), {==}, {==}, nat_eq_refl(am))
    case Spec.OrdRec{Spec.Failed{}, am, True{}, False{}}:
      ro3_mk(od, fo(Code.pay_ok(od)), {==}, {==}, nat_eq_refl(am))
    case Spec.OrdRec{Spec.Failed{}, am, False{}, True{}}:
      ro3_mk(od, fo(Code.pay_ok(od)), {==}, {==}, nat_eq_refl(am))
    case Spec.OrdRec{Spec.Failed{}, am, False{}, False{}}:
      ro3_mk(od, fo(Code.pay_ok(od)), {==}, {==}, nat_eq_refl(am))
    case Spec.OrdRec{Spec.Refunded{}, am, True{}, True{}}:
      ro3_mk(od, fo(Code.pay_ok(od)), {==}, {==}, nat_eq_refl(am))
    case Spec.OrdRec{Spec.Refunded{}, am, True{}, False{}}:
      ro3_mk(od, fo(Code.pay_ok(od)), {==}, {==}, nat_eq_refl(am))
    case Spec.OrdRec{Spec.Refunded{}, am, False{}, True{}}:
      ro3_mk(od, fo(Code.pay_ok(od)), {==}, {==}, nat_eq_refl(am))
    case Spec.OrdRec{Spec.Refunded{}, am, False{}, False{}}:
      ro3_mk(od, fo(Code.pay_ok(od)), {==}, {==}, nat_eq_refl(am))

def ro_pay_no(+od: Spec.OrdRec) -> {ro3(od, fo(Code.pay_no(od))) == True{} : Bool}:
  match od:
    case Spec.OrdRec{Spec.NoOrder{}, am, True{}, True{}}:
      ro3_mk(od, fo(Code.pay_no(od)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.NoOrder{}, am, True{}, False{}}:
      ro3_mk(od, fo(Code.pay_no(od)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.NoOrder{}, am, False{}, True{}}:
      ro3_mk(od, fo(Code.pay_no(od)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.NoOrder{}, am, False{}, False{}}:
      ro3_mk(od, fo(Code.pay_no(od)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, True{}, True{}}:
      ro3_mk(od, fo(Code.pay_no(od)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, True{}, False{}}:
      ro3_mk(od, fo(Code.pay_no(od)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, False{}, True{}}:
      ro3_mk(od, fo(Code.pay_no(od)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, False{}, False{}}:
      ro3_mk(od, fo(Code.pay_no(od)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.Paid{}, am, True{}, True{}}:
      ro3_mk(od, fo(Code.pay_no(od)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.Paid{}, am, True{}, False{}}:
      ro3_mk(od, fo(Code.pay_no(od)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.Paid{}, am, False{}, True{}}:
      ro3_mk(od, fo(Code.pay_no(od)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.Paid{}, am, False{}, False{}}:
      ro3_mk(od, fo(Code.pay_no(od)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.Failed{}, am, True{}, True{}}:
      ro3_mk(od, fo(Code.pay_no(od)), {==}, {==}, nat_eq_refl(am))
    case Spec.OrdRec{Spec.Failed{}, am, True{}, False{}}:
      ro3_mk(od, fo(Code.pay_no(od)), {==}, {==}, nat_eq_refl(am))
    case Spec.OrdRec{Spec.Failed{}, am, False{}, True{}}:
      ro3_mk(od, fo(Code.pay_no(od)), {==}, {==}, nat_eq_refl(am))
    case Spec.OrdRec{Spec.Failed{}, am, False{}, False{}}:
      ro3_mk(od, fo(Code.pay_no(od)), {==}, {==}, nat_eq_refl(am))
    case Spec.OrdRec{Spec.Refunded{}, am, True{}, True{}}:
      ro3_mk(od, fo(Code.pay_no(od)), {==}, {==}, nat_eq_refl(am))
    case Spec.OrdRec{Spec.Refunded{}, am, True{}, False{}}:
      ro3_mk(od, fo(Code.pay_no(od)), {==}, {==}, nat_eq_refl(am))
    case Spec.OrdRec{Spec.Refunded{}, am, False{}, True{}}:
      ro3_mk(od, fo(Code.pay_no(od)), {==}, {==}, nat_eq_refl(am))
    case Spec.OrdRec{Spec.Refunded{}, am, False{}, False{}}:
      ro3_mk(od, fo(Code.pay_no(od)), {==}, {==}, nat_eq_refl(am))

def ro_refund_order(+od: Spec.OrdRec) -> {ro3(od, fo(Code.refund_order(od))) == True{} : Bool}:
  match od:
    case Spec.OrdRec{Spec.NoOrder{}, am, True{}, True{}}:
      ro3_mk(od, fo(Code.refund_order(od)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.NoOrder{}, am, True{}, False{}}:
      ro3_mk(od, fo(Code.refund_order(od)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.NoOrder{}, am, False{}, True{}}:
      ro3_mk(od, fo(Code.refund_order(od)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.NoOrder{}, am, False{}, False{}}:
      ro3_mk(od, fo(Code.refund_order(od)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, True{}, True{}}:
      ro3_mk(od, fo(Code.refund_order(od)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, True{}, False{}}:
      ro3_mk(od, fo(Code.refund_order(od)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, False{}, True{}}:
      ro3_mk(od, fo(Code.refund_order(od)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.AwaitingPayment{}, am, False{}, False{}}:
      ro3_mk(od, fo(Code.refund_order(od)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.Paid{}, am, True{}, True{}}:
      ro3_mk(od, fo(Code.refund_order(od)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.Paid{}, am, True{}, False{}}:
      ro3_mk(od, fo(Code.refund_order(od)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.Paid{}, am, False{}, True{}}:
      ro3_mk(od, fo(Code.refund_order(od)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.Paid{}, am, False{}, False{}}:
      ro3_mk(od, fo(Code.refund_order(od)), {==}, {==}, {==})
    case Spec.OrdRec{Spec.Failed{}, am, True{}, True{}}:
      ro3_mk(od, fo(Code.refund_order(od)), {==}, {==}, nat_eq_refl(am))
    case Spec.OrdRec{Spec.Failed{}, am, True{}, False{}}:
      ro3_mk(od, fo(Code.refund_order(od)), {==}, {==}, nat_eq_refl(am))
    case Spec.OrdRec{Spec.Failed{}, am, False{}, True{}}:
      ro3_mk(od, fo(Code.refund_order(od)), {==}, {==}, nat_eq_refl(am))
    case Spec.OrdRec{Spec.Failed{}, am, False{}, False{}}:
      ro3_mk(od, fo(Code.refund_order(od)), {==}, {==}, nat_eq_refl(am))
    case Spec.OrdRec{Spec.Refunded{}, am, True{}, True{}}:
      ro3_mk(od, fo(Code.refund_order(od)), {==}, {==}, nat_eq_refl(am))
    case Spec.OrdRec{Spec.Refunded{}, am, True{}, False{}}:
      ro3_mk(od, fo(Code.refund_order(od)), {==}, {==}, nat_eq_refl(am))
    case Spec.OrdRec{Spec.Refunded{}, am, False{}, True{}}:
      ro3_mk(od, fo(Code.refund_order(od)), {==}, {==}, nat_eq_refl(am))
    case Spec.OrdRec{Spec.Refunded{}, am, False{}, False{}}:
      ro3_mk(od, fo(Code.refund_order(od)), {==}, {==}, nat_eq_refl(am))

def rel_slot_step(+sl: Spec.Slot, +k: Nat, +e: Spec.Ev) -> {rel(sl, fs(Code.slot_step(sl, k, e))) == True{} : Bool}:
  match sl e:
    case Spec.Slot{od, pv} Spec.PlaceOrder{_, a}:
      rel_wo(od, Code.place(od, a), pv, ro_place(od, a))
    case Spec.Slot{od, pv} Spec.RetryTimeout{_}:
      rel_wo(od, Code.retry(od), pv, ro_retry(od))
    case Spec.Slot{od, pv} Spec.FlushChargeReq{_}:
      rel_wo(od, Code.flush_charge(od, k), pv, ro_flush_charge(od, k))
    case Spec.Slot{od, pv} Spec.FlushRefundReq{_}:
      rel_wo(od, Code.flush_refund(od, k), pv, ro_flush_refund(od, k))
    case Spec.Slot{od, pv} Spec.PaymentApproved{_}:
      rel_wo(od, Code.pay_ok(od), pv, ro_pay_ok(od))
    case Spec.Slot{od, pv} Spec.PaymentDeclined{_}:
      rel_wo(od, Code.pay_no(od), pv, ro_pay_no(od))
    case Spec.Slot{od, pv} Spec.RefundOrder{_}:
      rel_wo(od, Code.refund_order(od), pv, ro_refund_order(od))
    case Spec.Slot{od, pv} Spec.ChargeReqRecv{_, a, d}:
      rel_wp(pv, Code.charge_recv(pv, k, a, d), od, rp_charge_recv(pv, k, a, d))
    case Spec.Slot{od, pv} Spec.RefundReqRecv{_}:
      rel_wp(pv, Code.refund_recv(pv, k), od, rp_rp(pv, k, Nat.is_lt(Spec.refund_count(pv), Spec.charge_count(pv))))
    case Spec.Slot{od, pv} Spec.FlushReply{_}:
      rel_wp(pv, Code.flush_reply(pv, k), od, rp_flush_reply(pv, k))
    case Spec.Slot{od, pv} Spec.Crash{_}:
      rel_refl(sl)
    case Spec.Slot{od, pv} Spec.Restart{_}:
      rel_refl(sl)

def rel_set(+l: +List<Spec.Slot>, +o: Nat, +x: Spec.Slot, +q: Nat, +hx: {rel(Spec.get_l(l, o), x) == True{} : Bool}) -> {rel(Spec.get_l(l, q), Spec.get_l(Spec.set(l, o, x), q)) == True{} : Bool}:
  match l o q:
    case Nil{} _ _:
      rel_refl(Spec.default_slot())
    case +h <> +t 0n 0n:
      hx
    case +h <> +t 0n 1n+q2:
      rel_refl(Spec.get_l(t, q2))
    case +h <> +t 1n+o2 0n:
      rel_refl(h)
    case +h <> +t 1n+o2 1n+q2:
      rel_set(t, o2, x, q2, hx)

def ws_get(r: +List<Spec.Slot> & List<Spec.Effect>, +ou: Bool, +pu: Bool, +q: Nat) -> {Spec.get_l(fl(r), q) == Spec.get(Code.fst(Code.with_state(r, ou, pu)), q) : Spec.Slot}:
  match r:
    case (sl2, fx):
      {==}

def rel_recv(+sl: +List<Spec.Slot>, up: Bool, +ou: Bool, +pu: Bool, +e: Spec.Ev, +q: Nat) -> {rel(Spec.get_l(sl, q), Spec.get(Code.fst(Code.recv(sl, up, ou, pu, e)), q)) == True{} : Bool}:
  match up:
    case False{}:
      rel_refl(Spec.get_l(sl, q))
    case True{}:
      %ws_get(Code.go(sl, Spec.ev_idx(e), Spec.ev_idx(e), e), ou, pu, q) : {rel(Spec.get_l(sl, q), _) == True{} : Bool}
      %go_fst(sl, Spec.ev_idx(e), Spec.ev_idx(e), e) : {rel(Spec.get_l(sl, q), Spec.get_l(_, q)) == True{} : Bool}
      rel_set(sl, Spec.ev_idx(e), fs(Code.slot_step(Spec.get_l(sl, Spec.ev_idx(e)), Spec.ev_idx(e), e)), q, rel_slot_step(Spec.get_l(sl, Spec.ev_idx(e)), Spec.ev_idx(e), e))

def rel_step(+s: Spec.State, +e: Spec.Ev, +q: Nat) -> {rel(Spec.get(s, q), Spec.get(Code.fst(Code.step(s, e)), q)) == True{} : Bool}:
  match s:
    case Spec.State{sl, ou, pu}:
      match e:
        case Spec.PlaceOrder{o, a}:
          rel_recv(sl, ou, ou, pu, e, q)
        case Spec.RetryTimeout{o}:
          rel_recv(sl, ou, ou, pu, e, q)
        case Spec.FlushChargeReq{o}:
          rel_recv(sl, ou, ou, pu, e, q)
        case Spec.FlushRefundReq{o}:
          rel_recv(sl, ou, ou, pu, e, q)
        case Spec.PaymentApproved{o}:
          rel_recv(sl, ou, ou, pu, e, q)
        case Spec.PaymentDeclined{o}:
          rel_recv(sl, ou, ou, pu, e, q)
        case Spec.RefundOrder{o}:
          rel_recv(sl, ou, ou, pu, e, q)
        case Spec.ChargeReqRecv{o, a, d}:
          rel_recv(sl, pu, ou, pu, e, q)
        case Spec.RefundReqRecv{o}:
          rel_recv(sl, pu, ou, pu, e, q)
        case Spec.FlushReply{o}:
          rel_recv(sl, pu, ou, pu, e, q)
        case Spec.Crash{svc}:
          match svc:
            case Spec.OrderSvc{}:
              rel_refl(Spec.get_l(sl, q))
            case Spec.Provider{}:
              rel_refl(Spec.get_l(sl, q))
        case Spec.Restart{svc}:
          match svc:
            case Spec.OrderSvc{}:
              rel_refl(Spec.get_l(sl, q))
            case Spec.Provider{}:
              rel_refl(Spec.get_l(sl, q))

def Laws.pin_legal_transitions(s, e, o, h):
  ro3_l(Spec.ord_of(Spec.get(s, o)), Spec.ord_of(Spec.get(Code.fst(Code.step(s, e)), o)), rel_ro(Spec.get(s, o), Spec.get(Code.fst(Code.step(s, e)), o), rel_step(s, e, o)))

def Laws.pin_prov_rec_stable(s, e, o, h):
  rel_rp(Spec.get(s, o), Spec.get(Code.fst(Code.step(s, e)), o), rel_step(s, e, o))

def p2b_a_st(+x: Spec.Status, +y: Spec.Status, +hl: {Spec.legal(x, y) == True{} : Bool}, hn: {x != Spec.Refunded{} : Spec.Status}, +hy: {seq(y, Spec.Refunded{}) == True{} : Bool}) -> {x == Spec.Paid{} : Spec.Status}:
  match x y:
    case Spec.NoOrder{} Spec.NoOrder{}:
      ft_absurd({x == Spec.Paid{} : Spec.Status}, hy)
    case Spec.NoOrder{} Spec.AwaitingPayment{}:
      ft_absurd({x == Spec.Paid{} : Spec.Status}, hy)
    case Spec.NoOrder{} Spec.Paid{}:
      ft_absurd({x == Spec.Paid{} : Spec.Status}, hy)
    case Spec.NoOrder{} Spec.Failed{}:
      ft_absurd({x == Spec.Paid{} : Spec.Status}, hy)
    case Spec.NoOrder{} Spec.Refunded{}:
      ft_absurd({x == Spec.Paid{} : Spec.Status}, hl)
    case Spec.AwaitingPayment{} Spec.NoOrder{}:
      ft_absurd({x == Spec.Paid{} : Spec.Status}, hy)
    case Spec.AwaitingPayment{} Spec.AwaitingPayment{}:
      ft_absurd({x == Spec.Paid{} : Spec.Status}, hy)
    case Spec.AwaitingPayment{} Spec.Paid{}:
      ft_absurd({x == Spec.Paid{} : Spec.Status}, hy)
    case Spec.AwaitingPayment{} Spec.Failed{}:
      ft_absurd({x == Spec.Paid{} : Spec.Status}, hy)
    case Spec.AwaitingPayment{} Spec.Refunded{}:
      ft_absurd({x == Spec.Paid{} : Spec.Status}, hl)
    case Spec.Paid{} Spec.NoOrder{}:
      ft_absurd({x == Spec.Paid{} : Spec.Status}, hy)
    case Spec.Paid{} Spec.AwaitingPayment{}:
      ft_absurd({x == Spec.Paid{} : Spec.Status}, hy)
    case Spec.Paid{} Spec.Paid{}:
      ft_absurd({x == Spec.Paid{} : Spec.Status}, hy)
    case Spec.Paid{} Spec.Failed{}:
      ft_absurd({x == Spec.Paid{} : Spec.Status}, hy)
    case Spec.Paid{} Spec.Refunded{}:
      {==}
    case Spec.Failed{} Spec.NoOrder{}:
      ft_absurd({x == Spec.Paid{} : Spec.Status}, hy)
    case Spec.Failed{} Spec.AwaitingPayment{}:
      ft_absurd({x == Spec.Paid{} : Spec.Status}, hy)
    case Spec.Failed{} Spec.Paid{}:
      ft_absurd({x == Spec.Paid{} : Spec.Status}, hy)
    case Spec.Failed{} Spec.Failed{}:
      ft_absurd({x == Spec.Paid{} : Spec.Status}, hy)
    case Spec.Failed{} Spec.Refunded{}:
      ft_absurd({x == Spec.Paid{} : Spec.Status}, hl)
    case Spec.Refunded{} Spec.NoOrder{}:
      ft_absurd({x == Spec.Paid{} : Spec.Status}, hy)
    case Spec.Refunded{} Spec.AwaitingPayment{}:
      ft_absurd({x == Spec.Paid{} : Spec.Status}, hy)
    case Spec.Refunded{} Spec.Paid{}:
      ft_absurd({x == Spec.Paid{} : Spec.Status}, hy)
    case Spec.Refunded{} Spec.Failed{}:
      ft_absurd({x == Spec.Paid{} : Spec.Status}, hy)
    case Spec.Refunded{} Spec.Refunded{}:
      empty_elim({x == Spec.Paid{} : Spec.Status}, hn({==}))

def seq_to_eq(+x: Spec.Status, +y: Spec.Status, +h: {seq(x, y) == True{} : Bool}) -> {x == y : Spec.Status}:
  match x y:
    case Spec.NoOrder{} Spec.NoOrder{}:
      {==}
    case Spec.NoOrder{} Spec.AwaitingPayment{}:
      ft_absurd({x == y : Spec.Status}, h)
    case Spec.NoOrder{} Spec.Paid{}:
      ft_absurd({x == y : Spec.Status}, h)
    case Spec.NoOrder{} Spec.Failed{}:
      ft_absurd({x == y : Spec.Status}, h)
    case Spec.NoOrder{} Spec.Refunded{}:
      ft_absurd({x == y : Spec.Status}, h)
    case Spec.AwaitingPayment{} Spec.NoOrder{}:
      ft_absurd({x == y : Spec.Status}, h)
    case Spec.AwaitingPayment{} Spec.AwaitingPayment{}:
      {==}
    case Spec.AwaitingPayment{} Spec.Paid{}:
      ft_absurd({x == y : Spec.Status}, h)
    case Spec.AwaitingPayment{} Spec.Failed{}:
      ft_absurd({x == y : Spec.Status}, h)
    case Spec.AwaitingPayment{} Spec.Refunded{}:
      ft_absurd({x == y : Spec.Status}, h)
    case Spec.Paid{} Spec.NoOrder{}:
      ft_absurd({x == y : Spec.Status}, h)
    case Spec.Paid{} Spec.AwaitingPayment{}:
      ft_absurd({x == y : Spec.Status}, h)
    case Spec.Paid{} Spec.Paid{}:
      {==}
    case Spec.Paid{} Spec.Failed{}:
      ft_absurd({x == y : Spec.Status}, h)
    case Spec.Paid{} Spec.Refunded{}:
      ft_absurd({x == y : Spec.Status}, h)
    case Spec.Failed{} Spec.NoOrder{}:
      ft_absurd({x == y : Spec.Status}, h)
    case Spec.Failed{} Spec.AwaitingPayment{}:
      ft_absurd({x == y : Spec.Status}, h)
    case Spec.Failed{} Spec.Paid{}:
      ft_absurd({x == y : Spec.Status}, h)
    case Spec.Failed{} Spec.Failed{}:
      {==}
    case Spec.Failed{} Spec.Refunded{}:
      ft_absurd({x == y : Spec.Status}, h)
    case Spec.Refunded{} Spec.NoOrder{}:
      ft_absurd({x == y : Spec.Status}, h)
    case Spec.Refunded{} Spec.AwaitingPayment{}:
      ft_absurd({x == y : Spec.Status}, h)
    case Spec.Refunded{} Spec.Paid{}:
      ft_absurd({x == y : Spec.Status}, h)
    case Spec.Refunded{} Spec.Failed{}:
      ft_absurd({x == y : Spec.Status}, h)
    case Spec.Refunded{} Spec.Refunded{}:
      {==}

def p2b_b_od(+od: Spec.OrdRec, +od2: Spec.OrdRec, +hro: {ro3(od, od2) == True{} : Bool}, +hn: {Spec.out_refund(od) == False{} : Bool}, +hs: {Spec.out_refund(od2) == True{} : Bool}) -> {Spec.status_of(od) == Spec.Paid{} : Spec.Status}:
  match od od2:
    case Spec.OrdRec{x, am, oc, False{}} Spec.OrdRec{x2, am2, oc2, True{}}:
      seq_to_eq(x, Spec.Paid{}, ro3_f(od, od2, hro))
    case Spec.OrdRec{x, am, oc, True{}} Spec.OrdRec{x2, am2, oc2, True{}}:
      tf_absurd({Spec.status_of(od) == Spec.Paid{} : Spec.Status}, hn)
    case Spec.OrdRec{x, am, oc, True{}} Spec.OrdRec{x2, am2, oc2, False{}}:
      tf_absurd({Spec.status_of(od) == Spec.Paid{} : Spec.Status}, hn)
    case Spec.OrdRec{x, am, oc, False{}} Spec.OrdRec{x2, am2, oc2, False{}}:
      ft_absurd({Spec.status_of(od) == Spec.Paid{} : Spec.Status}, hs)

def Laws.p2b_a(s, e, o, h, hn, hs):
  p2b_a_st(Spec.st(s, o), Spec.st(Code.fst(Code.step(s, e)), o), Laws.pin_legal_transitions(s, e, o, h), hn, st_true(Spec.st(Code.fst(Code.step(s, e)), o), Spec.Refunded{}, hs))

def Laws.p2b_b(s, e, o, h, hn, hs):
  p2b_b_od(Spec.od(s, o), Spec.od(Code.fst(Code.step(s, e)), o), rel_ro(Spec.get(s, o), Spec.get(Code.fst(Code.step(s, e)), o), rel_step(s, e, o)), hn, hs)

# ------------------------------------------------------------------------ P3
def p3_st(+x: Spec.Status, +y: Spec.Status, +ht: {Spec.is_terminal(x) == True{} : Bool}, +hl: {Spec.legal(x, y) == True{} : Bool}) -> {y == x : Spec.Status}:
  match x y:
    case Spec.NoOrder{} Spec.NoOrder{}:
      ft_absurd({y == x : Spec.Status}, ht)
    case Spec.NoOrder{} Spec.AwaitingPayment{}:
      ft_absurd({y == x : Spec.Status}, ht)
    case Spec.NoOrder{} Spec.Paid{}:
      ft_absurd({y == x : Spec.Status}, ht)
    case Spec.NoOrder{} Spec.Failed{}:
      ft_absurd({y == x : Spec.Status}, ht)
    case Spec.NoOrder{} Spec.Refunded{}:
      ft_absurd({y == x : Spec.Status}, ht)
    case Spec.AwaitingPayment{} Spec.NoOrder{}:
      ft_absurd({y == x : Spec.Status}, ht)
    case Spec.AwaitingPayment{} Spec.AwaitingPayment{}:
      ft_absurd({y == x : Spec.Status}, ht)
    case Spec.AwaitingPayment{} Spec.Paid{}:
      ft_absurd({y == x : Spec.Status}, ht)
    case Spec.AwaitingPayment{} Spec.Failed{}:
      ft_absurd({y == x : Spec.Status}, ht)
    case Spec.AwaitingPayment{} Spec.Refunded{}:
      ft_absurd({y == x : Spec.Status}, ht)
    case Spec.Paid{} Spec.NoOrder{}:
      ft_absurd({y == x : Spec.Status}, ht)
    case Spec.Paid{} Spec.AwaitingPayment{}:
      ft_absurd({y == x : Spec.Status}, ht)
    case Spec.Paid{} Spec.Paid{}:
      ft_absurd({y == x : Spec.Status}, ht)
    case Spec.Paid{} Spec.Failed{}:
      ft_absurd({y == x : Spec.Status}, ht)
    case Spec.Paid{} Spec.Refunded{}:
      ft_absurd({y == x : Spec.Status}, ht)
    case Spec.Failed{} Spec.NoOrder{}:
      ft_absurd({y == x : Spec.Status}, hl)
    case Spec.Failed{} Spec.AwaitingPayment{}:
      ft_absurd({y == x : Spec.Status}, hl)
    case Spec.Failed{} Spec.Paid{}:
      ft_absurd({y == x : Spec.Status}, hl)
    case Spec.Failed{} Spec.Failed{}:
      {==}
    case Spec.Failed{} Spec.Refunded{}:
      ft_absurd({y == x : Spec.Status}, hl)
    case Spec.Refunded{} Spec.NoOrder{}:
      ft_absurd({y == x : Spec.Status}, hl)
    case Spec.Refunded{} Spec.AwaitingPayment{}:
      ft_absurd({y == x : Spec.Status}, hl)
    case Spec.Refunded{} Spec.Paid{}:
      ft_absurd({y == x : Spec.Status}, hl)
    case Spec.Refunded{} Spec.Failed{}:
      ft_absurd({y == x : Spec.Status}, hl)
    case Spec.Refunded{} Spec.Refunded{}:
      {==}

def p3_st2(+x: Spec.Status, +y: Spec.Status, +ht: {Spec.is_terminal(x) == True{} : Bool}, +hl: {Spec.legal(x, y) == True{} : Bool}) -> {x == y : Spec.Status}:
  match x y:
    case Spec.NoOrder{} Spec.NoOrder{}:
      ft_absurd({x == y : Spec.Status}, ht)
    case Spec.NoOrder{} Spec.AwaitingPayment{}:
      ft_absurd({x == y : Spec.Status}, ht)
    case Spec.NoOrder{} Spec.Paid{}:
      ft_absurd({x == y : Spec.Status}, ht)
    case Spec.NoOrder{} Spec.Failed{}:
      ft_absurd({x == y : Spec.Status}, ht)
    case Spec.NoOrder{} Spec.Refunded{}:
      ft_absurd({x == y : Spec.Status}, ht)
    case Spec.AwaitingPayment{} Spec.NoOrder{}:
      ft_absurd({x == y : Spec.Status}, ht)
    case Spec.AwaitingPayment{} Spec.AwaitingPayment{}:
      ft_absurd({x == y : Spec.Status}, ht)
    case Spec.AwaitingPayment{} Spec.Paid{}:
      ft_absurd({x == y : Spec.Status}, ht)
    case Spec.AwaitingPayment{} Spec.Failed{}:
      ft_absurd({x == y : Spec.Status}, ht)
    case Spec.AwaitingPayment{} Spec.Refunded{}:
      ft_absurd({x == y : Spec.Status}, ht)
    case Spec.Paid{} Spec.NoOrder{}:
      ft_absurd({x == y : Spec.Status}, ht)
    case Spec.Paid{} Spec.AwaitingPayment{}:
      ft_absurd({x == y : Spec.Status}, ht)
    case Spec.Paid{} Spec.Paid{}:
      ft_absurd({x == y : Spec.Status}, ht)
    case Spec.Paid{} Spec.Failed{}:
      ft_absurd({x == y : Spec.Status}, ht)
    case Spec.Paid{} Spec.Refunded{}:
      ft_absurd({x == y : Spec.Status}, ht)
    case Spec.Failed{} Spec.NoOrder{}:
      ft_absurd({x == y : Spec.Status}, hl)
    case Spec.Failed{} Spec.AwaitingPayment{}:
      ft_absurd({x == y : Spec.Status}, hl)
    case Spec.Failed{} Spec.Paid{}:
      ft_absurd({x == y : Spec.Status}, hl)
    case Spec.Failed{} Spec.Failed{}:
      {==}
    case Spec.Failed{} Spec.Refunded{}:
      ft_absurd({x == y : Spec.Status}, hl)
    case Spec.Refunded{} Spec.NoOrder{}:
      ft_absurd({x == y : Spec.Status}, hl)
    case Spec.Refunded{} Spec.AwaitingPayment{}:
      ft_absurd({x == y : Spec.Status}, hl)
    case Spec.Refunded{} Spec.Paid{}:
      ft_absurd({x == y : Spec.Status}, hl)
    case Spec.Refunded{} Spec.Failed{}:
      ft_absurd({x == y : Spec.Status}, hl)
    case Spec.Refunded{} Spec.Refunded{}:
      {==}

def nat_eq_true(+n: Nat, +m: Nat, +h: {Nat.is_eq(n, m) == True{} : Bool}) -> {m == n : Nat}:
  match n m:
    case 0n 0n:
      {==}
    case 0n 1n+m2:
      ft_absurd({1n+m2 == 0n : Nat}, h)
    case 1n+n2 0n:
      ft_absurd({0n == 1n+n2 : Nat}, h)
    case 1n+n2 1n+m2:
      %nat_eq_true(n2, m2, h) : {1n+m2 == 1n+_ : Nat}
      {==}

def imp_t(+t: Bool, +b: Bool, +ht: {t == True{} : Bool}, +h: {Spec.imp(t, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match t:
    case False{}:
      ft_absurd({b == True{} : Bool}, ht)
    case True{}:
      h

def p3_od(+od: Spec.OrdRec, +od2: Spec.OrdRec, +hro: {ro3(od, od2) == True{} : Bool}, +ht: {Spec.is_terminal(Spec.status_of(od)) == True{} : Bool}) -> {(Spec.status_of(od2), Spec.amount_of(od2)) == (Spec.status_of(od), Spec.amount_of(od)) : Spec.Status & Nat}:
  match od od2:
    case Spec.OrdRec{x, am, oc, orf} Spec.OrdRec{x2, am2, oc2, orf2}:
      %p3_st(x, x2, ht, ro3_l(od, od2, hro)) : {(x2, am2) == (_, am) : Spec.Status & Nat}
      %nat_eq_true(am, am2, imp_t(Spec.is_terminal(x), Nat.is_eq(am, am2), ht, ro3_t(od, od2, hro))) : {(x2, am2) == (x2, _) : Spec.Status & Nat}
      {==}

def p3_ht(+od: Spec.OrdRec, +od2: Spec.OrdRec, +hro: {ro3(od, od2) == True{} : Bool}, +ht: {Spec.is_terminal(Spec.status_of(od)) == True{} : Bool}) -> {Spec.is_terminal(Spec.status_of(od2)) == True{} : Bool}:
  match od od2:
    case Spec.OrdRec{x, am, oc, orf} Spec.OrdRec{x2, am2, oc2, orf2}:
      %p3_st2(x, x2, ht, ro3_l(od, od2, hro)) : {Spec.is_terminal(_) == True{} : Bool}
      ht

def p3_state(+s: Spec.State, +e: Spec.Ev, +o: Nat, +ht: {Spec.is_terminal(Spec.st(s, o)) == True{} : Bool}) -> {(Spec.st(Code.fst(Code.step(s, e)), o), Spec.amount_of(Spec.od(Code.fst(Code.step(s, e)), o))) == (Spec.st(s, o), Spec.amount_of(Spec.od(s, o))) : Spec.Status & Nat}:
  p3_od(Spec.od(s, o), Spec.od(Code.fst(Code.step(s, e)), o), rel_ro(Spec.get(s, o), Spec.get(Code.fst(Code.step(s, e)), o), rel_step(s, e, o)), ht)

def p3_ht_state(+s: Spec.State, +e: Spec.Ev, +o: Nat, +ht: {Spec.is_terminal(Spec.st(s, o)) == True{} : Bool}) -> {Spec.is_terminal(Spec.st(Code.fst(Code.step(s, e)), o)) == True{} : Bool}:
  p3_ht(Spec.od(s, o), Spec.od(Code.fst(Code.step(s, e)), o), rel_ro(Spec.get(s, o), Spec.get(Code.fst(Code.step(s, e)), o), rel_step(s, e, o)), ht)

def p3_run_l(events: List<Spec.Ev>, +s: Spec.State, +o: Nat, +h: {Spec.inv(s) == True{} : Bool}, +ht: {Spec.is_terminal(Spec.st(s, o)) == True{} : Bool}) -> {(Spec.st(Code.run(events, s), o), Spec.amount_of(Spec.od(Code.run(events, s), o))) == (Spec.st(s, o), Spec.amount_of(Spec.od(s, o))) : Spec.Status & Nat}:
  match events:
    case Nil{}:
      {==}
    case +e <> t:
      %p3_state(s, e, o, ht) : {(Spec.st(Code.run(t, Code.fst(Code.step(s, e))), o), Spec.amount_of(Spec.od(Code.run(t, Code.fst(Code.step(s, e))), o))) == _ : Spec.Status & Nat}
      p3_run_l(t, Code.fst(Code.step(s, e)), o, Laws.inv_step(s, e, h), p3_ht_state(s, e, o, ht))

def Laws.p3_step(s, e, o, h, ht):
  p3_state(s, e, o, ht)

def Laws.p3_run(events, s, o, h, ht):
  p3_run_l(events, s, o, h, ht)
# ------------------------------------------------------------------ P2b(c), (d)
def sndl(r: +List<Spec.Slot> & List<Spec.Effect>) -> List<Spec.Effect>:
  match r:
    case (a, b):
      b

def snds(r: Spec.Slot & List<Spec.Effect>) -> List<Spec.Effect>:
  match r:
    case (a, b):
      b

def nat_eq_true2(+n: Nat, +m: Nat, +h: {Nat.is_eq(n, m) == True{} : Bool}) -> {n == m : Nat}:
  match n m:
    case 0n 0n:
      {==}
    case 0n 1n+m2:
      ft_absurd({0n == 1n+m2 : Nat}, h)
    case 1n+n2 0n:
      ft_absurd({1n+n2 == 0n : Nat}, h)
    case 1n+n2 1n+m2:
      %nat_eq_true2(n2, m2, h) : {1n+n2 == 1n+_ : Nat}
      {==}

def or_f(+a: Bool, +h: {Bool.or(a, False{}) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case False{}:
      ft_absurd({False{} == True{} : Bool}, h)
    case True{}:
      {==}

def isref_eq(+x: Spec.Status, +h: {Spec.is_refunded(x) == True{} : Bool}) -> {x == Spec.Refunded{} : Spec.Status}:
  match x:
    case Spec.NoOrder{}:
      ft_absurd({Spec.NoOrder{} == Spec.Refunded{} : Spec.Status}, h)
    case Spec.AwaitingPayment{}:
      ft_absurd({Spec.AwaitingPayment{} == Spec.Refunded{} : Spec.Status}, h)
    case Spec.Paid{}:
      ft_absurd({Spec.Paid{} == Spec.Refunded{} : Spec.Status}, h)
    case Spec.Failed{}:
      ft_absurd({Spec.Failed{} == Spec.Refunded{} : Spec.Status}, h)
    case Spec.Refunded{}:
      {==}

def ct_has(r: Spec.Slot & List<Spec.Effect>, +t: +List<Spec.Slot>, +X: Spec.Effect, +h: {Spec.has(sndl(Code.cons_tail(r, t)), X) == True{} : Bool}) -> {Spec.has(snds(r), X) == True{} : Bool}:
  match r:
    case (x, fx):
      h

def cs_has(+x: Spec.Slot, r: +List<Spec.Slot> & List<Spec.Effect>, +X: Spec.Effect, +h: {Spec.has(sndl(Code.cons_slot(x, r)), X) == True{} : Bool}) -> {Spec.has(sndl(r), X) == True{} : Bool}:
  match r:
    case (t2, fx):
      h

def go_fx(+sl: +List<Spec.Slot>, +o: Nat, +k: Nat, +e: Spec.Ev, +X: Spec.Effect, +hh: {Spec.has(sndl(Code.go(sl, o, k, e)), X) == True{} : Bool}) -> {Spec.has(snds(Code.slot_step(Spec.get_l(sl, o), k, e)), X) == True{} : Bool}:
  match sl o:
    case Nil{} _:
      ft_absurd({Spec.has(snds(Code.slot_step(Spec.get_l(Nil{}, o), k, e)), X) == True{} : Bool}, hh)
    case +h <> +t 0n:
      ct_has(Code.slot_step(h, k, e), t, X, hh)
    case +h <> +t 1n+p:
      go_fx(t, p, k, e, X, cs_has(h, Code.go(t, p, k, e), X, hh))

def fx_ws(r: +List<Spec.Slot> & List<Spec.Effect>, +ou: Bool, +pu: Bool, +X: Spec.Effect, +h: {Spec.has(Code.snd(Code.with_state(r, ou, pu)), X) == True{} : Bool}) -> {Spec.has(sndl(r), X) == True{} : Bool}:
  match r:
    case (sl2, fx):
      h

def fx_recv(+sl: +List<Spec.Slot>, up: Bool, +ou: Bool, +pu: Bool, +e: Spec.Ev, +X: Spec.Effect, +h: {Spec.has(Code.snd(Code.recv(sl, up, ou, pu, e)), X) == True{} : Bool}) -> {Spec.has(snds(Code.slot_step(Spec.get_l(sl, Spec.ev_idx(e)), Spec.ev_idx(e), e)), X) == True{} : Bool}:
  match up:
    case False{}:
      ft_absurd({Spec.has(snds(Code.slot_step(Spec.get_l(sl, Spec.ev_idx(e)), Spec.ev_idx(e), e)), X) == True{} : Bool}, h)
    case True{}:
      go_fx(sl, Spec.ev_idx(e), Spec.ev_idx(e), e, X, fx_ws(Code.go(sl, Spec.ev_idx(e), Spec.ev_idx(e), e), ou, pu, X, h))

def fx_step(+s: Spec.State, +e: Spec.Ev, +X: Spec.Effect, +h: {Spec.has(Code.snd(Code.step(s, e)), X) == True{} : Bool}) -> {Spec.has(snds(Code.slot_step(Spec.get(s, Spec.ev_idx(e)), Spec.ev_idx(e), e)), X) == True{} : Bool}:
  match s:
    case Spec.State{sl, ou, pu}:
      match e:
        case Spec.PlaceOrder{o, a}:
          fx_recv(sl, ou, ou, pu, e, X, h)
        case Spec.RetryTimeout{o}:
          fx_recv(sl, ou, ou, pu, e, X, h)
        case Spec.FlushChargeReq{o}:
          fx_recv(sl, ou, ou, pu, e, X, h)
        case Spec.FlushRefundReq{o}:
          fx_recv(sl, ou, ou, pu, e, X, h)
        case Spec.PaymentApproved{o}:
          fx_recv(sl, ou, ou, pu, e, X, h)
        case Spec.PaymentDeclined{o}:
          fx_recv(sl, ou, ou, pu, e, X, h)
        case Spec.RefundOrder{o}:
          fx_recv(sl, ou, ou, pu, e, X, h)
        case Spec.ChargeReqRecv{o, a, d}:
          fx_recv(sl, pu, ou, pu, e, X, h)
        case Spec.RefundReqRecv{o}:
          fx_recv(sl, pu, ou, pu, e, X, h)
        case Spec.FlushReply{o}:
          fx_recv(sl, pu, ou, pu, e, X, h)
        case Spec.Crash{svc}:
          ft_absurd({Spec.has(snds(Code.slot_step(Spec.get(s, Spec.ev_idx(e)), Spec.ev_idx(e), e)), X) == True{} : Bool}, h)
        case Spec.Restart{svc}:
          ft_absurd({Spec.has(snds(Code.slot_step(Spec.get(s, Spec.ev_idx(e)), Spec.ev_idx(e), e)), X) == True{} : Bool}, h)

def wr_rp(+od: Spec.OrdRec, +r: Spec.Res, +cc: Nat, +rc: Nat, +am: Nat, +orr: Bool, +k: Nat, +q: Nat, +g: Bool, +hw: {Spec.has(snds(Code.with_prov(Code.refund_pick(Spec.ProvRec{r, cc, rc, am, orr}, k, g), od)), Spec.WireRefundReq{q}) == True{} : Bool}) -> {k == q : Nat} & {Spec.status_of(od) == Spec.Refunded{} : Spec.Status}:
  match r g:
    case Spec.NoRec{} _:
      ft_absurd({k == q : Nat} & {Spec.status_of(od) == Spec.Refunded{} : Spec.Status}, hw)
    case Spec.Declined{} _:
      ft_absurd({k == q : Nat} & {Spec.status_of(od) == Spec.Refunded{} : Spec.Status}, hw)
    case Spec.Approved{} False{}:
      ft_absurd({k == q : Nat} & {Spec.status_of(od) == Spec.Refunded{} : Spec.Status}, hw)
    case Spec.Approved{} True{}:
      ft_absurd({k == q : Nat} & {Spec.status_of(od) == Spec.Refunded{} : Spec.Status}, hw)

def wd_rp(+od: Spec.OrdRec, +r: Spec.Res, +cc: Nat, +rc: Nat, +am: Nat, +orr: Bool, +k: Nat, +q: Nat, +ex: Nat, +g: Bool, +hw: {Spec.has(snds(Code.with_prov(Code.refund_pick(Spec.ProvRec{r, cc, rc, am, orr}, k, g), od)), Spec.Refund{q, ex}) == True{} : Bool}) -> {k == q : Nat} & {r == Spec.Approved{} : Spec.Res}:
  match r g:
    case Spec.NoRec{} _:
      ft_absurd({k == q : Nat} & {r == Spec.Approved{} : Spec.Res}, hw)
    case Spec.Declined{} _:
      ft_absurd({k == q : Nat} & {r == Spec.Approved{} : Spec.Res}, hw)
    case Spec.Approved{} False{}:
      ft_absurd({k == q : Nat} & {r == Spec.Approved{} : Spec.Res}, hw)
    case Spec.Approved{} True{}:
      (nat_eq_true2(k, q, and_l(Nat.is_eq(k, q), Nat.is_eq(am, ex), or_f(Bool.and(Nat.is_eq(k, q), Nat.is_eq(am, ex)), hw))), {==})

def wr_slot(+sl0: Spec.Slot, +k: Nat, +e: Spec.Ev, +q: Nat, +hh: {Spec.slot_ok(sl0) == True{} : Bool}, +hw: {Spec.has(snds(Code.slot_step(sl0, k, e)), Spec.WireRefundReq{q}) == True{} : Bool}) -> {k == q : Nat} & {Spec.status_of(Spec.ord_of(sl0)) == Spec.Refunded{} : Spec.Status}:
  match sl0 e:
    case Spec.Slot{Spec.OrdRec{Spec.NoOrder{}, am, oc, orf}, pv} Spec.PlaceOrder{_, 0n}:
      ft_absurd({k == q : Nat} & {Spec.status_of(Spec.ord_of(sl0)) == Spec.Refunded{} : Spec.Status}, hw)
    case Spec.Slot{Spec.OrdRec{Spec.NoOrder{}, am, oc, orf}, pv} Spec.PlaceOrder{_, 1n+pa}:
      ft_absurd({k == q : Nat} & {Spec.status_of(Spec.ord_of(sl0)) == Spec.Refunded{} : Spec.Status}, hw)
    case Spec.Slot{Spec.OrdRec{Spec.AwaitingPayment{}, am, oc, orf}, pv} Spec.PlaceOrder{_, a}:
      ft_absurd({k == q : Nat} & {Spec.status_of(Spec.ord_of(sl0)) == Spec.Refunded{} : Spec.Status}, hw)
    case Spec.Slot{Spec.OrdRec{Spec.Paid{}, am, oc, orf}, pv} Spec.PlaceOrder{_, a}:
      ft_absurd({k == q : Nat} & {Spec.status_of(Spec.ord_of(sl0)) == Spec.Refunded{} : Spec.Status}, hw)
    case Spec.Slot{Spec.OrdRec{Spec.Failed{}, am, oc, orf}, pv} Spec.PlaceOrder{_, a}:
      ft_absurd({k == q : Nat} & {Spec.status_of(Spec.ord_of(sl0)) == Spec.Refunded{} : Spec.Status}, hw)
    case Spec.Slot{Spec.OrdRec{Spec.Refunded{}, am, oc, orf}, pv} Spec.PlaceOrder{_, a}:
      ft_absurd({k == q : Nat} & {Spec.status_of(Spec.ord_of(sl0)) == Spec.Refunded{} : Spec.Status}, hw)
    case Spec.Slot{Spec.OrdRec{Spec.NoOrder{}, am, oc, orf}, pv} Spec.RetryTimeout{_}:
      ft_absurd({k == q : Nat} & {Spec.status_of(Spec.ord_of(sl0)) == Spec.Refunded{} : Spec.Status}, hw)
    case Spec.Slot{Spec.OrdRec{Spec.AwaitingPayment{}, am, oc, orf}, pv} Spec.RetryTimeout{_}:
      ft_absurd({k == q : Nat} & {Spec.status_of(Spec.ord_of(sl0)) == Spec.Refunded{} : Spec.Status}, hw)
    case Spec.Slot{Spec.OrdRec{Spec.Paid{}, am, oc, orf}, pv} Spec.RetryTimeout{_}:
      ft_absurd({k == q : Nat} & {Spec.status_of(Spec.ord_of(sl0)) == Spec.Refunded{} : Spec.Status}, hw)
    case Spec.Slot{Spec.OrdRec{Spec.Failed{}, am, oc, orf}, pv} Spec.RetryTimeout{_}:
      ft_absurd({k == q : Nat} & {Spec.status_of(Spec.ord_of(sl0)) == Spec.Refunded{} : Spec.Status}, hw)
    case Spec.Slot{Spec.OrdRec{Spec.Refunded{}, am, oc, orf}, pv} Spec.RetryTimeout{_}:
      ft_absurd({k == q : Nat} & {Spec.status_of(Spec.ord_of(sl0)) == Spec.Refunded{} : Spec.Status}, hw)
    case Spec.Slot{Spec.OrdRec{Spec.NoOrder{}, am, oc, orf}, pv} Spec.PaymentApproved{_}:
      ft_absurd({k == q : Nat} & {Spec.status_of(Spec.ord_of(sl0)) == Spec.Refunded{} : Spec.Status}, hw)
    case Spec.Slot{Spec.OrdRec{Spec.AwaitingPayment{}, am, oc, orf}, pv} Spec.PaymentApproved{_}:
      ft_absurd({k == q : Nat} & {Spec.status_of(Spec.ord_of(sl0)) == Spec.Refunded{} : Spec.Status}, hw)
    case Spec.Slot{Spec.OrdRec{Spec.Paid{}, am, oc, orf}, pv} Spec.PaymentApproved{_}:
      ft_absurd({k == q : Nat} & {Spec.status_of(Spec.ord_of(sl0)) == Spec.Refunded{} : Spec.Status}, hw)
    case Spec.Slot{Spec.OrdRec{Spec.Failed{}, am, oc, orf}, pv} Spec.PaymentApproved{_}:
      ft_absurd({k == q : Nat} & {Spec.status_of(Spec.ord_of(sl0)) == Spec.Refunded{} : Spec.Status}, hw)
    case Spec.Slot{Spec.OrdRec{Spec.Refunded{}, am, oc, orf}, pv} Spec.PaymentApproved{_}:
      ft_absurd({k == q : Nat} & {Spec.status_of(Spec.ord_of(sl0)) == Spec.Refunded{} : Spec.Status}, hw)
    case Spec.Slot{Spec.OrdRec{Spec.NoOrder{}, am, oc, orf}, pv} Spec.PaymentDeclined{_}:
      ft_absurd({k == q : Nat} & {Spec.status_of(Spec.ord_of(sl0)) == Spec.Refunded{} : Spec.Status}, hw)
    case Spec.Slot{Spec.OrdRec{Spec.AwaitingPayment{}, am, oc, orf}, pv} Spec.PaymentDeclined{_}:
      ft_absurd({k == q : Nat} & {Spec.status_of(Spec.ord_of(sl0)) == Spec.Refunded{} : Spec.Status}, hw)
    case Spec.Slot{Spec.OrdRec{Spec.Paid{}, am, oc, orf}, pv} Spec.PaymentDeclined{_}:
      ft_absurd({k == q : Nat} & {Spec.status_of(Spec.ord_of(sl0)) == Spec.Refunded{} : Spec.Status}, hw)
    case Spec.Slot{Spec.OrdRec{Spec.Failed{}, am, oc, orf}, pv} Spec.PaymentDeclined{_}:
      ft_absurd({k == q : Nat} & {Spec.status_of(Spec.ord_of(sl0)) == Spec.Refunded{} : Spec.Status}, hw)
    case Spec.Slot{Spec.OrdRec{Spec.Refunded{}, am, oc, orf}, pv} Spec.PaymentDeclined{_}:
      ft_absurd({k == q : Nat} & {Spec.status_of(Spec.ord_of(sl0)) == Spec.Refunded{} : Spec.Status}, hw)
    case Spec.Slot{Spec.OrdRec{Spec.NoOrder{}, am, oc, orf}, pv} Spec.RefundOrder{_}:
      ft_absurd({k == q : Nat} & {Spec.status_of(Spec.ord_of(sl0)) == Spec.Refunded{} : Spec.Status}, hw)
    case Spec.Slot{Spec.OrdRec{Spec.AwaitingPayment{}, am, oc, orf}, pv} Spec.RefundOrder{_}:
      ft_absurd({k == q : Nat} & {Spec.status_of(Spec.ord_of(sl0)) == Spec.Refunded{} : Spec.Status}, hw)
    case Spec.Slot{Spec.OrdRec{Spec.Paid{}, am, oc, orf}, pv} Spec.RefundOrder{_}:
      ft_absurd({k == q : Nat} & {Spec.status_of(Spec.ord_of(sl0)) == Spec.Refunded{} : Spec.Status}, hw)
    case Spec.Slot{Spec.OrdRec{Spec.Failed{}, am, oc, orf}, pv} Spec.RefundOrder{_}:
      ft_absurd({k == q : Nat} & {Spec.status_of(Spec.ord_of(sl0)) == Spec.Refunded{} : Spec.Status}, hw)
    case Spec.Slot{Spec.OrdRec{Spec.Refunded{}, am, oc, orf}, pv} Spec.RefundOrder{_}:
      ft_absurd({k == q : Nat} & {Spec.status_of(Spec.ord_of(sl0)) == Spec.Refunded{} : Spec.Status}, hw)
    case Spec.Slot{Spec.OrdRec{x, am, True{}, orf}, pv} Spec.FlushChargeReq{_}:
      ft_absurd({k == q : Nat} & {Spec.status_of(Spec.ord_of(sl0)) == Spec.Refunded{} : Spec.Status}, hw)
    case Spec.Slot{Spec.OrdRec{x, am, False{}, orf}, pv} Spec.FlushChargeReq{_}:
      ft_absurd({k == q : Nat} & {Spec.status_of(Spec.ord_of(sl0)) == Spec.Refunded{} : Spec.Status}, hw)
    case Spec.Slot{Spec.OrdRec{x, am, oc, False{}}, pv} Spec.FlushRefundReq{_}:
      ft_absurd({k == q : Nat} & {Spec.status_of(Spec.ord_of(sl0)) == Spec.Refunded{} : Spec.Status}, hw)
    case Spec.Slot{Spec.OrdRec{x, am, oc, True{}}, pv} Spec.FlushRefundReq{_}:
      (nat_eq_true2(k, q, or_f(Nat.is_eq(k, q), hw)), isref_eq(x, and_l(Spec.imp(True{}, Spec.is_refunded(x)), Spec.imp(oc, Bool.not(Spec.is_noorder(x))), sp_r(Spec.OrdRec{x, am, oc, True{}}, pv, hh))))
    case Spec.Slot{od, Spec.ProvRec{Spec.NoRec{}, cc, rc, am, orr}} Spec.ChargeReqRecv{_, 0n, _}:
      ft_absurd({k == q : Nat} & {Spec.status_of(Spec.ord_of(sl0)) == Spec.Refunded{} : Spec.Status}, hw)
    case Spec.Slot{od, Spec.ProvRec{Spec.NoRec{}, cc, rc, am, orr}} Spec.ChargeReqRecv{_, 1n+pa, Spec.Approve{}}:
      ft_absurd({k == q : Nat} & {Spec.status_of(Spec.ord_of(sl0)) == Spec.Refunded{} : Spec.Status}, hw)
    case Spec.Slot{od, Spec.ProvRec{Spec.NoRec{}, cc, rc, am, orr}} Spec.ChargeReqRecv{_, 1n+pa, Spec.Decline{}}:
      ft_absurd({k == q : Nat} & {Spec.status_of(Spec.ord_of(sl0)) == Spec.Refunded{} : Spec.Status}, hw)
    case Spec.Slot{od, Spec.ProvRec{Spec.Approved{}, cc, rc, am, orr}} Spec.ChargeReqRecv{_, 0n, _}:
      ft_absurd({k == q : Nat} & {Spec.status_of(Spec.ord_of(sl0)) == Spec.Refunded{} : Spec.Status}, hw)
    case Spec.Slot{od, Spec.ProvRec{Spec.Approved{}, cc, rc, am, orr}} Spec.ChargeReqRecv{_, 1n+pa, _}:
      ft_absurd({k == q : Nat} & {Spec.status_of(Spec.ord_of(sl0)) == Spec.Refunded{} : Spec.Status}, hw)
    case Spec.Slot{od, Spec.ProvRec{Spec.Declined{}, cc, rc, am, orr}} Spec.ChargeReqRecv{_, 0n, _}:
      ft_absurd({k == q : Nat} & {Spec.status_of(Spec.ord_of(sl0)) == Spec.Refunded{} : Spec.Status}, hw)
    case Spec.Slot{od, Spec.ProvRec{Spec.Declined{}, cc, rc, am, orr}} Spec.ChargeReqRecv{_, 1n+pa, _}:
      ft_absurd({k == q : Nat} & {Spec.status_of(Spec.ord_of(sl0)) == Spec.Refunded{} : Spec.Status}, hw)
    case Spec.Slot{od, Spec.ProvRec{r, cc, rc, am, orr}} Spec.RefundReqRecv{_}:
      wr_rp(od, r, cc, rc, am, orr, k, q, Nat.is_lt(rc, cc), hw)
    case Spec.Slot{od, Spec.ProvRec{Spec.NoRec{}, cc, rc, am, True{}}} Spec.FlushReply{_}:
      ft_absurd({k == q : Nat} & {Spec.status_of(Spec.ord_of(sl0)) == Spec.Refunded{} : Spec.Status}, hw)
    case Spec.Slot{od, Spec.ProvRec{Spec.NoRec{}, cc, rc, am, False{}}} Spec.FlushReply{_}:
      ft_absurd({k == q : Nat} & {Spec.status_of(Spec.ord_of(sl0)) == Spec.Refunded{} : Spec.Status}, hw)
    case Spec.Slot{od, Spec.ProvRec{Spec.Approved{}, cc, rc, am, True{}}} Spec.FlushReply{_}:
      ft_absurd({k == q : Nat} & {Spec.status_of(Spec.ord_of(sl0)) == Spec.Refunded{} : Spec.Status}, hw)
    case Spec.Slot{od, Spec.ProvRec{Spec.Approved{}, cc, rc, am, False{}}} Spec.FlushReply{_}:
      ft_absurd({k == q : Nat} & {Spec.status_of(Spec.ord_of(sl0)) == Spec.Refunded{} : Spec.Status}, hw)
    case Spec.Slot{od, Spec.ProvRec{Spec.Declined{}, cc, rc, am, True{}}} Spec.FlushReply{_}:
      ft_absurd({k == q : Nat} & {Spec.status_of(Spec.ord_of(sl0)) == Spec.Refunded{} : Spec.Status}, hw)
    case Spec.Slot{od, Spec.ProvRec{Spec.Declined{}, cc, rc, am, False{}}} Spec.FlushReply{_}:
      ft_absurd({k == q : Nat} & {Spec.status_of(Spec.ord_of(sl0)) == Spec.Refunded{} : Spec.Status}, hw)
    case Spec.Slot{od, pv} Spec.Crash{_}:
      ft_absurd({k == q : Nat} & {Spec.status_of(Spec.ord_of(sl0)) == Spec.Refunded{} : Spec.Status}, hw)
    case Spec.Slot{od, pv} Spec.Restart{_}:
      ft_absurd({k == q : Nat} & {Spec.status_of(Spec.ord_of(sl0)) == Spec.Refunded{} : Spec.Status}, hw)

def wd_slot(+sl0: Spec.Slot, +k: Nat, +e: Spec.Ev, +q: Nat, +ex: Nat, +hw: {Spec.has(snds(Code.slot_step(sl0, k, e)), Spec.Refund{q, ex}) == True{} : Bool}) -> {k == q : Nat} & {Spec.rec_of(Spec.prov_of(sl0)) == Spec.Approved{} : Spec.Res}:
  match sl0 e:
    case Spec.Slot{Spec.OrdRec{Spec.NoOrder{}, am, oc, orf}, pv} Spec.PlaceOrder{_, 0n}:
      ft_absurd({k == q : Nat} & {Spec.rec_of(Spec.prov_of(sl0)) == Spec.Approved{} : Spec.Res}, hw)
    case Spec.Slot{Spec.OrdRec{Spec.NoOrder{}, am, oc, orf}, pv} Spec.PlaceOrder{_, 1n+pa}:
      ft_absurd({k == q : Nat} & {Spec.rec_of(Spec.prov_of(sl0)) == Spec.Approved{} : Spec.Res}, hw)
    case Spec.Slot{Spec.OrdRec{Spec.AwaitingPayment{}, am, oc, orf}, pv} Spec.PlaceOrder{_, a}:
      ft_absurd({k == q : Nat} & {Spec.rec_of(Spec.prov_of(sl0)) == Spec.Approved{} : Spec.Res}, hw)
    case Spec.Slot{Spec.OrdRec{Spec.Paid{}, am, oc, orf}, pv} Spec.PlaceOrder{_, a}:
      ft_absurd({k == q : Nat} & {Spec.rec_of(Spec.prov_of(sl0)) == Spec.Approved{} : Spec.Res}, hw)
    case Spec.Slot{Spec.OrdRec{Spec.Failed{}, am, oc, orf}, pv} Spec.PlaceOrder{_, a}:
      ft_absurd({k == q : Nat} & {Spec.rec_of(Spec.prov_of(sl0)) == Spec.Approved{} : Spec.Res}, hw)
    case Spec.Slot{Spec.OrdRec{Spec.Refunded{}, am, oc, orf}, pv} Spec.PlaceOrder{_, a}:
      ft_absurd({k == q : Nat} & {Spec.rec_of(Spec.prov_of(sl0)) == Spec.Approved{} : Spec.Res}, hw)
    case Spec.Slot{Spec.OrdRec{Spec.NoOrder{}, am, oc, orf}, pv} Spec.RetryTimeout{_}:
      ft_absurd({k == q : Nat} & {Spec.rec_of(Spec.prov_of(sl0)) == Spec.Approved{} : Spec.Res}, hw)
    case Spec.Slot{Spec.OrdRec{Spec.AwaitingPayment{}, am, oc, orf}, pv} Spec.RetryTimeout{_}:
      ft_absurd({k == q : Nat} & {Spec.rec_of(Spec.prov_of(sl0)) == Spec.Approved{} : Spec.Res}, hw)
    case Spec.Slot{Spec.OrdRec{Spec.Paid{}, am, oc, orf}, pv} Spec.RetryTimeout{_}:
      ft_absurd({k == q : Nat} & {Spec.rec_of(Spec.prov_of(sl0)) == Spec.Approved{} : Spec.Res}, hw)
    case Spec.Slot{Spec.OrdRec{Spec.Failed{}, am, oc, orf}, pv} Spec.RetryTimeout{_}:
      ft_absurd({k == q : Nat} & {Spec.rec_of(Spec.prov_of(sl0)) == Spec.Approved{} : Spec.Res}, hw)
    case Spec.Slot{Spec.OrdRec{Spec.Refunded{}, am, oc, orf}, pv} Spec.RetryTimeout{_}:
      ft_absurd({k == q : Nat} & {Spec.rec_of(Spec.prov_of(sl0)) == Spec.Approved{} : Spec.Res}, hw)
    case Spec.Slot{Spec.OrdRec{Spec.NoOrder{}, am, oc, orf}, pv} Spec.PaymentApproved{_}:
      ft_absurd({k == q : Nat} & {Spec.rec_of(Spec.prov_of(sl0)) == Spec.Approved{} : Spec.Res}, hw)
    case Spec.Slot{Spec.OrdRec{Spec.AwaitingPayment{}, am, oc, orf}, pv} Spec.PaymentApproved{_}:
      ft_absurd({k == q : Nat} & {Spec.rec_of(Spec.prov_of(sl0)) == Spec.Approved{} : Spec.Res}, hw)
    case Spec.Slot{Spec.OrdRec{Spec.Paid{}, am, oc, orf}, pv} Spec.PaymentApproved{_}:
      ft_absurd({k == q : Nat} & {Spec.rec_of(Spec.prov_of(sl0)) == Spec.Approved{} : Spec.Res}, hw)
    case Spec.Slot{Spec.OrdRec{Spec.Failed{}, am, oc, orf}, pv} Spec.PaymentApproved{_}:
      ft_absurd({k == q : Nat} & {Spec.rec_of(Spec.prov_of(sl0)) == Spec.Approved{} : Spec.Res}, hw)
    case Spec.Slot{Spec.OrdRec{Spec.Refunded{}, am, oc, orf}, pv} Spec.PaymentApproved{_}:
      ft_absurd({k == q : Nat} & {Spec.rec_of(Spec.prov_of(sl0)) == Spec.Approved{} : Spec.Res}, hw)
    case Spec.Slot{Spec.OrdRec{Spec.NoOrder{}, am, oc, orf}, pv} Spec.PaymentDeclined{_}:
      ft_absurd({k == q : Nat} & {Spec.rec_of(Spec.prov_of(sl0)) == Spec.Approved{} : Spec.Res}, hw)
    case Spec.Slot{Spec.OrdRec{Spec.AwaitingPayment{}, am, oc, orf}, pv} Spec.PaymentDeclined{_}:
      ft_absurd({k == q : Nat} & {Spec.rec_of(Spec.prov_of(sl0)) == Spec.Approved{} : Spec.Res}, hw)
    case Spec.Slot{Spec.OrdRec{Spec.Paid{}, am, oc, orf}, pv} Spec.PaymentDeclined{_}:
      ft_absurd({k == q : Nat} & {Spec.rec_of(Spec.prov_of(sl0)) == Spec.Approved{} : Spec.Res}, hw)
    case Spec.Slot{Spec.OrdRec{Spec.Failed{}, am, oc, orf}, pv} Spec.PaymentDeclined{_}:
      ft_absurd({k == q : Nat} & {Spec.rec_of(Spec.prov_of(sl0)) == Spec.Approved{} : Spec.Res}, hw)
    case Spec.Slot{Spec.OrdRec{Spec.Refunded{}, am, oc, orf}, pv} Spec.PaymentDeclined{_}:
      ft_absurd({k == q : Nat} & {Spec.rec_of(Spec.prov_of(sl0)) == Spec.Approved{} : Spec.Res}, hw)
    case Spec.Slot{Spec.OrdRec{Spec.NoOrder{}, am, oc, orf}, pv} Spec.RefundOrder{_}:
      ft_absurd({k == q : Nat} & {Spec.rec_of(Spec.prov_of(sl0)) == Spec.Approved{} : Spec.Res}, hw)
    case Spec.Slot{Spec.OrdRec{Spec.AwaitingPayment{}, am, oc, orf}, pv} Spec.RefundOrder{_}:
      ft_absurd({k == q : Nat} & {Spec.rec_of(Spec.prov_of(sl0)) == Spec.Approved{} : Spec.Res}, hw)
    case Spec.Slot{Spec.OrdRec{Spec.Paid{}, am, oc, orf}, pv} Spec.RefundOrder{_}:
      ft_absurd({k == q : Nat} & {Spec.rec_of(Spec.prov_of(sl0)) == Spec.Approved{} : Spec.Res}, hw)
    case Spec.Slot{Spec.OrdRec{Spec.Failed{}, am, oc, orf}, pv} Spec.RefundOrder{_}:
      ft_absurd({k == q : Nat} & {Spec.rec_of(Spec.prov_of(sl0)) == Spec.Approved{} : Spec.Res}, hw)
    case Spec.Slot{Spec.OrdRec{Spec.Refunded{}, am, oc, orf}, pv} Spec.RefundOrder{_}:
      ft_absurd({k == q : Nat} & {Spec.rec_of(Spec.prov_of(sl0)) == Spec.Approved{} : Spec.Res}, hw)
    case Spec.Slot{Spec.OrdRec{x, am, True{}, orf}, pv} Spec.FlushChargeReq{_}:
      ft_absurd({k == q : Nat} & {Spec.rec_of(Spec.prov_of(sl0)) == Spec.Approved{} : Spec.Res}, hw)
    case Spec.Slot{Spec.OrdRec{x, am, False{}, orf}, pv} Spec.FlushChargeReq{_}:
      ft_absurd({k == q : Nat} & {Spec.rec_of(Spec.prov_of(sl0)) == Spec.Approved{} : Spec.Res}, hw)
    case Spec.Slot{Spec.OrdRec{x, am, oc, False{}}, pv} Spec.FlushRefundReq{_}:
      ft_absurd({k == q : Nat} & {Spec.rec_of(Spec.prov_of(sl0)) == Spec.Approved{} : Spec.Res}, hw)
    case Spec.Slot{Spec.OrdRec{x, am, oc, True{}}, pv} Spec.FlushRefundReq{_}:
      ft_absurd({k == q : Nat} & {Spec.rec_of(Spec.prov_of(sl0)) == Spec.Approved{} : Spec.Res}, hw)
    case Spec.Slot{od, Spec.ProvRec{Spec.NoRec{}, cc, rc, am, orr}} Spec.ChargeReqRecv{_, 0n, _}:
      ft_absurd({k == q : Nat} & {Spec.rec_of(Spec.prov_of(sl0)) == Spec.Approved{} : Spec.Res}, hw)
    case Spec.Slot{od, Spec.ProvRec{Spec.NoRec{}, cc, rc, am, orr}} Spec.ChargeReqRecv{_, 1n+pa, Spec.Approve{}}:
      ft_absurd({k == q : Nat} & {Spec.rec_of(Spec.prov_of(sl0)) == Spec.Approved{} : Spec.Res}, hw)
    case Spec.Slot{od, Spec.ProvRec{Spec.NoRec{}, cc, rc, am, orr}} Spec.ChargeReqRecv{_, 1n+pa, Spec.Decline{}}:
      ft_absurd({k == q : Nat} & {Spec.rec_of(Spec.prov_of(sl0)) == Spec.Approved{} : Spec.Res}, hw)
    case Spec.Slot{od, Spec.ProvRec{Spec.Approved{}, cc, rc, am, orr}} Spec.ChargeReqRecv{_, 0n, _}:
      ft_absurd({k == q : Nat} & {Spec.rec_of(Spec.prov_of(sl0)) == Spec.Approved{} : Spec.Res}, hw)
    case Spec.Slot{od, Spec.ProvRec{Spec.Approved{}, cc, rc, am, orr}} Spec.ChargeReqRecv{_, 1n+pa, _}:
      ft_absurd({k == q : Nat} & {Spec.rec_of(Spec.prov_of(sl0)) == Spec.Approved{} : Spec.Res}, hw)
    case Spec.Slot{od, Spec.ProvRec{Spec.Declined{}, cc, rc, am, orr}} Spec.ChargeReqRecv{_, 0n, _}:
      ft_absurd({k == q : Nat} & {Spec.rec_of(Spec.prov_of(sl0)) == Spec.Approved{} : Spec.Res}, hw)
    case Spec.Slot{od, Spec.ProvRec{Spec.Declined{}, cc, rc, am, orr}} Spec.ChargeReqRecv{_, 1n+pa, _}:
      ft_absurd({k == q : Nat} & {Spec.rec_of(Spec.prov_of(sl0)) == Spec.Approved{} : Spec.Res}, hw)
    case Spec.Slot{od, Spec.ProvRec{r, cc, rc, am, orr}} Spec.RefundReqRecv{_}:
      wd_rp(od, r, cc, rc, am, orr, k, q, ex, Nat.is_lt(rc, cc), hw)
    case Spec.Slot{od, Spec.ProvRec{Spec.NoRec{}, cc, rc, am, True{}}} Spec.FlushReply{_}:
      ft_absurd({k == q : Nat} & {Spec.rec_of(Spec.prov_of(sl0)) == Spec.Approved{} : Spec.Res}, hw)
    case Spec.Slot{od, Spec.ProvRec{Spec.NoRec{}, cc, rc, am, False{}}} Spec.FlushReply{_}:
      ft_absurd({k == q : Nat} & {Spec.rec_of(Spec.prov_of(sl0)) == Spec.Approved{} : Spec.Res}, hw)
    case Spec.Slot{od, Spec.ProvRec{Spec.Approved{}, cc, rc, am, True{}}} Spec.FlushReply{_}:
      ft_absurd({k == q : Nat} & {Spec.rec_of(Spec.prov_of(sl0)) == Spec.Approved{} : Spec.Res}, hw)
    case Spec.Slot{od, Spec.ProvRec{Spec.Approved{}, cc, rc, am, False{}}} Spec.FlushReply{_}:
      ft_absurd({k == q : Nat} & {Spec.rec_of(Spec.prov_of(sl0)) == Spec.Approved{} : Spec.Res}, hw)
    case Spec.Slot{od, Spec.ProvRec{Spec.Declined{}, cc, rc, am, True{}}} Spec.FlushReply{_}:
      ft_absurd({k == q : Nat} & {Spec.rec_of(Spec.prov_of(sl0)) == Spec.Approved{} : Spec.Res}, hw)
    case Spec.Slot{od, Spec.ProvRec{Spec.Declined{}, cc, rc, am, False{}}} Spec.FlushReply{_}:
      ft_absurd({k == q : Nat} & {Spec.rec_of(Spec.prov_of(sl0)) == Spec.Approved{} : Spec.Res}, hw)
    case Spec.Slot{od, pv} Spec.Crash{_}:
      ft_absurd({k == q : Nat} & {Spec.rec_of(Spec.prov_of(sl0)) == Spec.Approved{} : Spec.Res}, hw)
    case Spec.Slot{od, pv} Spec.Restart{_}:
      ft_absurd({k == q : Nat} & {Spec.rec_of(Spec.prov_of(sl0)) == Spec.Approved{} : Spec.Res}, hw)

def wr_fin(+sl: +List<Spec.Slot>, +i: Nat, +o: Nat, p: {i == o : Nat} & {Spec.status_of(Spec.ord_of(Spec.get_l(sl, i))) == Spec.Refunded{} : Spec.Status}) -> {Spec.status_of(Spec.ord_of(Spec.get_l(sl, o))) == Spec.Refunded{} : Spec.Status}:
  match p:
    case (e1, e2):
      %e1 : {Spec.status_of(Spec.ord_of(Spec.get_l(sl, _))) == Spec.Refunded{} : Spec.Status}
      e2

def wd_fin(+sl: +List<Spec.Slot>, +i: Nat, +o: Nat, p: {i == o : Nat} & {Spec.rec_of(Spec.prov_of(Spec.get_l(sl, i))) == Spec.Approved{} : Spec.Res}) -> {Spec.rec_of(Spec.prov_of(Spec.get_l(sl, o))) == Spec.Approved{} : Spec.Res}:
  match p:
    case (e1, e2):
      %e1 : {Spec.rec_of(Spec.prov_of(Spec.get_l(sl, _))) == Spec.Approved{} : Spec.Res}
      e2

def p2b_c_l(+s: Spec.State, +e: Spec.Ev, +o: Nat, +h: {Spec.inv(s) == True{} : Bool}, +hw: {Spec.has(Code.snd(Code.step(s, e)), Spec.WireRefundReq{o}) == True{} : Bool}) -> {Spec.st(s, o) == Spec.Refunded{} : Spec.Status}:
  match s:
    case Spec.State{sl, ou, pu}:
      wr_fin(sl, Spec.ev_idx(e), o, wr_slot(Spec.get_l(sl, Spec.ev_idx(e)), Spec.ev_idx(e), e, o, inv_get(sl, Spec.ev_idx(e), h), fx_step(s, e, Spec.WireRefundReq{o}, hw)))

def p2b_d_l(+s: Spec.State, +e: Spec.Ev, +o: Nat, +ex: Nat, +hw: {Spec.has(Code.snd(Code.step(s, e)), Spec.Refund{o, ex}) == True{} : Bool}) -> {Spec.rec_of(Spec.pr(s, o)) == Spec.Approved{} : Spec.Res}:
  match s:
    case Spec.State{sl, ou, pu}:
      wd_fin(sl, Spec.ev_idx(e), o, wd_slot(Spec.get_l(sl, Spec.ev_idx(e)), Spec.ev_idx(e), e, o, ex, fx_step(s, e, Spec.Refund{o, ex}, hw)))

def Laws.p2b_c(s, e, o, h, hw):
  p2b_c_l(s, e, o, h, hw)

def Laws.p2b_d(s, e, o, x, h, hw):
  p2b_d_l(s, e, o, x, hw)

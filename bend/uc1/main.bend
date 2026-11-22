import Base
import ./spec.bend as Spec
import ./code.bend as Code

# Conformance runner for harness/conformance. One line on stdin:
#   N  k o a d svc  k o a d svc  ...   (ASCII digits, single spaces)
# Every event has five fields; unused ones are 0. k is the Go Kind number
# (0 PlaceOrder .. 11 Restart), d is 0 Approve / 1 Decline, svc is 0 OrderSvc /
# 1 Provider. N, o and a are capped at 100000 (Nat is unary). Anything else
# (non-digit, overflow, bad k/d/svc, field count not 5 per event, not exactly
# one line) exits 1. Output: one `key=value` line, the final State and the
# count, order-id sum and amount sum of each effect kind. Input of 16 MiB or more
# is an error (File.read would truncate it). Status numbers follow Go: NoOrder is 0.

type Parse is Data:
  Bad{msg: String}
  Good{evs: +List<Spec.Ev>}

type Nums is Data:
  BadNum{msg: String}
  GoodNums{ns: +List<Nat>}

# per effect kind: how many, and the U32 (wrapping) sums of the order id and amount
type Tot is Data:
  Tot{n: Nat, so: U32, sa: U32}

type Cnt is Data:
  Cnt{wc: Tot, wr: Tot, wa: Tot, wd: Tot, ch: Tot, rf: Tot}

# ------------------------------------------------------------------- input
def cap() -> U32:
  100000

def capped(n: U32, ok: Bool) -> Maybe<&2, Nat>:
  match ok:
    case True{}:
      Some{U32.to_nat(n)}
    case False{}:
      None{}

def conv(m: Maybe<&2, U32>) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      None{}
    case Some{+n}:
      capped(n, U32.is_le(n, cap()))

def cons_num(n: Nat, r: Nums) -> Nums:
  match r:
    case BadNum{m}:
      BadNum{m}
    case GoodNums{ns}:
      GoodNums{n <> ns}

def num_then(m: Maybe<&2, Nat>, r: Nums) -> Nums:
  match m:
    case None{}:
      BadNum{"bad number"}
    case Some{n}:
      cons_num(n, r)

def nums(ws: List<&2, String>) -> Nums:
  match ws:
    case Nil{}:
      GoodNums{Nil{}}
    case w <> t:
      num_then(conv(U32.read(w)), nums(t))

def mk_dec(d: Nat) -> Spec.Dec:
  match d:
    case 0n:
      Spec.Approve{}
    case _:
      Spec.Decline{}

def mk_svc(v: Nat) -> Spec.Svc:
  match v:
    case 0n:
      Spec.OrderSvc{}
    case _:
      Spec.Provider{}

def mk_ev(k: Nat, o: Nat, a: Nat, d: Nat, v: Nat) -> Spec.Ev:
  match k:
    case 0n:
      Spec.PlaceOrder{o, a}
    case 1n:
      Spec.RetryTimeout{o}
    case 2n:
      Spec.FlushChargeReq{o}
    case 3n:
      Spec.FlushRefundReq{o}
    case 4n:
      Spec.PaymentApproved{o}
    case 5n:
      Spec.PaymentDeclined{o}
    case 6n:
      Spec.RefundOrder{o}
    case 7n:
      Spec.ChargeReqRecv{o, a, mk_dec(d)}
    case 8n:
      Spec.RefundReqRecv{o}
    case 9n:
      Spec.FlushReply{o}
    case 10n:
      Spec.Crash{mk_svc(v)}
    case _:
      Spec.Restart{mk_svc(v)}

def fields_ok(k: Nat, d: Nat, v: Nat) -> Bool:
  Bool.and(Nat.is_lt(k, 12n), Bool.and(Nat.is_lt(d, 2n), Nat.is_lt(v, 2n)))

def cons_ev(e: Spec.Ev, r: Parse) -> Parse:
  match r:
    case Bad{m}:
      Bad{m}
    case Good{es}:
      Good{e <> es}

def ev_or_bad(ok: Bool, e: Spec.Ev, r: Parse) -> Parse:
  match ok:
    case True{}:
      cons_ev(e, r)
    case False{}:
      Bad{"bad kind, decision or service"}

# groups of five numbers, one event each; leftover numbers are an error
def groups(ns: +List<Nat>) -> Parse:
  match ns:
    case Nil{}:
      Good{Nil{}}
    case +k <> r1:
      match r1:
        case Nil{}:
          Bad{"incomplete event"}
        case o <> r2:
          match r2:
            case Nil{}:
              Bad{"incomplete event"}
            case a <> r3:
              match r3:
                case Nil{}:
                  Bad{"incomplete event"}
                case +d <> r4:
                  match r4:
                    case Nil{}:
                      Bad{"incomplete event"}
                    case +v <> r5:
                      ev_or_bad(fields_ok(k, d, v), mk_ev(k, o, a, d, v), groups(r5))

# ------------------------------------------------------------------- run
def tot(t: Tot, o: Nat, a: Nat) -> Tot:
  match t:
    case Tot{n, so, sa}:
      Tot{1n+n, U32.add(so, U32.from_nat(o)), U32.add(sa, U32.from_nat(a))}

def count(c: Cnt, f: Spec.Effect) -> Cnt:
  match c f:
    case Cnt{a, b, x, d, e, g} Spec.WireChargeReq{o, am}:
      Cnt{tot(a, o, am), b, x, d, e, g}
    case Cnt{a, b, x, d, e, g} Spec.WireRefundReq{o}:
      Cnt{a, tot(b, o, 0n), x, d, e, g}
    case Cnt{a, b, x, d, e, g} Spec.WireApproved{o}:
      Cnt{a, b, tot(x, o, 0n), d, e, g}
    case Cnt{a, b, x, d, e, g} Spec.WireDeclined{o}:
      Cnt{a, b, x, tot(d, o, 0n), e, g}
    case Cnt{a, b, x, d, e, g} Spec.Charge{o, am}:
      Cnt{a, b, x, d, tot(e, o, am), g}
    case Cnt{a, b, x, d, e, g} Spec.Refund{o, am}:
      Cnt{a, b, x, d, e, tot(g, o, am)}

def count_all(fx: List<Spec.Effect>, c: Cnt) -> Cnt:
  match fx:
    case Nil{}:
      c
    case f <> t:
      count_all(t, count(c, f))

def fold_step(r: Spec.State & List<Spec.Effect>, c: Cnt) -> Spec.State & Cnt:
  match r:
    case (s, fx):
      (s, count_all(fx, c))

def step_cnt(r: Spec.State & Cnt, e: Spec.Ev) -> Spec.State & Cnt:
  match r:
    case (s, c):
      fold_step(Code.step(s, e), c)

# same fold as Code.run, keeping the effect counts. events first (termination)
def run_fx(events: +List<Spec.Ev>, r: Spec.State & Cnt) -> Spec.State & Cnt:
  match events:
    case Nil{}:
      r
    case e <> t:
      run_fx(t, step_cnt(r, e))

# ------------------------------------------------------------------- output
def bit(x: Bool) -> String:
  match x:
    case True{}:
      "1"
    case False{}:
      "0"

def status_n(x: Spec.Status) -> String:
  match x:
    case Spec.NoOrder{}:
      "0"
    case Spec.AwaitingPayment{}:
      "1"
    case Spec.Paid{}:
      "2"
    case Spec.Failed{}:
      "3"
    case Spec.Refunded{}:
      "4"

def res_n(x: Spec.Res) -> String:
  match x:
    case Spec.NoRec{}:
      "0"
    case Spec.Approved{}:
      "1"
    case Spec.Declined{}:
      "2"

def show_slot(+i: Nat, sl: Spec.Slot) -> String:
  match sl:
    case Spec.Slot{Spec.OrdRec{x, am, oc, orf}, Spec.ProvRec{r, cc, rc, amt, orr}}:
      " s" ++ Nat.show(i) ++ ".status=" ++ status_n(x) ++ " s" ++ Nat.show(i) ++ ".amount=" ++ Nat.show(am) ++ " s" ++ Nat.show(i) ++ ".outCharge=" ++ bit(oc) ++ " s" ++ Nat.show(i) ++ ".outRefund=" ++ bit(orf) ++ " s" ++ Nat.show(i) ++ ".rec=" ++ res_n(r) ++ " s" ++ Nat.show(i) ++ ".chargeCount=" ++ Nat.show(cc) ++ " s" ++ Nat.show(i) ++ ".refundCount=" ++ Nat.show(rc) ++ " s" ++ Nat.show(i) ++ ".amt=" ++ Nat.show(amt) ++ " s" ++ Nat.show(i) ++ ".outReply=" ++ bit(orr)

def show_slots(sl: +List<Spec.Slot>, +i: Nat) -> String:
  match sl:
    case Nil{}:
      ""
    case h <> t:
      show_slot(i, h) ++ show_slots(t, 1n+i)

def show_tot(+name: String, t: Tot) -> String:
  match t:
    case Tot{n, so, sa}:
      " fx." ++ name ++ "=" ++ Nat.show(n) ++ " fx." ++ name ++ ".o=" ++ U32.show(so) ++ " fx." ++ name ++ ".a=" ++ U32.show(sa)

def show_cnt(c: Cnt) -> String:
  match c:
    case Cnt{a, bb, x, d, e, g}:
      show_tot("WireChargeReq", a) ++ show_tot("WireRefundReq", bb) ++ show_tot("WireApproved", x) ++ show_tot("WireDeclined", d) ++ show_tot("Charge", e) ++ show_tot("Refund", g)

def show(r: Spec.State & Cnt) -> String:
  match r:
    case (Spec.State{sl, ou, pu}, c):
      "orderUp=" ++ bit(ou) ++ " provUp=" ++ bit(pu) ++ show_slots(sl, 0n) ++ show_cnt(c)

def finish(n: Nat, es: +List<Spec.Ev>) -> String:
  show(run_fx(es, (Spec.init(n), Cnt{Tot{0n, 0, 0}, Tot{0n, 0, 0}, Tot{0n, 0, 0}, Tot{0n, 0, 0}, Tot{0n, 0, 0}, Tot{0n, 0, 0}})))

type Out is Data:
  Err{msg: String}
  Okay{line: String}

def solve_with(n: Nat, p: Parse) -> Out:
  match p:
    case Bad{m}:
      Err{m}
    case Good{es}:
      Okay{finish(n, es)}

def solve(ns: +List<Nat>) -> Out:
  match ns:
    case Nil{}:
      Err{"missing N"}
    case n <> t:
      solve_with(n, groups(t))

def solve_nums(r: Nums) -> Out:
  match r:
    case BadNum{m}:
      Err{m}
    case GoodNums{ns}:
      solve(ns)

def only_line(l: String, empty: Bool) -> Out:
  match empty:
    case True{}:
      solve_nums(nums(String.split(l, ' ')))
    case False{}:
      Err{"expected exactly one line"}

# one line, with or without its final newline (split gives a trailing "")
def one_line(ls: List<&2, String>) -> Out:
  match ls:
    case l <> Nil{}:
      only_line(l, True{})
    case l <> e <> Nil{}:
      only_line(l, String.is_empty(e))
    case _:
      Err{"expected exactly one line"}

def exec_ok(text: String, big: Bool) -> Out:
  match big:
    case True{}:
      Err{"input too large (16 MiB or more)"}
    case False{}:
      one_line(String.lines(text))

# File.read stops at 16 MiB; input that fills it may have been cut, so it is an error
def exec(+text: String) -> Out:
  exec_ok(text, Nat.is_ge(String.length(text), 16777216n))

def emit(o: Out) -> IO(Unit):
  match o:
    case Err{m}:
      IO.die(Unit, 1, "error=" ++ m)
    case Okay{line}:
      IO.print(line)

def done(r: File & Result<&1, &1, U32 & String, String>) -> IO(Unit):
  (f, res) = r
  do IO<Unit>:
    text : String <- IO.pass(String, res)
    File.close(f)
    emit(exec(text))

def main() -> IO(Unit):
  do IO<Unit>:
    f : File <- IO.try(File, File.open("/dev/stdin", "r"))
    r : File & Result<&1, &1, U32 & String, String> <- File.read(f, 16777216)
    done(r)

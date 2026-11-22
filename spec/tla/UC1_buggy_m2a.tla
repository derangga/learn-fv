---- MODULE UC1_buggy_m2a ----
\* MUTANT M2A (properties/UC1.md section 5): refund without a status check: RefundOrder sets Refunded and queues the refund row in any status.
\* Copy of UC1.tla; only the lines marked "M2A:" differ (see `diff UC1.tla UC1_buggy_m2a.tla`).
\* Bounds are those of UC1.cfg.
\* UC1: idempotent payment (order service and payment provider, with retries).
\* Mirrors properties/UC1.md sections 2 to 4 directly. Bounds live in UC1.cfg.
EXTENDS Naturals, Integers, Sequences, FiniteSets

CONSTANTS N, Amounts, DupMax, MaxCrashes, MaxRetries
ASSUME N \in Nat /\ N > 0
ASSUME Amounts \subseteq Nat \ {0}
ASSUME DupMax \in Nat /\ MaxCrashes \in Nat /\ MaxRetries \in Nat

VARIABLES slots, orderUp, provUp, net, dup, crashes, retries, lastEvent, lastFx
vars == <<slots, orderUp, provUp, net, dup, crashes, retries, lastEvent, lastFx>>

\* ---------------------------------------------------------------- state model
OrdIds == 0..(N - 1)
Svcs == {"OrderSvc", "Provider"}
Statuses == {"None", "AwaitingPayment", "Paid", "Failed", "Refunded"}
Ress == {"NoRec", "Approved", "Declined"}
Decisions == {"Approve", "Decline"}

DefOrd == [status |-> "None", amount |-> 0, outCharge |-> FALSE, outRefund |-> FALSE]
DefProv == [rec |-> "NoRec", chargeCount |-> 0, refundCount |-> 0, amt |-> 0, outReply |-> FALSE]
DefSlot == [ord |-> DefOrd, prov |-> DefProv]

\* The contract state S = { slots, orderUp, provUp }.
S == [slots |-> slots, orderUp |-> orderUp, provUp |-> provUp]

get(s, o) == IF o \in DOMAIN s.slots THEN s.slots[o] ELSE DefSlot
st(s, o) == get(s, o).ord.status
pr(s, o) == get(s, o).prov
od(s, o) == get(s, o).ord
IsTerminal(x) == x \in {"Failed", "Refunded"}

\* Effects: uniform record, a = 0 where the effect has no amount.
Eff(t, o, a) == [t |-> t, o |-> o, a |-> a]
HasFx(fx, t, o) == \E i \in DOMAIN fx : fx[i].t = t /\ fx[i].o = o

\* ---------------------------------------------------------------------- Step
OrderKinds == {"PlaceOrder", "RetryTimeout", "FlushChargeReq", "FlushRefundReq",
               "PaymentApproved", "PaymentDeclined", "RefundOrder"}

Out(state, fx) == [state |-> state, fx |-> fx]
WithSlot(s, o, ordR, provR) == [s EXCEPT !.slots[o] = [ord |-> ordR, prov |-> provR]]

\* Step(s, e) -> [state, fx]; total and deterministic. Rule D and frame F as in section 3.
Step(s, e) ==
  LET k == e.kind IN
  IF k = "Crash" THEN
    Out([s EXCEPT !.orderUp = IF e.svc = "OrderSvc" THEN FALSE ELSE s.orderUp,
                  !.provUp = IF e.svc = "Provider" THEN FALSE ELSE s.provUp], <<>>)
  ELSE IF k = "Restart" THEN
    Out([s EXCEPT !.orderUp = IF e.svc = "OrderSvc" THEN TRUE ELSE s.orderUp,
                  !.provUp = IF e.svc = "Provider" THEN TRUE ELSE s.provUp], <<>>)
  ELSE
    LET up == IF k \in OrderKinds THEN s.orderUp ELSE s.provUp IN
    IF ~up \/ ~(e.o \in DOMAIN s.slots) THEN Out(s, <<>>)          \* rule D
    ELSE
      LET o == e.o
          sl == s.slots[o]
          O == sl.ord
          P == sl.prov
      IN
      CASE k = "PlaceOrder" ->                                           \* A1
             IF e.a > 0 /\ O.status = "None"
             THEN Out(WithSlot(s, o, [O EXCEPT !.status = "AwaitingPayment", !.amount = e.a,
                                               !.outCharge = TRUE], P), <<>>)
             ELSE Out(s, <<>>)
        [] k = "RetryTimeout" ->                                         \* A2
             IF O.status = "AwaitingPayment"
             THEN Out(WithSlot(s, o, [O EXCEPT !.outCharge = TRUE], P), <<>>)
             ELSE Out(s, <<>>)
        [] k = "FlushChargeReq" ->                                       \* A3
             IF O.outCharge
             THEN Out(WithSlot(s, o, [O EXCEPT !.outCharge = FALSE], P),
                      <<Eff("WireChargeReq", o, O.amount)>>)
             ELSE Out(s, <<>>)
        [] k = "PaymentApproved" ->                                      \* A4
             IF O.status = "AwaitingPayment"
             THEN Out(WithSlot(s, o, [O EXCEPT !.status = "Paid"], P), <<>>)
             ELSE Out(s, <<>>)
        [] k = "PaymentDeclined" ->                                      \* A5
             IF O.status = "AwaitingPayment"
             THEN Out(WithSlot(s, o, [O EXCEPT !.status = "Failed"], P), <<>>)
             ELSE Out(s, <<>>)
        [] k = "RefundOrder" ->                                          \* A6
             IF TRUE                                                     \* M2A: no status check
             THEN Out(WithSlot(s, o, [O EXCEPT !.status = "Refunded", !.outRefund = TRUE], P), <<>>)
             ELSE Out(s, <<>>)
        [] k = "FlushRefundReq" ->                                       \* A7
             IF O.outRefund
             THEN Out(WithSlot(s, o, [O EXCEPT !.outRefund = FALSE], P),
                      <<Eff("WireRefundReq", o, 0)>>)
             ELSE Out(s, <<>>)
        [] k = "ChargeReqRecv" ->                                        \* A8
             IF e.a = 0 THEN Out(s, <<>>)
             ELSE IF P.rec = "NoRec" THEN
               IF e.d = "Approve"
               THEN Out(WithSlot(s, o, O, [P EXCEPT !.rec = "Approved", !.chargeCount = @ + 1,
                                                    !.amt = e.a, !.outReply = TRUE]),
                        <<Eff("Charge", o, e.a)>>)
               ELSE Out(WithSlot(s, o, O, [P EXCEPT !.rec = "Declined", !.outReply = TRUE]), <<>>)
             ELSE Out(WithSlot(s, o, O, [P EXCEPT !.outReply = TRUE]), <<>>)
        [] k = "FlushReply" ->                                           \* A9
             IF P.outReply /\ P.rec # "NoRec"
             THEN Out(WithSlot(s, o, O, [P EXCEPT !.outReply = FALSE]),
                      <<Eff(IF P.rec = "Approved" THEN "WireApproved" ELSE "WireDeclined", o, 0)>>)
             ELSE Out(s, <<>>)
        [] k = "RefundReqRecv" ->                                        \* A10
             IF P.rec = "Approved" /\ P.refundCount < P.chargeCount
             THEN Out(WithSlot(s, o, O, [P EXCEPT !.refundCount = @ + 1]),
                      <<Eff("Refund", o, P.amt)>>)
             ELSE Out(s, <<>>)
        [] OTHER -> Out(s, <<>>)

\* -------------------------------------------------------------------- network
ChargeReqMsg(o, a) == [t |-> "ChargeReq", o |-> o, a |-> a]
RefundReqMsg(o) == [t |-> "RefundReq", o |-> o, a |-> 0]
ApprovedMsg(o) == [t |-> "Approved", o |-> o, a |-> 0]
DeclinedMsg(o) == [t |-> "Declined", o |-> o, a |-> 0]

MsgSet == {ChargeReqMsg(o, a) : o \in OrdIds, a \in Amounts}
          \cup {RefundReqMsg(o) : o \in OrdIds}
          \cup {ApprovedMsg(o) : o \in OrdIds}
          \cup {DeclinedMsg(o) : o \in OrdIds}

\* Upper bound on copies of one message: at most 1 + MaxRetries flushes, plus a reply per
\* delivery, plus DupMax duplicates. Only used by TypeOK; a wrong bound shows as a TypeOK failure.
NetMax == MaxRetries + 1 + 2 * DupMax

WireMsg(f) ==
  CASE f.t = "WireChargeReq" -> ChargeReqMsg(f.o, f.a)
    [] f.t = "WireRefundReq" -> RefundReqMsg(f.o)
    [] f.t = "WireApproved" -> ApprovedMsg(f.o)
    [] f.t = "WireDeclined" -> DeclinedMsg(f.o)

IsWire(f) == f.t \in {"WireChargeReq", "WireRefundReq", "WireApproved", "WireDeclined"}

AddWire(n, fx) ==
  IF fx # <<>> /\ IsWire(fx[1]) THEN [n EXCEPT ![WireMsg(fx[1])] = @ + 1] ELSE n

\* Run Step on e; put the wire effects on bag n0; record the step.
DoStep(e, n0) ==
  LET r == Step(S, e) IN
  /\ slots' = r.state.slots
  /\ orderUp' = r.state.orderUp
  /\ provUp' = r.state.provUp
  /\ net' = AddWire(n0, r.fx)
  /\ lastEvent' = e
  /\ lastFx' = r.fx

\* ----------------------------------------------------------------------- Init
Init ==
  /\ slots = [o \in OrdIds |-> DefSlot]
  /\ orderUp = TRUE
  /\ provUp = TRUE
  /\ net = [m \in MsgSet |-> 0]
  /\ dup = [m \in MsgSet |-> 0]
  /\ crashes = [v \in Svcs |-> 0]
  /\ retries = [o \in OrdIds |-> 0]
  /\ lastEvent = [kind |-> "Init"]
  /\ lastFx = <<>>

\* -------------------------------------------------------------------- actions
PlaceOrder(o, a) ==
  /\ DoStep([kind |-> "PlaceOrder", o |-> o, a |-> a], net)
  /\ UNCHANGED <<dup, crashes, retries>>

RetryTimeout(o) ==
  /\ retries[o] < MaxRetries
  /\ DoStep([kind |-> "RetryTimeout", o |-> o], net)
  /\ retries' = [retries EXCEPT ![o] = @ + 1]
  /\ UNCHANGED <<dup, crashes>>

RefundOrder(o) ==
  /\ DoStep([kind |-> "RefundOrder", o |-> o], net)
  /\ UNCHANGED <<dup, crashes, retries>>

ClientAction ==
  \/ \E o \in OrdIds, a \in Amounts : PlaceOrder(o, a)
  \/ \E o \in OrdIds : RetryTimeout(o)
  \/ \E o \in OrdIds : RefundOrder(o)

Flush(kind, o) ==
  /\ DoStep([kind |-> kind, o |-> o], net)
  /\ UNCHANGED <<dup, crashes, retries>>

OutboxFlush ==
  \E o \in OrdIds : \/ Flush("FlushChargeReq", o)
                    \/ Flush("FlushRefundReq", o)
                    \/ Flush("FlushReply", o)

\* Delivery: pick any message in net (delay, reorder), remove one copy, run Step.
Deliver ==
  \E m \in MsgSet :
    /\ net[m] > 0
    /\ LET n1 == [net EXCEPT ![m] = @ - 1] IN
       \/ m.t = "ChargeReq"
          /\ \E d \in Decisions :
               DoStep([kind |-> "ChargeReqRecv", o |-> m.o, a |-> m.a, d |-> d], n1)
       \/ m.t = "RefundReq" /\ DoStep([kind |-> "RefundReqRecv", o |-> m.o], n1)
       \/ m.t = "Approved" /\ DoStep([kind |-> "PaymentApproved", o |-> m.o], n1)
       \/ m.t = "Declined" /\ DoStep([kind |-> "PaymentDeclined", o |-> m.o], n1)
    /\ UNCHANGED <<dup, crashes, retries>>

Drop(m) ==
  /\ net[m] > 0
  /\ net' = [net EXCEPT ![m] = @ - 1]
  /\ lastEvent' = [kind |-> "Drop"]
  /\ lastFx' = <<>>
  /\ UNCHANGED <<slots, orderUp, provUp, dup, crashes, retries>>

Duplicate(m) ==
  /\ net[m] > 0
  /\ dup[m] < DupMax
  /\ net' = [net EXCEPT ![m] = @ + 1]
  /\ dup' = [dup EXCEPT ![m] = @ + 1]
  /\ lastEvent' = [kind |-> "Duplicate"]
  /\ lastFx' = <<>>
  /\ UNCHANGED <<slots, orderUp, provUp, crashes, retries>>

IsUp(svc) == IF svc = "OrderSvc" THEN orderUp ELSE provUp

Crash(svc) ==
  /\ IsUp(svc)
  /\ crashes[svc] < MaxCrashes
  /\ DoStep([kind |-> "Crash", svc |-> svc], net)
  /\ crashes' = [crashes EXCEPT ![svc] = @ + 1]
  /\ UNCHANGED <<dup, retries>>

Restart(svc) ==
  /\ ~IsUp(svc)
  /\ DoStep([kind |-> "Restart", svc |-> svc], net)
  /\ UNCHANGED <<dup, crashes, retries>>

Next ==
  \/ ClientAction
  \/ OutboxFlush
  \/ Deliver
  \/ \E m \in MsgSet : Drop(m) \/ Duplicate(m)
  \/ \E svc \in Svcs : Crash(svc) \/ Restart(svc)

Spec == Init /\ [][Next]_vars

\* ------------------------------------------------------------------- TypeOK
EventSet ==
  {[kind |-> "Init"]}
  \cup [kind : {"PlaceOrder"}, o : OrdIds, a : Amounts]
  \cup [kind : {"RetryTimeout", "FlushChargeReq", "FlushRefundReq", "PaymentApproved",
                "PaymentDeclined", "RefundOrder", "RefundReqRecv", "FlushReply"}, o : OrdIds]
  \cup [kind : {"ChargeReqRecv"}, o : OrdIds, a : Amounts, d : Decisions]
  \cup [kind : {"Crash", "Restart"}, svc : Svcs]
  \cup [kind : {"Drop", "Duplicate"}]

EffSet ==
  [t : {"Charge", "Refund", "WireChargeReq", "WireRefundReq", "WireApproved", "WireDeclined"},
   o : OrdIds, a : Amounts \cup {0}]

TypeOK ==
  \* Counts are Nat, not 0..1, so TypeOK does not bake in P1/P2a (those are Inv/NoDoubleCharge).
  /\ slots \in [OrdIds -> [ord : [status : Statuses, amount : {0} \cup Amounts,
                                  outCharge : BOOLEAN, outRefund : BOOLEAN],
                           prov : [rec : Ress, chargeCount : Nat, refundCount : Nat,
                                   amt : {0} \cup Amounts, outReply : BOOLEAN]]]
  /\ orderUp \in BOOLEAN
  /\ provUp \in BOOLEAN
  /\ net \in [MsgSet -> 0..NetMax]
  /\ dup \in [MsgSet -> 0..DupMax]
  /\ crashes \in [Svcs -> 0..MaxCrashes]
  /\ retries \in [OrdIds -> 0..MaxRetries]
  /\ lastEvent \in EventSet
  /\ lastFx \in {<<>>} \cup {<<f>> : f \in EffSet}

\* ----------------------------------------------------------------- invariants
Inv ==
  \A o \in OrdIds :
    /\ pr(S, o).chargeCount = IF pr(S, o).rec = "Approved" THEN 1 ELSE 0
    /\ pr(S, o).refundCount <= pr(S, o).chargeCount
    /\ od(S, o).outRefund => st(S, o) = "Refunded"
    /\ od(S, o).outCharge => st(S, o) # "None"

NoDoubleCharge == \A o \in OrdIds : pr(S, o).chargeCount <= 1                         \* P1
RefundNeverExceedsCharge == \A o \in OrdIds : pr(S, o).refundCount <= pr(S, o).chargeCount  \* P2a

\* --------------------------------------------------- transition properties
\* P2b (a) to (d). Pre-state S, post-state S', effects lastFx'.
RefundedOnlyFromPaid ==
  [][\A o \in OrdIds :
       /\ (st(S, o) # "Refunded" /\ st(S', o) = "Refunded") => st(S, o) = "Paid"
       /\ (~od(S, o).outRefund /\ od(S', o).outRefund) => st(S, o) = "Paid"
       /\ HasFx(lastFx', "WireRefundReq", o) => st(S, o) = "Refunded"
       /\ HasFx(lastFx', "Refund", o) => pr(S, o).rec = "Approved"]_vars

\* P3 (with the amount clause).
TerminalStable ==
  [][\A o \in OrdIds :
       IsTerminal(st(S, o)) => /\ st(S', o) = st(S, o)
                               /\ od(S', o).amount = od(S, o).amount]_vars

\* -------------------------------------------------------------- pinning laws
Same == S' = S /\ lastFx' = <<>>
Ups(o, ordR, provR) == WithSlot(S, o, ordR, provR)

PinPlaceOrder ==                                                                  \* A1
  [][lastEvent'.kind = "PlaceOrder" =>
       LET e == lastEvent'  o == e.o IN
       IF orderUp /\ e.a > 0 /\ st(S, o) = "None"
       THEN /\ S' = Ups(o, [od(S, o) EXCEPT !.status = "AwaitingPayment", !.amount = e.a,
                                            !.outCharge = TRUE], pr(S, o))
            /\ lastFx' = <<>>
       ELSE Same]_vars

PinRetryTimeout ==                                                                \* A2
  [][lastEvent'.kind = "RetryTimeout" =>
       LET o == lastEvent'.o IN
       IF orderUp /\ st(S, o) = "AwaitingPayment"
       THEN /\ S' = Ups(o, [od(S, o) EXCEPT !.outCharge = TRUE], pr(S, o))
            /\ lastFx' = <<>>
       ELSE Same]_vars

PinFlushChargeReq ==                                                              \* A3
  [][lastEvent'.kind = "FlushChargeReq" =>
       LET o == lastEvent'.o IN
       IF orderUp /\ od(S, o).outCharge
       THEN /\ S' = Ups(o, [od(S, o) EXCEPT !.outCharge = FALSE], pr(S, o))
            /\ lastFx' = <<Eff("WireChargeReq", o, od(S, o).amount)>>
       ELSE Same]_vars

PinPaymentApproved ==                                                             \* A4
  [][lastEvent'.kind = "PaymentApproved" =>
       LET o == lastEvent'.o IN
       IF orderUp /\ st(S, o) = "AwaitingPayment"
       THEN /\ S' = Ups(o, [od(S, o) EXCEPT !.status = "Paid"], pr(S, o))
            /\ lastFx' = <<>>
       ELSE Same]_vars

PinPaymentDeclined ==                                                             \* A5
  [][lastEvent'.kind = "PaymentDeclined" =>
       LET o == lastEvent'.o IN
       IF orderUp /\ st(S, o) = "AwaitingPayment"
       THEN /\ S' = Ups(o, [od(S, o) EXCEPT !.status = "Failed"], pr(S, o))
            /\ lastFx' = <<>>
       ELSE Same]_vars

PinRefundOrder ==                                                                 \* A6
  [][lastEvent'.kind = "RefundOrder" =>
       LET o == lastEvent'.o IN
       IF orderUp /\ st(S, o) = "Paid"
       THEN /\ S' = Ups(o, [od(S, o) EXCEPT !.status = "Refunded", !.outRefund = TRUE], pr(S, o))
            /\ lastFx' = <<>>
       ELSE Same]_vars

PinFlushRefundReq ==                                                              \* A7
  [][lastEvent'.kind = "FlushRefundReq" =>
       LET o == lastEvent'.o IN
       IF orderUp /\ od(S, o).outRefund
       THEN /\ S' = Ups(o, [od(S, o) EXCEPT !.outRefund = FALSE], pr(S, o))
            /\ lastFx' = <<Eff("WireRefundReq", o, 0)>>
       ELSE Same]_vars

PinChargeReqRecv ==                                                               \* A8
  [][lastEvent'.kind = "ChargeReqRecv" =>
       LET e == lastEvent'  o == e.o  p == pr(S, o) IN
       IF ~provUp \/ e.a = 0 THEN Same
       ELSE IF p.rec = "NoRec" /\ e.d = "Approve"
            THEN /\ S' = Ups(o, od(S, o), [p EXCEPT !.rec = "Approved",
                                                    !.chargeCount = p.chargeCount + 1,
                                                    !.amt = e.a, !.outReply = TRUE])
                 /\ lastFx' = <<Eff("Charge", o, e.a)>>
            ELSE IF p.rec = "NoRec" /\ e.d = "Decline"
            THEN /\ S' = Ups(o, od(S, o), [p EXCEPT !.rec = "Declined", !.outReply = TRUE])
                 /\ lastFx' = <<>>
            ELSE /\ S' = Ups(o, od(S, o), [p EXCEPT !.outReply = TRUE])
                 /\ lastFx' = <<>>]_vars

PinFlushReply ==                                                                  \* A9
  [][lastEvent'.kind = "FlushReply" =>
       LET o == lastEvent'.o  p == pr(S, o) IN
       IF provUp /\ p.outReply /\ p.rec # "NoRec"
       THEN /\ S' = Ups(o, od(S, o), [p EXCEPT !.outReply = FALSE])
            /\ lastFx' = IF p.rec = "Approved" THEN <<Eff("WireApproved", o, 0)>>
                                               ELSE <<Eff("WireDeclined", o, 0)>>
       ELSE Same]_vars

PinRefundReqRecv ==                                                               \* A10
  [][lastEvent'.kind = "RefundReqRecv" =>
       LET o == lastEvent'.o  p == pr(S, o) IN
       IF provUp /\ p.rec = "Approved" /\ p.refundCount < p.chargeCount
       THEN /\ S' = Ups(o, od(S, o), [p EXCEPT !.refundCount = p.refundCount + 1])
            /\ lastFx' = <<Eff("Refund", o, p.amt)>>
       ELSE Same]_vars

PinCrashRestart ==                                                                \* A11
  [][/\ (lastEvent'.kind = "Crash") =>
        (/\ slots' = slots
         /\ orderUp' = (orderUp /\ lastEvent'.svc # "OrderSvc")
         /\ provUp' = (provUp /\ lastEvent'.svc # "Provider")
         /\ lastFx' = <<>>)
     /\ (lastEvent'.kind = "Restart") =>
        (/\ slots' = slots
         /\ orderUp' = (orderUp \/ lastEvent'.svc = "OrderSvc")
         /\ provUp' = (provUp \/ lastEvent'.svc = "Provider")
         /\ lastFx' = <<>>)]_vars

LegalTransitions == {<<"None", "AwaitingPayment">>, <<"AwaitingPayment", "Paid">>,
                     <<"AwaitingPayment", "Failed">>, <<"Paid", "Refunded">>}

PinLegalTransitions ==                                                            \* A12
  [][\A o \in OrdIds :
       st(S', o) # st(S, o) => <<st(S, o), st(S', o)>> \in LegalTransitions]_vars

PinProvRecStable ==                                                               \* A13
  [][\A o \in OrdIds :
       /\ pr(S', o).rec # pr(S, o).rec =>
            /\ pr(S, o).rec = "NoRec"
            /\ pr(S', o).rec \in {"Approved", "Declined"}
       /\ pr(S', o).chargeCount >= pr(S, o).chargeCount
       /\ pr(S', o).refundCount >= pr(S, o).refundCount]_vars

\* --------------------------------------------- reachability witnesses (non-vacuity)
\* Each is a deliberately false invariant; TLC must violate it (see UC1_reach_*.cfg).
ReachPaid == \A o \in OrdIds : st(S, o) # "Paid"
ReachRefunded == \A o \in OrdIds : st(S, o) # "Refunded"
ReachFailed == \A o \in OrdIds : st(S, o) # "Failed"
\* Reply queued while a record exists (also true right after a first request).
ReachReplayFlag == \A o \in OrdIds : ~(pr(S, o).outReply /\ pr(S, o).rec # "NoRec")
\* A true replay: a delivered charge request found rec = Approved (no Charge effect).
ReachReplay ==
  ~(lastEvent.kind = "ChargeReqRecv" /\ provUp /\ lastFx = <<>>
    /\ pr(S, lastEvent.o).rec = "Approved")
\* A replay while no retry was ever used: the second request can only be a duplicate.
ReachDupReplay == ~(~ReachReplay /\ \A o \in OrdIds : retries[o] = 0)
ReachDuplicate == \A m \in MsgSet : dup[m] = 0
ReachCrash == \A v \in Svcs : crashes[v] = 0
\* Provider refund path: A10 fired, a Refund effect, a WireRefundReq effect, a WireDeclined effect.
ReachRefundCount == \A o \in OrdIds : pr(S, o).refundCount = 0
ReachRefundFx == \A o \in OrdIds : ~HasFx(lastFx, "Refund", o)
ReachWireRefundReq == \A o \in OrdIds : ~HasFx(lastFx, "WireRefundReq", o)
ReachWireDeclined == \A o \in OrdIds : ~HasFx(lastFx, "WireDeclined", o)
ReachProvDown == provUp
ReachOrderDown == orderUp
\* Persisted but not sent: an order with a pending charge row while the order service is down.
ReachPersistedNotSent == ~(~orderUp /\ \E o \in OrdIds : od(S, o).outCharge)

====

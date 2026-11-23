---- MODULE UC2 ----
\* UC2: stock reservation (inventory service). Mirrors properties/UC2.md sections 2 to 4 directly.
\* Bounds live in the .cfg files (UC2.cfg is the contract bound of UC2.md section 6 item 8).
EXTENDS Naturals, Integers, Sequences, FiniteSets

CONSTANTS Ids, EvSkus, Qtys, Ttls, Total, MaxClock, MaxCrashes, MaxCopies
ASSUME Ids \subseteq Nat /\ Qtys \subseteq Nat /\ Ttls \subseteq Nat
ASSUME 0 \in EvSkus /\ EvSkus \subseteq Nat
ASSUME Total \in Nat /\ MaxClock \in Nat /\ MaxCrashes \in Nat /\ MaxCopies \in Nat

VARIABLES stocks, res, up, clock, net, made, crashes, emitted, lastEvent, lastFx
vars == <<stocks, res, up, clock, net, made, crashes, emitted, lastEvent, lastFx>>

\* ---------------------------------------------------------------- state model
StockSkus == {0}                       \* exactly one stock, sku 0 (UC2.md section 6 item 7)
Statuses == {"Held", "Confirmed", "Expired"}
Reasons == {"BadRequest", "UnknownSku", "DuplicateId", "InsufficientStock",
            "UnknownReservation", "NotHeld", "TooLate", "NotYet"}

\* The contract state s = { up, clock, stocks, reservations }. `stocks` is a function sku -> Stock
\* with the single sku 0; `res` is the list of reservation records, in append order.
S == [up |-> up, clock |-> clock, stocks |-> stocks, reservations |-> res]

InitStock == [sku |-> 0, total |-> Total, available |-> Total, reserved |-> 0, sold |-> 0]

SetOf(rs) == {rs[i] : i \in 1..Len(rs)}
HasId(rs, id) == \E i \in 1..Len(rs) : rs[i].id = id
IdxOf(rs, id) == CHOOSE i \in 1..Len(rs) : rs[i].id = id     \* only used when HasId; ids are unique (A2)
Due(s, r) == r.expiresAt <= s.clock

RECURSIVE SumQty(_, _, _)
SumQty(rs, sku, st) ==
  IF rs = <<>> THEN 0
  ELSE (IF rs[1].sku = sku /\ rs[1].status = st THEN rs[1].qty ELSE 0) + SumQty(Tail(rs), sku, st)
HeldQty(s, k) == SumQty(s.reservations, k.sku, "Held")
ConfirmedQty(s, k) == SumQty(s.reservations, k.sku, "Confirmed")

\* ---------------------------------------------------------------------- Step
Out(state, fx) == [state |-> state, fx |-> fx]
Rej(id, c) == <<[t |-> "FxRejected", id |-> id, reason |-> c]>>

\* S2, S3: Reserve. Checks in the order BadRequest, UnknownSku, DuplicateId, InsufficientStock.
Reserve(s, e) ==
  IF e.qty = 0 \/ e.ttl = 0 THEN Out(s, Rej(e.id, "BadRequest"))
  ELSE IF ~(e.sku \in DOMAIN s.stocks) THEN Out(s, Rej(e.id, "UnknownSku"))
  ELSE IF HasId(s.reservations, e.id) THEN Out(s, Rej(e.id, "DuplicateId"))
  ELSE IF e.qty > s.stocks[e.sku].available THEN Out(s, Rej(e.id, "InsufficientStock"))
  ELSE Out([s EXCEPT !.stocks[e.sku].available = @ - e.qty,       \* guard: qty <= available
                     !.stocks[e.sku].reserved = @ + e.qty,
                     !.reservations = Append(@, [id |-> e.id, sku |-> e.sku, qty |-> e.qty,
                                                 status |-> "Held", expiresAt |-> s.clock + e.ttl,
                                                 confirmedAt |-> 0, returned |-> 0])],
           <<[t |-> "FxReserved", id |-> e.id, sku |-> e.sku, qty |-> e.qty,
              expiresAt |-> s.clock + e.ttl]>>)

\* S4, S5: Confirm. Needs Held and not Due (clock < expiresAt).
Confirm(s, e) ==
  IF ~HasId(s.reservations, e.id) THEN Out(s, Rej(e.id, "UnknownReservation"))
  ELSE
    LET i == IdxOf(s.reservations, e.id)
        r == s.reservations[i]
    IN
    IF r.status # "Held" THEN Out(s, Rej(e.id, "NotHeld"))
    ELSE IF Due(s, r) THEN Out(s, Rej(e.id, "TooLate"))
    ELSE Out([s EXCEPT !.stocks[r.sku].reserved = @ - r.qty,       \* guard: A1 (reserved = HeldQty >= qty)
                       !.stocks[r.sku].sold = @ + r.qty,
                       !.reservations[i].status = "Confirmed",
                       !.reservations[i].confirmedAt = s.clock],
             <<[t |-> "FxConfirmed", id |-> e.id]>>)

\* S6, S7: Expire. Needs Held and Due (expiresAt <= clock).
Expire(s, e) ==
  IF ~HasId(s.reservations, e.id) THEN Out(s, Rej(e.id, "UnknownReservation"))
  ELSE
    LET i == IdxOf(s.reservations, e.id)
        r == s.reservations[i]
    IN
    IF r.status # "Held" THEN Out(s, Rej(e.id, "NotHeld"))
    ELSE IF ~Due(s, r) THEN Out(s, Rej(e.id, "NotYet"))
    ELSE Out([s EXCEPT !.stocks[r.sku].available = @ + r.qty,
                       !.stocks[r.sku].reserved = @ - r.qty,       \* guard: A1 (reserved = HeldQty >= qty)
                       !.reservations[i].status = "Expired",
                       !.reservations[i].returned = @ + 1],
             <<[t |-> "FxReleased", id |-> e.id, qty |-> r.qty]>>)

\* Step(s, e) -> [state, fx]; total and deterministic. S0, S1, S8, S9 here; S2 to S7 above.
Step(s, e) ==
  LET k == e.kind IN
  IF k = "Tick" THEN Out([s EXCEPT !.clock = @ + 1], <<>>)                 \* S1 (up or down)
  ELSE IF k = "Crash" THEN Out([s EXCEPT !.up = FALSE], <<>>)              \* S8
  ELSE IF k = "Restart" THEN Out([s EXCEPT !.up = TRUE], <<>>)             \* S9
  ELSE IF ~s.up THEN Out(s, <<>>)                                          \* S0
  ELSE IF k = "Reserve" THEN Reserve(s, e)
  ELSE IF k = "Confirm" THEN Confirm(s, e)
  ELSE IF k = "Expire" THEN Expire(s, e)
  ELSE Out(s, <<>>)

\* -------------------------------------------------------------------- network
ReserveMsg == [kind : {"Reserve"}, id : Ids, sku : EvSkus, qty : Qtys, ttl : Ttls]
ConfirmMsg == [kind : {"Confirm"}, id : Ids]
ExpireMsg == [kind : {"Expire"}, id : Ids]
MsgSet == ReserveMsg \cup ConfirmMsg \cup ExpireMsg
\* `net[m]` = copies of message m in flight; `made[m]` = copies ever created (Send, Duplicate), at
\* most MaxCopies, so each message is delivered at most MaxCopies times.
ZeroNet == [m \in MsgSet |-> 0]
NetCount == LET RECURSIVE Sum(_, _)
                Sum(ms, n) == IF ms = {} THEN n
                              ELSE LET m == CHOOSE x \in ms : TRUE IN Sum(ms \ {m}, n + net[m])
            IN Sum(MsgSet, 0)

AddEmitted(fx) ==
  IF fx # <<>> /\ fx[1].t = "FxReleased"
  THEN [emitted EXCEPT ![[id |-> fx[1].id, qty |-> fx[1].qty]] = @ + 1]
  ELSE emitted

\* Run Step on e; install the network net0; record the step; log released effects in `emitted`.
DoStep(e, net0) ==
  LET r == Step(S, e) IN
  /\ up' = r.state.up
  /\ clock' = r.state.clock
  /\ stocks' = r.state.stocks
  /\ res' = r.state.reservations
  /\ net' = net0
  /\ emitted' = AddEmitted(r.fx)
  /\ lastEvent' = e
  /\ lastFx' = r.fx

\* ----------------------------------------------------------------------- Init
Init ==
  /\ stocks = [k \in StockSkus |-> InitStock]
  /\ res = <<>>
  /\ up = TRUE
  /\ clock = 0
  /\ net = ZeroNet
  /\ made = ZeroNet
  /\ crashes = 0
  /\ emitted = [x \in [id : Ids, qty : Qtys] |-> 0]
  /\ lastEvent = [kind |-> "Init"]
  /\ lastFx = <<>>

\* -------------------------------------------------------------------- actions
Send(m) ==
  /\ made[m] = 0
  /\ net' = [net EXCEPT ![m] = 1]
  /\ made' = [made EXCEPT ![m] = 1]
  /\ lastEvent' = [kind |-> "Send"]
  /\ lastFx' = <<>>
  /\ UNCHANGED <<stocks, res, up, clock, crashes, emitted>>

Drop(m) ==
  /\ net[m] > 0
  /\ net' = [net EXCEPT ![m] = @ - 1]
  /\ lastEvent' = [kind |-> "Drop"]
  /\ lastFx' = <<>>
  /\ UNCHANGED <<stocks, res, up, clock, made, crashes, emitted>>

Duplicate(m) ==
  /\ net[m] > 0
  /\ made[m] < MaxCopies
  /\ net' = [net EXCEPT ![m] = @ + 1]
  /\ made' = [made EXCEPT ![m] = @ + 1]
  /\ lastEvent' = [kind |-> "Duplicate"]
  /\ lastFx' = <<>>
  /\ UNCHANGED <<stocks, res, up, clock, crashes, emitted>>

\* Delivery: any message in flight (delay, reorder); remove one copy and run Step on it.
Deliver(m) ==
  /\ net[m] > 0
  /\ DoStep(m, [net EXCEPT ![m] = @ - 1])
  /\ UNCHANGED <<made, crashes>>

Tick ==
  /\ clock < MaxClock
  /\ DoStep([kind |-> "Tick"], net)
  /\ UNCHANGED <<made, crashes>>

\* Crash clears the in-flight set (lost events, pending Expire timers); `made` keeps its count.
Crash ==
  /\ up
  /\ crashes < MaxCrashes
  /\ DoStep([kind |-> "Crash", lost |-> NetCount], ZeroNet)
  /\ crashes' = crashes + 1
  /\ UNCHANGED made

Restart ==
  /\ ~up
  /\ DoStep([kind |-> "Restart"], net)
  /\ UNCHANGED <<made, crashes>>

Next ==
  \/ \E m \in MsgSet : Send(m) \/ Drop(m) \/ Duplicate(m) \/ Deliver(m)
  \/ Tick
  \/ Crash
  \/ Restart
  \/ UNCHANGED vars          \* stutter: bounded runs end in states with no other step; not a deadlock

Spec == Init /\ [][Next]_vars

\* ------------------------------------------------------------------- TypeOK
EventSet ==
  {[kind |-> "Init"]}
  \cup MsgSet
  \cup [kind : {"Send", "Drop", "Duplicate", "Tick", "Restart"}]
  \cup [kind : {"Crash"}, lost : 0..(Cardinality(MsgSet) * MaxCopies)]

MaxTtl == CHOOSE t \in Ttls : \A u \in Ttls : u <= t
ExpMax == MaxClock + MaxTtl           \* largest expiresAt a Reserve can set (TypeOK only)

EffSet ==
  [t : {"FxReserved"}, id : Ids, sku : EvSkus, qty : Qtys, expiresAt : 0..ExpMax]
  \cup [t : {"FxConfirmed"}, id : Ids]
  \cup [t : {"FxReleased"}, id : Ids, qty : Qtys]
  \cup [t : {"FxRejected"}, id : Ids, reason : Reasons]

ResSet == [id : Ids, sku : StockSkus, qty : Qtys, status : Statuses,
           expiresAt : Nat, confirmedAt : Nat, returned : Nat]

TypeOK ==
  \* Counters are Int (not Nat, not 0..total), so TypeOK does not restate P1 or P2.
  /\ stocks \in [StockSkus -> [sku : StockSkus, total : Int, available : Int, reserved : Int, sold : Int]]
  /\ res \in Seq(ResSet)
  /\ up \in BOOLEAN
  /\ clock \in 0..MaxClock
  /\ net \in [MsgSet -> 0..MaxCopies]
  /\ made \in [MsgSet -> 0..MaxCopies]
  /\ crashes \in 0..MaxCrashes
  /\ emitted \in [[id : Ids, qty : Qtys] -> Nat]
  /\ lastEvent \in EventSet
  /\ lastFx \in {<<>>} \cup {<<f>> : f \in EffSet}

\* ----------------------------------------------------------------- invariants
NonNegativeAvailable == \A sk \in DOMAIN stocks : stocks[sk].available >= 0              \* P1
Conservation ==                                                                          \* P2
  \A sk \in DOMAIN stocks :
    stocks[sk].available + stocks[sk].reserved + stocks[sk].sold = stocks[sk].total
ExpiredReturnedOnce ==                                                                   \* P3
  \A r \in SetOf(res) : r.returned = IF r.status = "Expired" THEN 1 ELSE 0
EmittedCount(id) ==
  \* total FxReleased effects emitted for id, over every qty
  LET RECURSIVE Add(_, _)
      Add(qs, n) == IF qs = {} THEN n
                    ELSE LET q == CHOOSE x \in qs : TRUE
                         IN Add(qs \ {q}, n + emitted[[id |-> id, qty |-> q]])
  IN Add(Qtys, 0)
ReleasedMatchesReturned ==                                                               \* P3b
  \A r \in SetOf(res) :
    /\ EmittedCount(r.id) = r.returned
    /\ \A q \in Qtys : q # r.qty => emitted[[id |-> r.id, qty |-> q]] = 0
ConfirmedBeforeDue ==                                                                    \* P4a
  \A r \in SetOf(res) : r.status = "Confirmed" => r.confirmedAt < r.expiresAt
CountersMatchRecords ==                                                                  \* A1
  \A sk \in DOMAIN stocks :
    /\ stocks[sk].reserved = HeldQty(S, stocks[sk])
    /\ stocks[sk].sold = ConfirmedQty(S, stocks[sk])
UniqueIdsKnownSku ==                                                                     \* A2
  /\ \A i, j \in 1..Len(res) : i # j => res[i].id # res[j].id
  /\ \A r \in SetOf(res) : r.sku \in DOMAIN stocks

\* --------------------------------------------------- transition properties
\* Pre-state S, post-state S', event lastEvent', effects lastFx'.
ExpiredNeverConfirmed ==                                                                 \* P4
  [][\A r \in SetOf(res) :
       r.status = "Expired" => \E r2 \in SetOf(res') : r2.id = r.id /\ r2.status = "Expired"]_vars

NoOversell ==                                                                            \* P1b
  [][\A sk \in DOMAIN stocks :
       stocks'[sk].available < stocks[sk].available =>
         LET e == lastEvent' IN
         /\ e.kind = "Reserve" /\ e.sku = sk
         /\ lastFx' = <<[t |-> "FxReserved", id |-> e.id, sku |-> sk, qty |-> e.qty,
                         expiresAt |-> clock + e.ttl]>>
         /\ stocks'[sk].available + e.qty = stocks[sk].available]_vars

ConfirmOnlyBeforeDue ==                                                                  \* P4b
  [][\A r \in SetOf(res), r2 \in SetOf(res') :
       (r2.id = r.id /\ r.status # "Confirmed" /\ r2.status = "Confirmed")
         => (r.status = "Held" /\ ~Due(S, r))]_vars

\* -------------------------------------------------------------- pinning laws
Same == S' = S /\ lastFx' = <<>>
RecOf(id) == res[IdxOf(res, id)]

ReserveAccepted(e) ==
  /\ e.qty >= 1 /\ e.ttl >= 1
  /\ e.sku \in DOMAIN stocks
  /\ ~HasId(res, e.id)
  /\ e.qty <= stocks[e.sku].available

PinReserveOk ==                                                                          \* S2
  [][(lastEvent'.kind = "Reserve" /\ up /\ ReserveAccepted(lastEvent')) =>
       LET e == lastEvent' k == stocks[e.sku] IN
       /\ S' = [S EXCEPT !.stocks[e.sku].available = k.available - e.qty,
                         !.stocks[e.sku].reserved = k.reserved + e.qty,
                         !.reservations = Append(res, [id |-> e.id, sku |-> e.sku, qty |-> e.qty,
                                                       status |-> "Held",
                                                       expiresAt |-> clock + e.ttl,
                                                       confirmedAt |-> 0, returned |-> 0])]
       /\ lastFx' = <<[t |-> "FxReserved", id |-> e.id, sku |-> e.sku, qty |-> e.qty,
                       expiresAt |-> clock + e.ttl]>>]_vars

PinReserveRejected ==                                                                    \* S3
  [][(lastEvent'.kind = "Reserve" /\ up /\ ~ReserveAccepted(lastEvent')) =>
       LET e == lastEvent' IN
       /\ S' = S
       /\ lastFx' = Rej(e.id,
            IF e.qty = 0 \/ e.ttl = 0 THEN "BadRequest"
            ELSE IF ~(e.sku \in DOMAIN stocks) THEN "UnknownSku"
            ELSE IF HasId(res, e.id) THEN "DuplicateId"
            ELSE "InsufficientStock")]_vars

PinConfirmOk ==                                                                          \* S4
  [][(lastEvent'.kind = "Confirm" /\ up /\ HasId(res, lastEvent'.id)
      /\ RecOf(lastEvent'.id).status = "Held" /\ ~Due(S, RecOf(lastEvent'.id))) =>
       LET e == lastEvent' i == IdxOf(res, e.id) r == res[i] k == stocks[r.sku] IN
       /\ S' = [S EXCEPT !.stocks[r.sku].reserved = k.reserved - r.qty,
                         !.stocks[r.sku].sold = k.sold + r.qty,
                         !.reservations[i].status = "Confirmed",
                         !.reservations[i].confirmedAt = clock]
       /\ lastFx' = <<[t |-> "FxConfirmed", id |-> e.id]>>]_vars

PinConfirmRejected ==                                                                    \* S5
  [][(lastEvent'.kind = "Confirm" /\ up
      /\ ~(HasId(res, lastEvent'.id) /\ RecOf(lastEvent'.id).status = "Held"
           /\ ~Due(S, RecOf(lastEvent'.id)))) =>
       LET e == lastEvent' IN
       /\ S' = S
       /\ lastFx' = Rej(e.id,
            IF ~HasId(res, e.id) THEN "UnknownReservation"
            ELSE IF RecOf(e.id).status # "Held" THEN "NotHeld"
            ELSE "TooLate")]_vars

PinExpireOk ==                                                                           \* S6
  [][(lastEvent'.kind = "Expire" /\ up /\ HasId(res, lastEvent'.id)
      /\ RecOf(lastEvent'.id).status = "Held" /\ Due(S, RecOf(lastEvent'.id))) =>
       LET e == lastEvent' i == IdxOf(res, e.id) r == res[i] k == stocks[r.sku] IN
       /\ S' = [S EXCEPT !.stocks[r.sku].available = k.available + r.qty,
                         !.stocks[r.sku].reserved = k.reserved - r.qty,
                         !.reservations[i].status = "Expired",
                         !.reservations[i].returned = r.returned + 1]
       /\ lastFx' = <<[t |-> "FxReleased", id |-> e.id, qty |-> r.qty]>>]_vars

PinExpireRejected ==                                                                     \* S7
  [][(lastEvent'.kind = "Expire" /\ up
      /\ ~(HasId(res, lastEvent'.id) /\ RecOf(lastEvent'.id).status = "Held"
           /\ Due(S, RecOf(lastEvent'.id)))) =>
       LET e == lastEvent' IN
       /\ S' = S
       /\ lastFx' = Rej(e.id,
            IF ~HasId(res, e.id) THEN "UnknownReservation"
            ELSE IF RecOf(e.id).status # "Held" THEN "NotHeld"
            ELSE "NotYet")]_vars

PinDown ==                                                                               \* S0
  [][(lastEvent'.kind \in {"Reserve", "Confirm", "Expire", "Crash"} /\ ~up) => Same]_vars

PinTick ==                                                                               \* S1
  [][lastEvent'.kind = "Tick" =>
       /\ S' = [S EXCEPT !.clock = clock + 1]
       /\ lastFx' = <<>>]_vars

PinCrash ==                                                                              \* S8
  [][lastEvent'.kind = "Crash" => (S' = [S EXCEPT !.up = FALSE] /\ lastFx' = <<>>)]_vars

PinRestart ==                                                                            \* S9
  [][lastEvent'.kind = "Restart" => (S' = [S EXCEPT !.up = TRUE] /\ lastFx' = <<>>)]_vars

FieldsStable ==                                                                          \* S10
  [][/\ \A sk \in DOMAIN stocks : stocks'[sk].total = stocks[sk].total
     /\ Len(res') >= Len(res)
     /\ \A i \in 1..Len(res) :
          /\ res'[i].id = res[i].id
          /\ res'[i].sku = res[i].sku
          /\ res'[i].qty = res[i].qty
          /\ res'[i].expiresAt = res[i].expiresAt
          /\ res[i].status \in {"Confirmed", "Expired"} => res'[i].status = res[i].status]_vars

\* S11 (DupFollowsFromPins) is derived from PinReserveOk .. PinExpireRejected and is not checked.

\* --------------------------------------------- reachability witnesses (non-vacuity)
\* Each is a deliberately false invariant; TLC must violate it (see UC2_reach_*.cfg).
LastRej(c) == lastFx # <<>> /\ lastFx[1].t = "FxRejected" /\ lastFx[1].reason = c
LastFxT(t) == lastFx # <<>> /\ lastFx[1].t = t
StatusOf(id) == IF HasId(res, id) THEN RecOf(id).status ELSE "None"
Copies(e) == IF e \in MsgSet THEN made[e] ELSE 0

ReachReserveOk == ~LastFxT("FxReserved")
ReachReserveExact == ~(LastFxT("FxReserved") /\ stocks[0].available = 0)     \* qty == available
ReachUnknownSku == ~LastRej("UnknownSku")
ReachDuplicateId == ~LastRej("DuplicateId")
ReachInsufficient == ~LastRej("InsufficientStock")
\* oversell attempt: the rejected Reserve asked for exactly available + 1
ReachOversellPlusOne ==
  ~(LastRej("InsufficientStock") /\ lastEvent.qty = stocks[0].available + 1)
ReachConfirmOk == ~LastFxT("FxConfirmed")
ReachConfirmUnknown == ~(lastEvent.kind = "Confirm" /\ LastRej("UnknownReservation"))
ReachConfirmNotHeld == ~(lastEvent.kind = "Confirm" /\ LastRej("NotHeld"))
ReachConfirmTooLate == ~LastRej("TooLate")
ReachExpireOk == ~LastFxT("FxReleased")
ReachExpireUnknown == ~(lastEvent.kind = "Expire" /\ LastRej("UnknownReservation"))
ReachExpireNotYet == ~LastRej("NotYet")
ReachExpireNotHeld == ~(lastEvent.kind = "Expire" /\ LastRej("NotHeld"))
\* Expire rejected NotHeld on a second copy of a message that had a duplicate made.
ReachExpireDupNotHeld ==
  ~(lastEvent.kind = "Expire" /\ LastRej("NotHeld") /\ Copies(lastEvent) = 2
    /\ StatusOf(lastEvent.id) = "Expired")
ReachConfirmDupNotHeld ==
  ~(lastEvent.kind = "Confirm" /\ LastRej("NotHeld") /\ Copies(lastEvent) = 2
    /\ StatusOf(lastEvent.id) = "Confirmed")
ReachReserveDupRejected ==
  ~(lastEvent.kind = "Reserve" /\ LastRej("DuplicateId") /\ Copies(lastEvent) = 2)
ReachExpiredRecord == \A r \in SetOf(res) : r.status # "Expired"
ReachConfirmedRecord == \A r \in SetOf(res) : r.status # "Confirmed"
ReachExpireNotHeldAfterConfirm ==
  ~(lastEvent.kind = "Expire" /\ LastRej("NotHeld") /\ StatusOf(lastEvent.id) = "Confirmed")
ReachTick == lastEvent.kind # "Tick"
ReachTickDown == ~(lastEvent.kind = "Tick" /\ ~up)
ReachCrash == crashes = 0
ReachRestart == lastEvent.kind # "Restart"
ReachDeliverDown == ~(lastEvent.kind \in {"Reserve", "Confirm", "Expire"} /\ ~up)
\* Crash that dropped at least one in-flight message.
ReachCrashLost == ~(lastEvent.kind = "Crash" /\ lastEvent.lost > 0)
\* A Reserve accepted and its effect lost by a crash: a Held record exists after a crash.
ReachHeldAfterCrash == ~(crashes = 1 /\ \E r \in SetOf(res) : r.status = "Held")
ReachDuplicated == \A m \in MsgSet : made[m] < 2
ReachDropped == lastEvent.kind # "Drop"
ReachReleasedEmitted == \A x \in DOMAIN emitted : emitted[x] = 0

====

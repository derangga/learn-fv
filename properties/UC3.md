# UC3: lease manager and worker, with fencing token

Status: draft for approval. After approval this file is frozen. Source: `docs/handover.md` section 5 (UC3). Lesson applied: laws that only bound
state let wrong step functions pass (`docs/results/phase0-bend-smoke.md` section 5), so section 4 pins each event's effect. Items not in the handover are marked "Proposed addition (not in handover)".

## 1. Scope

A lease manager grants a lease on one resource to one worker at a time (by its own bookkeeping), stamping each grant with a fencing token. Workers write to a
protected resource service, which sees each write's token. The wire between the parties drops, duplicates, delays and reorders messages. The manager and each worker can
crash and restart. A worker can pause (a long GC stop, say) after checking its lease and then act on it after it expired. Time is one injected logical clock; no skew.
Expected finding: with fencing (the resource rejects a token below the highest it accepted) a paused, stale worker cannot overwrite a newer holder's data; without fencing it can.
In scope: token issue, lease expiry, worker belief, resource acceptance. Out of scope: renew, voluntary release, resource crash, clock skew, authentication, liveness, W != 2.

## 2. State model (shared by TLA+, Go core, Bend port)

Values are natural numbers: Go `uint32`, Bend `Nat`, TLA+ integers (`Int`, used only as non-negative). No rule subtracts, so truncation or wrap never differs between tools. Worker ids: exactly 1 and 2 (`W = 2`);
0 means "none". An event whose worker id is not 1 or 2 changes nothing and emits nothing (no state change, empty effects). Names are the contract: Go `Mgr.Holder`, TLA+ `mgr.holder`, Bend `holder`.

| Component | Field | Meaning | Initial |
|---|---|---|---|
| `clock` | Nat | logical now | 0 |
| `mgr` | `holder` / `expiry` / `next` | worker the manager believes holds the lease / tick it ends / token of the next grant (persisted across restart) | 0 / 0 / 1 |
| `w1`, `w2` | `tok` / `exp` / `paused` | token of the lease the worker believes it holds, 0 none / expiry tick received with it / 1 frozen after its lease check | 0 / 0 / 0 |
| `res` | `highest` / `last` / `accepted` | highest token among accepted writes / token of the latest accepted write / count of accepted writes | 0 / 0 / 0 |
| `audit` | `last_grant` | token of the latest grant ever issued; set only by the grant rule; no restart resets it | 0 |
| ghost counters (Proposed addition) | `audit.bad_grants`, `res.bad_accepts` | grants whose token was not above `last_grant`; accepted writes whose token was below `res.highest` before the update. Same rule in both steps: on every accepted write, `bad_accepts' = bad_accepts` plus 1 if `tok < res.highest` else 0 (section 4) | 0, 0 |

Derived: `live = (mgr.holder != 0) and (clock < mgr.expiry)`. A lease expires by the clock passing `expiry`; there is no expire event. Constant `TTL >= 1` (lease length in ticks).

Events (inputs to `Step(state, event) -> (state, effects)`; each is a delivery to one party or an environment action):

| Event | Fields | Delivered to |
|---|---|---|
| `Tick` | none | clock |
| `Acquire` | `w` | manager (a request) |
| `DeliverGrant` | `w`, `tok`, `exp` | worker w |
| `WorkerWrite` / `Pause` / `Resume` / `RestartWorker` | `w` | worker w (`WorkerWrite` = it decides to write, re-checking its lease) |
| `DeliverWrite` | `tok` | resource |
| `RestartManager` | none | manager (crash plus restart) |

Effects: `SendGrant(w, tok, exp)`, `SendWrite(tok)`, `Accept(tok)`, `Reject(tok)`. They go to the transport and `Step` never reads them. Faults are not events: drop = never delivered;
delay and reorder = any sent message is deliverable at any time; duplicate = a delivered message may be delivered again.

Encodings (one per tool; the same names and shapes everywhere):

- Go (`internal/uc3/core`): `type State struct{Clock uint32; Mgr Mgr; W1, W2 Worker; Res Res; Audit Audit}`, `type Event struct{Kind EventKind; W, Tok, Exp uint32}`, `type Effect struct{Kind EffectKind; W, Tok, Exp uint32}`.
  `StepFenced(State, Event) (State, []Effect)`, `StepUnfenced(...)` same shape, `Init() State`, `RunFenced([]Event, State) State`, `RunUnfenced(...)` (fold head first, effects dropped).
- Bend (`bend/uc3/code.bend`): datatypes `Mgr`, `Worker`, `Res`, `Audit`, `St` (fields as above, `w1`, `w2`), `Ev` (one constructor per event), `Fx`; `init` : `St`; `step_fenced(s, e)` and `step_unfenced(s, e)` return
  a pair `(St, List<Fx>)`, projected by `st(r)` and `fx(r)`; `run_fenced(evs, s)`, `run_unfenced(evs, s)` : `St` (list first, fold head first, per the smoke test).
  Predicates (`Bool`): `p1a(s)` = `Nat.is_lt(s.audit.last_grant, s.mgr.next)`; `p3(s)` = `Nat.is_eq(s.res.last, s.res.highest)`; `inv(s)` = `Bool.and(p1a(s), p3(s))`. Step code uses `Nat.max`, `Nat.add`, `Nat.is_lt`, `Nat.is_le`. Laws take hypotheses as `h : {p == True{} : Bool}` and conclude with `Nat.is_le(..) == True{}`, `Nat.is_lt(..) == True{}` or Nat equalities.
- TLA+ (`spec/tla/UC3.tla`, fenced; `spec/tla/UC3_buggy_unfenced.tla`, differs only in action `DeliverWrite`): `CONSTANTS W, TTL, MAXCLOCK, MAXTOK, MAXPAUSE, MAXRESTM, MAXRESTW, MAXACC`;
  `VARIABLES clock, mgr, wrk, res, audit, net, lastEvent, lastFx, npause, nrestm, nrestw`; `vars == <<clock, mgr, wrk, res, audit, net, lastEvent, lastFx, npause, nrestm, nrestw>>`.
  `wrk` is a function `1..W -> [tok, exp, paused]`; `net` is the set of sent messages (effects are added to it, so deliveries are enabled only for messages in `net`; `Acquire` is always enabled);
  `lastEvent` is the event of the last step (`[kind |-> "Init"]` initially) and `lastFx` the sequence of its effects (`<<>>` initially; `net' = net` plus the elements of `lastFx'`), the history variables the pins read, as in UC1; `npause, nrestm, nrestw` count pauses and restarts for the bounds. `TypeOK` types every variable
  (fields are naturals, `paused` in `{0,1}`, `holder` in `0..W`, `net` a subset of all messages, `lastEvent` an event record, `lastFx` a sequence of effect records). A no-op branch (e.g. `AcquireLive`) is a real action that sets `lastEvent` and `lastFx`.
  Go and Bend accept any event list, including deliveries never sent (forged); TLC explores only realizable ones. State this in every result report.

## 3. Properties

Notation: `s` pre-state, `s'` post-state of one step. Every per-event law (`*_step`) assumes exactly the hypothesis in its row, and a row that says "no hypothesis" assumes nothing. No law that applies to `step_unfenced` assumes `p3` (it fails mid-run there); `inv` is used only for the fenced step.
Every `*_run` law: for all `evs`, `s`, hypothesis as stated, conclusion about `run(evs, s)`'s final state, by induction on `evs` from the `*_step` law. Transition properties are TLA+ action properties
`[][...]_vars` checked as `PROPERTY`; state invariants are checked as `INVARIANT`. Go: one test per row on seeded random event lists from `internal/sim`, checked after every step. The sim generates only deliveries of messages that were sent (realizable only, like TLC); Go unit tests that call `Step` directly (the pin tests, the witness tests) may use forged events and arbitrary states.

| Id | Plain English | Precise statement | Kind | Applies to | TLA+ | Bend laws | Go test |
|---|---|---|---|---|---|---|---|
| P1 | Every grant gets a strictly larger fencing token than the previous grant. | a step that grants token `tok` has `tok > s.audit.last_grant`, i.e. `audit.bad_grants' = audit.bad_grants`; hyp `p1a(s)` | transition | fenced, unfenced | `P1_GrantStrictlyIncreases` | `p1_step`; `p1_run`: hyp `p1a(s)`, `bad_grants` of the final state equals `bad_grants(s)` | `TestUC3_P1_GrantTokenStrictlyIncreases` |
| P2 | The resource never accepts a write with a token lower than one it has already seen. | a step never accepts `DeliverWrite(tok)` with `tok < res.highest`, i.e. `res.bad_accepts' = res.bad_accepts`; no hypothesis. The counter is computed identically in both steps, so for `step_fenced` the law holds only because the guard `tok >= highest` precedes every accept. "Seen" = `highest`: it is the maximum over accepted writes, and equals the maximum over all received writes because a rejected write has `tok < highest` and cannot raise it. | transition | fenced only | `P2_NoLowerTokenAccepted` | `p2_step`; `p2_run`: `bad_accepts` of the final state equals `bad_accepts(s)` | `TestUC3_P2_NoLowerTokenAccepted` |
| P3 | No stale write lands: after a higher-token write was accepted no lower-token write is. The checkable form of the expected finding. Proposed addition (not in handover). | `res.last = res.highest` | safety invariant | fenced only | `P3_StaleWriteExcluded` | `p3_step` (hyp `p3(s)`); `p3_run` (hyp `p3(s)`, concl `p3`) | `TestUC3_P3_StaleWriteExcluded` |
| P1a | Next token is above every issued token; makes P1 inductive and catches a reset of `next`. Proposed addition (not in handover). | `audit.last_grant < mgr.next` | safety invariant | fenced, unfenced | `P1a_NextAboveLastGrant` | `p1a_step` (hyp `p1a(s)`); `p1a_run` (hyp `p1a(s)`, concl `p1a`) | `TestUC3_P1a_NextAboveLastGrant` |
| Init | Proposed addition (not in handover). The initial state satisfies the invariants and zero counters. | `p1a(init)`, `p3(init)`, `bad_grants = 0`, `bad_accepts = 0` | init | both | `Init` (checked by `INVARIANT`) | `init_inv` | `TestUC3_InitInv` |

From `init`, P1 and P2 (with `bad_*` starting at 0) give: after any event list, `bad_grants = 0` and (fenced) `bad_accepts = 0`. Only the handover's P1 and P2 are listed as properties of the system; the counters are Proposed additions (not in handover), made so the `*_run` laws speak about the final state only. The counter rules are pinned in section 4, so a mutant cannot hide a bad grant by not counting it.

Expected finding (the frozen check). Witness event list `T` (W=2, TTL=2, from `init`): `Acquire(1)`, `DeliverGrant(1,1,2)`, `Pause(1)`, `Tick`, `Tick`, `Acquire(2)`, `DeliverGrant(2,2,4)`, `WorkerWrite(2)`,
`DeliverWrite(2)`, `Resume(1)`, `DeliverWrite(1)`. Worker 1 pauses holding token 1, its lease ends at tick 2, worker 2 gets token 2 and writes, worker 1 resumes and writes token 1.
(The same stale write arises without a pause if worker 1's write message is merely delayed past worker 2's.) Final states, full records, `n.f` for field `f` of `n`:
`S_f` (after `run_fenced(T, init)`): `clock 2; mgr (2, 4, 3); w1 (1, 2, 0); w2 (2, 4, 0); res (highest 2, last 2, accepted 1, bad_accepts 0); audit (last_grant 2, bad_grants 0)`.
`S_u` (after `run_unfenced(T, init)`): same, except `res (highest 2, last 1, accepted 2, bad_accepts 1)`, so `p3` is false.
Proposed addition (not in handover): these positive laws must CHECK in every tool, with no hypothesis:

| Name | Statement | TLA+ | Bend | Go |
|---|---|---|---|---|
| fenced witness | `run_fenced(T, init) == S_f` (P3 true) | invariant `NotAfterT_fenced` = not (shared fields equal `S_f` and `lastEvent = DeliverWrite(tok 1)` and `lastFx = <<Reject(1)>>`); TLC on `spec/tla/UC3.tla` with `spec/tla/UC3_witness.cfg` must VIOLATE it | `witness_fenced`, `{==}` by computation | `TestUC3_WitnessFenced` |
| unfenced witness | `run_unfenced(T, init) == S_u` (P3 false) | `NotAfterT_unfenced` = not (shared fields equal `S_u` and `lastEvent = DeliverWrite(tok 1)` and `lastFx = <<Accept(1)>>`); `spec/tla/UC3_buggy_unfenced_witness.cfg` must VIOLATE it | `witness_unfenced` | `TestUC3_WitnessUnfenced` |

The TLA+ witness check shows `S_f` (resp. `S_u`) is reached by a step that delivers the stale write (token 1) and gets it rejected (resp. accepted), in the section 6 bounds; the fields `net`, `lastEvent`, `lastFx` other than that last step, and the pause/restart counters are not compared elsewhere. For a mutant, run `UC3_witness.cfg` on the mutant spec: `NotAfterT_fenced` NOT violated means the mutant is killed (it cannot reproduce the fenced witness). The fenced and unfenced step functions are the same except the resource rule.
Expected recorded results (not frozen laws): for `step_unfenced`, `p2_step` and `p3_step` cannot be proved (record the checker's error); TLC reports a counterexample to `P2_NoLowerTokenAccepted` and to `P3_StaleWriteExcluded`; P1 and P1a hold for both variants. `spec/tla/UC3.cfg` checks `INVARIANT TypeOK, P1a_NextAboveLastGrant, P3_StaleWriteExcluded` and `PROPERTY P1_GrantStrictlyIncreases, P2_NoLowerTokenAccepted` plus every pin of section 4 except `S_OutOfRange` and `S_ResUnfenced`. `spec/tla/UC3_buggy_unfenced.cfg` is the same list with `S_ResUnfenced` in place of `S_ResFenced` (`S_ResFenced` is expected to fail there, so it is left out); TLC stops at the first violation, so the two expected violations are recorded from two runs: `UC3_buggy_unfenced_P2.cfg` (`PROPERTY P2_NoLowerTokenAccepted` only) and `UC3_buggy_unfenced_P3.cfg` (`INVARIANT P3_StaleWriteExcluded` only). For `step_fenced` all laws and properties of this section hold, for every event list including forged ones.

## 4. Step-effect (pinning) laws

Proposed addition (not in handover). Each pins what one event does, so a wrong step that still satisfies P1 to P3 is caught. Fields and effects not named are unchanged or empty.
Each is a transition property: TLA+ `[][ lastEvent'.kind = "X" => post ]_vars` (`lastEvent'` is the event just taken, `post` includes `lastFx'`); Bend: the law in the Bend column, for all `s`, `e` of that shape, no hypothesis; Go: the test in the Go column. A paused worker ignores
`DeliverGrant`, `WorkerWrite` and `Pause`; only `Resume` and `RestartWorker` change it. Workers `i` run the rule on `wi`.

| Pin | Event and guard | Effect on `s'` and effects | TLA+ | Bend | Go (`TestUC3_`) |
|---|---|---|---|---|---|
| Tick | `Tick` | `clock' = clock + 1`; no effects | `S_Tick` | `s_tick_step` | `S_Tick` |
| AcquireLive | `Acquire(w)`, `live` | `s' = s`; no effects (a repeat from the holder too) | `S_AcquireLive` | `s_acquire_live_step` | `S_AcquireLive` |
| AcquireGrant | `Acquire(w)`, not `live` | `mgr.holder' = w`, `mgr.expiry' = clock + TTL`, `mgr.next' = mgr.next + 1`, `audit.last_grant' = mgr.next`, `audit.bad_grants' = audit.bad_grants` plus 1 if `mgr.next <= audit.last_grant` else 0; effects `[SendGrant(w, mgr.next, clock + TTL)]` | `S_AcquireGrant` | `s_acquire_grant_step` | `S_AcquireGrant` |
| GrantRecv | `DeliverGrant(i,tok,exp)`, `paused = 0`, `tok > wi.tok`, `clock < exp` | `wi.tok' = tok`, `wi.exp' = exp`; no effects | `S_GrantRecv` | `s_grant_recv_step` | `S_GrantRecv` |
| GrantIgnore | `DeliverGrant(i,..)` otherwise | `s' = s` (stale, duplicate, expired or paused target) | `S_GrantIgnore` | `s_grant_ignore_step` | `S_GrantIgnore` |
| WriteOk | `WorkerWrite(i)`, `paused = 0`, `tok != 0`, `clock < exp` | `s' = s`; `[SendWrite(wi.tok)]` | `S_WriteOk` | `s_write_ok_step` | `S_WriteOk` |
| WriteExpired | `WorkerWrite(i)`, `paused = 0`, `tok != 0`, `clock >= exp` | `wi.tok' = 0`, `wi.exp' = 0`; no effects | `S_WriteExpired` | `s_write_expired_step` | `S_WriteExpired` |
| WriteNone | `WorkerWrite(i)` otherwise | `s' = s` | `S_WriteNone` | `s_write_none_step` | `S_WriteNone` |
| Pause | `Pause(i)`, `paused = 0`, `tok != 0` | `wi.paused' = 1`; otherwise `s' = s` | `S_Pause` | `s_pause_step` | `S_Pause` |
| Resume | `Resume(i)`, `paused = 1` | `wi.paused' = 0`; `[SendWrite(wi.tok)]` with no clock check (the stale act); otherwise `s' = s` | `S_Resume` | `s_resume_step` | `S_Resume` |
| ResFenced (`step_fenced`) | `DeliverWrite(tok)` | if `tok >= res.highest`: `highest' = tok`, `last' = tok`, `accepted' = accepted + 1`, `bad_accepts' = bad_accepts` plus 1 if `tok < res.highest` else 0 (the guard makes it 0), `[Accept(tok)]`; else `s' = s`, `[Reject(tok)]` | `S_ResFenced` | `s_res_fenced_step` | `S_ResFenced` |
| ResUnfenced (`step_unfenced`) | `DeliverWrite(tok)` | always: `highest' = max(highest, tok)`, `last' = tok`, `accepted' = accepted + 1`, `bad_accepts' = bad_accepts` plus 1 if `tok < res.highest` else 0, `[Accept(tok)]` | `S_ResUnfenced` | `s_res_unfenced_step` | `S_ResUnfenced` |
| MgrRestart | `RestartManager` | `mgr.holder' = 0`, `mgr.expiry' = 0`; `mgr.next`, `audit`, `clock` unchanged; no effects | `S_MgrRestart` | `s_mgr_restart_step` | `S_MgrRestart` |
| WorkerRestart | `RestartWorker(i)` | `wi` back to `(0, 0, 0)`; no effects | `S_WorkerRestart` | `s_worker_restart_step` | `S_WorkerRestart` |
| OutOfRange | any event with worker id not in `{1, 2}` | `s' = s`; no effects | none (TLA+ never generates one) | `s_out_of_range_step` | `S_OutOfRange` |

`ResFenced` is stated in both directions (accept iff `tok >= highest`), so it also pins the case P2 and P3 cannot see. The pin for each event holds on the step functions it names; the others hold on both.

## 5. Mutants

Same bug in all three tools, one path triple per mutant (`unfenced`, `nonstrict_token`, `res_accepts_le`, `res_off_by_one`, `reset_on_restart`, `grant_while_live`):
`spec/tla/UC3_buggy_unfenced.tla`, `mutants/uc3/unfenced/`, `bend/uc3/mutants/unfenced/`; likewise `UC3_buggy_nonstrict_token.tla`, `UC3_buggy_res_accepts_le.tla`, `UC3_buggy_res_off_by_one.tla`,
`UC3_buggy_reset_on_restart.tla`, `UC3_buggy_grant_while_live.tla` under `spec/tla/`, and the same five names as directories under `mutants/uc3/` and `bend/uc3/mutants/`.
Each runs against the fenced core (M1 replaces the fenced rule by the unfenced one). A mutant must be rejected by every tool. Surviving every property and pin is a finding about the contract.

| Id | Bug | Killed by |
|---|---|---|
| `unfenced` (M1) | resource accepts every write (rule `ResUnfenced`): the handover's "lease without fencing" | P2, P3, `ResFenced`, `fenced witness` (unfenced result `S_u` differs from `S_f`) |
| `nonstrict_token` (M2) | `AcquireGrant` leaves `mgr.next` unchanged (token not strictly larger: `>=` where `>` is needed) | P1a (after the first grant), P1 (the second grant), `AcquireGrant` |
| `res_accepts_le` (M3) | resource accepts iff `tok <= res.highest`; on accept `highest' = max(highest, tok)`, `last' = tok`, `accepted + 1`, counter by the common rule | Bend: P2 (`p2_step` quantifies over all states, e.g. `highest = 5`, `DeliverWrite(3)` is accepted and counted bad). TLC and the Go sim (realizable events only) reach only `highest = 0` (only token 0 passes, never sent), so P1 to P3 all hold there; there it is killed only by the Proposed pin `ResFenced` (a Go pin unit test may use a forged state) and `fenced witness`. |
| `res_off_by_one` (M4) Proposed addition (not in handover) | resource accepts iff `tok + 1 >= res.highest`; on accept `highest' = max(highest, tok)`, `last' = tok`, counter by the common rule, as in section 4 (no subtraction anywhere) | P2 and P3 (a write one below `highest` is accepted), `ResFenced`, `fenced witness` |
| `reset_on_restart` (M5) | `RestartManager` sets `mgr.next' = 1` | P1a (at the restart), P1 (TLC and Go: the next grant), `MgrRestart` |
| `grant_while_live` (M6) Proposed addition (not in handover) | `AcquireGrant` also fires when `live` | `AcquireLive` only. Fencing masks it: P1 to P3 still hold. |

Expected H3 observation to record: for M3, Bend rejects the mutant through P2 over unreachable states, while TLC (bounded, reachable states) and Go need the proposed pin. M3 survives the handover's P1 and P2 in TLC and Go.

## 6. Assumptions and open questions (proposed defaults; the user decides)

Defaults apply unless the user says otherwise before approval.

1. Does the manager persist `next` across restart? Default: yes (`next` persisted; `holder`, `expiry` volatile). If not persisted, `next` resets on restart and P1 and P1a fail by design (that is mutant M5 made the spec); the property set would then need a persisted epoch, and P1 could hold only for runs without a manager restart.
2. Two grants in one tick? Default: only after `RestartManager` (the holder is forgotten). Without a restart `TTL >= 1` forbids it. After a restart two workers can both believe they hold a lease; P1 to P3 still hold.
3. Renew and voluntary release: out of scope. Adding either changes the events and needs its own pins.
4. Resource crash: not modelled; `res` is durable. A resource restart that forgot `highest` would break P2 by design.
5. Duplicate `Acquire` from the live holder: rejected (`AcquireLive`), no re-send. A lost grant is recovered only after expiry.
6. A worker accepts only a strictly newer, unexpired grant (`GrantRecv`).
7. One global logical clock shared by all parties; skew is out of scope. The pause is the only way a worker acts on an expired lease. `Resume` writes without a clock check (it passed its check, then froze); `WorkerWrite` is the checked path.
8. TLC bounds (in `spec/tla/UC3.cfg` and the other cfgs, restated in every report, never changed silently): `W = 2`, `TTL = 2`, `MAXCLOCK = 5`, `MAXTOK = 4`, `MAXPAUSE = 1`, `MAXRESTM = 1`, `MAXRESTW = 1`, `MAXACC = 4`.
   `CONSTRAINT clock <= MAXCLOCK /\ mgr.next <= MAXTOK + 1 /\ res.accepted <= MAXACC`; `Pause`, `RestartManager`, `RestartWorker` are guarded by their counters. `MAXACC` is needed because a delivered message can repeat forever;
   behaviours with more than 4 accepted writes go unchecked. TLC also sees the extra variables `lastEvent` and `lastFx` (more distinct states). Bend and Go have no bounds.
9. Values stay far below 2^32 in tests and the harness; overflow is out of scope.

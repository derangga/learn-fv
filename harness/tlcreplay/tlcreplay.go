// Package tlcreplay replays TLC traces (tlc -dumpTrace json) of the UC1 TLA+
// model against the Go payment services (services/payment.Cluster).
//
// Each TLA+ step is mapped to one Cluster call. The action is identified from
// lastEvent; Deliver, Drop and Duplicate carry no message in lastEvent (Drop and
// Duplicate) or only its kind (Deliver), so the message comes from the net bag
// (diff between consecutive states). After every step the Cluster snapshot and
// its in-flight messages are compared with the TLA+ state. See
// docs/results/uc1-replay.md for the mapping table and the modelling gaps.
package tlcreplay

//go:generate bash gen.sh

import (
	"encoding/json"
	"errors"
	"fmt"
	"os"
	"reflect"
	"regexp"
	"sort"
	"strconv"
	"strings"

	"github.com/derangga/learn-formal-verification/internal/sim"
	"github.com/derangga/learn-formal-verification/internal/uc1/core"
	"github.com/derangga/learn-formal-verification/services/payment"
)

// TLA+ state as dumped by TLC (only the variables the replay uses).
type tlaState struct {
	Slots map[string]struct {
		Ord struct {
			Status    string `json:"status"`
			Amount    uint32 `json:"amount"`
			OutCharge bool   `json:"outCharge"`
			OutRefund bool   `json:"outRefund"`
		} `json:"ord"`
		Prov struct {
			Rec         string `json:"rec"`
			ChargeCount uint32 `json:"chargeCount"`
			RefundCount uint32 `json:"refundCount"`
			Amt         uint32 `json:"amt"`
			OutReply    bool   `json:"outReply"`
		} `json:"prov"`
	} `json:"slots"`
	OrderUp   bool           `json:"orderUp"`
	ProvUp    bool           `json:"provUp"`
	Net       map[string]int `json:"net"`
	LastEvent struct {
		Kind string `json:"kind"`
		O    uint32 `json:"o"`
		A    uint32 `json:"a"`
		D    string `json:"d"`
		Svc  string `json:"svc"`
	} `json:"lastEvent"`
}

// Trace is one TLC counterexample or witness.
type Trace struct {
	Name      string // file stem, e.g. reach_paid, buggy_m1
	Violation string // TLC's "Error: ... is violated." line
	States    []tlaState
}

// Load reads testdata/<name>.json and <name>.violation from dir.
func Load(dir, name string) (*Trace, error) {
	b, err := os.ReadFile(dir + "/" + name + ".json")
	if err != nil {
		return nil, err
	}
	t := &Trace{Name: name}
	if err := json.Unmarshal(b, &t.States); err != nil {
		return nil, fmt.Errorf("%s: %w", name, err)
	}
	if len(t.States) == 0 || t.States[0].LastEvent.Kind != "Init" {
		return nil, fmt.Errorf("%s: trace does not start at Init", name)
	}
	if v, err := os.ReadFile(dir + "/" + name + ".violation"); err == nil {
		t.Violation = strings.TrimSpace(string(v))
	}
	return t, nil
}

// N is the number of orders of the trace.
func (t *Trace) N() uint32 { return uint32(len(t.States[0].Slots)) }

// ViolatedProperty is the name TLC reported, e.g. "NoDoubleCharge".
func (t *Trace) ViolatedProperty() string {
	f := strings.Fields(strings.TrimSuffix(t.Violation, " is violated."))
	if len(f) == 0 {
		return ""
	}
	return f[len(f)-1]
}

func lookup[T comparable](s string, all []T, name func(T) string) T {
	for _, v := range all {
		if name(v) == s {
			return v
		}
	}
	panic("tlcreplay: unknown name " + s)
}

// toCore converts a TLA+ state to the core state (slots, orderUp, provUp).
func toCore(s tlaState, n uint32) core.State {
	c := core.Init(n)
	c.OrderUp, c.ProvUp = s.OrderUp, s.ProvUp
	sts := []core.Status{core.None, core.AwaitingPayment, core.Paid, core.Failed, core.Refunded}
	rs := []core.Res{core.NoRec, core.Approved, core.Declined}
	for k, sl := range s.Slots {
		o, _ := strconv.Atoi(k)
		c.Slots[o] = core.Slot{
			Ord: core.OrdRec{
				Status:    lookup(sl.Ord.Status, sts, core.Status.String),
				Amount:    sl.Ord.Amount,
				OutCharge: sl.Ord.OutCharge,
				OutRefund: sl.Ord.OutRefund,
			},
			Prov: core.ProvRec{
				Rec:         lookup(sl.Prov.Rec, rs, core.Res.String),
				ChargeCount: sl.Prov.ChargeCount,
				RefundCount: sl.Prov.RefundCount,
				Amt:         sl.Prov.Amt,
				OutReply:    sl.Prov.OutReply,
			},
		}
	}
	return c
}

// TLA+ message type -> wire effect kind.
var wireKind = map[string]core.EffectKind{
	"ChargeReq": core.WireChargeReq, "RefundReq": core.WireRefundReq,
	"Approved": core.WireApproved, "Declined": core.WireDeclined,
}

var (
	reO = regexp.MustCompile(`o \|-> (\d+)`)
	reT = regexp.MustCompile(`t \|-> "(\w+)"`)
	reA = regexp.MustCompile(`a \|-> (\d+)`)
)

// parseMsg reads a TLC net key such as `[o |-> 0, t |-> "ChargeReq", a |-> 5]`.
func parseMsg(key string) (core.Effect, error) {
	o, t, a := reO.FindStringSubmatch(key), reT.FindStringSubmatch(key), reA.FindStringSubmatch(key)
	if o == nil || t == nil || a == nil {
		return core.Effect{}, fmt.Errorf("bad net key %q", key)
	}
	k, ok := wireKind[t[1]]
	if !ok {
		return core.Effect{}, fmt.Errorf("bad message type in %q", key)
	}
	ov, _ := strconv.Atoi(o[1])
	av, _ := strconv.Atoi(a[1])
	return core.Effect{Kind: k, O: uint32(ov), A: uint32(av)}, nil
}

// bag turns the TLA+ net function into a multiset of messages.
func bag(net map[string]int) (map[core.Effect]int, error) {
	m := map[core.Effect]int{}
	for k, n := range net {
		if n == 0 {
			continue
		}
		e, err := parseMsg(k)
		if err != nil {
			return nil, err
		}
		m[e] += n
	}
	return m, nil
}

func flightBag(msgs []sim.Msg[core.Effect]) map[core.Effect]int {
	m := map[core.Effect]int{}
	for _, x := range msgs {
		m[x.Body]++
	}
	return m
}

func fmtBag(m map[core.Effect]int) string {
	var s []string
	for e, n := range m {
		s = append(s, fmt.Sprintf("%dx%v(o=%d,a=%d)", n, e.Kind, e.O, e.A))
	}
	sort.Strings(s)
	return "{" + strings.Join(s, " ") + "}"
}

// diffState describes what differs between the service snapshot and the TLA+
// state; "" means equal.
func diffState(got, want core.State) string {
	var d []string
	if got.OrderUp != want.OrderUp {
		d = append(d, fmt.Sprintf("orderUp svc=%v tla=%v", got.OrderUp, want.OrderUp))
	}
	if got.ProvUp != want.ProvUp {
		d = append(d, fmt.Sprintf("provUp svc=%v tla=%v", got.ProvUp, want.ProvUp))
	}
	for o := range want.Slots {
		if !reflect.DeepEqual(got.Slots[o], want.Slots[o]) {
			d = append(d, fmt.Sprintf("slot %d svc=%+v tla=%+v", o, got.Slots[o], want.Slots[o]))
		}
	}
	return strings.Join(d, "; ")
}

func describe(e struct {
	Kind string `json:"kind"`
	O    uint32 `json:"o"`
	A    uint32 `json:"a"`
	D    string `json:"d"`
	Svc  string `json:"svc"`
}) string {
	switch e.Kind {
	case "Init", "Drop", "Duplicate":
		return e.Kind
	case "Crash", "Restart":
		return e.Kind + "(" + e.Svc + ")"
	case "PlaceOrder":
		return fmt.Sprintf("PlaceOrder(o=%d,a=%d)", e.O, e.A)
	case "ChargeReqRecv":
		return fmt.Sprintf("ChargeReqRecv(o=%d,a=%d,d=%s)", e.O, e.A, e.D)
	}
	return fmt.Sprintf("%s(o=%d)", e.Kind, e.O)
}

// StepResult is the outcome of replaying one TLA+ step.
type StepResult struct {
	I       int    // index of the TLA+ state reached (1-based; 0 is Init)
	Event   string // TLA+ action
	Skipped string // why the step could not be mapped or applied ("" if applied)
	Diff    string // difference from the TLA+ state ("" if equal)
}

// Result is the whole replay. Snaps[i] is the service state after step i
// (Snaps[0] is the initial snapshot); Flight[i] its in-flight bag.
type Result struct {
	Steps    []StepResult
	FirstDiv int // index into Steps of the first divergence, -1 if none
	Snaps    []core.State
	Ledger   []core.Effect
}

// Replay runs the trace against a fresh Cluster. After a divergence it keeps
// applying the remaining steps (state-independent actions; deliveries only
// when a copy with the TLA+ message value is in flight) so the caller can check
// properties on the service's own trajectory.
func Replay(t *Trace, dir string) (*Result, error) {
	n := t.N()
	// ScriptIssuer: the provider asks the issuer on every charge request it
	// receives while up, so the script is one decision per such TLA+ step.
	var script []core.Decision
	for i := 1; i < len(t.States); i++ {
		e := t.States[i].LastEvent
		if e.Kind == "ChargeReqRecv" && t.States[i-1].ProvUp {
			if e.D == "Decline" {
				script = append(script, core.Decline)
			} else {
				script = append(script, core.Approve)
			}
		}
	}
	c, err := payment.NewCluster(payment.Config{
		N: n, Dir: dir, Seed: 1,
		// The TLA+ bound is per message value, the sim's is per original: lift the
		// sim bound; TLC already enforced DupMax on the trace.
		Faults: sim.Faults{MaxDup: 1 << 20},
		Crash:  sim.CrashConfig{MaxCrashes: 1 << 20},
		Issuer: &payment.ScriptIssuer{Script: script},
	})
	if err != nil {
		return nil, err
	}
	defer c.Close()

	res := &Result{FirstDiv: -1}
	snap, err := c.Snapshot()
	if err != nil {
		return nil, err
	}
	res.Snaps = append(res.Snaps, snap)
	if d := diffState(snap, toCore(t.States[0], n)); d != "" {
		return nil, fmt.Errorf("%s: initial state differs: %s", t.Name, d)
	}

	for i := 1; i < len(t.States); i++ {
		prev, cur := t.States[i-1], t.States[i]
		sr := StepResult{I: i, Event: describe(cur.LastEvent)}
		sr.Skipped, err = applyStep(c, prev, cur)
		if err != nil {
			return nil, fmt.Errorf("%s step %d %s: %w", t.Name, i, sr.Event, err)
		}
		snap, err := c.Snapshot()
		if err != nil {
			return nil, err
		}
		res.Snaps = append(res.Snaps, snap)
		var diffs []string
		if sr.Skipped != "" {
			diffs = append(diffs, "step not applied: "+sr.Skipped)
		}
		if d := diffState(snap, toCore(cur, n)); d != "" {
			diffs = append(diffs, d)
		}
		want, err := bag(cur.Net)
		if err != nil {
			return nil, err
		}
		if got := flightBag(c.InFlight()); !reflect.DeepEqual(got, want) {
			diffs = append(diffs, fmt.Sprintf("net svc=%s tla=%s", fmtBag(got), fmtBag(want)))
		}
		sr.Diff = strings.Join(diffs, "; ")
		if sr.Diff != "" && res.FirstDiv < 0 {
			res.FirstDiv = len(res.Steps)
		}
		res.Steps = append(res.Steps, sr)
	}
	if res.Ledger, err = c.Ledger(); err != nil {
		return nil, err
	}
	return res, nil
}

// find returns the index of an in-flight copy with the message value m.
func find(c *payment.Cluster, m core.Effect) int {
	for i, x := range c.InFlight() {
		if x.Body == m {
			return i
		}
	}
	return -1
}

// changed returns the message whose count differs by delta between two net bags.
func changed(prev, cur map[string]int, delta int) (core.Effect, bool) {
	for k, n := range cur {
		if n-prev[k] == delta {
			e, err := parseMsg(k)
			return e, err == nil
		}
	}
	return core.Effect{}, false
}

// applyStep maps one TLA+ action to a Cluster call. It returns a non-empty
// skip reason when the action has no service counterpart or its message is not
// in flight; a service that is down must answer ErrDown (TLA+ rule D).
func applyStep(c *payment.Cluster, prev, cur tlaState) (skipped string, err error) {
	e := cur.LastEvent
	down := func(err error, up bool) error {
		if errors.Is(err, payment.ErrDown) && !up {
			return nil // rule D: a call on a crashed service is a no-op
		}
		return err
	}
	deliver := func(m core.Effect) (string, error) {
		i := find(c, m)
		if i < 0 {
			return fmt.Sprintf("no in-flight copy of %v(o=%d,a=%d)", m.Kind, m.O, m.A), nil
		}
		ok, err := c.DeliverIndex(i)
		if err == nil && !ok {
			err = errors.New("DeliverIndex out of range")
		}
		return "", err
	}
	switch e.Kind {
	case "PlaceOrder":
		return "", down(c.PlaceOrder(e.O, e.A), prev.OrderUp)
	case "RetryTimeout":
		return "", down(c.RetryTimeout(e.O), prev.OrderUp)
	case "RefundOrder":
		return "", down(c.RefundOrder(e.O), prev.OrderUp)
	case "FlushChargeReq":
		return "", down(c.FlushCharge(e.O), prev.OrderUp)
	case "FlushRefundReq":
		return "", down(c.FlushRefund(e.O), prev.OrderUp)
	case "FlushReply":
		return "", down(c.FlushReply(e.O), prev.ProvUp)
	case "ChargeReqRecv":
		return deliver(core.Effect{Kind: core.WireChargeReq, O: e.O, A: e.A})
	case "RefundReqRecv":
		return deliver(core.Effect{Kind: core.WireRefundReq, O: e.O})
	case "PaymentApproved":
		return deliver(core.Effect{Kind: core.WireApproved, O: e.O})
	case "PaymentDeclined":
		return deliver(core.Effect{Kind: core.WireDeclined, O: e.O})
	case "Drop", "Duplicate":
		delta := -1
		if e.Kind == "Duplicate" {
			delta = 1
		}
		pb, err := bag(prev.Net)
		if err != nil {
			return "", err
		}
		cb, err := bag(cur.Net)
		if err != nil {
			return "", err
		}
		var m core.Effect
		found := false
		for k := range pb {
			if cb[k]-pb[k] == delta {
				m, found = k, true
			}
		}
		if !found && delta == 1 {
			for k := range cb {
				if cb[k]-pb[k] == delta {
					m, found = k, true
				}
			}
		}
		if !found {
			return "net diff has no " + e.Kind + " message", nil
		}
		i := find(c, m)
		if i < 0 {
			return fmt.Sprintf("no in-flight copy of %v(o=%d)", m.Kind, m.O), nil
		}
		if (e.Kind == "Drop" && !c.Drop(i)) || (e.Kind == "Duplicate" && !c.Duplicate(i)) {
			return "", fmt.Errorf("%s of copy %d refused", e.Kind, i)
		}
		return "", nil
	case "Crash", "Restart":
		s := core.OrderSvc
		if e.Svc == "Provider" {
			s = core.Provider
		}
		if e.Kind == "Crash" {
			if !c.Crash(s) {
				return "crash refused", nil
			}
			return "", nil
		}
		return "", c.Restart(s)
	}
	return "TLA+ action " + e.Kind + " has no Cluster call", nil
}

// ---- properties checked on the service trajectory (buggy traces) ----

// Violation checks the named TLA+ property on the service snapshots (pairs of
// consecutive snapshots for action properties). It returns a description of the
// first violation, or "" if the service satisfies the property throughout.
func Violation(prop string, snaps []core.State, ledger []core.Effect) string {
	for i, s := range snaps {
		for o, sl := range s.Slots {
			switch prop {
			case "NoDoubleCharge":
				if sl.Prov.ChargeCount > 1 {
					return fmt.Sprintf("state %d: order %d chargeCount=%d", i, o, sl.Prov.ChargeCount)
				}
			case "RefundNeverExceedsCharge":
				if sl.Prov.RefundCount > sl.Prov.ChargeCount {
					return fmt.Sprintf("state %d: order %d refundCount=%d > chargeCount=%d", i, o, sl.Prov.RefundCount, sl.Prov.ChargeCount)
				}
			}
		}
		if i == 0 {
			continue
		}
		p := snaps[i-1]
		for o := range s.Slots {
			a, b := p.Slots[o], s.Slots[o]
			switch prop {
			case "RefundedOnlyFromPaid": // P2b (a) and (b)
				if a.Ord.Status != core.Refunded && b.Ord.Status == core.Refunded && a.Ord.Status != core.Paid {
					return fmt.Sprintf("step %d: order %d %v -> Refunded", i, o, a.Ord.Status)
				}
				if !a.Ord.OutRefund && b.Ord.OutRefund && a.Ord.Status != core.Paid {
					return fmt.Sprintf("step %d: order %d outRefund raised from %v", i, o, a.Ord.Status)
				}
			case "TerminalStable": // P3
				if core.IsTerminal(a.Ord.Status) && (b.Ord.Status != a.Ord.Status || b.Ord.Amount != a.Ord.Amount) {
					return fmt.Sprintf("step %d: order %d terminal %v/%d -> %v/%d", i, o, a.Ord.Status, a.Ord.Amount, b.Ord.Status, b.Ord.Amount)
				}
			case "PinProvRecStable": // A13
				if b.Prov.Rec != a.Prov.Rec && a.Prov.Rec != core.NoRec {
					return fmt.Sprintf("step %d: order %d rec %v -> %v", i, o, a.Prov.Rec, b.Prov.Rec)
				}
				if b.Prov.ChargeCount < a.Prov.ChargeCount || b.Prov.RefundCount < a.Prov.RefundCount {
					return fmt.Sprintf("step %d: order %d a count decreased", i, o)
				}
			}
		}
	}
	if prop == "NoDoubleCharge" {
		per := map[uint32]int{}
		for _, f := range ledger {
			if f.Kind == core.Charge {
				per[f.O]++
				if per[f.O] > 1 {
					return fmt.Sprintf("ledger: order %d charged %d times", f.O, per[f.O])
				}
			}
		}
	}
	return ""
}

// TLASnaps converts a trace to core states, to run Violation on the TLA+ side
// (a property checker that does not flag the TLA+ trace would be vacuous).
func TLASnaps(t *Trace) []core.State {
	var out []core.State
	for _, s := range t.States {
		out = append(out, toCore(s, t.N()))
	}
	return out
}

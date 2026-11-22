package payment

import (
	"encoding/json"
	"errors"
	"fmt"
	"math/rand/v2"
	"net/http"
	"reflect"
	"strings"
	"testing"
	"time"

	"github.com/derangga/learn-formal-verification/internal/sim"
	"github.com/derangga/learn-formal-verification/internal/uc1/core"
)

func must(t *testing.T, err error) {
	t.Helper()
	if err != nil {
		t.Fatal(err)
	}
}

func newC(t *testing.T, cfg Config) *Cluster {
	t.Helper()
	cfg.Dir = t.TempDir()
	if cfg.N == 0 {
		cfg.N = 2
	}
	c, err := NewCluster(cfg)
	must(t, err)
	t.Cleanup(c.Close)
	return c
}

func snap(t *testing.T, c *Cluster) core.State {
	t.Helper()
	s, err := c.Snapshot()
	must(t, err)
	return s
}

// pump delivers FIFO until the wire is empty.
func pump(t *testing.T, c *Cluster) {
	t.Helper()
	for {
		ok, err := c.Next()
		must(t, err)
		if !ok {
			return
		}
	}
}

func TestHappyPathToPaid(t *testing.T) {
	c := newC(t, Config{})
	must(t, c.PlaceOrder(0, 50))
	must(t, c.FlushCharge(0))
	pump(t, c)
	must(t, c.FlushReply(0))
	pump(t, c)
	s := snap(t, c)
	if got := core.St(s, 0); got != core.Paid {
		t.Fatalf("status %v, want Paid", got)
	}
	if p := core.Pr(s, 0); p.Rec != core.Approved || p.ChargeCount != 1 || p.Amt != 50 {
		t.Fatalf("prov %+v", p)
	}
	if !core.Inv(s) {
		t.Fatal("Inv")
	}
}

func TestRefundFlow(t *testing.T) {
	c := newC(t, Config{})
	must(t, c.PlaceOrder(1, 70))
	must(t, c.FlushCharge(1))
	pump(t, c)
	must(t, c.FlushReply(1))
	pump(t, c)
	must(t, c.RefundOrder(1))
	must(t, c.FlushRefund(1))
	pump(t, c)
	s := snap(t, c)
	if core.St(s, 1) != core.Refunded || core.Pr(s, 1).RefundCount != 1 || core.Od(s, 1).OutRefund {
		t.Fatalf("slot %+v", core.Get(s, 1))
	}
	led, err := c.Ledger()
	must(t, err)
	want := []core.Effect{{Kind: core.Charge, O: 1, A: 70}, {Kind: core.Refund, O: 1, A: 70}}
	if !reflect.DeepEqual(led, want) {
		t.Fatalf("ledger %v, want %v", led, want)
	}
}

func TestDeclineGoesFailed(t *testing.T) {
	c := newC(t, Config{Issuer: &ScriptIssuer{Script: []core.Decision{core.Decline}}})
	must(t, c.PlaceOrder(0, 5))
	must(t, c.FlushCharge(0))
	pump(t, c)
	must(t, c.FlushReply(0))
	pump(t, c)
	if got := core.St(snap(t, c), 0); got != core.Failed {
		t.Fatalf("status %v, want Failed", got)
	}
}

func TestCrashAfterCommitBeforeSend(t *testing.T) {
	c := newC(t, Config{Crash: sim.CrashConfig{MaxCrashes: 1,
		Script: []sim.CrashPoint{{Svc: "OrderSvc", Point: AfterCommit, Nth: 1}}}})
	must(t, c.PlaceOrder(0, 9)) // commits the outbox row, then the service crashes
	if err := c.FlushCharge(0); !errors.Is(err, ErrDown) {
		t.Fatalf("flush on crashed service: %v, want ErrDown", err)
	}
	if len(c.InFlight()) != 0 {
		t.Fatal("nothing may be sent while down")
	}
	s := snap(t, c) // reads the durable file of the crashed service
	if s.OrderUp || !core.Od(s, 0).OutCharge || core.St(s, 0) != core.AwaitingPayment {
		t.Fatalf("durable state lost: %+v up=%v", core.Od(s, 0), s.OrderUp)
	}
	must(t, c.Restart(core.OrderSvc))
	if s := snap(t, c); !s.OrderUp || !core.Od(s, 0).OutCharge {
		t.Fatal("outbox row lost across restart")
	}
	must(t, c.FlushCharge(0))
	in := c.InFlight()
	if len(in) != 1 || in[0].Body.Kind != core.WireChargeReq || in[0].Body.A != 9 {
		t.Fatalf("in flight %+v", in)
	}
	if core.Od(snap(t, c), 0).OutCharge {
		t.Fatal("flag not cleared by flush")
	}
}

func TestDeliveryToCrashedProviderIsLost(t *testing.T) {
	c := newC(t, Config{Crash: sim.CrashConfig{MaxCrashes: 1}})
	must(t, c.PlaceOrder(0, 3))
	must(t, c.FlushCharge(0))
	if !c.Crash(core.Provider) {
		t.Fatal("crash refused")
	}
	if ok, err := c.DeliverIndex(0); !ok || err != nil {
		t.Fatal(ok, err)
	}
	must(t, c.Restart(core.Provider))
	if p := core.Pr(snap(t, c), 0); p.Rec != core.NoRec || p.ChargeCount != 0 {
		t.Fatalf("lost message had effect: %+v", p)
	}
}

func TestHTTPBadRequests(t *testing.T) {
	c := newC(t, Config{})
	if got := doPost(c.oh, "/place", "{bad"); got != http.StatusBadRequest {
		t.Fatalf("bad /place body: %d, want 400", got)
	}
	if got := doPost(c.oh, "/nope", `{"o":0}`); got != http.StatusNotFound {
		t.Fatalf("unknown route: %d, want 404", got)
	}
}

// Provider commits Approved + reply outbox, crashes before FlushReply; after
// restart the reply is still in the outbox and goes out.
func TestProviderCrashAfterCommitBeforeReply(t *testing.T) {
	c := newC(t, Config{Crash: sim.CrashConfig{MaxCrashes: 1,
		Script: []sim.CrashPoint{{Svc: "Provider", Point: AfterCommit, Nth: 1}}}})
	must(t, c.PlaceOrder(0, 8))
	must(t, c.FlushCharge(0))
	if ok, err := c.DeliverIndex(0); !ok || err != nil { // provider commits, then crashes
		t.Fatal(ok, err)
	}
	if err := c.FlushReply(0); !errors.Is(err, ErrDown) {
		t.Fatalf("flush on crashed provider: %v", err)
	}
	if len(c.InFlight()) != 0 {
		t.Fatal("nothing may be sent while down")
	}
	s := snap(t, c)
	if p := core.Pr(s, 0); s.ProvUp || p.Rec != core.Approved || !p.OutReply || p.ChargeCount != 1 {
		t.Fatalf("durable provider state: %+v up=%v", p, s.ProvUp)
	}
	must(t, c.Restart(core.Provider))
	if !core.Pr(snap(t, c), 0).OutReply {
		t.Fatal("reply outbox row lost across restart")
	}
	must(t, c.FlushReply(0))
	in := c.InFlight()
	if len(in) != 1 || in[0].Body.Kind != core.WireApproved {
		t.Fatalf("in flight %+v", in)
	}
	pump(t, c)
	if got := core.St(snap(t, c), 0); got != core.Paid {
		t.Fatalf("status %v, want Paid", got)
	}
}

func TestListenLocalOnly(t *testing.T) {
	c := newC(t, Config{})
	if _, _, err := ListenLocal(c.oh, "0.0.0.0:0"); err == nil {
		t.Fatal("non-loopback accepted")
	}
	addr, stop, err := ListenLocal(c.oh, "127.0.0.1:0")
	must(t, err)
	defer stop()
	resp, err := (&http.Client{Timeout: 5 * time.Second}).Post("http://"+addr.String()+"/place", "application/json", strings.NewReader(`{"o":0,"a":4}`))
	must(t, err)
	defer resp.Body.Close()
	var fx []core.Effect
	must(t, json.NewDecoder(resp.Body).Decode(&fx))
	if resp.StatusCode != 200 || core.St(snap(t, c), 0) != core.AwaitingPayment {
		t.Fatalf("status %d", resp.StatusCode)
	}
}

// randomRun drives one seeded run and checks P1, P2a and Inv after every step.
func randomRun(t *testing.T, seed uint64, steps int) *Cluster {
	t.Helper()
	c := newC(t, Config{N: 2, Seed: seed,
		Faults: sim.Faults{Drop: 0.15, Dup: 0.15, MaxDup: 2, Reorder: true},
		Crash:  sim.CrashConfig{Prob: 0.08, MaxCrashes: 3},
		Issuer: NewSeededIssuer(seed, 0.3)})
	rng := rand.New(rand.NewPCG(seed, 99))
	svcs := []core.Service{core.OrderSvc, core.Provider}
	for i := 0; i < steps; i++ {
		o := uint32(rng.IntN(2))
		var err error
		switch rng.IntN(12) {
		case 0, 1:
			err = c.PlaceOrder(o, uint32(1+rng.IntN(3)))
		case 2:
			err = c.RetryTimeout(o)
		case 3:
			err = c.RefundOrder(o)
		case 4, 5:
			err = c.FlushCharge(o)
		case 6:
			err = c.FlushRefund(o)
		case 7:
			err = c.FlushReply(o)
		case 8, 9, 10:
			_, err = c.Next()
		case 11:
			if s := svcs[rng.IntN(2)]; rng.IntN(2) == 0 {
				c.Crash(s)
			} else {
				err = c.Restart(s)
			}
		}
		if err != nil && !errors.Is(err, ErrDown) {
			t.Fatalf("seed %d step %d: %v", seed, i, err)
		}
		checkInvariants(t, c, seed, i)
	}
	return c
}

func checkInvariants(t *testing.T, c *Cluster, seed uint64, i int) {
	t.Helper()
	s := snap(t, c)
	led, err := c.Ledger()
	must(t, err)
	n := map[core.EffectKind]map[uint32]int{core.Charge: {}, core.Refund: {}}
	for _, f := range led {
		n[f.Kind][f.O]++
	}
	for o := uint32(0); o < c.N; o++ {
		if n[core.Charge][o] > 1 { // P1 on ledger rows
			t.Fatalf("seed %d step %d: P1 order %d charged %d times", seed, i, o, n[core.Charge][o])
		}
		if n[core.Refund][o] > n[core.Charge][o] { // P2a on ledger rows
			t.Fatalf("seed %d step %d: P2a order %d", seed, i, o)
		}
	}
	if !core.Inv(s) {
		t.Fatalf("seed %d step %d: Inv violated: %+v", seed, i, s)
	}
}

// cov counts what the fault runs actually exercised.
type cov struct {
	dupDelivered, drops, crashOrder, crashProv    int
	dedupe, declinedAtProv, declinedApplied       int
	refundRows, refundOrderApplied, charges, paid int
}

func (v *cov) add(t *testing.T, c *Cluster) {
	t.Helper()
	for _, e := range c.Trace.Entries {
		switch e.Kind {
		case "drop":
			v.drops++
		case "crash":
			if e.Svc == "OrderSvc" {
				v.crashOrder++
			} else {
				v.crashProv++
			}
		case "deliver":
			var id, orig int
			if _, err := fmt.Sscanf(e.Detail, "id=%d orig=%d", &id, &orig); err == nil && id != orig {
				v.dupDelivered++
			}
		}
	}
	s := core.Init(c.N)
	for _, e := range c.Log() {
		switch {
		case e.Kind == core.ChargeReqRecv && e.A > 0 && core.Pr(s, e.O).Rec != core.NoRec:
			v.dedupe++
		case e.Kind == core.ChargeReqRecv && e.A > 0 && e.D == core.Decline:
			v.declinedAtProv++
		case e.Kind == core.PaymentDeclined && core.St(s, e.O) == core.AwaitingPayment:
			v.declinedApplied++
		case e.Kind == core.RefundOrder && core.St(s, e.O) == core.Paid:
			v.refundOrderApplied++
		case e.Kind == core.PaymentApproved && core.St(s, e.O) == core.AwaitingPayment:
			v.paid++
		}
		s, _ = core.Step(s, e)
	}
	led, err := c.Ledger()
	must(t, err)
	for _, f := range led {
		if f.Kind == core.Refund {
			v.refundRows++
		} else if f.Kind == core.Charge {
			v.charges++
		}
	}
}

func (v cov) check(t *testing.T) {
	t.Helper()
	t.Logf("coverage: %+v", v)
	for name, n := range map[string]int{
		"duplicates delivered": v.dupDelivered, "drops": v.drops, "order crashes": v.crashOrder,
		"provider crashes": v.crashProv, "provider dedupe branch": v.dedupe,
		"declined at provider": v.declinedAtProv, "Declined applied at order": v.declinedApplied,
		"Refund ledger rows": v.refundRows, "RefundOrder applied": v.refundOrderApplied,
		"charges": v.charges, "Approved applied": v.paid,
	} {
		if n == 0 {
			t.Fatalf("fault runs never exercised: %s (%+v)", name, v)
		}
	}
}

const runSeeds, runSteps = 200, 150

func TestP1NoDoubleCharge(t *testing.T) {
	var v cov
	for seed := uint64(1); seed <= runSeeds; seed++ {
		v.add(t, randomRun(t, seed, runSteps))
	}
	v.check(t)
}

// Snapshot equals folding core.Step over the events the services applied.
func TestDifferentialAgainstCoreFold(t *testing.T) {
	var v cov
	for seed := uint64(1); seed <= runSeeds/2; seed++ {
		c := randomRun(t, seed, runSteps)
		s := core.Init(c.N)
		for _, e := range c.Log() {
			s, _ = core.Step(s, e)
		}
		if got := snap(t, c); !reflect.DeepEqual(got, s) {
			t.Fatalf("seed %d: snapshot %+v\nfold     %+v\nlog %v", seed, got, s, c.Log())
		}
		v.add(t, c)
	}
	v.check(t)
}

func doPost(h http.Handler, path, body string) int {
	w := newRec()
	h.ServeHTTP(w, newReq(path, body))
	return w.Code
}

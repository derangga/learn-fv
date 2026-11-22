package sim

import (
	"reflect"
	"slices"
	"testing"
	"time"
)

func TestFakeClock(t *testing.T) {
	t0 := time.Unix(1000, 0)
	f := NewFake(t0)
	if !f.Now().Equal(t0) {
		t.Fatal("fake clock moved on its own")
	}
	f.Advance(5 * time.Second)
	if !f.Now().Equal(t0.Add(5 * time.Second)) {
		t.Fatal("Advance")
	}
	f.Set(t0)
	if !f.Now().Equal(t0) {
		t.Fatal("Set")
	}
	var _ Clock = Real{}
	var _ Clock = f
}

// run drives a mixed workload and returns the full trace.
func run(seed uint64) []string {
	tr := &Trace{}
	cr := NewCrasher(seed, CrashConfig{Prob: 0.3, MaxCrashes: 2}, tr)
	n := NewNet[int](seed, Faults{Drop: 0.2, Dup: 0.3, MaxDup: 2, Reorder: true}, cr, tr)
	for i := 0; i < 20; i++ {
		n.Send([]string{"a", "b"}[i%2], i)
		if cr.ShouldCrash("a", "send") {
			cr.Restart("a")
		}
		if i%3 == 0 {
			n.Next()
		}
	}
	for {
		if _, ok := n.Next(); !ok {
			break
		}
	}
	return tr.Strings()
}

func TestDeterministic(t *testing.T) {
	a, b := run(7), run(7)
	if !reflect.DeepEqual(a, b) || len(a) == 0 {
		t.Fatal("same seed gave different traces")
	}
	if reflect.DeepEqual(a, run(8)) {
		t.Fatal("different seeds gave the same trace")
	}
}

func TestDrop(t *testing.T) {
	tr := &Trace{}
	n := NewNet[int](1, Faults{Drop: 1}, nil, tr)
	n.Send("a", 1)
	if _, ok := n.Next(); ok || len(n.InFlight()) != 0 {
		t.Fatal("message not dropped")
	}
	if tr.Entries[len(tr.Entries)-1].Kind != "drop" {
		t.Fatal("drop not traced")
	}
}

func TestDupBound(t *testing.T) {
	tr := &Trace{}
	n := NewNet[int](1, Faults{Dup: 1, MaxDup: 2}, nil, tr)
	n.Send("a", 1)
	got := 0
	for {
		if _, ok := n.Next(); !ok {
			break
		}
		got++
	}
	if got != 3 { // original + MaxDup copies
		t.Fatalf("delivered %d, want 3", got)
	}
}

func TestReorderHappens(t *testing.T) {
	order := func(seed uint64, reorder bool) []int {
		n := NewNet[int](seed, Faults{Reorder: reorder}, nil, &Trace{})
		for i := 0; i < 5; i++ {
			n.Send("a", i)
		}
		var out []int
		for {
			d, ok := n.Next()
			if !ok {
				return out
			}
			out = append(out, d.Body)
		}
	}
	if !slices.Equal(order(1, false), []int{0, 1, 2, 3, 4}) {
		t.Fatal("no-reorder config must be FIFO")
	}
	for seed := uint64(0); seed < 20; seed++ {
		if !slices.Equal(order(seed, true), []int{0, 1, 2, 3, 4}) {
			return
		}
	}
	t.Fatal("no seed reordered")
}

func TestScripted(t *testing.T) {
	tr := &Trace{}
	n := NewNet[string](0, Faults{MaxDup: 1}, nil, tr)
	n.Send("a", "x")
	n.Send("a", "y")
	n.Send("a", "z")
	if !n.Duplicate(1) || n.Duplicate(1) || n.Duplicate(3) {
		t.Fatal("dup bound is per original, copies share it")
	}
	n.Drop(0)
	var got []string
	for len(n.InFlight()) > 0 {
		d, _ := n.Deliver(len(n.InFlight()) - 1)
		got = append(got, d.Body)
	}
	if !slices.Equal(got, []string{"y", "z", "y"}) {
		t.Fatalf("got %v", got)
	}
}

func TestDeliveryToDownIsLost(t *testing.T) {
	tr := &Trace{}
	cr := NewCrasher(0, CrashConfig{MaxCrashes: 1}, tr)
	n := NewNet[int](0, Faults{}, cr, tr)
	n.Send("a", 1)
	cr.Crash("a")
	d, ok := n.Next()
	if !ok || !d.Lost {
		t.Fatal("expected a lost delivery")
	}
	cr.Restart("a")
	n.Send("a", 2)
	if d, _ := n.Next(); d.Lost {
		t.Fatal("up service must receive")
	}
}

func TestCrashBudgetAndScript(t *testing.T) {
	tr := &Trace{}
	cr := NewCrasher(3, CrashConfig{MaxCrashes: 1, Script: []CrashPoint{{"a", "p", 2}}}, tr)
	if cr.ShouldCrash("a", "p") || !cr.Up("a") {
		t.Fatal("crashed on 1st occurrence")
	}
	if !cr.ShouldCrash("a", "p") || cr.Up("a") {
		t.Fatal("scripted crash on 2nd occurrence missing")
	}
	cr.Restart("a")
	if cr.Crash("a") || cr.Crashes("a") != 1 {
		t.Fatal("budget exceeded")
	}
	if !cr.Crash("b") || cr.Crashes("b") != 1 {
		t.Fatal("budget is per service")
	}
}

func TestCrashRandomRespectsBudget(t *testing.T) {
	cr := NewCrasher(5, CrashConfig{Prob: 1, MaxCrashes: 3}, &Trace{})
	for i := 0; i < 50; i++ {
		if cr.ShouldCrash("a", "p") {
			cr.Restart("a")
		}
	}
	if cr.Crashes("a") != 3 {
		t.Fatalf("crashes=%d, want 3", cr.Crashes("a"))
	}
}

func kinds(tr *Trace) []string {
	var k []string
	for _, e := range tr.Entries {
		k = append(k, e.Kind)
	}
	return k
}

func TestDupDenied(t *testing.T) {
	tr := &Trace{}
	n := NewNet[int](1, Faults{MaxDup: 1}, nil, tr)
	n.Send("a", 1)
	n.Duplicate(0)
	if n.Duplicate(0) {
		t.Fatal("bound ignored")
	}
	if !slices.Equal(kinds(tr), []string{"send", "dup", "dup-denied"}) {
		t.Fatalf("trace %v", kinds(tr))
	}
	// inside Next: bound hit must be traced too
	tr2 := &Trace{}
	n2 := NewNet[int](1, Faults{Dup: 1, MaxDup: 1}, nil, tr2)
	n2.Send("a", 1)
	for {
		if _, ok := n2.Next(); !ok {
			break
		}
	}
	if !slices.Contains(kinds(tr2), "dup-denied") {
		t.Fatalf("Next did not trace dup-denied: %v", kinds(tr2))
	}
}

func TestCrashDenied(t *testing.T) {
	tr := &Trace{}
	cr := NewCrasher(0, CrashConfig{MaxCrashes: 1, Script: []CrashPoint{{"a", "p", 2}}}, tr)
	cr.Crash("a")
	cr.Crash("a") // already down
	cr.Restart("a")
	cr.Restart("a") // already up
	cr.ShouldCrash("a", "p")
	if cr.ShouldCrash("a", "p") { // scripted but budget spent
		t.Fatal("budget ignored")
	}
	want := []string{"crash", "crash-denied", "restart", "restart-noop", "crash-denied"}
	if !slices.Equal(kinds(tr), want) {
		t.Fatalf("trace %v", kinds(tr))
	}
	// zero config: scripted crash is refused
	z := NewCrasher(0, CrashConfig{Script: []CrashPoint{{"a", "p", 1}}}, nil)
	if z.ShouldCrash("a", "p") || !z.Up("a") {
		t.Fatal("zero config must never crash")
	}
}

func TestScriptedOutOfRange(t *testing.T) {
	tr := &Trace{}
	n := NewNet[int](0, Faults{MaxDup: 1}, nil, tr)
	n.Send("a", 1)
	before := len(tr.Entries)
	if _, ok := n.Deliver(5); ok {
		t.Fatal("Deliver")
	}
	if n.Drop(-1) || n.Duplicate(1) {
		t.Fatal("Drop/Duplicate")
	}
	if len(tr.Entries) != before || len(n.InFlight()) != 1 {
		t.Fatal("out-of-range call had an effect")
	}
}

func TestNilTrace(t *testing.T) {
	cr := NewCrasher(1, CrashConfig{Prob: 1, MaxCrashes: 1}, nil)
	n := NewNet[int](1, Faults{Dup: 0.5, MaxDup: 1}, cr, nil)
	n.Send("a", 1)
	cr.ShouldCrash("a", "p")
	for {
		if _, ok := n.Next(); !ok {
			break
		}
	}
	cr.Restart("a")
	var tr *Trace
	if tr.Strings() != nil {
		t.Fatal("nil trace Strings")
	}
}

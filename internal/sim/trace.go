package sim

import "fmt"

// TraceEntry records one decision (a fault, a delivery or a crash).
type TraceEntry struct {
	Seq    int
	Kind   string // send, deliver, lost, drop, dup, crash, crash-denied, restart, restart-noop, dup-denied
	Svc    string
	Detail string
}

func (e TraceEntry) String() string {
	return fmt.Sprintf("%d %s %s %s", e.Seq, e.Kind, e.Svc, e.Detail)
}

// Trace is shared by a Net and its Crasher so the schedule reads in order.
// A nil *Trace is valid: entries are discarded and Strings returns nil.
// OnEntry, if set, is called for each entry as it is added.
type Trace struct {
	Entries []TraceEntry
	OnEntry func(TraceEntry)
}

func (t *Trace) add(kind, svc, detail string) {
	if t == nil {
		return
	}
	e := TraceEntry{Seq: len(t.Entries), Kind: kind, Svc: svc, Detail: detail}
	t.Entries = append(t.Entries, e)
	if t.OnEntry != nil {
		t.OnEntry(e)
	}
}

// Strings renders the whole schedule, one line per entry.
func (t *Trace) Strings() []string {
	if t == nil {
		return nil
	}
	out := make([]string, len(t.Entries))
	for i, e := range t.Entries {
		out[i] = e.String()
	}
	return out
}

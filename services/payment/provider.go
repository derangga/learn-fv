package payment

import (
	"database/sql"

	"github.com/derangga/learn-formal-verification/internal/sim"
	"github.com/derangga/learn-formal-verification/internal/uc1/core"
)

const providerSchema = `
CREATE TABLE IF NOT EXISTS prov(o INTEGER PRIMARY KEY, rec INTEGER NOT NULL, amt INTEGER NOT NULL);
CREATE TABLE IF NOT EXISTS ledger(id INTEGER PRIMARY KEY AUTOINCREMENT, o INTEGER NOT NULL, kind INTEGER NOT NULL, amount INTEGER NOT NULL);
CREATE TABLE IF NOT EXISTS outbox(o INTEGER NOT NULL, kind TEXT NOT NULL, PRIMARY KEY(o, kind));`

// Issuer is the card issuer's answer for a first charge request.
type Issuer interface{ Decide(o uint32) core.Decision }

// ProvSvc owns the idempotency record, the ledger and the reply outbox.
// ChargeCount and RefundCount are not stored: they are counts of ledger rows.
type ProvSvc struct {
	base
	issuer Issuer
}

func newProvSvc(path string, n uint32, cr *sim.Crasher, is Issuer) *ProvSvc {
	return &ProvSvc{base{name: core.Provider.String(), path: path, schema: providerSchema, n: n, cr: cr}, is}
}

// Apply runs one provider-side event (ChargeReqRecv, RefundReqRecv, FlushReply).
func (s *ProvSvc) Apply(e core.Event) ([]core.Effect, error) {
	return s.apply(e, loadProv, saveProv)
}

func ledgerCount(q querier, o uint32, k core.EffectKind) (n uint32, err error) {
	err = q.QueryRow(`SELECT COUNT(*) FROM ledger WHERE o=? AND kind=?`, o, k).Scan(&n)
	return
}

func loadProv(q querier, o uint32) (core.Slot, error) {
	var sl core.Slot
	var rec uint32
	if err := scanOrNone(q.QueryRow(`SELECT rec, amt FROM prov WHERE o=?`, o), &rec, &sl.Prov.Amt); err != nil {
		return sl, err
	}
	sl.Prov.Rec = core.Res(rec)
	var err error
	if sl.Prov.ChargeCount, err = ledgerCount(q, o, core.Charge); err != nil {
		return sl, err
	}
	if sl.Prov.RefundCount, err = ledgerCount(q, o, core.Refund); err != nil {
		return sl, err
	}
	sl.Prov.OutReply, err = hasRow(q, o, "reply")
	return sl, err
}

func saveProv(tx *sql.Tx, o uint32, sl core.Slot, fx []core.Effect) error {
	p := sl.Prov
	if _, err := tx.Exec(`INSERT INTO prov(o, rec, amt) VALUES(?,?,?)
		ON CONFLICT(o) DO UPDATE SET rec=excluded.rec, amt=excluded.amt`, o, p.Rec, p.Amt); err != nil {
		return err
	}
	for _, f := range fx {
		if isLedger(f.Kind) {
			if _, err := tx.Exec(`INSERT INTO ledger(o, kind, amount) VALUES(?,?,?)`, f.O, f.Kind, f.A); err != nil {
				return err
			}
		}
	}
	return setRow(tx, o, "reply", p.OutReply)
}

func (s *ProvSvc) load(o uint32) (sl core.Slot, err error) {
	err = s.read(func(q querier) (e error) { sl, e = loadProv(q, o); return })
	return
}

// Ledger returns every Charge/Refund row in insertion order.
func (s *ProvSvc) Ledger() (out []core.Effect, err error) {
	err = s.read(func(q querier) error {
		rows, e := q.Query(`SELECT kind, o, amount FROM ledger ORDER BY id`)
		if e != nil {
			return e
		}
		defer rows.Close()
		for rows.Next() {
			var f core.Effect
			if e := rows.Scan(&f.Kind, &f.O, &f.A); e != nil {
				return e
			}
			out = append(out, f)
		}
		return rows.Err()
	})
	return
}

// SeededIssuer declines with probability P, drawn from a seeded stream.
type SeededIssuer struct {
	P   float64
	rng *rngSrc
}

// ScriptIssuer answers from Script in order, then Approve forever.
type ScriptIssuer struct {
	Script []core.Decision
	i      int
}

func (s *ScriptIssuer) Decide(uint32) core.Decision {
	if s.i < len(s.Script) {
		s.i++
		return s.Script[s.i-1]
	}
	return core.Approve
}

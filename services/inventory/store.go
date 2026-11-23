package inventory

import (
	"database/sql"
	"errors"

	_ "modernc.org/sqlite" // pure-Go driver, no cgo

	"github.com/derangga/learn-formal-verification/internal/uc2/core"
)

const schema = `
CREATE TABLE IF NOT EXISTS meta(id INTEGER PRIMARY KEY CHECK(id=1), up INTEGER NOT NULL, clock INTEGER NOT NULL);
CREATE TABLE IF NOT EXISTS stock(pos INTEGER PRIMARY KEY, sku INTEGER NOT NULL, total INTEGER NOT NULL,
	available INTEGER NOT NULL, reserved INTEGER NOT NULL, sold INTEGER NOT NULL);
CREATE TABLE IF NOT EXISTS res(pos INTEGER PRIMARY KEY, id INTEGER NOT NULL, sku INTEGER NOT NULL, qty INTEGER NOT NULL,
	status INTEGER NOT NULL, expires_at INTEGER NOT NULL, confirmed_at INTEGER NOT NULL, returned INTEGER NOT NULL);
CREATE TABLE IF NOT EXISTS outbox(seq INTEGER PRIMARY KEY AUTOINCREMENT, kind INTEGER NOT NULL, id INTEGER NOT NULL,
	sku INTEGER NOT NULL, qty INTEGER NOT NULL, expires_at INTEGER NOT NULL, reason INTEGER NOT NULL, sent INTEGER NOT NULL DEFAULT 0);`

type querier interface {
	QueryRow(query string, args ...any) *sql.Row
	Query(query string, args ...any) (*sql.Rows, error)
}

func openDB(path string) (*sql.DB, error) {
	db, err := sql.Open("sqlite", "file:"+path+"?_pragma=synchronous(OFF)&_pragma=busy_timeout(5000)")
	if err != nil {
		return nil, err
	}
	db.SetMaxOpenConns(1)
	if _, err := db.Exec(schema); err != nil {
		db.Close()
		return nil, err
	}
	return db, nil
}

// load reads the whole durable state. Reservations keep their insertion order
// (pos), so a fold of core.Step compares equal.
func load(q querier) (core.State, bool, error) {
	var s core.State
	var up int
	err := q.QueryRow(`SELECT up, clock FROM meta WHERE id=1`).Scan(&up, &s.Clock)
	if errors.Is(err, sql.ErrNoRows) {
		return s, false, nil
	}
	if err != nil {
		return s, false, err
	}
	s.Up = up != 0
	rows, err := q.Query(`SELECT sku, total, available, reserved, sold FROM stock ORDER BY pos`)
	if err != nil {
		return s, false, err
	}
	for rows.Next() {
		var k core.Stock
		if err := rows.Scan(&k.Sku, &k.Total, &k.Available, &k.Reserved, &k.Sold); err != nil {
			rows.Close()
			return s, false, err
		}
		s.Stocks = append(s.Stocks, k)
	}
	rows.Close()
	rows, err = q.Query(`SELECT id, sku, qty, status, expires_at, confirmed_at, returned FROM res ORDER BY pos`)
	if err != nil {
		return s, false, err
	}
	defer rows.Close()
	for rows.Next() {
		var r core.Res
		if err := rows.Scan(&r.ID, &r.Sku, &r.Qty, &r.Status, &r.ExpiresAt, &r.ConfirmedAt, &r.Returned); err != nil {
			return s, false, err
		}
		s.Res = append(s.Res, r)
	}
	return s, true, rows.Err()
}

// save writes the state and appends fx to the outbox, in the caller's transaction.
func save(tx *sql.Tx, s core.State, fx []core.Effect) error {
	up := 0
	if s.Up {
		up = 1
	}
	if _, err := tx.Exec(`INSERT INTO meta(id, up, clock) VALUES(1,?,?)
		ON CONFLICT(id) DO UPDATE SET up=excluded.up, clock=excluded.clock`, up, s.Clock); err != nil {
		return err
	}
	for i, k := range s.Stocks {
		if _, err := tx.Exec(`INSERT OR REPLACE INTO stock(pos, sku, total, available, reserved, sold) VALUES(?,?,?,?,?,?)`,
			i, k.Sku, k.Total, k.Available, k.Reserved, k.Sold); err != nil {
			return err
		}
	}
	for i, r := range s.Res {
		if _, err := tx.Exec(`INSERT OR REPLACE INTO res(pos, id, sku, qty, status, expires_at, confirmed_at, returned) VALUES(?,?,?,?,?,?,?,?)`,
			i, r.ID, r.Sku, r.Qty, r.Status, r.ExpiresAt, r.ConfirmedAt, r.Returned); err != nil {
			return err
		}
	}
	for _, f := range fx {
		if _, err := tx.Exec(`INSERT INTO outbox(kind, id, sku, qty, expires_at, reason) VALUES(?,?,?,?,?,?)`,
			f.Kind, f.ID, f.Sku, f.Qty, f.ExpiresAt, f.Reason); err != nil {
			return err
		}
	}
	return nil
}

// outbox lists effect rows in insertion order; onlyUnsent filters to sent=0.
func outbox(q querier, onlyUnsent bool) ([]core.Effect, []int64, error) {
	where := ""
	if onlyUnsent {
		where = " WHERE sent=0"
	}
	rows, err := q.Query(`SELECT seq, kind, id, sku, qty, expires_at, reason FROM outbox` + where + ` ORDER BY seq`)
	if err != nil {
		return nil, nil, err
	}
	defer rows.Close()
	var fx []core.Effect
	var seqs []int64
	for rows.Next() {
		var f core.Effect
		var seq int64
		if err := rows.Scan(&seq, &f.Kind, &f.ID, &f.Sku, &f.Qty, &f.ExpiresAt, &f.Reason); err != nil {
			return nil, nil, err
		}
		fx, seqs = append(fx, f), append(seqs, seq)
	}
	return fx, seqs, rows.Err()
}

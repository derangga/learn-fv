# UC2 pure core (`internal/uc2/core`)

Authoring time (estimate, no timer was kept): about 40 minutes for `core.go` and `core_test.go`, including the mutation sanity runs. Failed iterations: 1 (see Friction). Wall hit: none.

## What was built

- `internal/uc2/core/core.go` (435 lines): `Status` (`Held|Confirmed|Expired`), `Stock`, `Res` (with ghost fields `ConfirmedAt`, `Returned`), `State` (`Up`, `Clock`, `Stocks`, `Res`), `StockInit`, `Kind` (`Reserve|Confirm|Expire|Tick|Crash|Restart`), `EffectKind` (`FxReserved|FxConfirmed|FxReleased|FxRejected`), `Reason` (the 8 reject reasons), `Init`, `Step`. All numbers are `int64`. Standard library only.
  - `Step` clones both slices first, so its input is never mutated. S0 (down) is checked before the event switch. `reserve`, `confirm`, `expire` are the S2/S3, S4/S5, S6/S7 branches. S3 order: `BadRequest` (`qty < 1` or `ttl < 1`), `UnknownSku`, `DuplicateId`, `InsufficientStock` (`qty > available`, so `qty == available` is accepted). `Confirm`: `UnknownReservation`, `NotHeld`, `TooLate` (`Due`), else S4. `Expire`: `UnknownReservation`, `NotHeld`, `NotYet` (not `Due`), else S6. `Due == expiresAt <= clock`.
  - The three subtractions each carry a comment naming their guard: `Reserve` (`qty <= available`, just checked), `Confirm` and `Expire` (`reserved - qty`, guard A1: `reserved == HeldQty >= qty` and the record is `Held`).
  - Exported predicates: `NonNegativeAvailable` (P1), `Conservation` (P2), `ExpiredReturnedOnce` (P3), `ConfirmedBeforeDue` (P4a), `CountersMatchRecords` (A1), `UniqueIdsKnownSku` (A2), `Inv` (their conjunction); transition and history predicates `ExpiredNeverConfirmed` (P4), `ConfirmOnlyBeforeDue` (P4b), `NoOversell` (P1b), `ReleasedMatchesReturned` and `ReleasedCount` (P3b). Helpers `HeldQty`, `ConfirmedQty`, `Due`.
- `internal/uc2/core/core_test.go` (591 lines): every test named in UC2.md sections 3 and 4 (`TestInitSatisfiesInv`, `TestP1NonNegativeAvailable`, `TestP2Conservation`, `TestP3ExpiredReturnsOnce`, `TestP4ExpiredNeverConfirmed`, `TestP1bNoOversell`, `TestP3bReleasedEffectCount`, `TestP4aConfirmedBeforeDue`, `TestP4bConfirmOnlyBeforeDue`, `TestA1CountersMatchRecords`, `TestA2UniqueIds`, `TestPinDown`, `TestPinTick`, `TestPinReserveOk`, `TestPinReserveRejected`, `TestPinConfirmOk`, `TestPinConfirmRejected`, `TestPinExpireOk`, `TestPinExpireRejected`, `TestPinCrash`, `TestPinRestart`, `TestPinStable`, `TestPinDuplicateDelivery`) plus `TestInvHolds` (the whole conjunction after every step).
  - Property tests share `forRuns`: seeded PCG, 1000 sequences of 0 to 150 events, 1 to 3 SKUs (totals 1 to 6), events for an unknown SKU, `qty` 0 to 7, `ttl` 0 to 3, ids 1 to 6, all six kinds, and 20% of events re-sent from earlier in the sequence (duplicate and reorder). `forRuns` also checks that `Step` never mutates its input, and requires every one of 27 guarded branches (22 plus per-kind down-dropped, crash-while-down, restart-while-up) to have fired (`t.Fatalf("vacuous ...")` otherwise).
  - Pins build the expected state independently (clone the pre-state, set only the fields S2 to S9 name) and compare field by field; reject pins recompute the reason in the test's own check order. Directed cases: `qty == available` accepted, `available + 1` rejected, every-check-failing orders for S3, `Confirm` at `clock == expiresAt - 1` accepted and at `expiresAt` `TooLate` with the record still `Held`, `Expire` at `expiresAt - 1` `NotYet` and at `expiresAt` accepted. `TestInitSatisfiesInv` also builds one bad state per predicate and checks that predicate (and `Inv`) rejects it.
  - Values stay far below 2^31.

## Commands and output

```
$ source .nix/env.sh; go vet ./... && go test ./internal/uc2/... ./services/inventory/... -count=1
ok  	github.com/derangga/learn-formal-verification/internal/uc2/core	6.486s
ok  	github.com/derangga/learn-formal-verification/services/inventory	34.678s

$ go test ./... -count=1
ok  	github.com/derangga/learn-formal-verification/internal/sim	0.007s
ok  	github.com/derangga/learn-formal-verification/internal/uc1/core	0.452s
ok  	github.com/derangga/learn-formal-verification/internal/uc2/core	4.531s
ok  	github.com/derangga/learn-formal-verification/mutants/uc1	57.324s
ok  	github.com/derangga/learn-formal-verification/services/inventory	17.139s
ok  	github.com/derangga/learn-formal-verification/services/payment	135.221s
```
(`go vet ./...` printed nothing. The `go test ./...` listing is the tail of the output; no line was FAIL.)

Non-vacuity, one run of the 1000 seeded sequences (`TestP1NonNegativeAvailable`; the other tests print the same order of magnitude). 27 branch counters must all be nonzero:

```
confirm-NotHeld:884 confirm-TooLate:616 confirm-UnknownReservation:8245 confirm-ok:313 confirm-on-Expired:504
crash:1753 crash-while-down:1146 down-dropped-Confirm:4925 down-dropped-Crash:1146 down-dropped-Expire:4957
down-dropped-Reserve:7340 expire-NotHeld:973 expire-NotYet:348 expire-UnknownReservation:8150
expire-after-confirm:362 expire-ok:567 expire-on-Expired:611 multi-sku-frame:1207
rej-BadRequest:5167 rej-DuplicateId:1543 rej-InsufficientStock:3346 rej-UnknownSku:3576
reserve-ok:1511 reserve-qty=avail:532 restart:4500 restart-while-up:3097 tick-down:4928
```

`TestPinDuplicateDelivery` also counts first deliveries that were accepted and requires each count above 0 (S11 two-step form, no delayed duplicates): `Reserve=1510 Confirm=307 Expire=595`.

## Mutation sanity (applied temporarily to `core.go`, reverted, `diff` against the saved original empty)

Tests that failed on an assertion (not only on the vacuity guard), per mutant, each run test by test:

| Mutant (same bug as UC2.md section 5) | Failing tests | UC2.md says |
|---|---|---|
| M1: `Confirm` rejects only when `expiresAt < clock` | InvHolds, P4aConfirmedBeforeDue, P4bConfirmOnlyBeforeDue, PinConfirmRejected | P4a, P4b, S5 (match) |
| M2: `Expire` without the `Held` check | InvHolds, P3ExpiredReturnsOnce, A1CountersMatchRecords, PinExpireRejected, PinStable, PinDuplicateDelivery | P3, A1, S7, S11 (match, plus PinStable) |
| M5a: `Reserve` without the `InsufficientStock` check (plain int64 subtraction) | P1NonNegativeAvailable, InvHolds, PinReserveRejected | P1, P2, P1b, S3 (P1 and S3 match; P2 and P1b do not fail, see below) |
| M6: `Expire` does not reduce `reserved` | InvHolds, P2Conservation, A1CountersMatchRecords, PinExpireOk | P2, A1, S6 (match) |
| M7: duplicate `Reserve` id accepted | InvHolds, P3bReleasedEffectCount, A2UniqueIds, PinReserveRejected, PinDuplicateDelivery | A2, S3, S11 (match, plus P3b) |

Observations on the contract (not changed, for the user):

- M5a: with signed counters and no guard, `available` and `reserved` still move by exactly `qty`, so P2 and P1b hold; the Go tests do not fail them, and the mutant is killed by P1 and S3. UC2.md section 5 lists P2 and P1b for M5a, which looks too strong for the Go form (it fits the truncating M5, which has no Go-only reading here).
- M7 also breaks P3b in Go, because `ReleasedCount` is per id and two records share the id.
- The vacuity guard turns most tests red for any mutant that removes a branch (the branch counter drops to 0). That is intended, but it means the attribution above needs the per-test assertion check, not a plain `go test` listing.

## Ambiguities resolved (literal reading)

1. Path `internal/uc2/core` as the task said, not `internal/inventory/core`.
2. `Qty` and `Ttl` below 1 (including negative) are `BadRequest`; the contract says `== 0` for the check and `>= 1` for accepted.
3. `Confirm` or `Expire` for a record whose SKU is missing from `Stocks` cannot happen under A2; `Step` stays total and returns the state unchanged with no effect. Not covered by a test (unreachable from `Init`).
4. An out-of-range `Kind` value is a no-op with no effects (`Step` is total).
5. `Step` returns a fresh slice copy even for no-ops; `fx` is nil when empty (tests compare `fx != nil` for S0, S1, S8, S9).
6. `Crash` while down and `Restart` while up are applied as S8 and S9 (state `Up` set, no effect).
7. SKU values are arbitrary int64; stocks are found by `Sku`, not by index.
8. `Step` appends `Res` in the order events were accepted (insertion order is part of the Frame in the contract).

## Friction

- Failed iteration 1: my first `TestP1NonNegativeAvailable` asserted `Inv`, so a mutant that broke only P4a also turned P1 red. P1 now checks only `NonNegativeAvailable`; the conjunction is `TestInvHolds`.
- The vacuity guard and the mutation runs: see the third observation above.
- The sandbox needs `GOCACHE=$TMPDIR/gocache` (the default cache dir is read-only), and `services/inventory` needs the module cache, which was at `/tmp/claude-1001/gomodcache` (`GOMODCACHE=... GOPROXY=off`). Neither changes the repo.
- `core.go` is 435 lines against UC1's 348: the contract has more state and 8 reject reasons, and the predicate set (11 exported predicates) is deliberately public for the mutant tests.

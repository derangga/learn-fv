#!/usr/bin/env bash
# Checks UC1 property P1 (an order is never charged twice) in every tool that encodes it.
# Run inside the dev shell, from anywhere:
#   nix develop --command bash .claude/skills/verify-uc1-idempotent-charge/check.sh          # all stages
#   nix develop --command bash .claude/skills/verify-uc1-idempotent-charge/check.sh quick    # skip TLC
# Exit 0 only if every stage passes. TLC scratch files go in a mktemp dir that is deleted on exit.
set -uo pipefail
cd "$(dirname "$0")/../../.." || exit 2
need="go bend"; [ "${1:-}" = quick ] || need="$need tlc"
for t in $need; do command -v "$t" >/dev/null || { echo "missing $t: run this inside 'nix develop --command ...'" >&2; exit 2; }; done
fail=0
bad() { echo "FAIL: $*"; fail=1; }

echo "== bend proofs (bend/uc1/PROOF.bend)"
out=$(bend bend/uc1/PROOF.bend 2>&1)
if grep -q 'ALL PROOFS CHECK' <<<"$out"; then echo "ok: ALL PROOFS CHECK"; else bad "bend proofs"; head -20 <<<"$out"; fi

echo "== bend mutants (each must be rejected for its expected reason)"
bash bend/uc1/mutants/run.sh || bad "bend mutants"

echo "== go: core, mutants, conformance (Go core vs compiled Bend), TLC trace replay, payment service"
# -count=1: the conformance test shells out to bend, and Go's test cache does not see files a subprocess reads.
go test -count=1 ./internal/uc1/... ./mutants/uc1/... ./harness/conformance/... ./harness/tlcreplay/... ./services/payment/... || bad "go tests"

if [ "${1:-}" != quick ]; then
  tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
  echo "== tlc UC1.cfg (N=1): must find no error"
  timeout 1200 tlc -noGenerateSpecTE -workers auto -metadir "$tmp/ok" -config spec/tla/UC1.cfg spec/tla/UC1.tla >"$tmp/ok.out" 2>&1
  if grep -q 'No error has been found' "$tmp/ok.out"; then grep -E 'states generated|depth of the complete' "$tmp/ok.out"; else bad "tlc UC1.cfg"; tail -25 "$tmp/ok.out"; fi
  for m in UC1_buggy UC1_buggy_m3; do   # M1 (no idempotency check) and M3 (check-then-act race): both must break P1
    echo "== tlc $m: must violate NoDoubleCharge"
    timeout 600 tlc -noGenerateSpecTE -workers auto -metadir "$tmp/$m" -config "spec/tla/$m.cfg" "spec/tla/$m.tla" >"$tmp/$m.out" 2>&1
    if grep -q 'Invariant NoDoubleCharge is violated' "$tmp/$m.out"; then grep -m1 'is violated' "$tmp/$m.out"; else bad "tlc $m did not violate NoDoubleCharge"; grep -m3 -E 'Error|violated' "$tmp/$m.out"; fi
  done
fi
[ "$fail" = 0 ] && echo "ALL UC1 P1 CHECKS PASS" || echo "UC1 P1 CHECKS FAILED"
exit "$fail"

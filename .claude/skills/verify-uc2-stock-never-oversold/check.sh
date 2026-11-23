#!/usr/bin/env bash
# Checks UC2 (stock is never oversold: P1, P1b, P2, plus P3, P4 and the pins) in every tool that encodes it.
# Run from anywhere:
#   nix develop --command bash .claude/skills/verify-uc2-stock-never-oversold/check.sh          # all stages
#   nix develop --command bash .claude/skills/verify-uc2-stock-never-oversold/check.sh quick    # skip TLC
# Exit 0 only if every stage passes. TLC scratch files go in a mktemp dir that is deleted on exit.
set -uo pipefail
cd "$(dirname "$0")/../../.." || exit 2
need="go bend"; [ "${1:-}" = quick ] || need="$need tlc"
for t in $need; do command -v "$t" >/dev/null || { echo "missing $t: run this inside 'nix develop --command ...'" >&2; exit 2; }; done
fail=0
bad() { echo "FAIL: $*"; fail=1; }

echo "== bend proofs (bend/uc2/PROOF.bend)"
out=$(bend bend/uc2/PROOF.bend 2>&1)
if grep -q 'ALL PROOFS CHECK' <<<"$out"; then echo "ok: ALL PROOFS CHECK"; else bad "bend proofs"; head -20 <<<"$out"; fi

echo "== bend mutants (each must be rejected for its expected reason)"
bash bend/uc2/mutants/run.sh || bad "bend mutants"

echo "== go: core, mutants, conformance (Go core vs compiled Bend), inventory service"
# -count=1: the conformance test shells out to bend, and Go's test cache does not see files a subprocess reads.
go test -count=1 ./internal/uc2/... ./mutants/uc2/... ./harness/uc2conformance/... ./services/inventory/... || bad "go tests"

if [ "${1:-}" != quick ]; then
  tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
  # Approved bounds: UC2.cfg (ids {1,2}, no duplicate delivery) and UC2_dup.cfg (duplicate delivery, 1 id).
  for c in UC2 UC2_dup; do
    echo "== tlc $c.cfg: must find no error"
    timeout 1500 tlc -noGenerateSpecTE -workers auto -metadir "$tmp/$c" -config "spec/tla/$c.cfg" spec/tla/UC2.tla >"$tmp/$c.out" 2>&1
    if grep -q 'No error has been found' "$tmp/$c.out"; then grep -E 'states generated|depth of the complete' "$tmp/$c.out"; else bad "tlc $c.cfg"; tail -25 "$tmp/$c.out"; fi
  done
  # Mutants that stay cheap (under a minute each) at the contract constants. Each must break the named property.
  # M1b, M3, M3b and M6 take 2 to 3.5 minutes each and M2 does not finish at its cfg bound (docs/results/uc2-mutants.md); Bend and Go cover them.
  while read -r m want; do
    echo "== tlc $m: must violate $want"
    timeout 600 tlc -noGenerateSpecTE -workers auto -metadir "$tmp/$m" -config "spec/tla/$m.cfg" "spec/tla/$m.tla" >"$tmp/$m.out" 2>&1
    if grep -q "$want is violated" "$tmp/$m.out"; then grep -m1 'is violated' "$tmp/$m.out"; else bad "tlc $m did not violate $want"; grep -m3 -E 'Error|violated' "$tmp/$m.out"; fi
  done <<'EOF'
UC2_buggy ConfirmedBeforeDue
UC2_buggy_m4 NoOversell
UC2_buggy_m5 Conservation
UC2_buggy_m5a NonNegativeAvailable
UC2_buggy_m7 UniqueIdsKnownSku
EOF
fi
[ "$fail" = 0 ] && echo "ALL UC2 STOCK CHECKS PASS" || echo "UC2 STOCK CHECKS FAILED"
exit "$fail"

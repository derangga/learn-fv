#!/usr/bin/env bash
# Soundness probes: every PROOF.bend states a false law, so the gate must reject it.
# Each dir's EXPECT holds substrings (one per line) of the first error that show the attack itself was refused.
# PASS = SOME PROOFS FAIL and every EXPECT line appear. Anything else is FAIL (a parse error is "wrong reason").
cd "$(dirname "$0")" || exit 2
bad=0
for d in */; do
  d=${d%/}; v=
  out=$(bend "$d/PROOF.bend" 2>&1); rc=$?
  if [ ! -s "$d/EXPECT" ]; then v="FAIL no EXPECT file"
  elif grep -q 'ALL PROOFS CHECK' <<<"$out"; then v="FAIL accepted a false law"
  elif ! grep -q 'SOME PROOFS FAIL' <<<"$out"; then v="FAIL no verdict (rc=$rc): $(head -n1 <<<"$out")"
  else
    while IFS= read -r want; do
      grep -qF -- "$want" <<<"$out" || { v="FAIL wrong reason (missing '$want'): $(sed -n '2,3p' <<<"$out" | tr '\n' ' ')"; break; }
    done < "$d/EXPECT"
    : "${v:=PASS rejected as expected}"
  fi
  case $v in PASS*) ;; *) bad=1;; esac
  printf '%-22s %s\n' "$d" "$v"
done
exit $bad

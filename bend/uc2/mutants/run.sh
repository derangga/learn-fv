#!/usr/bin/env bash
# UC2 Bend mutants: every <mid>/PROOF.bend must be rejected by the gate for the expected reason.
# Each dir holds copies of spec.bend, code.bend (mutated), LAWS.bend and PROOF.bend. LAWS.bend must be
# byte-identical to ../LAWS.bend in every dir; DIFFERS lists the other files that may differ from ../*.bend
# (all other files must be identical), so every deviation from the approved files is explicit.
# EXPECT holds substrings (one per line) of the first error, naming the lemma the gate rejects.
# PASS = files as declared, SOME PROOFS FAIL, and every EXPECT line appears.
cd "$(dirname "$0")" || exit 2
bad=0
for d in */; do
  d=${d%/}; v=
  for f in spec code LAWS PROOF; do
    if cmp -s "$d/$f.bend" "../$f.bend"; then same=1; else same=0; fi
    if grep -qx "$f.bend" "$d/DIFFERS" 2>/dev/null; then want=0; else want=1; fi
    [ "$f" = LAWS ] && want=1
    [ "$same" = "$want" ] || v="FAIL $f.bend: identical=$same but DIFFERS says identical=$want"
  done
  if [ -z "$v" ]; then
    out=$(bend "$d/PROOF.bend" 2>&1); rc=$?
    if [ ! -s "$d/EXPECT" ]; then v="FAIL no EXPECT file"
    elif grep -q 'ALL PROOFS CHECK' <<<"$out"; then v="FAIL accepted a mutant"
    elif ! grep -q 'SOME PROOFS FAIL' <<<"$out"; then v="FAIL no verdict (rc=$rc): $(head -n1 <<<"$out")"
    else
      while IFS= read -r want; do
        grep -qF -- "$want" <<<"$out" || { v="FAIL wrong reason (missing '$want'): $(sed -n '2,3p' <<<"$out" | tr '\n' ' ')"; break; }
      done < "$d/EXPECT"
      : "${v:=PASS rejected as expected ($(head -n1 "$d/EXPECT"))}"
    fi
  fi
  case $v in PASS*) ;; *) bad=1;; esac
  printf '%-6s %s\n' "$d" "$v"
done
exit $bad

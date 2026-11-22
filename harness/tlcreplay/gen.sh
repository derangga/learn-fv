#!/usr/bin/env bash
# Regenerate harness/tlcreplay/testdata/ from TLC counterexamples.
#   source .nix/env.sh && go generate ./harness/tlcreplay
# For every spec/tla/UC1_reach_*.cfg (module UC1) and spec/tla/UC1_buggy*.cfg
# (module = cfg stem) TLC runs with `-dumpTrace json`; the trace goes to
# testdata/<reach_X|buggy_X>.json and TLC's "Error: ... is violated." line to
# testdata/<same>.violation. TLC exits 12 (invariant) or 13 (action property) on a violation, which is expected.
# Needs tlc on PATH. Takes about 5 s per cfg. Scratch files go in $TMPDIR.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
out="$here/testdata"
tmp=${TMPDIR:-/tmp}/tlcreplay-gen
mkdir -p "$out" "$tmp"
cd "$root"
for cfg in spec/tla/UC1_reach_*.cfg spec/tla/UC1_buggy*.cfg; do
  stem=$(basename "$cfg" .cfg)
  case $stem in
    UC1_reach_*) name=reach_${stem#UC1_reach_}; mod=UC1 ;;
    UC1_buggy)   name=buggy; mod=$stem ;;
    UC1_buggy_*) name=buggy_${stem#UC1_buggy_}; mod=$stem ;;
  esac
  echo "== $name"
  rc=0
  tlc -noGenerateSpecTE -workers 1 -metadir "$tmp/$name" -dumpTrace json "$out/$name.json" \
      -config "$cfg" "spec/tla/$mod.tla" >"$tmp/$name.out" 2>&1 || rc=$?
  if [ "$rc" -ne 12 ] && [ "$rc" -ne 13 ]; then echo "FAIL: $name: tlc exit $rc" >&2; cat "$tmp/$name.out" >&2; exit 1; fi
  grep -m1 -E '^Error: .* is violated' "$tmp/$name.out" >"$out/$name.violation"
done
echo "gen: $(ls "$out"/*.json | wc -l) traces"

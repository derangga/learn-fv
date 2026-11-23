# Assumes the caller already ran `source .nix/env.sh` (go, tlc, bend, just on PATH).
set shell := ["bash", "-euo", "pipefail", "-c"]

default:
    @just --list

# Everything: unit tests, TLC (good then buggy), Bend proofs, harness.
all: test check-tla check-tla-buggy prove-bend harness

test:
    #!/usr/bin/env bash
    set -euo pipefail
    if [ -z "$(find . -name '*.go' -not -path './.git/*' -print -quit)" ]; then echo "no .go files yet; skipping"; exit 0; fi
    go test ./...

# TLC on every cfg except *_buggy*, *_reach*, *_wall* and *_proposed* ones; the module is the cfg's stem.
check-tla:
    #!/usr/bin/env bash
    set -euo pipefail
    tmp=${TMPDIR:-/tmp}
    n=0
    for cfg in spec/tla/*.cfg; do
      [ -e "$cfg" ] || continue
      name=$(basename "$cfg" .cfg)
      case $name in *_buggy*|*_reach*|*_wall*|*_proposed*) continue;; esac
      [ -f "spec/tla/$name.tla" ] || { echo "error: $cfg has no spec/tla/$name.tla" >&2; exit 1; }
      echo "== tlc $name"
      tlc -noGenerateSpecTE -workers auto -metadir "$tmp/tlc-$name" -config "$cfg" "spec/tla/$name.tla"
      n=$((n+1))
    done
    echo "check-tla: $n spec(s) passed"

# Every *_buggy* cfg must produce a counterexample (TLC exits nonzero); fail if one passes.
check-tla-buggy:
    #!/usr/bin/env bash
    set -euo pipefail
    tmp=${TMPDIR:-/tmp}
    n=0
    for cfg in spec/tla/*_buggy*.cfg; do
      [ -e "$cfg" ] || continue
      name=$(basename "$cfg" .cfg)
      [ -f "spec/tla/$name.tla" ] || { echo "error: $cfg has no spec/tla/$name.tla" >&2; exit 1; }
      echo "== tlc (expect violation) $name"
      rc=0
      tlc -noGenerateSpecTE -metadir "$tmp/tlc-$name" -config "$cfg" "spec/tla/$name.tla" >"$tmp/tlc-$name.out" 2>&1 || rc=$?
      if [ "$rc" -eq 0 ]; then
        echo "FAIL: $name passed but must produce a counterexample" >&2
        exit 1
      fi
      if ! grep -m1 -E 'is violated|Temporal properties were violated' "$tmp/tlc-$name.out"; then
        echo "FAIL: $name exited $rc without a violation (parse error or bad config?)" >&2
        cat "$tmp/tlc-$name.out" >&2
        exit 1
      fi
      n=$((n+1))
    done
    echo "check-tla-buggy: $n buggy spec(s) rejected as expected"

# Each bend/uc*/PROOF.bend and bend/smoke/PROOF.bend must print ALL PROOFS CHECK; then the soundness probes.
prove-bend:
    #!/usr/bin/env bash
    set -euo pipefail
    n=0
    for f in bend/smoke/PROOF.bend bend/uc*/PROOF.bend; do
      [ -e "$f" ] || continue
      echo "== bend $f"
      rc=0
      out=$(bend "$f" 2>&1) || rc=$?
      if [ "$rc" -eq 0 ] && grep -q 'ALL PROOFS CHECK' <<<"$out"; then
        echo "ALL PROOFS CHECK"
      else
        echo "FAIL: $f (bend exit $rc)" >&2; echo "$out" >&2; exit 1
      fi
      n=$((n+1))
    done
    echo "prove-bend: $n proof file(s) checked"
    bash bend/probes/run.sh
    for m in bend/uc*/mutants/run.sh; do
      [ -e "$m" ] || continue
      echo "== $m"
      bash "$m"
    done

harness:
    #!/usr/bin/env bash
    set -euo pipefail
    if [ ! -d harness ]; then echo "harness/ does not exist yet; skipping"; exit 0; fi
    go test ./harness/...

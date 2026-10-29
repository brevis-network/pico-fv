#!/usr/bin/env bash
# Checks the top-level theorems in theorems.txt: each must exist, depend only on Lean's core
# axioms or the RISC-V spec's declared axioms in spec-axioms.txt (so no sorryAx), and keep the
# axioms and statement recorded in axioms.txt and signatures.txt. Run after `lake build`.
#   scripts/fv-check/check.sh            check; exit 1 on any violation or drift
#   scripts/fv-check/check.sh --update   after a clean check of the rules, rewrite the snapshots
set -euo pipefail

cd "$(dirname "$0")/../.."
dir=scripts/fv-check
core='^(propext|Classical\.choice|Quot\.sound|Lean\.ofReduceBool|Lean\.trustCompiler)$'

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
if ! lake env lean "$dir/Report.lean" > "$tmp/report"; then
  cat "$tmp/report"
  echo "Report.lean failed; is PicoFV64 built?"
  exit 1
fi

status=0
expected=$(grep -c . "$dir/theorems.txt" || true)
found=$(grep -c '^AXIOMS ' "$tmp/report" || true)
if grep '^MISSING ' "$tmp/report"; then status=1; fi

{ grep '^AXIOMS ' "$tmp/report" || true; } | cut -d' ' -f2- | sort > "$tmp/axioms.txt"
{ grep '^SIGNATURE ' "$tmp/report" || true; } | cut -d' ' -f2- | sort > "$tmp/signatures.txt"
while read -r name axs; do
  for ax in ${axs//,/ }; do
    if ! [[ $ax =~ $core ]] && ! grep -qxF "$ax" "$dir/spec-axioms.txt"; then
      echo "AXIOM VIOLATION: $name depends on $ax"
      status=1
    fi
  done
done < "$tmp/axioms.txt"

if [[ ${1:-} == --update ]]; then
  if [[ $status != 0 ]]; then
    echo "not updating the snapshots: fix the violations above first"
    exit 1
  fi
  cp "$tmp/axioms.txt" "$tmp/signatures.txt" "$dir/"
  echo "updated $dir/axioms.txt and $dir/signatures.txt"
else
  for snapshot in axioms signatures; do
    if ! diff -u "$dir/$snapshot.txt" "$tmp/$snapshot.txt"; then
      echo "DRIFT in $snapshot.txt: review the change above, then rerun with --update"
      status=1
    fi
  done
fi

echo "checked $found of $expected theorems: $([[ $status == 0 ]] && echo OK || echo FAILED)"
exit $status

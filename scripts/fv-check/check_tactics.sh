#!/usr/bin/env bash
# Ratchet on tactics that trust compiled code (`native_decide`, `bv_decide`, `decide +native`):
# no file may use them more often than tactic-baseline.txt records. Lowering a count is welcome;
# record it with --update, which refuses to raise any count. --against <ref> also fails if the
# committed baseline raises a count over the one at <ref> (CI passes the pull request's base).
#   scripts/fv-check/check_tactics.sh                 check
#   scripts/fv-check/check_tactics.sh --update        rewrite the baseline after removing uses
#   scripts/fv-check/check_tactics.sh --against REF   check, and compare the baseline with REF's
set -euo pipefail

cd "$(dirname "$0")/../.."
baseline=scripts/fv-check/tactic-baseline.txt
pattern='\b(native_decide|bv_decide|decide \+native)\b'

# "count path" for every file that uses the tactics, counting each use outside line comments.
current() {
  grep -rnE --include='*.lean' "$pattern" PicoFV | grep -vE '^[^:]+:[0-9]+:[[:space:]]*--' \
    | while IFS=: read -r file _ text; do
        grep -oE "$pattern" <<< "$text" | sed "s|.*|$file|"
      done | sort | uniq -c | awk '{ print $1, $2 }'
}

# Fails for every path whose count in $1 exceeds the one in $2 ("count path" lines).
exceeds() {
  local status=0
  while read -r n path; do
    allowed=$(awk -v p="$path" '$2 == p { print $1 }' "$2")
    if (( n > ${allowed:-0} )); then
      echo "TACTIC RATCHET: $path has $n uses of native_decide/bv_decide/decide +native ($3 ${allowed:-0})"
      status=1
    fi
  done < "$1"
  return $status
}

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
current > "$tmp/current"

status=0
exceeds "$tmp/current" "$baseline" "baseline" || status=1

case ${1:-} in
  --update)
    if [[ $status != 0 ]]; then
      echo "not updating: the baseline only goes down"
      exit 1
    fi
    cp "$tmp/current" "$baseline"
    echo "updated $baseline"
    ;;
  --against)
    # A base without a baseline (the commit that introduces this check) has nothing to compare.
    if git show "$2:$baseline" > "$tmp/base" 2>/dev/null; then
      exceeds "$baseline" "$tmp/base" "at $2" || status=1
    fi
    ;;
esac

total=$(awk '{ s += $1 } END { print s + 0 }' "$tmp/current")
echo "compiled-code tactic uses: $total ($([[ $status == 0 ]] && echo OK || echo FAILED))"
exit $status

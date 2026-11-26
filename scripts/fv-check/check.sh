#!/usr/bin/env bash
# Checks the top-level theorems listed in theorems.d/*.txt: each must exist, depend only on Lean's core
# axioms or the RISC-V spec's declared axioms in spec-axioms.txt (so no sorryAx), and keep the
# axioms and statement recorded in axioms.txt and signatures.txt. Run after `lake build`.
# It also checks the definitions those statements reach (in this repository, following definition
# bodies): each keeps the fingerprint recorded in definitions.txt, so a changed definition fails
# the check until it is reviewed, even when no statement's text changes. A fingerprint does not
# depend on this repository's names, so a rename listed in definition-renames.txt is not drift.
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
expected=$(cat "$dir"/theorems.d/*.txt | grep -c . || true)
found=$(grep -c '^AXIOMS ' "$tmp/report" || true)
if grep '^MISSING ' "$tmp/report"; then status=1; fi
if grep '^DEFINITION-ERROR ' "$tmp/report"; then status=1; fi

# Byte order, whatever the locale: a UTF-8 locale's collation ignores case and punctuation on its
# first pass, so a plain `sort` orders the snapshots differently on a default macOS shell than on CI.
{ grep '^AXIOMS ' "$tmp/report" || true; } | cut -d' ' -f2- | LC_ALL=C sort > "$tmp/axioms.txt"
{ grep '^SIGNATURE ' "$tmp/report" || true; } | cut -d' ' -f2- | LC_ALL=C sort > "$tmp/signatures.txt"
{ grep '^DEFINITION ' "$tmp/report" || true; } | cut -d' ' -f2- | LC_ALL=C sort > "$tmp/definitions.txt"
defs=$(grep -c . "$tmp/definitions.txt" || true)
while read -r name axs; do
  for ax in ${axs//,/ }; do
    if ! [[ $ax =~ $core ]] && ! grep -qxF "$ax" "$dir/spec-axioms.txt"; then
      echo "AXIOM VIOLATION: $name depends on $ax"
      status=1
    fi
  done
done < "$tmp/axioms.txt"

# Compares definitions.txt (committed) with the new one. A name in both must keep its fingerprint.
# A name that left the file is looked up under the rename map in the new file: an equal fingerprint
# is a rename, a different one is drift named under both names. Names that are only removed or only
# added are reported too, since the set of reached definitions changed.
compare_definitions() {
  awk -v mapfile="$dir/definition-renames.txt" '
    function rename(name,   i, k, from, to, at, rest, before, after) {
      for (i = 1; i <= nmap; i++) {
        from = mfrom[i]; to = mto[i]; rest = name; at = 0
        while ((k = index(rest, from)) > 0) {
          before = (at + k == 1) ? "." : substr(name, at + k - 1, 1)
          after = substr(name, at + k + length(from), 1)
          if (before == "." && (after == "." || after == "")) {
            name = substr(name, 1, at + k - 1) to substr(name, at + k + length(from))
            break
          }
          at += k; rest = substr(name, at + 1)
        }
      }
      return name
    }
    BEGIN {
      while ((getline line < mapfile) > 0) {
        sub(/#.*/, "", line)
        if (split(line, f, " ") == 2) { nmap++; mfrom[nmap] = f[1]; mto[nmap] = f[2] }
      }
    }
    FILENAME == ARGV[1] { old[$1] = $2; next }
    { new[$1] = $2 }
    END {
      bad = 0
      for (n in old) {
        if (n in new) {
          if (old[n] != new[n]) { print "DEFINITION DRIFT: " n; bad = 1 }
          continue
        }
        m = rename(n)
        if (m != n && (m in new)) {
          paired[m] = 1
          if (old[n] == new[m]) print "renamed, no drift: " n " -> " m
          else { print "DEFINITION DRIFT: " n " (now " m ")"; bad = 1 }
        } else { print "DEFINITION GONE: " n; bad = 1 }
      }
      for (m in new) if (!(m in old) && !(m in paired)) { print "DEFINITION NEW: " m; bad = 1 }
      exit bad
    }' "$dir/definitions.txt" "$tmp/definitions.txt" | LC_ALL=C sort
  return "${PIPESTATUS[0]}"
}

if [[ ${1:-} == --update ]]; then
  if [[ $status != 0 ]]; then
    echo "not updating the snapshots: fix the violations above first"
    exit 1
  fi
  cp "$tmp/axioms.txt" "$tmp/signatures.txt" "$tmp/definitions.txt" "$dir/"
  echo "updated $dir/axioms.txt, $dir/signatures.txt and $dir/definitions.txt"
else
  for snapshot in axioms signatures; do
    if ! diff -u "$dir/$snapshot.txt" "$tmp/$snapshot.txt"; then
      echo "DRIFT in $snapshot.txt: review the change above, then rerun with --update"
      status=1
    fi
  done
  if ! compare_definitions; then
    echo "DRIFT in definitions.txt: review each definition named above (a change also shows on every"
    echo "definition that uses it), then rerun with --update"
    status=1
  fi
fi

echo "checked $found of $expected theorems and $defs definitions: $([[ $status == 0 ]] && echo OK || echo FAILED)"
exit $status

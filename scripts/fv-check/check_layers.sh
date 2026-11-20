#!/usr/bin/env bash
# Keeps the chips independent. A chip's Airs/Constraints/Spec files may import the shared layers
# (Fundamentals, RVSail, Transpiler), the extraction of that chip, gadgets, and the chip's own
# files, but never another chip. A gadget may import only the shared layers and other gadgets.
# Equivalence may import only the CPU chip, RVSail and its own files.
set -euo pipefail

cd "$(dirname "$0")/../.."
status=0

# Chip name of a module: its last component without a trailing helper suffix.
chip() { local n=${1##*.}; n=${n%Interpretations}; n=${n%Core}; echo "$n"; }
shared() { [[ $1 =~ ^PicoFV\.(Fundamentals|RV64IM\.(RVSail|Transpiler))\. ]]; }
gadget() { [[ ${1##*.} =~ Gadget|^SubAirs$|^Attributes$ ]]; }

# Every module a file imports, whatever the modifiers or the number of modules on a line.
imports() {
  sed -nE 's/^[[:space:]]*((public|private|meta)[[:space:]]+)*import[[:space:]]+//p' "$1" \
    | sed 's/--.*//' | tr -s ' \t' '\n' | grep '^PicoFV\.' || true
}

violation() { echo "LAYER VIOLATION: $1 imports $2 ($3)"; status=1; }

for f in PicoFV/RV64IM/{Airs,Constraints,Spec}/*.lean; do
  me=$(chip "$(basename "$f" .lean)")
  while read -r dep; do
    [[ -z $dep ]] && continue
    if shared "$dep" || gadget "$dep"; then continue; fi
    if gadget "$me"; then
      violation "$f" "$dep" "a gadget may use only shared layers and gadgets"
    elif [[ $(chip "$dep") != "$me" ]]; then
      violation "$f" "$dep" "another chip"
    fi
  done < <(imports "$f")
done

for f in PicoFV/RV64IM/Equivalence/*.lean; do
  while read -r dep; do
    [[ -z $dep ]] && continue
    if shared "$dep" || [[ $dep =~ ^PicoFV\.RV64IM\.(Equivalence\.|Constraints\.CpuChip) ]]; then
      continue
    fi
    violation "$f" "$dep" "Equivalence may use only the CPU chip"
  done < <(imports "$f")
done

[[ $status == 0 ]] && echo "layers: OK"
exit $status

#!/usr/bin/env bash
# Builds one stage of the CI build: every module under the given directories, or the given
# targets. The stage's modules listed in heavy-modules.txt build first, one at a time. Sets the
# step output `built` to whether Lake built anything, so that an up-to-date stage saves no
# cache entry.
#   scripts/ci/build_stage.sh PicoFV/RV64IM/Spec      every module under the directory
#   scripts/ci/build_stage.sh PicoFV64                a Lake target
set -euo pipefail
cd "$(dirname "$0")/../.."
targets=()
for arg in "$@"; do
  if [[ -d $arg ]]; then
    while IFS= read -r f; do
      f=${f%.lean}
      targets+=("${f//\//.}")
    done < <(find "$arg" -name '*.lean' | sort)
  else
    targets+=("$arg")
  fi
done
log=$(mktemp)
status=0
while read -r heavy; do
  if [[ $status == 0 ]] && printf '%s\n' "${targets[@]}" | grep -qxF "$heavy"; then
    echo "building $heavy alone"
    lake build "$heavy" 2>&1 | tee -a "$log" || status=$?
  fi
done < <(grep -v '^#' scripts/ci/heavy-modules.txt)
if [[ $status == 0 ]]; then
  lake build "${targets[@]}" 2>&1 | tee -a "$log" || status=$?
fi
built=false
if grep -q ' Built ' "$log"; then built=true; fi
echo "built=$built" >> "${GITHUB_OUTPUT:-/dev/null}"
exit $status

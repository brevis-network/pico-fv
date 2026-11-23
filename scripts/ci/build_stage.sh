#!/usr/bin/env bash
# Builds one stage of the CI build: every module under the given directories, or the given
# targets. With --alone, each target builds in a Lake run of its own, so no other module
# compiles beside it. Sets the step output `built` to whether Lake built anything, so that an
# up-to-date stage saves no cache entry.
#   scripts/ci/build_stage.sh PicoFV/RV64IM/Spec           every module under the directory
#   scripts/ci/build_stage.sh PicoFV64                     a Lake target
#   scripts/ci/build_stage.sh --alone PicoFV.Fundamentals.Word ...
set -euo pipefail
cd "$(dirname "$0")/../.."
alone=false
if [[ ${1:-} == --alone ]]; then
  alone=true
  shift
fi
targets=()
for arg in "$@"; do
  arg=${arg%/}
  if [[ -z $arg ]]; then
    echo "empty target"
    exit 1
  elif [[ -d $arg ]]; then
    while IFS= read -r f; do
      f=${f%.lean}
      targets+=("${f//\//.}")
    done < <(find "$arg" -name '*.lean' | sort)
  elif [[ $arg == */* ]]; then
    echo "no such directory: $arg"
    exit 1
  elif [[ $arg == *.* && ! -f ${arg//.//}.lean ]]; then
    echo "no such module: $arg"
    exit 1
  else
    targets+=("$arg")
  fi
done
if [[ ${#targets[@]} == 0 ]]; then
  echo "no targets"
  exit 1
fi
log=$(mktemp)
trap 'rm -f "$log"' EXIT
status=0
if $alone; then
  for t in "${targets[@]}"; do
    lake build "$t" 2>&1 | tee -a "$log" || { status=$?; break; }
  done
else
  lake build "${targets[@]}" 2>&1 | tee -a "$log" || status=$?
fi
built=false
if grep -q ' Built ' "$log"; then built=true; fi
echo "built=$built" >> "${GITHUB_OUTPUT:-/dev/null}"
exit $status

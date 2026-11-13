#!/usr/bin/env bash
# Installs a pinned elan release, checking the archive's digest, for CI on x86_64 Linux. elan then
# installs the toolchain `lean-toolchain` names. Pinned rather than "latest", whose redirect can fail.
set -euo pipefail

version="v4.2.4"
target="x86_64-unknown-linux-gnu"
digest="42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63"

work_dir="$(mktemp -d)"
trap 'rm -rf "$work_dir"' EXIT
archive="$work_dir/elan.tar.gz"
curl -sSfL --retry 5 --retry-all-errors -o "$archive" \
  "https://github.com/leanprover/elan/releases/download/$version/elan-$target.tar.gz"
echo "$digest  $archive" | sha256sum -c -

tar -xzf "$archive" -C "$work_dir"
"$work_dir/elan-init" -y --default-toolchain none --no-modify-path
echo "$HOME/.elan/bin" >> "${GITHUB_PATH:-/dev/null}"

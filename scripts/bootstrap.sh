#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

# This commit is not necessarily reachable from the upstream default branch.
# Fetch it explicitly before Lake resolves the pinned package and its subdirectory.
package_dir=.lake/packages/PercolationContinuity
revision=795efb86f191735c5481675763537cfb4ff37e55
if [[ ! -e "$package_dir" ]]; then
  mkdir -p "$package_dir"
  git -C "$package_dir" init -q
  git -C "$package_dir" remote add origin https://github.com/anthropics/formal-math
fi
if ! git -C "$package_dir" cat-file -e "$revision^{commit}" 2>/dev/null; then
  git -C "$package_dir" fetch origin "$revision"
fi
if [[ "$(git -C "$package_dir" rev-parse --verify HEAD 2>/dev/null || true)" != "$revision" ]]; then
  git -C "$package_dir" checkout --detach "$revision"
fi
lake exe cache get
lake build

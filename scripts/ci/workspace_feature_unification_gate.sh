#!/usr/bin/env bash
# ay-script: workspace-feature-unification-gate
#
# Fresh-target regression for workspace feature unification. The main `ay`
# binary enables ay-sys's mimalloc arena trim, while `ay-pb` deliberately uses
# the system allocator. Cargo unifies that feature when both roots are selected;
# both binaries must still link from one invocation.

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"
TARGET_DIR="$(mktemp -d "${TMPDIR:-/tmp}/ay-feature-unification.XXXXXX")"
trap 'rm -rf "$TARGET_DIR"' EXIT

cd "$REPO_ROOT"
CARGO_BUILD_JOBS="${CARGO_BUILD_JOBS:-2}" \
    cargo build --locked --release --target-dir "$TARGET_DIR" \
    -p ay -p ay-pb --features ay/cli

test -x "$TARGET_DIR/release/ay"
test -x "$TARGET_DIR/release/ay-pb"

echo "workspace feature-unification gate: PASS"

#!/usr/bin/env bash
# ay-script: doc-reality-gate
# Documentation-reality gate. Keep the shell entrypoint stable for release
# tooling while the checked implementation lives in the Rust quality-gate
# crate.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${REPO_ROOT}"

exec cargo run --locked --quiet -p ay-quality-gate --bin ay-doc-reality -- \
    --repo-root "${REPO_ROOT}" \
    README.md \
    the development design notes \
    the development design notes

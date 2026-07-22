#!/usr/bin/env bash
# ay-script: public-clone-check
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0
#
# public-clone-check.sh — unauthenticated public-clone build evidence.
#
# Simulates what a fresh, unauthenticated clone of the public AY repository sees:
# a clean checkout at a given ref must resolve dependencies with the committed
# Cargo.lock (`--locked`) and build the release `ay` binary from source. Emits a
# machine-checkable log consumed by `ay z3-audit` (see crates/ay/src/cmd_z3_audit.rs
# public_clone_log_passes / public_source_build_evidence) plus per-step provenance
# files.
#
# This is an honest local approximation: it clones the working repository to a
# scratch directory and builds there with --locked, reusing the shared cargo
# registry cache (the same artifacts crates.io would serve). It does NOT fake any
# step — PASS lines are emitted only when the underlying command actually succeeds.
#
# Usage:
#   scripts/public-clone-check.sh [--ref <commit>] [--metadata-only]
#                                 [--repo <path-or-url>] [--output <log>]
#
#   --ref <commit>     Commit/ref to check out in the fresh clone (default: HEAD).
#   --metadata-only    Only run `cargo metadata --no-deps --locked` (skip the
#                      release build).
#   --repo <path|url>  Source to clone (default: this repository's root).
#   --output <log>     Log path (default:
#                      target/public-clone-check/public-clone-check.log).
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PROVENANCE_DIR="${REPO_ROOT}/target/public-clone-check"

REF="HEAD"
METADATA_ONLY=0
REPO_SRC="${REPO_ROOT}"
OUTPUT=""

while [[ $# -gt 0 ]]; do
  case "$1" in
    --ref) REF="$2"; shift 2 ;;
    --metadata-only) METADATA_ONLY=1; shift ;;
    --repo) REPO_SRC="$2"; shift 2 ;;
    --output) OUTPUT="$2"; shift 2 ;;
    *) echo "unknown argument: $1" >&2; exit 2 ;;
  esac
done

COMMIT="$(git -C "${REPO_ROOT}" rev-parse "${REF}")"
mkdir -p "${PROVENANCE_DIR}"
[[ -z "${OUTPUT}" ]] && OUTPUT="${PROVENANCE_DIR}/public-clone-check.log"

WORK="$(mktemp -d "${TMPDIR:-/tmp}/ay-public-clone-XXXXXX")"
trap 'rm -rf "${WORK}"' EXIT
CLONE="${WORK}/clone"

LOG_LINES=()
OVERALL_OK=1
emit() { LOG_LINES+=("$1"); }

emit "public-clone-check: repo=${REPO_SRC}"
emit "public-clone-check: ref=${REF} commit=${COMMIT}"

# Fresh, unauthenticated checkout.
if git clone --quiet "${REPO_SRC}" "${CLONE}" 2>"${WORK}/clone.stderr" \
  && git -C "${CLONE}" checkout --quiet "${COMMIT}" 2>>"${WORK}/clone.stderr"; then
  emit "public-clone-check: PASS clone"
else
  emit "public-clone-check: FAIL clone"
  OVERALL_OK=0
fi

# Locked dependency resolution — must use the committed Cargo.lock unchanged.
# --no-deps keeps this a workspace-resolution check that does not fetch every
# dependency source.
if [[ "${OVERALL_OK}" -eq 1 ]]; then
  if cargo metadata --manifest-path "${CLONE}/Cargo.toml" --format-version 1 --no-deps --locked \
      >"${WORK}/metadata.json" 2>"${WORK}/metadata.stderr"; then
    emit "public-clone-check: PASS cargo_metadata_locked"
  else
    emit "public-clone-check: FAIL cargo_metadata_locked"
    OVERALL_OK=0
  fi
fi

# Locked release build of the CLI from source.
if [[ "${METADATA_ONLY}" -eq 1 ]]; then
  emit "public-clone-check: SKIP release_build (metadata-only)"
elif [[ "${OVERALL_OK}" -eq 1 ]]; then
  BUILD_CMD="cargo build --release --locked -p ay --features cli --bin ay"
  printf '%s\n' "${BUILD_CMD}" >"${PROVENANCE_DIR}/cargo-build-release.command.txt"
  if (cd "${CLONE}" && eval "${BUILD_CMD}") \
      >"${PROVENANCE_DIR}/cargo-build-release.stdout.txt" \
      2>"${PROVENANCE_DIR}/cargo-build-release.stderr.txt"; then
    emit "public-clone-check: PASS release_build"
  else
    emit "public-clone-check: FAIL release_build"
    OVERALL_OK=0
  fi

  if [[ "${OVERALL_OK}" -eq 1 ]] && [[ -x "${CLONE}/target/release/ay" ]]; then
    VERSION="$("${CLONE}/target/release/ay" --version 2>/dev/null | head -1 || true)"
    printf '%s\n' "${VERSION}" >"${PROVENANCE_DIR}/ay-version.txt"
    emit "public-clone-check: version ${VERSION}"
  else
    emit "public-clone-check: FAIL version"
    OVERALL_OK=0
  fi
fi

if [[ "${OVERALL_OK}" -eq 1 ]]; then
  emit "public-clone-check: overall PASS"
else
  emit "public-clone-check: overall FAIL"
fi

printf '%s\n' "${LOG_LINES[@]}" | tee "${OUTPUT}"
[[ "${OVERALL_OK}" -eq 1 ]]

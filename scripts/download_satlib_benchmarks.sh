#!/usr/bin/env bash
# ay-script: satlib-fetch
# download_satlib_benchmarks.sh — fetch the SATLIB uniform-random 3-SAT sets the
# ay-sat soundness / DRAT tests resolve.
#
# Source: SATLIB (Hoos & Stützle), www.cs.ubc.ca/~hoos/SATLIB, RND3SAT collection.
# Four sets, each 100 instances at the phase-transition ratio:
#   UF200.860.100  (sat,   200 vars / 860 clauses)   <- uf200-860.tar.gz
#   UUF200.860.100 (unsat, 200 vars / 860 clauses)   <- uuf200-860.tar.gz
#   UF250.1065.100 (sat,   250 vars / 1065 clauses)  <- uf250-1065.tar.gz
#   UUF250.1065.100(unsat, 250 vars / 1065 clauses)  <- uuf250-1065.tar.gz
#
# The tests resolve these under reference/creusat/tests/satlib/<SET>/ (the same
# gitignored reference/ tree the mfleury benchmarks live in; CreuSAT itself does
# not vendor the satlib set, so it is fetched here). The original SATLIB
# filenames (e.g. uf200-036.cnf, uuf250-01.cnf) are preserved.
#
# Usage: scripts/download_satlib_benchmarks.sh   # fetches all four sets
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
BASE_URL="https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/RND3SAT"
DEST_ROOT="$ROOT/reference/creusat/tests/satlib"

command -v curl >/dev/null 2>&1 || { echo "error: curl not found" >&2; exit 1; }
command -v tar  >/dev/null 2>&1 || { echo "error: tar not found"  >&2; exit 1; }

# tarball  ->  destination directory
sets=(
  "uf200-860:UF200.860.100"
  "uuf200-860:UUF200.860.100"
  "uf250-1065:UF250.1065.100"
  "uuf250-1065:UUF250.1065.100"
)

TMP="$(mktemp -d "${TMPDIR:-/tmp}/satlib.XXXXXX")"
trap 'rm -rf "$TMP"' EXIT

for entry in "${sets[@]}"; do
  tarball="${entry%%:*}"
  dir="${entry##*:}"
  dest="$DEST_ROOT/$dir"
  mkdir -p "$dest"
  echo "satlib[$dir]: downloading ${tarball}.tar.gz ..."
  if ! curl -fSL --retry 3 --max-time 600 "$BASE_URL/${tarball}.tar.gz" -o "$TMP/${tarball}.tar.gz"; then
    echo "error: download failed for ${tarball}.tar.gz (see ${BASE_URL})" >&2
    exit 1
  fi
  mkdir -p "$TMP/x_$tarball"
  tar -xzf "$TMP/${tarball}.tar.gz" -C "$TMP/x_$tarball"
  before="$(find "$dest" -name '*.cnf' 2>/dev/null | wc -l | tr -d ' ')"
  # The SATLIB tarballs nest the .cnf files under ai/hoos/...; flatten them into
  # the destination set directory, never clobbering an existing file.
  find "$TMP/x_$tarball" -name '*.cnf' -exec cp -n {} "$dest/" \;
  after="$(find "$dest" -name '*.cnf' 2>/dev/null | wc -l | tr -d ' ')"
  echo "satlib[$dir]: $dest now has ${after} .cnf (added $((after - before)))."
done

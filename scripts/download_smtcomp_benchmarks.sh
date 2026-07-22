#!/usr/bin/env bash
# ay-script: smtcomp-fetch
# download_smtcomp_benchmarks.sh — fetch SMT-LIB non-incremental benchmarks for a
# given logic into benchmarks/smtcomp/<LOGIC>/.
#
# Source: the SMT-LIB release 2024 (non-incremental benchmarks), Zenodo record
# 11061097 (https://zenodo.org/records/11061097), one `<LOGIC>.tar.zst` per logic.
#
# The per-logic archive is downloaded and every `*.smt2` it contains is placed,
# flattened, under benchmarks/smtcomp/<LOGIC>/ — the flat layout the soundness /
# model-validation tests resolve (e.g. benchmarks/smtcomp/QF_LRA/<file>.smt2).
# Already-present files (incl. the committed `.gitignore`-whitelisted ones) are
# never overwritten. The benchmarks/smtcomp/QF_*/ tree is gitignored (it is large
# and fetched on demand); only a couple of tiny representative files are vendored.
#
# Usage:
#   scripts/download_smtcomp_benchmarks.sh --logic QF_LRA
#   scripts/download_smtcomp_benchmarks.sh --logic QF_AUFLIA
#
#   --logic <L>      SMT-LIB logic to fetch (e.g. QF_LRA, QF_AUFLIA, QF_UF, QF_BV).
#   --skip-download  Do not fetch; just report what is already present (used by
#                    eval harnesses that pre-populate the corpus).
set -euo pipefail

ZENODO_RECORD="11061097"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

LOGIC=""
SKIP_DOWNLOAD=0

usage() { sed -n '2,30p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; }

while [ "$#" -gt 0 ]; do
  case "$1" in
    --logic) LOGIC="${2:-}"; shift 2 ;;
    --logic=*) LOGIC="${1#*=}"; shift ;;
    --skip-download) SKIP_DOWNLOAD=1; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "error: unknown argument '$1'" >&2; usage >&2; exit 2 ;;
  esac
done

[ -n "$LOGIC" ] || { echo "error: --logic <LOGIC> is required (e.g. QF_LRA)" >&2; exit 2; }

DEST="$ROOT/benchmarks/smtcomp/$LOGIC"
mkdir -p "$DEST"

if [ "$SKIP_DOWNLOAD" -eq 1 ]; then
  echo "smtcomp[$LOGIC]: --skip-download; $(find "$DEST" -name '*.smt2' 2>/dev/null | wc -l | tr -d ' ') .smt2 present at $DEST"
  exit 0
fi

for tool in curl tar zstd; do
  command -v "$tool" >/dev/null 2>&1 || { echo "error: required tool '$tool' not found on PATH" >&2; exit 1; }
done

URL="https://zenodo.org/api/records/${ZENODO_RECORD}/files/${LOGIC}.tar.zst/content"
TMP="$(mktemp -d "${TMPDIR:-/tmp}/smtcomp-${LOGIC}.XXXXXX")"
trap 'rm -rf "$TMP"' EXIT

echo "smtcomp[$LOGIC]: downloading ${LOGIC}.tar.zst from Zenodo ${ZENODO_RECORD} ..."
if ! curl -fSL --retry 3 --max-time 1800 "$URL" -o "$TMP/${LOGIC}.tar.zst"; then
  echo "error: download failed (logic '$LOGIC' may not exist in Zenodo ${ZENODO_RECORD}); see https://zenodo.org/records/${ZENODO_RECORD}" >&2
  exit 1
fi

echo "smtcomp[$LOGIC]: extracting ..."
mkdir -p "$TMP/x"
zstd -dc "$TMP/${LOGIC}.tar.zst" | tar -xf - -C "$TMP/x"

# Flatten every *.smt2 into benchmarks/smtcomp/<LOGIC>/, never clobbering an
# existing (e.g. vendored) file. This is the flat layout the QF_LRA / QF_AUFLIA
# soundness tests resolve.
before="$(find "$DEST" -name '*.smt2' 2>/dev/null | wc -l | tr -d ' ')"
find "$TMP/x" -name '*.smt2' -exec cp -n {} "$DEST/" \;
after="$(find "$DEST" -name '*.smt2' 2>/dev/null | wc -l | tr -d ' ')"

# Also mirror the archive's native nested layout under benchmarks/smtcomp/ (e.g.
# non-incremental/<LOGIC>/<family>/<file>.smt2) — the path other tests resolve
# directly (ay-dpll QF_UF eq_diamond, etc.). Re-extract straight into place with
# -k (keep existing files) so the `non-incremental/` prefix is preserved.
zstd -dc "$TMP/${LOGIC}.tar.zst" | tar -xkf - -C "$ROOT/benchmarks/smtcomp/" 2>/dev/null || true

echo "smtcomp[$LOGIC]: done. $DEST now has ${after} .smt2 (added $((after - before))); nested layout mirrored under benchmarks/smtcomp/."

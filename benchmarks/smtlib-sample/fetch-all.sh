#!/bin/bash
# ay-script: smtlib-sample-fetch-all
# Fetch a deterministic sample of EVERY SMT-LIB 2024 division into a corpus
# tree, for `ay-z3-parity scoreboard` to track AY-vs-z3 across all logics.
#
# Source: SMT-LIB release 2024 (non-incremental), Zenodo record 11061097.
# Unlike fetch.sh (5 pinned divisions, N=300), this discovers ALL divisions
# from the Zenodo API and verifies each archive against the API-published md5.
#
# Config (env):
#   AY_SAMPLE_N     files sampled per division (default 500; "all" = every file)
#   AY_MAX_MB       skip archives larger than this many MB (default 60; the
#                   giants QF_BV 1.7GB / QF_LIA 689MB / QF_IDL 428MB / AUFBV
#                   256MB etc. are excluded unless you raise this)
#   AY_DEST         corpus root (default: a sibling `smtlib-all` dir)
#   AY_ONLY         space-separated division allowlist (default: all discovered)
#
# Deterministic sampling: list every *.smt2 path, LC_ALL=C sort, take N evenly
# spaced at floor(i*total/N). Same rule as fetch.sh, so it is auditable.
#
# Requires: curl, unzstd (zstd), tar, python3, md5(macOS)/md5sum.
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
N="${AY_SAMPLE_N:-500}"
MAX_MB="${AY_MAX_MB:-60}"
DEST="${AY_DEST:-$(cd "$HERE/.." && pwd)/smtlib-all}"
ONLY="${AY_ONLY:-}"
API="https://zenodo.org/api/records/11061097"

md5_of() { if command -v md5 >/dev/null 2>&1; then md5 -q "$1"; else md5sum "$1" | cut -d' ' -f1; fi; }

mkdir -p "$DEST"
echo "== discovering divisions from Zenodo (max ${MAX_MB}MB each, N=${N}/division) ..."
MANIFEST="$(mktemp)"; trap 'rm -f "$MANIFEST"' EXIT
curl -fSL --retry 3 --max-time 120 "$API" \
  | python3 -c "
import sys, json
d = json.load(sys.stdin)
for f in d.get('files', []):
    key = f['key']
    if not key.endswith('.tar.zst'): continue
    div = key[:-len('.tar.zst')]
    size = f.get('size', 0)
    md5 = (f.get('checksum','') or '').replace('md5:','')
    print(div, size, md5)
" > "$MANIFEST"

TOTAL_DIVS=0; DONE_DIVS=0; SKIPPED=0
while read -r DIV SIZE MD5; do
  [ -n "$DIV" ] || continue
  if [ -n "$ONLY" ] && ! grep -qw "$DIV" <<<"$ONLY"; then continue; fi
  TOTAL_DIVS=$((TOTAL_DIVS+1))
  SIZE_MB=$(( SIZE / 1000000 ))
  if [ "$SIZE_MB" -gt "$MAX_MB" ]; then
    echo "-- $DIV: ${SIZE_MB}MB > ${MAX_MB}MB cap — skipped (raise AY_MAX_MB to include)"
    SKIPPED=$((SKIPPED+1)); continue
  fi
  TMP="$(mktemp -d "${TMPDIR:-/tmp}/smtlib-$DIV.XXXXXX")"
  AR="$TMP/$DIV.tar.zst"
  echo "== $DIV (${SIZE_MB}MB): downloading ..."
  if ! curl -fSL --retry 3 --max-time 1800 "$API/files/$DIV.tar.zst/content" -o "$AR"; then
    echo "   download failed — skipping $DIV"; rm -rf "$TMP"; continue
  fi
  GOT="$(md5_of "$AR")"
  if [ -n "$MD5" ] && [ "$GOT" != "$MD5" ]; then
    echo "   md5 mismatch (got $GOT want $MD5) — skipping $DIV"; rm -rf "$TMP"; continue
  fi
  XD="$TMP/x"; mkdir -p "$XD"
  if ! tar --use-compress-program=unzstd -xf "$AR" -C "$XD" 2>/dev/null; then
    echo "   extract failed — skipping $DIV"; rm -rf "$TMP"; continue
  fi
  ( cd "$XD" && find . -name '*.smt2' | sed 's|^\./||' | LC_ALL=C sort ) > "$TMP/list"
  CNT="$(wc -l < "$TMP/list" | tr -d ' ')"
  [ "$CNT" -gt 0 ] || { echo "   no .smt2 in $DIV — skipping"; rm -rf "$TMP"; continue; }
  mkdir -p "$DEST/$DIV"
  WANT="$N"; [ "$N" = "all" ] && WANT="$CNT"
  python3 - "$TMP/list" "$CNT" "$WANT" "$XD" "$DEST/$DIV" <<'PY'
import sys, shutil, os
listing, total, n, src, dst = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4], sys.argv[5]
paths = [l.rstrip("\n") for l in open(listing)]
n = min(n, total)
idxs = sorted({i * total // n for i in range(n)})
for i in idxs:
    p = paths[i]
    shutil.copyfile(os.path.join(src, p), os.path.join(dst, p.replace("/", "__")))
print(f"   sampled {len(idxs)}/{total}")
PY
  rm -rf "$TMP"
  DONE_DIVS=$((DONE_DIVS+1))
done < "$MANIFEST"

echo "== done: $DONE_DIVS divisions fetched into $DEST ($SKIPPED over the ${MAX_MB}MB cap)"
echo "   run: ay-z3-parity scoreboard $DEST --ay <libay_ffi> --jobs 4"

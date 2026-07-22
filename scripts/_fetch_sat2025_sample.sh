#!/usr/bin/env bash
# ay-script: satcomp25-sample-fetch
# Fetch a size-bounded sample of the SAT-COMP 2025 main track for local
# iteration benchmarking. Not a competition harness — just enough instances,
# small enough to sweep quickly, to measure solved-count / PAR-2 deltas.
set -uo pipefail

# Download destination; override with SATCOMP2025_DEST.
DEST="${SATCOMP2025_DEST:-$(cd "$(dirname "$0")/.." && pwd)/benchmarks/sat/satcomp2025}"
URLS="/tmp/main2025.txt"

# Single-URL worker mode: _fetch ... --one <url> <dest> <maxxz> <maxcnf>
if [ "${1:-}" = "--one" ]; then
  url="$2"; dest="$3"; maxxz="$4"; maxcnf="$5"
  hash="${url##*/}"
  xz="$dest/$hash.cnf.xz"; cnf="$dest/$hash.cnf"
  [ -s "$cnf" ] && { echo "HAVE $hash"; exit 0; }
  if ! curl -sL --fail --max-time 180 --max-filesize "$maxxz" -o "$xz" "$url"; then
    rm -f "$xz"; echo "SKIP-BIG-OR-FAIL $hash"; exit 1
  fi
  if ! xz -dkf "$xz" 2>/dev/null; then rm -f "$xz" "$cnf"; echo "SKIP-BADXZ $hash"; exit 1; fi
  rm -f "$xz"
  sz=$(stat -f%z "$cnf" 2>/dev/null || echo 0)
  if [ "$sz" -gt "$maxcnf" ]; then rm -f "$cnf"; echo "SKIP-BIGCNF $hash ($sz)"; exit 1; fi
  if ! head -c 4000 "$cnf" | grep -q "p cnf"; then rm -f "$cnf"; echo "SKIP-NOTCNF $hash"; exit 1; fi
  echo "OK $hash ($sz bytes)"; exit 0
fi

TARGET_COUNT="${1:-60}"
MAX_XZ_BYTES="${2:-6000000}"
MAX_CNF_BYTES="${3:-80000000}"
STRIDE="${4:-6}"
SELF="$(cd "$(dirname "$0")" && pwd)/$(basename "$0")"

mkdir -p "$DEST"
total=$(wc -l < "$URLS" | tr -d ' ')
echo "total urls: $total ; target: $TARGET_COUNT ; max_xz: $MAX_XZ_BYTES"

# Pass 1: deterministic stride sample, fetched in parallel via self-invocation.
awk -v s="$STRIDE" 'NR % s == 1' "$URLS" | \
  xargs -P 8 -I{} bash "$SELF" --one {} "$DEST" "$MAX_XZ_BYTES" "$MAX_CNF_BYTES"

have=$(find "$DEST" -name '*.cnf' | wc -l | tr -d ' ')
echo "after stride pass: $have instances"

# Pass 2: top up sequentially from the full list until target reached.
if [ "$have" -lt "$TARGET_COUNT" ]; then
  echo "topping up to $TARGET_COUNT ..."
  while IFS= read -r url; do
    have=$(find "$DEST" -name '*.cnf' | wc -l | tr -d ' ')
    [ "$have" -ge "$TARGET_COUNT" ] && break
    bash "$SELF" --one "$url" "$DEST" "$MAX_XZ_BYTES" "$MAX_CNF_BYTES" || true
  done < "$URLS"
fi

echo "=== FINAL ==="
find "$DEST" -name '*.cnf' | wc -l
du -sh "$DEST"

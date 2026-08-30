#!/bin/bash
# ay-script: pb-cert-delivery-run
#
# Sweep the DELIVERY/SEARCH-PROOF discriminator over a list of MISS instances.
# One row per instance per route selector; resumable; refuses to report a sweep
# that measured nothing.
#
# Read `pb_cert_delivery_probe.sh` for what the probe does and why raising
# `--timeout` is not a substitute for it.
#
# Usage: pb_cert_delivery_run.sh <ay> <certrefute> <veripb> <list> <out.tsv>
#                                [solve_ms] [cert_ms] [parallel] [route]
set -u

BIN=$1; REFUTE=$2; VERIPB=$3; LIST=$4; OUT=$5
SOLVE_MS=${6:-60000}; CERT_MS=${7:-60000}; PAR=${8:-4}; ROUTE=${9:-all}
HERE=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)

total=$(grep -c . "$LIST")
[ "$total" -gt 0 ] || { echo "ERROR: '$LIST' is empty; nothing to probe" >&2; exit 2; }

todo=$(mktemp "${TMPDIR:-/tmp}/ay-delivery-todo.XXXXXX")
while IFS= read -r f; do
    [ -n "$f" ] || continue
    if [ -s "$OUT" ] && cut -f1 "$OUT" | grep -qxF "$f"; then continue; fi
    printf '%s\n' "$f" >> "$todo"
done < "$LIST"
n=$(grep -c . "$todo" || true)

echo "delivery probe: $total instances ($n to run), route=$ROUTE, solve=${SOLVE_MS}ms cert=${CERT_MS}ms"
echo "start: $(date -u +%Y-%m-%dT%H:%M:%SZ) load $(uptime | sed 's/.*averages: //')"
if [ "$n" -gt 0 ]; then
    xargs -P "$PAR" -n1 -I{} "$HERE/pb_cert_delivery_probe.sh" \
        "$BIN" "$REFUTE" "$VERIPB" "$SOLVE_MS" "$CERT_MS" {} "$ROUTE" < "$todo" >> "$OUT"
fi
rm -f "$todo"
echo "end:   $(date -u +%Y-%m-%dT%H:%M:%SZ) load $(uptime | sed 's/.*averages: //')"

got=$(grep -c . "$OUT" 2>/dev/null || echo 0)
echo "rows: $got/$total"
echo "--- scores ---"
cut -f8 "$OUT" | sort | uniq -c | sort -rn
[ "$got" -eq "$total" ] || { echo "INCOMPLETE SWEEP" >&2; exit 2; }

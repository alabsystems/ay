#!/bin/bash
# ay-script: pb-cert-census-mutate-run
#
# Regenerate the census's OWN accepted certificates and put them through the
# adversarial battery. The census's VERIFIED count is worth nothing unless a
# WRONG proof would have been rejected, and the only proofs whose rejection
# behaviour is evidence about THIS census are the ones this census scored.
#
# The census worker deletes each proof after scoring it (the corpus is 9.1 GB
# and proofs can be megabytes), so the proofs are re-emitted here from the same
# binary at the same budget. Byte-identical re-emission is not assumed: each
# regenerated proof is re-checked and only mutated if the checker accepts it,
# so a proof that did not reproduce is skipped rather than silently scored.
#
# Usage: pb_cert_mutate_run.sh <ay-bin> <veripb> <covered-list> <out.json> [budget_ms] [max]
set -u

BIN=$1; VERIPB=$2; LIST=$3; OUT=$4; TMO=${5:-5000}; MAX=${6:-6}
HERE=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)

work=$(mktemp -d "${TMPDIR:-/tmp}/ay-mutate-corpus.XXXXXX")
trap 'rm -rf "$work"' EXIT

pairs=()
n=0
while IFS= read -r f; do
    [ -n "$f" ] || continue
    [ "$n" -ge "$MAX" ] && break
    pf="$work/p$n.pbp"
    "$BIN" pb solve --timeout "$TMO" --proof "$pf" "$f" >/dev/null 2>&1
    if [ -s "$pf" ]; then
        pairs+=("$f" "$pf")
        n=$((n + 1))
        echo "   regenerated $(basename "$f") -> $(wc -c <"$pf" | tr -d ' ') bytes"
    else
        echo "   SKIPPED (no proof re-emitted): $(basename "$f")" >&2
    fi
done < "$LIST"

if [ "$n" -eq 0 ]; then
    echo "ERROR: no proof was re-emitted; the battery would have measured NOTHING" >&2
    exit 2
fi

python3 "$HERE/pb_cert_census_mutate.py" "$VERIPB" "$OUT" "${pairs[@]}"

#!/bin/bash
# ay-script: pb-cert-budget-ab-run
#
# Sweeps `pb_cert_budget_ab.sh` over an instance list. Resumable, one file per
# arm, and it REFUSES to summarise a sweep that measured fewer rows than the
# list has lines: a harness that measured nothing must exit non-zero, never
# report "0 fail".
#
# Usage: pb_cert_budget_ab_run.sh <base-bin> <head-bin> <veripb> <list> <outdir>
#                                 <label> [budget_ms] [parallel]
set -u

BASE=$1; HEAD=$2; VERIPB=$3; LIST=$4; OUTDIR=$5; LABEL=$6
TMO=${7:-5000}; PAR=${8:-4}
HERE=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)

mkdir -p "$OUTDIR"
total=$(grep -c . "$LIST")
[ "$total" -gt 0 ] || { echo "ERROR: instance list '$LIST' is empty" >&2; exit 2; }

ARMS="base-noproof base-proof head-proof head-noproof"
arm_files=""
for a in $ARMS; do arm_files="$arm_files $OUTDIR/$LABEL-$a.tsv"; done

echo "budget A/B: $total instances, label=$LABEL, budget=${TMO}ms, parallel=$PAR"
echo "base:    $BASE sha256=$(shasum -a 256 "$BASE" | awk '{print $1}')"
echo "head:    $HEAD sha256=$(shasum -a 256 "$HEAD" | awk '{print $1}')"
echo "checker: $VERIPB sha256=$(shasum -a 256 "$VERIPB" | awk '{print $1}')"
echo "list:    $LIST sha256=$(shasum -a 256 "$LIST" | awk '{print $1}')"
echo "start:   $(date -u +%Y-%m-%dT%H:%M:%SZ) load $(uptime | sed 's/.*averages: //')"

split_rows() {
    while IFS= read -r row; do
        arm=$(printf '%s' "$row" | cut -f2)
        printf '%s\n' "$row" >> "$OUTDIR/$arm.tsv"
    done
}

todo="$OUTDIR/.todo-$LABEL"
: > "$todo"
while IFS= read -r f; do
    [ -n "$f" ] || continue
    done_all=1
    for af in $arm_files; do
        if [ ! -s "$af" ] || ! cut -f1 "$af" | grep -qxF "$f"; then done_all=0; break; fi
    done
    [ "$done_all" -eq 1 ] || printf '%s\n' "$f" >> "$todo"
done < "$LIST"
n=$(grep -c . "$todo" || true)
echo "todo:    $n instances"

if [ "$n" -gt 0 ]; then
    xargs -P "$PAR" -n1 -I{} "$HERE/pb_cert_budget_ab.sh" \
        "$BASE" "$HEAD" "$VERIPB" "$TMO" "$LABEL" {} < "$todo" | split_rows
fi
rm -f "$todo"

echo "end:     $(date -u +%Y-%m-%dT%H:%M:%SZ) load $(uptime | sed 's/.*averages: //')"
bad=0
for af in $arm_files; do
    got=$(grep -c . "$af" 2>/dev/null || echo 0)
    echo "arm $(basename "$af"): $got/$total rows"
    [ "$got" -eq "$total" ] || bad=1
done
[ "$bad" -eq 0 ] || { echo "INCOMPLETE A/B" >&2; exit 2; }
echo "A/B COMPLETE"

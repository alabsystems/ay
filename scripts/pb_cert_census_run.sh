#!/bin/bash
# ay-script: pb-cert-census-run
#
# THE HARNESS. Runs the PB certificate census over the PB25 OPT-LIN corpus:
# every instance gets all four arms back to back (see pb_cert_census.sh for why
# the arms are interleaved per instance rather than swept pass by pass), and
# each arm's row is appended to its own TSV.
#
# RESUMABLE. An instance whose row is already present in EVERY arm file is not
# re-run, so a killed harness loses at most the instances in flight. Rerunning
# after a crash therefore converges rather than duplicating.
#
# EXIT CODES: 0 = every arm has a row for every instance. 2 = the census
# measured nothing, or fewer rows than the list has lines. A harness that
# measured NOTHING must exit non-zero, never report "0 fail".
#
# Usage: pb_cert_census_run.sh <ay-cli> <ay-pb> <veripb-bin> <list> <outdir> [parallel] [arms]
set -u

CLI=$1; PBBIN=$2; VERIPB=$3; LIST=$4; OUTDIR=$5; PAR=${6:-5}
ARMS=${7:-cli:noproof:5000,cli:proof:5000,aypb:noproof:5000,aypb:proof:5000}
HERE=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)

mkdir -p "$OUTDIR"
total=$(grep -c . "$LIST")
[ "$total" -gt 0 ] || { echo "ERROR: instance list '$LIST' is empty" >&2; exit 2; }

echo "census: $total instances, parallel=$PAR, arms=$ARMS"
echo "cli:     $CLI sha256=$(shasum -a 256 "$CLI" | awk '{print $1}')"
echo "ay-pb:   $PBBIN sha256=$(shasum -a 256 "$PBBIN" | awk '{print $1}')"
echo "checker: $VERIPB sha256=$(shasum -a 256 "$VERIPB" | awk '{print $1}')"
echo "list:    $LIST sha256=$(shasum -a 256 "$LIST" | awk '{print $1}')"
echo "start:   $(date -u +%Y-%m-%dT%H:%M:%SZ) load $(uptime | sed 's/.*averages: //')"

# ---- split the worker's multi-arm stdout into one file per arm.
split_rows() {
    while IFS= read -r row; do
        mode=$(printf '%s' "$row" | cut -f2)
        tmo=$(printf '%s' "$row" | cut -f3)
        printf '%s\n' "$row" >> "$OUTDIR/$mode-$tmo.tsv"
    done
}

# An instance is DONE only when every arm has a row for it.
arm_files=""
IFS=',' read -ra SPECS <<< "$ARMS"
for spec in "${SPECS[@]}"; do
    IFS=":" read -r s_bin s_mode s_tmo <<< "$spec"
    arm_files="$arm_files $OUTDIR/$s_bin-$s_mode-$s_tmo.tsv"
done

todo="$OUTDIR/.todo"
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
    xargs -P "$PAR" -n1 -I{} "$HERE/pb_cert_census.sh" "$CLI" "$PBBIN" "$VERIPB" "$ARMS" {} \
        < "$todo" | split_rows
fi
rm -f "$todo"

echo "end:     $(date -u +%Y-%m-%dT%H:%M:%SZ) load $(uptime | sed 's/.*averages: //')"
bad=0
for af in $arm_files; do
    got=$(grep -c . "$af" 2>/dev/null || echo 0)
    echo "arm $(basename "$af"): $got/$total rows"
    [ "$got" -eq "$total" ] || bad=1
done
[ "$bad" -eq 0 ] || { echo "INCOMPLETE CENSUS" >&2; exit 2; }
echo "CENSUS COMPLETE"

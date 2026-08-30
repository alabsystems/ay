#!/bin/bash
# ay-script: pb-cert-cli-ab-run
#
# THE HARNESS behind `pb_cert_cli_ab.sh`: sweeps an instance list, giving every
# instance all arms back to back, one TSV per arm.
#
# RESUMABLE: an instance already present in EVERY arm file is not re-run, so a
# killed sweep loses at most the instances in flight and a rerun converges.
#
# EXIT CODES: 0 = every arm has a row for every instance. 2 = the sweep measured
# nothing, or fewer rows than the list has lines. A harness that measured
# NOTHING must exit non-zero, never report "0 fail".
#
# Usage: pb_cert_cli_ab_run.sh <bin-map> <veripb> <list> <outdir> [parallel] [arms]
set -u

BINMAP=$1; VERIPB=$2; LIST=$3; OUTDIR=$4; PAR=${5:-4}
ARMS=${6:-cli0:proof:5000,cli1:proof:5000,pb1:proof:5000}
HERE=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)

mkdir -p "$OUTDIR"
total=$(grep -c . "$LIST")
[ "$total" -gt 0 ] || { echo "ERROR: instance list '$LIST' is empty" >&2; exit 2; }

echo "cli-ab: $total instances, parallel=$PAR, arms=$ARMS"
IFS=',' read -ra PAIRS <<< "$BINMAP"
for p in "${PAIRS[@]}"; do
    echo "bin ${p%%=*}: ${p#*=} sha256=$(shasum -a 256 "${p#*=}" | awk '{print $1}')"
done
echo "checker: $VERIPB sha256=$(shasum -a 256 "$VERIPB" | awk '{print $1}')"
echo "list:    $LIST sha256=$(shasum -a 256 "$LIST" | awk '{print $1}')"
echo "start:   $(date -u +%Y-%m-%dT%H:%M:%SZ) load $(uptime | sed 's/.*averages: //')"

split_rows() {
    while IFS= read -r row; do
        arm=$(printf '%s' "$row" | cut -f2)
        tmo=$(printf '%s' "$row" | cut -f3)
        printf '%s\n' "$row" >> "$OUTDIR/$arm-$tmo.tsv"
    done
}

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
    xargs -P "$PAR" -n1 -I{} "$HERE/pb_cert_cli_ab.sh" "$BINMAP" "$VERIPB" "$ARMS" {} \
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
[ "$bad" -eq 0 ] || { echo "INCOMPLETE SWEEP" >&2; exit 2; }
echo "SWEEP COMPLETE"

#!/bin/bash
# The certified-track manifest, run through the SHIPPED CLI.
#
# `scripts/ci/pb_certified_gate.sh` only ever runs `ay-pb`. That is exactly how
# the CLI's certificate chain was able to fall six routes behind without any
# gate going red: no committed gate runs `ay pb solve --proof` over the cert
# manifest at all. This runs it, for a named binary, and requires for every row
#
#   * the status AY prints is the status the manifest says, and
#   * the pinned checker's verdict LINE is exactly `s VERIFIED <conclusion>`
#     for the conclusion the manifest names, with exit code 0.
#
# A success status with no proof file is a FAILURE, not a skip — that pairing is
# the hole the certified track exists to keep closed.
#
# Usage: cli_manifest_gate.sh <ay-cli-bin> <veripb> [timeout_ms]
set -u
BIN=$1; VERIPB=$2; TMO=${3:-10000}
REPO=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
MAN=$REPO/ci/cert-instances/manifest.tsv
. "$REPO/scripts/lib/veripb_verdict.sh"

work=$(mktemp -d "${TMPDIR:-/tmp}/ay-cli-manifest.XXXXXX")
trap 'rm -rf "$work"' EXIT

echo "binary:  $BIN sha256=$(shasum -a 256 "$BIN" | awk '{print $1}')"
echo "checker: $VERIPB sha256=$(shasum -a 256 "$VERIPB" | awk '{print $1}')"

rows=0; fails=0; refusals=0
while IFS=$'\t' read -r instance mode status conclusion; do
    case "$instance" in ''|'#'*) continue ;; esac
    rows=$((rows + 1))
    f=$REPO/$instance
    pf=$work/p.pbp
    rm -f "$pf"
    got=$("$BIN" pb solve --timeout "$TMO" --proof "$pf" "$f" 2>/dev/null | grep '^s ' | tail -1)
    # A DOCUMENTED FAIL-CLOSED REFUSAL IS NOT A WRONG ANSWER, AND IT IS NOT A
    # PASS EITHER. The CLI answers `s UNSUPPORTED` to `--proof` on a non-linear
    # instance ("proof logging for non-linear PB is not supported; refusing
    # uncertified solve"), where `ay-pb` answers `s SATISFIABLE` and ships a
    # proof the pinned checker cannot even parse (the certified gate scores that
    # row UNCHECKABLE). Counted separately, printed every run, never folded into
    # the pass count and never silently zero.
    if [ "$got" = "s UNSUPPORTED" ] && [ "$status" != "s UNSUPPORTED" ]; then
        echo "REFUSED [$(basename "$instance")] AY declined to solve uncertified; manifest says '$status'"
        refusals=$((refusals + 1))
        continue
    fi
    if [ "$got" != "$status" ]; then
        echo "FAIL [$instance] AY said '${got:-<no s line>}', manifest says '$status'"
        fails=$((fails + 1))
        continue
    fi
    if [ ! -s "$pf" ]; then
        echo "FAIL [$instance] status '$status' with NO proof file"
        fails=$((fails + 1))
        continue
    fi
    veripb_run "$VERIPB" --opb "$f" "$pf"
    if veripb_accepted && [ "$VERIPB_VERDICT" = "s VERIFIED $conclusion" ]; then
        echo "ok   [$(basename "$instance")] $status -> $VERIPB_VERDICT"
    else
        echo "FAIL [$instance] exit=$VERIPB_EXIT verdict='${VERIPB_VERDICT:-<none>}' want='s VERIFIED $conclusion'"
        fails=$((fails + 1))
    fi
done < "$MAN"

echo "rows=$rows fails=$fails refusals=$refusals"
[ "$rows" -gt 0 ] || { echo "MEASURED NOTHING" >&2; exit 2; }
[ "$fails" -eq 0 ] || exit 1
echo "CLI MANIFEST GATE PASSED (with $refusals documented refusal(s))"

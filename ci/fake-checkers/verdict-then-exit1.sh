#!/bin/sh
# FAKE VeriPB checker (i): correct verdict, wrong exit code.
#
# Delegates to a REAL checker named by $AY_FAKE_VERIPB_DELEGATE and reprints its
# output verbatim — so its verdict LINE is genuinely correct — then exits 1.
#
# This is the fake that every "assert on the verdict text, exit status is not a
# gate" rule waves through. Modelled on a checker that dies after printing (OOM
# killer, signal, a wrapper with a broken teardown): the verdict on stdout is no
# longer evidence that the run completed.
set -u
case "${1:-}" in --version) echo "Running VeriPB version 3.0.2"; echo "veripb 3.0.2"; exit 0 ;; esac
delegate=${AY_FAKE_VERIPB_DELEGATE:-}
if [ -z "$delegate" ] || [ ! -x "$delegate" ]; then
    echo "fake checker (i) needs AY_FAKE_VERIPB_DELEGATE=<real veripb>" >&2
    exit 127
fi
"$delegate" "$@"
exit 1

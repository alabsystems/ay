#!/bin/sh
# FAKE VeriPB checker (ii): says nothing, exits 0.
#
# The /usr/bin/true case. Any gate whose success condition is "the checker
# process exited successfully" is satisfied by this having checked nothing.
set -u
case "${1:-}" in --version) echo "Running VeriPB version 3.0.2"; echo "veripb 3.0.2"; exit 0 ;; esac
exit 0

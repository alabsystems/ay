#!/bin/sh
# ay-script: cert-ci-gate
# CERT-track CI gate (campaign M0: CakePB/VeriPB CI harness, stage 1).
#
# Produces a proof for every certified outcome class with the CURRENT release
# binary and verifies each with the OFFICIAL VeriPB checker (v3, the PB26+
# format). Any unverified proof fails the gate — an unshippable certificate is
# a silently forfeited CERT instance (historically the difference between
# 12 and 147-class answer counts).
#
# Checker resolution order: $VERIPB_BIN, `veripb` on PATH, cached build under
# ~/.cache/ay-veripb (cloned from the official GitLab and built once).
# Stage 2 (tracked in the campaign plan): add the CakePB verified backend via
# `veripb --elaborate` once proofs at scale enter CI.
set -eu

REPO=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
BIN=${AY_PB_BIN:-"$REPO/target/release/ay-pb"}
[ -x "$BIN" ] || { echo "ERROR: solver binary missing: $BIN (cargo build -p ay-pb --release)" >&2; exit 2; }

VERIPB=${VERIPB_BIN:-}
if [ -z "$VERIPB" ] && command -v veripb >/dev/null 2>&1; then
    VERIPB=$(command -v veripb)
fi
if [ -z "$VERIPB" ]; then
    CACHE="${XDG_CACHE_HOME:-$HOME/.cache}/ay-veripb"
    VERIPB="$CACHE/VeriPB/target/release/veripb"
    if [ ! -x "$VERIPB" ]; then
        echo "== building official VeriPB checker into $CACHE"
        mkdir -p "$CACHE"
        [ -d "$CACHE/VeriPB" ] || git clone --quiet --depth 1 \
            https://gitlab.com/MIAOresearch/software/VeriPB.git "$CACHE/VeriPB"
        (cd "$CACHE/VeriPB" && cargo build --release --quiet)
    fi
fi
echo "checker: $("$VERIPB" --version 2>&1 | head -1 || echo "$VERIPB")"

WORK=$(mktemp -d "${TMPDIR:-/tmp}/ay-cert-ci.XXXXXX")
trap 'rm -rf "$WORK"' EXIT

fail=0
check_class() {
    label=$1; instance=$2; expect_status=$3; env_extra=${4:-}
    proof="$WORK/$label.veripb"
    got=$(env $env_extra "$BIN" pb solve --timeout 15000 --proof "$proof" \
        "$instance" | grep '^s ' | head -1)
    if [ "$got" != "$expect_status" ]; then
        echo "FAIL [$label]: solver said '$got', expected '$expect_status'" >&2
        fail=1
        return
    fi
    if [ ! -f "$proof" ]; then
        echo "FAIL [$label]: no proof file produced" >&2
        fail=1
        return
    fi
    if verdict=$("$VERIPB" "$instance" "$proof" 2>&1 | grep '^s ' | head -1) \
        && case "$verdict" in "s VERIFIED"*) true;; *) false;; esac; then
        echo "  OK [$label]: $got -> $verdict"
    else
        echo "FAIL [$label]: checker rejected the proof: $verdict" >&2
        fail=1
    fi
}

cat > "$WORK/opt.opb" <<'EOF'
* #variable= 2 #constraint= 2
min: +2 x1 +3 x2 ;
+1 x1 +1 x2 >= 1 ;
-1 x1 -1 x2 >= -2 ;
EOF
cat > "$WORK/unsat.opb" <<'EOF'
* #variable= 1 #constraint= 2
+1 x1 >= 1 ;
-1 x1 >= 0 ;
EOF
cat > "$WORK/opt-unsat.opb" <<'EOF'
* #variable= 2 #constraint= 2
min: +1 x1 +1 x2 ;
+1 x1 >= 1 ;
-1 x1 >= 0 ;
EOF
cat > "$WORK/card.opb" <<'EOF'
* #variable= 4 #constraint= 2
min: +1 x1 +1 x2 +1 x3 +1 x4 ;
+1 x1 +1 x2 +1 x3 +1 x4 >= 2 ;
+1 x1 +1 x2 >= 1 ;
EOF

check_class native-optimum   "$WORK/opt.opb"       "s OPTIMUM FOUND"
check_class decision-unsat   "$WORK/unsat.opb"     "s UNSATISFIABLE"
check_class opt-unsat-infinf "$WORK/opt-unsat.opb" "s UNSATISFIABLE"
check_class cardinality-opt  "$WORK/card.opb"      "s OPTIMUM FOUND"
# The certify-after-solve fallback pipeline (portfolio finds, helpers certify).
check_class fallback-certified "$WORK/opt.opb"     "s OPTIMUM FOUND" "AY_PB_CERT_NATIVE_CAP_MS=0"
cat > "$WORK/dec-sat.opb" <<'EOF2'
* #variable= 3 #constraint= 2
+1 x1 +1 x2 >= 1 ;
+1 x2 +1 x3 >= 1 ;
EOF2
# Decision-SAT via the solution-only proof (plain-speed phase, checker-validated model).
check_class decision-sat-fallback "$WORK/dec-sat.opb" "s SATISFIABLE" "AY_PB_CERT_NATIVE_CAP_MS=0"

if [ "$fail" -ne 0 ]; then
    echo "CERT CI: FAILED" >&2
    exit 1
fi
echo "CERT CI: all proof classes verified by the official checker"

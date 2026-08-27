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
# WHAT "VERIFIED" MEANS HERE. The gate does not ask "did the checker print
# something starting with `s VERIFIED`". That test passed a SATISFIABLE
# instance whose proof concluded NOTHING (`s VERIFIED NO CONCLUSION` has that
# prefix) and would equally have passed a proof establishing the OPPOSITE of
# what AY answered. Every class now names the conclusion its status entails,
# the gate cross-checks that the named conclusion really is the one the status
# entails (including that an OPTIMUM's bounds are the `o` value AY printed),
# and the checker must confirm EXACTLY that conclusion, with exit code 0, via
# scripts/lib/veripb_verdict.sh. `NO CONCLUSION` is a rejection.
#
# WHICH CHECKER. Resolution order mirrors the ONE shared Rust resolver in
# crates/ay-test-support/src/veripb.rs: $VERIPB_BIN / $AY_PB26_VERIPB_BIN /
# $VERIPB, `veripb` on PATH, known local build locations, and finally a cached
# build under ~/.cache/ay-veripb (cloned from the official GitLab and built
# once). Whatever is resolved must then PASS THE SELF-TEST BATTERY before any
# of its verdicts is believed: a binary that cannot be shown to check proofs
# fails the gate rather than silently rubber-stamping it. A checker is never
# optional here.
# Stage 2 (tracked in the campaign plan): add the CakePB verified backend via
# `veripb --elaborate` once proofs at scale enter CI.
set -eu

REPO=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
. "$REPO/scripts/lib/veripb_verdict.sh"

# The checker PIN is the single source of truth for WHICH VeriPB a certified
# claim is made against; scripts/ci/pb_certified_gate.sh reads the same file.
PIN_FILE="$REPO/ci/veripb.pin"
[ -r "$PIN_FILE" ] || { echo "ERROR: missing checker pin: $PIN_FILE" >&2; exit 2; }
. "$PIN_FILE"
for _required in VERIPB_REPO VERIPB_COMMIT VERIPB_PATCH VERIPB_PATCH_SHA256 \
                 VERIPB_PATCH2 VERIPB_PATCH2_SHA256 VERIPB_SOUNDNESS_DIR; do
    eval "_value=\${$_required:-}"
    [ -n "$_value" ] || { echo "ERROR: $PIN_FILE does not set $_required" >&2; exit 2; }
done

BIN=${AY_PB_BIN:-"$REPO/target/release/ay-pb"}
[ -x "$BIN" ] || { echo "ERROR: solver binary missing: $BIN (cargo build -p ay-pb --release)" >&2; exit 2; }

VERIPB=${VERIPB_BIN:-${AY_PB26_VERIPB_BIN:-${VERIPB:-}}}
if [ -n "$VERIPB" ] && [ ! -x "$VERIPB" ]; then
    echo "ERROR: VERIPB_BIN/AY_PB26_VERIPB_BIN/VERIPB names '$VERIPB', which is not executable" >&2
    exit 2
fi
if [ -z "$VERIPB" ] && command -v veripb >/dev/null 2>&1; then
    VERIPB=$(command -v veripb)
fi
if [ -z "$VERIPB" ]; then
    for candidate in \
        /tmp/veripb-3/bin/veripb \
        "$HOME/.cargo/bin/veripb"
    do
        [ -x "$candidate" ] || continue
        VERIPB=$candidate
        break
    done
fi
if [ -z "$VERIPB" ]; then
    # Build the PINNED checker: the pinned commit with the reviewed patch
    # applied, in a directory keyed by both. This used to `git clone --depth 1`
    # the upstream default branch and build whatever it got — an UNPINNED,
    # UNPATCHED checker, which is precisely the binary the pin exists to
    # exclude. That build passes the self-test battery below and still answers
    # `s VERIFIED UNSATISFIABLE` for satisfiable formulas (see
    # ci/veripb-soundness/03 and 04), so the gate would have certified AY's
    # answers against a checker known to give wrong verdicts.
    CACHE="${VERIPB_CACHE:-${XDG_CACHE_HOME:-$HOME/.cache}/ay-veripb}"
    actual_patch_sha=$(sha256_file "$REPO/$VERIPB_PATCH" 2>/dev/null || true)
    if [ "$actual_patch_sha" != "$VERIPB_PATCH_SHA256" ]; then
        echo "ERROR: $VERIPB_PATCH does not match VERIPB_PATCH_SHA256 in $PIN_FILE" >&2
        echo "       pin:  $VERIPB_PATCH_SHA256" >&2
        echo "       file: ${actual_patch_sha:-<unreadable>}" >&2
        exit 2
    fi
    actual_patch2_sha=$(sha256_file "$REPO/$VERIPB_PATCH2" 2>/dev/null || true)
    if [ "$actual_patch2_sha" != "$VERIPB_PATCH2_SHA256" ]; then
        echo "ERROR: $VERIPB_PATCH2 does not match VERIPB_PATCH2_SHA256 in $PIN_FILE" >&2
        echo "       pin:  $VERIPB_PATCH2_SHA256" >&2
        echo "       file: ${actual_patch2_sha:-<unreadable>}" >&2
        exit 2
    fi
    # Both patch hashes are in the key: a changed or added patch must rebuild.
    BUILD_ID="${VERIPB_COMMIT}-$(printf '%s' "$VERIPB_PATCH_SHA256" | cut -c1-12)"
    BUILD_ID="${BUILD_ID}-$(printf '%s' "$VERIPB_PATCH2_SHA256" | cut -c1-12)"
    BUILD_DIR="$CACHE/$BUILD_ID"
    VERIPB="$BUILD_DIR/target/release/veripb"
    if [ ! -x "$VERIPB" ]; then
        echo "== building pinned checker ($VERIPB_COMMIT + $(basename "$VERIPB_PATCH") + $(basename "$VERIPB_PATCH2")) into $BUILD_DIR"
        mkdir -p "$CACHE"
        [ -d "$BUILD_DIR" ] || git clone --quiet "$VERIPB_REPO" "$BUILD_DIR"
        git -C "$BUILD_DIR" checkout --quiet "$VERIPB_COMMIT"
        got=$(git -C "$BUILD_DIR" rev-parse HEAD)
        [ "$got" = "$VERIPB_COMMIT" ] || {
            echo "ERROR: checkout landed on $got, pin says $VERIPB_COMMIT" >&2
            exit 2
        }
        git -C "$BUILD_DIR" apply "$REPO/$VERIPB_PATCH"
        git -C "$BUILD_DIR" apply "$REPO/$VERIPB_PATCH2"
        (cd "$BUILD_DIR" && cargo build --release --quiet)
    fi
fi
echo "checker: $("$VERIPB" --version 2>&1 | head -1 || echo "$VERIPB")"

# Prove the binary BEHAVES like a proof checker before believing a verdict...
veripb_require_self_test "$VERIPB"
# ...and that it is a CORRECT one. The self-test battery alone does not
# establish that: published VeriPB 3.0.2 passes all six of its probes and still
# contradicts the truth on all TWENTY-TWO fixtures below (twenty-two fixtures
# covering the twenty-one known wrong-verdict defects).
veripb_require_soundness "$VERIPB" "$REPO/$VERIPB_SOUNDNESS_DIR"

WORK=$(mktemp -d "${TMPDIR:-/tmp}/ay-cert-ci.XXXXXX")
trap 'rm -rf "$WORK"' EXIT

fail=0

# check_class LABEL INSTANCE EXPECT_STATUS EXPECT_CONCLUSION [ENV_EXTRA]
#
# EXPECT_CONCLUSION is the checker conclusion that EXPECT_STATUS entails. The
# gate re-derives that relationship rather than trusting the table:
#
#   s SATISFIABLE      -> SATISFIABLE
#   s UNSATISFIABLE    -> UNSATISFIABLE, or BOUNDS INF <= obj <= INF when the
#                         instance has an objective (infeasible optimisation)
#   s OPTIMUM FOUND    -> BOUNDS v <= obj <= v, where v is the objective value
#                         AY itself printed on its last `o ` line
#
# so a row cannot silently declare a conclusion that does not match the answer
# being certified.
check_class() {
    label=$1; instance=$2; expect_status=$3; expect_conclusion=$4; env_extra=${5:-}
    proof="$WORK/$label.veripb"
    solver_out="$WORK/$label.stdout"

    env $env_extra "$BIN" pb solve --timeout 15000 --proof "$proof" \
        "$instance" > "$solver_out" 2>/dev/null || true
    got=$(grep '^s ' "$solver_out" | head -1 || true)
    objective=$(grep '^o ' "$solver_out" | tail -1 | sed 's/^o //' || true)

    if [ "$got" != "$expect_status" ]; then
        echo "FAIL [$label]: solver said '${got:-<no s line>}', expected '$expect_status'" >&2
        fail=1
        return
    fi
    if [ ! -f "$proof" ]; then
        echo "FAIL [$label]: no proof file produced" >&2
        fail=1
        return
    fi

    # The status/conclusion consistency check. This is the part that makes
    # "the checker agreed" mean "the checker agreed WITH AY".
    if ! entailed=$(veripb_entailed_conclusion "$expect_status" "$instance" "$objective"); then
        echo "FAIL [$label]: cannot certify this answer" >&2
        fail=1
        return
    fi
    if [ "$expect_conclusion" != "$entailed" ]; then
        echo "FAIL [$label]: the declared conclusion is not the one '$expect_status' entails" >&2
        echo "     declared: $expect_conclusion" >&2
        echo "     entailed: $entailed" >&2
        fail=1
        return
    fi

    if veripb_require_conclusion "$VERIPB" "$instance" "$proof" "$expect_conclusion" "$label"; then
        echo "  OK [$label]: $got -> s VERIFIED $expect_conclusion"
    else
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

check_class native-optimum   "$WORK/opt.opb"       "s OPTIMUM FOUND"  "BOUNDS 2 <= obj <= 2"
check_class decision-unsat   "$WORK/unsat.opb"     "s UNSATISFIABLE"  "UNSATISFIABLE"
check_class opt-unsat-infinf "$WORK/opt-unsat.opb" "s UNSATISFIABLE"  "BOUNDS INF <= obj <= INF"
check_class cardinality-opt  "$WORK/card.opb"      "s OPTIMUM FOUND"  "BOUNDS 2 <= obj <= 2"
# The certify-after-solve fallback pipeline (portfolio finds, helpers certify).
check_class fallback-certified "$WORK/opt.opb"     "s OPTIMUM FOUND"  "BOUNDS 2 <= obj <= 2" \
    "AY_PB_CERT_NATIVE_CAP_MS=0"
cat > "$WORK/dec-sat.opb" <<'EOF2'
* #variable= 3 #constraint= 2
+1 x1 +1 x2 >= 1 ;
+1 x2 +1 x3 >= 1 ;
EOF2
# Decision-SAT via the solution-only proof (plain-speed phase, checker-validated model).
check_class decision-sat-fallback "$WORK/dec-sat.opb" "s SATISFIABLE" "SATISFIABLE" \
    "AY_PB_CERT_NATIVE_CAP_MS=0"

if [ "$fail" -ne 0 ]; then
    echo "CERT CI: FAILED" >&2
    exit 1
fi
echo "CERT CI: every proof class checked, and every conclusion matched AY's own answer"

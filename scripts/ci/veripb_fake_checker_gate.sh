#!/bin/sh
# ay-script: veripb-fake-checker-gate
#
# Point every VeriPB-backed gate in this repository at five binaries that are
# NOT proof checkers, and FAIL if any gate passes.
#
# This is the executable form of "our proof gates cannot be fooled". Each fake
# under ci/fake-checkers/ answers `--version` with `veripb 3.0.2`, so the
# version pin waves all five through; only behaviour separates them from a real
# checker.
#
#   (i)   verdict-then-exit1.sh  a REAL checker's verdict, verbatim, then exit 1
#   (ii)  silent-exit0.sh        prints nothing, exits 0
#   (iii) always-unsat.sh        `s VERIFIED UNSATISFIABLE` for every input
#   (iv)  parrot.sh              echoes back whatever the proof itself claims
#   (v)   comment-verified.sh    REFUSES (`s NOT VERIFIED`), exits 0, and says
#                                the accepting words in a `c` comment. Only a
#                                reader that scans stdout for a SUBSTRING
#                                accepts it -- which veripb_runner::verify_unsat
#                                did, turning a refusal into a verification.
#
# Gates exercised:
#   * scripts/cert_ci.sh
#   * scripts/ci/pb_certified_gate.sh
#   * scripts/pb_cert_coverage.sh
#   * the shared self-test in scripts/lib/veripb_verdict.sh (directly)
#   * ay-pb-dev certify-unsat --veripb (the CLI surface that takes a checker
#     path from the user) -- REQUIRED, not conditional: it used to run only
#     `if [ -x "$DEV" ]`, and nothing here builds that binary, so the one
#     surface with a user-supplied checker path was the one never checked
#
# The Rust half lives in crates/ay-pb/tests/veripb_fake_checker_gate.rs and
# runs the same five fakes through ay_test_support::veripb::self_test.
#
# Usage: scripts/ci/veripb_fake_checker_gate.sh [real-veripb]
#   The real checker is needed for two reasons: fake (i) delegates to it, and
#   the control run proves the gates still PASS for a genuine checker (a suite
#   that rejects everything would be just as useless as one that accepts
#   everything).
set -u

REPO=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
cd "$REPO"
. "$REPO/scripts/lib/veripb_verdict.sh"

REAL=${1:-${VERIPB_BIN:-${AY_PB26_VERIPB_BIN:-${VERIPB:-}}}}
if [ -z "$REAL" ] && command -v veripb >/dev/null 2>&1; then
    REAL=$(command -v veripb)
fi
if [ -z "$REAL" ]; then
    for candidate in \
        /tmp/veripb-3/bin/veripb \
        "$HOME/.cargo/bin/veripb" \
        "${XDG_CACHE_HOME:-$HOME/.cache}/ay-veripb/VeriPB/target/release/veripb"
    do
        [ -x "$candidate" ] || continue
        REAL=$candidate
        break
    done
fi
[ -n "$REAL" ] && [ -x "$REAL" ] || {
    echo "ERROR: need a real VeriPB to delegate to and to run the control case." >&2
    echo "       Usage: $0 /path/to/veripb" >&2
    exit 2
}

BIN=${AY_PB_BIN:-"$REPO/target/release/ay-pb"}
[ -x "$BIN" ] || { echo "ERROR: solver binary missing: $BIN" >&2; exit 2; }

# The certify-unsat surface used to be checked only `if [ -x "$DEV" ]`, and
# NOTHING in this repository builds ay-pb-dev, so in practice that surface was
# never checked at all -- a silent skip inside the very script whose job is to
# prove no gate is vacuous. It is now required, like $BIN above.
DEV=${AY_PB_DEV_BIN:-"$REPO/target/release/ay-pb-dev"}
[ -x "$DEV" ] || {
    echo "ERROR: campaign binary missing: $DEV" >&2
    echo "       It carries the certify-unsat --veripb surface, which is the one" >&2
    echo "       that takes a checker path from the user. Build it with:" >&2
    echo "         cargo build --release -p ay-pb --features dev-tools --bin ay-pb-dev" >&2
    exit 2
}

WORK=$(mktemp -d "${TMPDIR:-/tmp}/ay-fake-checker.XXXXXX")
trap 'rm -rf "$WORK"' EXIT
ls "$REPO/benchmarks/pb-comp/test-instances"/*.opb > "$WORK/list.txt"

FAKES="verdict-then-exit1 silent-exit0 always-unsat parrot comment-verified"
fail=0
checks=0

# Wrap a fake so it carries the delegate environment and can be handed to any
# gate as a plain path.
shim_for() {
    _shim="$WORK/shim-$1"
    {
        echo '#!/bin/sh'
        echo "AY_FAKE_VERIPB_DELEGATE='$REAL' exec '$REPO/ci/fake-checkers/$1.sh' \"\$@\""
    } > "$_shim"
    chmod +x "$_shim"
    echo "$_shim"
}

# must_fail <label> <command...>   — the gate must NOT pass.
must_fail() {
    _label=$1; shift
    checks=$((checks + 1))
    if "$@" > "$WORK/last.log" 2>&1; then
        echo "  ACCEPTED  $_label   <-- THIS IS A HOLE" >&2
        sed 's/^/      | /' "$WORK/last.log" | tail -20 >&2
        fail=1
    else
        echo "  rejected  $_label (exit $?)"
    fi
}

# must_pass <label> <command...>   — the control: a real checker must still work.
must_pass() {
    _label=$1; shift
    checks=$((checks + 1))
    if "$@" > "$WORK/last.log" 2>&1; then
        echo "  passed    $_label"
    else
        echo "  FAILED    $_label   <-- the gate rejects a REAL checker" >&2
        sed 's/^/      | /' "$WORK/last.log" | tail -30 >&2
        fail=1
    fi
}

echo "== control: the real checker must still pass every gate"
must_pass "self-test            [real]" veripb_self_test "$REAL"
must_pass "ay-pb-dev certify-unsat [real]" "$DEV" certify-unsat \
    "$REPO/benchmarks/pb-comp/test-instances/trivial-unsat.opb" \
    --limit 1 --veripb "$REAL"
must_pass "cert_ci.sh           [real]" env VERIPB_BIN="$REAL" sh "$REPO/scripts/cert_ci.sh"
must_pass "pb_certified_gate.sh [real]" env VERIPB_BIN="$REAL" sh "$REPO/scripts/ci/pb_certified_gate.sh"
must_pass "pb_cert_coverage.sh  [real]" bash "$REPO/scripts/pb_cert_coverage.sh" \
    "$BIN" "$REAL" "$WORK/list.txt" "$WORK/cov-real.txt"

for fake in $FAKES; do
    shim=$(shim_for "$fake")
    echo
    echo "== fake: $fake"
    # The fake really does impersonate the pinned checker's identity.
    reported=$("$shim" --version 2>&1 | tail -1 | awk '{print $NF}')
    echo "  (it answers --version with '$reported', so the version pin cannot see it)"

    must_fail "self-test            [$fake]" veripb_self_test "$shim"
    must_fail "cert_ci.sh           [$fake]" env VERIPB_BIN="$shim" sh "$REPO/scripts/cert_ci.sh"
    must_fail "pb_certified_gate.sh [$fake]" env VERIPB_BIN="$shim" sh "$REPO/scripts/ci/pb_certified_gate.sh"
    must_fail "pb_cert_coverage.sh  [$fake]" bash "$REPO/scripts/pb_cert_coverage.sh" \
        "$BIN" "$shim" "$WORK/list.txt" "$WORK/cov-$fake.txt"

    must_fail "ay-pb-dev certify-unsat [$fake]" "$DEV" certify-unsat \
        "$REPO/benchmarks/pb-comp/test-instances/trivial-unsat.opb" \
        --limit 1 --veripb "$shim"
done

echo
if [ "$fail" -ne 0 ]; then
    echo "FAKE CHECKER GATE: FAILED — a binary that does not check proofs got through" >&2
    exit 1
fi
echo "FAKE CHECKER GATE: PASSED ($checks checks; 5 fakes rejected by every gate, real checker still accepted)"

#!/bin/sh
# ay-script: pb-certified-gate
#
# The PB certified-track CI gate: AY emits proofs for a committed instance set
# and a PINNED VeriPB checks every one of them. Any rejected proof fails the
# build.
#
# Before the audit there was no CI job anywhere in this repo that ran VeriPB,
# so "certified track" meant "we emit a file". This script is the gate that
# makes the claim falsifiable, in six phases:
#
#   1. SOLVER    unless AY_PB_BIN explicitly selects an external binary, ask
#                Cargo to build the checked-out ay-pb, capture the executable
#                path from Cargo's artifact record, and hash that exact file.
#                Every instance uses that one artifact; an old binary cannot
#                silently certify newer sources, and shared-target worktrees
#                cannot trigger a rebuild before every manifest row.
#   2. PIN       resolve the checker named by ci/veripb.pin (build it from the
#                pinned upstream commit + pinned patch if we do not have it),
#                and refuse to proceed if its --version disagrees with the pin.
#   3. SELFTEST  prove the resolved binary is a proof checker at all, with the
#                shared six-probe battery in scripts/lib/veripb_verdict.sh. A
#                version string is trivially forgeable — every fake checker in
#                ci/fake-checkers/ answers `--version` with `veripb 3.0.2` —
#                so the pin's version half cannot be the only identity check.
#   4. SOUNDNESS make the checker prove it is worth trusting: six committed
#                formula/proof pairs on which published VeriPB 3.0.2 returns a
#                verdict that contradicts the truth must all be REJECTED.
#                ~0.1s. Without this, phase 6 could be green against a checker
#                that says VERIFIED UNSATISFIABLE for satisfiable input.
#   5. DRIFT     the reviewed workflow copy and the installed one must agree.
#   6. CERT      for every manifest row: run AY with --proof, require the
#                expected `s ...` status, re-derive the conclusion that status
#                ENTAILS, and require the checker's own verdict LINE to be
#                exactly `s VERIFIED <that conclusion>` with exit code 0.
#
# WHAT COUNTS AS ACCEPTANCE. Exit code 0 AND a verdict line
# `s VERIFIED <conclusion>` with a real conclusion. Neither stream alone is a
# gate: VeriPB exits 0 while printing `s VERIFIED NO CONCLUSION` for a proof
# that concludes nothing, and a checker can print a success line and still exit
# 1 (audit vpb-cli; ci/fake-checkers/verdict-then-exit1.sh reproduces it). And
# the conclusion is not merely "some conclusion" — it must be the one AY's own
# answer entails, so a checker confirming the OPPOSITE of the claim fails.
#
# A success status with NO proof file is a failure, not a skip. That pairing —
# `s OPTIMUM FOUND` with nothing to check — is exactly the hole this gate
# exists to keep closed.
#
# Usage:  scripts/ci/pb_certified_gate.sh [per-instance-timeout-ms]
# Env:
#   VERIPB_BIN    use this checker instead of building the pin. Its --version
#                 must still match, and it still faces the soundness fixtures.
#   AY_PB_BIN     deliberately use this external solver binary instead of
#                 building/running the exact checkout. Its source identity is
#                 not asserted, so the gate says so in its provenance output.
#   VERIPB_CACHE  where pinned checkers are built (default
#                 ${XDG_CACHE_HOME:-~/.cache}/ay-veripb).
set -eu

REPO=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
TIMEOUT_MS=${1:-15000}
cd "$REPO"

# The ONE shell-side verdict gate, shared with scripts/cert_ci.sh.
. "$REPO/scripts/lib/veripb_verdict.sh"

PIN_FILE=ci/veripb.pin
[ -f "$PIN_FILE" ] || { echo "ERROR: missing pin file $PIN_FILE" >&2; exit 2; }
# The pin is strict KEY=VALUE with no expansion, so sourcing it is safe and
# keeps ONE parser shared with the Rust side (crates/ay-test-support veripb::pin).
. "./$PIN_FILE"

for required in VERIPB_REPO VERIPB_COMMIT VERIPB_VERSION VERIPB_PATCH \
                VERIPB_PATCH_SHA256 VERIPB_SOUNDNESS_DIR VERIPB_CERT_MANIFEST; do
    eval "value=\${$required:-}"
    [ -n "$value" ] || { echo "ERROR: $PIN_FILE does not define $required" >&2; exit 2; }
done

sha256_file() {
    if command -v shasum >/dev/null 2>&1; then
        shasum -a 256 "$1" | awk '{print $1}'
    elif command -v sha256sum >/dev/null 2>&1; then
        sha256sum "$1" | awk '{print $1}'
    else
        return 1
    fi
}

# --------------------------------------------------------- phase 1: solver
echo "== phase 1/6: exact-checkout solver"
if [ -n "${AY_PB_BIN:-}" ]; then
    BIN=$AY_PB_BIN
    [ -x "$BIN" ] || {
        echo "ERROR: AY_PB_BIN is not executable: $BIN" >&2
        exit 2
    }
    solver_sha=$(sha256_file "$BIN") || {
        echo "ERROR: neither shasum nor sha256sum is available to identify AY_PB_BIN" >&2
        exit 2
    }
    echo "   solver: $BIN (supplied via AY_PB_BIN; sha256 $solver_sha)"
    echo "   source: not asserted for an external solver"
    run_solver() { "$BIN" "$@"; }
else
    command -v cargo >/dev/null 2>&1 || {
        echo "ERROR: cargo is required to build the exact checked-out ay-pb" >&2
        echo "       or set AY_PB_BIN explicitly to opt into an external binary" >&2
        exit 2
    }
    source_rev=$(git rev-parse HEAD 2>/dev/null || printf '%s' '<unknown>')
    source_status=$(git status --porcelain --untracked-files=normal 2>/dev/null || true)
    [ -z "$source_status" ] || {
        echo "ERROR: the exact-checkout gate requires a clean source tree" >&2
        echo "       commit the source, or set AY_PB_BIN to identify an external binary" >&2
        exit 2
    }
    expected_pkg=$(cargo pkgid -p ay-pb)
    artifact_log=$(mktemp "${TMPDIR:-/tmp}/ay-pb-cargo-artifact.XXXXXX")
    if ! cargo build --release -p ay-pb --bin ay-pb \
        --message-format=json-render-diagnostics >"$artifact_log"
    then
        echo "ERROR: cargo could not build the checked-out ay-pb" >&2
        tail -50 "$artifact_log" >&2
        rm -f "$artifact_log"
        exit 2
    fi
    artifact_candidates=$(
        awk -v package_id="$expected_pkg" '
            index($0, "\"reason\":\"compiler-artifact\"") &&
            index($0, "\"package_id\":\"" package_id "\"") &&
            index($0, "\"target\":{\"kind\":[\"bin\"],\"crate_types\":[\"bin\"],\"name\":\"ay-pb\"") &&
            index($0, "\"profile\":{\"opt_level\":\"3\",\"debuginfo\":0,\"debug_assertions\":false,\"overflow_checks\":true,\"test\":false}") &&
            index($0, "\"executable\":\"") {
                executable = $0
                sub(/^.*"executable":"/, "", executable)
                sub(/".*$/, "", executable)
                print executable
            }
        ' "$artifact_log"
    )
    artifact_count=$(
        printf '%s\n' "$artifact_candidates" |
            awk 'NF { count += 1 } END { print count + 0 }'
    )
    rm -f "$artifact_log"
    [ "$artifact_count" -eq 1 ] || {
        echo "ERROR: expected exactly one release ay-pb executable artifact" >&2
        echo "       Cargo reported $artifact_count exact package/target/profile candidates" >&2
        exit 2
    }
    BIN=$artifact_candidates
    [ -x "$BIN" ] || {
        echo "ERROR: Cargo's ay-pb artifact is not executable: $BIN" >&2
        exit 2
    }
    source_rev_after=$(git rev-parse HEAD 2>/dev/null || printf '%s' '<unknown>')
    source_status_after=$(git status --porcelain --untracked-files=normal 2>/dev/null || true)
    if [ "$source_rev_after" != "$source_rev" ] ||
        [ -n "$source_status_after" ]
    then
        echo "ERROR: the source tree changed while Cargo was building ay-pb" >&2
        echo "       refusing to attach a moving source identity to the artifact" >&2
        exit 2
    fi
    solver_sha=$(sha256_file "$BIN") || {
        echo "ERROR: neither shasum nor sha256sum is available to identify ay-pb" >&2
        exit 2
    }
    echo "   solver: $BIN (Cargo artifact; sha256 $solver_sha)"
    echo "   source: $source_rev (clean working tree; $(cargo --version); $(rustc --version))"
    run_solver() { "$BIN" "$@"; }
fi

fail=0
note_fail() { echo "FAIL $*" >&2; fail=1; }

# ---------------------------------------------------------------- phase 2: pin
echo "== phase 2/6: pinned checker"

actual_patch_sha=$(sha256_file "$VERIPB_PATCH" 2>/dev/null || true)
if [ "$actual_patch_sha" != "$VERIPB_PATCH_SHA256" ]; then
    echo "ERROR: $VERIPB_PATCH does not match VERIPB_PATCH_SHA256 in $PIN_FILE" >&2
    echo "       pin:  $VERIPB_PATCH_SHA256" >&2
    echo "       file: ${actual_patch_sha:-<could not hash>}" >&2
    echo "       The patch defines what the trusted checker IS. Update both together." >&2
    exit 2
fi

CACHE=${VERIPB_CACHE:-"${XDG_CACHE_HOME:-$HOME/.cache}/ay-veripb"}
# Cache key covers the commit AND the patch: repatching must rebuild.
BUILD_ID="${VERIPB_COMMIT}-$(printf '%s' "$VERIPB_PATCH_SHA256" | cut -c1-12)"
BUILD_DIR="$CACHE/$BUILD_ID"

CHECKER=${VERIPB_BIN:-}
PROVENANCE="${VERIPB_COMMIT} + $(basename "$VERIPB_PATCH")"
if [ -n "$CHECKER" ]; then
    [ -x "$CHECKER" ] || { echo "ERROR: VERIPB_BIN='$CHECKER' is not executable" >&2; exit 2; }
    # Provenance is UNVERIFIED here: we did not build this binary, so the pin
    # can only be enforced behaviourally (version string + phase 2 fixtures).
    PROVENANCE="provenance unverified — supplied via VERIPB_BIN"
    echo "   using VERIPB_BIN=$CHECKER (pin build skipped; version + soundness still enforced)"
else
    CHECKER="$BUILD_DIR/target/release/veripb"
    if [ ! -x "$CHECKER" ]; then
        echo "   building pinned checker into $BUILD_DIR"
        rm -rf "$BUILD_DIR"
        mkdir -p "$CACHE"
        git clone --quiet "$VERIPB_REPO" "$BUILD_DIR"
        git -C "$BUILD_DIR" checkout --quiet "$VERIPB_COMMIT"
        got=$(git -C "$BUILD_DIR" rev-parse HEAD)
        [ "$got" = "$VERIPB_COMMIT" ] || {
            echo "ERROR: checkout landed on $got, pin says $VERIPB_COMMIT" >&2
            exit 2
        }
        git -C "$BUILD_DIR" apply "$REPO/$VERIPB_PATCH"
        ( cd "$BUILD_DIR" && cargo build --release --quiet --bin veripb )
    else
        echo "   reusing cached pinned build $BUILD_DIR"
    fi
fi

reported=$("$CHECKER" --version 2>&1 | tail -1 | awk '{print $NF}')
if [ "$reported" != "$VERIPB_VERSION" ]; then
    echo "ERROR: checker reports version '$reported', pin says '$VERIPB_VERSION'." >&2
    echo "       Refusing to certify against an unpinned checker: a verdict only" >&2
    echo "       means something if you can say which checker produced it." >&2
    exit 2
fi
echo "   checker: $CHECKER (veripb $reported; $PROVENANCE)"

# ----------------------------------------------------------- phase 3: selftest
# The version string above proves nothing on its own: every script in
# ci/fake-checkers/ answers `--version` with `veripb 3.0.2`. This phase makes
# the binary demonstrate that it checks proofs — verifies valid UNSAT and SAT
# certificates, and refuses a false-UNSAT claim, a false-SAT claim, a garbage
# file and a proof that concludes nothing. Failing it is fatal, not a skip.
echo "== phase 3/6: checker self-test (is this binary a proof checker at all?)"
veripb_require_self_test "$CHECKER"

# ---------------------------------------------------------- phase 4: soundness
# A checker that accepts a wrong proof makes every later PASS meaningless, so
# this runs BEFORE any AY proof is checked.
echo "== phase 4/6: checker soundness fixtures (must all be REJECTED)"
soundness_rows=0
while IFS='	' read -r dir flag formula proof truth wrong; do
    case "$dir" in ''|\#*) continue;; esac
    soundness_rows=$((soundness_rows + 1))
    case_dir="$VERIPB_SOUNDNESS_DIR/$dir"
    # Rejection is judged by the shared contract (exit code + parsed verdict),
    # so `s VERIFIED NO CONCLUSION`, a parse error and silence all count as
    # rejections while any real accepting conclusion does not.
    if veripb_require_rejected "$CHECKER" "$flag" "$case_dir/$formula" \
        "$case_dir/$proof" "soundness/$dir"
    then
        printf '   rejected  %-38s (truth: %s)\n' "$dir" "$truth"
    else
        fail=1
        echo "     truth:    $truth" >&2
        echo "     expected: rejection (published 3.0.2 answers '$wrong' here)" >&2
        echo "     This checker cannot be trusted to certify anything. Do not" >&2
        echo "     move the pin onto it." >&2
    fi
done < "$VERIPB_SOUNDNESS_DIR/expected.tsv"
[ "$soundness_rows" -eq 6 ] || note_fail \
    "[soundness] expected 6 fixtures, read $soundness_rows from $VERIPB_SOUNDNESS_DIR/expected.tsv"

# -------------------------------------------------------- phase 5: job drift
# The reviewed workflow and the installed one must be the same bytes; otherwise
# "CI runs this" is an assumption rather than a fact.
#
# This repository has a standing owner decision (commit 58391bbdd) of NO
# workflows: neither file exists, and nothing here installs one. That is a
# consistent state, not drift, so it passes — but ONLY when both are absent. As
# soon as either file appears, both must exist and match, which is the case the
# check was written for.
echo "== phase 5/6: workflow install is in sync"
INSTALLED=.github/workflows/pb-certified-proofs.yml
REVIEWED=ci/github-ci.yml
if [ ! -f "$REVIEWED" ] && [ ! -f "$INSTALLED" ]; then
    echo "   no workflow on either side (repo policy: no GitHub Actions) — nothing to drift"
    echo "   NOTE: this gate therefore runs only when invoked, e.g. from scripts/ or a hook."
elif [ ! -f "$REVIEWED" ]; then
    note_fail "[workflow] $INSTALLED is installed but $REVIEWED (the reviewed copy) is missing"
elif [ ! -f "$INSTALLED" ]; then
    note_fail "[workflow] $REVIEWED exists but $INSTALLED does not — the job is not installed and will never run"
elif ! cmp -s "$REVIEWED" "$INSTALLED"; then
    note_fail "[workflow] $REVIEWED and $INSTALLED differ; the reviewed job is not the job that runs"
else
    echo "   $INSTALLED == $REVIEWED"
fi

# ------------------------------------------------------- phase 6: cert track
echo "== phase 6/6: certified track over $VERIPB_CERT_MANIFEST"
WORK=$(mktemp -d "${TMPDIR:-/tmp}/ay-pb-cert-gate.XXXXXX")
trap 'rm -rf "$WORK"' EXIT

verified=0
unverifiable=0
row=0
while IFS='	' read -r instance mode status conclusion; do
    case "$instance" in ''|\#*) continue;; esac
    row=$((row + 1))
    label=$(basename "$instance" .opb)
    proof="$WORK/$label.pbp"

    if [ ! -f "$instance" ]; then
        note_fail "[$label] manifest names a missing instance: $instance"
        continue
    fi

    run_solver pb solve --timeout "$TIMEOUT_MS" --proof "$proof" "$instance" \
        >"$WORK/$label.stdout" 2>/dev/null || true
    got=$(grep '^s ' "$WORK/$label.stdout" | head -1 || true)
    objective=$(grep '^o ' "$WORK/$label.stdout" | tail -1 | sed 's/^o //' || true)
    if [ "$got" != "$status" ]; then
        note_fail "[$label] AY said '${got:-<no s line>}', manifest says '$status'"
        continue
    fi

    if [ ! -f "$proof" ]; then
        # The exact hole this gate exists to keep closed: a success status with
        # nothing to check. Fail closed on UNKNOWN instead of reporting this.
        note_fail "[$label] AY reported '$got' but wrote NO proof file — an unbacked answer on the certified track"
        continue
    fi

    if [ "$mode" = "unverifiable" ]; then
        veripb_run "$CHECKER" --opb "$instance" "$proof"
        # Any acceptance at all — including the weaker `-u` verdict — means the
        # row is no longer unverifiable and must be promoted.
        if veripb_accepted_at_all; then
            note_fail "[$label] declared 'unverifiable' but the checker now accepts it: $VERIPB_VERDICT"
            echo "     Promote this row to mode=verify with conclusion '${VERIPB_VERDICT#s VERIFIED }'." >&2
        else
            printf '   UNCHECKABLE %-34s %-16s (checker cannot parse the formula; proof unverified)\n' \
                "$label" "$got"
            unverifiable=$((unverifiable + 1))
        fi
        continue
    fi

    # The manifest's conclusion column is checked against the conclusion AY's
    # own answer ENTAILS before it is used, so a row cannot quietly certify a
    # different claim from the one the solver made.
    if ! entailed=$(veripb_entailed_conclusion "$got" "$instance" "$objective"); then
        note_fail "[$label] AY's answer '$got' has no certifiable conclusion"
        continue
    fi
    if [ "$conclusion" != "$entailed" ]; then
        note_fail "[$label] manifest conclusion is not the one '$got' entails"
        echo "     manifest: $conclusion" >&2
        echo "     entailed: $entailed" >&2
        continue
    fi

    if veripb_require_conclusion "$CHECKER" "$instance" "$proof" "$conclusion" "$label"; then
        printf '   OK          %-34s %-16s -> %s\n' "$label" "$got" "s VERIFIED $conclusion"
        verified=$((verified + 1))
    else
        fail=1
    fi
done < "$VERIPB_CERT_MANIFEST"

[ "$row" -gt 0 ] || note_fail "[manifest] no instance rows read from $VERIPB_CERT_MANIFEST"

echo
echo "checker-verified proofs: $verified / $((row - unverifiable))   (unverifiable rows: $unverifiable)"
if [ "$fail" -ne 0 ]; then
    echo "PB CERTIFIED GATE: FAILED" >&2
    exit 1
fi
echo "PB CERTIFIED GATE: PASSED"

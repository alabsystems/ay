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
#                pinned upstream commit + the pinned patch if we do not have it),
#                and refuse to proceed if its --version disagrees with the pin.
#                2b builds and tests `veripb-core-proved`, the proved kernel the
#                pinned patch now carries. It is a workspace member NOTHING
#                depends on, so `cargo build --bin veripb` would never compile
#                it and it would rot unnoticed. See the phase body for exactly
#                what that does and does not establish.
#   3. SELFTEST  prove the resolved binary is a proof checker at all, with the
#                shared six-probe battery in scripts/lib/veripb_verdict.sh. A
#                version string is trivially forgeable — every fake checker in
#                ci/fake-checkers/ answers `--version` with `veripb 3.0.2` —
#                so the pin's version half cannot be the only identity check.
#   4. SOUNDNESS make the checker prove it is worth trusting: twenty-two committed
#                formula/proof pairs, covering all twenty-one known wrong-verdict
#                defects of published VeriPB 3.0.2, must all be REJECTED.
#                ~0.03s. Without this, phase 6 could be green against a checker
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
# The ONE cache-key authority, shared with scripts/cert_ci.sh and pinned
# byte-for-byte by the Rust resolvers' cross-language tests.
. "$REPO/scripts/lib/veripb_build_id.sh"

PIN_FILE=ci/veripb.pin
[ -f "$PIN_FILE" ] || { echo "ERROR: missing pin file $PIN_FILE" >&2; exit 2; }
# The pin is strict KEY=VALUE with no expansion, so sourcing it is safe and
# keeps ONE parser shared with the Rust side (crates/ay-test-support veripb::pin).
. "./$PIN_FILE"

for required in VERIPB_REPO VERIPB_COMMIT VERIPB_VERSION VERIPB_PATCH \
                VERIPB_PATCH_SHA256 \
                VERIPB_SOUNDNESS_DIR VERIPB_CERT_MANIFEST; do
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
# Cache key covers the commit, the patch, AND THE COMPILER: repatching must
# rebuild, and so must a toolchain change.
#
# WHY THE COMPILER IS IN THE KEY (added 2026-08-31). The gate failed with
#   error[E0514]: found crate `malachite_bigint` compiled by an incompatible
#                 version of rustc
#   FAIL [proved-core] veripb-core-proved test suite FAILED
# because the cache had been built by Homebrew rustc 1.96 and the gate was then
# run with the Trust toolchain first on PATH (installed via aterm's `atpkg`).
# One target dir, two compilers — the same defect class as sharing
# CARGO_TARGET_DIR across worktrees, and it surfaced here first because
# `veripb-core-proved`'s DOCTEST links rlibs directly.
#
# Read the failure correctly before reacting to it: the 22 soundness fixtures
# and the 11 certified-track proofs had ALREADY passed under the cached
# checker. The crate that could not link decides no verdict. So this was a
# build-hygiene failure, never a soundness one — but the gate is fail-closed
# and was right to refuse.
#
# Keying on the compiler makes each build self-consistent AND PRESERVES the
# older one. That preservation is the point: recorded census verdicts cite the
# checker by sha256, so the binary that produced them must not be silently
# replaced by a rebuild under a different compiler.
#
# The key format and the compiler-resolution rules live in ONE place,
# scripts/lib/veripb_build_id.sh (sourced above), shared with cert_ci.sh and
# pinned by the Rust resolvers' tests. This gate accepts KEYED directories
# only — never the legacy unkeyed layout — because phase 2b compiles and
# tests veripb-core-proved INSIDE the cache directory, and a directory whose
# key does not name the current compiler is exactly the mixed-rlib E0514
# hazard again. Resolvers that only RUN the cached binary (cert_ci.sh, the
# Rust gates) may keep accepting a legacy build; this gate must not.
# The Trust toolchain ships `trustdoc`, NOT `rustdoc`. Cargo looks for a binary
# literally named `rustdoc`, does not find one beside this `rustc`, and falls
# through to whatever `rustdoc` is next on PATH. Phase 2b's doctests then link
# THIS cache's rlibs with a foreign rustdoc and fail E0514 — which is exactly
# how this gate failed even after the cache was keyed by compiler: the key
# fixed the rlibs, but the tool reading them was still the wrong one. Only
# `cargo test` runs doctests, which is why `cargo build` never showed it.
# AY_VERIPB_RUSTC is the compiler the key names, resolved by the shared lib
# ($RUSTC, then rustc on PATH, then the compiler_consumer sysroot's compat rustc — a
# Trust-only machine has no bare rustc). Every cargo invocation against the
# cache directory passes it explicitly as RUSTC so the compiler in the key is
# provably the compiler that built (and re-tests) the artifact — otherwise
# cargo's own resolution could drift from the fingerprinted one.
AY_VERIPB_RUSTC=$(veripb_rustc_path) || exit 2

if [ -z "${RUSTDOC:-}" ]; then
    _rustc_dir=$(dirname "$AY_VERIPB_RUSTC")
    if [ ! -x "$_rustc_dir/rustdoc" ] && [ -x "$_rustc_dir/trustdoc" ]; then
        RUSTDOC="$_rustc_dir/trustdoc"; export RUSTDOC
        echo "   RUSTDOC=$RUSTDOC (this toolchain names it trustdoc)"
    fi
fi

BUILD_ID=$(veripb_build_id "$VERIPB_COMMIT" "$VERIPB_PATCH_SHA256") || exit 2
BUILD_DIR="$CACHE/$BUILD_ID"
# The checker is the anchor that makes every certificate claim mean anything.
# If it is about to be built by a -dev compiler, say so out loud rather than
# letting it pass unremarked.
case "$(veripb_rustc_release)" in
    *-dev|*-nightly|*-beta)
        echo "   NOTE: the pinned checker will be built by a NON-RELEASE compiler"
        echo "         ($("$AY_VERIPB_RUSTC" --version 2>&1 | head -1)). The 22 must-reject"
        echo "         fixtures below re-prove its behaviour either way, but a"
        echo "         stable compiler is the conservative choice for the anchor." ;;
esac

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
        ( cd "$BUILD_DIR" && RUSTC="$AY_VERIPB_RUSTC" cargo build --release --quiet --bin veripb )
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

# ------------------------------------------------- phase 2b: proved kernel
# The pinned patch carries `veripb-core-proved`, a Clean-proved kernel for the
# arithmetic of seven checking rules (add, multiply, divide, saturate, literal
# axiom, weaken, and the RUP-to-UNSAT reduction), plus the width guards that
# re-certify every machine-width value against unbounded Int.
#
# READ THIS BEFORE CITING IT. The crate is a workspace MEMBER THAT NOTHING
# DEPENDS ON. `cargo build --bin veripb` does not compile it and the shipped
# binary contains none of its symbols, so it decides NO verdict. Nothing in
# phases 3-6 gets more trustworthy because this phase is green.
#
# What this phase is for is narrower and still worth having: an artifact that
# no build touches is an artifact that rots, and this repo has repeatedly found
# gates that were green because they were running nothing. So the kernel is
# compiled and its tests are run on every gate invocation, and the "it is an
# island" claim above is MEASURED rather than asserted.
#
# What it deliberately does NOT do is run `clean check` on the proof itself.
# The Clean toolchain is a local unreleased build, not something CI can obtain
# or pin by hash, and as committed the kernel checks 102/105 (the DIVIDE rule,
# the RUP bridge and one arithmetic lemma fail to elaborate). Adding a proof
# check that cannot run, or one weakened to accept 102/105, would be worse than
# having none. Until the toolchain is pinnable AND the file checks clean, this
# gate makes no claim about the proof — only about the crate.
echo "== phase 2b/6: proved kernel (veripb-core-proved) builds and its tests pass"
if [ -n "${VERIPB_BIN:-}" ]; then
    echo "   SKIPPED: VERIPB_BIN supplied a prebuilt checker, so there is no"
    echo "   pinned source tree here to build the kernel from. The kernel is"
    echo "   not part of the binary either way; phases 3-6 are unaffected."
elif [ ! -d "$BUILD_DIR/veripb-core-proved" ]; then
    note_fail "[proved-core] $BUILD_DIR/veripb-core-proved is missing — the pinned patch should have created it"
else
    if ( cd "$BUILD_DIR" && RUSTC="$AY_VERIPB_RUSTC" cargo build --release --quiet -p veripb-core-proved ); then
        echo "   built     veripb-core-proved"
    else
        note_fail "[proved-core] veripb-core-proved failed to COMPILE from the pinned patch"
    fi
    # island_sync (proof text in the Rust trust surface matches clean/veripb_kernel.lean)
    # and width_guards (the machine-width re-certification the kernel's checked
    # variants describe), plus the crate's own unit tests.
    if ( cd "$BUILD_DIR" && RUSTC="$AY_VERIPB_RUSTC" cargo test --release --quiet -p veripb-core-proved ); then
        echo "   tested    veripb-core-proved (unit + island_sync + width_guards)"
    else
        note_fail "[proved-core] veripb-core-proved test suite FAILED"
    fi
    # The island claim, measured. If this fires, someone wired the kernel into
    # the checker for real — that is GOOD NEWS, and the honest response is to
    # update this phase and ci/veripb.pin to say so, not to delete the check.
    if command -v strings >/dev/null 2>&1; then
        kernel_syms=$(strings -a "$CHECKER" 2>/dev/null | grep -c 'core_proved\|VeriPbCore' || true)
        control_syms=$(strings -a "$CHECKER" 2>/dev/null | grep -c 'veripb_checker\|veripb_propagator' || true)
        # `grep -c` exits 1 on zero matches; the `|| true` above keeps `set -e`
        # happy, and these defaults keep an empty capture from making `-eq`
        # explode. A broken scan must degrade to "prove nothing", never to a
        # silent pass of the assertion below.
        kernel_syms=${kernel_syms:-0}
        control_syms=${control_syms:-0}
        if [ "$control_syms" -eq 0 ]; then
            echo "   NOTE: symbol scan found no veripb_checker/veripb_propagator either,"
            echo "   so it proves nothing here; skipping the linkage assertion."
        elif [ "$kernel_syms" -eq 0 ]; then
            echo "   linkage   0 kernel symbols in the shipped binary (control: $control_syms checker symbols)"
            echo "             — confirms the kernel decides no verdict, as documented"
        else
            note_fail "[proved-core] the shipped checker now references the proved kernel ($kernel_syms symbols), but ci/veripb.pin and ci/veripb-soundness/README.md still say it is an unused island. Update them — the docs, not this check, are what is stale."
        fi
    fi
fi

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
# TWENTY-ONE defects, TWENTY-TWO fixtures: defect 7 (normalization wrapping) has
# two manifestations with opposite wrong verdicts, so it needs two pairs. If you
# change this number, change ci/veripb.pin and ci/veripb-soundness/README.md
# with it — a count that drifts turns this gate red on bookkeeping instead of
# on a regression, which trains people to edit the number rather than read it.
[ "$soundness_rows" -eq 22 ] || note_fail \
    "[soundness] expected 22 fixtures, read $soundness_rows from $VERIPB_SOUNDNESS_DIR/expected.tsv"

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

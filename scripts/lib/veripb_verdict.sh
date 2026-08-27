# ay-script-lib: veripb-verdict
# The ONE shell-side VeriPB verdict gate. Source this; do not re-implement it.
#
# WHY THIS FILE EXISTS
# -------------------
# Every shell gate in this repo used to decide "the proof is good" with some
# variant of
#
#     verdict=$("$VERIPB" "$f" "$p" | grep '^s ')
#     case "$verdict" in "s VERIFIED"*) pass;; *) fail;; esac
#
# That test is unsound four separate ways, and all four were demonstrated:
#
#   1. PREFIX, NOT CONCLUSION. `s VERIFIED NO CONCLUSION` starts with
#      `s VERIFIED`. VeriPB prints exactly that, and exits 0, for a proof that
#      proves nothing. A SATISFIABLE instance whose proof concludes nothing
#      passed the gate.
#   2. CONCLUSION NOT COMPARED TO THE CLAIM. `s VERIFIED SATISFIABLE` passed a
#      gate guarding an UNSAT answer. A checker confirming the OPPOSITE of what
#      the solver claimed was a PASS.
#   3. EXIT CODE IGNORED. A checker that prints a correct-looking verdict and
#      then exits 1 (crashed, was killed, failed after printing) was a PASS.
#   4. NO PROOF THAT THE CHECKER IS A CHECKER. `/usr/bin/true`, a script that
#      prints a fixed `s VERIFIED UNSATISFIABLE`, and a script that parrots
#      back whatever conclusion the proof file claims all passed every gate.
#
# The contract enforced here, for every caller:
#
#   ACCEPTED  :=  checker exited 0
#             AND its stdout carries a verdict line `s VERIFIED <conclusion>`
#             AND <conclusion> is not `NO CONCLUSION` and not empty.
#   PASS      :=  ACCEPTED and <conclusion> is EXACTLY the conclusion the
#                 solver's own claimed status entails.
#
# `s UNDER WEAKENED GUARANTEES ...` (what `veripb -u` prints) is an acceptance
# but a strictly weaker one; it is never a PASS here. Anything else — a parse
# error, a missing verdict line, silence — is a rejection.
#
# Callers must also pass an explicit formula-format flag. Letting VeriPB guess
# the parser from the file extension has bitten this repo before, and `--opb`
# is what every AY-emitted certificate is checked against.
#
# This is the shell twin of crates/ay-test-support/src/veripb.rs. The two
# implement the same contract, including the same self-test battery, so a fake
# checker cannot pass one surface by failing the other.

# ---------------------------------------------------------------- primitives

# veripb_status_conclusion <ay `s ...` status line>
#
# Maps a solver status to the checker conclusion it entails, for the statuses
# whose entailed conclusion is fixed. `s OPTIMUM FOUND` is deliberately absent:
# its conclusion is `BOUNDS v <= obj <= v` for the specific optimum v, which
# the caller must state, because that value is the whole claim.
veripb_status_conclusion() {
    case "$1" in
        "s UNSATISFIABLE") echo "UNSATISFIABLE" ;;
        "s SATISFIABLE")   echo "SATISFIABLE" ;;
        *) return 1 ;;
    esac
}

# veripb_bounds_conclusion <optimum>
veripb_bounds_conclusion() {
    echo "BOUNDS $1 <= obj <= $1"
}

# veripb_entailed_conclusion <status> <instance> <objective-or-empty>
#
# The conclusion a solver status ENTAILS for this instance, printed on stdout.
# This is what turns "the checker verified something" into "the checker
# verified what AY claimed":
#
#   s SATISFIABLE    -> SATISFIABLE
#   s UNSATISFIABLE  -> UNSATISFIABLE for a decision instance;
#                       BOUNDS INF <= obj <= INF when the instance has an
#                       objective (VeriPB restates infeasible optimisation as
#                       an empty bound interval, not as UNSATISFIABLE)
#   s OPTIMUM FOUND  -> BOUNDS v <= obj <= v for the objective value v the
#                       solver itself printed. An `s OPTIMUM FOUND` with no
#                       `o ` line has no optimum to certify and is an error.
#
# Returns non-zero, with a reason on stderr, for any status whose entailed
# conclusion is not defined — never a default, never a pass.
veripb_entailed_conclusion() {
    _vg_status=$1; _vg_instance=$2; _vg_obj=${3:-}
    case "$_vg_status" in
        "s SATISFIABLE")
            echo "SATISFIABLE"
            ;;
        "s UNSATISFIABLE")
            if grep -qE '^(min|max):' "$_vg_instance"; then
                echo "BOUNDS INF <= obj <= INF"
            else
                echo "UNSATISFIABLE"
            fi
            ;;
        "s OPTIMUM FOUND")
            if [ -z "$_vg_obj" ]; then
                echo "'$_vg_status' came with no 'o ' objective line: there is no optimum to certify" >&2
                return 1
            fi
            veripb_bounds_conclusion "$_vg_obj"
            ;;
        *)
            echo "no checker conclusion is defined for solver status '$_vg_status'" >&2
            return 1
            ;;
    esac
    return 0
}

# veripb_run <checker> <format-flag> <formula> <proof>
#
# Runs the checker and publishes the result in three globals:
#   VERIPB_EXIT     the checker's exit code
#   VERIPB_VERDICT  its first `s ...` line, or the empty string
#   VERIPB_OUTPUT   combined stdout+stderr (diagnostics only)
#
# stderr is folded into VERIPB_OUTPUT for reporting, but the verdict is taken
# from stdout ALONE: a checker must not be able to satisfy a gate by writing a
# success line to the wrong stream.
# NOTE ON THE TEMP-DIR VARIABLE. It is `_vg_rundir`, deliberately not `_vg_dir`.
# POSIX sh has no locals, so every `_vg_*` name here is global and this function
# is called from inside loops that hold their own state. `_vg_dir` used to be
# this scratch path AND the fixture root in veripb_soundness_probe: the first
# call reassigned it to a mktemp path and then `rm -rf`'d it, so from the second
# fixture on every path pointed into a deleted directory, the checker could not
# open the files, printed no `s` line, and the probe scored that silence as a
# REJECTION. Eight of nine fixtures were vacuous and the probe reported "PASSED
# (9/9 refused)" for a checker that accepted all nine. Do not reuse `_vg_dir`.
veripb_run() {
    _vg_checker=$1; _vg_flag=$2; _vg_formula=$3; _vg_proof=$4
    _vg_rundir=$(mktemp -d "${TMPDIR:-/tmp}/ay-veripb-run.XXXXXX")
    VERIPB_EXIT=0
    "$_vg_checker" "$_vg_flag" "$_vg_formula" "$_vg_proof" \
        >"$_vg_rundir/out" 2>"$_vg_rundir/err" || VERIPB_EXIT=$?
    VERIPB_VERDICT=$(grep '^s ' "$_vg_rundir/out" 2>/dev/null | head -1 \
        | sed 's/[[:space:]]*$//' || true)
    VERIPB_OUTPUT=$(cat "$_vg_rundir/out" "$_vg_rundir/err" 2>/dev/null || true)
    rm -rf "$_vg_rundir"
    return 0
}

# veripb_accepted — true when the LAST veripb_run was a real acceptance.
#
# Exit code 0 is required. VeriPB exits 0 for `s VERIFIED NO CONCLUSION` (so
# exit code alone is not a gate either) but it exits non-zero whenever it
# refuses a proof, so a non-zero exit beside an accepting-looking line means the
# run is not trustworthy. Fail closed.
veripb_accepted() {
    [ "${VERIPB_EXIT:-1}" -eq 0 ] || return 1
    case "${VERIPB_VERDICT:-}" in
        "s VERIFIED NO CONCLUSION") return 1 ;;
        "s VERIFIED") return 1 ;;
        "s VERIFIED "*) return 0 ;;
        *) return 1 ;;
    esac
}

# veripb_accepted_at_all — true when the LAST veripb_run was an acceptance at
# ANY guarantee level, including the weaker `s UNDER WEAKENED GUARANTEES ...`
# that `veripb -u` prints.
#
# Used only to decide REJECTION. A weakened acceptance is not good enough to
# certify an answer (so [`veripb_accepted`] excludes it), but it is far too good
# to count as a refusal: a checker that answers `s UNDER WEAKENED GUARANTEES
# SATISFIABLE` for an UNSATISFIABLE soundness fixture has accepted a proof that
# contradicts the truth, and must fail the soundness gate. Treating that as a
# "rejection" is exactly how a checker bug would slip through.
veripb_accepted_at_all() {
    if veripb_accepted; then
        return 0
    fi
    [ "${VERIPB_EXIT:-1}" -eq 0 ] || return 1
    case "${VERIPB_VERDICT:-}" in
        "s UNDER WEAKENED GUARANTEES NO CONCLUSION") return 1 ;;
        "s UNDER WEAKENED GUARANTEES") return 1 ;;
        "s UNDER WEAKENED GUARANTEES "*) return 0 ;;
        *) return 1 ;;
    esac
}

# veripb_report <label> <what was expected>
veripb_report() {
    echo "     checker exit: ${VERIPB_EXIT:-<none>}" >&2
    echo "     verdict line: ${VERIPB_VERDICT:-<no 's ...' verdict line>}" >&2
    echo "     expected:     $2" >&2
    echo "     checker output follows:" >&2
    printf '%s\n' "${VERIPB_OUTPUT:-}" | sed 's/^/       | /' >&2
}

# ------------------------------------------------------------------- gates

# veripb_require_conclusion <checker> <formula> <proof> <conclusion> <label>
#
# The main gate: PASS iff the checker exits 0 AND its verdict line is EXACTLY
# `s VERIFIED <conclusion>`. The conclusion is supplied by the caller from the
# solver's own claimed status, so a checker that confirms a DIFFERENT truth
# than the one being claimed is a failure, not a pass.
veripb_require_conclusion() {
    _vg_want=$4; _vg_label=$5
    veripb_run "$1" --opb "$2" "$3"
    if veripb_accepted && [ "$VERIPB_VERDICT" = "s VERIFIED $_vg_want" ]; then
        return 0
    fi
    echo "FAIL [$_vg_label]: the checker did not confirm the claimed conclusion" >&2
    veripb_report "$_vg_label" "s VERIFIED $_vg_want (exit 0)"
    return 1
}

# veripb_require_rejected <checker> <format-flag> <formula> <proof> <label>
#
# PASS iff the checker did NOT accept. Used for the soundness fixtures and for
# the self-test battery below.
veripb_require_rejected() {
    _vg_label=$5
    veripb_run "$1" "$2" "$3" "$4"
    if veripb_accepted_at_all; then
        echo "FAIL [$_vg_label]: the checker ACCEPTED a proof that must be rejected" >&2
        veripb_report "$_vg_label" "rejection (no accepting verdict)"
        return 1
    fi
    return 0
}

# --------------------------------------------------------------- self-test

# veripb_self_test <checker>
#
# Prove the binary is a proof checker before any of its verdicts is believed.
# Six probes, each of which some real fake checker passes all the others of:
#
#   good-unsat    a valid refutation must yield EXACTLY
#                 `s VERIFIED UNSATISFIABLE` AND exit 0.
#                 Rejects: silent exit-0 binaries (/usr/bin/true), always-reject
#                 binaries (/usr/bin/false), and checkers that print the right
#                 verdict but exit non-zero.
#   good-sat      a satisfiable formula with a genuine solution must yield
#                 EXACTLY `s VERIFIED SATISFIABLE`.
#                 Rejects: binaries that print one hard-coded verdict, whatever
#                 the input.
#   false-unsat   a SATISFIABLE formula with a proof claiming UNSAT must be
#                 rejected.
#                 Rejects: `s VERIFIED UNSATISFIABLE` rubber stamps.
#   false-sat     a proof claiming SAT whose stated solution FALSIFIES the
#                 formula must be rejected.
#                 Rejects: parrots — a checker that reads the proof's own
#                 `conclusion` line and echoes back the matching verdict passes
#                 every probe above and fails here.
#   garbage       a file that is not a proof at all must be rejected.
#                 Rejects: parrots and rubber stamps a second, independent way.
#   no-conclusion a well-formed proof that concludes NOTHING must not be
#                 treated as an acceptance. Real VeriPB prints
#                 `s VERIFIED NO CONCLUSION` and exits 0 here, so this probe is
#                 aimed at the GATE, not only at the checker: it is the exact
#                 string that used to satisfy `case $v in "s VERIFIED"*)`.
#
# Returns 0 when every probe holds. On failure it prints what went wrong and
# returns 1; callers must treat that as fatal — a verdict from a binary that
# fails this battery is not evidence of anything.
veripb_self_test() {
    _vg_checker=$1
    [ -x "$_vg_checker" ] || {
        echo "ERROR: checker '$_vg_checker' is not executable" >&2
        return 1
    }
    _vg_st=$(mktemp -d "${TMPDIR:-/tmp}/ay-veripb-selftest.XXXXXX")
    _vg_bad=0

    # A refutation of x1 >= 1 /\ -x1 >= 0.
    printf '* #variable= 1 #constraint= 2\n+1 x1 >= 1 ;\n-1 x1 >= 0 ;\n' \
        > "$_vg_st/unsat.opb"
    printf 'pseudo-Boolean proof version 3.0\nf 2 ;\npol 1 2 +;\nrup >= 1 ;\noutput NONE;\nconclusion UNSAT : 4;\nend pseudo-Boolean proof;\n' \
        > "$_vg_st/good-unsat.pbp"
    # Same formula, a proof that derives and concludes nothing.
    printf 'pseudo-Boolean proof version 3.0\nf 2 ;\noutput NONE;\nconclusion NONE;\nend pseudo-Boolean proof;\n' \
        > "$_vg_st/no-conclusion.pbp"
    # A SATISFIABLE formula.
    printf '* #variable= 2 #constraint= 1\n+1 x1 +1 x2 >= 1 ;\n' \
        > "$_vg_st/sat.opb"
    printf 'pseudo-Boolean proof version 3.0\nf 1 ;\noutput NONE;\nconclusion SAT : x1 ~x2;\nend pseudo-Boolean proof;\n' \
        > "$_vg_st/good-sat.pbp"
    # ...claimed UNSAT, citing a satisfiable input row as the contradiction.
    printf 'pseudo-Boolean proof version 3.0\nf 1 ;\noutput NONE;\nconclusion UNSAT : 1;\nend pseudo-Boolean proof;\n' \
        > "$_vg_st/false-unsat.pbp"
    # ...claimed SAT with an assignment that falsifies the one constraint.
    printf 'pseudo-Boolean proof version 3.0\nf 1 ;\noutput NONE;\nconclusion SAT : ~x1 ~x2;\nend pseudo-Boolean proof;\n' \
        > "$_vg_st/false-sat.pbp"
    printf 'this file is not a pseudo-Boolean proof\n' > "$_vg_st/garbage.pbp"

    veripb_run "$_vg_checker" --opb "$_vg_st/unsat.opb" "$_vg_st/good-unsat.pbp"
    if ! veripb_accepted || [ "$VERIPB_VERDICT" != "s VERIFIED UNSATISFIABLE" ]; then
        echo "FAIL [checker-self-test/good-unsat]: it did not verify a valid refutation" >&2
        veripb_report good-unsat "s VERIFIED UNSATISFIABLE (exit 0)"
        _vg_bad=1
    fi

    veripb_run "$_vg_checker" --opb "$_vg_st/sat.opb" "$_vg_st/good-sat.pbp"
    if ! veripb_accepted || [ "$VERIPB_VERDICT" != "s VERIFIED SATISFIABLE" ]; then
        echo "FAIL [checker-self-test/good-sat]: it did not verify a valid solution" >&2
        veripb_report good-sat "s VERIFIED SATISFIABLE (exit 0)"
        _vg_bad=1
    fi

    veripb_require_rejected "$_vg_checker" --opb "$_vg_st/sat.opb" \
        "$_vg_st/false-unsat.pbp" "checker-self-test/false-unsat" || _vg_bad=1
    veripb_require_rejected "$_vg_checker" --opb "$_vg_st/sat.opb" \
        "$_vg_st/false-sat.pbp" "checker-self-test/false-sat" || _vg_bad=1
    veripb_require_rejected "$_vg_checker" --opb "$_vg_st/unsat.opb" \
        "$_vg_st/garbage.pbp" "checker-self-test/garbage" || _vg_bad=1
    veripb_require_rejected "$_vg_checker" --opb "$_vg_st/unsat.opb" \
        "$_vg_st/no-conclusion.pbp" "checker-self-test/no-conclusion" || _vg_bad=1

    rm -rf "$_vg_st"
    if [ "$_vg_bad" -ne 0 ]; then
        echo "ERROR: '$_vg_checker' failed the VeriPB self-test." >&2
        echo "       Refusing to certify anything against a binary that cannot be" >&2
        echo "       shown to check proofs. This is not a skip: fix the checker." >&2
        return 1
    fi
    return 0
}

# veripb_require_self_test <checker>
#
# Self-test or die. Every gate calls this BEFORE it trusts a verdict.
veripb_require_self_test() {
    if veripb_self_test "$1"; then
        echo "   checker self-test: PASSED (6/6 probes)"
        return 0
    fi
    exit 3
}

# ------------------------------------------------------------------ hashing

# sha256_file <path>
#
# Hex sha256 of a file, or non-zero when no hasher is available. Shared so the
# checker PIN can be enforced identically by every gate that reads it.
sha256_file() {
    if command -v shasum >/dev/null 2>&1; then
        shasum -a 256 "$1" | awk '{print $1}'
    elif command -v sha256sum >/dev/null 2>&1; then
        sha256sum "$1" | awk '{print $1}'
    else
        return 1
    fi
}

# ------------------------------------------------------- soundness fixtures

# veripb_soundness_probe <checker> <soundness-dir>
#
# The self-test battery above proves a binary BEHAVES like a proof checker. It
# does not prove the binary is a CORRECT one, and that gap is not theoretical:
# published VeriPB 3.0.2 passes all six self-test probes while answering
# `s VERIFIED UNSATISFIABLE` for satisfiable formulas (fixtures 03, 04 and 07)
# and `s VERIFIED SATISFIABLE` for unsatisfiable ones (05, 06 and 08). That is
# why ci/veripb.pin pins a COMMIT AND ITS PATCHES rather than a version number.
#
# This probe faces the checker with the TWENTY-TWO formula/proof pairs whose
# verdicts are known to contradict the truth — twenty-two pairs for TWENTY-ONE
# defects, because defect 7 (normalization wrapping) has two manifestations with
# opposite wrong verdicts. A checker AY is willing to certify against must refuse
# all twenty-two.
# Rejection here means "printed no accepting `s ...` line at any guarantee
# level" — `s VERIFIED NO CONCLUSION` is a rejection, and so is a parse error
# with no `s` line. It does NOT mean "the checker produced no output": see the
# readability guard in the loop below for why that distinction is load-bearing.
#
# <soundness-dir> is VERIPB_SOUNDNESS_DIR from ci/veripb.pin, relative to the
# repo root. Returns 0 only when every fixture is refused.
veripb_soundness_probe() {
    _vg_checker=$1
    _vg_root=$2
    _vg_expected="$_vg_root/expected.tsv"
    [ -r "$_vg_expected" ] || {
        echo "ERROR: soundness fixture manifest missing: $_vg_expected" >&2
        return 1
    }
    _vg_bad=0
    _vg_seen=0
    # POSIX read loop over the manifest; '#' and blank lines are comments.
    while IFS='	' read -r _vg_name _vg_flag _vg_formula _vg_proof _vg_truth _vg_wrong; do
        case "$_vg_name" in ''|'#'*) continue ;; esac
        _vg_seen=$((_vg_seen + 1))
        # A missing input is a BROKEN PROBE, never a rejection. The contract
        # scores "printed no accepting `s` line" as a refusal, so a checker that
        # cannot open its arguments looks exactly like a checker that refused
        # them — which is how a clobbered fixture root once turned eight of the
        # rows into free passes. Unreadable inputs fail loudly instead.
        if [ ! -r "$_vg_root/$_vg_name/$_vg_formula" ] \
           || [ ! -r "$_vg_root/$_vg_name/$_vg_proof" ]; then
            echo "ERROR: soundness fixture $_vg_name is unreadable under $_vg_root" >&2
            echo "       expected $_vg_root/$_vg_name/{$_vg_formula,$_vg_proof}" >&2
            echo "       Refusing to score an unopenable fixture as a rejection." >&2
            _vg_bad=1
            continue
        fi
        veripb_require_rejected "$_vg_checker" "$_vg_flag" \
            "$_vg_root/$_vg_name/$_vg_formula" "$_vg_root/$_vg_name/$_vg_proof" \
            "checker-soundness/$_vg_name" || {
            echo "       truth is '$_vg_truth'; an unfixed checker answers '$_vg_wrong'" >&2
            _vg_bad=1
        }
    done < "$_vg_expected"
    # A manifest that parsed to nothing would make this gate vacuous, which is
    # the exact failure mode it exists to prevent.
    if [ "$_vg_seen" -eq 0 ]; then
        echo "ERROR: soundness manifest $_vg_expected yielded no fixtures" >&2
        return 1
    fi
    [ "$_vg_bad" -eq 0 ] || return 1
    echo "   checker soundness: PASSED ($_vg_seen/$_vg_seen wrong-verdict fixtures refused)"
    return 0
}

# veripb_require_soundness <checker> <soundness-dir>
#
# Soundness fixtures or die. A gate that skips this can certify AY's answers
# against a checker that calls satisfiable formulas unsatisfiable.
veripb_require_soundness() {
    veripb_soundness_probe "$1" "$2" && return 0
    echo "ERROR: the resolved checker gave a verdict contradicting known truth." >&2
    echo "       Refusing to certify against it. Build the pinned checker per" >&2
    echo "       ci/veripb.pin (commit + reviewed patches), not an unpinned clone." >&2
    exit 3
}

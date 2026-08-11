#!/usr/bin/env bash
# ay-script: critical-solver-policy-gate
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0
#
# check_critical_solver_policy.sh — enforce that changes to critical solver
# files land with evidence of the checked-in native solver gate.

set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

usage() {
    cat >&2 <<'EOF'
Usage:
  bash scripts/check_critical_solver_policy.sh --staged --message-file <path>
  bash scripts/check_critical_solver_policy.sh --paths-file <path> --message-file <path> [--context <label>]
  bash scripts/check_critical_solver_policy.sh --commit <rev>
  bash scripts/check_critical_solver_policy.sh --rev-range <range>
EOF
}

is_explicit_critical_solver_test_path() {
    local path="$1"

    case "$path" in
        benchmarks/consumers/external_codegen/atomic-bv-identity-bvsub-eq-bvadd-bvneg.smt2 | \
        benchmarks/consumers/external_codegen/bv-strength-reduction-mul3-eq-add3.smt2 | \
        benchmarks/consumers/external_codegen/fp16-add-commutativity.smt2 | \
        crates/ay/tests/group_cli.rs | \
        crates/ay/tests/group_cli/external_codegen_consumer_canaries_8870.rs | \
        crates/ay-dpll/tests/group_differential.rs | \
        crates/ay-dpll/tests/group_differential/external_codegen_consumer_differential_8870.rs | \
        crates/ay-dpll/tests/group_fp.rs | \
        crates/ay-dpll/tests/group_fp/external_codegen_fp16_commutativity_8870.rs)
            return 0
            ;;
    esac

    return 1
}

is_critical_solver_path() {
    local path="$1"

    if is_explicit_critical_solver_test_path "$path"; then
        return 0
    fi

    case "$path" in
        .github/workflows/solver-gate.yml | \
        crates/ay/src/cmd_gate.rs | \
        crates/ay/src/main.rs | \
        crates/ay/build.rs | \
        crates/ay-dpll/build.rs | \
        crates/ay-dpll/src/executor/* | \
        crates/ay-dpll/src/executor.rs | \
        crates/ay-sat/src/* | \
        scripts/check_critical_solver_policy.sh | \
        scripts/ay_binary_policy.sh)
            ;;
        *)
            return 1
            ;;
    esac

    case "$path" in
        */tests/* | */tests.rs | *_tests.rs)
            return 1
            ;;
    esac

    return 0
}

title_is_incomplete_checkpoint() {
    local title="$1"
    printf '%s\n' "$title" | grep -qiE '(^|:[[:space:]]*)\[INCOMPLETE\]([[:space:]]|$)'
}

extract_verified_section() {
    local message_file="$1"
    sed -n '/^## Verified/,$p' "$message_file" | sed -n '1p; 2,${ /^## /q; p; }'
}

is_checked_in_solver_gate_command() {
    local command="$1"

    command="${command#"${command%%[![:space:]]*}"}"
    command="${command%"${command##*[![:space:]]}"}"
    [[ "$command" == "cargo run --locked -p ay --features cli -- gate solver" ]]
}

verified_has_solver_gate_evidence() {
    local message_file="$1"
    local verified_section
    local line
    local command

    verified_section="$(extract_verified_section "$message_file")"
    [[ -n "$verified_section" ]] || return 1

    while IFS= read -r line; do
        printf '%s\n' "$line" | grep -qE '^[[:space:]]*(([-*$])|([0-9]+[.)]))[[:space:]]' || continue
        [[ "$line" == *"solver-gate:"* ]] || continue

        command="${line#*solver-gate:}"
        if is_checked_in_solver_gate_command "$command"; then
            return 0
        fi
    done <<<"$verified_section"

    return 1
}

print_critical_paths() {
    local paths_file="$1"
    local path

    while IFS= read -r path; do
        [[ -n "$path" ]] || continue
        is_critical_solver_path "$path" || continue
        echo "     $path" >&2
    done <"$paths_file"
}

paths_file_has_critical() {
    local paths_file="$1"
    local path

    while IFS= read -r path; do
        [[ -n "$path" ]] || continue
        if is_critical_solver_path "$path"; then
            return 0
        fi
    done <"$paths_file"

    return 1
}

append_critical_paths() {
    local paths_file="$1"
    local output_file="$2"
    local path

    while IFS= read -r path; do
        [[ -n "$path" ]] || continue
        is_critical_solver_path "$path" || continue
        printf '%s\n' "$path" >>"$output_file"
    done <"$paths_file"
}

check_message_and_paths() {
    local context_label="$1"
    local paths_file="$2"
    local message_file="$3"
    local title
    local failed=false
    local has_critical=false

    if paths_file_has_critical "$paths_file"; then
        has_critical=true
    fi

    [[ "$has_critical" == "true" ]] || return 0

    title="$(sed -n '1p' "$message_file")"

    if title_is_incomplete_checkpoint "$title"; then
        echo "" >&2
        echo "ERROR: [INCOMPLETE] commits cannot include critical solver files." >&2
        echo "   Context: ${context_label}" >&2
        echo "   Critical solver files:" >&2
        print_critical_paths "$paths_file"
        echo "   Rewrite the title as a normal commit before landing solver changes." >&2
        echo "" >&2
        failed=true
    fi

    if ! verified_has_solver_gate_evidence "$message_file"; then
        echo "" >&2
        echo "ERROR: Critical solver changes require evidence of the checked-in solver gate." >&2
        echo "   Context: ${context_label}" >&2
        echo "   Critical solver files:" >&2
        print_critical_paths "$paths_file"
        echo "   Add a line in ## Verified that runs the checked-in native solver gate, for example:" >&2
        echo "     - solver-gate: cargo run --locked -p ay --features cli -- gate solver" >&2
        echo "       [solver-gate output]" >&2
        echo "   Ad hoc cargo test or other gate lines do not satisfy this policy." >&2
        echo "" >&2
        failed=true
    fi

    [[ "$failed" == "false" ]]
}

check_staged() {
    local message_file="$1"
    local paths_file
    local status=0

    paths_file="$(mktemp "${TMPDIR:-/tmp}/critical-solver-staged.XXXXXX")"
    git diff --cached --name-only --diff-filter=ACMRD >"$paths_file"
    if ! check_message_and_paths "staged changes" "$paths_file" "$message_file"; then
        status=1
    fi
    rm -f "$paths_file"
    return "$status"
}

check_commit() {
    local commit="$1"
    local paths_file
    local message_file
    local status=0
    local title

    paths_file="$(mktemp "${TMPDIR:-/tmp}/critical-solver-paths.XXXXXX")"
    message_file="$(mktemp "${TMPDIR:-/tmp}/critical-solver-msg.XXXXXX")"

    git diff-tree --root --no-commit-id --name-only -r -m --diff-filter=ACMRD "$commit" | sort -u >"$paths_file"
    git log -1 --format=%B "$commit" >"$message_file"
    title="$(git log -1 --format=%s "$commit")"

    if ! check_message_and_paths "commit ${commit} (${title})" "$paths_file" "$message_file"; then
        status=1
    fi

    rm -f "$paths_file" "$message_file"
    return "$status"
}

check_range() {
    local range="$1"
    local tmpdir
    local aggregate_paths
    local tip_commit=""
    local tip_title=""
    local tip_message_file=""
    local commit
    local paths_file
    local message_file
    local title
    local status=0

    tmpdir="$(mktemp -d "${TMPDIR:-/tmp}/critical-solver-range.XXXXXX")"
    aggregate_paths="${tmpdir}/critical-paths.txt"
    : >"$aggregate_paths"

    while IFS= read -r commit; do
        [[ -n "$commit" ]] || continue
        tip_commit="$commit"
        tip_title="$(git log -1 --format=%s "$commit")"

        paths_file="${tmpdir}/${commit}.paths"
        message_file="${tmpdir}/${commit}.msg"

        git diff-tree --root --no-commit-id --name-only -r -m --diff-filter=ACMRD "$commit" | sort -u >"$paths_file"
        git log -1 --format=%B "$commit" >"$message_file"
        title="$(sed -n '1p' "$message_file")"

        if paths_file_has_critical "$paths_file"; then
            append_critical_paths "$paths_file" "$aggregate_paths"

            if title_is_incomplete_checkpoint "$title"; then
                echo "" >&2
                echo "ERROR: [INCOMPLETE] commits cannot appear in a critical solver landing range." >&2
                echo "   Context: landing range ${range} includes commit ${commit} (${title})" >&2
                echo "   Critical solver files:" >&2
                print_critical_paths "$paths_file"
                echo "   Rewrite the title as a normal commit before landing solver changes." >&2
                echo "" >&2
                status=1
            fi
        fi
    done < <(git rev-list --reverse "$range")

    if [[ -z "$tip_commit" || ! -s "$aggregate_paths" ]]; then
        rm -rf "$tmpdir"
        return "$status"
    fi

    tip_message_file="${tmpdir}/tip.msg"
    git log -1 --format=%B "$tip_commit" >"$tip_message_file"

    if title_is_incomplete_checkpoint "$tip_title"; then
        echo "" >&2
        echo "ERROR: Critical solver landing ranges cannot terminate in an [INCOMPLETE] commit." >&2
        echo "   Context: landing range ${range} (tip ${tip_commit} (${tip_title}))" >&2
        echo "" >&2
        status=1
    fi

    if ! verified_has_solver_gate_evidence "$tip_message_file"; then
        echo "" >&2
        echo "ERROR: Critical solver landing ranges require checked-in solver-gate verification on the tip commit." >&2
        echo "   Context: landing range ${range} (tip ${tip_commit} (${tip_title}))" >&2
        echo "   Critical solver files touched somewhere in the range:" >&2
        print_critical_paths "$aggregate_paths"
        echo "   Add a line in the tip commit's ## Verified section that runs the checked-in native solver gate, for example:" >&2
        echo "     - solver-gate: cargo run --locked -p ay --features cli -- gate solver" >&2
        echo "       [solver-gate output]" >&2
        echo "" >&2
        status=1
    fi

    rm -rf "$tmpdir"
    return "$status"
}

MODE=""
MESSAGE_FILE=""
PATHS_FILE=""
CONTEXT_LABEL="provided paths"
REV_RANGE=""
COMMIT_REV=""

while [[ $# -gt 0 ]]; do
    case "$1" in
        --staged)
            MODE="staged"
            ;;
        --message-file)
            MESSAGE_FILE="${2:-}"
            shift
            ;;
        --paths-file)
            MODE="paths"
            PATHS_FILE="${2:-}"
            shift
            ;;
        --context)
            CONTEXT_LABEL="${2:-}"
            shift
            ;;
        --rev-range)
            MODE="range"
            REV_RANGE="${2:-}"
            shift
            ;;
        --commit)
            MODE="commit"
            COMMIT_REV="${2:-}"
            shift
            ;;
        -h | --help)
            usage
            exit 0
            ;;
        *)
            usage
            exit 2
            ;;
    esac
    shift
done

case "$MODE" in
    staged)
        [[ -n "$MESSAGE_FILE" ]] || { usage; exit 2; }
        check_staged "$MESSAGE_FILE"
        ;;
    paths)
        [[ -n "$PATHS_FILE" && -n "$MESSAGE_FILE" ]] || { usage; exit 2; }
        check_message_and_paths "$CONTEXT_LABEL" "$PATHS_FILE" "$MESSAGE_FILE"
        ;;
    range)
        [[ -n "$REV_RANGE" ]] || { usage; exit 2; }
        check_range "$REV_RANGE"
        ;;
    commit)
        [[ -n "$COMMIT_REV" ]] || { usage; exit 2; }
        check_commit "$COMMIT_REV"
        ;;
    *)
        usage
        exit 2
        ;;
esac

#!/usr/bin/env bash
# ay-script: mzn-local-bench
# Copyright 2026 Andrew Yates
# Author: Andrew Yates
# Licensed under the Apache License, Version 2.0

set -u

# Run local FlatZinc benchmarks through the same CLI surface used by the
# MiniZinc 2026 wrapper.
#
# Usage:
#   benchmarks/minizinc/run_benchmarks.sh [timeout_ms] [core|challenge|guard|all]
#
# Environment:
#   AY_MINIZINC_BIN       ay binary to execute
#   AY_MINIZINC_STRICT    fail if any benchmark errors (default: 1)
#   AY_MINIZINC_REQUIRE_SOLVED
#                         minimum solved count required for this sweep
#   AY_MINIZINC_PROCESS_TIMEOUT_S
#                         external process cap in seconds (default: ceil(timeout_ms/1000)+1)
#   AY_MINIZINC_EXPECT
#                         comma-separated expectations:
#                         benchmark=RESULT or benchmark=RESULT|detail-substring

TIMEOUT_MS="${1:-10000}"
SCOPE="${2:-core}"

script_dir="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
repo_root="$(CDPATH= cd -- "$script_dir/../.." && pwd)"
bench_dir="$repo_root/benchmarks/minizinc"

ay_bin="${AY_MINIZINC_BIN:-}"
if [[ -z "$ay_bin" && -x "$repo_root/target/debug/ay" ]]; then
    ay_bin="$repo_root/target/debug/ay"
fi
if [[ -z "$ay_bin" && -x "$repo_root/target/release/ay" ]]; then
    ay_bin="$repo_root/target/release/ay"
fi

if [[ -z "$ay_bin" || ! -x "$ay_bin" ]]; then
    echo "ERROR: ay binary not found; set AY_MINIZINC_BIN or build target/debug/ay" >&2
    exit 1
fi

case "$SCOPE" in
    core|challenge|guard|all) ;;
    *)
        echo "ERROR: scope must be one of: core, challenge, guard, all" >&2
        exit 1
        ;;
esac

STRICT="${AY_MINIZINC_STRICT:-1}"
REQUIRE_SOLVED="${AY_MINIZINC_REQUIRE_SOLVED:-0}"
process_timeout_s="${AY_MINIZINC_PROCESS_TIMEOUT_S:-$(( (TIMEOUT_MS + 999) / 1000 + 1 ))}"

solved=0
total=0
failed=0
timeout=0
unknown=0
timeout_incumbent=0
expect_failed=0
expect_seen=","

tmp_dir="$(mktemp -d "${TMPDIR:-/tmp}/ay-minizinc-bench.XXXXXX")"
trap 'rm -rf "$tmp_dir"' EXIT

add_files() {
    local dir="$1"
    find "$dir" -maxdepth 1 -type f -name '*.fzn' | sort
}

guard_files() {
    printf '%s\n' \
        "$bench_dir/challenge/array_var_element_fallback_proxy.fzn" \
        "$bench_dir/challenge/black_hole_0.fzn" \
        "$bench_dir/challenge/costas_10.fzn" \
        "$bench_dir/challenge/jobshop_abz5.fzn" \
        "$bench_dir/challenge/steiner_09.fzn" \
        "$bench_dir/community_detect_s26.fzn"
}

latest_objective_line() {
    local fzn="$1"
    local out_file="$2"
    local objective

    objective="$(sed -n -E 's/^solve[[:space:]].*(minimize|maximize)[[:space:]]+([A-Za-z_][A-Za-z0-9_]*)[[:space:]]*;.*/\2/p' "$fzn" | tail -1)"
    if [[ -n "$objective" ]]; then
        grep -E "^${objective} = [-0-9]+;" "$out_file" | tail -1
    else
        grep -E '^[A-Za-z_][A-Za-z0-9_]* = [-0-9]+;' "$out_file" | tail -1
    fi
}

check_expectation() {
    local name="$1"
    local result="$2"
    local detail="$3"
    local spec expected_name expected_rest expected_result expected_detail

    if [[ -z "${AY_MINIZINC_EXPECT:-}" ]]; then
        return
    fi

    local old_ifs="$IFS"
    IFS=,
    for spec in $AY_MINIZINC_EXPECT; do
        IFS="$old_ifs"
        expected_name="${spec%%=*}"
        expected_rest="${spec#*=}"
        expected_result="${expected_rest%%|*}"
        expected_detail=""
        if [[ "$expected_rest" == *"|"* ]]; then
            expected_detail="${expected_rest#*|}"
        fi

        if [[ "$expected_name" != "$name" ]]; then
            IFS=,
            continue
        fi

        if [[ "$expect_seen" != *",$name,"* ]]; then
            expect_seen="${expect_seen}${name},"
        fi

        if [[ "$expected_result" != "$result" ]]; then
            printf "EXPECTATION FAILED: %s result %s != %s\n" "$name" "$result" "$expected_result" >&2
            expect_failed=$((expect_failed + 1))
        elif [[ -n "$expected_detail" && "$detail" != *"$expected_detail"* ]]; then
            printf "EXPECTATION FAILED: %s detail does not contain %s\n" "$name" "$expected_detail" >&2
            expect_failed=$((expect_failed + 1))
        fi
        IFS=,
    done
    IFS="$old_ifs"
}

case "$SCOPE" in
    core)
        fzn_sources="$(add_files "$bench_dir")"
        ;;
    challenge)
        fzn_sources="$(add_files "$bench_dir/challenge")"
        ;;
    guard)
        fzn_sources="$(guard_files)"
        if [[ -z "${AY_MINIZINC_EXPECT:-}" ]]; then
            AY_MINIZINC_EXPECT="challenge/array_var_element_fallback_proxy=SOLVED|xs = array1d(1..6,challenge/array_var_element_fallback_proxy=SOLVED|val = 3;,challenge/black_hole_0=SOLVED|x = array1d(1..52,challenge/costas_10=SOLVED|costas = array1d(1..10,challenge/jobshop_abz5=SOLVED|t_end = 1234;,challenge/steiner_09=SOLVED|sets = array1d(1..12,community_detect_s26=SOLVED|obj = 2114335;"
        fi
        ;;
    all)
        fzn_sources="$(add_files "$bench_dir"; add_files "$bench_dir/challenge")"
        ;;
esac

fzn_files=()
while IFS= read -r fzn; do
    if [[ -n "$fzn" ]]; then
        if [[ ! -f "$fzn" ]]; then
            echo "ERROR: benchmark file not found: $fzn" >&2
            exit 1
        fi
        fzn_files+=("$fzn")
    fi
done <<< "$fzn_sources"

printf "ay: %s\n" "$ay_bin"
printf "scope: %s | timeout_ms: %s | process_timeout_s: %s\n" "$SCOPE" "$TIMEOUT_MS" "$process_timeout_s"
printf "%-40s %-18s %-10s %s\n" "Benchmark" "Result" "Time(ms)" "Details"
printf "%s\n" "$(printf '=%.0s' {1..92})"

for fzn in "${fzn_files[@]}"; do
    name="${fzn#"$bench_dir/"}"
    name="${name%.fzn}"
    total=$((total + 1))
    out_file="$tmp_dir/out.$total"

    start_ns="$(python3 -c 'import time; print(time.time_ns())')"
    python3 - "$process_timeout_s" "$out_file" "$ay_bin" flatzinc solve -t "$TIMEOUT_MS" "$fzn" <<'PY'
import subprocess
import sys

timeout_s = float(sys.argv[1])
out_path = sys.argv[2]
cmd = sys.argv[3:]
with open(out_path, "wb") as out:
    try:
        result = subprocess.run(
            cmd,
            stdout=out,
            stderr=subprocess.STDOUT,
            timeout=timeout_s,
            check=False,
        )
        sys.exit(result.returncode)
    except subprocess.TimeoutExpired:
        sys.exit(124)
PY
    exit_code=$?
    end_ns="$(python3 -c 'import time; print(time.time_ns())')"
    elapsed_ms=$(( (end_ns - start_ns) / 1000000 ))
    output="$(cat "$out_file")"
    detail="$(printf '%s' "$output" | tr '\n' ' ' | cut -c 1-80)"

    if [[ "$exit_code" -eq 124 ]]; then
        if grep -Fq -- "----------" "$out_file" || grep -Fq -- "==========" "$out_file"; then
            obj="$(latest_objective_line "$fzn" "$out_file" || true)"
            result="TIMEOUT_INCUMBENT"
            printf "%-40s %-18s %-10s %s\n" "$name" "$result" "$elapsed_ms" "$obj"
            check_expectation "$name" "$result" "$obj"
            timeout_incumbent=$((timeout_incumbent + 1))
        else
            result="TIMEOUT"
            printf "%-40s %-18s %-10s %s\n" "$name" "$result" "$elapsed_ms" ""
            check_expectation "$name" "$result" ""
            timeout=$((timeout + 1))
        fi
    elif [[ "$exit_code" -ne 0 ]]; then
        result="ERROR"
        printf "%-40s %-18s %-10s %s\n" "$name" "$result" "$elapsed_ms" "$detail"
        check_expectation "$name" "$result" "$detail"
        failed=$((failed + 1))
    elif grep -Fq "UNSATISFIABLE" "$out_file"; then
        result="UNSAT"
        printf "%-40s %-18s %-10s %s\n" "$name" "$result" "$elapsed_ms" ""
        check_expectation "$name" "$result" ""
        solved=$((solved + 1))
    elif grep -Fq -- "----------" "$out_file" || grep -Fq -- "==========" "$out_file"; then
        obj="$(latest_objective_line "$fzn" "$out_file" || true)"
        result="SOLVED"
        printf "%-40s %-18s %-10s %s\n" "$name" "$result" "$elapsed_ms" "$obj"
        check_expectation "$name" "$result" "$output"
        solved=$((solved + 1))
    elif grep -Fq "UNKNOWN" "$out_file"; then
        result="UNKNOWN"
        printf "%-40s %-18s %-10s %s\n" "$name" "$result" "$elapsed_ms" ""
        check_expectation "$name" "$result" ""
        unknown=$((unknown + 1))
    else
        result="ERROR"
        printf "%-40s %-18s %-10s %s\n" "$name" "$result" "$elapsed_ms" "$detail"
        check_expectation "$name" "$result" "$detail"
        failed=$((failed + 1))
    fi
done

printf "%s\n" "$(printf '=%.0s' {1..92})"
printf "Total: %d | Solved: %d | Timeout: %d | TimeoutIncumbent: %d | Unknown: %d | Error: %d\n" \
    "$total" "$solved" "$timeout" "$timeout_incumbent" "$unknown" "$failed"
printf "Solve rate: %d/%d (%.1f%%)\n" "$solved" "$total" \
    "$(python3 -c "print(100*$solved/$total if $total>0 else 0)")"

if [[ "$STRICT" != "0" && "$failed" -ne 0 ]]; then
    echo "ERROR: MiniZinc benchmark sweep had $failed errors" >&2
    exit 1
fi

if [[ "$expect_failed" -ne 0 ]]; then
    echo "ERROR: MiniZinc benchmark sweep had $expect_failed expectation failures" >&2
    exit 1
fi

if [[ -n "${AY_MINIZINC_EXPECT:-}" ]]; then
    old_ifs="$IFS"
    IFS=,
    for spec in $AY_MINIZINC_EXPECT; do
        IFS="$old_ifs"
        expected_name="${spec%%=*}"
        if [[ "$expect_seen" != *",$expected_name,"* ]]; then
            echo "ERROR: MiniZinc expectation did not match any benchmark: $expected_name" >&2
            exit 1
        fi
        IFS=,
    done
    IFS="$old_ifs"
fi

if [[ "$REQUIRE_SOLVED" -gt 0 && "$solved" -lt "$REQUIRE_SOLVED" ]]; then
    echo "ERROR: MiniZinc benchmark sweep solved $solved, below required $REQUIRE_SOLVED" >&2
    exit 1
fi

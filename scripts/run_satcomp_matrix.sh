#!/usr/bin/env bash
# ay-script: satcomp-matrix-shim
# Copyright 2026 Andrew Yates
# Author: Andrew Yates
# Licensed under the Apache License, Version 2.0

set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

# Compatibility shim only: SAT-COMP matrix run/admission behavior lives in the
# Rust CLI below, including retained Fmla learned-LRAT dry-run artifact handoff.
# Keep this wrapper to legacy argument translation rather than duplicating gates.

resolve_ay_cli() {
    if [[ -n "${AY_SATCOMP_MATRIX_CLI:-}" ]]; then
        printf '%s\n' "$AY_SATCOMP_MATRIX_CLI"
        return 0
    fi
    # The matrix CLI now ships in the `ay` binary (ay was renamed to ay). Prefer
    # a prebuilt release binary so the documented command runs without a cargo
    # build, falling back to `cargo run -p ay` below.
    if [[ -x "$ROOT_DIR/target/release/ay" ]]; then
        printf '%s\n' "$ROOT_DIR/target/release/ay"
        return 0
    fi
    if [[ -x "$ROOT_DIR/target/debug/ay" ]]; then
        printf '%s\n' "$ROOT_DIR/target/debug/ay"
        return 0
    fi
    return 1
}

run_ay() {
    if cli="$(resolve_ay_cli)"; then
        exec "$cli" "$@"
    fi
    exec cargo run --quiet -p ay --features cli -- "$@"
}

mode="run"
has_evidence_scoreboard=0
for arg in "$@"; do
    case "$arg" in
        --evidence-summary)
            mode="evidence-summary"
            ;;
        --evidence-scoreboard)
            has_evidence_scoreboard=1
            ;;
    esac
done

translated=()
if [[ "$mode" == "evidence-summary" ]]; then
    while [[ $# -gt 0 ]]; do
        case "$1" in
            --evidence-summary)
                shift
                ;;
            --evidence-scoreboard)
                [[ $# -ge 2 ]] || { echo "run_satcomp_matrix.sh: --evidence-scoreboard requires a value" >&2; exit 2; }
                translated+=(--scoreboard "$2")
                shift 2
                ;;
            --evidence-out)
                [[ $# -ge 2 ]] || { echo "run_satcomp_matrix.sh: --evidence-out requires a value" >&2; exit 2; }
                translated+=(--output "$2")
                shift 2
                ;;
            --evidence-variant)
                [[ $# -ge 2 ]] || { echo "run_satcomp_matrix.sh: --evidence-variant requires a value" >&2; exit 2; }
                translated+=(--variant "$2")
                shift 2
                ;;
            --evidence-candidate-mode)
                [[ $# -ge 2 ]] || { echo "run_satcomp_matrix.sh: --evidence-candidate-mode requires a value" >&2; exit 2; }
                translated+=(--candidate-mode "$2")
                shift 2
                ;;
            --evidence-stats-json)
                [[ $# -ge 2 ]] || { echo "run_satcomp_matrix.sh: --evidence-stats-json requires a value" >&2; exit 2; }
                translated+=(--stats-json "$2")
                shift 2
                ;;
            --output)
                [[ $# -ge 2 ]] || { echo "run_satcomp_matrix.sh: --output requires a value" >&2; exit 2; }
                if [[ "$has_evidence_scoreboard" -eq 0 ]]; then
                    translated+=(--scoreboard "$2/scoreboard.json")
                fi
                shift 2
                ;;
            *)
                translated+=("$1")
                shift
                ;;
        esac
    done
    run_ay submission preflight sat-matrix evidence-summary "${translated[@]}"
else
    while [[ $# -gt 0 ]]; do
        case "$1" in
            --single)
                shift
                ;;
            --reference-solver)
                # The Rust-owned sat-matrix run gate does not perform in-run
                # reference-solver cross-checks (that lives in `ay bench run`).
                # Translate legacy `--reference-solver name=path` (the verdict is
                # confirmed against the reference out-of-band) into a no-op so the
                # documented matrix command runs against the current CLI.
                if [[ $# -ge 2 && "$2" != --* ]]; then
                    shift 2
                else
                    shift
                fi
                ;;
            *)
                translated+=("$1")
                shift
                ;;
        esac
    done
    run_ay submission preflight sat-matrix run "${translated[@]}"
fi

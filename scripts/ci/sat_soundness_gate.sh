#!/usr/bin/env bash
# ay-script: sat-soundness-gate
# SAT soundness gate (SAT-COMP campaign).
#
# Runs the `ay` binary on LABELED vendored CNFs and fails the build on:
#   - any WRONG verdict (SAT for a known-UNSAT instance, or vice versa), and
#   - any UNSAT whose emitted proof FAILS internal verification (a rejected
#     certificate — the SAT-COMP "no points / DQ" failure mode).
# A sound `s UNKNOWN` / timeout is tolerated (never a wrong answer) but reported,
# so solved-count regressions are visible. This is the "zero wrong answers"
# gate the audit found missing — what would have caught inc1/6/7 never landing,
# and what guards a future soundness regression on the core CDCL path.
#
# Verdict + proof are checked in ONE run via --verify-proof, which exits:
#   10 = SAT,  20 = UNSAT (+ proof internally verified),  1 = proof REJECTED,
#   other = UNKNOWN/timeout.
#
# A standalone invocation acquires the host-wide `_oom_guard.py` lease before
# planning its single solver child. The continuous campaign already owns that
# lease and passes an explicit, validated parent envelope instead.
#
# Usage: scripts/ci/sat_soundness_gate.sh [ay-binary] [proof-format] [timeout-s]
set -u

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$REPO_ROOT"

OOM_GUARD="$REPO_ROOT/scripts/_oom_guard.py"
PROOF_DIR=""
LEASE_IPC_DIR=""
LEASE_CONTROL_OPEN=0
LEASE_PID=""

cleanup() {
    local rc=$?
    local lease_rc=0
    trap - EXIT INT TERM HUP
    if [ -n "$PROOF_DIR" ]; then
        rm -rf -- "$PROOF_DIR"
    fi
    if [ "$LEASE_CONTROL_OPEN" -eq 1 ]; then
        exec 9>&-
        LEASE_CONTROL_OPEN=0
    fi
    if [ -n "$LEASE_PID" ]; then
        wait "$LEASE_PID" || lease_rc=$?
        if [ "$rc" -eq 0 ] && [ "$lease_rc" -ne 0 ]; then
            echo "FATAL: oom-guard lease sidecar exited with status $lease_rc" >&2
            rc=2
        fi
    fi
    if [ -n "$LEASE_IPC_DIR" ]; then
        rm -rf -- "$LEASE_IPC_DIR"
    fi
    exit "$rc"
}

fatal() {
    echo "FATAL: $*" >&2
    exit 2
}

require_positive_decimal() {
    local name="$1"
    local value="$2"
    if ! [[ "$value" =~ ^[1-9][0-9]*$ ]] || [ "${#value}" -gt 9 ]; then
        fatal "$name must be a positive decimal integer"
    fi
}

require_nonnegative_decimal() {
    local name="$1"
    local value="$2"
    if ! [[ "$value" =~ ^(0|[1-9][0-9]*)$ ]] || [ "${#value}" -gt 9 ]; then
        fatal "$name must be a non-negative decimal integer"
    fi
}

trap cleanup EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
trap 'exit 129' HUP

BIN="${1:-}"
if [ -z "$BIN" ]; then
    if [ -x target/release/ay ]; then BIN=target/release/ay
    elif [ -x target/debug/ay ]; then BIN=target/debug/ay
    else echo "FATAL: no ay binary found (build with: cargo build -p ay --features cli)"; exit 2; fi
fi
FMT="${2:-drat}"     # drat (SAT-COMP Main canonical) or lrat
TIMEOUT="${3:-60}"

RESOURCE_JOBS=""
RESOURCE_MEMLIMIT_MB=""
RESOURCE_NBCORE=""
RESOURCE_HEADROOM_MB=""
RESOURCE_LEASE=""
RESOURCE_SOURCE=""

if [ "${AY_OOM_GUARD_PARENT_LEASE:-}" = "1" ]; then
    require_positive_decimal "AY_CONTINUOUS_JOBS" "${AY_CONTINUOUS_JOBS:-}"
    require_positive_decimal \
        "AY_CONTINUOUS_MEMLIMIT_MB" "${AY_CONTINUOUS_MEMLIMIT_MB:-}"
    require_positive_decimal "MEMLIMIT" "${MEMLIMIT:-}"
    require_positive_decimal "NBCORE" "${NBCORE:-}"
    require_nonnegative_decimal \
        "AY_CONTINUOUS_HEADROOM_MB" "${AY_CONTINUOUS_HEADROOM_MB:-}"

    RESOURCE_JOBS=$((10#$AY_CONTINUOUS_JOBS))
    RESOURCE_MEMLIMIT_MB=$((10#$AY_CONTINUOUS_MEMLIMIT_MB))
    RESOURCE_NBCORE=$((10#$NBCORE))
    RESOURCE_HEADROOM_MB=$((10#$AY_CONTINUOUS_HEADROOM_MB))
    if [ "$RESOURCE_JOBS" -ne 1 ]; then
        fatal "parent resource plan must admit exactly one SAT gate child"
    fi
    if [ "$RESOURCE_MEMLIMIT_MB" -ne "$((10#$MEMLIMIT))" ]; then
        fatal "AY_CONTINUOUS_MEMLIMIT_MB and MEMLIMIT must match"
    fi
    RESOURCE_LEASE="parent-held"
    RESOURCE_SOURCE="parent-plan"
elif [ -n "${AY_OOM_GUARD_PARENT_LEASE:-}" ]; then
    fatal "AY_OOM_GUARD_PARENT_LEASE must be 1 when set"
else
    [ -f "$OOM_GUARD" ] || fatal "missing resource planner: $OOM_GUARD"
    # macOS still ships Bash 3.2, which has neither `coproc` nor dynamic
    # `exec {fd}` descriptors. Use two private FIFOs and one script-owned
    # descriptor instead: fd 9 keeps the sidecar's stdin open for the whole
    # gate, while the readiness FIFO preserves the same fail-closed handshake.
    LEASE_IPC_DIR="$(
        mktemp -d "${TMPDIR:-/tmp}/ay-sat-soundness-lease.XXXXXX"
    )" || fatal "could not create oom-guard lease IPC directory"
    LEASE_CONTROL_FIFO="$LEASE_IPC_DIR/control"
    LEASE_READY_FIFO="$LEASE_IPC_DIR/ready"
    mkfifo "$LEASE_CONTROL_FIFO" "$LEASE_READY_FIFO" \
        || fatal "could not create oom-guard lease FIFOs"
    python3 "$OOM_GUARD" lease --label "sat-soundness-gate" \
        <"$LEASE_CONTROL_FIFO" >"$LEASE_READY_FIFO" &
    LEASE_PID=$!
    exec 9>"$LEASE_CONTROL_FIFO"
    LEASE_CONTROL_OPEN=1
    lease_ready=""
    if ! IFS= read -r lease_ready <"$LEASE_READY_FIFO"; then
        fatal "oom-guard lease sidecar exited before readiness"
    fi
    if [ "$lease_ready" != "AY_OOM_HARNESS_LEASE_READY_V1" ]; then
        fatal "unexpected oom-guard lease readiness marker"
    fi

    plan_output=""
    if ! plan_output="$(
        python3 "$OOM_GUARD" plan \
            --jobs 1 \
            --label "sat-soundness-gate" \
            --warn-concurrent-build
    )"; then
        fatal "oom-guard could not plan the SAT soundness gate"
    fi
    while IFS='=' read -r key value; do
        case "$key" in
            PLAN_JOBS)
                [ -z "$RESOURCE_JOBS" ] || fatal "duplicate PLAN_JOBS"
                RESOURCE_JOBS="$value"
                ;;
            PLAN_MEMLIMIT_MB)
                [ -z "$RESOURCE_MEMLIMIT_MB" ] || \
                    fatal "duplicate PLAN_MEMLIMIT_MB"
                RESOURCE_MEMLIMIT_MB="$value"
                ;;
            PLAN_NBCORE)
                [ -z "$RESOURCE_NBCORE" ] || fatal "duplicate PLAN_NBCORE"
                RESOURCE_NBCORE="$value"
                ;;
            PLAN_HEADROOM_MB)
                [ -z "$RESOURCE_HEADROOM_MB" ] || \
                    fatal "duplicate PLAN_HEADROOM_MB"
                RESOURCE_HEADROOM_MB="$value"
                ;;
            *)
                fatal "unexpected oom-guard plan output: $key"
                ;;
        esac
    done <<< "$plan_output"

    require_positive_decimal "PLAN_JOBS" "$RESOURCE_JOBS"
    require_positive_decimal "PLAN_MEMLIMIT_MB" "$RESOURCE_MEMLIMIT_MB"
    require_positive_decimal "PLAN_NBCORE" "$RESOURCE_NBCORE"
    require_nonnegative_decimal "PLAN_HEADROOM_MB" "$RESOURCE_HEADROOM_MB"
    RESOURCE_JOBS=$((10#$RESOURCE_JOBS))
    RESOURCE_MEMLIMIT_MB=$((10#$RESOURCE_MEMLIMIT_MB))
    RESOURCE_NBCORE=$((10#$RESOURCE_NBCORE))
    RESOURCE_HEADROOM_MB=$((10#$RESOURCE_HEADROOM_MB))
    if [ "$RESOURCE_JOBS" -ne 1 ]; then
        fatal "oom-guard plan did not admit exactly one SAT gate child"
    fi

    RESOURCE_SOURCE="auto-plan"
    for resource_cap in \
        "AY_CONTINUOUS_MEMLIMIT_MB=${AY_CONTINUOUS_MEMLIMIT_MB:-}" \
        "MEMLIMIT=${MEMLIMIT:-}"
    do
        cap_name="${resource_cap%%=*}"
        cap_value="${resource_cap#*=}"
        [ -z "$cap_value" ] && continue
        require_positive_decimal "$cap_name" "$cap_value"
        cap_value=$((10#$cap_value))
        if [ "$cap_value" -lt "$RESOURCE_MEMLIMIT_MB" ]; then
            RESOURCE_MEMLIMIT_MB="$cap_value"
        fi
        RESOURCE_SOURCE="auto-plan-capped"
    done
    if [ -n "${NBCORE:-}" ]; then
        require_positive_decimal "NBCORE" "$NBCORE"
        caller_nbcore=$((10#$NBCORE))
        if [ "$caller_nbcore" -lt "$RESOURCE_NBCORE" ]; then
            RESOURCE_NBCORE="$caller_nbcore"
        fi
        RESOURCE_SOURCE="auto-plan-capped"
    fi
    RESOURCE_LEASE="sidecar"
fi

export AY_CONTINUOUS_JOBS="$RESOURCE_JOBS"
export AY_CONTINUOUS_MEMLIMIT_MB="$RESOURCE_MEMLIMIT_MB"
export AY_CONTINUOUS_HEADROOM_MB="$RESOURCE_HEADROOM_MB"
export MEMLIMIT="$RESOURCE_MEMLIMIT_MB"
export NBCORE="$RESOURCE_NBCORE"
MEMORY_ARGS=(--memory "$RESOURCE_MEMLIMIT_MB")
RESOURCE_ENVELOPE="RESOURCE_ENVELOPE_V1 requested_jobs=1 jobs=$RESOURCE_JOBS \
memlimit_mb_per_child=$RESOURCE_MEMLIMIT_MB \
nbcore_per_child=$RESOURCE_NBCORE headroom_mb=$RESOURCE_HEADROOM_MB \
memory_enforcement=ay-main--memory lease=$RESOURCE_LEASE \
source=$RESOURCE_SOURCE"

# Labeled instances: "<expected> <path>"; everything under sat/unsat/ is UNSAT.
declare -a CASES=(
    "SAT   benchmarks/sat/canary/tiny_sat.cnf"
    "UNSAT benchmarks/sat/canary/tiny_unsat.cnf"
)
while IFS= read -r f; do
    CASES+=("UNSAT $f")
done < <(find benchmarks/sat/unsat -name '*.cnf' 2>/dev/null | sort)

TO=""
if command -v timeout >/dev/null 2>&1; then TO="timeout ${TIMEOUT}s"
elif command -v gtimeout >/dev/null 2>&1; then TO="gtimeout ${TIMEOUT}s"; fi

PROOF_DIR="$(mktemp -d)"

wrong=0; rejected=0; solved=0; unknown=0; harness_error=0; total=0
echo "SAT soundness gate: binary=$BIN format=$FMT timeout=${TIMEOUT}s"
echo "$RESOURCE_ENVELOPE"
echo "------------------------------------------------------------"
for case in "${CASES[@]}"; do
    expected="${case%% *}"; path="${case##* }"
    [ -f "$path" ] || { echo "SKIP  (missing) $path"; continue; }
    total=$((total + 1))
    proof="$PROOF_DIR/$(basename "$path").$FMT"
    $TO "$BIN" "$path" "${MEMORY_ARGS[@]}" --proof "$proof" --proof-format "$FMT" --verify-proof >/dev/null 2>&1
    rc=$?
    case "$rc" in
        10) verdict=SAT ;;
        20) verdict=UNSAT ;;       # UNSAT + proof verified
        1)  verdict=PROOF_REJECTED ;;
        0|124) verdict=UNKNOWN ;;  # solver-declared unknown or wall timeout
        *)  verdict=HARNESS_ERROR ;;
    esac
    rm -f "$proof"
    if [ "$verdict" = "PROOF_REJECTED" ]; then
        echo "REJECT proof failed verification  $path"; rejected=$((rejected + 1))
    elif [ "$verdict" = "HARNESS_ERROR" ]; then
        echo "ERROR unexpected solver/checker exit=$rc  $path"; harness_error=$((harness_error + 1))
    elif [ "$verdict" = "UNKNOWN" ]; then
        echo "warn  UNKNOWN/timeout   ($expected) $path"; unknown=$((unknown + 1))
    elif [ "$verdict" = "$expected" ]; then
        echo "ok    $verdict (proof ok if UNSAT)  $path"; solved=$((solved + 1))
    else
        echo "WRONG got=$verdict expected=$expected  $path"; wrong=$((wrong + 1))
    fi
done
echo "------------------------------------------------------------"
echo "total=$total solved=$solved unknown=$unknown WRONG=$wrong PROOF_REJECTED=$rejected HARNESS_ERROR=$harness_error"
if [ "$wrong" -gt 0 ] || [ "$rejected" -gt 0 ] || [ "$harness_error" -gt 0 ]; then
    echo "FAIL: $wrong wrong verdict(s) + $rejected rejected proof(s) + $harness_error harness error(s) — soundness regression, blocking."
    exit 1
fi
echo "PASS: zero wrong answers, all UNSAT proofs verified."
exit 0

#!/usr/bin/env bash
# ay-script: sat26-package
# Copyright 2026 Andrew Yates
# Author: Andrew Yates
# Licensed under the Apache License, Version 2.0

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
SAT_PROFILE_MATRIX="$SCRIPT_DIR/sat_profile_matrix.json"

TRACK="main"
AI_CLASS="regular"
PROOF_FORMAT="drat"
OUTPUT_DIR="$REPO_ROOT/target/sat26-submission"
STAGE_BINARY="none"
SOURCE_MODE="archive"
ALLOW_LOCAL_RUNSH_PREFLIGHT_BINARY=0
declare -a VARIANTS=()
SOURCE_TMP_DIR=""
SOURCE_FILES_MANIFEST=""
SOURCE_ARCHIVE_SHA256=""
SOURCE_FILES_SHA256=""
SOURCE_DIRTY_AT_STAGE_TIME="unknown"
SOURCE_GIT_STATUS_SHA256="unknown"
declare -a PROFILE_IDS=()
declare -a PROFILE_IDENTITIES=()
declare -a PROFILE_SOLVER_VARIANTS=()
declare -a PROFILE_RUNTIME_VARIANTS=()
declare -a PROFILE_JIT_MODES=()
declare -a PROFILE_RUNTIME_ENVS=()
declare -a PROFILE_BCP_LEARNED_1963_BLOCKER_CERT_ELISIONS=()
declare -a PROFILE_BCP_LEARNED_1963_BLOCKER_CERT_FALSE_REJECT_DEMOTES=()
declare -a PROFILE_DENSE_CLIQUE_PHP_PROOF_ROUTES=()

usage() {
    cat <<'EOF'
Usage: competition/prepare_sat26_submission.sh [OPTIONS]

Generate SAT-COMP 2026 BenchCloud/NHR-style submission roots. Each root has
top-level build.sh and run.sh, where run.sh accepts:

  ./run.sh <instance.cnf> <output_dir>

Options:
  --all-regular            Generate default, aggressive, probe, and minimal.
  --variant NAME           Generate one variant (repeatable).
  --variants A,B           Generate comma-separated variants.
  --track NAME             Competition track label (default: main).
  --ai-class NAME          SAT profile matrix id (default: regular).
  --proof-format FORMAT    Proof format for UNSAT output (default: drat).
  --output DIR             Output directory (default: target/sat26-submission).
  --stage-binary MODE      auto, none, or path to ay (default: none).
  --source-mode MODE       archive or none (default: archive).
  --allow-local-runsh-preflight-binary
                           Allow --stage-binary for Main/regular local run.sh
                           preflight only; not submission evidence.
  -h, --help               Show this help.

Generation-time evidence overrides:
  SAT26_PROFILE_BCP_LEARNED_1963_BLOCKER_CERT_ELISION=0|1
  SAT26_PROFILE_BCP_LEARNED_1963_BLOCKER_CERT_FALSE_REJECT_DEMOTE=0|1
                           Override only these profile-owned #9707 runtime envs
                           when generating baseline/candidate evidence roots.
EOF
}

add_variant() {
    local variant="$1"
    case "$variant" in
        default|aggressive|probe|minimal) ;;
        *)
            echo "ERROR: unknown SAT variant '$variant' (expected default, aggressive, probe, minimal)" >&2
            exit 2
            ;;
    esac
    VARIANTS+=("$variant")
}

while [[ $# -gt 0 ]]; do
    case "$1" in
        --all-regular)
            VARIANTS=(default aggressive probe minimal)
            shift
            ;;
        --variant)
            [[ $# -ge 2 ]] || { echo "ERROR: --variant requires a value" >&2; exit 2; }
            add_variant "$2"
            shift 2
            ;;
        --variants)
            [[ $# -ge 2 ]] || { echo "ERROR: --variants requires a value" >&2; exit 2; }
            IFS=',' read -r -a requested <<<"$2"
            for variant in "${requested[@]}"; do
                [[ -n "$variant" ]] && add_variant "$variant"
            done
            shift 2
            ;;
        --track)
            [[ $# -ge 2 ]] || { echo "ERROR: --track requires a value" >&2; exit 2; }
            TRACK="$2"
            shift 2
            ;;
        --ai-class)
            [[ $# -ge 2 ]] || { echo "ERROR: --ai-class requires a value" >&2; exit 2; }
            AI_CLASS="$2"
            shift 2
            ;;
        --proof-format)
            [[ $# -ge 2 ]] || { echo "ERROR: --proof-format requires a value" >&2; exit 2; }
            PROOF_FORMAT="$2"
            shift 2
            ;;
        --output)
            [[ $# -ge 2 ]] || { echo "ERROR: --output requires a value" >&2; exit 2; }
            OUTPUT_DIR="$2"
            shift 2
            ;;
        --stage-binary)
            [[ $# -ge 2 ]] || { echo "ERROR: --stage-binary requires a value" >&2; exit 2; }
            STAGE_BINARY="$2"
            shift 2
            ;;
        --source-mode)
            [[ $# -ge 2 ]] || { echo "ERROR: --source-mode requires a value" >&2; exit 2; }
            SOURCE_MODE="$2"
            shift 2
            ;;
        --allow-local-runsh-preflight-binary)
            ALLOW_LOCAL_RUNSH_PREFLIGHT_BINARY=1
            shift
            ;;
        -h|--help)
            usage
            exit 0
            ;;
        *)
            echo "ERROR: unknown argument '$1'" >&2
            usage >&2
            exit 2
            ;;
    esac
done

if [[ ${#VARIANTS[@]} -eq 0 ]]; then
    VARIANTS=(default)
fi

case "$PROOF_FORMAT" in
    drat|lrat) ;;
    *)
        echo "ERROR: --proof-format supports drat (default) or lrat for SAT26 Main" >&2
        exit 2
        ;;
esac

case "$SOURCE_MODE" in
    archive|none) ;;
    *)
        echo "ERROR: --source-mode must be archive or none" >&2
        exit 2
        ;;
esac

if [[ "$TRACK" == "main" && "$AI_CLASS" == "regular" ]]; then
    if [[ "$SOURCE_MODE" != "archive" ]]; then
        echo "ERROR: Main/regular SAT26 source root must include source.tar.gz (--source-mode archive)" >&2
        exit 2
    fi
    if [[ "$STAGE_BINARY" != "none" ]]; then
        if [[ "$ALLOW_LOCAL_RUNSH_PREFLIGHT_BINARY" -ne 1 ]]; then
            echo "ERROR: Main/regular SAT26 source root must not use --stage-binary; build from source.tar.gz" >&2
            exit 2
        fi
    fi
fi

if [[ "$STAGE_BINARY" != "auto" && "$STAGE_BINARY" != "none" && ! -x "$STAGE_BINARY" ]]; then
    echo "ERROR: --stage-binary path is not executable: $STAGE_BINARY" >&2
    exit 2
fi

resolve_stage_binary() {
    case "$STAGE_BINARY" in
        none)
            return 1
            ;;
        auto)
            if [[ -x "$REPO_ROOT/target/release-perf/ay" ]]; then
                printf '%s\n' "$REPO_ROOT/target/release-perf/ay"
                return 0
            fi
            return 1
            ;;
        *)
            printf '%s\n' "$STAGE_BINARY"
            return 0
            ;;
    esac
}

sha256_file() {
    local path="$1"
    case "$path" in
        *\\*|?:*) if command -v cygpath >/dev/null 2>&1; then
            path="$(cygpath -u -- "$path" 2>/dev/null || printf '%s\n' "$path")"
        fi ;;
    esac
    if command -v sha256sum >/dev/null 2>&1; then
        sha256sum "$path" | awk '{ print $1 }'
    else
        shasum -a 256 "$path" | awk '{ print $1 }'
    fi
}

sha256_text() {
    if command -v sha256sum >/dev/null 2>&1; then
        sha256sum | awk '{ print $1 }'
    else
        shasum -a 256 | awk '{ print $1 }'
    fi
}

source_git_status() {
    case "${AY_SOURCE_GIT_DIRTY:-}" in
        0|false|False|FALSE|no|No|NO|clean|Clean|CLEAN)
            return 0
            ;;
    esac

    git -C "$REPO_ROOT" status --porcelain=v1 --untracked-files=all -- \
        Cargo.toml Cargo.lock crates build_support LICENSE NOTICE README.md THIRD_PARTY.md \
        rustfmt.toml \
        competition/prepare_sat26_submission.sh \
        competition/validate_sat26_submission.sh competition/rehearse_sat26_linux_build.sh \
        competition/solver_description.txt competition/jit_mode_matrix.json \
        competition/jit_mode_matrix.schema.json \
        competition/sat_profile_matrix.json competition/sat_profile_matrix.schema.json \
        evals/registry/sat-par2-dev.yaml \
        benchmarks/sat/satcomp2024-sample/manifest.csv \
        2>/dev/null || true
}

scrub_source_tree() {
    local source_dir="$1"

    find "$source_dir" -type d \( \
            -name '__pycache__' -o \
            -name 'reports' \
        \) -prune -exec rm -rf {} +
    find "$source_dir" -type f \( \
            -name '*.pyc' -o \
            -name '*.pyo' -o \
            -name '*.profraw' -o \
            -name '*.profdata' -o \
            -name '*.gcda' -o \
            -name '*.gcno' -o \
            -name '.DS_Store' \
        \) -delete
}

write_files_sha256() {
    local base_dir="$1"
    local out="$2"
    local rel
    local hash

    (
        cd "$base_dir"
        find . -type f -print | LC_ALL=C sort
    ) | while IFS= read -r rel; do
        rel="${rel#./}"
        hash="$(sha256_file "$base_dir/$rel")"
        printf '%s  %s\n' "$hash" "$rel"
    done >"$out"
}

write_package_files_sha256() {
    local root_dir="$1"
    local out="$root_dir/package-files.sha256"
    local rel
    local hash

    (
        cd "$root_dir"
        find . -type f \
            ! -path './build/*' \
            ! -path './ay' \
            ! -path './package-files.sha256' \
            -print | LC_ALL=C sort
    ) | while IFS= read -r rel; do
        rel="${rel#./}"
        hash="$(sha256_file "$root_dir/$rel")"
        printf '%s  %s\n' "$hash" "$rel"
    done >"$out"
}

verify_package_files_sha256() {
    local root_dir="$1"
    local manifest="$root_dir/package-files.sha256"
    local saw_submission=0
    local saw_profile=0
    local saw_staged_binary_manifest=0
    local line
    local expected
    local rel
    local actual
    local cr
    cr="$(printf '\r')"

    [[ -f "$manifest" ]] || {
        echo "ERROR: generated root is missing package-files.sha256: $root_dir" >&2
        exit 2
    }

    while IFS= read -r line || [[ -n "$line" ]]; do
        line="${line%$cr}"
        [[ -n "$line" ]] || continue
        expected="${line%%  *}"
        rel="${line#*  }"
        if [[ "$expected" == "$line" || -z "$rel" ]]; then
            echo "ERROR: malformed package-files.sha256 entry: $line" >&2
            exit 2
        fi
        if [[ ${#expected} -ne 64 || "$expected" == *[!0123456789abcdef]* ]]; then
            echo "ERROR: malformed package-files.sha256 hash for $rel" >&2
            exit 2
        fi
        case "$rel" in
            /*|..|../*|*/../*|*/..)
                echo "ERROR: unsafe package-files.sha256 path: $rel" >&2
                exit 2
                ;;
            ay|build/*|package-files.sha256)
                echo "ERROR: package-files.sha256 lists excluded generated path: $rel" >&2
                exit 2
                ;;
            SAT26_SUBMISSION.md)
                saw_submission=1
                ;;
            profile/satcomp26_profile.json)
                saw_profile=1
                ;;
            staged-binary.sha256)
                saw_staged_binary_manifest=1
                ;;
        esac

        [[ -f "$root_dir/$rel" ]] || {
            echo "ERROR: package-files.sha256 lists missing file: $rel" >&2
            exit 2
        }
        actual="$(sha256_file "$root_dir/$rel")"
        if [[ "$actual" != "$expected" ]]; then
            echo "ERROR: package-files.sha256 hash mismatch for $rel" >&2
            exit 2
        fi
    done <"$manifest"

    [[ "$saw_submission" -eq 1 ]] || {
        echo "ERROR: package-files.sha256 is missing SAT26_SUBMISSION.md" >&2
        exit 2
    }
    [[ "$saw_profile" -eq 1 ]] || {
        echo "ERROR: package-files.sha256 is missing profile/satcomp26_profile.json" >&2
        exit 2
    }
    if [[ ! -f "$root_dir/source.tar.gz" && -x "$root_dir/ay" && "$saw_staged_binary_manifest" -ne 1 ]]; then
        echo "ERROR: package-files.sha256 is missing staged-binary.sha256 for staged ay" >&2
        exit 2
    fi
}

profile_metadata_value() {
    local profile_json="$1"
    local key="$2"

    awk -F'"' -v key="$key" '$2 == key { print $4; exit }' "$profile_json"
}

verify_profile_metadata_hash() {
    local root_dir="$1"
    local label="$2"
    local path="$3"
    local profile_json="$root_dir/profile/satcomp26_profile.json"
    local expected
    local actual

    [[ -f "$profile_json" ]] || {
        echo "ERROR: generated root is missing profile/satcomp26_profile.json: $root_dir" >&2
        exit 2
    }
    [[ -f "$path" ]] || {
        echo "ERROR: generated root is missing $(basename "$path") for profile hash check" >&2
        exit 2
    }

    expected="$(profile_metadata_value "$profile_json" "$label")"
    if [[ -z "$expected" ]]; then
        echo "ERROR: profile/satcomp26_profile.json is missing $label" >&2
        exit 2
    fi
    actual="$(sha256_file "$path")"
    if [[ "$actual" != "$expected" ]]; then
        echo "ERROR: profile/satcomp26_profile.json $label does not match $(basename "$path")" >&2
        exit 2
    fi
}

load_sat_profile_metadata() {
    local track="$1"
    local ai_class="$2"
    local variant="$3"
    local proof_format="$4"

    [[ -f "$SAT_PROFILE_MATRIX" ]] || {
        echo "ERROR: SAT profile matrix is missing: $SAT_PROFILE_MATRIX" >&2
        exit 2
    }
    command -v python3 >/dev/null 2>&1 || {
        echo "ERROR: python3 is required to resolve SAT profile matrix identities" >&2
        exit 2
    }

    # Every runtime_env key the matrix exports must be a name the solver knows.
    # The block below already checks the REQUIRED keys are PRESENT; nothing checked
    # that a declared key means anything, and three did not -- two of them carrying
    # the literal placeholder value "required". A profile that exports a key nothing
    # reads does not describe the configuration the scored run executes.
    "${REPO_ROOT:-$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)}/competition/validate_runtime_env.py" || {
        echo "ERROR: submission profile exports a runtime_env key the solver does not know" >&2
        exit 2
    }

    SAT_PROFILE_METADATA=()
    while IFS= read -r line; do
        line="${line%$'\r'}"
        SAT_PROFILE_METADATA+=("$line")
    done < <(
        python3 - "$SAT_PROFILE_MATRIX" "$track" "$ai_class" "$variant" "$proof_format" <<'PY'
import json
import os
import sys
from pathlib import Path

matrix_path = Path(sys.argv[1])
track = sys.argv[2]
ai_class = sys.argv[3]
variant = sys.argv[4]
proof_format = sys.argv[5]

matrix = json.loads(matrix_path.read_text(encoding="utf-8"))
profiles = {
    str(profile.get("id", "")): profile
    for profile in matrix.get("profiles", [])
    if isinstance(profile, dict)
}

if track == "main" and ai_class == "regular":
    requested_profile_id = str(
        matrix.get("sat26_compliance", {})
        .get("main_track_contract", {})
        .get("profile_id", "regular")
    )
else:
    requested_profile_id = ai_class

profile = profiles.get(requested_profile_id)
if profile is None:
    print(
        "ERROR: no SAT profile matrix identity for "
        f"track={track!r}, ai_class={ai_class!r}, variant={variant!r}",
        file=sys.stderr,
    )
    print(
        "ERROR: use one of the matrix profile ids with its solver_variant",
        file=sys.stderr,
    )
    sys.exit(2)

solver_variant = str(profile.get("solver_variant", ""))
if solver_variant != variant:
    print(
        "ERROR: SAT profile matrix identity "
        f"{requested_profile_id!r} declares solver_variant {solver_variant!r}, "
        f"not requested variant {variant!r}",
        file=sys.stderr,
    )
    sys.exit(2)

requirements = profile.get("requirements", {})
unsat_proof = requirements.get("unsat_proof", {})
if unsat_proof.get("path_template") != "$2/proof.out":
    print(
        "ERROR: SAT profile matrix UNSAT proof path must be $2/proof.out",
        file=sys.stderr,
    )
    sys.exit(2)
if unsat_proof.get("format") != proof_format:
    print(
        "ERROR: SAT profile matrix proof format "
        f"{unsat_proof.get('format')!r} does not match {proof_format!r}",
        file=sys.stderr,
    )
    sys.exit(2)

runtime_env = dict(profile.get("runtime_env", {}))
# B76: profile-owned lever decisions live in `profile_levers` and reach the
# solver as typed --sat-* CLI flags baked into run.sh, never as env exports.
profile_levers = dict(profile.get("profile_levers", {}))
profile_bool_overrides = {
    "SAT26_PROFILE_BCP_LEARNED_1963_BLOCKER_CERT_ELISION":
        "bcp_learned_1963_blocker_cert_elision",
    "SAT26_PROFILE_BCP_LEARNED_1963_BLOCKER_CERT_FALSE_REJECT_DEMOTE":
        "bcp_learned_1963_blocker_cert_false_reject_demote",
}
for env_name, lever_key in profile_bool_overrides.items():
    raw_value = os.environ.get(env_name, "").strip()
    if not raw_value:
        continue
    if raw_value not in ("0", "1"):
        print(
            f"ERROR: {env_name} must be 0 or 1, got {raw_value!r}",
            file=sys.stderr,
        )
        sys.exit(2)
    if raw_value == "1":
        profile_levers[lever_key] = "1"
    else:
        profile_levers.pop(lever_key, None)
required_env = [
    "AY_SAT_COMPETITION_PROFILE",
    "AY_SAT_PROFILE_ID",
    "AY_SAT_VARIANT",
    "AY_COMPETITION_JIT_MODE",
]
missing_env = [key for key in required_env if not str(runtime_env.get(key, "")).strip()]
if missing_env:
    print(
        "ERROR: SAT profile matrix runtime_env missing "
        + ", ".join(missing_env),
        file=sys.stderr,
    )
    sys.exit(2)
if runtime_env["AY_SAT_COMPETITION_PROFILE"] != requested_profile_id:
    print("ERROR: SAT profile matrix runtime profile id mismatch", file=sys.stderr)
    sys.exit(2)
if runtime_env["AY_SAT_PROFILE_ID"] != profile.get("profile_identity"):
    print("ERROR: SAT profile matrix runtime identity mismatch", file=sys.stderr)
    sys.exit(2)
if runtime_env["AY_SAT_VARIANT"] != variant:
    print("ERROR: SAT profile matrix runtime variant mismatch", file=sys.stderr)
    sys.exit(2)

print(requested_profile_id)
print(str(profile["profile_identity"]))
print(solver_variant)
print(str(runtime_env["AY_SAT_VARIANT"]))
print(str(runtime_env["AY_COMPETITION_JIT_MODE"]))
print(json.dumps(runtime_env, sort_keys=True, separators=(",", ":")))
print(str(profile_levers.get("bcp_learned_1963_blocker_cert_elision", "")))
print(str(profile_levers.get("bcp_learned_1963_blocker_cert_false_reject_demote", "")))
print(str(profile_levers.get("dense_clique_php_proof_route", "")))
PY
    )

    if [[ ${#SAT_PROFILE_METADATA[@]} -ne 9 ]]; then
        echo "ERROR: SAT profile matrix resolver returned incomplete metadata" >&2
        exit 2
    fi
}

preflight_generated_root() {
    local root_dir="$1"
    local track="$2"
    local ai_class="$3"
    local variant="$4"
    local proof_format="$5"
    local profile_id="$6"
    local profile_identity="$7"
    local runtime_variant="$8"
    local jit_mode="$9"
    local tmp_dir
    local cnf
    local out_dir
    local expected_proof
    local fake_ay
    local original_ay
    local had_ay=0
    local arity_code
    local missing_output_code
    local run_code

    [[ -x "$root_dir/build.sh" ]] || {
        echo "ERROR: generated root is missing top-level executable build.sh: $root_dir" >&2
        exit 2
    }
    [[ -x "$root_dir/run.sh" ]] || {
        echo "ERROR: generated root is missing top-level executable run.sh: $root_dir" >&2
        exit 2
    }
    bash -n "$root_dir/run.sh"
    if grep -Eq 'STAREXEC_|[Ss]tar[Ee]xec' "$root_dir/run.sh"; then
        echo "ERROR: generated run.sh must not contain stale StarExec timeout fallback" >&2
        exit 2
    fi
    verify_package_files_sha256 "$root_dir"

    if [[ -f "$root_dir/source.tar.gz" ]]; then
        verify_profile_metadata_hash "$root_dir" source_archive_sha256 "$root_dir/source.tar.gz"
        verify_profile_metadata_hash "$root_dir" source_files_sha256 "$root_dir/source-files.sha256"
    fi

    tmp_dir="$(mktemp -d "${TMPDIR:-/tmp}/ay-sat26-preflight.XXXXXX")"
    cnf="$tmp_dir/tiny_unsat.cnf"
    out_dir="$tmp_dir/out"
    expected_proof="$out_dir/proof.out"
    fake_ay="$root_dir/ay"
    original_ay="$tmp_dir/original-ay"

    cat >"$cnf" <<'EOF'
p cnf 1 2
1 0
-1 0
EOF

    set +e
    "$root_dir/run.sh" >"$tmp_dir/arity.stdout" 2>"$tmp_dir/arity.stderr"
    arity_code=$?
    set -e
    if [[ "$arity_code" -ne 2 ]]; then
        echo "ERROR: generated run.sh must reject missing <instance> <output_dir> with exit 2" >&2
        sed -n '1,80p' "$tmp_dir/arity.stderr" >&2 || true
        rm -rf "$tmp_dir"
        exit 2
    fi

    set +e
    "$root_dir/run.sh" "$cnf" >"$tmp_dir/missing-output.stdout" 2>"$tmp_dir/missing-output.stderr"
    missing_output_code=$?
    set -e
    if [[ "$missing_output_code" -ne 2 ]]; then
        echo "ERROR: generated run.sh must reject missing <output_dir> with exit 2" >&2
        sed -n '1,80p' "$tmp_dir/missing-output.stderr" >&2 || true
        rm -rf "$tmp_dir"
        exit 2
    fi

    if [[ -e "$fake_ay" ]]; then
        mv "$fake_ay" "$original_ay"
        had_ay=1
    fi

    cat >"$fake_ay" <<'PY'
#!/usr/bin/env python3
import os
import pathlib
import sys

args = sys.argv[1:]
errors = []

def flag_values(flag: str) -> list[str]:
    values: list[str] = []
    index = 0
    while index < len(args):
        arg = args[index]
        if arg == flag:
            if index + 1 >= len(args):
                errors.append(f"{flag} missing value")
            else:
                values.append(args[index + 1])
            index += 2
            continue
        if arg.startswith(flag + "="):
            values.append(arg.split("=", 1)[1])
        index += 1
    return values

if not args or args[0] != "solve":
    errors.append(f"argv must start with solve, got {args[:1]!r}")
if not args or args[-1] != os.environ["SAT26_PREFLIGHT_INSTANCE"]:
    errors.append("argv must end with the instance path")

for obsolete in ("--sat-track", "--sat-ai-class", "--sat-mode"):
    if any(arg == obsolete or arg.startswith(obsolete + "=") for arg in args):
        errors.append(f"generated command must use matrix identity env, not {obsolete}")

expected_env = {
    "AY_SAT_COMPETITION_PROFILE": os.environ["SAT26_PREFLIGHT_PROFILE_ID"],
    "AY_SAT_PROFILE_ID": os.environ["SAT26_PREFLIGHT_PROFILE_IDENTITY"],
    "AY_SAT_VARIANT": os.environ["SAT26_PREFLIGHT_RUNTIME_VARIANT"],
    "AY_COMPETITION_JIT_MODE": os.environ["SAT26_PREFLIGHT_JIT_MODE"],
    "AY_INTERNAL_PROVENANCE_CHILD": "1",
    "AY_INTERNAL_SATCOMP_WRAPPER": os.environ["SAT26_PREFLIGHT_WRAPPER"],
}
for key, expected in expected_env.items():
    actual = os.environ.get(key, "")
    if actual != expected:
        errors.append(f"{key}={actual!r}, expected {expected!r}")
if os.environ.get("AY_SAT_MAIN_ENABLE_STARTUP_PHASE_INIT"):
    errors.append("AY_SAT_MAIN_ENABLE_STARTUP_PHASE_INIT was not scrubbed")
if os.environ.get("AY_SAT_TRACK"):
    errors.append("AY_SAT_TRACK was not scrubbed")
if os.environ.get("AY_SAT_AI_CLASS"):
    errors.append("AY_SAT_AI_CLASS was not scrubbed")
# B76: the profile lever decisions travel as typed CLI flags on the solve
# argv; the env spellings have no reader in the binary any more.
def lever_flag_check(preflight_key: str, flag: str) -> None:
    expected = os.environ.get(preflight_key, "")
    present = any(arg == flag for arg in args)
    if expected == "1":
        if not present:
            errors.append(f"{flag} missing despite profile decision")
    elif present:
        errors.append(f"{flag} leaked without profile decision")

lever_flag_check(
    "SAT26_PREFLIGHT_BCP_LEARNED_1963_BLOCKER_CERT_ELISION",
    "--sat-bcp-learned-1963-blocker-cert-elision",
)
lever_flag_check(
    "SAT26_PREFLIGHT_BCP_LEARNED_1963_BLOCKER_CERT_FALSE_REJECT_DEMOTE",
    "--sat-bcp-learned-1963-blocker-cert-false-reject-demote",
)
lever_flag_check(
    "SAT26_PREFLIGHT_DENSE_CLIQUE_PHP_PROOF_ROUTE",
    "--sat-dense-clique-php-proof-route",
)

if flag_values("--sat-variant") != [os.environ["SAT26_PREFLIGHT_VARIANT"]]:
    errors.append("--sat-variant does not match requested variant")
if flag_values("--proof") != [os.environ["SAT26_PREFLIGHT_EXPECTED_PROOF"]]:
    errors.append("--proof must be $2/proof.out")
if flag_values("--proof-format") != [os.environ["SAT26_PREFLIGHT_PROOF_FORMAT"]]:
    errors.append("--proof-format does not match profile")
if "--no-verify-proof" not in args:
    errors.append("--no-verify-proof missing")
if flag_values("--timeout") != ["1234"]:
    errors.append("SATCOMP_TIMEOUT_MS was not forwarded as --timeout=1234")

if errors:
    for error in errors:
        print(f"ERROR: {error}", file=sys.stderr)
    sys.exit(97)

proof_path = pathlib.Path(os.environ["SAT26_PREFLIGHT_EXPECTED_PROOF"])
proof_path.parent.mkdir(parents=True, exist_ok=True)
proof_path.write_text("3 0 1 2 0\n", encoding="utf-8")
print("s UNSATISFIABLE")
sys.exit(20)
PY
    chmod 755 "$fake_ay"

    mkdir -p "$out_dir"
    set +e
    SATCOMP_TIMEOUT_MS=1234 \
    AY_SOLVE_SESSION_PROVENANCE=stale-parent \
    AY_SAT_MAIN_ENABLE_STARTUP_PHASE_INIT=1 \
    AY_SAT_TRACK=experimental \
    AY_SAT_AI_CLASS=ai-tuned \
    AY_SAT_ALLOW_MAIN_CANDIDATE_VARIANTS=1 \
    AY_SAT_BCP_ADVANCE_SAVED_POS=1 \
    AY_SAT_BCP_LEARNED_1963_FALSE_SAVED_POS_RESET=1 \
    AY_SAT_BCP_LEARNED_1963_TRUE_TAIL_RELOCATION=1 \
    AY_SAT_BCP_LEARNED_1963_BLOCKER_CERT_ELISION=1 \
    AY_SAT_BCP_LEARNED_1963_BLOCKER_CERT_SHADOW=1 \
    AY_SAT_BCP_LEARNED_1963_BLOCKER_CERT_FALSE_REJECT_DEMOTE=1 \
    AY_SAT_BCP_LEARNED_1963_USED5_FSW_SAVED_POS_RESET=1 \
    AY_SAT_BCP_LEARNED_1963_FSW_CONFLICT_SAVED_POS_RESET=1 \
    AY_SAT_BCP_LEARNED_1963_FSW_GENT_SKIP=1 \
    AY_SAT_BCP_LEARNED_618_TRUE_TAIL_RELOCATION=1 \
    AY_SAT_BCP_LEARNED_NO_REPLACEMENT_SAVED_POS_UPDATE=1 \
    AY_SAT_BCP_LEARNED_NO_REPLACEMENT_SCAN_PRESSURE=1 \
    AY_SAT_BCP_LEARNED_1963_IDENTITY=1 \
    AY_SAT_BCP_LEARNED_1963_PRESSURE_REDUCTION=1 \
    AY_SAT_BCP_LEARNED_1963_PRESSURE_RETENTION=1 \
    AY_SAT_BCP_DISABLE_LEARNED_1963_NO_REPLACEMENT_UNIT_BLOCKER_REFRESH=1 \
    AY_SAT_BCP_LEARNED_1963_TAIL_REORDER_SWAP_BUDGET=256 \
    AY_SAT_DENSE_CLIQUE_MAB_BRANCH=1 \
    AY_SAT_DENSE_MUTEX_FOCUSED_RESTART_GATE=1 \
    AY_SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE=ambient-stale \
    AY_SAT_DENSE_CLIQUE_PHP_COMPACT_LRAT_PROOF=/tmp/ambient-compact.lrat \
    AY_SAT_OFFICIAL_ALLOW_DESTRUCTIVE_TRANSFORMS=decompose \
    AY_NO_DECOMPOSE=1 \
    SAT26_PREFLIGHT_INSTANCE="$cnf" \
    SAT26_PREFLIGHT_EXPECTED_PROOF="$expected_proof" \
    SAT26_PREFLIGHT_VARIANT="$variant" \
    SAT26_PREFLIGHT_RUNTIME_VARIANT="$runtime_variant" \
    SAT26_PREFLIGHT_PROOF_FORMAT="$proof_format" \
    SAT26_PREFLIGHT_PROFILE_ID="$profile_id" \
    SAT26_PREFLIGHT_PROFILE_IDENTITY="$profile_identity" \
    SAT26_PREFLIGHT_JIT_MODE="$jit_mode" \
    SAT26_PREFLIGHT_BCP_LEARNED_1963_BLOCKER_CERT_ELISION="${PROFILE_BCP_LEARNED_1963_BLOCKER_CERT_ELISIONS[$idx]}" \
    SAT26_PREFLIGHT_BCP_LEARNED_1963_BLOCKER_CERT_FALSE_REJECT_DEMOTE="${PROFILE_BCP_LEARNED_1963_BLOCKER_CERT_FALSE_REJECT_DEMOTES[$idx]}" \
    SAT26_PREFLIGHT_DENSE_CLIQUE_PHP_PROOF_ROUTE="${PROFILE_DENSE_CLIQUE_PHP_PROOF_ROUTES[$idx]}" \
    SAT26_PREFLIGHT_WRAPPER="$track-$ai_class-$variant-$proof_format-v1" \
        "$root_dir/run.sh" "$cnf" "$out_dir" >"$tmp_dir/run.stdout" 2>"$tmp_dir/run.stderr"
    run_code=$?
    set -e

    rm -f "$fake_ay"
    if [[ "$had_ay" -eq 1 ]]; then
        mv "$original_ay" "$fake_ay"
    fi

    if [[ "$run_code" -ne 20 ]]; then
        echo "ERROR: generated run.sh preflight failed with exit $run_code" >&2
        sed -n '1,120p' "$tmp_dir/run.stderr" >&2 || true
        rm -rf "$tmp_dir"
        exit 2
    fi
    [[ -s "$expected_proof" ]] || {
        echo "ERROR: generated run.sh did not write UNSAT proof to \$2/proof.out" >&2
        rm -rf "$tmp_dir"
        exit 2
    }

    rm -rf "$tmp_dir"
}

if [[ "$TRACK" == "main" && "$AI_CLASS" == "regular" ]]; then
    for variant in "${VARIANTS[@]}"; do
        if [[ "$variant" != "default" ]]; then
            echo "ERROR: Main/regular SAT26 source root must use variant 'default' (got '$variant')" >&2
            exit 2
        fi
    done
fi

for variant in "${VARIANTS[@]}"; do
    load_sat_profile_metadata "$TRACK" "$AI_CLASS" "$variant" "$PROOF_FORMAT"
    PROFILE_IDS+=("${SAT_PROFILE_METADATA[0]}")
    PROFILE_IDENTITIES+=("${SAT_PROFILE_METADATA[1]}")
    PROFILE_SOLVER_VARIANTS+=("${SAT_PROFILE_METADATA[2]}")
    PROFILE_RUNTIME_VARIANTS+=("${SAT_PROFILE_METADATA[3]}")
    PROFILE_JIT_MODES+=("${SAT_PROFILE_METADATA[4]}")
    PROFILE_RUNTIME_ENVS+=("${SAT_PROFILE_METADATA[5]}")
    PROFILE_BCP_LEARNED_1963_BLOCKER_CERT_ELISIONS+=("${SAT_PROFILE_METADATA[6]}")
    PROFILE_BCP_LEARNED_1963_BLOCKER_CERT_FALSE_REJECT_DEMOTES+=("${SAT_PROFILE_METADATA[7]}")
    PROFILE_DENSE_CLIQUE_PHP_PROOF_ROUTES+=("${SAT_PROFILE_METADATA[8]}")
done

SOURCE_ARCHIVE=""
if [[ "$SOURCE_MODE" == "archive" ]]; then
    SOURCE_TMP_DIR="$(mktemp -d "${TMPDIR:-/tmp}/ay-sat26-source.XXXXXX")"
    SOURCE_ARCHIVE="$SOURCE_TMP_DIR/source.tar.gz"
    trap 'rm -rf "$SOURCE_TMP_DIR"' EXIT
    (
        cd "$REPO_ROOT"
        git archive --format=tar --prefix=source/ HEAD \
            Cargo.toml Cargo.lock crates build_support LICENSE NOTICE README.md THIRD_PARTY.md rustfmt.toml |
            tar xf - -C "$SOURCE_TMP_DIR"
    )
    scrub_source_tree "$SOURCE_TMP_DIR/source"
    SOURCE_FILES_MANIFEST="$SOURCE_TMP_DIR/source-files.sha256"
    write_files_sha256 "$SOURCE_TMP_DIR/source" "$SOURCE_FILES_MANIFEST"
    SOURCE_FILES_SHA256="$(sha256_file "$SOURCE_FILES_MANIFEST")"
    tar --format ustar --owner=0 --group=0 --numeric-owner -czf "$SOURCE_ARCHIVE" -C "$SOURCE_TMP_DIR" source
    SOURCE_ARCHIVE_SHA256="$(sha256_file "$SOURCE_ARCHIVE")"
fi

COMMIT="$(git -C "$REPO_ROOT" rev-parse HEAD 2>/dev/null || printf 'unknown')"
VERSION="$(grep '^version' "$REPO_ROOT/Cargo.toml" | head -1 | sed 's/.*"\(.*\)".*/\1/')"
SOURCE_STATUS="$(source_git_status)"
if [[ -z "$SOURCE_STATUS" ]]; then
    SOURCE_DIRTY_AT_STAGE_TIME="false"
else
    SOURCE_DIRTY_AT_STAGE_TIME="true"
fi
SOURCE_GIT_STATUS_SHA256="$(printf '%s' "$SOURCE_STATUS" | sha256_text)"
mkdir -p "$OUTPUT_DIR"

STAGED_BINARY=""
if STAGED_BINARY="$(resolve_stage_binary)"; then
    :
else
    STAGED_BINARY=""
fi
LOCAL_RUNSH_PREFLIGHT_BINARY="false"
STAGED_BINARY_DECLARED="false"
if [[ -n "$STAGED_BINARY" ]]; then
    if [[ "$TRACK" == "main" && "$AI_CLASS" == "regular" && "$ALLOW_LOCAL_RUNSH_PREFLIGHT_BINARY" -eq 1 ]]; then
        LOCAL_RUNSH_PREFLIGHT_BINARY="true"
    else
        STAGED_BINARY_DECLARED="true"
    fi
fi

declare -a ROOT_NAMES=()

for idx in "${!VARIANTS[@]}"; do
    variant="${VARIANTS[$idx]}"
    root_name="ay-${TRACK}-${AI_CLASS}-${variant}"
    root_dir="$OUTPUT_DIR/$root_name"
    ROOT_NAMES+=("$root_name")

    rm -rf "$root_dir"
    mkdir -p "$root_dir/profile"

    if [[ -n "$SOURCE_ARCHIVE" ]]; then
        cp "$SOURCE_ARCHIVE" "$root_dir/source.tar.gz"
        cp "$SOURCE_FILES_MANIFEST" "$root_dir/source-files.sha256"
    fi
    if [[ -n "$STAGED_BINARY" ]]; then
        cp "$STAGED_BINARY" "$root_dir/ay"
        chmod 755 "$root_dir/ay"
        printf '%s  ay\n' "$(sha256_file "$root_dir/ay")" >"$root_dir/staged-binary.sha256"
    fi

    if [[ -f "$SCRIPT_DIR/solver_description.txt" ]]; then
        cp "$SCRIPT_DIR/solver_description.txt" "$root_dir/solver_description.txt"
    fi
    if [[ -f "$SCRIPT_DIR/jit_mode_matrix.json" ]]; then
        cp "$SCRIPT_DIR/jit_mode_matrix.json" "$root_dir/profile/jit_mode_matrix.json"
    fi
    if [[ -f "$SCRIPT_DIR/jit_mode_matrix.schema.json" ]]; then
        cp "$SCRIPT_DIR/jit_mode_matrix.schema.json" "$root_dir/profile/jit_mode_matrix.schema.json"
    fi
    if [[ -f "$SCRIPT_DIR/sat_profile_matrix.json" ]]; then
        cp "$SCRIPT_DIR/sat_profile_matrix.json" "$root_dir/profile/sat_profile_matrix.json"
    fi
    if [[ -f "$SCRIPT_DIR/sat_profile_matrix.schema.json" ]]; then
        cp "$SCRIPT_DIR/sat_profile_matrix.schema.json" "$root_dir/profile/sat_profile_matrix.schema.json"
    fi
    if [[ -f "$REPO_ROOT/evals/registry/sat-par2-dev.yaml" ]]; then
        cp "$REPO_ROOT/evals/registry/sat-par2-dev.yaml" "$root_dir/profile/sat-par2-dev.yaml"
    fi
    if [[ -f "$REPO_ROOT/benchmarks/sat/satcomp2024-sample/manifest.csv" ]]; then
        cp "$REPO_ROOT/benchmarks/sat/satcomp2024-sample/manifest.csv" "$root_dir/profile/satcomp2024-sample-manifest.csv"
    fi

    cat >"$root_dir/profile/satcomp26_profile.json" <<EOF
{
  "solver": "ay",
  "version": "$VERSION",
  "source_commit": "$COMMIT",
  "track": "$TRACK",
  "ai_class": "$AI_CLASS",
  "variant": "$variant",
  "profile_id": "${PROFILE_IDS[$idx]}",
  "profile_identity": "${PROFILE_IDENTITIES[$idx]}",
  "matrix_solver_variant": "${PROFILE_SOLVER_VARIANTS[$idx]}",
  "matrix_runtime_env": ${PROFILE_RUNTIME_ENVS[$idx]},
  "proof_format": "$PROOF_FORMAT",
  "run_contract": "run.sh <instance> <output_dir>",
  "unsat_proof": "proof.out",
  "pgo_policy": "$([[ "$SOURCE_MODE" == "archive" ]] && printf 'required-source-build-pgo/v1' || printf 'not-applicable-no-source/v1')",
  "pgo_marker": "ay.pgo.json",
  "pgo_profdata": "ay.pgo.profdata",
  "pgo_profile_use_required": $([[ "$SOURCE_MODE" == "archive" ]] && printf 'true' || printf 'false'),
  "source_dirty_at_stage_time": $SOURCE_DIRTY_AT_STAGE_TIME,
  "source_git_status_sha256": "$SOURCE_GIT_STATUS_SHA256",
  "source_archive_sha256": "$SOURCE_ARCHIVE_SHA256",
  "source_files_sha256": "$SOURCE_FILES_SHA256",
  "staged_binary": $STAGED_BINARY_DECLARED,
  "local_runsh_preflight_binary": $LOCAL_RUNSH_PREFLIGHT_BINARY
}
EOF

    cat >"$root_dir/SAT26_SUBMISSION.md" <<EOF
# AY SAT-COMP 2026 Submission Root

- track: $TRACK
- ai_class: $AI_CLASS
- variant: $variant
- profile_id: ${PROFILE_IDS[$idx]}
- profile_identity: ${PROFILE_IDENTITIES[$idx]}
- matrix_solver_variant: ${PROFILE_SOLVER_VARIANTS[$idx]}
- proof_format: $PROOF_FORMAT
- source_commit: $COMMIT
- source_dirty_at_stage_time: $SOURCE_DIRTY_AT_STAGE_TIME
- source_git_status_sha256: $SOURCE_GIT_STATUS_SHA256
- source_archive: source.tar.gz
- source_archive_sha256: $SOURCE_ARCHIVE_SHA256
- source_file_manifest: source-files.sha256
- source_files_sha256: $SOURCE_FILES_SHA256
- source_snapshot_manifest: source-files.sha256
- source_snapshot_sha256: $SOURCE_FILES_SHA256
- package_file_manifest: package-files.sha256
- jit_mode_matrix: profile/jit_mode_matrix.json
- jit_mode_matrix_schema: profile/jit_mode_matrix.schema.json
- sat_profile_matrix: profile/sat_profile_matrix.json
- sat_profile_matrix_schema: profile/sat_profile_matrix.schema.json
- pgo_policy: $([[ "$SOURCE_MODE" == "archive" ]] && printf 'required-source-build-pgo/v1' || printf 'not-applicable-no-source/v1')
- pgo_marker: ay.pgo.json
- pgo_profdata: ay.pgo.profdata
- pgo_profile_use_required: $([[ "$SOURCE_MODE" == "archive" ]] && printf 'true' || printf 'false')
- staged_binary: $STAGED_BINARY_DECLARED
- local_runsh_preflight_binary: $LOCAL_RUNSH_PREFLIGHT_BINARY
- local_runsh_preflight_policy: $([[ "$LOCAL_RUNSH_PREFLIGHT_BINARY" == "true" ]] && printf 'local-runsh-smoke-only-not-submission-evidence/v1' || printf 'not-applicable')

Build:

\`\`\`sh
./build.sh
\`\`\`

Run:

\`\`\`sh
./run.sh input.cnf output-dir
\`\`\`
EOF

    cat >"$root_dir/build.sh" <<'EOF'
#!/bin/sh
set -eu

ROOT_DIR="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"

sha256_file() {
    path="$1"
    case "$path" in
        *\\*|?:*) if command -v cygpath >/dev/null 2>&1; then
            path="$(cygpath -u -- "$path" 2>/dev/null || printf '%s\n' "$path")"
        fi ;;
    esac
    if command -v sha256sum >/dev/null 2>&1; then
        sha256sum "$path" | awk '{ print $1 }'
    else
        shasum -a 256 "$path" | awk '{ print $1 }'
    fi
}

file_size_bytes() {
    path="$1"
    if size="$(stat -c '%s' "$path" 2>/dev/null)"; then
        printf '%s\n' "$size"
    else
        stat -f '%z' "$path"
    fi
}

json_escape() {
    printf '%s' "$1" | awk 'BEGIN { ORS = "" } { gsub(/\\/, "\\\\"); gsub(/"/, "\\\""); printf "%s", $0 }'
}

manifest_value() {
    key="$1"
    awk -F': ' -v key="$key" '$1 == "- " key { print $2; exit }' "$ROOT_DIR/SAT26_SUBMISSION.md"
}

profile_value() {
    key="$1"
    awk -F'"' -v key="$key" '$2 == key { print $4; exit }' "$ROOT_DIR/profile/satcomp26_profile.json"
}

write_files_sha256() {
    base_dir="$1"
    out="$2"

    (
        cd "$base_dir"
        find . -type f -print | LC_ALL=C sort
    ) | while IFS= read -r rel; do
        rel="${rel#./}"
        hash="$(sha256_file "$base_dir/$rel")"
        printf '%s  %s\n' "$hash" "$rel"
    done >"$out"
}

write_package_files_sha256() {
    root_dir="$1"
    out="$2"

    (
        cd "$root_dir"
        find . -type f \
            ! -path './build/*' \
            ! -path './ay' \
            ! -path './package-files.sha256' \
            -print | LC_ALL=C sort
    ) | while IFS= read -r rel; do
        rel="${rel#./}"
        hash="$(sha256_file "$root_dir/$rel")"
        printf '%s  %s\n' "$hash" "$rel"
    done >"$out"
}

verify_package_files() {
    manifest="$ROOT_DIR/package-files.sha256"
    saw_submission=0
    saw_profile=0
    saw_staged_binary_manifest=0
    cr="$(printf '\r')"

    if [ ! -f "$manifest" ]; then
        echo "ERROR: package-files.sha256 is missing" >&2
        exit 2
    fi

    while IFS= read -r line || [ -n "$line" ]; do
        line="${line%$cr}"
        [ -n "$line" ] || continue
        expected="${line%%  *}"
        rel="${line#*  }"
        if [ "$expected" = "$line" ] || [ -z "$rel" ]; then
            echo "ERROR: malformed package-files.sha256 entry: $line" >&2
            exit 2
        fi
        if [ "${#expected}" -ne 64 ]; then
            echo "ERROR: malformed package-files.sha256 hash for $rel" >&2
            exit 2
        fi
        case "$expected" in
            *[!0123456789abcdef]*)
                echo "ERROR: malformed package-files.sha256 hash for $rel" >&2
                exit 2
                ;;
        esac
        case "$rel" in
            /*|..|../*|*/../*|*/..)
                echo "ERROR: unsafe package-files.sha256 path: $rel" >&2
                exit 2
                ;;
        esac

        case "$rel" in
            SAT26_SUBMISSION.md)
                saw_submission=1
                ;;
            profile/satcomp26_profile.json)
                saw_profile=1
                ;;
            staged-binary.sha256)
                saw_staged_binary_manifest=1
                ;;
        esac

        if [ ! -f "$ROOT_DIR/$rel" ]; then
            echo "ERROR: package-files.sha256 lists missing file: $rel" >&2
            exit 2
        fi
        actual="$(sha256_file "$ROOT_DIR/$rel")"
        if [ "$actual" != "$expected" ]; then
            echo "ERROR: package-files.sha256 hash mismatch for $rel" >&2
            exit 2
        fi
    done <"$manifest"

    if [ "$saw_submission" -ne 1 ]; then
        echo "ERROR: package-files.sha256 is missing SAT26_SUBMISSION.md" >&2
        exit 2
    fi
    if [ "$saw_profile" -ne 1 ]; then
        echo "ERROR: package-files.sha256 is missing profile/satcomp26_profile.json" >&2
        exit 2
    fi
    if [ ! -f "$ROOT_DIR/source.tar.gz" ] && [ -x "$ROOT_DIR/ay" ] && [ "$saw_staged_binary_manifest" -ne 1 ]; then
        echo "ERROR: package-files.sha256 is missing staged-binary.sha256 for staged ay" >&2
        exit 2
    fi
}

verify_staged_binary_hash() {
    staged_manifest="$ROOT_DIR/staged-binary.sha256"
    line_count=0
    first_line=""

    if [ ! -f "$staged_manifest" ]; then
        echo "ERROR: staged-binary.sha256 is missing for staged ay" >&2
        exit 2
    fi

    while IFS= read -r line || [ -n "$line" ]; do
        line_count=$((line_count + 1))
        if [ "$line_count" -eq 1 ]; then
            first_line="$line"
        fi
    done <"$staged_manifest"

    if [ "$line_count" -ne 1 ]; then
        echo "ERROR: staged-binary.sha256 must contain exactly one ay entry" >&2
        exit 2
    fi

    expected="${first_line%%  *}"
    rel="${first_line#*  }"
    if [ "$expected" = "$first_line" ] || [ "$rel" != "ay" ]; then
        echo "ERROR: staged-binary.sha256 must contain one 'sha256  ay' entry" >&2
        exit 2
    fi
    if [ "${#expected}" -ne 64 ]; then
        echo "ERROR: malformed staged-binary.sha256 hash for ay" >&2
        exit 2
    fi
    case "$expected" in
        *[!0123456789abcdef]*)
            echo "ERROR: malformed staged-binary.sha256 hash for ay" >&2
            exit 2
            ;;
    esac

    actual="$(sha256_file "$ROOT_DIR/ay")"
    if [ "$actual" != "$expected" ]; then
        echo "ERROR: staged-binary.sha256 does not match ay" >&2
        exit 2
    fi
}

verify_declared_hash() {
    label="$1"
    path="$2"
    expected="$(manifest_value "$label")"

    if [ -z "$expected" ]; then
        echo "ERROR: SAT26_SUBMISSION.md is missing $label" >&2
        exit 2
    fi
    actual="$(sha256_file "$path")"
    if [ "$actual" != "$expected" ]; then
        echo "ERROR: $label does not match $(basename "$path")" >&2
        exit 2
    fi
}

verify_profile_hash() {
    label="$1"
    path="$2"

    if [ ! -f "$ROOT_DIR/profile/satcomp26_profile.json" ]; then
        echo "ERROR: profile/satcomp26_profile.json is missing" >&2
        exit 2
    fi
    expected="$(profile_value "$label")"
    if [ -z "$expected" ]; then
        echo "ERROR: profile/satcomp26_profile.json is missing $label" >&2
        exit 2
    fi
    actual="$(sha256_file "$path")"
    if [ "$actual" != "$expected" ]; then
        echo "ERROR: profile/satcomp26_profile.json $label does not match $(basename "$path")" >&2
        exit 2
    fi
}

append_rustflag() {
    base="$1"
    flag="$2"
    if [ -n "$base" ]; then
        printf '%s %s\n' "$base" "$flag"
    else
        printf '%s\n' "$flag"
    fi
}

find_llvm_profdata() {
    if command -v rustc >/dev/null 2>&1; then
        sysroot="$(rustc --print sysroot 2>/dev/null || true)"
        host="$(rustc -vV 2>/dev/null | awk '/^host:/ { print $2; exit }')"
        if [ -n "$sysroot" ] && [ -n "$host" ]; then
            candidate="$sysroot/lib/rustlib/$host/bin/llvm-profdata"
            if [ -x "$candidate" ]; then
                printf '%s\n' "$candidate"
                return 0
            fi
        fi
        if [ -n "$sysroot" ]; then
            candidate="$sysroot/bin/llvm-profdata"
            if [ -x "$candidate" ]; then
                printf '%s\n' "$candidate"
                return 0
            fi
        fi
    fi
    if command -v llvm-profdata >/dev/null 2>&1; then
        command -v llvm-profdata
        return 0
    fi
    return 1
}

write_pgo_training_cnfs() {
    training_dir="$1"
    mkdir -p "$training_dir"
    cat >"$training_dir/sat-unit.cnf" <<'CNF'
c ay SAT26 PGO training: SAT unit
p cnf 1 1
1 0
CNF
    cat >"$training_dir/unsat-unit.cnf" <<'CNF'
c ay SAT26 PGO training: UNSAT unit
p cnf 1 2
1 0
-1 0
CNF
    cat >"$training_dir/chain-unsat.cnf" <<'CNF'
c ay SAT26 PGO training: bounded propagation chain
p cnf 3 4
1 0
-1 2 0
-2 3 0
-3 0
CNF
}

write_pgo_disabled_marker() {
    reason="$1"
    detail="$2"
    marker_path="$ROOT_DIR/ay.pgo.json"
    escaped_reason="$(json_escape "$reason")"
    escaped_detail="$(json_escape "$detail")"

    cat >"$marker_path" <<EOF_MARKER
{
  "schema": "ay-pgo-build-provenance/v1",
  "pgo_enabled": false,
  "failure": {
    "reason": "$escaped_reason",
    "detail": "$escaped_detail"
  },
  "build": {
    "final_profile": "release-perf",
    "profile_use_required": true
  },
  "profile": {
    "profdata_path": "ay.pgo.profdata"
  }
}
EOF_MARKER
    write_package_files_sha256 "$ROOT_DIR" "$ROOT_DIR/package-files.sha256"
}

write_local_validation_marker() {
    validation_binary="$1"
    validation_binary_real="$2"
    source_commit="$(manifest_value source_commit)"
    source_archive_sha256="$(manifest_value source_archive_sha256)"
    source_files_sha256="$(manifest_value source_files_sha256)"
    rustc_version="$(rustc --version 2>/dev/null || true)"
    validation_version="$("$validation_binary" --version 2>&1 || true)"
    validation_commit="$(printf '%s\n' "$validation_version" | awk -F= '$1 == "build.commit" { print $2; exit }')"
    validation_stamp="$(printf '%s\n' "$validation_version" | awk -F= '$1 == "build.stamp" { print $2; exit }')"

    cat >"$ROOT_DIR/ay.local-validation-build.json" <<EOF_MARKER
{
  "schema": "ay-sat26-local-validation-build/v1",
  "score_bearing": false,
  "official_submission_build": false,
  "reason": "local run.sh validation binary staged via AY_SAT26_LOCAL_VALIDATION_BINARY",
  "source": {
    "source_kind": "sat26-source-root",
    "source_commit": "$(json_escape "$source_commit")",
    "source_archive_sha256": "$(json_escape "$source_archive_sha256")",
    "source_files_sha256": "$(json_escape "$source_files_sha256")"
  },
  "toolchain": {
    "rustc": "$(json_escape "$rustc_version")"
  },
  "binary": {
    "input_path": "$(json_escape "$validation_binary_real")",
    "input_sha256": "$(sha256_file "$validation_binary")",
    "build_commit": "$(json_escape "$validation_commit")",
    "build_stamp": "$(json_escape "$validation_stamp")",
    "source_commit_match": true,
    "path": "ay",
    "sha256": "$(sha256_file "$ROOT_DIR/ay")",
    "size_bytes": $(file_size_bytes "$ROOT_DIR/ay")
  }
}
EOF_MARKER
}

fail_pgo() {
    reason="$1"
    detail="$2"
    write_pgo_disabled_marker "$reason" "$detail"
    echo "ERROR: SAT26 source build requires PGO: $detail" >&2
    exit 2
}

run_pgo_training_instance() {
    training_bin="$1"
    training_cnf="$2"
    training_out="$3"
    variant="$(manifest_value variant)"
    profile_id="$(manifest_value profile_id)"
    profile_identity="$(manifest_value profile_identity)"
    proof_path="$training_out/$(basename "$training_cnf").lrat"

    mkdir -p "$training_out"
    rm -f "$proof_path"
    set +e
    LLVM_PROFILE_FILE="$PGO_PROFILE_PATTERN" \
    AY_INTERNAL_PROVENANCE_CHILD=1 \
    AY_INTERNAL_SATCOMP_WRAPPER="sat26-pgo-training-lrat-v1" \
    AY_SAT_COMPETITION_PROFILE="$profile_id" \
    AY_SAT_PROFILE_ID="$profile_identity" \
    AY_SAT_VARIANT="$variant" \
    AY_COMPETITION_JIT_MODE="off" \
        "$training_bin" solve \
            --sat-variant "$variant" \
            --proof "$proof_path" \
            --proof-format lrat \
            --no-verify-proof \
            "$training_cnf" >/dev/null 2>&1
    rc=$?
    set -e
    case "$rc" in
        0|10|20)
            ;;
        *)
            fail_pgo "training-failed" "PGO training failed for $(basename "$training_cnf") with exit $rc"
            ;;
    esac
}

write_pgo_marker() {
    profraw_count="$1"
    final_rustflags="$2"
    profile_use_flag="-Cprofile-use=$ROOT_DIR/ay.pgo.profdata"
    final_command="CARGO_SKIP_CACHE=1 RUSTFLAGS=\"$final_rustflags\" cargo build --locked --profile release-perf -p ay --bin ay --features cli"
    rustc_version="$(rustc --version 2>/dev/null || true)"
    llvm_profdata_version="$("$LLVM_PROFDATA" --version 2>&1 | sed -n '1p' || true)"
    source_commit="$(manifest_value source_commit)"
    source_archive_sha256="$(manifest_value source_archive_sha256)"
    source_files_sha256="$(manifest_value source_files_sha256)"

    cat >"$ROOT_DIR/ay.pgo.json" <<EOF_MARKER
{
  "schema": "ay-pgo-build-provenance/v1",
  "pgo_enabled": true,
  "source": {
    "source_kind": "sat26-source-root",
    "source_commit": "$(json_escape "$source_commit")",
    "source_archive_sha256": "$(json_escape "$source_archive_sha256")",
    "source_files_sha256": "$(json_escape "$source_files_sha256")"
  },
  "toolchain": {
    "rustc": "$(json_escape "$rustc_version")",
    "llvm_profdata": "$(json_escape "$LLVM_PROFDATA")",
    "llvm_profdata_version": "$(json_escape "$llvm_profdata_version")"
  },
  "build": {
    "final_profile": "release-perf",
    "final_command": "$(json_escape "$final_command")",
    "profile_generate_flag": "$(json_escape "-Cprofile-generate=$PGO_RAW_DIR")",
    "profile_use_flag": "$(json_escape "$profile_use_flag")"
  },
  "profile": {
    "profdata_path": "ay.pgo.profdata",
    "profdata_sha256": "$(sha256_file "$ROOT_DIR/ay.pgo.profdata")",
    "profdata_size_bytes": $(file_size_bytes "$ROOT_DIR/ay.pgo.profdata"),
    "profraw_count": $profraw_count,
    "training_cnf_count": 3
  },
  "binary": {
    "path": "ay",
    "sha256": "$(sha256_file "$ROOT_DIR/ay")",
    "size_bytes": $(file_size_bytes "$ROOT_DIR/ay")
  }
}
EOF_MARKER
}

build_source_with_pgo() {
    source_dir="$BUILD_DIR/source"
    PGO_RAW_DIR="$BUILD_DIR/pgo-profraw"
    PGO_TRAINING_DIR="$BUILD_DIR/pgo-training"
    PGO_TRAINING_OUT="$BUILD_DIR/pgo-training-output"
    PGO_PROFILE_PATTERN="$PGO_RAW_DIR/ay-%p-%m.profraw"
    merged_profdata="$BUILD_DIR/ay.pgo.profdata"
    BASE_RUSTFLAGS="${RUSTFLAGS:-}"
    # Match Kissat/CaDiCaL's -march=native floor: the Linux competition binary
    # must NOT ship at the x86-64-v1 (SSE2) baseline. A plain RUSTFLAGS env
    # overrides .cargo/config.toml's per-target rustflags, so set target-cpu here
    # too (both PGO builds below inherit BASE_RUSTFLAGS). Respect a caller-set
    # target-cpu; override the floor with AY_SAT_TARGET_CPU (e.g. "native" when
    # build.sh runs on the judge box).
    case "$BASE_RUSTFLAGS" in
        *target-cpu*) ;;
        *) BASE_RUSTFLAGS="$(append_rustflag "$BASE_RUSTFLAGS" "-Ctarget-cpu=${AY_SAT_TARGET_CPU:-x86-64-v3}")" ;;
    esac
    SOURCE_BUILD_COMMIT="$(manifest_value source_commit)"
    SOURCE_BUILD_DIRTY="$(manifest_value source_dirty_at_stage_time)"

    case "$SOURCE_BUILD_DIRTY" in
        false) ;;
        true)
            fail_pgo "dirty-source" "Main/regular SAT26 source build requires source_dirty_at_stage_time=false"
            ;;
        *)
            fail_pgo "invalid-source-dirty-state" "invalid source_dirty_at_stage_time: $SOURCE_BUILD_DIRTY"
            ;;
    esac
    if [ -z "$SOURCE_BUILD_COMMIT" ] || [ "$SOURCE_BUILD_COMMIT" = "unknown" ]; then
        fail_pgo "missing-source-commit" "SAT26 source build requires source_commit provenance"
    fi

    LLVM_PROFDATA="$(find_llvm_profdata || true)"
    if [ -z "$LLVM_PROFDATA" ]; then
        fail_pgo "missing-llvm-profdata" "llvm-profdata is required to merge Rust PGO profiles"
    fi

    rm -rf "$PGO_RAW_DIR" "$PGO_TRAINING_DIR" "$PGO_TRAINING_OUT"
    mkdir -p "$PGO_RAW_DIR"
    write_pgo_training_cnfs "$PGO_TRAINING_DIR"

    instrument_rustflags="$(append_rustflag "$BASE_RUSTFLAGS" "-Cprofile-generate=$PGO_RAW_DIR")"
    AY_SOURCE_GIT_COMMIT="$SOURCE_BUILD_COMMIT" \
    AY_SOURCE_GIT_DIRTY="$SOURCE_BUILD_DIRTY" \
    CARGO_SKIP_CACHE=1 RUSTFLAGS="$instrument_rustflags" cargo build --locked --profile release-perf -p ay --bin ay --features cli || \
        fail_pgo "instrumented-build-failed" "instrumented release-perf build failed"

    instrumented_bin="$source_dir/target/release-perf/ay"
    if [ ! -x "$instrumented_bin" ]; then
        fail_pgo "missing-instrumented-binary" "instrumented build did not produce target/release-perf/ay"
    fi

    for training_cnf in "$PGO_TRAINING_DIR"/*.cnf; do
        [ -f "$training_cnf" ] || continue
        run_pgo_training_instance "$instrumented_bin" "$training_cnf" "$PGO_TRAINING_OUT"
    done

    profraw_count="$(find "$PGO_RAW_DIR" -type f -name '*.profraw' -print | wc -l | tr -d ' ')"
    if [ "$profraw_count" -lt 1 ]; then
        fail_pgo "missing-profraw" "PGO training did not produce any .profraw files"
    fi

    "$LLVM_PROFDATA" merge -o "$merged_profdata" "$PGO_RAW_DIR"/*.profraw || \
        fail_pgo "profdata-merge-failed" "llvm-profdata failed to merge PGO profiles"
    if [ ! -s "$merged_profdata" ]; then
        fail_pgo "empty-profdata" "llvm-profdata produced an empty profdata artifact"
    fi
    cp "$merged_profdata" "$ROOT_DIR/ay.pgo.profdata"

    cargo clean --profile release-perf >/dev/null 2>&1 || true
    final_rustflags="$(append_rustflag "$BASE_RUSTFLAGS" "-Cprofile-use=$ROOT_DIR/ay.pgo.profdata")"
    AY_SOURCE_GIT_COMMIT="$SOURCE_BUILD_COMMIT" \
    AY_SOURCE_GIT_DIRTY="$SOURCE_BUILD_DIRTY" \
    CARGO_SKIP_CACHE=1 RUSTFLAGS="$final_rustflags" cargo build --locked --profile release-perf -p ay --bin ay --features cli || \
        fail_pgo "profile-use-build-failed" "final release-perf build with -Cprofile-use failed"

    if [ ! -x "$source_dir/target/release-perf/ay" ]; then
        fail_pgo "missing-final-binary" "final PGO build did not produce target/release-perf/ay"
    fi
    cp "$source_dir/target/release-perf/ay" "$ROOT_DIR/ay"
    chmod 755 "$ROOT_DIR/ay"
    write_pgo_marker "$profraw_count" "$final_rustflags"
    write_package_files_sha256 "$ROOT_DIR" "$ROOT_DIR/package-files.sha256"
}

build_with_local_validation_binary() {
    validation_binary="$1"
    source_dir="$BUILD_DIR/source"
    SOURCE_BUILD_COMMIT="$(manifest_value source_commit)"
    SOURCE_BUILD_DIRTY="$(manifest_value source_dirty_at_stage_time)"

    case "$SOURCE_BUILD_DIRTY" in
        false) ;;
        true)
            fail_pgo "dirty-source" "local SAT26 validation binary requires source_dirty_at_stage_time=false"
            ;;
        *)
            fail_pgo "invalid-source-dirty-state" "invalid source_dirty_at_stage_time: $SOURCE_BUILD_DIRTY"
            ;;
    esac
    if [ -z "$SOURCE_BUILD_COMMIT" ] || [ "$SOURCE_BUILD_COMMIT" = "unknown" ]; then
        fail_pgo "missing-source-commit" "local SAT26 validation binary requires source_commit provenance"
    fi
    if [ ! -x "$validation_binary" ]; then
        fail_pgo "missing-local-validation-binary" "AY_SAT26_LOCAL_VALIDATION_BINARY is not executable: $validation_binary"
    fi

    case "$validation_binary" in
        /*) validation_binary_real="$validation_binary" ;;
        *) validation_binary_real="$(cd "$(dirname "$validation_binary")" && pwd)/$(basename "$validation_binary")" ;;
    esac
    validation_version="$("$validation_binary" --version 2>&1)" || \
        fail_pgo "local-validation-binary-version-failed" "AY_SAT26_LOCAL_VALIDATION_BINARY --version failed: $validation_binary_real"
    validation_commit="$(printf '%s\n' "$validation_version" | awk -F= '$1 == "build.commit" { print $2; exit }')"
    if [ -z "$validation_commit" ]; then
        fail_pgo "local-validation-binary-missing-build-commit" "AY_SAT26_LOCAL_VALIDATION_BINARY did not report build.commit: $validation_binary_real"
    fi
    case "$validation_commit" in
        *-dirty)
            fail_pgo "local-validation-binary-dirty" "AY_SAT26_LOCAL_VALIDATION_BINARY is dirty-stamped: $validation_commit"
            ;;
    esac
    if [ "$validation_commit" != "$SOURCE_BUILD_COMMIT" ]; then
        fail_pgo "local-validation-binary-commit-mismatch" "AY_SAT26_LOCAL_VALIDATION_BINARY build.commit=$validation_commit does not match source_commit=$SOURCE_BUILD_COMMIT"
    fi

    cp "$validation_binary" "$ROOT_DIR/ay"
    chmod 755 "$ROOT_DIR/ay"
    write_local_validation_marker "$validation_binary" "$validation_binary_real"
    write_package_files_sha256 "$ROOT_DIR" "$ROOT_DIR/package-files.sha256"
    echo "local SAT26 validation binary staged: $ROOT_DIR/ay"
    echo "local SAT26 validation marker: $ROOT_DIR/ay.local-validation-build.json"
}

verify_package_files

if [ ! -f "$ROOT_DIR/source.tar.gz" ]; then
    if [ -x "$ROOT_DIR/ay" ]; then
        verify_staged_binary_hash
        echo "ay binary already staged: $ROOT_DIR/ay"
        exit 0
    fi
    echo "ERROR: source.tar.gz is missing and no ay binary is staged" >&2
    exit 2
fi

if [ ! -f "$ROOT_DIR/SAT26_SUBMISSION.md" ]; then
    echo "ERROR: SAT26_SUBMISSION.md is missing" >&2
    exit 2
fi
if [ ! -f "$ROOT_DIR/source-files.sha256" ]; then
    echo "ERROR: source-files.sha256 is missing" >&2
    exit 2
fi
verify_declared_hash source_archive_sha256 "$ROOT_DIR/source.tar.gz"
verify_declared_hash source_files_sha256 "$ROOT_DIR/source-files.sha256"
verify_profile_hash source_archive_sha256 "$ROOT_DIR/source.tar.gz"
verify_profile_hash source_files_sha256 "$ROOT_DIR/source-files.sha256"

BUILD_DIR="$ROOT_DIR/build"
rm -f "$ROOT_DIR/ay" "$ROOT_DIR/staged-binary.sha256" "$ROOT_DIR/ay.pgo.json" "$ROOT_DIR/ay.pgo.profdata"
rm -rf "$BUILD_DIR"
mkdir -p "$BUILD_DIR"
tar xzf "$ROOT_DIR/source.tar.gz" -C "$BUILD_DIR"
if [ ! -d "$BUILD_DIR/source" ]; then
    echo "ERROR: source.tar.gz does not contain source/ root" >&2
    exit 2
fi
write_files_sha256 "$BUILD_DIR/source" "$BUILD_DIR/source-files.actual.sha256"
if ! cmp -s "$ROOT_DIR/source-files.sha256" "$BUILD_DIR/source-files.actual.sha256"; then
    echo "ERROR: source-files.sha256 does not match source.tar.gz contents" >&2
    exit 2
fi

if ! command -v cargo >/dev/null 2>&1; then
    if command -v rustup >/dev/null 2>&1; then
        :
    else
        curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs |
            sh -s -- -y --default-toolchain stable
        # shellcheck disable=SC1091
        . "$HOME/.cargo/env"
    fi
fi

cd "$BUILD_DIR/source"
if [ -n "${AY_SAT26_LOCAL_VALIDATION_BINARY:-}" ]; then
    build_with_local_validation_binary "$AY_SAT26_LOCAL_VALIDATION_BINARY"
else
    build_source_with_pgo
fi
EOF
    chmod 755 "$root_dir/build.sh"

    cat >"$root_dir/run.sh" <<EOF
#!/usr/bin/env bash
set -euo pipefail

if [[ \$# -ne 2 ]]; then
    echo "usage: ./run.sh <instance> <output_dir>" >&2
    exit 2
fi

SCRIPT_DIR="\$(cd "\$(dirname "\$0")" && pwd)"
INSTANCE="\$1"
OUTPUT_DIR="\$2"
mkdir -p "\$OUTPUT_DIR"

if [[ ! -x "\$SCRIPT_DIR/ay" ]]; then
    echo "ERROR: ay binary missing; run ./build.sh first" >&2
    exit 2
fi

TIMEOUT_ARGS=()
if [[ -n "\${SATCOMP_TIMEOUT_MS:-}" ]]; then
    TIMEOUT_ARGS+=(--timeout="\$SATCOMP_TIMEOUT_MS")
elif [[ -n "\${BENCHCLOUD_WALLCLOCK_LIMIT:-}" && "\$BENCHCLOUD_WALLCLOCK_LIMIT" =~ ^[0-9]+$ && "\$BENCHCLOUD_WALLCLOCK_LIMIT" -gt 5 ]]; then
    BUDGET_MS=\$(( (BENCHCLOUD_WALLCLOCK_LIMIT - 5) * 1000 ))
    TIMEOUT_ARGS+=(--timeout="\$BUDGET_MS")
fi

STATS_ARGS=()
if [[ "\${AY_SATCOMP_MATRIX:-0}" == "1" || "\${AY_SAT_EMIT_STATS_JSON:-0}" == "1" ]]; then
    STATS_ARGS+=(--stats-json)
fi

ARGS=(
    solve
    --sat-variant "$variant"
)

PROOF_OUT="\$OUTPUT_DIR/proof.out"
rm -f "\$PROOF_OUT"
ARGS+=(--proof "\$PROOF_OUT" --proof-format "$PROOF_FORMAT" --no-verify-proof)

PROFILE_BCP_LEARNED_1963_BLOCKER_CERT_ELISION="${PROFILE_BCP_LEARNED_1963_BLOCKER_CERT_ELISIONS[$idx]}"
PROFILE_BCP_LEARNED_1963_BLOCKER_CERT_FALSE_REJECT_DEMOTE="${PROFILE_BCP_LEARNED_1963_BLOCKER_CERT_FALSE_REJECT_DEMOTES[$idx]}"
# B76: profile lever decisions travel as typed CLI flags, not env exports.
if [[ "\$PROFILE_BCP_LEARNED_1963_BLOCKER_CERT_ELISION" == "1" ]]; then
    ARGS+=(--sat-bcp-learned-1963-blocker-cert-elision)
fi
if [[ "\$PROFILE_BCP_LEARNED_1963_BLOCKER_CERT_FALSE_REJECT_DEMOTE" == "1" ]]; then
    ARGS+=(--sat-bcp-learned-1963-blocker-cert-false-reject-demote)
fi

PROFILE_DENSE_CLIQUE_PHP_PROOF_ROUTE="${PROFILE_DENSE_CLIQUE_PHP_PROOF_ROUTES[$idx]}"
if [[ "\$PROFILE_DENSE_CLIQUE_PHP_PROOF_ROUTE" == "1" ]]; then
    ARGS+=(--sat-dense-clique-php-proof-route)
fi

exec env -u AY_SAT_MAIN_ENABLE_STARTUP_PHASE_INIT \
    -u AY_SAT_TRACK \
    -u AY_SAT_AI_CLASS \
    AY_INTERNAL_PROVENANCE_CHILD=1 \
    AY_INTERNAL_SATCOMP_WRAPPER="$TRACK-$AI_CLASS-$variant-$PROOF_FORMAT-v1" \
    AY_SAT_COMPETITION_PROFILE="${PROFILE_IDS[$idx]}" \
    AY_SAT_PROFILE_ID="${PROFILE_IDENTITIES[$idx]}" \
    AY_SAT_VARIANT="${PROFILE_RUNTIME_VARIANTS[$idx]}" \
    AY_COMPETITION_JIT_MODE="${PROFILE_JIT_MODES[$idx]}" \
    "\$SCRIPT_DIR/ay" "\${ARGS[@]}" \${TIMEOUT_ARGS[@]+"\${TIMEOUT_ARGS[@]}"} \${STATS_ARGS[@]+"\${STATS_ARGS[@]}"} "\$INSTANCE"
EOF
    chmod 755 "$root_dir/run.sh"

    cat >"$root_dir/README.md" <<EOF
# AY SAT-COMP 2026 $TRACK/$AI_CLASS/$variant

This generated root follows the SAT-COMP BenchCloud/NHR interface:

    ./build.sh
    ./run.sh <instance.cnf> <output_dir>

UNSAT proofs are written to \`<output_dir>/proof.out\` in $PROOF_FORMAT format.
The exact profile metadata is in \`profile/satcomp26_profile.json\`.
The SAT profile matrix identity is \`${PROFILE_IDENTITIES[$idx]}\`.
Package and source hash closures are recorded in \`package-files.sha256\`,
\`source-files.sha256\`, and \`SAT26_SUBMISSION.md\`.
EOF
    write_package_files_sha256 "$root_dir"
    preflight_generated_root \
        "$root_dir" \
        "$TRACK" \
        "$AI_CLASS" \
        "$variant" \
        "$PROOF_FORMAT" \
        "${PROFILE_IDS[$idx]}" \
        "${PROFILE_IDENTITIES[$idx]}" \
        "${PROFILE_RUNTIME_VARIANTS[$idx]}" \
        "${PROFILE_JIT_MODES[$idx]}"
done

{
    printf '{\n'
    printf '  "source_commit": "%s",\n' "$COMMIT"
    printf '  "source_dirty_at_stage_time": %s,\n' "$SOURCE_DIRTY_AT_STAGE_TIME"
    printf '  "source_git_status_sha256": "%s",\n' "$SOURCE_GIT_STATUS_SHA256"
    printf '  "source_archive_sha256": "%s",\n' "$SOURCE_ARCHIVE_SHA256"
    printf '  "source_files_sha256": "%s",\n' "$SOURCE_FILES_SHA256"
    printf '  "track": "%s",\n' "$TRACK"
    printf '  "ai_class": "%s",\n' "$AI_CLASS"
    printf '  "proof_format": "%s",\n' "$PROOF_FORMAT"
    printf '  "roots": [\n'
    for idx in "${!ROOT_NAMES[@]}"; do
        comma=","
        [[ "$idx" -eq $((${#ROOT_NAMES[@]} - 1)) ]] && comma=""
        printf '    {"variant": "%s", "path": "%s"}%s\n' "${VARIANTS[$idx]}" "${ROOT_NAMES[$idx]}" "$comma"
    done
    printf '  ]\n'
    printf '}\n'
} >"$OUTPUT_DIR/lineup.json"

echo "Generated SAT-COMP 2026 roots under: $OUTPUT_DIR"
for root_name in "${ROOT_NAMES[@]}"; do
    echo "  $OUTPUT_DIR/$root_name"
done

#!/bin/sh
# ay-script-lib: veripb-build-id
#
# THE one authority for the pinned-checker cache key. Every entry point that
# builds or resolves the pinned VeriPB by cache path under
# ${VERIPB_CACHE:-${XDG_CACHE_HOME:-~/.cache}/ay-veripb} speaks this format:
#
#   keyed  : <VERIPB_COMMIT>-<patch-sha256 first 12>-rustc<release>[-<commit-hash first 10>]
#   legacy : <VERIPB_COMMIT>-<patch-sha256 first 12>
#
# The legacy form is the pre-compiler-key layout (before commit 8499748c6,
# 2026-08-30). Builds at that path are NOT orphaned: their binaries are still
# the pinned source, and every gate re-proves behaviour (version cross-check,
# self-test battery, 22 must-reject soundness fixtures) before believing a
# verdict, so resolvers may accept a legacy BINARY. What nothing may do is
# compile INSIDE a cache directory whose key does not name the current
# compiler — that is exactly the E0514 mixed-rlib failure the key exists to
# prevent (see the prose in scripts/ci/pb_certified_gate.sh, phase 2).
#
# Consumers of this contract:
#   scripts/ci/pb_certified_gate.sh    builds + resolves KEYED ONLY — it also
#                                      compiles and tests veripb-core-proved
#                                      inside the cache dir (phase 2b), so a
#                                      foreign-compiler dir is unusable to it.
#   scripts/cert_ci.sh                 resolves keyed, falls back to a legacy
#                                      build's binary (announced), builds keyed.
#   crates/ay-test-support/src/veripb.rs
#   crates/ay/src/maxsat_cert.rs       resolve any cache dir matching the
#                                      identity prefix (keyed or legacy);
#                                      they never build.
#
# The Rust side pins this file's format with EXECUTABLE tests
# (`shell_and_rust_agree_on_the_cache_key` and neighbours in
# crates/ay-test-support/src/veripb.rs): they run these functions under a stub
# compiler and compare byte-for-byte with the Rust computation. Change the
# format here and those tests fail until the Rust side moves with it. Do not
# reimplement any of this inline in a gate script — that is the drift this
# file exists to end (pb_certified_gate.sh grew a keyed id on 2026-08-30 while
# cert_ci.sh and both Rust resolvers still computed the legacy one, so the
# same pinned checker lived at two paths depending on who built it).
#
# WHICH COMPILER KEYS THE CACHE: the one the build will actually run. Builds
# go through veripb_cargo (below): `targo --unverified` wherever the Trust
# toolchain is installed (owner ruling 2026-09-23: Rust here is targo), plain
# `cargo` on a host without it. Resolved as
#   1. $RUSTC        — both frontends honour it, so the key must too;
#   2. $(compiler_consumer --print sysroot)/bin/rustc — the compiler targo runs. It
#      outranks a PATH rustc: inside aterm a bare `rustc` is a reroute stub,
#      and on a Trust machine it is not what builds the checker;
#   3. rustc on PATH — plain cargo's default resolution, for a host without
#      the Trust toolchain.
# No compiler at all is a loud, fail-closed error: a cache keyed blindly is a
# cache that will hand a foreign-compiler build to a gate that compiles in it.
# Callers that BUILD with the resolved compiler must pass it to cargo as
# RUSTC=$(veripb_rustc_path) so the compiler named in the key is the compiler
# that actually built the artifact.

# Absolute path of the compiler that keys the cache (resolution order above).
# Prints the path on stdout; returns 2 (with the fix on stderr) when none of
# the three steps yields an executable compiler.
veripb_rustc_path() {
    if [ -n "${RUSTC:-}" ]; then
        if [ -x "$RUSTC" ]; then
            printf '%s\n' "$RUSTC"
            return 0
        fi
        echo "ERROR: \$RUSTC is set to '$RUSTC', which is not executable." >&2
        echo "       the build would fail on it too; unset RUSTC or fix the path." >&2
        return 2
    fi
    if command -v compiler_consumer >/dev/null 2>&1; then
        _vbi_sysroot=$(compiler_consumer --print sysroot 2>/dev/null) || _vbi_sysroot=
        if [ -n "$_vbi_sysroot" ] && [ -x "$_vbi_sysroot/bin/rustc" ]; then
            printf '%s\n' "$_vbi_sysroot/bin/rustc"
            return 0
        fi
    fi
    _vbi_rustc=$(command -v rustc 2>/dev/null) || _vbi_rustc=
    if [ -n "$_vbi_rustc" ]; then
        printf '%s\n' "$_vbi_rustc"
        return 0
    fi
    echo "ERROR: no compiler to key the veripb cache: \$RUSTC is unset, no compiler_consumer" >&2
    echo "       sysroot supplies one, and no 'rustc' is on PATH. Refusing to key a" >&2
    echo "       cache blindly — install a toolchain or set RUSTC=/path/to/rustc." >&2
    return 2
}

# The Cargo-family frontend for the pinned-checker builds (and the ay-pb
# solver pb_certified_gate.sh certifies): `targo` where the Trust toolchain is
# installed, in its unverified lane for a compilation command — these builds
# are measurement subjects, not proof claims — and plain `cargo` on a host
# without it. The discriminator is the only one that holds: the real targo
# accepts `--unverified --version`, stock Cargo refuses the flag.
veripb_cargo() {
    if targo --unverified --version >/dev/null 2>&1; then
        case "${1:-}" in
            build|check|test|run|bench|rustc|install) targo --unverified "$@" ;;
            *) targo "$@" ;;
        esac
    else
        cargo "$@"
    fi
}

# `release[-commithash10]` of the keying compiler, sanitised for use in a
# directory name. `rustc -vV` prints commit-hash BEFORE release, so the fields
# are picked by name — a positional concatenation yields a directory name with
# no human-readable version in it.
veripb_rustc_fingerprint() {
    _vbi_path=$(veripb_rustc_path) || return 2
    _vbi_fp=$("$_vbi_path" -vV 2>/dev/null | awk '
        /^release:/     {r=$2}
        /^commit-hash:/ {h=substr($2,1,10)}
        END {if (r != "") printf "%s%s", r, (h == "" ? "" : "-" h)}' \
        | tr -c 'A-Za-z0-9._-' '_')
    if [ -z "$_vbi_fp" ]; then
        echo "ERROR: '$_vbi_path -vV' yielded no release field to fingerprint." >&2
        echo "       Refusing to key the veripb cache on an unidentifiable compiler." >&2
        return 2
    fi
    printf '%s\n' "$_vbi_fp"
}

# The plain `release` field of the keying compiler (for the non-release-
# compiler notice in pb_certified_gate.sh). Empty output means unidentifiable;
# callers already fail on veripb_rustc_fingerprint in that case.
veripb_rustc_release() {
    _vbi_path=$(veripb_rustc_path) || return 2
    "$_vbi_path" -vV 2>/dev/null | awk '/^release:/ {print $2}'
}

# veripb_build_id VERIPB_COMMIT VERIPB_PATCH_SHA256 -> the keyed cache id.
veripb_build_id() {
    _vbi_kfp=$(veripb_rustc_fingerprint) || return 2
    printf '%s-%s-rustc%s\n' "$1" "$(printf '%s' "$2" | cut -c1-12)" "$_vbi_kfp"
}

# veripb_legacy_build_id VERIPB_COMMIT VERIPB_PATCH_SHA256 -> the pre-2026-08-30
# unkeyed id. For RESOLVING existing builds only — never build at this path.
veripb_legacy_build_id() {
    printf '%s-%s\n' "$1" "$(printf '%s' "$2" | cut -c1-12)"
}

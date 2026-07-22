#!/bin/bash
# ay-script: linux-static-build
# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0

set -euo pipefail

TOOL="auto"
if [ "${1:-}" = "--tool" ]; then
    if [ "$#" -lt 2 ]; then
        echo "error: --tool requires one of: auto, native, cross, docker, zigbuild" >&2
        exit 2
    fi
    TOOL="$2"
    shift 2
fi

if [ "$#" -ne 0 ]; then
    echo "error: unexpected arguments: $*" >&2
    exit 2
fi

ROOT="$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)"
cd "$ROOT"

TARGET="x86_64-unknown-linux-musl"
OUT="target/$TARGET/release/ay"
BUILD_ARGS=(-p ay --bin ay --features cli --target "$TARGET" --release)

select_auto_tool() {
    if command -v cargo-zigbuild >/dev/null 2>&1; then
        printf 'zigbuild\n'
    elif command -v cross >/dev/null 2>&1; then
        printf 'cross\n'
    else
        printf 'native\n'
    fi
}

if [ "$TOOL" = "auto" ]; then
    TOOL="$(select_auto_tool)"
fi

echo "Building static Linux x86_64 ay CLI binary with $TOOL..."

configure_zig_musl_cc_env() {
    # gmp-mpfr-sys invokes GMP's configure directly, which reads plain CC/AR
    # instead of Cargo's target-specific linker settings. The wrappers also
    # normalize cc-rs target flags that Zig does not accept verbatim.
    export CC="${CC:-$ROOT/scripts/zig-cc-x86_64-linux-musl.sh}"
    export CXX="${CXX:-$ROOT/scripts/zig-cxx-x86_64-linux-musl.sh}"
    export AR="${AR:-$ROOT/scripts/zig-ar.sh}"
    export RANLIB="${RANLIB:-$ROOT/scripts/zig-ranlib.sh}"
    export CC_x86_64_unknown_linux_musl="${CC_x86_64_unknown_linux_musl:-$CC}"
    export CXX_x86_64_unknown_linux_musl="${CXX_x86_64_unknown_linux_musl:-$CXX}"
    export AR_x86_64_unknown_linux_musl="${AR_x86_64_unknown_linux_musl:-$AR}"
    export RANLIB_x86_64_unknown_linux_musl="${RANLIB_x86_64_unknown_linux_musl:-$RANLIB}"
}

case "$TOOL" in
    zigbuild)
        configure_zig_musl_cc_env
        cargo zigbuild "${BUILD_ARGS[@]}"
        ;;
    cross|docker)
        cross build "${BUILD_ARGS[@]}"
        ;;
    native)
        cargo build "${BUILD_ARGS[@]}"
        ;;
    *)
        echo "error: unknown static build tool '$TOOL' (expected auto, native, cross, docker, zigbuild)" >&2
        exit 2
        ;;
esac

"$ROOT/scripts/validate_linux_static_binary.sh" "$OUT"
echo "Build complete. Binary is at $OUT"

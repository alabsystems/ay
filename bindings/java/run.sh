#!/usr/bin/env bash
# ay-script: java-binding-smoke
# Copyright 2026 Andrew Yates
# Author: Andrew Yates
# Licensed under the Apache License, Version 2.0
#
# Build and run the AY Java (FFM) binding test against libay_ffi.
#
# Prereqs:
#   * A JDK 22+ (java.lang.foreign is stable). This repo uses openjdk 26.
#     A JDK is installed but may not be on PATH; this script prepends the
#     Homebrew openjdk location if present.
#   * libay_ffi built:  cargo build -p ay-ffi   (debug) producing
#     target/{debug,release}/libay_ffi.{dylib,so}.
#
# Usage:  bash bindings/java/run.sh [--release]
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
SRC="$HERE/src"

# The JDK is installed but not on PATH; make it explicit (openjdk 26).
export PATH="/opt/homebrew/opt/openjdk/bin:$PATH"

PROFILE="debug"
if [[ "${1:-}" == "--release" ]]; then PROFILE="release"; fi
LIBDIR="$ROOT/target/$PROFILE"

# Resolve the platform library basename.
case "$(uname -s)" in
  Darwin) LIBNAME="libay_ffi.dylib" ;;
  *)      LIBNAME="libay_ffi.so" ;;
esac

if ! command -v javac >/dev/null 2>&1; then
  echo "ERROR: javac not found. Install a JDK 22+ (e.g. brew install openjdk)." >&2
  exit 2
fi
if [[ ! -e "$LIBDIR/$LIBNAME" ]]; then
  echo "ERROR: $LIBNAME not found in $LIBDIR. Run: cargo build -p ay-ffi" >&2
  exit 2
fi

# Point the binding at the freshly built native library.
export AYZ3_LIB="$LIBDIR/$LIBNAME"

OUT="$(mktemp -d)"
trap 'rm -rf "$OUT"' EXIT

echo "=== compiling (javac) ==="
javac -d "$OUT" "$SRC"/ay/z3/*.java

echo "=== running ay.z3.Test ==="
# --enable-native-access silences the restricted-method (FFM) warning; the
# binding only reaches native code through the loaded libay_ffi.
java --enable-native-access=ALL-UNNAMED -cp "$OUT" ay.z3.Test

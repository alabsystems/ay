#!/usr/bin/env bash
# ay-script: ocaml-binding-smoke
# Copyright 2026 Andrew Yates
# Author: Andrew Yates
# Licensed under the Apache License, Version 2.0
#
# Build and run the AY OCaml binding test against libay_ffi.
#
# Prereqs:
#   * OCaml native compiler (ocamlopt) on PATH  -- findlib/ctypes NOT required.
#   * libay_ffi built:  cargo build -p ay-ffi   (debug) producing
#     target/debug/libay_ffi.{a,dylib,so}.
#
# Usage:  bash bindings/ocaml/run.sh [--release]
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
INC="$ROOT/crates/ay-ffi/include"

PROFILE="debug"
if [[ "${1:-}" == "--release" ]]; then PROFILE="release"; fi
LIBDIR="$ROOT/target/$PROFILE"

if ! command -v ocamlopt >/dev/null 2>&1; then
  echo "ERROR: ocamlopt not found on PATH (install OCaml)." >&2
  exit 2
fi
if [[ ! -e "$LIBDIR/libay_ffi.a" && ! -e "$LIBDIR/libay_ffi.dylib" && ! -e "$LIBDIR/libay_ffi.so" ]]; then
  echo "ERROR: libay_ffi not found in $LIBDIR. Run: cargo build -p ay-ffi" >&2
  exit 2
fi

# Location of the OCaml C runtime headers (caml/*.h).
OCAML_LIBDIR="$(ocamlopt -config | awk -F': *' '/^standard_library:/ {print $2}')"

WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
cp "$HERE/ay.ml" "$HERE/ay.mli" "$HERE/ay_stubs.c" "$HERE/test_ay.ml" "$WORK/"
cd "$WORK"

# 1. Compile the C stubs (needs both the OCaml runtime headers and ay.h).
ocamlopt -c -ccopt "-I$OCAML_LIBDIR" -ccopt "-I$INC" ay_stubs.c

# 2. Compile the OCaml module (interface first, then implementation).
ocamlopt -c ay.mli
ocamlopt -c ay.ml
ocamlopt -c test_ay.ml

# 3. Link everything against the static AY FFI library.
#    Static linking avoids any DYLD_LIBRARY_PATH dance at run time.
UNAME="$(uname -s)"
EXTRA_LINK=""
if [[ "$UNAME" == "Darwin" ]]; then
  # libay_ffi pulls in system frameworks on macOS.
  EXTRA_LINK="-cclib -framework -cclib Security -cclib -framework -cclib CoreFoundation"
fi

if [[ -e "$LIBDIR/libay_ffi.a" ]]; then
  # shellcheck disable=SC2086
  ocamlopt -o test_ay \
    ay_stubs.o ay.cmx test_ay.cmx \
    -cclib "-L$LIBDIR" -cclib "-lay_ffi" $EXTRA_LINK
else
  # Fall back to the dynamic library.
  # shellcheck disable=SC2086
  ocamlopt -o test_ay \
    ay_stubs.o ay.cmx test_ay.cmx \
    -cclib "-L$LIBDIR" -cclib "-lay_ffi" $EXTRA_LINK
  export DYLD_LIBRARY_PATH="$LIBDIR:${DYLD_LIBRARY_PATH:-}"
  export LD_LIBRARY_PATH="$LIBDIR:${LD_LIBRARY_PATH:-}"
fi

echo "=== running test_ay ==="
./test_ay

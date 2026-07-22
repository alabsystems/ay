#!/usr/bin/env bash
# ay-script: linux-static-validate
# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0

set -euo pipefail

if [ "$#" -ne 1 ]; then
    echo "usage: $0 PATH_TO_AY_LINUX_STATIC_BINARY" >&2
    exit 2
fi

BIN="$1"

if [ ! -f "$BIN" ]; then
    echo "error: binary does not exist: $BIN" >&2
    exit 1
fi

if [ ! -x "$BIN" ]; then
    echo "error: binary is not executable: $BIN" >&2
    exit 1
fi

if ! command -v file >/dev/null 2>&1; then
    echo "error: 'file' is required to validate the Linux static binary" >&2
    exit 1
fi

INFO="$(file "$BIN")"
case "$INFO" in
    *ELF*64-bit*x86-64*statically\ linked*) ;;
    *)
        echo "error: expected a statically linked Linux x86_64 ELF binary: $BIN" >&2
        echo "file: $INFO" >&2
        exit 1
        ;;
esac

echo "validated static Linux x86_64 binary: $BIN"

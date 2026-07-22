#!/bin/bash
# ay-script: zig-cc
# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0

set -euo pipefail

if ! command -v zig >/dev/null 2>&1; then
    echo "error: zig is required for x86_64-unknown-linux-musl C compilation" >&2
    exit 127
fi

args=()
skip_next=0
for arg in "$@"; do
    if [ "$skip_next" -eq 1 ]; then
        skip_next=0
        continue
    fi

    case "$arg" in
        --target=x86_64-unknown-linux-musl|-target=x86_64-unknown-linux-musl)
            ;;
        --target|-target)
            skip_next=1
            ;;
        *)
            args+=("$arg")
            ;;
    esac
done

exec zig cc -target x86_64-linux-musl "${args[@]}"

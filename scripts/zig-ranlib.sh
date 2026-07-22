#!/bin/bash
# ay-script: zig-ranlib
# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0

set -euo pipefail

if ! command -v zig >/dev/null 2>&1; then
    echo "error: zig is required for x86_64-unknown-linux-musl ranlib" >&2
    exit 127
fi

exec zig ranlib "$@"

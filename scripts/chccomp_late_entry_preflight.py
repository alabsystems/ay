#!/usr/bin/env python3
# ay-script: chccomp-late-preflight
"""Compatibility wrapper for the Rust CHC-COMP late-entry preflight."""

import os
import subprocess
import sys


def main() -> int:
    ay_cli = os.environ.get("AY_CLI", "ay")
    command = [ay_cli, "submission", "preflight", "chc-late-entry", *sys.argv[1:]]
    return subprocess.call(command)


if __name__ == "__main__":
    raise SystemExit(main())

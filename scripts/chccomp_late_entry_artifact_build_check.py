#!/usr/bin/env python3
# ay-script: chccomp-late-artifact-check
"""Compatibility metadata for CHC-COMP late-entry artifact checks."""

TRACKS = [
    "BOOL",
    "BV",
    "BV-Lin",
    "LRA-Lin",
    "LIA-Lin",
    "LIA",
    "LIA-Arrays",
    "LIA-Lin-Arrays",
    "ADT-LIA",
    "ADT-LIA-Arrays",
    "mixed_LIA_LRA",
]


def main() -> int:
    print(",".join(TRACKS))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

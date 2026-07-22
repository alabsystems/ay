#!/usr/bin/env python3
# ay-script: chc-cert-check
# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0

"""Independent CHC SAFE-certificate checker (external SMT arbiter).

Takes an original CHC-COMP .smt2 file and an ay-chc-cert v1 certificate
(the define-fun block AY prints after `sat`), substitutes the model for the
predicate declarations, and asks an EXTERNAL solver (z3) to verify every
clause: for each (assert F) in the original file it checks (not F) is UNSAT.
All-UNSAT ==> the model is a genuine inductive invariant and `sat` is correct,
independent of anything AY computed.

Usage:
  python scripts/chc_cert_check.py --smt2 problem.smt2 --cert cert.smt2 \
      [--z3 reference/chc-solvers/bin/z3.exe] [--timeout-ms 60000]

The cert file: only its (define-fun ...) top-level forms are used.
Exit 0 = certificate VALID; 2 = some clause FAILED (prints which); 3 = unknown.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
import tempfile
from pathlib import Path


def top_level_forms(text: str) -> list[str]:
    """Split SMT-LIB text into top-level s-expression forms (comment-aware)."""
    forms = []
    depth = 0
    start = None
    in_comment = False
    in_string = False
    in_bars = False
    for i, ch in enumerate(text):
        if in_comment:
            if ch == "\n":
                in_comment = False
            continue
        if in_string:
            if ch == '"':
                in_string = False
            continue
        if in_bars:
            if ch == "|":
                in_bars = False
            continue
        if ch == ";":
            in_comment = True
            continue
        if ch == '"':
            in_string = True
            continue
        if ch == "|":
            in_bars = True
            continue
        if ch == "(":
            if depth == 0:
                start = i
            depth += 1
        elif ch == ")":
            depth -= 1
            if depth == 0 and start is not None:
                forms.append(text[start : i + 1])
                start = None
    return forms


def head_symbol(form: str) -> str:
    m = re.match(r"\(\s*([a-zA-Z_\-!?.$@^~&*+=<>/0-9]+)", form)
    return m.group(1) if m else ""


def defined_name(form: str) -> str:
    m = re.match(r"\(\s*(?:define-fun|declare-fun)\s+\|?([^\s|()]+)\|?", form)
    return m.group(1) if m else ""


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--smt2", required=True)
    ap.add_argument("--cert", required=True)
    ap.add_argument("--z3", default=str(Path(__file__).resolve().parent.parent / "reference/chc-solvers/bin/z3.exe"))
    ap.add_argument("--timeout-ms", type=int, default=120000)
    ap.add_argument("--keep", action="store_true", help="keep the generated check file")
    args = ap.parse_args()

    problem = Path(args.smt2).read_text(encoding="utf-8", errors="replace")
    cert = Path(args.cert).read_text(encoding="utf-8", errors="replace")

    defs = [f for f in top_level_forms(cert) if head_symbol(f) == "define-fun"]
    if not defs:
        print("cert-check: no define-fun forms found in certificate", file=sys.stderr)
        return 3
    defined = {defined_name(f) for f in defs}

    asserts: list[str] = []
    out: list[str] = []
    for form in top_level_forms(problem):
        h = head_symbol(form)
        if h == "set-logic":
            continue  # HORN logic would reject quantified (not F) checks; use ALL
        if h == "check-sat" or h == "exit" or h == "get-model":
            continue
        if h == "declare-fun" and defined_name(form) in defined:
            continue  # replaced by the certificate's define-fun
        if h == "assert":
            asserts.append(form)
            continue
        out.append(form)

    if not asserts:
        print("cert-check: no asserts found in problem", file=sys.stderr)
        return 3

    lines = ["(set-logic ALL)"] + out + defs
    for i, a in enumerate(asserts):
        inner = a.strip()
        assert inner.startswith("(")
        body = inner[len("(assert") : -1].strip()
        lines.append("(push 1)")
        lines.append(f"(assert (not {body}))")
        lines.append(f'(echo "clause-{i}")')
        lines.append("(check-sat)")
        lines.append("(pop 1)")

    with tempfile.NamedTemporaryFile(
        "w", suffix=".smt2", delete=False, encoding="utf-8"
    ) as fh:
        fh.write("\n".join(lines) + "\n")
        check_path = fh.name

    try:
        try:
            proc = subprocess.run(
                [args.z3, f"-T:{max(1, args.timeout_ms // 1000)}", check_path],
                capture_output=True,
                text=True,
                timeout=args.timeout_ms / 1000 + 30,
            )
        except subprocess.TimeoutExpired:
            # Keep the documented exit contract (0 valid / 2 failed / 3 unknown)
            # even when the external z3 blows through its own -T wall limit.
            print("cert-check: INCOMPLETE (external z3 wall timeout)")
            return 3
        outp = proc.stdout.splitlines()
        verdicts: dict[str, str] = {}
        current = None
        for line in outp:
            line = line.strip()
            if line.startswith("clause-"):
                current = line
            elif line in ("sat", "unsat", "unknown") and current:
                verdicts[current] = line
                current = None
        bad = {k: v for k, v in verdicts.items() if v != "unsat"}
        print(f"cert-check: {len(verdicts)}/{len(asserts)} clauses checked")
        if len(verdicts) < len(asserts):
            print("cert-check: INCOMPLETE (solver died or timed out mid-run)")
            print("stderr:", proc.stderr[-500:])
            return 3
        if not bad:
            print("cert-check: CERTIFICATE VALID — every clause verified UNSAT by external z3")
            return 0
        for k, v in bad.items():
            print(f"cert-check: {k} -> {v}  (clause NOT valid under the model)")
        print("cert-check: CERTIFICATE INVALID — false SAT" if any(v == "sat" for v in bad.values())
              else "cert-check: UNDECIDED (unknown verdicts)")
        return 2 if any(v == "sat" for v in bad.values()) else 3
    finally:
        if args.keep:
            print(f"check file: {check_path}")
        else:
            Path(check_path).unlink(missing_ok=True)


if __name__ == "__main__":
    sys.exit(main())

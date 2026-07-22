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
import json
import os
import re
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from _oom_guard import (  # noqa: E402
    ResourcePlan,
    plan_solver_resources,
    run_captured,
    warn_concurrent_build,
)

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
    ap.add_argument("--evidence-out", default="",
                    help="optional JSON checker evidence output")
    ap.add_argument("--memlimit-mb", type=int,
                    help="reuse an outer harness per-child memory budget")
    ap.add_argument("--nbcore", type=int,
                    help="reuse an outer harness per-child CPU budget")
    ap.add_argument("--headroom-mb", type=int,
                    help="reuse an outer harness headroom value")
    ap.add_argument("--resource-jobs", type=int, default=1,
                    help="outer plan's admitted job count")
    ap.add_argument("--resource-requested-jobs", type=int, default=1,
                    help="outer plan's requested job count")
    args = ap.parse_args()
    if args.timeout_ms <= 0:
        ap.error("--timeout-ms must be positive")

    warn_concurrent_build()
    explicit = (args.memlimit_mb, args.nbcore, args.headroom_mb)
    if any(value is not None for value in explicit):
        if any(value is None for value in explicit):
            ap.error("--memlimit-mb, --nbcore, and --headroom-mb must be supplied together")
        if args.memlimit_mb <= 0 or args.nbcore <= 0 or args.headroom_mb < 0:
            ap.error("explicit resource values must be positive (headroom may be zero)")
        if args.resource_jobs <= 0 or args.resource_requested_jobs <= 0:
            ap.error("explicit resource job counts must be positive")
        plan = ResourcePlan(
            args.resource_jobs,
            args.memlimit_mb,
            args.nbcore,
            args.headroom_mb,
        )
    else:
        plan = plan_solver_resources(1, label="chc_cert_check.py")
    resource_plan = {
        "requested_jobs": args.resource_requested_jobs if args.memlimit_mb else 1,
        "jobs": plan.jobs,
        "memlimit_mb_per_child": plan.memlimit_mb,
        "nbcore_per_child": plan.nbcore,
        "headroom_mb": plan.headroom_mb,
        "enforcement": "process-group rss_watchdog; MEMLIMIT/NBCORE environment",
    }
    print(f"cert-check: resource plan {json.dumps(resource_plan, sort_keys=True)}")

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
            proc = run_captured(
                [args.z3, f"-T:{max(1, args.timeout_ms // 1000)}", check_path],
                plan.memlimit_mb,
                args.timeout_ms / 1000 + 30,
                label="chc_cert_check.py[z3]",
                env=dict(os.environ, MEMLIMIT=str(plan.memlimit_mb),
                         NBCORE=str(plan.nbcore)),
            )
        except (OSError, RuntimeError) as error:
            print(f"cert-check: INCOMPLETE (could not run external z3: {error})")
            return 3
        if proc.timed_out or proc.memout or proc.output_truncated:
            # Keep the documented exit contract (0 valid / 2 failed / 3 unknown)
            # when the external z3 exceeds either enforced budget.
            reason = (
                "memory envelope"
                if proc.memout
                else "wall timeout"
                if proc.timed_out
                else "bounded output capture"
            )
            if args.evidence_out:
                Path(args.evidence_out).write_text(json.dumps({
                    "resource_plan": resource_plan,
                    "status": "incomplete",
                    "reason": reason,
                }, indent=2) + "\n")
            print(f"cert-check: INCOMPLETE (external z3 {reason})")
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
        status = ("valid" if len(verdicts) == len(asserts) and not bad else
                  "invalid" if any(v == "sat" for v in bad.values()) else
                  "incomplete")
        if args.evidence_out:
            Path(args.evidence_out).write_text(json.dumps({
                "resource_plan": resource_plan,
                "status": status,
                "clauses": len(asserts),
                "clauses_checked": len(verdicts),
                "solver_exit_code": proc.returncode,
            }, indent=2) + "\n")
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

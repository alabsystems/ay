#!/usr/bin/env python3
# ay-script: chc-disagreement-audit
# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0

"""Arbitrate every AY-vs-ground-truth disagreement in a harness run.

For each instance where AY answered sat/unsat but the corpus expected_verdict
disagrees (and no arbitrated correction exists yet):

  AY said sat  -> reproduce with --verbose (up to N attempts, concurrent to
                  recreate lane-race schedules), extract the ay-chc-cert
                  SAFE certificate, verify it with EXTERNAL z3 via
                  chc_cert_check.py. VALID => corpus label is wrong (emit a
                  correction candidate). INVALID => genuine AY false-SAT (bug).
  AY said unsat -> ask external z3 (default HORN/Spacer) for a second opinion
                  at a generous timeout. z3 unsat too => corpus label is wrong.
                  z3 sat => genuine AY false-UNSAT (bug). z3 unknown => leave
                  unresolved (never auto-correct on AY's word alone).

Output: audit report + gt_corrections candidates (NOT auto-applied — append to
the development design notes only with the evidence
recorded in GROUND_TRUTH_CORRECTIONS.md).

Usage:
  python scripts/chc_disagreement_audit.py --tag final900gt [--track BV]
      [--attempts 8] [--solve-timeout-ms 900000]
"""

from __future__ import annotations

import argparse
import json
import os
import signal
import subprocess
import sys
import tempfile
import threading
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from _oom_guard import plan_solver_resources, rss_watchdog, warn_concurrent_build  # noqa: E402

REPO = Path(__file__).resolve().parent.parent
Z3 = REPO / "reference/chc-solvers/bin/z3.exe"
CERT_CHECK = REPO / "scripts/chc_cert_check.py"
BENCH = REPO / "benchmarks/chc/chc-comp25-benchmarks"


def _popen_kwargs() -> dict:
    """Start each solver child in its own process group / session so timeouts,
    the early-exit kill sweep, and the rss_watchdog cover its whole tree."""
    if os.name == "nt":
        return {"creationflags": subprocess.CREATE_NEW_PROCESS_GROUP}
    return {"start_new_session": True}


def _kill_tree(proc: subprocess.Popen) -> None:
    """SIGKILL a child's whole process group; tolerate an already-dead child."""
    if os.name == "nt":
        subprocess.run(["taskkill", "/F", "/T", "/PID", str(proc.pid)],
                       capture_output=True)
        return
    try:
        os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
    except (ProcessLookupError, PermissionError):
        pass


def extract_cert(stdout: str) -> str | None:
    lines = stdout.splitlines()
    try:
        start = next(i for i, l in enumerate(lines) if "AY CHC Certificate" in l)
        end = next(i for i, l in enumerate(lines[start:], start) if "Proof obligations" in l)
    except StopIteration:
        return None
    return "\n".join(l for l in lines[start:end] if not l.strip().startswith(";;"))


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--tag", required=True)
    ap.add_argument("--track", default="BV")
    ap.add_argument("--year", default="2025")
    ap.add_argument("--attempts", type=int, default=8)
    ap.add_argument("--solve-timeout-ms", type=int, default=900000)
    ap.add_argument("--ay-bin", default=os.environ.get("AY_BIN", str(REPO / "target_lever/release/ay.exe")))
    args = ap.parse_args()

    # OOM guard (scripts/_oom_guard.py): cap the reproduction pool so
    # `jobs x per-child envelope` fits in RAM, hand each
    # ay child an explicit --memory budget (its standalone default is 85% of RAM
    # per process, sibling-blind), and backstop the external z3 (which has no
    # honored memory knob) with an rss_watchdog.
    warn_concurrent_build()
    plan = plan_solver_resources(min(8, args.attempts), label="chc_disagreement_audit.py")

    run_path = REPO / f"evals/results/chccomp-harness/{args.year}/{args.track}/{args.tag}/ay.jsonl"
    corrections_path = REPO / "the development design notes"
    corrections = json.loads(corrections_path.read_text()) if corrections_path.is_file() else {}

    disagreements = []
    for line in run_path.read_text(encoding="utf-8-sig").splitlines():
        if not line.strip():
            continue
        r = json.loads(line)
        rid = r["instance"].replace("\\", "/")
        if r.get("correct") is False and rid not in corrections:
            disagreements.append(r)

    print(f"[audit] {len(disagreements)} unarbitrated disagreement(s)")
    verdicts = []
    for r in disagreements:
        rid = r["instance"].replace("\\", "/")
        smt2 = BENCH / rid.replace(".yml", ".smt2")
        # instance rel_id is the yml path; recover the smt2 via the yml's input_files
        yml = BENCH / rid
        if yml.is_file():
            import re
            m = re.search(r"input_files:\s*'?([^'\n]+)'?", yml.read_text())
            if m:
                smt2 = (yml.parent / m.group(1).strip()).resolve()
        if not smt2.is_file():
            print(f"[audit] {rid}: SMT2 NOT FOUND ({smt2})")
            continue
        ay_says, gt = r["status"], r["verdict"]
        print(f"\n[audit] {rid}: AY={ay_says} yml={gt}")

        if ay_says == "sat":
            cert = None
            stop = threading.Event()
            procs = []
            procs_lock = threading.Lock()

            def attempt(i):
                if stop.is_set():
                    return None
                argv = [args.ay_bin, "--chc", "--competition", "--verbose",
                        "--timeout", str(args.solve_timeout_ms)]
                if plan.memlimit_mb:
                    argv += ["--memory", str(plan.memlimit_mb)]
                argv.append(str(smt2))
                proc = subprocess.Popen(
                    argv, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                    text=True, encoding="utf-8", errors="replace",
                    **_popen_kwargs())
                with procs_lock:
                    procs.append(proc)
                if stop.is_set():
                    # A certificate arrived while we were spawning: kill now
                    # rather than race the sweep and orphan a 15-minute solve.
                    _kill_tree(proc)
                try:
                    out, err = proc.communicate(timeout=args.solve_timeout_ms / 1000 + 60)
                except subprocess.TimeoutExpired:
                    _kill_tree(proc)
                    out, err = proc.communicate()
                return extract_cert((out or "") + "\n" + (err or ""))

            with ThreadPoolExecutor(max_workers=plan.jobs) as pool:
                futs = [pool.submit(attempt, i) for i in range(args.attempts)]
                for f in as_completed(futs):
                    c = f.result()
                    if c:
                        cert = c
                        # Genuine early exit: cancel pending futures, tell
                        # workers to stop, and kill the live solver process
                        # groups so the pool drains immediately (Future.cancel
                        # alone is a no-op on already-running tasks).
                        stop.set()
                        pool.shutdown(wait=False, cancel_futures=True)
                        with procs_lock:
                            for pr in procs:
                                _kill_tree(pr)
                        break
            if not cert:
                print(f"[audit] {rid}: could not reproduce a certificate — UNRESOLVED")
                verdicts.append((rid, "unresolved-no-cert"))
                continue
            with tempfile.NamedTemporaryFile("w", suffix=".smt2", delete=False, encoding="utf-8") as fh:
                fh.write(cert)
                cert_path = fh.name
            p = subprocess.run(
                [sys.executable, str(CERT_CHECK), "--smt2", str(smt2), "--cert", cert_path,
                 "--timeout-ms", "300000"],
                capture_output=True, text=True, encoding="utf-8", errors="replace")
            os.unlink(cert_path)
            print((p.stdout or "").strip())
            if p.returncode == 0:
                print(f"[audit] {rid}: CORPUS LABEL WRONG — correction candidate: sat")
                verdicts.append((rid, "correction:sat"))
            elif p.returncode == 2:
                print(f"[audit] {rid}: !! GENUINE AY FALSE-SAT — soundness bug")
                verdicts.append((rid, "AY-FALSE-SAT"))
            else:
                verdicts.append((rid, "unresolved-cert-unknown"))
        else:  # AY said unsat
            proc = subprocess.Popen(
                [str(Z3), "-T:600", str(smt2)],
                stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                encoding="utf-8", errors="replace", **_popen_kwargs())
            # z3 has no honored memory knob (-memory: silently overshoots; see
            # _oom_guard docstring), so the rss_watchdog is the only enforcement.
            guard = rss_watchdog(
                proc,
                plan.memlimit_mb,
                label="chc_disagreement_audit.py[z3]",
                grace_mb=0,
            )
            try:
                z3_out, _ = proc.communicate(timeout=660)
            except subprocess.TimeoutExpired:
                _kill_tree(proc)
                z3_out, _ = proc.communicate()
            finally:
                guard.stop()
            if guard.breached:
                z = "unknown"  # memout: leave unresolved, never guess
            else:
                z = next((l.strip() for l in (z3_out or "").splitlines()
                          if l.strip() in ("sat", "unsat")), "unknown")
            print(f"[audit] {rid}: external z3 says {z}")
            if z == "unsat":
                print(f"[audit] {rid}: CORPUS LABEL WRONG — correction candidate: unsat")
                verdicts.append((rid, "correction:unsat"))
            elif z == "sat":
                print(f"[audit] {rid}: !! GENUINE AY FALSE-UNSAT — soundness bug")
                verdicts.append((rid, "AY-FALSE-UNSAT"))
            else:
                verdicts.append((rid, "unresolved-z3-unknown"))

    print("\n=== AUDIT SUMMARY ===")
    for rid, v in verdicts:
        print(f"  {v:28s} {rid}")
    return 0


if __name__ == "__main__":
    sys.exit(main())

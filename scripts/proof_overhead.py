#!/usr/bin/env python3
# ay-script: proof-overhead-gate
# Author: Andrew Yates <andrewyates.name@gmail.com>
"""Proof Tap PHASE-4 overhead gate: dense-tap proof-on vs plain, median <=2x.

Runs each corpus instance in two (optionally three) modes and reports the
wall-clock overhead ratio distribution:
  - dense-tap : ay-pb pb solve --proof <tmp>   (the default payload)
  - plain     : ay-pb pb solve                                    (preprocessed)
  - plain-unpp: ay-pb pb solve, preprocessing disabled if a flag exists
                (proof mode runs UNpreprocessed per cdcl.rs:1628, so the tap's
                own contribution is dense-tap vs plain-unpreprocessed; the
                preprocessing gap is out of scope — reported separately).

SEQUENTIAL by design (jobs=1): clean, uncontended wall times. MEMLIMIT is set
per scripts/_oom_guard so a heavy proof-on run cannot overcommit RAM; a per-run
wall cap and safety RSS kill backstop the solver's own guard. Proof files go to
a scratch dir and are deleted immediately.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import signal
import statistics
import subprocess
import sys
import tempfile
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from _oom_guard import (  # noqa: E402
    copy_stream_limited,
    plan_solver_resources,
    run_captured,
    warn_concurrent_build,
)


NONCOMPARABLE = {"MEMOUT", "WALLTIMEOUT", "SPAWN_ERROR", "NO_S_LINE"}


def s_line(out: str) -> str:
    for ln in out.splitlines():
        if ln.startswith("s "):
            return ln[2:].strip()
    return "NO_S_LINE"


def s_line_file(stream) -> str:
    """Read only the status line from a seekable solver-output stream."""
    stream.flush()
    stream.seek(0)
    for line in stream:
        if line.startswith("s "):
            return line[2:].strip()
    return "NO_S_LINE"


def kill_process_group(proc: subprocess.Popen) -> None:
    """Kill an isolated solver tree; tolerate an already-reaped leader."""
    try:
        os.killpg(proc.pid, signal.SIGKILL)
    except (ProcessLookupError, PermissionError):
        pass


def executable_provenance(command: str) -> dict:
    candidate = Path(command)
    if candidate.exists():
        resolved = candidate.resolve()
    else:
        found = shutil.which(command)
        resolved = Path(found).resolve() if found else candidate
    try:
        stat = resolved.stat()
        digest = hashlib.sha256()
        with resolved.open("rb") as binary:
            for chunk in iter(lambda: binary.read(1024 * 1024), b""):
                digest.update(chunk)
        return {"path": str(resolved), "size": stat.st_size,
                "sha256": digest.hexdigest(),
                "runnable": resolved.is_file() and os.access(resolved, os.X_OK)}
    except OSError:
        return {"path": str(resolved), "size": None, "sha256": None,
                "runnable": False}


def run(bin_path: str, inst: Path, timeout_ms: int, wall_cap: float, memlimit_mb: int,
        nbcore: int, mode: str, proof_dir: Path | None):
    """mode: 'plain' (no proof, preprocessed) | 'dense' (dense tap proof-on,
    unpreprocessed) | 'legacy' (legacy synchronous proof-on, unpreprocessed)."""
    if memlimit_mb <= 0 or nbcore <= 0:
        raise ValueError("proof run requires positive memory and core budgets")
    env = dict(os.environ, MEMLIMIT=str(memlimit_mb), NBCORE=str(nbcore))
    args = [bin_path, "pb", "solve", "--timeout", str(timeout_ms)]
    proof_path = None
    if mode in ("dense", "legacy"):
        # dense = the tap (the default); legacy = the escape hatch
        # (B31: --proof-tap-legacy replaced AY_PB_PROOF_TAP=legacy.)
        if mode == "legacy":
            args.append("--proof-tap-legacy")
        proof_path = proof_dir / f"{inst.stem}.{mode}.{os.getpid()}.pbp"
        args += ["--proof", str(proof_path)]
    args.append(str(inst))
    try:
        try:
            captured = run_captured(
                args,
                memlimit_mb,
                wall_cap,
                label=f"proof_overhead.py[{mode}]",
                env=env,
            )
        except Exception:
            return "SPAWN_ERROR", 0.0
        if captured.memout:
            st = "MEMOUT"
        elif captured.timed_out:
            st = "WALLTIMEOUT"
        elif captured.cancelled or captured.output_truncated:
            st = "SPAWN_ERROR(CAPTURE)"
        else:
            st = s_line(captured.stdout)
            if st == "NO_S_LINE" and captured.returncode != 0:
                st = f"SPAWN_ERROR({captured.returncode})"
        secs = captured.wall_sec
    finally:
        if proof_path is not None:
            proof_path.unlink(missing_ok=True)
    return st, round(secs, 4)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--corpus", action="append", required=True)
    ap.add_argument("--bin", required=True)
    ap.add_argument("--timeout-ms", type=int, default=10000)
    ap.add_argument("--wall-grace-s", type=float, default=20.0)
    ap.add_argument("--limit", type=int)
    ap.add_argument("--out", required=True)
    args = ap.parse_args()
    if (args.timeout_ms <= 0 or args.wall_grace_s < 0 or
            (args.limit is not None and args.limit < 0)):
        print("proof-overhead: timeout must be positive; grace/limit must be "
              "nonnegative", file=sys.stderr)
        return 2

    # One solver at a time (clean wall times), but jobs=1 still needs an exact
    # envelope. The shared check refuses a corpus sweep during a cargo build.
    try:
        warn_concurrent_build()
        plan = plan_solver_resources(1, label="proof_overhead")
    except RuntimeError as exc:
        if "REFUSING" not in str(exc):
            print(f"proof-overhead: resource planning failed: {exc}",
                  file=sys.stderr)
        return 2
    if plan.memlimit_mb <= 0 or plan.nbcore <= 0:
        print("proof-overhead: resource planner returned no enforceable budget",
              file=sys.stderr)
        return 2
    if not hasattr(os, "killpg"):
        print("proof-overhead: exact process-group RSS enforcement requires POSIX", file=sys.stderr)
        return 2
    memlimit_mb = plan.memlimit_mb
    nbcore = plan.nbcore
    wall_cap = args.timeout_ms / 1000.0 + args.wall_grace_s

    paths: list[Path] = []
    for root in args.corpus:
        paths += sorted(Path(root).rglob("*.opb.xz"))
        paths += sorted(Path(root).rglob("*.opb"))
        paths += sorted(Path(root).rglob("*.wbo.xz"))
    if args.limit is not None:
        paths = paths[: args.limit]
    if not paths:
        print("no instances", file=sys.stderr)
        return 2
    binary = executable_provenance(args.bin)
    if not binary["runnable"]:
        print(f"proof-overhead: solver executable unavailable: {binary['path']}",
              file=sys.stderr)
        return 2
    args.bin = binary["path"]

    outdir = Path(args.out)
    outdir.mkdir(parents=True, exist_ok=True)
    proof_dir = outdir / "proofs"
    proof_dir.mkdir(exist_ok=True)
    tmp = outdir / "inst"
    tmp.mkdir(exist_ok=True)
    resource_envelope = {
        "schema": "ay.benchmark-resource-envelope/v1",
        "requested_jobs": 1,
        "jobs": plan.jobs,
        "memlimit_mb_per_child": memlimit_mb,
        "nbcore_per_child": nbcore,
        "headroom_mb": plan.headroom_mb,
        "memory_enforcement": "process-group rss_watchdog",
        "rss_grace_mb": 0,
        "solver_env": {"MEMLIMIT": str(memlimit_mb), "NBCORE": str(nbcore)},
        "timeout_enforcement": "process-group SIGKILL + reap",
        "timeout_ms": args.timeout_ms,
        "wall_cap_sec": wall_cap,
        "solver": binary,
    }
    (outdir / "resource-envelope.json").write_text(
        json.dumps(resource_envelope, indent=2) + "\n"
    )
    print(f"proof-overhead: {len(paths)} instances, MEMLIMIT={memlimit_mb}MiB, "
          f"NBCORE={nbcore}, T={args.timeout_ms/1000}s (sequential)", file=sys.stderr)

    def comparable(a_st, a_s, b_st, b_s):
        ok = (a_st not in NONCOMPARABLE and not a_st.startswith("SPAWN_ERROR(")
              and b_st not in NONCOMPARABLE and not b_st.startswith("SPAWN_ERROR(")
              and a_st == b_st)
        return round(a_s / b_s, 3) if (ok and b_s >= 0.05) else None

    rows = []
    r_vs_plain, r_vs_legacy = [], []
    verdict_mismatches = []
    for i, p in enumerate(paths):
        if p.suffix == ".xz":
            import lzma
            inst = tmp / p.name[:-3]
            with lzma.open(p, "rb") as src, inst.open("wb") as dst:
                copy_stream_limited(src, dst)
        else:
            inst = p
        try:
            plain_st, plain_s = run(args.bin, inst, args.timeout_ms, wall_cap, memlimit_mb, nbcore, "plain", None)
            legacy_st, legacy_s = run(args.bin, inst, args.timeout_ms, wall_cap, memlimit_mb, nbcore, "legacy", proof_dir)
            dense_st, dense_s = run(args.bin, inst, args.timeout_ms, wall_cap, memlimit_mb, nbcore, "dense", proof_dir)
        finally:
            if p.suffix == ".xz":
                inst.unlink(missing_ok=True)
        # dense-vs-plain = total proof overhead (INCLUDES the preprocessing gap).
        # dense-vs-legacy = the TAP's own contribution (both proof-on/unpreprocessed).
        rp = comparable(dense_st, dense_s, plain_st, plain_s)
        rl = comparable(dense_st, dense_s, legacy_st, legacy_s)
        statuses = (plain_st, legacy_st, dense_st)
        comparable_statuses = [
            status for status in statuses
            if status not in NONCOMPARABLE
            and not status.startswith("SPAWN_ERROR(")
        ]
        if len(set(comparable_statuses)) > 1:
            verdict_mismatches.append((p.name, *statuses))
        if rp is not None:
            r_vs_plain.append(rp)
        if rl is not None:
            r_vs_legacy.append(rl)
        rows.append((p.name, plain_st, plain_s, legacy_st, legacy_s, dense_st, dense_s, rp, rl))
        if (i + 1) % 25 == 0:
            print(f"  {i+1}/{len(paths)}", file=sys.stderr)

    tsv = outdir / "overhead.tsv"
    with tsv.open("w") as fh:
        fh.write("instance\tplain_s\tplain_sec\tlegacy_s\tlegacy_sec\tdense_s\tdense_sec\t"
                 "dense_vs_plain\tdense_vs_legacy\n")
        for row in rows:
            fh.write("\t".join(str(x) for x in row) + "\n")

    def summ(name, ratios, note):
        print(f"\n=== {name} (n={len(ratios)} comparable) ===")
        if not ratios:
            print("  no comparable instances")
            return None
        ratios.sort()
        med = statistics.median(ratios)
        p90 = ratios[min(len(ratios) - 1, int(0.9 * len(ratios)))]
        print(f"  median {med:.3f}x  p90 {p90:.3f}x  max {max(ratios):.3f}x  min {min(ratios):.3f}x")
        print(f"  {note}")
        return med

    med_legacy = summ("TAP OVERHEAD: dense-tap vs legacy proof (both unpreprocessed — the CLEAN tap number)",
                      r_vs_legacy, f"GATE target <= 2.0x -> {'PASS' if r_vs_legacy and statistics.median(r_vs_legacy) <= 2.0 else 'FAIL/NA'}")
    med_plain = summ("TOTAL: dense-tap proof-on vs plain (INCLUDES preprocessing confound)",
                     r_vs_plain, "> 2x here may be the preprocessing gap, not the tap")
    worst = sorted([r for r in rows if r[8] is not None], key=lambda r: -r[8])[:8]
    print("\nworst dense-vs-legacy instances (ratio / legacy_sec / dense_sec):")
    for row in worst:
        print(f"  {row[8]:.2f}x  {row[4]:.3f}s -> {row[6]:.3f}s  {row[0]}")
    print(f"\nPHASE-4 PERF GATE: {'PASS' if med_legacy is not None and med_legacy <= 2.0 else 'REVIEW'} "
          f"(clean tap median {med_legacy if med_legacy is not None else 'n/a'}x)")
    if verdict_mismatches:
        print("\nVERDICT MISMATCHES (proof modes must be semantically identical):")
        for name, plain, legacy, dense in verdict_mismatches:
            print(f"  {name}: plain={plain} legacy={legacy} dense={dense}")
    print(f"wrote {tsv}")
    if verdict_mismatches:
        return 3
    return 0 if med_legacy is not None and med_legacy <= 2.0 else 1


if __name__ == "__main__":
    sys.exit(main())

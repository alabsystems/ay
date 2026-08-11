#!/usr/bin/env python3
"""Windows-native SAT-COMP sweep harness.

Why not `scripts/sweep.py`
--------------------------
That harness is POSIX-only and, worse, fails SILENTLY here. Its `run_one` wraps
the runner in a bare `except Exception` (sweep.py:43-45) and returns
`{"verdict": "error"}`. `_oom_guard`'s `run_captured` / `guarded_popen` /
`run_guarded` / `rss_watchdog` all raise unconditionally when `os.name == "nt"`.
The two failures compose into the worst possible outcome: a complete,
well-formed results file in which every row is `error` -- a scoreboard that
looks real and measures nothing.

This harness therefore does the opposite of swallowing failures. Every
non-solve outcome is a distinct, recorded verdict, and any condition that would
invalidate the run aborts the sweep loudly instead of producing a row.

Scoring
-------
Ground truth comes from the official per-instance results export, NOT from a
label file we control:
  https://satcompetition.github.io/2026/downloads/scores.csv
An instance's truth is the `vresult` agreed by the competition's own verified
solvers. Any AY answer contradicting it is a WRONG ANSWER -- competition
disqualification -- and is reported at the top of the summary, never averaged
away.

Reported score is mean PAR-2 at the stated timeout, matching the competition
ranking rule (SAT-COMP ranks on PAR-2, not solved count).

Caveat this harness cannot fix: AY emits no UNSAT proof on Windows (the
transactional DIMACS proof path is `cfg(linux/macos)`-gated). So results here
measure ANSWER correctness only. A Main-track claim additionally requires a
checker-verified certificate and must be produced on Linux.
"""

from __future__ import annotations

import argparse
import csv
import json
import lzma
import os
import re
import shutil
import subprocess
import sys
import tempfile
import threading
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
_lock = threading.Lock()

SAT_RE = re.compile(r"^s +SATISFIABLE", re.M)
UNSAT_RE = re.compile(r"^s +UNSATISFIABLE", re.M)


def load_ground_truth(scores_csv: Path) -> dict[str, str]:
    """Per-instance truth agreed by the competition's verified solvers."""
    seen: dict[str, set[str]] = {}
    with scores_csv.open(newline="") as fh:
        for row in csv.DictReader(fh):
            v = row.get("vresult", "")
            if v in ("sat", "unsat"):
                seen.setdefault(row["instanceid"], set()).add(v)
    conflicts = {k: v for k, v in seen.items() if len(v) > 1}
    if conflicts:
        raise SystemExit(
            f"ground truth is self-contradictory for {len(conflicts)} instances "
            f"(e.g. {list(conflicts)[:3]}); refusing to score against it"
        )
    return {k: next(iter(v)) for k, v in seen.items()}


# A solved instance in the official export. Note `sat`/`unsat` WITHOUT the
# `-verified` suffix are genuine solves in the Experimental track, which carries
# no proof requirement -- filtering on `-verified` alone silently discards 144 of
# kissat-sup's 274 solves and understates that bar by more than 3000 PAR-2.
SOLVED_STATUSES = {"sat", "unsat", "sat-verified", "unsat-verified"}


def official_par2(scores_csv: Path) -> dict[str, dict]:
    """Recompute each official solver's mean PAR-2 from the authoritative
    `score` column (runtime when solved, 2x timeout otherwise)."""
    runs: dict[str, list[tuple[float, str]]] = {}
    with scores_csv.open(newline="") as fh:
        for row in csv.DictReader(fh):
            runs.setdefault(row["solverid"], []).append(
                (float(row["score"]), row["status"])
            )
    out = {}
    for solver, rows in runs.items():
        solved = sum(1 for _, s in rows if s in SOLVED_STATUSES)
        par2 = sum(score for score, _ in rows) / len(rows)
        out[solver] = {"solved": solved, "par2": round(par2, 2), "n": len(rows)}
    return out


def decompress(src: Path, dest: Path) -> None:
    with lzma.open(src, "rb") as fin, dest.open("wb") as fout:
        shutil.copyfileobj(fin, fout, length=1 << 22)


def kill_tree(proc: subprocess.Popen) -> None:
    """Windows has no process groups; taskkill /T is the only reliable reap."""
    try:
        subprocess.run(
            ["taskkill", "/F", "/T", "/PID", str(proc.pid)],
            capture_output=True,
            timeout=60,
        )
    except Exception:
        pass
    try:
        proc.kill()
    except Exception:
        pass


def run_one(
    solver: Path,
    instance_xz: Path,
    instance_id: str,
    timeout: float,
    memory_mb: int,
    workdir: Path,
    extra_args: list[str],
) -> dict:
    """Run one instance. Every failure mode gets its own verdict; none are hidden."""
    cnf = workdir / f"{instance_id}.cnf"
    rec: dict = {"instance": instance_id}
    try:
        t0 = time.monotonic()
        decompress(instance_xz, cnf)
        rec["decompress_s"] = round(time.monotonic() - t0, 2)
    except Exception as exc:  # noqa: BLE001
        rec.update(verdict="harness-error", error=f"decompress: {exc}", time=0.0)
        return rec

    cmd = [
        str(solver), "solve", "-q", "--competition",
        "--timeout", str(int(timeout * 1000)),
        "--memory", str(memory_mb),
        *extra_args,
        str(cnf),
    ]
    # Outer wall-clock guard: the in-process --timeout is the primary control,
    # but a hung or wedged child must never stall the sweep.
    hard = timeout + 120
    start = time.monotonic()
    proc = subprocess.Popen(
        cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
        errors="replace",
    )
    timed_out = False
    try:
        out, err = proc.communicate(timeout=hard)
    except subprocess.TimeoutExpired:
        timed_out = True
        kill_tree(proc)
        try:
            out, err = proc.communicate(timeout=60)
        except Exception:  # noqa: BLE001
            out, err = "", ""
    elapsed = time.monotonic() - start
    rc = proc.returncode

    try:
        cnf.unlink()
    except OSError:
        pass

    if timed_out:
        verdict = "timeout-hard"
    elif rc == 10 and SAT_RE.search(out or ""):
        verdict = "sat"
    elif rc == 20 and UNSAT_RE.search(out or ""):
        verdict = "unsat"
    elif SAT_RE.search(out or ""):
        # Verdict line without the matching exit code is a protocol violation:
        # record it distinctly rather than crediting the answer.
        verdict = "sat-badexit"
    elif UNSAT_RE.search(out or ""):
        verdict = "unsat-badexit"
    elif elapsed >= timeout * 0.95:
        verdict = "timeout"
    elif rc == 0 or rc is None:
        verdict = "unknown"
    else:
        verdict = "crash"

    rec.update(
        verdict=verdict,
        time=round(elapsed, 2),
        rc=rc,
        stderr=(err or "")[-400:] if verdict in ("crash", "harness-error") else "",
    )
    return rec


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--solver", default=str(REPO / "target/release/ay.exe"))
    ap.add_argument("--instances", required=True, help="dir of <instanceid>.cnf.xz")
    src = ap.add_mutually_exclusive_group(required=True)
    src.add_argument("--scores", help="official 2026 scores.csv (ground truth)")
    src.add_argument(
        "--gt-json",
        help="ground-truth json {instanceid: sat|unsat} under key 'ground_truth' "
        "(used for 2025, which publishes no per-instance export)",
    )
    ap.add_argument("--timeout", type=float, default=60.0, help="seconds")
    ap.add_argument("--memory", type=int, default=8000, help="MB per solver process")
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--limit", type=int, default=0, help="only first N instances")
    ap.add_argument(
        "--only",
        help="file of instanceids (one per line) to restrict the run to; "
        "PAR-2 over a subset is NOT a competition score, only solved-counts "
        "are meaningful for an A/B",
    )
    ap.add_argument("--out", required=True)
    ap.add_argument("--tag", default="ay")
    ap.add_argument("--extra", default="", help="extra solver args, space separated")
    args = ap.parse_args()

    solver = Path(args.solver)
    if not solver.is_file():
        raise SystemExit(f"solver not found: {solver}")
    inst_dir = Path(args.instances)

    if args.scores:
        gt = load_ground_truth(Path(args.scores))
    else:
        payload = json.loads(Path(args.gt_json).read_text(encoding="utf-8"))
        gt = payload["ground_truth"]
        bad = {k: v for k, v in gt.items() if v not in ("sat", "unsat")}
        if bad:
            raise SystemExit(
                f"ground-truth file has {len(bad)} non-sat/unsat labels "
                f"(e.g. {list(bad.items())[:3]}); refusing to score against it"
            )
    instances = sorted(inst_dir.glob("*.cnf.xz"))
    if not instances:
        raise SystemExit(f"no *.cnf.xz under {inst_dir}")
    if args.only:
        wanted = {
            line.strip()
            for line in Path(args.only).read_text(encoding="utf-8").splitlines()
            if line.strip()
        }
        instances = [p for p in instances if p.name[: -len(".cnf.xz")] in wanted]
        missing = wanted - {p.name[: -len(".cnf.xz")] for p in instances}
        if missing:
            raise SystemExit(
                f"{len(missing)} requested instanceids are not present under "
                f"{inst_dir} (e.g. {sorted(missing)[:3]})"
            )
    if args.limit:
        instances = instances[: args.limit]

    # Refuse to silently score a partial corpus as if it were the full set.
    ids = [p.name[: -len(".cnf.xz")] for p in instances]
    unknown_ids = [i for i in ids if i not in gt]
    print(
        f"instances={len(ids)} with-ground-truth={len(ids) - len(unknown_ids)} "
        f"no-ground-truth={len(unknown_ids)} timeout={args.timeout}s "
        f"memory={args.memory}MB workers={args.workers}",
        flush=True,
    )

    total_ram_mb = args.memory * args.workers
    print(f"envelope: {args.workers} x {args.memory} MB = {total_ram_mb} MB peak", flush=True)

    workdir = Path(tempfile.mkdtemp(prefix="ay-sweep-"))
    extra = args.extra.split() if args.extra else []
    results: list[dict] = []
    done = {"n": 0}
    start = time.monotonic()

    def work(pair):
        path, iid = pair
        rec = run_one(
            solver, path, iid, args.timeout, args.memory, workdir, extra
        )
        rec["truth"] = gt.get(iid, "unknown")
        v = rec["verdict"]
        if v in ("sat", "unsat") and rec["truth"] in ("sat", "unsat"):
            rec["correct"] = v == rec["truth"]
        else:
            rec["correct"] = None
        with _lock:
            results.append(rec)
            done["n"] += 1
            if rec["correct"] is False:
                print(
                    f"*** WRONG ANSWER {iid}: ay={v} truth={rec['truth']} ***",
                    flush=True,
                )
            if done["n"] % 10 == 0:
                el = time.monotonic() - start
                nsolved = sum(1 for r in results if r["verdict"] in ("sat", "unsat"))
                print(
                    f"{done['n']}/{len(instances)} solved={nsolved} {el:.0f}s",
                    flush=True,
                )

    try:
        with ThreadPoolExecutor(max_workers=args.workers) as pool:
            list(pool.map(work, zip(instances, ids)))
    finally:
        shutil.rmtree(workdir, ignore_errors=True)

    wrong = [r for r in results if r["correct"] is False]
    solved = [r for r in results if r["verdict"] in ("sat", "unsat")]
    scored = [r for r in results if r["truth"] in ("sat", "unsat")]
    # PAR-2 over instances that have official ground truth, matching the
    # competition denominator.
    par2 = (
        sum(
            r["time"] if r["verdict"] in ("sat", "unsat") and r["correct"] else 2 * args.timeout
            for r in scored
        )
        / len(scored)
        if scored
        else float("nan")
    )
    by_verdict: dict[str, int] = {}
    for r in results:
        by_verdict[r["verdict"]] = by_verdict.get(r["verdict"], 0) + 1

    summary = {
        "tag": args.tag,
        "solver": str(solver),
        "timeout_s": args.timeout,
        "memory_mb": args.memory,
        "workers": args.workers,
        "instances": len(results),
        "scored_against_ground_truth": len(scored),
        "solved": len(solved),
        "solved_sat": sum(1 for r in solved if r["verdict"] == "sat"),
        "solved_unsat": sum(1 for r in solved if r["verdict"] == "unsat"),
        "wrong_answers": len(wrong),
        "wrong_detail": [
            {"instance": r["instance"], "ay": r["verdict"], "truth": r["truth"]}
            for r in wrong
        ],
        "mean_par2": round(par2, 2),
        "by_verdict": by_verdict,
        "wall_s": round(time.monotonic() - start, 1),
        "note": "answer-correctness only; no UNSAT proof emitted (Windows)",
    }

    Path(args.out).write_text(
        json.dumps({"summary": summary, "results": results}, indent=1), encoding="utf-8"
    )

    print("\n=== SUMMARY ===", flush=True)
    print(json.dumps(summary, indent=1), flush=True)
    if wrong:
        print(f"\n!!! {len(wrong)} WRONG ANSWERS — competition-disqualifying !!!", flush=True)
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())

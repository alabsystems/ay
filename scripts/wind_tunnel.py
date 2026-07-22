#!/usr/bin/env python3
# ay-script: wind-tunnel
# Author: Andrew Yates <andrewyates.name@gmail.com>
"""The Wind Tunnel: full-corpus PAR-2 evaluation with an independent output checker.

Campaign M0 cornerstone (the development design notes):
every engine change is measured here, in competition currency, before it ships.

- Sweeps a corpus of `.opb.xz` / `.wbo.xz` instances (PB24/PB25 layouts) with a
  solver binary; optional baseline binary for A/B.
- Independently validates EVERY SAT/OPT answer: v-line completeness, hard-row
  feasibility, final `o` == exact recomputed objective (WBO: true soft cost,
  strictly below the `soft:` top). Wrong answers fail the run (exit 3).
- Scores PAR-2 per track (wall-clock proxy for the portal's CPU clock) plus
  solved/answer counts and verdict-transition tables in A/B mode.
- Emits TSV (per-instance), JSON (machine), and Markdown (human) reports.

Typical runs:
  nightly:  wind_tunnel.py --corpus <pb24-dir> --bin target/release/ay-pb \
                --timeout-ms 15000 --jobs 6 --out results/wind-tunnel/nightly
  A/B gate: add --baseline-bin /path/to/old-ay-pb
  weekly:   --timeout-ms 300000; pre-freeze: --timeout-ms 1800000 --jobs 1

Scheduling (macOS example):
  crontab: 0 2 * * * cd ~/ay && python3 scripts/wind_tunnel.py ... >> wt.log
"""

from __future__ import annotations

import argparse
import concurrent.futures as cf
import hashlib
import json
import lzma
import os
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from _oom_guard import (  # noqa: E402
    copy_stream_limited,
    plan_solver_resources,
    run_captured,
    warn_concurrent_build,
)

TERM_RE = re.compile(r"([+-]?\d+)((?:\s+~?x\d+)+)")

TRACK_PATTERNS = [
    ("PARTIAL-LIN", "PARTIAL-LIN"),
    ("SOFT-LIN", "SOFT-LIN"),
    ("OPT-LIN", "OPT-LIN"),
    ("DEC-LIN", "DEC-SMALLINT"),  # PB24 layout variants fall through below
    ("OPT-NLC", "OPT-NLC"),
    ("DEC-NLC", "DEC-NLC"),
]

ANSWERS = {"SATISFIABLE", "OPTIMUM FOUND", "UNSATISFIABLE"}
CHECK_LOCK = threading.Lock()
MAX_CHECK_INPUT_BYTES = 16 * 1024 * 1024


def classify_track(path: str) -> str:
    upper = path.upper()
    for track, pat in TRACK_PATTERNS:
        if pat in upper:
            return track
    if "/WBO/" in upper:
        return "WBO-OTHER"
    if "DEC" in upper:
        return "DEC-LIN"
    return "OPT-LIN" if "OPT" in upper else "UNKNOWN-TRACK"


def parse_terms(text: str):
    """Parse one PB expression and reject any unrecognised residue."""
    terms = []
    cursor = 0
    for match in TERM_RE.finditer(text):
        if text[cursor:match.start()].strip():
            raise ValueError(f"malformed PB term near {text[cursor:]!r}")
        terms.append((int(match.group(1)), match.group(2).split()))
        cursor = match.end()
    if text[cursor:].strip():
        raise ValueError(f"malformed PB term near {text[cursor:]!r}")
    return terms


def parse_pb(text: str, is_wbo: bool):
    top, obj, hard, soft = None, None, [], []
    for line in text.splitlines():
        t = line.strip()
        if not t or t.startswith("*"):
            continue
        if is_wbo and t.startswith("soft:"):
            body = t[5:].strip().rstrip(";").strip()
            if body and not re.fullmatch(r"\d+", body):
                raise ValueError(f"malformed WBO top cost {body!r}")
            top = int(body) if body else None
            continue
        cost = None
        if is_wbo and t.startswith("["):
            m = re.match(r"\[\s*(\d+)\s*\]\s*(.*)$", t)
            if not m:
                raise ValueError(f"malformed WBO weight in {t!r}")
            cost = int(m.group(1))
            t = m.group(2)
        if t.startswith("min:"):
            obj = parse_terms(t[4:].rstrip(";"))
            continue
        t = t.rstrip(";").strip()
        if ">=" in t:
            rel = ">="
        elif "=" in t:
            rel = "="
        else:
            raise ValueError(f"constraint has no supported relation: {t!r}")
        lhs, rhs = t.rsplit(rel, 1)
        terms = parse_terms(lhs)
        con = (terms, rel, int(rhs.strip()))
        if cost is not None:
            soft.append((cost, con))
        else:
            hard.append(con)
    return top, obj, hard, soft


def lit_val(lit: str, assign) -> bool:
    neg = lit.startswith("~")
    val = assign.get(lit.lstrip("~"), False)
    return (not val) if neg else val


def con_val(con, assign) -> bool:
    terms, rel, rhs = con
    total = sum(c for c, lits in terms if all(lit_val(l, assign) for l in lits))
    return total >= rhs if rel == ">=" else total == rhs


def check_answer(text: str, is_wbo: bool, status: str, oval, vtoks) -> str:
    """Independent verdict on a SAT/OPT answer. Returns 'OK' or 'BAD(...)'."""
    top, obj, hard, soft = parse_pb(text, is_wbo)
    assign = {}
    seen = {}
    for tok in vtoks:
        if not re.fullmatch(r"-?x\d+", tok):
            return f"BAD(model-token={tok!r})"
        neg = tok.startswith("-")
        variable = tok.lstrip("-")
        value = not neg
        if variable in seen and seen[variable] != value:
            return f"BAD(conflicting-model-token={variable})"
        seen[variable] = value
        assign[variable] = value
    header = re.search(r"#variable=\s*(\d+)", text)
    if header:
        expected = {f"x{i}" for i in range(1, int(header.group(1)) + 1)}
    else:
        expected = {
            literal.lstrip("~")
            for terms, *_rest in hard + [constraint for _cost, constraint in soft]
            for _coefficient, literals in terms
            for literal in literals
        }
        if obj:
            expected.update(literal.lstrip("~")
                            for _coefficient, literals in obj
                            for literal in literals)
    missing = expected - set(assign)
    extra = set(assign) - expected
    if missing or extra:
        return f"BAD(model-missing={len(missing)},extra={len(extra)})"
    bad_hard = sum(1 for c in hard if not con_val(c, assign))
    if is_wbo:
        cost = sum(c for c, con in soft if not con_val(con, assign))
        ok = (
            bad_hard == 0
            and oval is not None
            and oval == cost
            and (top is None or cost < top)
        )
        return "OK" if ok else f"BAD(h={bad_hard},cost={cost},o={oval},top={top})"
    objv = (
        sum(c for c, lits in obj if all(lit_val(l, assign) for l in lits))
        if obj
        else None
    )
    needs_objective = obj is not None
    ok = (bad_hard == 0
          and (not needs_objective or oval is not None)
          and (oval is None or objv is None or oval == objv))
    return "OK" if ok else f"BAD(h={bad_hard},o={oval},real={objv})"


def resource_env(env_extra: dict, memlimit_mb: int, nbcore: int) -> dict:
    """Merge arbitrary child settings under the authoritative resource plan."""
    merged = dict(env_extra)
    if memlimit_mb:
        merged["MEMLIMIT"] = str(memlimit_mb)
    if nbcore:
        merged["NBCORE"] = str(nbcore)
    return merged


def kill_process_group(proc: subprocess.Popen) -> None:
    """Kill an isolated solver tree; tolerate an already-dead group."""
    try:
        os.killpg(proc.pid, signal.SIGKILL)
    except (ProcessLookupError, PermissionError):
        pass


def executable_provenance(command: str) -> dict:
    """Resolve and hash a solver before a sweep starts."""
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
        return {
            "path": str(resolved),
            "size": stat.st_size,
            "sha256": digest.hexdigest(),
            "runnable": resolved.is_file() and os.access(resolved, os.X_OK),
        }
    except OSError:
        return {"path": str(resolved), "size": None, "sha256": None,
                "runnable": False}


def parse_solver_output(output):
    """Extract only answer-bearing output from bounded solver output."""
    status, oval, vtoks = None, None, []
    for line in output.splitlines():
        if line.startswith("s "):
            status = line[2:].strip()
        elif line.startswith("o "):
            try:
                oval = int(line[2:])
            except ValueError:
                pass
        elif line.startswith("v "):
            # The independent checker necessarily retains the assignment, but
            # arbitrary progress/log output remains on disk rather than in RAM.
            vtoks.extend(line[2:].split())
    return status, oval, vtoks


def run_instance(binary: str, path: Path, timeout_ms: int, wall_cap: float,
                 env_extra: dict, workdir: Path):
    is_wbo = path.name.endswith(".wbo.xz")
    tmp = workdir / (path.name[:-3] + f".{os.getpid()}.{time.monotonic_ns()}")
    env = dict(os.environ, **env_extra)
    # The MEMLIMIT env is only enforced by ay-pb-lineage binaries; a main-`ay`
    # --bin (its `pb` subcommand sets NO memory limit at all) would run
    # unbounded, so the rss_watchdog backstop enforces the same envelope
    # externally (status MEMOUT on breach).
    try:
        memlimit_mb = int(env["MEMLIMIT"])
        nbcore = int(env["NBCORE"])
    except (KeyError, ValueError):
        raise ValueError("wind tunnel requires authoritative MEMLIMIT/NBCORE")
    if memlimit_mb <= 0 or nbcore <= 0:
        raise ValueError("wind tunnel requires positive resource budgets")
    try:
        with lzma.open(path, "rb") as src, tmp.open("wb") as dst:
            copy_stream_limited(src, dst)
        try:
            captured = run_captured(
                [binary, "pb", "solve", "--timeout", str(timeout_ms), str(tmp)],
                memlimit_mb,
                wall_cap,
                label="wind_tunnel.py",
                env=env,
            )
        except Exception as exc:
            return {"status": "SPAWN_ERROR", "o": None, "check": "-",
                    "seconds": 0.0, "exit_code": None, "memout": False,
                    "timed_out": False, "error": str(exc)[:200]}
        seconds = captured.wall_sec
        exit_code = captured.returncode
        if captured.memout:
            return {"status": "MEMOUT", "o": None, "check": "-",
                    "seconds": round(seconds, 3), "exit_code": exit_code,
                    "memout": True, "timed_out": False}
        if captured.timed_out:
            return {"status": "WALLTIMEOUT", "o": None, "check": "-",
                    "seconds": round(seconds, 3), "exit_code": exit_code,
                    "memout": False, "timed_out": True}
        if captured.cancelled or captured.output_truncated:
            return {"status": "CAPTURE_ERROR", "o": None, "check": "-",
                    "seconds": round(seconds, 3), "exit_code": exit_code,
                    "memout": False, "timed_out": False,
                    "error": "solver output truncated or capture cancelled"}

        # Output parsing retains a complete model. Serialize checks so their
        # parent-side structures cannot multiply, and reject large instances
        # before allocating a full parser representation.
        with CHECK_LOCK:
            status, oval, vtoks = parse_solver_output(captured.stdout)
            if status is None:
                status = "NOANSWER" if exit_code == 0 else "CRASH"
            chk = "-"
            if status in ("SATISFIABLE", "OPTIMUM FOUND"):
                if tmp.stat().st_size > MAX_CHECK_INPUT_BYTES:
                    chk = f"BAD(input-too-large>{MAX_CHECK_INPUT_BYTES})"
                else:
                    text = tmp.read_text(errors="replace")
                    chk = check_answer(text, is_wbo, status, oval, vtoks)
        return {"status": status, "o": oval, "check": chk,
                "seconds": round(seconds, 3), "exit_code": exit_code,
                "memout": False, "timed_out": False}
    finally:
        tmp.unlink(missing_ok=True)


def par2(row: dict, timeout_s: float, complete_only: bool) -> float:
    """PAR-2 contribution. complete_only counts only definitive answers."""
    definitive = {"OPTIMUM FOUND", "UNSATISFIABLE"} if complete_only else ANSWERS
    if row["status"] in definitive and not row["check"].startswith("BAD"):
        return min(row["seconds"], timeout_s)
    return 2.0 * timeout_s


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--corpus", action="append", required=True,
                    help="corpus root(s) containing .opb.xz/.wbo.xz (repeatable)")
    ap.add_argument("--bin", required=True, help="candidate solver binary")
    ap.add_argument("--baseline-bin", help="optional baseline binary for A/B")
    ap.add_argument("--timeout-ms", type=int, default=15000)
    ap.add_argument("--jobs", type=int, default=6)
    ap.add_argument("--wall-grace-s", type=float, default=25.0,
                    help="wall cap = timeout + this grace")
    ap.add_argument("--env", action="append", default=[],
                    help="KEY=VALUE for the solver env (repeatable)")
    ap.add_argument("--out", required=True, help="output directory")
    ap.add_argument("--limit", type=int, help="cap instance count (smoke runs)")
    ap.add_argument("--mem-headroom-mb", type=int, default=None,
                    help="RAM headroom (MiB) the resource planner reserves "
                         "(default: max(16 GiB, RAM/3); lower it on rented "
                         "big boxes)")
    args = ap.parse_args()

    if (args.jobs <= 0 or args.timeout_ms <= 0 or args.wall_grace_s < 0 or
            (args.limit is not None and args.limit < 0) or
            (args.mem_headroom_mb is not None and args.mem_headroom_mb < 0)):
        print("wind tunnel: jobs/timeout must be positive and resource "
              "headroom/grace must be nonnegative", file=sys.stderr)
        return 2

    env_user = {}
    for item in args.env:
        if "=" not in item or not item.split("=", 1)[0]:
            print(f"wind tunnel: invalid --env value {item!r}; expected KEY=VALUE",
                  file=sys.stderr)
            return 2
        key, value = item.split("=", 1)
        if key in {"MEMLIMIT", "NBCORE"}:
            print(f"wind tunnel: --env {key}=... cannot override the "
                  "authoritative resource plan", file=sys.stderr)
            return 2
        env_user[key] = value

    # OOM guard (scripts/_oom_guard.py): a full-corpus sweep concurrent with a
    # cargo LTO build caused the 2026-06-19 and 2026-07-11 watchdog kernel
    # panics. Refuse that combination, cap --jobs to a safe RAM budget, and
    # give every child an enforced MEMLIMIT/NBCORE. There is deliberately no
    # bypass: sweep + LTO has caused kernel watchdog panics.
    try:
        warn_concurrent_build()
        requested_jobs = args.jobs
        plan = plan_solver_resources(
            requested_jobs,
            headroom_mb=args.mem_headroom_mb,
            label="wind_tunnel.py",
        )
    except RuntimeError as exc:
        if "REFUSING" not in str(exc):
            print(f"wind tunnel: resource planning failed: {exc}", file=sys.stderr)
        return 2
    if plan.memlimit_mb <= 0 or plan.nbcore <= 0:
        print("wind tunnel: resource planner returned an unenforceable envelope",
              file=sys.stderr)
        return 2
    if not hasattr(os, "killpg"):
        print("wind tunnel: exact process-group RSS enforcement requires POSIX",
              file=sys.stderr)
        return 2
    args.jobs = plan.jobs
    env_extra = resource_env(env_user, plan.memlimit_mb, plan.nbcore)
    resource_plan = {
        "schema": "ay.benchmark-resource-envelope/v1",
        "requested_jobs": requested_jobs,
        "jobs": args.jobs,
        "memlimit_mb": plan.memlimit_mb,
        "memlimit_mb_per_child": plan.memlimit_mb,
        "nbcore": plan.nbcore,
        "nbcore_per_child": plan.nbcore,
        "headroom_mb": plan.headroom_mb,
        "memory_enforcement": "process-group rss_watchdog",
        "rss_grace_mb": 0,
        "solver_env": {"MEMLIMIT": str(plan.memlimit_mb),
                       "NBCORE": str(plan.nbcore)},
        "timeout_ms": args.timeout_ms,
        "wall_cap_sec": args.timeout_ms / 1000.0 + args.wall_grace_s,
        "timeout_enforcement": "process-group SIGKILL + reap",
        "capture": "temporary files (bounded parent RAM)",
        "checker_jobs": 1,
    }
    plan_line = (f"resource plan: jobs={resource_plan['jobs']}, "
                 f"MEMLIMIT={resource_plan['memlimit_mb']} MiB/job, "
                 f"NBCORE={resource_plan['nbcore']}, "
                 f"headroom={resource_plan['headroom_mb']} MiB")
    print(f"wind tunnel: {plan_line}", file=sys.stderr)
    timeout_s = args.timeout_ms / 1000.0
    wall_cap = timeout_s + args.wall_grace_s
    outdir = Path(args.out)
    outdir.mkdir(parents=True, exist_ok=True)
    workdir = outdir / "tmp"
    workdir.mkdir(exist_ok=True)

    paths: list[Path] = []
    for root in args.corpus:
        paths += sorted(Path(root).rglob("*.opb.xz"))
        paths += sorted(Path(root).rglob("*.wbo.xz"))
    if args.limit is not None:
        paths = paths[: args.limit]
    if not paths:
        print("no instances found", file=sys.stderr)
        return 2

    requested_bins = {"post": args.bin}
    if args.baseline_bin:
        requested_bins["pre"] = args.baseline_bin
    binary_provenance = {
        name: executable_provenance(command)
        for name, command in requested_bins.items()
    }
    unusable = [name for name, provenance in binary_provenance.items()
                if not provenance["runnable"]]
    if unusable:
        print("wind tunnel: solver executable(s) unavailable: " +
              ", ".join(f"{name}={binary_provenance[name]['path']}"
                        for name in unusable), file=sys.stderr)
        return 2
    bins = {name: provenance["path"]
            for name, provenance in binary_provenance.items()}
    resource_plan["binaries"] = binary_provenance
    jobs = [(p, name) for p in paths for name in bins]
    print(f"wind tunnel: {len(paths)} instances x {len(bins)} binaries, "
          f"T={timeout_s}s, jobs={args.jobs}", file=sys.stderr)

    results: dict = {}
    done = 0
    with cf.ThreadPoolExecutor(max_workers=args.jobs) as ex:
        futs = {
            ex.submit(run_instance, bins[name], p, args.timeout_ms, wall_cap,
                      env_extra, workdir): (p, name)
            for p, name in jobs
        }
        for fut in cf.as_completed(futs):
            results[futs[fut]] = fut.result()
            done += 1
            if done % 200 == 0:
                print(f"  {done}/{len(jobs)}", file=sys.stderr)

    # Per-instance TSV.
    tsv = outdir / "results.tsv"
    with tsv.open("w") as fh:
        cols = ["instance", "track"]
        for name in bins:
            cols += [f"{name}_s", f"{name}_o", f"{name}_chk", f"{name}_sec"]
        fh.write("\t".join(cols) + "\n")
        for p in paths:
            row = [p.name, classify_track(str(p))]
            for name in bins:
                r = results[(p, name)]
                row += [r["status"], str(r["o"]), r["check"], str(r["seconds"])]
            fh.write("\t".join(row) + "\n")

    # Aggregates.
    summary: dict = {"timeout_s": timeout_s, "instances": len(paths),
                     "binaries": {k: v for k, v in bins.items()},
                     "resource_plan": resource_plan, "tracks": {}}
    wrong = []
    tracks = sorted({classify_track(str(p)) for p in paths})
    for track in tracks:
        tp = [p for p in paths if classify_track(str(p)) == track]
        entry: dict = {"n": len(tp)}
        for name in bins:
            rows = [results[(p, name)] for p in tp]
            bad = [(p.name, r["check"]) for p, r in zip(tp, rows)
                   if r["check"].startswith("BAD")]
            wrong += [(name, track, *b) for b in bad]
            entry[name] = {
                "answers": sum(1 for r in rows if r["status"] in ANSWERS),
                "definitive": sum(1 for r in rows
                                  if r["status"] in ("OPTIMUM FOUND",
                                                     "UNSATISFIABLE")),
                "wrong": len(bad),
                "no_s_line": sum(1 for r in rows if r["status"] == "NOANSWER"),
                "crash": sum(1 for r in rows
                             if r["status"] in {"CRASH", "SPAWN_ERROR"}),
                "walltimeout": sum(1 for r in rows
                                   if r["status"] == "WALLTIMEOUT"),
                "memout": sum(1 for r in rows if r["status"] == "MEMOUT"),
                "par2_any": round(sum(par2(r, timeout_s, False) for r in rows), 1),
                "par2_complete": round(
                    sum(par2(r, timeout_s, True) for r in rows), 1),
            }
        summary["tracks"][track] = entry

    (outdir / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")

    md = [f"# Wind Tunnel — {time.strftime('%Y-%m-%d %H:%M')} UTC",
          f"{len(paths)} instances, T={timeout_s}s, jobs={args.jobs}",
          plan_line, ""]
    header = "| track | n | " + " | ".join(
        f"{n} answers / definitive / PAR-2(any) / PAR-2(complete)" for n in bins
    ) + " |"
    md += [header, "|" + "---|" * (2 + len(bins))]
    for track, entry in summary["tracks"].items():
        cells = [track, str(entry["n"])]
        for name in bins:
            e = entry[name]
            cells.append(f"{e['answers']} / {e['definitive']} / "
                         f"{e['par2_any']} / {e['par2_complete']}")
        md.append("| " + " | ".join(cells) + " |")
    if wrong:
        md += ["", "## WRONG ANSWERS (run fails)"]
        md += [f"- [{n}/{t}] {i}: {c}" for n, t, i, c in wrong]
    (outdir / "report.md").write_text("\n".join(md) + "\n")
    print("\n".join(md))

    if wrong:
        print(f"\nFAIL: {len(wrong)} wrong answers", file=sys.stderr)
        return 3
    return 0


if __name__ == "__main__":
    sys.exit(main())

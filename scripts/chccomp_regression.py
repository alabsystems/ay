#!/usr/bin/env python3
# ay-script: chccomp-regression
# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
"""Soundness/regression safety-net for every baselined CHC solve.

Long-term campaign guard. Loads the development design notes
(instances AY has correctly solved), re-runs each with the current binary, and
reports:
  WRONG        AY now answers the opposite verdict         -> HARD FAIL (exit 2)
  REGRESSION   was solved, now unknown under a matching
               recorded execution envelope                -> FAIL (exit 1)
  INCOMPARABLE was solved under an unknown/different
               historical envelope                        -> report, no claim
  OK           still solved with the same verdict
Any wrong answer is a soundness break (the campaign's 0-wrong banner). Only
matching resource/timeout envelopes can establish a capability regression;
the legacy baseline lacks that metadata, so its non-answers are explicitly
incomparable rather than false failures. Run after every build before pushing.

Usage:
  AY_BIN=target_lever/release/ay.exe python scripts/chccomp_regression.py \
      [--timeout 60] [--jobs 8] [--tracks BV,LIA-Lin] [--max-per-track N]
"""
from __future__ import annotations

import argparse
import hashlib
import io
import json
import os
import subprocess
import sys
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import chccomp_harness as H  # noqa: E402
from _oom_guard import plan_solver_resources, run_captured, warn_concurrent_build  # noqa: E402

REPO = Path(__file__).resolve().parent.parent
BASELINE = REPO / "the development design notes"
RESULTS = REPO / "evals/results/chccomp-regression/latest.json"


def resolve_smt2(year: str, track: str, inst_yml: str) -> str | None:
    root = H.BENCH_ROOT.get(int(year))
    if root is None:
        return None
    yml = root / inst_yml
    if not yml.is_file():
        return None
    import re
    m = re.search(r"input_files:\s*'?([^'\n]+)'?", yml.read_text(encoding="utf-8", errors="replace"))
    if not m:
        return None
    smt2 = (yml.parent / m.group(1).strip()).resolve()
    return str(smt2) if smt2.is_file() else None


def resource_comparison_key(envelope):
    if not isinstance(envelope, dict):
        return None
    fields = (
        "jobs",
        "memlimit_mb_per_child",
        "nbcore_per_child",
        "memory_enforcement",
        "rss_grace_mb",
        "solver_timeout_sec",
        "parent_wall_timeout_sec",
        "timeout_enforcement",
    )
    if any(field not in envelope for field in fields):
        return None
    return {field: envelope[field] for field in fields}


def run(entry, timeout_s, ay_bin, memlimit_mb=0, nbcore=1,
        campaign_envelope=None):
    if memlimit_mb <= 0 or nbcore <= 0:
        raise ValueError("CHC regression run requires positive resource budgets")
    started = time.monotonic()
    smt2 = resolve_smt2(entry["year"], entry["track"], entry["instance"])
    # Per-instance budget: at least `timeout_s`, but scaled to comfortably
    # cover the fastest recorded solve (2x + 20s slack). Instances originally
    # solved at a long budget (e.g. 900s) or under contention would otherwise
    # false-"regress" at a short flat budget — that is a measurement artifact,
    # not a capability loss. Cap to keep the sweep bounded.
    base_wall = float(entry.get("wall", 0.0) or 0.0)
    inst_budget = max(timeout_s, min(int(base_wall * 2) + 20, 900))
    envelope = dict(campaign_envelope or {})
    envelope.update({
        "schema": "ay.benchmark-resource-envelope/v1",
        "jobs": envelope.get("jobs", 1),
        "memlimit_mb_per_child": memlimit_mb,
        "nbcore_per_child": nbcore,
        "memory_enforcement": "AY --memory + process-group rss_watchdog",
        "rss_grace_mb": 0,
        "solver_timeout_sec": inst_budget,
        "parent_wall_timeout_sec": inst_budget + 15,
        "timeout_enforcement": "process-group SIGKILL + reap",
    })
    if smt2 is None:
        return {
            **entry,
            "status": "NO-FILE",
            "memlimit_mb": memlimit_mb,
            "nbcore": nbcore,
            "baseline_resource_envelope": entry.get("resource_envelope"),
            "resource_envelope": envelope,
            "memout": False,
            "timed_out": False,
            "wall_sec": round(time.monotonic() - started, 3),
        }
    argv = [ay_bin, "--chc", "--competition", "--timeout", str(inst_budget * 1000)]
    argv += ["--memory", str(memlimit_mb)]
    argv.append(smt2)
    status = "error"
    exit_code = None
    memout = False
    timed_out = False
    child_env = dict(os.environ, MEMLIMIT=str(memlimit_mb), NBCORE=str(nbcore))
    try:
        captured = run_captured(
            argv,
            memlimit_mb,
            inst_budget + 15,
            label="chccomp_regression.py",
            env=child_env,
        )
    except Exception as exc:
        captured = None
        error = str(exc)[:200]
    if captured is not None:
        exit_code = captured.returncode
        memout = captured.memout
        timed_out = captured.timed_out
        if captured.cancelled or captured.output_truncated:
            status = "error"
            error = "solver output truncated or capture cancelled"
        else:
            status = H.parse_status_stream(io.StringIO(captured.stdout))
            if status == "no-status":
                status = "unknown" if exit_code == 0 else "error"
            error = captured.stderr[-500:] if status == "error" else ""
    if memout:
        status = "memout"
    elif timed_out:
        status = "timeout"
    return {
        **entry,
        "status": status,
        "memlimit_mb": memlimit_mb,
        "nbcore": nbcore,
        "baseline_resource_envelope": entry.get("resource_envelope"),
        "resource_envelope": envelope,
        "memout": memout,
        "timed_out": timed_out,
        "exit_code": exit_code,
        "error": error,
        "wall_sec": round(
            captured.wall_sec if captured is not None
            else time.monotonic() - started,
            3,
        ),
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--timeout", type=int, default=60)
    ap.add_argument("--jobs", type=int, default=8)
    ap.add_argument("--tracks", default="")
    ap.add_argument("--max-per-track", type=int, default=0)
    ap.add_argument("--ay-bin", default=os.environ.get("AY_BIN", str(REPO / "target_lever/release/ay.exe")))
    ap.add_argument("--mem-headroom-mb", type=int, default=None,
                    help="RAM headroom (MiB) the resource planner reserves "
                         "(default: max(16 GiB, RAM/3); lower it to widen the "
                         "per-child --memory envelope, e.g. when re-checking a "
                         "suspected memout regression)")
    args = ap.parse_args()

    if (args.timeout <= 0 or args.jobs <= 0 or args.max_per_track < 0 or
            (args.mem_headroom_mb is not None and args.mem_headroom_mb < 0)):
        print("regression: timeout/jobs must be positive; caps/headroom "
              "must be nonnegative", file=sys.stderr)
        return 2

    # OOM guard (scripts/_oom_guard.py; 2026-06-19 / 2026-07-11 watchdog
    # panics): N parallel ay children each default to an 85%-of-RAM memory
    # limit, sibling-blind — cap jobs and pass each child an explicit --memory.
    try:
        warn_concurrent_build()
        requested_jobs = args.jobs
        plan = plan_solver_resources(args.jobs,
                                     headroom_mb=args.mem_headroom_mb,
                                     label="chccomp_regression.py")
    except RuntimeError as exc:
        if "REFUSING" not in str(exc):
            print(f"regression: resource planning failed: {exc}",
                  file=sys.stderr)
        return 2
    if plan.memlimit_mb <= 0 or plan.nbcore <= 0:
        print("regression: planner returned an unenforceable envelope",
              file=sys.stderr)
        return 2
    if not hasattr(os, "killpg"):
        print("regression: exact process-group RSS enforcement requires POSIX",
              file=sys.stderr)
        return 2
    args.jobs = plan.jobs
    # Always print the plan: the baseline was measured WITHOUT a per-child
    # --memory cap (ay's standalone default is 85% of RAM), so the envelope
    # this run enforces is part of the result and must be on the record.
    plan_line = (f"resource plan: requested={requested_jobs}, jobs={plan.jobs}, "
                 f"--memory={plan.memlimit_mb} MiB/child, "
                 f"NBCORE={plan.nbcore}, exact RSS grace=0 MiB, "
                 f"headroom={plan.headroom_mb} MiB")
    print(f"regression: {plan_line}", flush=True)

    baseline = json.loads(BASELINE.read_text())
    entries = list(baseline.values())
    if args.tracks:
        want = set(args.tracks.split(","))
        entries = [e for e in entries if e["track"] in want]
    if args.max_per_track:
        seen: dict[str, int] = {}
        capped = []
        for e in entries:
            seen[e["track"]] = seen.get(e["track"], 0) + 1
            if seen[e["track"]] <= args.max_per_track:
                capped.append(e)
        entries = capped
    if not entries:
        print("regression: no baseline entries selected", file=sys.stderr)
        return 2

    selection_digest = hashlib.sha256()
    for entry in sorted(entries, key=lambda value: (
            value["year"], value["track"], value["instance"])):
        selection_digest.update(
            f"{entry['year']}/{entry['track']}/{entry['instance']}\0".encode()
        )
    campaign_envelope = {
        "schema": "ay.benchmark-resource-envelope/v1",
        "requested_jobs": requested_jobs,
        "jobs": plan.jobs,
        "memlimit_mb_per_child": plan.memlimit_mb,
        "nbcore_per_child": plan.nbcore,
        "headroom_mb": plan.headroom_mb,
        "memory_enforcement": "AY --memory + process-group rss_watchdog",
        "rss_grace_mb": 0,
        "solver_env": {"MEMLIMIT": str(plan.memlimit_mb),
                       "NBCORE": str(plan.nbcore)},
        "timeout_policy": "max(cli, min(2 * baseline_wall + 20, 900))",
        "timeout_enforcement": "process-group SIGKILL + reap",
        "capture": "temporary files (bounded parent RAM)",
        "executable": H.executable_provenance(args.ay_bin),
        "harness": H.executable_provenance(__file__),
        "benchmark_revisions": {
            str(year): H.git_revision(root)
            for year, root in H.BENCH_ROOT.items()
        },
        "baseline": str(BASELINE.resolve()),
        "baseline_sha256": hashlib.sha256(BASELINE.read_bytes()).hexdigest(),
        "entry_count": len(entries),
        "entry_set_sha256": selection_digest.hexdigest(),
    }

    print(f"regression: {len(entries)} baselined solves, timeout={args.timeout}s, jobs={args.jobs}")
    t0 = time.time()
    wrong, regressed, incomparable, errors, ok, nofile = [], [], [], [], 0, []
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        futs = [
            pool.submit(
                run,
                entry,
                args.timeout,
                args.ay_bin,
                plan.memlimit_mb,
                plan.nbcore,
                campaign_envelope,
            )
            for entry in entries
        ]
        records = []
        done = 0
        for f in as_completed(futs):
            r = f.result()
            records.append(r)
            done += 1
            exp = r["verdict"]
            got = r["status"]
            if got == "NO-FILE":
                nofile.append(r)
            elif got in ("sat", "unsat") and got != exp:
                wrong.append(r)
            elif got == exp:
                ok += 1
            elif got == "error":
                errors.append(r)
            else:
                baseline_key = resource_comparison_key(
                    r.get("baseline_resource_envelope")
                )
                current_key = resource_comparison_key(r["resource_envelope"])
                if baseline_key is not None and baseline_key == current_key:
                    regressed.append(r)
                else:
                    incomparable.append(r)
            if done % 25 == 0:
                print(f"  {done}/{len(entries)} (ok {ok}, regressed "
                      f"{len(regressed)}, incomparable {len(incomparable)}, "
                      f"wrong {len(wrong)})", flush=True)

    payload = {
        "schema": "ay.chccomp-regression-results/v1",
        "resource_envelope": campaign_envelope,
        "summary": {
            "ok": ok,
            "regressed": len(regressed),
            "incomparable": len(incomparable),
            "wrong": len(wrong),
            "error": len(errors),
            "no_file": len(nofile),
        },
        "results": sorted(records, key=lambda record: (
            record["year"], record["track"], record["instance"]
        )),
    }
    RESULTS.parent.mkdir(parents=True, exist_ok=True)
    RESULTS.write_text(json.dumps(payload, indent=2) + "\n")

    print(f"\n=== regression result [{time.time()-t0:.0f}s] ===")
    print(f"  OK:         {ok}/{len(entries)}")
    print(f"  REGRESSED:  {len(regressed)}")
    print(f"  INCOMPARABLE: {len(incomparable)}")
    print(f"  WRONG:      {len(wrong)}")
    print(f"  error:      {len(errors)}")
    print(f"  no-file:    {len(nofile)}")
    for r in regressed[:30]:
        env = r.get("memlimit_mb") or 0
        tag = f"  [--memory {env} MiB]" if env else ""
        print(f"    REGRESSED {r['verdict']}->{r['status']}  {r['track']}/{r['instance']}{tag}")
    for r in wrong:
        print(f"    !! WRONG {r['verdict']}->{r['status']}  {r['track']}/{r['instance']}")
    for r in incomparable[:30]:
        print(f"    INCOMPARABLE {r['verdict']}->{r['status']}  "
              f"{r['track']}/{r['instance']}  "
              "[baseline has no matching resource envelope]")
    print(f"  results:    {RESULTS}")
    if wrong:
        print("\nSOUNDNESS BREAK — wrong answer(s) on baselined instances. DO NOT PUSH.")
        return 2
    if regressed:
        print("\nREGRESSION — matching-envelope previously-solved instance(s) "
              "no longer solved.")
        return 1
    if errors or nofile:
        print("\nINCOMPLETE — infrastructure errors or missing benchmark files "
              "prevent a complete audit.")
        return 2
    if incomparable:
        print("\nINCOMPARABLE — the legacy baseline lacks a matching enforced "
              "resource/timeout envelope; refusing to claim capability "
              "regressions. Definite opposite answers above remain soundness "
              "failures.")
        return 2
    print("\nclean — no wrong answers, no regressions.")
    return 0


if __name__ == "__main__":
    sys.exit(main())

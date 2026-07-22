#!/usr/bin/env python3
# ay-script: planted-sat-fuzz
"""Differential soundness fuzz for SCC equivalent-literal substitution (decompose).

Generates PLANTED-SATISFIABLE CNFs (a fixed assignment satisfies every clause),
heavy on equivalence cycles (the structure decompose's Tarjan-SCC collapses), at
densities where the density gate still runs decompose (< 50). Because every
instance is satisfiable by construction, ANY `s UNSATISFIABLE` verdict is a
provable soundness bug in substitution.

Background: config_preprocess.rs gates decompose off on dense formulas because
of a reported false-UNSAT (#8448). The original repro was lost to a squashed
history; 200 instances here did NOT reproduce it (the bug is well-contained /
possibly historical), but this harness stays as a regression net: run it with
decompose force-enabled (`--sat-variant probe`) and fail CI on any false UNSAT.

Usage: scripts/fuzz/decompose_planted_sat_fuzz.py [count] [ay-binary]
Exit: 0 = no false UNSAT or incomplete child; 1 = false UNSAT; 2 = incomplete.
"""
import argparse
import json
import os
import random
import sys
import tempfile
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parents[1]
REPO = SCRIPTS.parent
sys.path.insert(0, str(SCRIPTS))
from _oom_guard import (  # noqa: E402
    plan_solver_resources,
    run_captured,
    warn_concurrent_build,
)


def gen(n, classes, density, seed):
    r = random.Random(seed)
    A = {v: r.choice([True, False]) for v in range(1, n + 1)}
    vs = list(range(1, n + 1)); r.shuffle(vs)
    cls = [vs[i::classes] for i in range(classes)]
    for c in cls:                       # equal planted value within an SCC
        if c:
            val = A[c[0]]
            for v in c:
                A[v] = val
    clauses = []
    for c in cls:                       # equivalence CYCLE per class -> big SCC
        for i in range(len(c)):
            x, y = c[i], c[(i + 1) % len(c)]
            if x != y:
                clauses.append([-x, y]); clauses.append([x, -y])
    target = int(density * n)
    while len(clauses) < target:        # planted wider clauses for density
        k = r.choice([2, 3, 3, 4, 5])
        lits = set()
        while len(lits) < k:
            v = r.randint(1, n); lits.add(v if r.random() < 0.5 else -v)
        lits = list(lits)
        if not any((l > 0) == A[abs(l)] for l in lits):
            i = r.randrange(len(lits)); v = abs(lits[i]); lits[i] = v if A[v] else -v
        clauses.append(lits)
    r.shuffle(clauses)
    for c in clauses:
        r.shuffle(c)
    return n, clauses


def run(binary, n, clauses, timeout, plan):
    with tempfile.NamedTemporaryFile("w", suffix=".cnf", delete=False) as f:
        f.write(f"p cnf {n} {len(clauses)}\n")
        for c in clauses:
            f.write(" ".join(map(str, c)) + " 0\n")
        path = f.name
    try:
        p = run_captured(
            [
                binary,
                "--memory",
                str(plan.memlimit_mb),
                path,
                "--sat-variant",
                "probe",
                "--no-proof",
            ],
            plan.memlimit_mb,
            timeout,
            label="fuzz/decompose_planted_sat_fuzz.py",
            env=dict(
                os.environ,
                MEMLIMIT=str(plan.memlimit_mb),
                NBCORE=str(plan.nbcore),
            ),
        )
        if p.memout:
            return "MEMOUT", path, p.wall_sec
        if p.timed_out:
            return "TIMEOUT", path, p.wall_sec
        if p.output_truncated:
            return "ERROR", path, p.wall_sec
        s = [line for line in p.stdout.splitlines() if line.startswith("s ")]
        if not s and p.returncode != 0:
            return "CRASH", path, p.wall_sec
        return (s[0] if s else "s ?"), path, p.wall_sec
    except OSError:
        return "ERROR", path, 0.0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("count", nargs="?", type=int, default=120)
    parser.add_argument(
        "ay_binary",
        nargs="?",
        default=(
            "target/release/ay"
            if os.path.exists("target/release/ay")
            else "target/debug/ay"
        ),
    )
    parser.add_argument("--timeout", type=float, default=20.0)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO / "evals/results/planted-sat-fuzz/latest.json",
    )
    args = parser.parse_args()
    if args.count <= 0 or args.timeout <= 0:
        parser.error("count and --timeout must be positive")

    warn_concurrent_build()
    plan = plan_solver_resources(1, label="fuzz/decompose_planted_sat_fuzz.py")
    envelope = {
        "requested_jobs": 1,
        "jobs": plan.jobs,
        "memlimit_mb_per_child": plan.memlimit_mb,
        "nbcore_per_child": plan.nbcore,
        "headroom_mb": plan.headroom_mb,
        "enforcement": (
            "ay --memory; process-group rss_watchdog; MEMLIMIT/NBCORE environment"
        ),
    }
    print(f"resource plan: {json.dumps(envelope, sort_keys=True)}")

    bugs = 0
    incomplete = 0
    records = []
    for seed in range(args.count):
        rng = random.Random(seed * 7 + 1)
        n = rng.choice([40, 60, 90, 120])
        classes = rng.choice([2, 3, 5, 8])
        density = rng.choice([12, 20, 28, 38, 46])
        nn, clauses = gen(n, classes, density, seed)
        verdict, path, wall = run(
            args.ay_binary, nn, clauses, args.timeout, plan
        )
        record = {
            "seed": seed,
            "variables": nn,
            "classes": classes,
            "density": density,
            "clauses": len(clauses),
            "verdict": verdict,
            "wall_seconds": wall,
        }
        if "UNSATISF" in verdict:
            bugs += 1
            record["witness"] = path
            print(
                f"FALSE-UNSAT (decompose soundness bug): seed={seed} n={nn} "
                f"classes={classes} density~{density} clauses={len(clauses)} "
                f"file={path}"
            )
        elif verdict in ("TIMEOUT", "MEMOUT", "CRASH", "ERROR"):
            incomplete += 1
            record["witness"] = path
            print(f"INCOMPLETE: seed={seed} verdict={verdict} file={path}")
        else:
            os.unlink(path)
        records.append(record)

    evidence = {
        "schema": "ay-planted-sat-fuzz-v1",
        "binary": args.ay_binary,
        "count": args.count,
        "false_unsat": bugs,
        "incomplete": incomplete,
        "resource_plan": envelope,
        "records": records,
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(evidence, indent=2) + "\n", encoding="utf-8")
    print(
        f"ran={args.count} false_unsat={bugs} incomplete={incomplete} "
        f"binary={args.ay_binary} evidence={args.out}"
    )
    if bugs:
        return 1
    if incomplete:
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

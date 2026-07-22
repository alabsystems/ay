#!/usr/bin/env python3
# ay-script: chc-refonly-time
"""Measure how many ref_only instances ay closes at a longer (competition-realistic)
timeout. Samples the ref_only_list from a full baseline JSON, runs ay --chc, and
checks every solved verdict against the .yml expected_verdict (soundness)."""
import argparse, concurrent.futures as cf, json, os, re, subprocess, sys, time
from collections import Counter

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from _oom_guard import plan_solver_resources, warn_concurrent_build  # noqa: E402

VR = re.compile(r"^(sat|unsat|unknown)\s*$")

def expected(smt2):
    d, base = os.path.dirname(smt2), os.path.basename(smt2)
    for y in os.listdir(d):
        if y.endswith(".yml"):
            t = open(os.path.join(d, y), errors="replace").read()
            if f"input_files: {base}" in t or f"input_files: '{base}'" in t:
                if "expected_verdict: true" in t: return "sat"
                if "expected_verdict: false" in t: return "unsat"
    return None

def verdict(out):
    v = "unknown"
    for l in out.splitlines():
        if VR.match(l.strip()): v = l.strip()
    return v

def run(smt2, ay, t, memlimit_mb=0):
    argv = [ay, "--chc", "--timeout", str(t*1000)]
    if memlimit_mb:
        # Per-child envelope: ay's standalone default is 85% of RAM per
        # process, sibling-blind across workers (scripts/_oom_guard.py).
        argv += ["--memory", str(memlimit_mb)]
    argv.append(smt2)
    t0 = time.time()
    try:
        p = subprocess.run(argv, capture_output=True, text=True, timeout=t+12)
        return verdict(p.stdout+"\n"+p.stderr), round(time.time()-t0,1)
    except subprocess.TimeoutExpired:
        return "unknown", round(time.time()-t0,1)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("baseline_json"); ap.add_argument("--set-root", default="benchmarks/chc/chc-comp25-benchmarks")
    ap.add_argument("--timeout", type=int, default=60); ap.add_argument("--stride", type=int, default=8)
    ap.add_argument("--workers", type=int, default=5); ap.add_argument("--ay", default="./target/release/ay")
    a = ap.parse_args()
    rels = json.load(open(a.baseline_json))["summary"]["ref_only_list"][::a.stride]
    jobs = []
    for rel in rels:
        yml = os.path.join(a.set_root, rel)
        try: m = re.search(r"input_files:\s*'?([^'\n]+)'?", open(yml, errors="replace").read())
        except OSError: continue
        if not m: continue
        smt2 = os.path.join(os.path.dirname(yml), m.group(1).strip())
        if os.path.exists(smt2): jobs.append((rel, smt2))
    # OOM guard (scripts/_oom_guard.py): cap workers and give each ay child an
    # explicit --memory envelope.
    warn_concurrent_build()
    plan = plan_solver_resources(a.workers, label="chc_refonly_time.py")
    a.workers = plan.jobs
    print(f"ref_only sample: {len(jobs)}  ay timeout: {a.timeout}s  "
          f"workers: {a.workers}  --memory: {plan.memlimit_mb or 'default'} MiB/child")
    solved, wrong, fam = 0, [], Counter()
    def work(j):
        rel, smt2 = j; v, dt = run(smt2, a.ay, a.timeout, plan.memlimit_mb); return rel, smt2, v, dt
    with cf.ThreadPoolExecutor(max_workers=a.workers) as ex:
        for rel, smt2, v, dt in ex.map(work, jobs):
            if v in ("sat","unsat"):
                solved += 1; fam[rel.split("/")[0]] += 1
                exp = expected(smt2)
                if exp and v != exp: wrong.append({"rel": rel, "ay": v, "expected": exp})
                print(f"  CLOSED {v:6} ({dt:5.1f}s) {rel}", flush=True)
    print(f"\n=== {solved}/{len(jobs)} prior-ref_only CLOSED at {a.timeout}s; WRONG={len(wrong)} ===")
    print("by family:", dict(fam))
    if wrong: print("!!! WRONG ANSWERS:", wrong)

if __name__ == "__main__":
    main()

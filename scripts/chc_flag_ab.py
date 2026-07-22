#!/usr/bin/env python3
# ay-script: chc-flag-ab
"""A/B a set of ay --chc env configs on the ref_only instances from a baseline JSON.

For each instance (z3 solved, ay did not at baseline timeout) run ay under each
named config at a longer timeout and report how many flip to solved, and whether
any answer is WRONG vs the .yml expected_verdict.
"""
import argparse, concurrent.futures as cf, json, os, re, subprocess, sys, time
from collections import Counter

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from _oom_guard import plan_solver_resources, warn_concurrent_build  # noqa: E402

VERDICT_RE = re.compile(r"^(sat|unsat|unknown)\s*$")

def expected_for(smt2):
    # sibling .yml: input_files points here; expected_verdict true->sat false->unsat
    d = os.path.dirname(smt2)
    base = os.path.basename(smt2)
    for yml in os.listdir(d):
        if yml.endswith(".yml"):
            txt = open(os.path.join(d, yml), errors="replace").read()
            if f"input_files: {base}" in txt or f"input_files: '{base}'" in txt:
                if "expected_verdict: true" in txt:
                    return "sat"
                if "expected_verdict: false" in txt:
                    return "unsat"
    return None

def parse_verdict(out):
    v = "unknown"
    for line in out.splitlines():
        m = VERDICT_RE.match(line.strip())
        if m:
            v = m.group(1)
    return v

def run_ay(smt2, ay_bin, timeout_s, env_extra, memlimit_mb=0):
    env = dict(os.environ)
    env.update(env_extra)
    argv = [ay_bin, "--chc", "--timeout", str(timeout_s * 1000)]
    if memlimit_mb:
        # Per-child envelope: ay's standalone default is 85% of RAM per
        # process, sibling-blind across workers (scripts/_oom_guard.py).
        argv += ["--memory", str(memlimit_mb)]
    argv.append(smt2)
    t0 = time.time()
    try:
        p = subprocess.run(argv,
                           capture_output=True, text=True, timeout=timeout_s + 10, env=env)
        return parse_verdict(p.stdout + "\n" + p.stderr), round(time.time() - t0, 2)
    except subprocess.TimeoutExpired:
        return "unknown", round(time.time() - t0, 2)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("baseline_json")
    ap.add_argument("--corpus-root", default="benchmarks/chc/chc-comp25-benchmarks")
    ap.add_argument("--set-root", default="benchmarks/chc/chc-comp25-benchmarks")
    ap.add_argument("--timeout", type=int, default=30)
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--ay", default="./target/release/ay")
    ap.add_argument("--out", default="")
    a = ap.parse_args()

    base = json.load(open(a.baseline_json))
    # resolve ref_only .yml rels -> smt2 (reuse results entries for the smt2 path)
    by_rel = {r["rel"]: r for r in base["results"]}
    rels = base["summary"]["ref_only_list"]
    targets = []
    for rel in rels:
        yml = os.path.join(a.set_root, rel)
        try:
            ytxt = open(yml, errors="replace").read()
        except OSError:
            continue
        m = re.search(r"input_files:\s*'?([^'\n]+)'?", ytxt)
        if not m:
            continue
        smt2 = os.path.join(os.path.dirname(yml), m.group(1).strip())
        if os.path.exists(smt2):
            targets.append((rel, smt2))

    configs = {
        "default_long": {},
        "intern_long": {"AY_CHC_INTERN": "1"},
    }

    # OOM guard (scripts/_oom_guard.py): cap workers to a safe RAM budget and
    # give each ay child an
    # explicit --memory envelope.
    warn_concurrent_build()
    plan = plan_solver_resources(a.workers, label="chc_flag_ab.py")
    a.workers = plan.jobs

    print(f"ref_only targets resolved: {len(targets)} (timeout {a.timeout}s, "
          f"workers {a.workers}, --memory {plan.memlimit_mb or 'default'} MiB/child)")
    out = {"timeout": a.timeout, "n_targets": len(targets),
           "workers": a.workers, "memlimit_mb": plan.memlimit_mb, "configs": {}}

    for cfg_name, env_extra in configs.items():
        solved = 0
        wrong = []
        per = []
        def work(t):
            rel, smt2 = t
            v, dt = run_ay(smt2, a.ay, a.timeout, env_extra, plan.memlimit_mb)
            exp = expected_for(smt2)
            return rel, v, dt, exp
        with cf.ThreadPoolExecutor(max_workers=a.workers) as ex:
            for rel, v, dt, exp in ex.map(work, targets):
                if v in ("sat", "unsat"):
                    solved += 1
                    if exp and v != exp:
                        wrong.append({"rel": rel, "ay": v, "expected": exp})
                per.append({"rel": rel, "ay": v, "t": dt, "expected": exp})
                print(f"[{cfg_name}] {v:7} ({dt:5.1f}s) exp={exp} {rel}", flush=True)
        fam = Counter(p["rel"].split("/")[0] for p in per if p["ay"] in ("sat", "unsat"))
        out["configs"][cfg_name] = {"solved_of_refonly": solved, "wrong": wrong,
                                    "solved_by_family": dict(fam), "per": per}
        print(f"\n=== {cfg_name}: solved {solved}/{len(targets)} of prior ref_only; wrong={len(wrong)} ===\n")

    print(json.dumps({k: {"solved_of_refonly": v["solved_of_refonly"],
                          "wrong": len(v["wrong"]), "by_family": v["solved_by_family"]}
                      for k, v in out["configs"].items()}, indent=1))
    if a.out:
        json.dump(out, open(a.out, "w"), indent=1)
        print(f"wrote {a.out}")

if __name__ == "__main__":
    main()

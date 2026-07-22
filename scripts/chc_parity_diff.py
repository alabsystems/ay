#!/usr/bin/env python3
# ay-script: chc-parity-diff
"""CHC parity differential: ay --chc vs z3 fp.engine=spacer on a benchexec .set.

Usage:
  chc_parity_diff.py SET_FILE [--timeout S] [--stride N] [--limit K]
                     [--workers W] [--ay PATH] [--out JSON]

Resolves each .yml's input_files to its sibling .smt2, runs both solvers, and
classifies agree / ay_only / ref_only / disagree / both_unknown, plus checks each
solver's verdict against the .yml expected_verdict to flag WRONG answers.
"""
import argparse, concurrent.futures as cf, json, os, re, sys, time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from _oom_guard import plan_solver_resources, run_captured, warn_concurrent_build  # noqa: E402

VERDICT_RE = re.compile(r"^(sat|unsat|unknown)\s*$")

def read_expected(yml_path):
    try:
        txt = open(yml_path, "r", errors="replace").read()
    except OSError:
        return None, None
    inp = None
    exp = None
    for line in txt.splitlines():
        s = line.strip()
        if s.startswith("input_files:"):
            inp = s.split(":", 1)[1].strip().strip("'\"")
        if s.startswith("expected_verdict:"):
            v = s.split(":", 1)[1].strip().lower()
            if v == "true":
                exp = "sat"      # SAFE -> CHC system SAT (invariant exists)
            elif v == "false":
                exp = "unsat"    # UNSAFE -> CHC system UNSAT (counterexample)
    return inp, exp

def parse_verdict(out):
    v = "unknown"
    for line in out.splitlines():
        m = VERDICT_RE.match(line.strip())
        if m:
            v = m.group(1)   # last bare verdict line wins
    return v

def run(cmd, hard_timeout, memlimit_mb, nbcore):
    t0 = time.time()
    try:
        p = run_captured(
            cmd,
            memlimit_mb,
            hard_timeout,
            label="chc_parity_diff.py",
            env=dict(os.environ, MEMLIMIT=str(memlimit_mb),
                     NBCORE=str(max(1, nbcore))),
        )
        if p.memout:
            return "memout", time.time() - t0
        if p.timed_out or p.cancelled:
            return "unknown", time.time() - t0
        if p.output_truncated:
            return "unknown", time.time() - t0
        return parse_verdict(p.stdout + "\n" + p.stderr), time.time() - t0
    except (OSError, RuntimeError):
        return "unknown", time.time() - t0

def solve_one(smt2, ay_bin, timeout, memlimit_mb=0, nbcore=1):
    # ay --chc --timeout is MILLISECONDS; z3 -T: is SECONDS.
    # Same per-child memory envelope for BOTH solvers. AY gets its graceful
    # --memory path; both children get the external RSS watchdog because z3's
    # -memory counter is not a footprint bound.
    ay_argv = [ay_bin, "--chc", "--timeout", str(timeout * 1000)]
    z3_argv = ["z3", "fp.engine=spacer", f"-T:{timeout}"]
    if memlimit_mb:
        ay_argv += ["--memory", str(memlimit_mb)]
        z3_argv += [f"-memory:{memlimit_mb}"]
    ay_v, ay_t = run(ay_argv + [smt2], timeout + 8, memlimit_mb, nbcore)
    z3_v, z3_t = run(z3_argv + [smt2], timeout + 8, memlimit_mb, nbcore)
    return ay_v, ay_t, z3_v, z3_t

def classify(ay, z3):
    defed = lambda v: v in ("sat", "unsat")
    if defed(ay) and defed(z3):
        return "agree" if ay == z3 else "disagree"
    if defed(ay) and not defed(z3):
        return "ay_only"
    if defed(z3) and not defed(ay):
        return "ref_only"
    return "both_unknown"

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("set_file")
    ap.add_argument("--timeout", type=int, default=10)
    ap.add_argument("--stride", type=int, default=1)
    ap.add_argument("--limit", type=int, default=0)
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--ay", default="./target/release/ay")
    ap.add_argument("--out", default="")
    a = ap.parse_args()

    # OOM guard (scripts/_oom_guard.py): cap workers to a safe RAM budget; each
    # worker runs one solver
    # process at a time, and both solvers get the same --memory envelope.
    warn_concurrent_build()
    requested_workers = a.workers
    plan = plan_solver_resources(a.workers, label="chc_parity_diff.py")
    a.workers = plan.jobs
    print(f"workers={a.workers} memory envelope="
          f"{plan.memlimit_mb} MiB/child NBCORE={plan.nbcore} "
          "(rss_watchdog both; ay --memory)",
          flush=True)

    root = os.path.dirname(os.path.abspath(a.set_file))
    entries = [l.strip() for l in open(a.set_file) if l.strip()]
    entries = entries[:: a.stride]
    if a.limit:
        entries = entries[: a.limit]

    jobs = []
    for rel in entries:
        yml = os.path.join(root, rel)
        inp, exp = read_expected(yml)
        if not inp:
            continue
        smt2 = os.path.join(os.path.dirname(yml), inp)
        if not os.path.exists(smt2):
            continue
        fam = rel.split("/")[0]
        jobs.append((rel, smt2, fam, exp))

    results = []
    counts = {k: 0 for k in ("agree", "ay_only", "ref_only", "disagree", "both_unknown")}
    ay_wrong, z3_wrong = [], []
    ay_solved = z3_solved = 0

    def work(job):
        rel, smt2, fam, exp = job
        ay, ayt, z3, z3t = solve_one(smt2, a.ay, a.timeout,
                                     plan.memlimit_mb, plan.nbcore)
        return rel, fam, exp, ay, ayt, z3, z3t

    with cf.ThreadPoolExecutor(max_workers=a.workers) as ex:
        for (rel, fam, exp, ay, ayt, z3, z3t) in ex.map(work, jobs):
            cls = classify(ay, z3)
            counts[cls] += 1
            if ay in ("sat", "unsat"):
                ay_solved += 1
            if z3 in ("sat", "unsat"):
                z3_solved += 1
            if exp and ay in ("sat", "unsat") and ay != exp:
                ay_wrong.append({"rel": rel, "ay": ay, "expected": exp})
            if exp and z3 in ("sat", "unsat") and z3 != exp:
                z3_wrong.append({"rel": rel, "z3": z3, "expected": exp})
            results.append({"rel": rel, "family": fam, "expected": exp,
                            "ay": ay, "ay_time": round(ayt, 3),
                            "z3": z3, "z3_time": round(z3t, 3), "class": cls})
            print(f"[{cls:12}] ay={ay:7} z3={z3:7} {rel}", flush=True)

    summary = {
        "set_file": a.set_file, "timeout": a.timeout, "stride": a.stride,
        "workers": a.workers, "memlimit_mb": plan.memlimit_mb,
        "resource_plan": {
            "requested_jobs": requested_workers,
            "jobs": a.workers,
            "memlimit_mb_per_child": plan.memlimit_mb,
            "nbcore_per_child": plan.nbcore,
            "headroom_mb": plan.headroom_mb,
            "enforcement": "rss_watchdog(all solvers) + ay --memory",
        },
        "n": len(jobs), "ay_solved": ay_solved, "z3_solved": z3_solved,
        "counts": counts,
        "ay_wrong": ay_wrong, "z3_wrong": z3_wrong,
        "ref_only_list": [r["rel"] for r in results if r["class"] == "ref_only"],
        "disagree_list": [r for r in results if r["class"] == "disagree"],
    }
    print("\n=== SUMMARY ===")
    print(json.dumps(summary, indent=1))
    if a.out:
        json.dump({"summary": summary, "results": results}, open(a.out, "w"), indent=1)
        print(f"\nwrote {a.out}")

if __name__ == "__main__":
    main()

#!/usr/bin/env python3
# ay-script: smt-diff-sweep
"""Differential SMT sweep harness for SMT-COMP prep.

Runs AY and a field of competitor solvers over a corpus of .smt2 files
(incremental or single-query), compares the ordered sequence of
sat/unsat/unknown answers, and reports:

  * soundness conflicts  (one solver says sat where another says unsat)
  * per-solver solved / unknown / timeout / error counts
  * files where AY is uniquely unknown/slow vs the field

This is the data that tells us which division/track AY can actually win:
a track win = most files fully solved with ZERO soundness conflicts.

Usage:
  scripts/diff_sweep.py --corpus benchmarks/smtcomp-incremental/QF_UFLIA \
      --timeout 20 --out evals/results/incr-sweep/qf_uflia.json [--limit N]
"""
import argparse, json, os, random, sys, time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

sys.path.insert(0, str(Path(__file__).resolve().parent))
from _oom_guard import (  # noqa: E402
    plan_solver_resources,
    run_captured,
    warn_concurrent_build,
)

# Each solver: (argv template). {f} is the benchmark path.
# Only solvers whose binary is found are run.
SOLVERS = {
    "ay":          [str(ROOT / "target/release/ay"), "solve", "--competition", "{f}"],
    "z3":          ["z3", "{f}"],
    "cvc5":        [str(ROOT / ".competitors/cvc5"), "--incremental", "-q", "{f}"],
    "bitwuzla":    ["bitwuzla", "{f}"],
    "yices":       ["yices-smt2", "--incremental", "{f}"],
    "smtinterpol": ["java", "-jar", str(ROOT / ".competitors/smtinterpol.jar"), "{f}"],
    "opensmt":     [str(ROOT / ".competitors/opensmt"), "{f}"],
}

RESULT_TOKENS = {"sat", "unsat", "unknown"}


def _which_path(cmd):
    for p in os.environ.get("PATH", "").split(":"):
        if p and os.access(os.path.join(p, cmd), os.X_OK):
            return True
    return False


def available_solvers():
    avail = {}
    for name, argv in SOLVERS.items():
        # Every absolute path in the argv must exist (catches e.g. smtinterpol
        # whose launcher `java` is present but whose jar is not — previously
        # counted "available" and then errored on every single file).
        ok = True
        for i, a in enumerate(argv):
            if a.startswith("/"):
                if not os.path.exists(a):
                    ok = False
                    break
            elif i == 0 and not _which_path(a):
                ok = False
                break
        if ok:
            avail[name] = argv
    return avail


def run_solver(argv, fpath, timeout, memlimit_mb=0, nbcore=1):
    """Return (tokens:list[str], status:str, wall:float).
    status in {ok, timeout, memout, error}. tokens are the ordered
    sat/unsat/unknown.

    The SAME memory envelope is enforced on every solver (rss_watchdog hard
    kill => "memout"): capping only ay while the field runs unbounded would
    silently fold ay memout artifacts into ay_unique_unsolved and skew the
    comparison. ay additionally gets --memory (see main()) so it returns a
    graceful `unknown` before the backstop fires.
    """
    cmd = ["gtimeout", str(timeout)] + [a.replace("{f}", fpath) for a in argv]
    try:
        result = run_captured(
            cmd,
            memlimit_mb,
            timeout_s=timeout + 30,
            label="diff_sweep.py",
            env=dict(os.environ, MEMLIMIT=str(memlimit_mb),
                     NBCORE=str(max(1, nbcore))),
        )
    except Exception as e:  # noqa
        return [], f"error:{e}", 0.0
    wall = result.wall_sec
    if result.memout:
        return [], "memout", wall
    if result.timed_out or result.returncode == 124:
        return [], "timeout", wall
    if result.output_truncated:
        return [], "error:solver output exceeded capture limit", wall
    tokens = [
        ln.strip()
        for ln in result.stdout.splitlines()
        if ln.strip() in RESULT_TOKENS
    ]
    if not tokens:
        # error or unsupported logic; capture a short reason
        reason = (result.stderr or result.stdout).strip().splitlines()
        msg = reason[0][:80] if reason else f"rc={result.returncode}"
        return [], f"error:{msg}", wall
    return tokens, "ok", wall


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--corpus", required=True)
    ap.add_argument("--timeout", type=int, default=20)
    ap.add_argument("--limit", type=int, default=0, help="cap number of files (0=all)")
    ap.add_argument("--sample", type=int, default=0,
                    help="seeded random sample of N files across the whole corpus "
                         "(0=off). Unlike --limit, avoids sorted-prefix family bias.")
    ap.add_argument("--seed", type=int, default=2026, help="RNG seed for --sample")
    ap.add_argument("--out", required=True)
    ap.add_argument("--jobs", type=int, default=max(2, (os.cpu_count() or 4) - 2))
    ap.add_argument("--max-file-bytes", type=int, default=0,
                    help="skip .smt2 files larger than this (0=no cap). Bounds "
                         "solver memory on huge bit-blasting/array instances.")
    args = ap.parse_args()

    # OOM guard (scripts/_oom_guard.py): each job runs one solver process at a
    # time, so concurrent
    # solvers = jobs. Cap jobs to a safe RAM budget and enforce the SAME
    # per-child envelope on every solver via the rss_watchdog backstop in
    # run_solver (status "memout"). ay additionally gets --memory so it trips
    # its internal guard and answers `unknown` gracefully before the backstop.
    warn_concurrent_build()
    requested_jobs = args.jobs
    plan = plan_solver_resources(requested_jobs, label="diff_sweep.py")
    args.jobs = plan.jobs

    solvers = available_solvers()
    if "ay" in solvers and plan.memlimit_mb:
        ay_argv = solvers["ay"]
        solvers["ay"] = ay_argv[:-1] + ["--memory", str(plan.memlimit_mb)] + ay_argv[-1:]
    resource_plan = dict(requested_jobs=requested_jobs, jobs=args.jobs,
                         memlimit_mb_per_child=plan.memlimit_mb,
                         nbcore_per_child=plan.nbcore,
                         headroom_mb=plan.headroom_mb,
                         enforcement="rss_watchdog(all solvers) + ay --memory")
    print(f"solvers: {', '.join(solvers)} (jobs={args.jobs}, "
          f"envelope {plan.memlimit_mb or 'none'} MiB/child for ALL solvers)",
          file=sys.stderr)

    files = sorted(Path(args.corpus).rglob("*.smt2"))
    skipped_big = 0
    if args.max_file_bytes:
        kept = []
        for f in files:
            try:
                if f.stat().st_size <= args.max_file_bytes:
                    kept.append(f)
                else:
                    skipped_big += 1
            except OSError:
                pass
        files = kept
    if args.sample and args.sample < len(files):
        rng = random.Random(args.seed)
        files = sorted(rng.sample(files, args.sample))
    if args.limit:
        files = files[:args.limit]
    print(f"files: {len(files)} from {args.corpus} "
          f"(skipped {skipped_big} over {args.max_file_bytes}B)", file=sys.stderr)

    per_solver = {s: dict(solved=0, unknown=0, timeout=0, memout=0, error=0, time=0.0)
                  for s in solvers}
    conflicts = []
    ay_unique_unsolved = []
    records = []

    def process_file(f):
        fp = str(f)
        res = {}
        for s, argv in solvers.items():
            tokens, status, wall = run_solver(argv, fp, args.timeout,
                                              memlimit_mb=plan.memlimit_mb,
                                              nbcore=plan.nbcore)
            res[s] = dict(tokens=tokens, status=status, wall=round(wall, 3))
        return fp, res

    done = 0
    with ThreadPoolExecutor(max_workers=args.jobs) as ex:
        for fp, res in ex.map(process_file, files):
            done += 1
            for s in solvers:
                per_solver[s]["time"] += res[s]["wall"]

            # classify each solver on this file
            defin = {}  # solver -> tuple of definitive tokens if fully solved
            for s, r in res.items():
                if r["status"] == "timeout":
                    per_solver[s]["timeout"] += 1
                elif r["status"] == "memout":
                    per_solver[s]["memout"] += 1
                elif r["status"].startswith("error"):
                    per_solver[s]["error"] += 1
                elif any(t == "unknown" for t in r["tokens"]):
                    per_solver[s]["unknown"] += 1
                else:
                    per_solver[s]["solved"] += 1
                    defin[s] = tuple(r["tokens"])

            # soundness conflict: two solvers fully-solved with contradictory
            # token at some position
            names = list(defin)
            conflict = None
            for a_i in range(len(names)):
                for b_i in range(a_i + 1, len(names)):
                    ta, tb = defin[names[a_i]], defin[names[b_i]]
                    n = min(len(ta), len(tb))
                    for k in range(n):
                        if {ta[k], tb[k]} == {"sat", "unsat"}:
                            conflict = dict(file=fp, pos=k,
                                            a=names[a_i], a_val=ta[k],
                                            b=names[b_i], b_val=tb[k])
                            break
                    if conflict:
                        break
                if conflict:
                    break
            if conflict:
                conflicts.append(conflict)

            # AY uniquely unsolved (others solved, AY not)
            if "ay" in res:
                ay_solved = "ay" in defin
                others_solved = [s for s in defin if s != "ay"]
                if not ay_solved and others_solved:
                    ay_unique_unsolved.append(dict(file=fp, ay=res["ay"]["status"],
                                                   solved_by=others_solved))
            records.append(dict(file=os.path.relpath(fp, args.corpus), res=res))
            if done % 50 == 0:
                print(f"  ..{done}/{len(files)}", file=sys.stderr)

    # solver_argv + resource_plan make the enforced envelope part of the
    # persisted record: sweeps run under different envelopes (or the pre-guard
    # unbounded default) must never be compared as if equivalent, and
    # ay_unique_unsolved entries can be checked against per-record "memout".
    summary = dict(corpus=args.corpus, timeout=args.timeout, n_files=len(files),
                   solvers=list(solvers),
                   solver_argv={s: a for s, a in solvers.items()},
                   resource_plan=resource_plan, per_solver=per_solver,
                   n_conflicts=len(conflicts), conflicts=conflicts[:50],
                   ay_unique_unsolved_count=len(ay_unique_unsolved),
                   ay_unique_unsolved=ay_unique_unsolved[:50])
    outp = Path(args.out)
    outp.parent.mkdir(parents=True, exist_ok=True)
    outp.write_text(json.dumps(dict(summary=summary, records=records), indent=2))

    # human summary
    print("\n=== SWEEP SUMMARY ===")
    print(f"corpus={args.corpus} files={len(files)} timeout={args.timeout}s "
          f"envelope={plan.memlimit_mb or 'none'}MiB/child")
    hdr = (f"{'solver':10} {'solved':>7} {'unknown':>8} {'timeout':>8} "
           f"{'memout':>7} {'error':>7} {'time(s)':>9}")
    print(hdr)
    for s in solvers:
        d = per_solver[s]
        print(f"{s:10} {d['solved']:>7} {d['unknown']:>8} {d['timeout']:>8} "
              f"{d['memout']:>7} {d['error']:>7} {d['time']:>9.1f}")
    print(f"\nSOUNDNESS CONFLICTS (sat-vs-unsat between solvers): {len(conflicts)}")
    for c in conflicts[:20]:
        print(f"  {c['file']} @check-sat#{c['pos']}: {c['a']}={c['a_val']} vs {c['b']}={c['b_val']}")
    print(f"\nAY uniquely unsolved (field solved, AY did not): {len(ay_unique_unsolved)}")
    print(f"\nwrote {args.out}")


if __name__ == "__main__":
    main()

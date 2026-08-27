#!/usr/bin/env python3
# ay-script: sat-sweep
"""Lightweight SAT sweep harness for local iteration benchmarking.

Runs one or more solvers over a directory of DIMACS CNFs at a fixed timeout,
records per-instance verdict + wall time, cross-checks solvers against each
other for soundness disagreements (SAT vs UNSAT = critical wrong answer), and
reports solved-count + PAR-2 per solver.

Not a competition harness — a fast, reproducible signal for before/after deltas.

Usage:
  sweep.py --dir DIR --timeout 60 --workers 8 \
      --solver ay=./target/release/ay [--solver kissat=/tmp/kissat/build/kissat] \
      --out results.json
"""
import argparse, concurrent.futures as cf, datetime, functools, glob, hashlib, json, os, re, shutil, subprocess, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from _oom_guard import plan_solver_resources, run_captured, warn_concurrent_build

@functools.lru_cache(maxsize=None)
def kissat_accepts_options(path):
    """True when this Kissat build still has its command-line options compiled in.

    Competition builds (`./configure --competition` = `--no-options --quiet`)
    reject every short/long option, so the harness must invoke them bare and
    lean on its own process-group wall clock instead of `--time`.
    """
    try:
        probe = subprocess.run([path, "--time=1", "--version"],
                               capture_output=True, timeout=30)
        return probe.returncode == 0
    except (OSError, subprocess.SubprocessError):
        return False

def solver_reported_memout(result):
    """True when the captured output carries ay's graceful memout marker.

    The binary's memout grammar (crates/ay/src/main.rs, MEMOUT_* constants):
      - SMT-LIB grammar: stdout `unknown`, stderr `(:reason-unknown "memout")`,
        rc 124 -- the bare rc fallback used to mislabel these rows "timeout"
        (impossible 8 s "timeouts" on a 300 s budget).
      - --competition grammar: `c memout` on BOTH stdout and stderr plus
        `s UNKNOWN`, rc 0. The stdout copy is load-bearing here:
        ~/ay-bench/bin/ay-proofmode discards the child's stderr, so a
        proof-mode sweep only ever sees the stdout marker.
    """
    for stream in (result.stdout, result.stderr):
        if '(:reason-unknown "memout")' in stream:
            return True
        if any(line.strip() == "c memout" for line in stream.splitlines()):
            return True
    return False


SOLVER_WALL_RE = re.compile(r"\b(?:wall_time_ms|ay-wall-ms)=(\d+)")


def solver_reported_wall_ms(result):
    """AY's OWN wall clock, or None.

    Two spellings, because the number lives on STDERR (`c ay.session.end ...
    wall_time_ms=`) and ~/ay-bench/bin/ay-proofmode discards the child's stderr:
    the wrapper re-publishes it on stdout as `c ay-wall-ms=`.

    The harness clock is not the solve time: it also carries wrapper fork
    overhead and, in proof mode, whatever the wrapper does after the solver
    exits. Pricing a row at the solver's own clock is what makes a proof-mode
    PAR-2 mean the same thing as a bare-binary one. See
    scripts/verify_proof_manifest.py for the three configurations this
    distinction protects.
    """
    for stream in (result.stdout, result.stderr):
        hits = SOLVER_WALL_RE.findall(stream or "")
        if hits:
            return int(hits[-1])
    return None

# SAT Competition 2026 Main Track envelope, from
# https://satcompetition.github.io/2026/tracks.html : "The solvers will be
# executed with a time limit of 5000 seconds and memory limit of 32GB." (It was
# 128 GB in 2024 and 30 GB in 2025, so this is re-checked per year, not assumed.)
#
# This constant exists because a sweep silently measured against a cap 5.3x
# tighter than the competition's: six workers sharing one 137 GB box got
# --mem-mb 6000 each, and 23 instances were recorded `memout` and counted as
# losses. Re-run at 32 GB, they solve -- 6.xz in 9.4 s at 7.1 GB peak,
# oddball_70_5 in 188 s at 13.6 GB, both models verified against the full CNF.
# A memout under a sub-competition cap is an UNMEASURED row, exactly as a
# missing proof verdict is unmeasured rather than unverified.
SATCOMP_MEMORY_LIMIT_MB = 32_768


def solver_provenance(path):
    """Identify WHICH build produced a run's rows.

    A sweep JSON used to record `solver_configuration: "competition"` and
    nothing else, so a row could not be attributed to a binary. That is not
    cosmetic: on 2026-08-26 simon-r20-0/simon-r22-1 sat in
    proofmode-full400-aug25-corrected.json as 300 s timeouts while the binary
    on disk solved both in ~85 ms through the identical wrapper, NBCORE and
    memory cap. The rows were stale -- produced by an older build, kept after
    the regression was fixed -- and there was no way to prove that from the
    file. Everything derived from such a file inherits the error, so record
    the identity of the binary alongside the numbers.

    Hashing is capped: a solver binary is tens of MB, but some entries are
    shell wrappers of a few hundred bytes, and both must be identified.
    """
    info = {"path": path}
    real = shutil.which(path) or path
    try:
        st = os.stat(real)
        info["resolved"] = os.path.realpath(real)
        info["size"] = st.st_size
        info["mtime_utc"] = datetime.datetime.utcfromtimestamp(
            st.st_mtime).strftime("%Y-%m-%dT%H:%M:%SZ")
        h = hashlib.sha256()
        with open(real, "rb") as f:
            for chunk in iter(lambda: f.read(1 << 20), b""):
                h.update(chunk)
        info["sha256"] = h.hexdigest()
    except OSError as e:
        info["error"] = str(e)
        return info
    # Best-effort build stamp. A wrapper script has no --version and must not
    # be allowed to hang or to pollute the record with a usage error.
    try:
        p = subprocess.run([real, "--version"], capture_output=True,
                           text=True, timeout=20)
        if p.returncode == 0 and p.stdout.strip():
            info["version"] = p.stdout.strip().splitlines()[0]
    except (OSError, subprocess.SubprocessError):
        pass
    return info


def run_one(solver_name, cmd_template, cnf, timeout_s, mem_mb, nbcore=1, extra=(),
            proof_mode=False):
    """Run one solver on one instance. Returns dict."""
    if solver_name.startswith("ay"):
        # `--no-proof` was hard-coded here, so NO sweep could ever measure a
        # competition configuration -- and the submission always passes --proof
        # (competition/prepare_sat26_submission.sh:784). That blind spot hid
        # three separate defects: the orbitope route and the XOR route are both
        # skipped under a proof surface, and composite symmetry emits
        # certificates an external checker rejects. Pass --proof-mode to measure
        # what a submission would actually score.
        proof_args = [] if proof_mode else ["--no-proof"]
        cmd = [cmd_template, *proof_args, "-t", str(int(timeout_s * 1000)),
               "--memory", str(mem_mb), *extra, cnf]
    elif solver_name.startswith("kissat"):
        if kissat_accepts_options(cmd_template):
            cmd = [cmd_template, "-q", f"--time={int(timeout_s)}", *extra, cnf]
        else:
            cmd = [cmd_template, *extra, cnf]
    else:
        cmd = [cmd_template, *extra, cnf]
    start = time.monotonic()
    verdict = "unknown"
    # External wall-clock guard = solver timeout + grace; SIGKILL the group.
    hard = timeout_s + 20
    try:
        result = run_captured(
            cmd,
            mem_mb,
            timeout_s=hard,
            label=f"sweep.py[{solver_name}]",
            env=dict(os.environ, NBCORE=str(max(1, nbcore))),
        )
        rc = result.returncode
    except Exception as e:
        return {"solver": solver_name, "cnf": os.path.basename(cnf),
                "verdict": "error", "time": 0.0, "rc": None, "err": str(e)}
    elapsed = time.monotonic() - start
    if result.memout:
        verdict = "memout"
    elif result.timed_out:
        verdict = "timeout"
    elif result.cancelled:
        verdict = "cancelled"
    elif result.output_truncated:
        # A solver that ran to completion and exited 10/20 answered, even if its
        # model overflowed our bounded capture — a large SAT witness routinely
        # does. Scoring that as `error` silently deletes solved instances from a
        # sweep (it cost one on the SAT-COMP 2026 sample). Only a truncated
        # stream with no conclusive exit code is unusable.
        verdict = {10: "sat", 20: "unsat"}.get(rc, "error")
    else:
        # Parse only a complete, non-killed stream; fall back to conventional
        # SAT solver exit codes when no status line was emitted.
        for line in result.stdout.splitlines():
            ls = line.strip()
            if ls == "s SATISFIABLE" or ls.endswith(" SATISFIABLE"):
                verdict = "sat"; break
            if ls == "s UNSATISFIABLE" or ls.endswith(" UNSATISFIABLE"):
                verdict = "unsat"; break
        if verdict == "unknown":
            # A solver-reported memout outranks every rc fallback: the SMT-LIB
            # grammar exits 124 (which the bare rc rule read as "timeout") and
            # the --competition grammar exits 0 (which read as "unknown").
            if solver_reported_memout(result):
                verdict = "memout"
            elif rc == 10: verdict = "sat"
            elif rc == 20: verdict = "unsat"
            elif rc == 124: verdict = "timeout"
    row = {"solver": solver_name, "cnf": os.path.basename(cnf),
           "verdict": verdict, "time": round(elapsed, 2), "rc": rc,
           "memout": result.memout, "timed_out": result.timed_out,
           "output_truncated": result.output_truncated,
           "cancelled": result.cancelled}
    wall_ms = solver_reported_wall_ms(result)
    if wall_ms is not None:
        row["solver_wall_ms"] = wall_ms
    return row

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dir")
    ap.add_argument("--list", help="file with one CNF path per line")
    ap.add_argument("--timeout", type=float, default=60.0)
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--mem-mb", type=int, default=4000)
    ap.add_argument("--solver", action="append", default=[], help="name=path")
    ap.add_argument("--solver-extra", action="append", default=[],
                    help="name=ARGS: extra whitespace-split argv inserted before "
                         "the CNF path for that solver (e.g. ay=--competition)")
    ap.add_argument("--proof-mode", action="store_true",
                    help="do NOT pass --no-proof to ay* solvers, so the run matches the "
                         "competition configuration (the submission always writes a proof). "
                         "Pair with a solver wrapper that requests --proof, e.g. "
                         "~/ay-bench/bin/ay-proofmode. The wrapper RETAINS each certificate "
                         "and defers verification to scripts/verify_proof_manifest.py, so "
                         "this sweep's unsat count is PROVISIONAL until that join runs.")
    ap.add_argument("--phantom-memout-frac", type=float, default=0.15,
                    help="a memout/SIGKILL row that dies in under this fraction of "
                         "the timeout is suspect (rss watchdog tripped by CONCURRENT "
                         "machine load, not the instance) and is retried once, "
                         "sequentially, after the sweep; 0 disables")
    ap.add_argument("--out", default="sweep_results.json")
    ap.add_argument("--limit", type=int, default=0)
    args = ap.parse_args()
    if args.mem_mb <= 0:
        ap.error("--mem-mb must be positive so every solver has an enforced envelope")

    solvers = {}
    for s in args.solver:
        name, path = s.split("=", 1)
        solvers[name] = path
    if not solvers:
        solvers["ay"] = "./target/release/ay"
    extras = {}
    for s in args.solver_extra:
        name, argline = s.split("=", 1)
        if name not in solvers:
            ap.error(f"--solver-extra names unknown solver {name!r}")
        extras[name] = tuple(argline.split())

    cnfs = []
    if args.dir:
        cnfs += sorted(glob.glob(os.path.join(args.dir, "*.cnf")))
    if args.list:
        with open(args.list) as f:
            for ln in f:
                ln = ln.strip()
                if ln and not ln.startswith("#"):
                    cnfs.append(ln.split()[0])
    cnfs = [c for c in cnfs if os.path.exists(c)]
    if args.limit:
        cnfs = cnfs[:args.limit]
    # OOM guard: plan aggregate concurrency through the repository admission
    # policy, then enforce the requested per-child budget on EVERY solver.
    # `--memory` is the graceful AY path; rss_watchdog is the hard backstop for
    # Kissat and arbitrary external solvers that have no memory knob.
    warn_concurrent_build()
    requested_workers = args.workers
    plan = plan_solver_resources(args.workers, mem_floor_mb=args.mem_mb,
                                 label="sweep.py")
    args.workers = plan.jobs
    enforced_mem_mb = args.mem_mb
    print(f"instances: {len(cnfs)}  solvers: {list(solvers)}  "
          f"timeout: {args.timeout}s  workers: {args.workers}  "
          f"memory: {enforced_mem_mb}MiB/child NBCORE={plan.nbcore} "
          f"enforcement=rss_watchdog", flush=True)
    if enforced_mem_mb < SATCOMP_MEMORY_LIMIT_MB:
        print(f"  !! memout rows are UNMEASURED, not losses: {enforced_mem_mb} MiB/child "
              f"is below SAT-COMP's {SATCOMP_MEMORY_LIMIT_MB} MiB. Re-run any memout at "
              f"--mem-mb {SATCOMP_MEMORY_LIMIT_MB} before counting it against the solver.",
              flush=True)

    jobs = [(name, path, cnf) for cnf in cnfs for name, path in solvers.items()]
    results = []
    row_jobs = []  # results[i] came from row_jobs[i]; needed to re-run a row
    done = 0
    with cf.ThreadPoolExecutor(max_workers=args.workers) as ex:
        futs = {ex.submit(run_one, n, p, c, args.timeout, enforced_mem_mb,
                          plan.nbcore, extras.get(n, ()), args.proof_mode): (n, p, c)
                for (n, p, c) in jobs}
        for fut in cf.as_completed(futs):
            r = fut.result()
            results.append(r)
            row_jobs.append(futs[fut])
            done += 1
            if done % 10 == 0 or done == len(jobs):
                print(f"  {done}/{len(jobs)} done", flush=True)

    # Phantom-memout guard: concurrent machine load (another session's build)
    # can spike system memory and make the rss watchdog SIGKILL a healthy child
    # within seconds -- a "memout" the instance does not reproduce standalone
    # (2026-08-20: two rows killed at ~9.7s as memout ran the full 300s alone),
    # contaminating paired A/B measurements. A memout / rc=-9 row that died in
    # under --phantom-memout-frac of the timeout is suspect; retry each once
    # sequentially now that the parallel phase is over (quieter machine). A
    # changed verdict replaces the row ("retried_phantom_memout"); a repeat
    # keeps it ("memout_confirmed").
    frac = args.phantom_memout_frac
    suspects = [i for i, r in enumerate(results)
                if frac > 0 and not r.get("cancelled")
                and (r["verdict"] == "memout" or r.get("rc") == -9)
                and r["time"] < frac * args.timeout]
    corrected = 0
    if suspects:
        print(f"retrying {len(suspects)} suspect memout(s) sequentially "
              f"(died <{frac:.0%} of timeout)", flush=True)
    for i in suspects:
        n, p, c = row_jobs[i]
        retry = run_one(n, p, c, args.timeout, enforced_mem_mb, plan.nbcore,
                        extras.get(n, ()), args.proof_mode)
        if retry["verdict"] != results[i]["verdict"]:
            retry["retried_phantom_memout"] = True
            results[i] = retry
            corrected += 1
        else:
            results[i]["memout_confirmed"] = True
    if suspects:
        print(f"{len(suspects)} suspect memouts retried, {corrected} corrected",
              flush=True)

    # Aggregate per solver + cross-check soundness.
    by_inst = {}
    for r in results:
        by_inst.setdefault(r["cnf"], {})[r["solver"]] = r
    summary = {}
    for name in solvers:
        rs = [r for r in results if r["solver"] == name]
        solved = [r for r in rs if r["verdict"] in ("sat", "unsat")]
        par2 = sum(r["time"] if r["verdict"] in ("sat", "unsat") else 2 * args.timeout
                   for r in rs)
        summary[name] = {
            "solved": len(solved),
            "sat": sum(1 for r in rs if r["verdict"] == "sat"),
            "unsat": sum(1 for r in rs if r["verdict"] == "unsat"),
            "timeout": sum(1 for r in rs if r["verdict"] == "timeout"),
            "memout": sum(1 for r in rs if r["verdict"] == "memout"),
            "unknown": sum(1 for r in rs if r["verdict"] == "unknown"),
            "error": sum(1 for r in rs if r["verdict"] == "error"),
            "par2": round(par2, 1),
            "total_time": round(sum(r["time"] for r in rs), 1),
        }
    # Soundness disagreements: two solvers giving definite, opposite answers.
    disagreements = []
    for cnf, d in by_inst.items():
        verdicts = {n: v["verdict"] for n, v in d.items()}
        defs = {n: vv for n, vv in verdicts.items() if vv in ("sat", "unsat")}
        if len(set(defs.values())) > 1:
            disagreements.append({"cnf": cnf, "verdicts": verdicts})

    # Name the configuration in the artifact itself. Three exist and this
    # campaign has repeatedly conflated them: (1) `--competition --no-proof`
    # (upper bound only, never a score), (2) `--competition --proof ...
    # --no-verify-proof` (what the submission runs; its wall time IS the solve
    # time and its solved count is what compares with the official field), and
    # (3) (2) plus an OFFLINE certificate pass (the honest score). A sweep only
    # ever produces (1) or (2); reaching (3) requires
    # scripts/verify_proof_manifest.py score. See that file's header.
    configuration = "competition" if args.proof_mode else "no-proof"
    # Identity of every binary that produced a row, so a future reader can tell
    # a stale result from a current one instead of assuming (see
    # solver_provenance).
    provenance = {name: solver_provenance(path)
                  for name, path in sorted(solvers.items())}
    # An ay* entry is usually the ay-proofmode wrapper, whose own hash says
    # nothing about the solver; record the ay build it dispatches to as well.
    ay_bin = os.environ.get("AY_PROOFMODE_BIN") or "./target/release/ay"
    if any(n.startswith("ay") for n in solvers) and os.path.exists(ay_bin):
        provenance["_ay_binary"] = solver_provenance(ay_bin)
    out = {"timeout_s": args.timeout, "workers": args.workers,
           "solver_configuration": configuration,
           "solver_provenance": provenance,
           "resource_plan": {
               "requested_jobs": requested_workers,
               "jobs": args.workers,
               "memlimit_mb_per_child": enforced_mem_mb,
               "satcomp_memory_limit_mb": SATCOMP_MEMORY_LIMIT_MB,
               # True => this run's `memout` rows say nothing about the solver's
               # competition behaviour and must not be scored as losses.
               "memout_rows_are_unmeasured":
                   enforced_mem_mb < SATCOMP_MEMORY_LIMIT_MB,
               "nbcore_per_child": plan.nbcore,
               "headroom_mb": plan.headroom_mb,
               "enforcement": "exec-stopped + rss-watchdog-zero-grace(all solvers); "
                              "ay --memory; bounded 1MiB/stream capture",
           },
           "n_instances": len(cnfs), "summary": summary,
           "disagreements": disagreements, "results": results}
    with open(args.out, "w") as f:
        json.dump(out, f, indent=2)

    print("\n=== SUMMARY ===", flush=True)
    for name, s in summary.items():
        print(f"{name:10s} solved={s['solved']:3d} (sat={s['sat']} unsat={s['unsat']}) "
              f"timeout={s['timeout']} memout={s['memout']} "
              f"unknown={s['unknown']} err={s['error']} "
              f"PAR2={s['par2']:.0f}", flush=True)
    if disagreements:
        print(f"\n*** {len(disagreements)} SOUNDNESS DISAGREEMENTS ***", flush=True)
        for d in disagreements:
            print(f"  {d['cnf']}: {d['verdicts']}", flush=True)
    else:
        print("\nno soundness disagreements", flush=True)
    if args.proof_mode:
        print("\n--- configuration (2): --competition + an explicit proof, NOT "
              "re-checked in-process ---", flush=True)
        print("The count above is SOLVED (competition mode) and is PROVISIONAL "
              "as a score: certificates", flush=True)
        print("are verified OFFLINE, outside the solve budget. Drain and join "
              "before quoting a standing:", flush=True)
        print("  scripts/verify_proof_manifest.py drain", flush=True)
        print(f"  scripts/verify_proof_manifest.py score --sweep {args.out}",
              flush=True)
    print(f"\nwrote {args.out}", flush=True)

if __name__ == "__main__":
    main()

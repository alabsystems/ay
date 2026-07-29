#!/usr/bin/env python3
"""Streaming MaxSAT bench.

Differs from mbench.py in the one way that matters for multi-hour runs: every
completed instance is appended to the output as its own JSON line, flushed and
fsync'd immediately.  A run that is killed at any point still leaves every
result it had finished behind, and can be resumed by re-invoking with the same
output path (already-recorded instances are skipped).

Usage:
  mbench_stream.py <list-file> <bench-dir> <timeout> <jobs> <field-csv> <out.jsonl> [K=V ...]

<list-file> is one instance basename per line, or '-' for the whole directory.
"""
import sys, os, csv, subprocess, concurrent.futures as cf, json, time

BIN = os.environ.get("MBENCH_BIN", "target/release/ay")


def run_one(args):
    inst, path, tmo, opt, env_extra = args
    env = dict(os.environ)
    env.update(env_extra or {})
    t0 = time.monotonic()
    try:
        p = subprocess.run(
            [BIN, "maxsat", "solve", "--timeout", str(tmo), path],
            capture_output=True, text=True, timeout=tmo + 120, env=env,
        )
        out = p.stdout
    except Exception as e:
        return {"instance": inst, "status": "ERROR", "cost": None,
                "flag": str(e)[:80], "sec": round(time.monotonic() - t0, 2)}
    el = round(time.monotonic() - t0, 2)
    status, cost = "UNKNOWN", None
    for line in out.splitlines():
        if line.startswith("s "):
            status = line[2:].strip()
        elif line.startswith("o "):
            try:
                cost = int(line[2:].strip())
            except ValueError:
                pass
    solved = status in ("OPTIMUM FOUND", "OPTIMUM", "OPTIMUM_FOUND")
    wrong = solved and opt not in (None, "") and cost is not None and str(cost) != str(opt)
    return {"instance": inst, "status": "OPTIMUM" if solved else status,
            "cost": cost, "opt": opt, "flag": "WRONG" if wrong else "", "sec": el}


def main():
    listf, d, tmo, jobs, field, outp = sys.argv[1:7]
    tmo, jobs = int(tmo), int(jobs)
    env_extra = {}
    for kv in sys.argv[7:]:
        k, _, v = kv.partition("=")
        env_extra[k] = v

    opt = {}
    for r in csv.DictReader(open(field)):
        opt[r["instance"]] = r.get("o_value")

    if listf == "-":
        insts = sorted(f for f in os.listdir(d) if f.endswith(".wcnf"))
    else:
        insts = [l.strip() for l in open(listf) if l.strip()]

    done_already = set()
    if os.path.exists(outp):
        for line in open(outp):
            line = line.strip()
            if not line:
                continue
            try:
                done_already.add(json.loads(line)["instance"])
            except Exception:
                pass
    todo = [i for i in insts if i not in done_already]
    print(f"[{time.strftime('%H:%M:%S')}] {len(todo)} to run "
          f"({len(done_already)} already recorded), timeout={tmo}s jobs={jobs}", flush=True)

    tasks = [(i, os.path.join(d, i), tmo, opt.get(i), env_extra) for i in todo]
    out = open(outp, "a", buffering=1)
    n = 0
    with cf.ThreadPoolExecutor(max_workers=jobs) as ex:
        for r in ex.map(run_one, tasks):
            out.write(json.dumps(r) + "\n")
            out.flush()
            os.fsync(out.fileno())
            n += 1
            print(f"[{time.strftime('%H:%M:%S')}] {n}/{len(tasks)} "
                  f"{r['status']:8s} {r['sec']:8.1f}s {r['flag']:5s} {r['instance'][:70]}",
                  flush=True)
    out.close()
    print(f"[{time.strftime('%H:%M:%S')}] DONE {n} instances", flush=True)


if __name__ == "__main__":
    main()

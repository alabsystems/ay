#!/usr/bin/env python3
# ay-script: milp-compare
"""compare.py — ay-milp vs HiGHS verdict agreement on the downstream optimization consumer's real .milp corpus.

For every .milp instance: convert to exact MPS, solve with both ay's mps_solve
and the HiGHS CLI, normalise each verdict to SAT / UNSAT / OTHER, and report
agreement. A SAT-vs-UNSAT split between the two solvers is a hard correctness
disagreement (gate G0), printed and counted separately from mere OTHER/unknown.
"""
import argparse
import glob
import os
import re
import subprocess
import sys
import time

import milp2mps  # local

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

_ap = argparse.ArgumentParser(description=__doc__)
_ap.add_argument("corpus", help="directory of .milp instances")
_ap.add_argument("timeout", nargs="?", type=float, default=30.0,
                 help="per-solver wall timeout in seconds (default 30)")
_ap.add_argument("--ay-bin",
                 default=os.environ.get(
                     "AY_BIN",
                     os.path.join(REPO, "target/release/examples/mps_solve")),
                 help="ay mps_solve binary (env: AY_BIN)")
_args = _ap.parse_args()

AY = _args.ay_bin
TMO = _args.timeout
CORPUS = _args.corpus
TMP = "/tmp/cmp_mps"
os.makedirs(TMP, exist_ok=True)


def classify_ay(line):
    tok = line.split()
    st = tok[0] if tok else "EMPTY"
    if st in ("OPTIMAL", "FEASIBLE"):
        return "SAT", (float(tok[1]) if len(tok) > 1 and tok[1] not in ("-",) else None)
    if st == "INFEASIBLE":
        return "UNSAT", None
    return "OTHER:" + st, None


def run_ay(mps):
    t0 = time.monotonic()
    try:
        r = subprocess.run([AY, mps, str(TMO)], capture_output=True, text=True, timeout=TMO + 30)
    except subprocess.TimeoutExpired:
        return "OTHER:TIMEOUT", None, TMO + 30
    dt = time.monotonic() - t0
    out = (r.stdout or "").strip().splitlines()
    if not out:
        return "OTHER:CRASH", None, dt
    v, val = classify_ay(out[-1])
    return v, val, dt


def run_highs(mps):
    t0 = time.monotonic()
    try:
        r = subprocess.run(["highs", "--time_limit", str(TMO), mps],
                           capture_output=True, text=True, timeout=TMO + 30)
    except subprocess.TimeoutExpired:
        return "OTHER:TIMEOUT", None, TMO + 30
    dt = time.monotonic() - t0
    txt = r.stdout or ""
    m = re.search(r"^\s*Model status\s*:?\s*(.+)$", txt, re.M) or re.search(r"^\s*Status\s+(.+)$", txt, re.M)
    st = m.group(1).strip() if m else "?"
    ob = re.search(r"^\s*Objective\s+value\s*:?\s*(\S+)$", txt, re.M) or re.search(r"^\s*Primal bound\s+(\S+)$", txt, re.M)
    val = None
    if ob:
        try:
            val = float(ob.group(1))
        except ValueError:
            val = None
    if st == "Optimal":
        return "SAT", val, dt
    if "Infeasible" in st:
        return "UNSAT", None, dt
    if "Unbounded" in st:
        return "OTHER:UNBOUNDED", None, dt
    return "OTHER:" + st, val, dt


def main():
    files = sorted(glob.glob(os.path.join(CORPUS, "*.milp")))
    agree_sat = agree_unsat = 0
    disagree = []
    other = []
    ay_t = hi_t = 0.0
    n = 0
    for f in files:
        n += 1
        stem = os.path.splitext(os.path.basename(f))[0]
        mps = os.path.join(TMP, stem + ".mps")
        try:
            cols, rows = milp2mps.parse(f)
            with open(mps, "w") as fh:
                fh.write(milp2mps.emit(cols, rows, name=stem[:8]))
        except Exception as e:  # noqa
            other.append((stem, "CONVERT_FAIL", str(e)[:60]))
            continue
        a_v, a_val, a_t = run_ay(mps)
        h_v, h_val, h_t = run_highs(mps)
        ay_t += a_t
        hi_t += h_t
        base_a = a_v.split(":")[0]
        base_h = h_v.split(":")[0]
        if base_a == "SAT" and base_h == "SAT":
            agree_sat += 1
        elif base_a == "UNSAT" and base_h == "UNSAT":
            agree_unsat += 1
        elif base_a in ("SAT", "UNSAT") and base_h in ("SAT", "UNSAT") and base_a != base_h:
            disagree.append((stem, a_v, h_v))
        else:
            other.append((stem, a_v, h_v))
    print("=" * 72)
    print(f"instances: {n}   ay total {ay_t:.2f}s   highs total {hi_t:.2f}s")
    print(f"AGREE sat={agree_sat}  AGREE unsat={agree_unsat}  "
          f"total agree={agree_sat + agree_unsat}/{n}")
    print(f"hard disagreements (SAT vs UNSAT): {len(disagree)}")
    for stem, a, h in disagree:
        print(f"  !! {stem}: ay={a} highs={h}")
    if other:
        print(f"non-verdict rows (one side OTHER): {len(other)}")
        for stem, a, h in other[:20]:
            print(f"   ? {stem}: ay={a} highs={h}")
    print("=" * 72)
    return 1 if disagree else 0


if __name__ == "__main__":
    sys.exit(main())

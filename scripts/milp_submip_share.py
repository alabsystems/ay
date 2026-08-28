#!/usr/bin/env python3
# ay-script: milp-submip-share
"""milp_submip_share.py — how much of `nodes_explored()` is heuristic sub-MIP?

WHY THIS EXISTS. `ay_milp::nodes_explored()` is process-global and CUMULATIVE
across nested solves, so a RENS/RINS/ball sub-MIP's own tree lands in the same
number as the proof tree. Gurobi's `Model.NodeCount` does not work that way — it
reports the main branch-and-bound tree and excludes the sub-MIPs its heuristics
run. Every ay-vs-Gurobi node comparison in this repo has therefore been comparing
two different quantities, and the bias runs in BOTH directions at once:

  * ay's node count is INFLATED, so recorded tree-quality gaps (ay nodes / Gurobi
    nodes) are too large;
  * ay's per-node cost is DEFLATED by exactly the same factor, so recorded
    throughput gaps (ay us/node / Gurobi us/node) are too small.

Both corrections are the single per-instance number this script measures:

    r = root_nodes / total_nodes  in (0, 1]

`bab.rs`'s `SUBMIP_NODES_EXPLORED` supplies it; `examples/mps_solve` prints it on
STDERR as `nodes: total=T root=R submip=S`. STDERR on purpose —
`scripts/milp_node_gate.py` reads this example's node count as stdout `line[-1]`,
so a fifth stdout field would silently re-point all twenty ratchet pins.

USAGE
  python3 scripts/milp_submip_share.py --secs 20 --reps 3 \
      --solver head=target-t2/release/examples/mps_solve \
      --solver july=/path/to/other/mps_solve \
      --out the development design notes

Two solvers are INTERLEAVED per instance (A,B on instance 1, then A,B on
instance 2, ...), never run in blocks: a block confounds the arm with whatever
the machine was doing during that block. Reps are round-robin PASSES over the
whole corpus for the same reason. Every rep is kept in the output, with the
1-minute load average at the time it ran, because a single run is not evidence
on a 14-CPU box shared with other agents.

WHY TWO ARMS ARE USEFUL HERE. the development design notes was measured at
`f6b5028f6` (2026-07-26). Correcting its recorded ratios needs the share `r`
of THAT engine, not of today's; today's share is the one that describes what
ships. Measuring both in one interleaved pass gets both under the same load.
"""
from __future__ import annotations

import argparse
import json
import os
import pathlib
import re
import subprocess
import sys
import time

NODES_RE = re.compile(r"^nodes: total=(\d+) root=(\d+) submip=(\d+)\s*$", re.M)


def load_corpus(manifest: pathlib.Path, tier: str | None, only: list[str],
                limit: int) -> list[dict]:
    ins = json.loads(manifest.read_text())["instances"]
    out = []
    for name, e in ins.items():
        if tier and e.get("tier") != tier:
            continue
        if only and name not in only:
            continue
        out.append(dict(e, name=name))
    out.sort(key=lambda e: (e.get("cols") or 0, e["name"]))
    return out[:limit] if limit else out


def load1() -> float:
    return os.getloadavg()[0]


def run_one(solver: str, inst: dict, secs: float) -> dict:
    """One ay solve. stdout last line is `status value wall nodes`; the
    comparable split rides stderr."""
    t0 = time.monotonic()
    lo = load1()
    try:
        r = subprocess.run([solver, inst["file"], str(secs)], capture_output=True,
                           text=True, timeout=secs * 3 + 120)
    except subprocess.TimeoutExpired:
        return {"status": "HARNESS_TIMEOUT", "t": secs * 3 + 120, "load1": lo}
    wall = time.monotonic() - t0
    rec: dict = {"t": round(wall, 4), "load1": round(lo, 2),
                 "load1_end": round(load1(), 2), "rc": r.returncode}
    out = (r.stdout or "").strip().splitlines()
    if not out:
        rec["status"] = "NO_OUTPUT"
        rec["raw"] = ((r.stdout or "") + (r.stderr or ""))[-300:]
        return rec
    f = out[-1].split()
    rec["status"] = f[0]
    if len(f) > 1 and f[1] != "-":
        try:
            rec["obj"] = float(f[1])
        except ValueError:
            pass
    # Field 3 is the FROZEN cumulative counter, exactly as every prior campaign
    # recorded it. Parsed here from the same position so this script's `total`
    # is comparable with the development design notes field-for-field.
    if len(f) > 3:
        try:
            rec["nodes"] = int(f[3])
        except ValueError:
            pass
    m = NODES_RE.search(r.stderr or "")
    if m:
        tot, root, sub = (int(x) for x in m.groups())
        rec["total_nodes"], rec["root_nodes"], rec["submip_nodes"] = tot, root, sub
        # A parse that disagrees with stdout means the two instruments came
        # apart; record it rather than averaging it away.
        if rec.get("nodes") is not None and rec["nodes"] != tot:
            rec["MISMATCH"] = [rec["nodes"], tot]
    else:
        rec["NO_SPLIT"] = True
    return rec


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--manifest", default=str(pathlib.Path.home() / "ay-bench" / "milp" / "manifest.json"))
    ap.add_argument("--solver", action="append", required=True,
                    help="LABEL=PATH; repeat to interleave arms")
    ap.add_argument("--secs", type=float, default=20.0)
    ap.add_argument("--reps", type=int, default=1)
    ap.add_argument("--tier", default="gurobi")
    ap.add_argument("--only", action="append", default=[])
    ap.add_argument("--limit", type=int, default=0)
    ap.add_argument("--out", required=True)
    args = ap.parse_args()

    corpus = load_corpus(pathlib.Path(args.manifest), args.tier or None,
                         args.only, args.limit)
    arms = []
    for spec in args.solver:
        label, _, path = spec.partition("=")
        if not path:
            label, path = "ay", spec
        arms.append((label, os.path.abspath(path)))
    print(f"[submip-share] {len(corpus)} instances x {args.reps} reps @ {args.secs}s, "
          f"arms={[a[0] for a in arms]}", flush=True)
    for label, path in arms:
        h = subprocess.run(["shasum", "-a", "256", path], capture_output=True, text=True)
        print(f"[submip-share]   {label}: {h.stdout.strip()}", flush=True)
    runs: dict[str, dict[str, list[dict]]] = {
        c["name"]: {label: [] for label, _ in arms} for c in corpus}

    def dump(indent=None):
        with open(args.out, "w") as fh:
            json.dump({"mode": "submip-share", "secs": args.secs, "reps": args.reps,
                       "arms": {label: path for label, path in arms}, "runs": runs},
                      fh, indent=indent)

    for rep in range(args.reps):
        for i, inst in enumerate(corpus):
            for label, path in arms:
                rec = run_one(path, inst, args.secs)
                rec["rep"] = rep
                runs[inst["name"]][label].append(rec)
                sh = ("%.4f" % (rec["root_nodes"] / rec["total_nodes"])
                      if rec.get("total_nodes") else "-")
                print(f"  r{rep} {i + 1:3d}/{len(corpus)} {label:6s} {inst['name']:26s} "
                      f"{rec.get('status', '?'):9s} t={rec.get('t', 0):6.1f}s "
                      f"total={rec.get('total_nodes')} root={rec.get('root_nodes')} "
                      f"submip={rec.get('submip_nodes')} root_share={sh} "
                      f"load1={rec.get('load1')}", flush=True)
            dump()
    dump(indent=1)
    print(f"[submip-share] wrote {args.out}", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())

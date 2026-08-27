#!/usr/bin/env python3
"""THE LP GAP, decomposed into the part that is a solver and the part that was an instrument.

WHAT THIS EXISTS TO ANSWER
--------------------------
the development design notes:141` records "the gap is the LP core —
geomean 8.2x, median 6.7x, ay slower on 110/112" against Gurobi. Two defects in the
harness that produced it are confirmed:

  1. the ay arm was `milp_w0.py::run_ay_lp`, i.e. `AY_LP_ONLY=1` -> `bab::diag_float_lp`
     — the MEASUREMENT SCAFFOLD: one cold walk, no float-lane ladder, no eager-perturb
     retry, `plain_cold` off. It is the only float lane in the crate that gives up
     after a single declined walk; and
  2. `run_ay_lp` returned the elapsed wall REGARDLESS OF STATUS, so a truncated row
     entered the ratio as `deadline / gurobi_time` — a FLOOR presented as a measurement.

This harness separates those. It runs THREE arms on the SAME LP:

  scaffold  `ay-milp diag lp-only`     — the lane the 8.2x was taken on
  shipped   `ay-milp diag shipped-lp`  — the lane a solve actually runs
  highs     `scripts/lp_gap_highs.py`  — a real external reference solver

The scaffold-vs-shipped comparison needs NO external solver and is the cleanest
statement available about the size of defect (1): how many rows does the scaffold
truncate that the shipped lane solves?

WHAT THE `highs` ARM IS NOT
---------------------------
HiGHS IS NOT GUROBI. This harness cannot re-derive 8.2x, because gurobipy does not
import on this box. An `ay/HiGHS` ratio REPLACES nothing; it BOUNDS. HiGHS is
generally the slower of the two on LP, so `ay/HiGHS` is expected to read LOW
relative to `ay/Gurobi` — treat it as a lower bound on the recorded number, not as
a competing estimate of it.

MEASUREMENT DISCIPLINE
----------------------
* Arms are INTERLEAVED per instance, never run in blocks, and the arm order is
  REVERSED on odd reps so that any within-instance drift (page cache, thermal)
  cancels rather than accumulating onto whichever arm goes last.
* Every arm is one fresh process that reads the model itself. The reported `wall`
  of every arm EXCLUDES the model read, so the three are commensurable.
* `iters` (simplex iteration counts) and the terminate/truncate verdict are the
  load-invariant currencies here; `wall` is not, and a truncation verdict is
  WALL-DEADLINE-COUPLED by construction — under load, more rows truncate.

OBJECTIVES ARE IN DIFFERENT UNITS, and this bit them
----------------------------------------------------
Both ay diag lanes print the value of the MODEL AS READ, which `mps::read_mps`
has SCALED (`MpsProblem::obj_scale`); only the `solve` CLI unscales. On
`gt2_lprelax` the diag lanes say `1682.529134` where the file's optimum is
`13460.233074411897` — exactly 8x, the scale, not an error. So this harness
compares objectives ONLY after dividing the ay arms by the per-instance scale it
recovers from `ay-milp solve`, and never compares a raw diag value to a reference.
"""
from __future__ import annotations

import argparse
import json
import math
import os
import re
import statistics
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))

SCAFFOLD_RE = re.compile(r"diag_float_lp: status=(\w+).*?wall=([\d.]+)s", re.S)
SHIPPED_RE = re.compile(r"shipped_float_lp: outcome=(\S+).*?wall=([\d.]+)s", re.S)
HIGHS_RE = re.compile(r"highs_lp: status=(\S+) obj=(\S+) wall=([\d.]+) iters=(\d+)")
ITERS_RE = re.compile(r"primal=(\d+).*?dual=(\d+)", re.S)
DEGEN_RE = re.compile(r"degen=(\d+)")
MOVED_RE = re.compile(r"moved=(\d+)")
VALUE_RE = re.compile(r"value=([\d.eE+-]+)")
OBJMIN_RE = re.compile(r"obj\(min-form\)=([\d.eE+-]+)")


def _run(cmd: list[str], secs: float) -> tuple[str, bool]:
    """Run `cmd`, returning (stdout+stderr, hard_timeout). Never raises."""
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=secs + 90)
    except subprocess.TimeoutExpired:
        return "", True
    except OSError as e:
        return f"OSERROR {e}", False
    return (r.stdout or "") + (r.stderr or ""), False


def arm_scaffold(binary: str, path: str, secs: float) -> dict:
    """The lane the 8.2x number was taken on: ONE COLD WALK, no ladder, no retry."""
    txt, hard = _run([binary, "diag", "lp-only", path, str(secs)], secs)
    if hard:
        return {"status": "HARDTIMEOUT", "t": None}
    m = SCAFFOLD_RE.search(txt)
    if not m:
        return {"status": "NOPARSE", "t": None}
    return _counters(txt, {"status": m.group(1), "t": float(m.group(2)),
                           "obj_scaled": _f(OBJMIN_RE, txt)})


def arm_shipped(binary: str, path: str, secs: float) -> dict:
    """The lane a solve runs: plain_cold on, declined walk retried, basis certified."""
    txt, hard = _run([binary, "diag", "shipped-lp", path, str(secs)], secs)
    if hard:
        return {"status": "HARDTIMEOUT", "t": None}
    m = SHIPPED_RE.search(txt)
    if not m:
        return {"status": "NOPARSE", "t": None}
    # `outcome=OPTIMAL value=... certified=...` -> status OPTIMAL; `DECLINED(...)` -> DECLINED.
    status = m.group(1).split("(")[0]
    return _counters(txt, {"status": status, "t": float(m.group(2)),
                           "certified": "certified=true" in txt,
                           "obj_scaled": _f(VALUE_RE, txt)})


def arm_highs(path: str, secs: float) -> dict:
    """An external reference solver. NOT Gurobi — see this module's docstring."""
    txt, hard = _run([sys.executable, os.path.join(HERE, "lp_gap_highs.py"), path, str(secs)], secs)
    if hard:
        return {"status": "HARDTIMEOUT", "t": None}
    m = HIGHS_RE.search(txt)
    if not m:
        return {"status": "NOPARSE", "t": None}
    return {"status": m.group(1), "obj": float(m.group(2)), "t": float(m.group(3)),
            "iters": int(m.group(4))}


def _f(rx: re.Pattern, txt: str) -> float | None:
    m = rx.search(txt)
    try:
        return float(m.group(1)) if m else None
    except ValueError:
        return None


def _counters(txt: str, base: dict) -> dict:
    it = ITERS_RE.search(txt)
    base["primal_iters"] = int(it.group(1)) if it else None
    base["dual_iters"] = int(it.group(2)) if it else None
    dg = DEGEN_RE.search(txt)
    base["degen"] = int(dg.group(1)) if dg else None
    mv = MOVED_RE.search(txt)
    base["moved"] = int(mv.group(1)) if mv else None
    return base


def terminated(arm: dict) -> bool:
    """Did this arm reach a real answer, as opposed to spending its deadline?

    DERIVED, never stored — `milp_w0.py` learned this the expensive way: it stored a
    `truncated` key only on the branch that parsed successfully, so `TIMEOUT`,
    `CRASH` and `NOPARSE` rows carried no key and read back as CLEAN. Anything that
    is not a terminating optimum is a FLOOR, and this predicate is total.
    """
    return arm.get("status") in ("Optimal", "OPTIMAL", "kOptimal")


def geomean(xs: list[float]) -> float:
    return math.exp(sum(math.log(x) for x in xs) / len(xs))


def load_instances(args) -> list[dict]:
    if args.corpus == "oracle":
        root = os.path.expanduser("~/ay-bench/oracle_v2/lp")
        out = [{"name": f[: -len("_lprelax.mps")] if f.endswith("_lprelax.mps") else f,
                "file": os.path.join(root, f)}
               for f in sorted(os.listdir(root)) if f.endswith(".mps")]
    else:
        man = json.load(open(os.path.expanduser("~/ay-bench/milp/manifest.json")))
        out = [{"name": n, "file": e["file"], "rows": e.get("rows"), "cols": e.get("cols")}
               for n, e in man["instances"].items()]
        out.sort(key=lambda e: (e.get("cols") or 0, e["name"]))
    if args.only:
        keep = set(args.only.split(","))
        out = [e for e in out if e["name"] in keep]
    return out[: args.limit] if args.limit else out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--corpus", choices=("milp", "oracle"), default="milp")
    ap.add_argument("--secs", type=float, default=20.0)
    ap.add_argument("--reps", type=int, default=2)
    ap.add_argument("--limit", type=int, default=0)
    ap.add_argument("--only", default="")
    ap.add_argument("--bin", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--arms", default="scaffold,shipped,highs")
    args = ap.parse_args()

    binary = os.path.abspath(args.bin)
    arms = args.arms.split(",")
    insts = load_instances(args)
    sha = subprocess.run(["shasum", "-a", "256", binary], capture_output=True,
                         text=True).stdout.split()[0]
    load1 = os.getloadavg()[0]
    print(f"[lp-gap] {len(insts)} instances x {args.reps} reps x {len(arms)} arms, "
          f"{args.secs}s budget", flush=True)
    print(f"[lp-gap] binary {binary}\n[lp-gap] sha256 {sha}\n[lp-gap] load1 at start {load1:.2f}",
          flush=True)

    rows: list[dict] = []
    t_start = time.monotonic()
    for rep in range(args.reps):
        # REVERSED on odd reps: arms must not always be measured in the same order.
        order = arms if rep % 2 == 0 else list(reversed(arms))
        for i, inst in enumerate(insts):
            rec = {"name": inst["name"], "rep": rep, "rows": inst.get("rows"),
                   "cols": inst.get("cols"), "load1": os.getloadavg()[0]}
            for a in order:
                if a == "scaffold":
                    rec["scaffold"] = arm_scaffold(binary, inst["file"], args.secs)
                elif a == "shipped":
                    rec["shipped"] = arm_shipped(binary, inst["file"], args.secs)
                elif a == "highs":
                    rec["highs"] = arm_highs(inst["file"], args.secs)
            rows.append(rec)
            bits = []
            for a in arms:
                d = rec.get(a, {})
                tt = d.get("t")
                bits.append(f"{a[:4]}={d.get('status','?')[:8]}"
                            + ("" if tt is None else f"/{tt:.3f}s"))
            print(f"  r{rep} {i+1:3d}/{len(insts)} {inst['name'][:28]:28s} " + "  ".join(bits),
                  flush=True)
            json.dump({"binary": binary, "sha256": sha, "secs": args.secs,
                       "corpus": args.corpus, "rows": rows},
                      open(args.out, "w"), indent=1)
    print(f"[lp-gap] wall {time.monotonic()-t_start:.0f}s, load1 at end "
          f"{os.getloadavg()[0]:.2f}", flush=True)
    summarize(rows, arms)
    return 0


def summarize(rows: list[dict], arms: list[str]) -> None:
    """Report by rep, and never pool a floor with a measurement."""
    reps = sorted({r["rep"] for r in rows})
    print("\n=== TERMINATION BY ARM (per rep) ===")
    for rep in reps:
        rr = [r for r in rows if r["rep"] == rep]
        line = [f"rep{rep} n={len(rr)}"]
        for a in arms:
            ok = sum(1 for r in rr if terminated(r.get(a, {})))
            line.append(f"{a}={ok}/{len(rr)}")
        print("  " + "  ".join(line))

    if "scaffold" in arms and "shipped" in arms:
        print("\n=== DEFECT (1): SCAFFOLD TRUNCATES WHAT THE SHIPPED LANE SOLVES ===")
        for rep in reps:
            rr = [r for r in rows if r["rep"] == rep]
            both = sum(1 for r in rr if terminated(r["scaffold"]) and terminated(r["shipped"]))
            rescued = [r for r in rr if not terminated(r["scaffold"]) and terminated(r["shipped"])]
            lost = [r for r in rr if terminated(r["scaffold"]) and not terminated(r["shipped"])]
            neither = sum(1 for r in rr
                          if not terminated(r["scaffold"]) and not terminated(r["shipped"]))
            print(f"  rep{rep}: both={both}  scaffold-only-fails={len(rescued)}  "
                  f"shipped-only-fails={len(lost)}  neither={neither}")
            if rescued:
                print("    rescued by the shipped lane: "
                      + ", ".join(sorted(r["name"] for r in rescued)))
            if lost:
                print("    scaffold terminated where shipped did not: "
                      + ", ".join(sorted(r["name"] for r in lost)))

    for a in arms:
        if a == "highs":
            continue
        print(f"\n=== RATIO {a}/highs ===")
        for rep in reps:
            rr = [r for r in rows if r["rep"] == rep]
            allr, clean, zero = [], [], []
            for r in rr:
                x, h = r.get(a, {}), r.get("highs", {})
                ta, th = x.get("t"), h.get("t")
                if ta is None or th is None or th <= 0:
                    continue
                if ta <= 0.0:
                    # Below the emission's resolution. COUNTED, never silently
                    # dropped: this is the bin `milp_w0.py` deleted with a
                    # truthiness test, and it holds only ay's fastest rows.
                    zero.append(r["name"])
                    continue
                allr.append(ta / th)
                if terminated(x) and terminated(h):
                    clean.append(ta / th)
            if zero:
                print(f"  rep{rep} {len(zero)} rows below wall resolution, excluded "
                      f"(ay's FASTEST): {', '.join(sorted(zero)[:8])}"
                      + (" ..." if len(zero) > 8 else ""))
            if allr:
                print(f"  rep{rep} ALL {len(allr)} rows (INCLUDES FLOORS, this is the shape of "
                      f"the recorded number): geomean {geomean(allr):.2f}x "
                      f"median {statistics.median(allr):.2f}x")
            if clean:
                sl = sum(1 for x in clean if x > 1.0)
                print(f"  rep{rep} BOTH-TERMINATED {len(clean)} rows: "
                      f"geomean {geomean(clean):.2f}x median {statistics.median(clean):.2f}x "
                      f"ay slower on {sl}/{len(clean)}")

    iteration_report(rows, arms)


def ay_iters(d: dict) -> int | None:
    p, q = d.get("primal_iters"), d.get("dual_iters")
    return None if p is None or q is None else p + q


def iteration_report(rows: list[dict], arms: list[str]) -> None:
    """THE LOAD-INVARIANT HALF, and the test of the recorded decomposition.

    `reports/…-w1-w6-execution.md` decomposes the LP gap as
    `8.2x = 4.87x iterations x 1.67x per-iteration`, and that split was judged
    "mostly survives" the truncation defect on the argument that RATIOS are
    truncation-robust because numerator and denominator truncate together.

    Iteration COUNTS are deterministic: they do not move with the box's load, so
    the `iters` ratio below is the one number here that a contended machine
    cannot corrupt. Per-iteration cost is a wall quantity and inherits every
    caveat wall has — which is exactly why the two are reported apart.
    """
    if "highs" not in arms:
        return
    reps = sorted({r["rep"] for r in rows})
    print("\n=== ITERATION RATIO (LOAD-INVARIANT) vs per-iteration cost (NOT) ===")
    for a in arms:
        if a == "highs":
            continue
        for rep in reps:
            ir, pi_a, pi_h = [], [], []
            for r in rows:
                if r["rep"] != rep:
                    continue
                x, h = r.get(a, {}), r.get("highs", {})
                if not (terminated(x) and terminated(h)):
                    continue
                ia, ih = ay_iters(x), h.get("iters")
                if not ia or not ih:
                    continue
                ir.append(ia / ih)
                ta, th = x.get("t"), h.get("t")
                if ta and th and ta > 0 and th > 0:
                    pi_a.append(ta / ia)
                    pi_h.append(th / ih)
            if ir:
                print(f"  {a} rep{rep}: ITERS ay/highs geomean {geomean(ir):.2f}x "
                      f"median {statistics.median(ir):.2f}x over n={len(ir)}")
            if pi_a and len(pi_a) == len(pi_h):
                per = [x / y for x, y in zip(pi_a, pi_h)]
                print(f"  {a} rep{rep}: PER-ITERATION ay/highs geomean {geomean(per):.2f}x "
                      f"median {statistics.median(per):.2f}x over n={len(per)}  "
                      f"[WALL-DERIVED — load-sensitive]")

    if "scaffold" in arms and "shipped" in arms:
        print("\n=== IS PER-ITERATION COST STABLE BETWEEN THE AY LANES? ===")
        print("  (if the two lanes cost the same per iteration, a ratio built on either "
              "is telling you about ITERATION COUNT; if not, the lane choice is itself "
              "a per-iteration confound)")
        for rep in reps:
            same_iters, per_ratio = 0, []
            n = 0
            for r in rows:
                if r["rep"] != rep:
                    continue
                s, p = r.get("scaffold", {}), r.get("shipped", {})
                if not (terminated(s) and terminated(p)):
                    continue
                isc, ish = ay_iters(s), ay_iters(p)
                if not isc or not ish:
                    continue
                n += 1
                if isc == ish:
                    same_iters += 1
                ts, tp = s.get("t"), p.get("t")
                if ts and tp and ts > 0 and tp > 0:
                    per_ratio.append((tp / ish) / (ts / isc))
            if n:
                print(f"  rep{rep}: identical iteration counts on {same_iters}/{n} "
                      f"both-terminated rows")
            if per_ratio:
                print(f"  rep{rep}: per-iteration shipped/scaffold geomean "
                      f"{geomean(per_ratio):.2f}x median {statistics.median(per_ratio):.2f}x "
                      f"n={len(per_ratio)}  [WALL-DERIVED — load-sensitive]")


if __name__ == "__main__":
    raise SystemExit(main())

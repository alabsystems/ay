#!/usr/bin/env python3
# ay-script: mzn-score-ay
"""Score an AY results vector against the real MiniZinc Challenge 2025 field.

Appends AY as a solver and reports its total pairwise-Borda score and rank
within a category (fd/free/par), using the validated scorer in score.py.
Prints both the OFFICIAL score (time-split ties) and a QUALITY-ONLY score
(ties collapsed to 0.5) — the latter removes the hardware-relative time
confound and is the honest lower bound on solve quality.

Usage: score_ay.py <ay-run.json> [fd|free|par] [results-2025.json]
"""
import collections, json, os, sys
from score import pair_score, inst_kind_map

REPO = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
DEFAULT_RESULTS = f"{REPO}/benchmarks/minizinc/challenge-2025/results-2025.json"

def ay_vectors(ay_path):
    d = json.load(open(ay_path))
    out = {}
    for gi, r in enumerate(d["results"]):
        st = r["status"]
        if st == "UNSAT":  # proven infeasible on a feasible instance == no valid answer
            st = "ERR"
        out[gi] = (st, r.get("objective"), r.get("time_ms", 0))
    return out

def category_indices(d, cat):
    return [i for i, v in enumerate(d[{"fd": "fd_solvers", "free": "free_solvers", "par": "par_solvers"}[cat]]) if v]

def score(d, ay, cat, quality_only=False):
    ik = inst_kind_map(d)
    sv, R, O, T, S = d["solvers"], d["results"], d["objectives"], d["times"], d["scores"]
    ni = len(R[0]); comp = category_indices(d, cat); AY = "AY"; members = comp + [AY]

    def cell(a, b, i):
        if a == AY:
            s1, _ = pair_score(ik[i], *ay[i], R[b][i], O[b][i], T[b][i]); return s1
        if b == AY:
            _, s2 = pair_score(ik[i], R[a][i], O[a][i], T[a][i], *ay[i]); return s2
        return S[a][b][i]

    totals = {m: 0.0 for m in members}
    for i in range(ni):
        for a in members:
            for b in members:
                if a == b: continue
                v = cell(a, b, i)
                if quality_only and 0.0 < v < 1.0:
                    v = 0.5
                totals[a] += v
    ranked = sorted(totals.items(), key=lambda kv: -kv[1])
    name = {i: sv[i] for i in comp}; name[AY] = "*** AY ***"
    return ranked, name

def main():
    ay_path = sys.argv[1]
    cat = sys.argv[2] if len(sys.argv) > 2 else "free"
    results = sys.argv[3] if len(sys.argv) > 3 else DEFAULT_RESULTS
    d = json.load(open(results))["results"]; ay = ay_vectors(ay_path)
    cov = collections.Counter(v[0] for v in ay.values())
    print(f"AY coverage: {dict(cov)}  (from {os.path.basename(ay_path)})")
    for qo in (False, True):
        ranked, name = score(d, ay, cat, quality_only=qo)
        tag = "QUALITY-ONLY (ties=0.5)" if qo else "OFFICIAL (time-split)"
        pos = [k for k, (m, _) in enumerate(ranked) if m == "AY"][0] + 1
        print(f"\n=== category={cat}  {tag}  — AY rank {pos}/{len(ranked)} ===")
        for k, (m, sc) in enumerate(ranked):
            print(f"  {k+1:2}. {name[m]:34} {sc:8.2f}{'  <<<' if m == 'AY' else ''}")

if __name__ == "__main__":
    main()

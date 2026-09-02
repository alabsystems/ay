#!/usr/bin/env python3
"""Try HARD to CONSTRUCT a solution strictly BELOW a claimed floor.

Consults neither AY nor VeriPB: its own OPB reader, CP-SAT as the engine. A
SAT answer here would REFUTE the certificate. INFEASIBLE is the independent
corroboration; UNKNOWN is a failure to decide and is reported as such, never
as agreement.
"""
import re, sys
from ortools.sat.python import cp_model

TERM = re.compile(r'([+-]?\d+)\s+(~?)x(\d+)')

def parse(path):
    obj, cons = None, []
    with open(path) as fh:
        for line in fh:
            line = line.strip()
            if not line or line.startswith('*'):
                continue
            if line.startswith('min:'):
                obj = [(int(c), neg == '~', int(v))
                       for c, neg, v in TERM.findall(line)]
                continue
            m = re.search(r'(>=|=)\s*([+-]?\d+)\s*;?\s*$', line)
            if not m:
                continue
            rel, rhs = m.group(1), int(m.group(2))
            lhs = line[:m.start()]
            cons.append(([(int(c), neg == '~', int(v))
                          for c, neg, v in TERM.findall(lhs)], rel, rhs))
    return obj, cons

def main():
    path, floor, budget = sys.argv[1], int(sys.argv[2]), float(sys.argv[3])
    obj, cons = parse(path)
    if obj is None:
        print("SETUP-FAIL\tno min: objective"); return 2
    nv = max([v for _, _, v in obj] + [v for t, _, _ in cons for _, _, v in t])
    m = cp_model.CpModel()
    x = {i: m.NewBoolVar(f'x{i}') for i in range(1, nv + 1)}
    def lit(neg, v):
        return x[v].Not() if neg else x[v]
    for terms, rel, rhs in cons:
        e = sum(c * lit(n, v) for c, n, v in terms)
        m.Add(e == rhs) if rel == '=' else m.Add(e >= rhs)
    o = sum(c * lit(n, v) for c, n, v in obj)
    # THE WHOLE POINT: strictly below the claimed floor.
    m.Add(o <= floor - 1)
    s = cp_model.CpSolver()
    s.parameters.max_time_in_seconds = budget
    s.parameters.num_search_workers = 8
    st = s.Solve(m)
    name = s.StatusName(st)
    if st == cp_model.OPTIMAL or st == cp_model.FEASIBLE:
        print(f"REFUTED\t{path}\tfound obj <= {floor-1}\t{name}")
        return 1
    if st == cp_model.INFEASIBLE:
        print(f"NO-SOLUTION-BELOW-{floor}\t{path}\tCP-SAT proved obj <= {floor-1} INFEASIBLE")
        return 0
    print(f"UNDECIDED\t{path}\tCP-SAT {name} in {budget}s - NOT agreement")
    return 3

sys.exit(main())

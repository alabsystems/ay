#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
"""Bound the LP relaxation of a normalized OPB *independently of AY*.

WHY THIS EXISTS. An LP-dual floor certificate proves `obj >= ceil(y'b)` from a
dual-feasible `y >= 0`, and weak duality caps EVERY such floor at `ceil(LP*)`.
So an instance whose `ceil(LP*)` sits below its optimum can never be certified
by that route, no matter the budget, the vertex, or the denominator cap. AY's
own `lp_dual_floor_diagnosis` answers this from AY's dual solve — which is
exactly the component under suspicion when a floor looks bad, and which reports
`INCONCLUSIVE` whenever its solve does not converge. This script answers the
same question with no AY in the loop.

WHAT IS ACTUALLY PROVEN. Floats are used only to GUESS where to look; every
reported bound is recomputed in exact `Fraction` arithmetic and is valid on its
own terms even if the float engine returned nonsense:

  upper  a primal point snapped to a small denominator and verified row by row.
         Feasible => its exact objective is an upper bound on LP*.
  lower  y := max(0, -HiGHS marginals) snapped to a small denominator, with
         w := max(0, A'y - c). For ANY y >= 0 this pair is dual feasible, so
         `b'y - 1'w` is a lower bound on LP*. Nothing is assumed about y.

When the two meet, LP* is pinned to a rational exactly.

USAGE
  # exact two-sided bound on one instance
  pb_lp_relaxation_ceiling.py bound FILE.opb

  # corpus ceiling: TSV of `path <TAB> status <TAB> objective`, keeping the
  # rows whose status is `s OPTIMUM FOUND`, classify each REACHABLE/UNREACHABLE
  pb_lp_relaxation_ceiling.py census SOLVED.tsv OUT.tsv

Needs scipy (HiGHS). Read-only; solves nothing itself.
"""

import math
import sys
from fractions import Fraction

TOL = 1e-6
SNAP_DENOMINATORS = (1, 2, 3, 4, 5, 8, 10, 16, 20, 40, 80, 160, 1000, 10**6, 10**9)


class Unsupported(Exception):
    """The instance is outside the plain `>=` / unit-literal slice compared here."""


def parse_opb(path):
    """Parse to `min c'x  s.t.  Ax >= b, x in [0,1]`, or raise `Unsupported`."""
    objective, rows, num_vars, nnz = {}, [], 0, 0
    with open(path) as handle:
        for line in handle:
            line = line.strip()
            if not line or line.startswith("*"):
                continue
            if line.startswith("min:"):
                body = line[4:].strip().rstrip(";").split()
                if len(body) % 2:
                    raise Unsupported("objective-constant")
                for i in range(0, len(body), 2):
                    name = body[i + 1]
                    if not name.startswith("x"):
                        raise Unsupported("objective-nonlinear-or-negated")
                    var = int(name[1:])
                    objective[var] = objective.get(var, 0) + int(body[i])
                    num_vars = max(num_vars, var)
                continue
            tokens = line.rstrip(";").split()
            relation = tokens[-2]
            if relation not in (">=", "="):
                raise Unsupported(f"unsupported-relation({relation})")
            rhs, body = int(tokens[-1]), tokens[:-2]
            if len(body) % 2:
                raise Unsupported("row-constant")
            terms = {}
            for i in range(0, len(body), 2):
                name = body[i + 1]
                if not name.startswith("x"):
                    raise Unsupported("nonlinear-or-negated-row")
                var = int(name[1:])
                terms[var] = terms.get(var, 0) + int(body[i])
                num_vars = max(num_vars, var)
            nnz += len(terms)
            rows.append((terms, rhs))
            if relation == "=":
                # `a.x = r` is `a.x >= r` together with `-a.x >= -r`; keeping the
                # whole model one-sided lets the exact dual stay a plain y >= 0.
                rows.append(({var: -c for var, c in terms.items()}, -rhs))
                nnz += len(terms)
    if not objective:
        raise Unsupported("no-objective")
    return objective, rows, num_vars, nnz


def solve_float(objective, rows, num_vars):
    import numpy as np
    from scipy.optimize import linprog
    from scipy.sparse import coo_matrix

    cost = np.zeros(num_vars)
    for var, coeff in objective.items():
        cost[var - 1] = coeff
    row_idx, col_idx, data = [], [], []
    upper = np.zeros(len(rows))
    for i, (terms, rhs) in enumerate(rows):  # a.x >= r  ==>  -a.x <= -r
        for var, coeff in terms.items():
            row_idx.append(i)
            col_idx.append(var - 1)
            data.append(-float(coeff))
        upper[i] = -float(rhs)
    matrix = coo_matrix((data, (row_idx, col_idx)), shape=(len(rows), num_vars))
    result = linprog(cost, A_ub=matrix, b_ub=upper, bounds=(0, 1), method="highs")
    if result.status != 0:
        raise Unsupported(f"lp-status-{result.status}")
    return result


def exact_upper(objective, rows, num_vars, result):
    """Best exact upper bound on LP* from a verified snapped primal point."""
    best = None
    for denominator in SNAP_DENOMINATORS:
        point = {
            var: Fraction(result.x[var - 1]).limit_denominator(denominator)
            for var in range(1, num_vars + 1)
        }
        if any(value < 0 or value > 1 for value in point.values()):
            continue
        if any(
            sum(coeff * point[var] for var, coeff in terms.items()) < rhs
            for terms, rhs in rows
        ):
            continue
        value = sum(coeff * point[var] for var, coeff in objective.items())
        if best is None or value < best:
            best = value
    return best


def exact_lower(objective, rows, result):
    """Best exact lower bound on LP* from a self-certifying dual pair."""
    best = None
    marginals = result.ineqlin.marginals
    for denominator in SNAP_DENOMINATORS:
        duals = []
        for marginal in marginals:
            value = Fraction(-float(marginal)).limit_denominator(denominator)
            duals.append(value if value > 0 else Fraction(0))
        transposed = {}
        for i, (terms, _rhs) in enumerate(rows):
            if duals[i] == 0:
                continue
            for var, coeff in terms.items():
                transposed[var] = transposed.get(var, Fraction(0)) + coeff * duals[i]
        bound = sum(rhs * duals[i] for i, (_terms, rhs) in enumerate(rows))
        for var, value in transposed.items():
            excess = value - objective.get(var, 0)
            if excess > 0:  # w_var = excess, priced at 1 per unit
                bound -= excess
        if best is None or bound > best:
            best = bound
    return best


def bound(path):
    objective, rows, num_vars, nnz = parse_opb(path)
    result = solve_float(objective, rows, num_vars)
    low = exact_lower(objective, rows, result)
    high = exact_upper(objective, rows, num_vars, result)
    print(f"{path}")
    print(f"  vars={num_vars} rows={len(rows)} nnz={nnz}  HiGHS float LP* = {result.fun!r}")
    print(f"  EXACT lower bound on LP* : {low} = {float(low)!r}")
    if high is None:
        print("  EXACT upper bound on LP* : none found at these denominators")
    else:
        print(f"  EXACT upper bound on LP* : {high} = {float(high)!r}")
        if low == high:
            print(f"  => LP* = {low} EXACTLY; ceil(LP*) = {math.ceil(low)}")
    return low, high


def census(solved_tsv, out_tsv):
    reachable = unreachable = declined = 0
    with open(out_tsv, "w") as out:
        for line in open(solved_tsv):
            parts = line.rstrip("\n").split("\t")
            if len(parts) < 3 or parts[1] != "s OPTIMUM FOUND" or not parts[2]:
                continue
            path, optimum = parts[0], int(parts[2])
            try:
                objective, rows, num_vars, nnz = parse_opb(path)
                result = solve_float(objective, rows, num_vars)
                ceil_lp = math.ceil(result.fun - TOL)
                verdict = "REACHABLE" if ceil_lp >= optimum else "UNREACHABLE"
                reachable += verdict == "REACHABLE"
                unreachable += verdict == "UNREACHABLE"
                out.write(
                    f"{path}\t{optimum}\t{result.fun!r}\t{ceil_lp}\t{verdict}\t{nnz}\n"
                )
            except Exception as exc:  # noqa: BLE001 - every decline is reported
                declined += 1
                out.write(f"{path}\t{optimum}\t\t\tDECLINED:{exc}\t\n")
            out.flush()
    total = reachable + unreachable
    share = f"{100.0 * reachable / total:.1f}%" if total else "n/a"
    print(
        f"REACHABLE={reachable} UNREACHABLE={unreachable} DECLINED={declined}  "
        f"LP-dual-floor ceiling over classified = {share}"
    )


def main(argv):
    if len(argv) >= 3 and argv[1] == "bound":
        bound(argv[2])
        return 0
    if len(argv) >= 4 and argv[1] == "census":
        census(argv[2], argv[3])
        return 0
    sys.stderr.write(__doc__)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv))

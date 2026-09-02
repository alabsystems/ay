#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
"""Certified LP branch-and-bound -> VeriPB OPT-LIN optimality proof.

WHY THIS EXISTS.  It closes ONE typed gap in the PB certificate campaign, and it
makes a second instance's existing certificate 1,484x smaller.  Those are two
different kinds of win and an earlier version of this docstring ran them
together as "closes the last two TYPED gaps".  Stated apart:

    normalized-f20c10b_008_...opb    LP* = 93/4   = 23.25         ceil = 24
                                     optimum 25   ->  s VERIFIED BOUNDS 25 <= obj <= 25
        A GENUINE COVERAGE CONVERSION.  MISS in all eight arms of both the
        0829 and the 0830 censuses; certified here for the first time.

    normalized-g9x9.opb              LP* = 1113/61 = 18.245901..  ceil = 19
                                     optimum 20   ->  s VERIFIED BOUNDS 20 <= obj <= 20
        NOT a coverage conversion.  AY already certified this one BY SEARCH:
        census/definitive-2026-0829/census-60000.json has it COVERED on both
        binaries, proof_bytes 32,965,756, proof_lines 47,748, byte-reproduced
        (one distinct sha256 over four A/B runs).  What this buys is SIZE:
        22,213 bytes against 32,965,756, and 37 lines against 47,748.

    THE UNMEASURED LEAD.  Whether that compression also applies to the other
    ~150 certificates AY already produces by search is UNKNOWN -- nobody has
    looked, on any instance but g9x9.  At 60 s the cli arm accepts 153 proofs
    totalling 155,319,745 bytes, median only 18,547 B but with 16 above 1 MB
    and the ten largest carrying 82.7% of all bytes.  That is the measurement
    that decides whether the Rust port is justified on size.

Both are `ceil(LP*) = optimum - 1`: exactly one unit short, so weak duality caps
EVERY LP-dual floor strictly below the optimum, permanently.  The eight existing
certifiers each bought that unit from a STRUCTURAL fact (an odd cycle, a
handshake parity, a per-colour at-most-one, a pebbling layer).  g9x9 has no such
fact to find -- it is grid domination, whose lower bound is a transfer-matrix DP
that no counting argument reproduces -- and the search for one is measurably
dead:

    rank-1 {0,1/2} closure over the tight rows ....... 18.3333  (2 cuts, then none)
    multi-round CG-k, k in {2,3,5,7,11,13,17,19,23} .. 18.5738  (1500 cuts, tailing
                                                        off at +4e-5/round)

WHAT BUYS THE UNIT INSTEAD.  Not a better cut -- a SPLIT.  Cutting planes cannot
case-split on an objective bound (adding `S + M*x_i >= K` to `S - M*x_i >= K - M`
gives `S >= K - M/2`, the well-known collapse), but it CAN case-split on a
LITERAL, because the leaf of a split is closable as a CLAUSE, whose penalty
coefficient is 1 and therefore survives resolution.  The derivation is one line.

At a node with variables fixed to 1 (`F1`) and 0 (`F0`), let `y >= 0` be the
residual LP's row duals and `w >= 0` its upper-bound duals, scaled to integers
over a common denominator `q`.  Sum:

    sum_c Y_c * row_c                          ->  sum_v A_v x_v >= G
  + q * (the soli-installed row `-sum c_v x_v >= 1 - OPT`)
  + W_v * (~x_v >= 0)   for each free v        (the upper-bound duals)
  + (q*c_v + W_v - A_v) * (x_v >= 0)           for each free v   (zeroes it)
  + the same two axioms on the fixed v         (zeroes them, or leaves the sign
                                                that normalises into ~x_v)

Every free variable's coefficient cancels EXACTLY -- that is what residual dual
feasibility `A_v - W_v <= q*c_v` means -- so what is left is supported only on
the branch literals, with degree

    R = q * (node_bound - (OPT - 1)).

`node_bound > OPT-1` is the pruning test, so `R > 0`, and one division

    ; d K       K = max(R, largest remaining coefficient)

rounds every surviving coefficient to 1 and the degree to 1: the CLAUSE
`sum_{v in F1} ~x_v + sum_{v in F0} x_v >= 1`.  Internal nodes are then plain
resolution, `pol <c1> <c0> + s ;`, and the root clause is empty -- the
contradiction that justifies `conclusion BOUNDS opt opt`.

So the whole optimality proof is ONE `pol` line per pruned leaf plus one per
internal node.  Measured -- with ONE line-count convention, `derivation lines`
being the `pol` lines and the file carrying 6 more (header, `f`, `soli`,
`output`, `conclusion`, `end`):

    instance      derivation  total  leaves  depth  bytes
    g9x9                  31     37      16      6      22,213
    f20c10b_008          759    765     380     17  24,698,886
    petersen-vc            3      9       2      1         469

(The earlier text quoted "3.5 KB" for g9x9 -- wrong, the file is 22,213 bytes
-- and quoted 759 and 765 lines for f20c10b_008 in different places without
saying they were the derivation count and the total.  Both are fixed above.)

WHAT THE g9x9 LP FACT IS, AND WHAT IT IS NOT.  A retracted earlier draft argued
the bound from the LP optimum being a unique point recovered through `A^-1`.
That derivation is WRONG.  `A` is the 81x81 dominating-set incidence matrix of
`P9 [] P9` and it is SINGULAR -- rank(A) = 79 of 81 -- so `A^-1` does not exist,
and the optimal face is not a point: maximising and minimising one coordinate
over `{A x >= 1, 0 <= x <= 1, sum x = LP*}` gives

    x19 in [0.188525, 0.516393]

i.e. a polytope of positive dimension.  What survives is the only load-bearing
part, the VALUE: `LP* = 1113/61 = 18.245901..`, so `ceil(LP*) = 19` and the
weak-duality cap at `optimum - 1` stands.  Uniqueness was never needed for it.

FAIL-CLOSED.  The float LP only CHOOSES the branch variable and decides when to
try a leaf.  Nothing float reaches the proof: the duals are snapped DOWN onto an
integer denominator (so dual feasibility can only improve), the leaf is emitted
only if the exact integer `R > 0`, and if no denominator in the ladder yields
`R > 0` the node is simply branched further.  A wrong claimed optimum cannot
produce a proof: the generator asserts the incumbent is feasible and achieves
`OPT`, and any leaf that turns out integral within budget raises `FATAL:
integral leaf within budget` and writes NO file.

  Re-measured 2026-08-31 in the strongest form the premise admits: a wrong
  optimum supplied WITH A MATCHING FEASIBLE WITNESS, so the cheap
  "incumbent value != claimed optimum" guard cannot be what refuses it.
  `sbox_4_shg` has optimum 22; HiGHS was asked for a feasible point pinned at
  exactly 23 (found, exact recheck `violated=0 objective=23`) and the generator
  was run at `optimum=23` against it.  It raised `FATAL: integral leaf within
  budget 22 -> ... the claimed optimum 23 is WRONG`, exited 1, and wrote no
  file.  The premise fires on the VALUE, not on witness bookkeeping.

  BUT THAT MESSAGE WAS ALSO REACHED FOR A SECOND, WRONG REASON, and the fix is
  below.  On `f20c10b_011` and on three `injcomp` members the generator printed
  the same "the claimed optimum is WRONG" line about optima that are CORRECT.
  HiGHS MIP, consulted independently (own OPB reader, exact integer recheck,
  neither AY nor VeriPB in the loop), reports the accused value INFEASIBLE on
  all four.  The accusation came from the row-discharge test, not from the
  instance.  A fail-closed premise that can fire for two different reasons is
  only as good as its rarer one.

ADVERSARIAL BATTERY, AND THE SIX ACCEPTED NO-OPS.  Sixteen mutation shapes were
run against the COMMITTED bytes of `g9x9.pbp` and against `petersen-vc.pbp`,
with identical results on both: the ten must-reject shapes are all REJECTED by
the pin (exit 1), and six are accepted.  An earlier note disclosed two of the
six.  The six split three ways:
  * arithmetic identities -- ENLARGING a leaf divisor (all coefficients and the
    degree are already <= K, so the clause is unchanged), and swapping the two
    operands of a resolution step (addition commutes);
  * a local slack -- dropping the `s` from the FINAL resolution step, whose
    combination is already contradictory before saturation.  Not a general
    licence; only that step was tested;
  * FOUR `conclusion` hint mutations, which are one finding and it is about the
    CHECKER, not about this generator: the hint is advisory and UNVALIDATED.
    Pointing it at an input row, at a leaf id, or at id 999999 which does not
    exist at all, changes nothing -- the pin still finds the derived
    contradiction and still reports the true bound.
The control proving the hint case is not a hole is `strip all derivation, keep
soli + conclusion`, REJECTED on both instances: a hint alone carries no proof.
The control proving acceptance tracks TRUTH is `bound one higher`, also
rejected on both.

TWO CORRECTNESS FIXES, 2026-08-31.  Both are about NEGATIVE COEFFICIENTS, which
the SCOPE note below never excluded and the code silently mishandled.

  (1) ROW DISCHARGE.  `keep = r > -1e-9` dropped every row whose residual rhs
      had gone <= 0.  That is valid only when the coefficient matrix is
      non-negative, where the least achievable LHS over the free variables is 0.
      With negative coefficients the least achievable LHS is the sum of the
      row's NEGATIVE free coefficients, so the correct test is
      `r > sum_v min(0, A[c,v]) `.  Measured at the ROOT: `injcomp_..._size_30`
      dropped 1859 of 1979 rows, `f20c10b_011` 17126 of 43326.  The relaxation
      left over was so weak its optimum looked integral, which is exactly the
      false "claimed optimum is WRONG" above.
      It was never a SOUNDNESS hole -- a dropped row is simply a row the
      combination does not cite, every cited multiplier stays non-negative, and
      the pin re-checks the arithmetic regardless -- but it cost COMPLETENESS
      and, on the instances it did not stop outright, SIZE:
          f20c10b_008   759 -> 17 derivation lines, 380 -> 9 leaves,
                        24,698,884 -> 444,827 bytes (55.5x smaller)
      and it converted `f20c10b_011` outright (7 nodes, 4 leaves).

  (2) FARKAS LEAVES.  An LP-infeasible node had no leaf rule at all and raised
      `needs a Farkas leaf line (not implemented)`.  It is the same emission
      with the objective/`soli` multiplier `qo` set to 0: phase-1
      `min t s.t. Ak x + t >= rk, x in [0,1], t >= 0` is always feasible and its
      duals at `t* > 0` are the Farkas certificate.  See `Certifier.farkas`.

  Also fixed: an unconstrained residual (`Ak.shape[0] == 0`) returned `base`,
  ignoring the free objective.  With negative costs that OVERSTATES the node
  bound, which is the unsafe direction for a pruning test.

SCOPE.  `>=` rows over un-negated literals with integer coefficients of EITHER
sign, and a linear `min:` objective of either sign.  Equality rows are not
handled (VeriPB splits them into two ids and the `f` count would have to
follow).

THIRD MEMBER.  `ci/cert-instances/certified-bb/petersen-vc.opb` (minimum vertex
cover on the Petersen graph) is the generality probe.  It was chosen because
`ceil(LP*) = 5 < 6 = optimum`, so no LP-dual floor can reach the bound and a
SPLIT must fire -- `nodes=3 leaves=2 maxdepth=1`.  It replaces
`benchmarks/pb-comp/test-instances/optimization-small.opb`, which had `LP* = 3 =
optimum` and reported `nodes=1 leaves=1 maxdepth=0`: no split fired there, so
that run probed the parser and the emitter and none of the argument above.

Usage:
    pb_certified_bb_cert.py <instance.opb> <out.pbp> <optimum> <node-cap> <sol.json>

where sol.json is a list of 0-based variable indices set to 1 in an incumbent
achieving <optimum>.
"""
import json
import re
import sys
import time

import numpy as np
import scipy.sparse as sp
from scipy.optimize import linprog

np.seterr(all="ignore")

# Denominator ladder for snapping the residual duals to exact integers.
DENOMS = (16, 256, 4096, 65536, 1048576, 16777216)


def parse_opb(path):
    """Return (num_vars, rows, objective) with 0-based variable indices."""
    nvar = None
    rows = []
    obj = {}
    for line in open(path):
        s = line.strip()
        if s.startswith("*"):
            m = re.search(r"#variable=\s*(\d+)", s)
            if m:
                nvar = int(m.group(1))
            continue
        if not s:
            continue
        if s.startswith("min:"):
            t = s[4:].rstrip(";").split()
            i = 0
            while i < len(t):
                if t[i + 1].startswith("~"):
                    raise SystemExit("negated literal in objective: unsupported")
                obj[int(t[i + 1][1:]) - 1] = int(t[i])
                i += 2
            continue
        m = re.match(r"^(.*?)>=\s*(-?\d+)\s*;$", s)
        if not m:
            raise SystemExit("unsupported row (only `>=` is handled): %s" % s[:60])
        t = m.group(1).split()
        d = {}
        i = 0
        while i < len(t):
            if t[i + 1].startswith("~"):
                raise SystemExit("negated literal in row: unsupported")
            v = int(t[i + 1][1:]) - 1
            d[v] = d.get(v, 0) + int(t[i])
            i += 2
        rows.append((d, int(m.group(2))))
    if nvar is None:
        nvar = 1 + max(max(d) for d, _ in rows)
    return nvar, rows, obj


class Certifier:
    def __init__(self, opb, optimum, cap, solpath):
        self.n, self.rows, self.obj = parse_opb(opb)
        self.m = len(self.rows)
        self.opt = optimum
        self.bud = optimum - 1
        self.cap = cap
        self.o = np.zeros(self.n)
        for v, c in self.obj.items():
            self.o[v] = c
        I, J, V = [], [], []
        self.B = np.zeros(self.m)
        for r, (d, b) in enumerate(self.rows):
            for v, c in d.items():
                I.append(r)
                J.append(v)
                V.append(float(c))
            self.B[r] = b
        self.A = sp.csr_matrix((V, (I, J)), shape=(self.m, self.n))
        self.sol = set(json.load(open(solpath)))
        x = np.zeros(self.n)
        for v in self.sol:
            x[v] = 1
        if not (self.A @ x - self.B >= -1e-9).all():
            raise SystemExit("incumbent is INFEASIBLE -- refusing to emit")
        if int(round(self.o @ x)) != optimum:
            raise SystemExit(
                "incumbent value %d != claimed optimum %d -- refusing to emit"
                % (int(round(self.o @ x)), optimum)
            )
        self.lines = []
        self.next_id = self.m + 2  # 1..m inputs, m+1 = the soli-installed row
        self.stats = {"nodes": 0, "leaves": 0, "maxdepth": 0, "farkas": 0}

    # ---- node LP (guidance only; nothing float reaches the proof) ----
    def node_lp(self, f1, f0):
        fx = np.zeros(self.n)
        for v in f1:
            fx[v] = 1
        fixed = np.zeros(self.n, dtype=bool)
        for v in f1:
            fixed[v] = True
        for v in f0:
            fixed[v] = True
        free = np.nonzero(~fixed)[0]
        r = self.B - self.A @ fx
        # A row may be DISCHARGED only if it holds for EVERY assignment of the
        # free variables, i.e. residual rhs <= min achievable LHS = the sum of
        # the row's NEGATIVE free coefficients. The original `r > -1e-9` test
        # assumed that minimum is 0, which is true only for non-negative
        # coefficient matrices. On `injcomp_..._size_30` that dropped 1859 of
        # 1979 rows at the root and on `f20c10b_011` 17126 of 43326, producing a
        # relaxation so weak its optimum looked integral -- which surfaced as the
        # FALSE accusation "the claimed optimum is WRONG". HiGHS MIP, consulted
        # independently, reports the forbidden value INFEASIBLE on all four.
        Afree = self.A[:, free]
        minlhs = np.asarray(Afree.minimum(0).sum(axis=1)).ravel()
        keep = np.nonzero(r > minlhs + 1e-9)[0]
        Ak = Afree[keep]
        rk = r[keep]
        rowmax = np.asarray(Ak.maximum(0).sum(axis=1)).ravel()
        if (rowmax < rk - 1e-9).any():
            return (None, None) + self.farkas(Ak, rk, keep, free) + (True,)
        base = float(self.o[list(f1)].sum()) if f1 else 0.0
        if Ak.shape[0] == 0:
            # Unconstrained residual: the minimum is attained by setting every
            # free variable with a NEGATIVE cost to 1. Returning `base` alone
            # overstates the node bound whenever the objective has negative
            # coefficients, which is a wrong-direction (unsafe-pruning) error.
            free_min = float(np.minimum(self.o[free], 0.0).sum())
            xs = {int(v): (1.0 if self.o[v] < 0 else 0.0) for v in free}
            return base + free_min, xs, {}, {}, False
        res = linprog(
            self.o[free], A_ub=-Ak, b_ub=-rk, bounds=[(0, 1)] * len(free), method="highs"
        )
        if res.status == 2:
            return (None, None) + self.farkas(Ak, rk, keep, free) + (True,)
        if res.status != 0:
            raise SystemExit("node LP failed (status %d)" % res.status)
        y = {int(keep[i]): max(0.0, -res.ineqlin.marginals[i]) for i in range(len(keep))}
        w = {int(free[i]): max(0.0, -res.upper.marginals[i]) for i in range(len(free))}
        xs = {int(free[i]): res.x[i] for i in range(len(free))}
        return base + res.fun, xs, y, w, False

    # ---- Farkas duals for an INFEASIBLE node ----
    def farkas(self, Ak, rk, keep, free):
        """Phase-1 duals witnessing residual infeasibility.

        `min t s.t. Ak x + t*1 >= rk, x in [0,1], t >= 0` is always feasible, and
        its optimum `t* > 0` exactly when the node is infeasible. Its row duals
        `y >= 0` and upper-bound duals `w >= 0` then satisfy `Ak' y <= w` and
        `rk'y - 1'w = t* > 0` -- the same shape the objective leaf uses, with the
        objective/`soli` multiplier set to zero. Without this an infeasible node
        has no leaf line at all, which is the `node is LP-infeasible: needs a
        Farkas leaf line (not implemented)` decline.
        """
        nf = Ak.shape[1]
        A1 = sp.hstack([Ak, np.ones((Ak.shape[0], 1))], format="csr")
        cost = np.zeros(nf + 1)
        cost[nf] = 1.0
        res = linprog(
            cost, A_ub=-A1, b_ub=-rk,
            bounds=[(0, 1)] * nf + [(0, None)], method="highs",
        )
        if res.status != 0:
            return {}, {}
        y = {int(keep[i]): max(0.0, -res.ineqlin.marginals[i]) for i in range(len(keep))}
        w = {int(free[i]): max(0.0, -res.upper.marginals[i]) for i in range(nf)}
        return y, w

    # ---- exact integer leaf certificate ----
    def exact_leaf(self, f1, f0, yf, wf, use_obj=True):
        fixed = f1 | f0
        for q in DENOMS:
            # `qo` is the multiplier on the objective and on the `soli`-installed
            # row. A FARKAS leaf sets it to 0: the node is closed by row
            # infeasibility alone, so the objective plays no part and the
            # combination must not cite the `soli` row.
            qo = q if use_obj else 0
            Y = {c: int(np.floor(yf.get(c, 0.0) * q * (1 - 1e-12))) for c in yf}
            Y = {c: v for c, v in Y.items() if v > 0}
            if not Y:
                continue
            A = np.zeros(self.n, dtype=np.int64)
            G = 0
            for c, wt in Y.items():
                d, b = self.rows[c]
                for v, cc in d.items():
                    A[v] += cc * wt
                G += b * wt
            coef = A - qo * self.o.astype(np.int64)
            W = {}
            ok = True
            for v in range(self.n):
                if v in fixed:
                    continue
                need = int(coef[v])
                wv = int(np.ceil(wf.get(v, 0.0) * q)) if wf.get(v, 0.0) > 0 else 0
                if need > wv:
                    wv = need
                if need - wv > 0:
                    ok = False
                    break
                if wv:
                    W[v] = wv
            if not ok:
                continue
            R = (
                G
                + qo * (1 - self.opt)
                - sum(W.values())
                + sum(int(qo * self.o[v]) - int(A[v]) for v in f1)
            )
            if R <= 0:
                continue
            cl_pos = {v: int(coef[v]) for v in f0 if coef[v] > 0}
            cl_neg = {v: int(-coef[v]) for v in f1 if coef[v] < 0}
            ax_pos, ax_neg = {}, {}
            for v in range(self.n):
                if v in f1:
                    if coef[v] > 0:
                        ax_neg[v] = int(coef[v])
                elif v in f0:
                    if coef[v] < 0:
                        ax_pos[v] = int(-coef[v])
                else:
                    wv = W.get(v, 0)
                    if wv:
                        ax_neg[v] = wv
                    rem = wv - int(coef[v])
                    if rem > 0:
                        ax_pos[v] = rem
            K = max([R] + list(cl_pos.values()) + list(cl_neg.values()))
            return qo, Y, R, cl_pos, cl_neg, ax_pos, ax_neg, K
        return None

    def emit(self, s):
        self.lines.append(s)
        self.next_id += 1
        return self.next_id - 1

    @staticmethod
    def polline(terms, div):
        parts = []
        first = True
        for op, mult in terms:
            if mult == 0:
                continue
            seg = [op] if mult == 1 else [op, str(mult), "*"]
            parts += seg if first else seg + ["+"]
            first = False
        if first:
            raise SystemExit("empty pol combination")
        if div != 1:
            parts += [str(div), "d"]
        return "pol " + " ".join(parts) + " ;"

    def dfs(self, f1, f0, depth):
        self.stats["nodes"] += 1
        self.stats["maxdepth"] = max(self.stats["maxdepth"], depth)
        if self.stats["nodes"] > self.cap:
            raise SystemExit("NODE CAP %d hit at depth %d" % (self.cap, depth))
        bnd, xs, yf, wf, infeasible = self.node_lp(f1, f0)
        # A leaf closes either because the objective bound exceeds the refuted
        # budget (`use_obj`, cites the `soli` row) or because the node's rows are
        # already contradictory (FARKAS, `qo = 0`, cites no objective at all).
        if infeasible or bnd > self.bud + 1e-7:
            e = self.exact_leaf(f1, f0, yf, wf, use_obj=not infeasible)
            if e is not None:
                qo, Y, R, cp, cn, ap, an, K = e
                terms = [("%d" % (c + 1), w) for c, w in sorted(Y.items())]
                if qo:
                    terms.append(("%d" % (self.m + 1), qo))
                terms += [("x%d" % (v + 1), c) for v, c in sorted(ap.items())]
                terms += [("~x%d" % (v + 1), c) for v, c in sorted(an.items())]
                cid = self.emit(self.polline(terms, K))
                self.stats["leaves"] += 1
                self.stats["farkas"] += 1 if infeasible else 0
                return cid, set(cp) | set(cn)
            if infeasible:
                raise SystemExit(
                    "infeasible node: no denominator in the ladder cleared the "
                    "Farkas certificate at depth %d" % depth
                )
        cands = [(v, xs[v]) for v in xs if 1e-6 < xs[v] < 1 - 1e-6]
        if not cands:
            raise SystemExit(
                "FATAL: integral leaf within budget %d -> a better solution exists; "
                "the claimed optimum %d is WRONG" % (self.bud, self.opt)
            )
        v = max(cands, key=lambda t: -abs(t[1] - 0.5))[0]
        i1, s1 = self.dfs(f1 | {v}, f0, depth + 1)
        if v not in s1:
            return i1, s1
        i0, s0 = self.dfs(f1, f0 | {v}, depth + 1)
        if v not in s0:
            return i0, s0
        return self.emit("pol %d %d + s ;" % (i1, i0)), (s1 | s0) - {v}

    def run(self, out):
        t0 = time.time()
        sys.setrecursionlimit(20000)
        root, residual = self.dfs(set(), set(), 0)
        if residual:
            raise SystemExit("root clause is not empty: %s" % residual)
        assign = " ".join(
            ("x%d" % (v + 1)) if v in self.sol else ("~x%d" % (v + 1))
            for v in range(self.n)
        )
        with open(out, "w") as f:
            f.write("pseudo-Boolean proof version 3.0\n")
            f.write("f %d ;\n" % self.m)
            f.write("soli %s;\n" % assign)
            for line in self.lines:
                f.write(line + "\n")
            f.write("output NONE;\n")
            f.write(
                "conclusion BOUNDS %d : %d %d : %s;\n" % (self.opt, root, self.opt, assign)
            )
            f.write("end pseudo-Boolean proof;\n")
        print(
            "nodes=%d leaves=%d farkas=%d maxdepth=%d lines=%d [%.1fs] -> %s"
            % (
                self.stats["nodes"],
                self.stats["leaves"],
                self.stats["farkas"],
                self.stats["maxdepth"],
                len(self.lines),
                time.time() - t0,
                out,
            )
        )


def main(argv):
    if len(argv) != 6:
        raise SystemExit(__doc__.strip().splitlines()[-4].strip())
    Certifier(argv[1], int(argv[3]), int(argv[4]), argv[5]).run(argv[2])


if __name__ == "__main__":
    main(sys.argv)

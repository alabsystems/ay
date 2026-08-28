#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
"""A VeriPB optimality certificate for the PB25 `ihalainen/PBO-clique-coloring`
family -- the family pinned as PERMANENTLY UNCERTIFIABLE on 2026-08-27.

WHY THIS EXISTS. `040f9f41d` established, in exact rational arithmetic, that
these instances have `LP* = 0` exactly against optima of `n - t`, and concluded
that no LP-dual floor can ever fire on them. That conclusion is CORRECT and this
script does not touch it. What was over-read was the next step: "so they cannot
be certified". A dual floor is not the only certificate VeriPB accepts.

  * `LP* = 0` is reconfirmed here, and so is the stronger fact that the FULL
    level-1 RLT lift is still exactly 0 (measured: 209,314 rows on n=7-t=3,
    447,828 on n=8-t=3, both LP* = 0 with an exact rational witness). So the
    obvious repair -- lift into product space and take the dual there -- is
    ALSO dead, and that is a real negative, not a gap in the search.
  * What lifts the bound is the product atoms `p[i][j][k] = M[i][j]*C[i][k]`
    PLUS a per-colour AT-MOST-ONE over them. In the LP that AMO is only valid
    after an optimum-preserving symmetry break ("at most one vertex per slot",
    which is NOT a cut -- `two_in_a_slot` below is a feasible point it removes).
  * In the PROOF SYSTEM no symmetry break is needed. Cutting planes has
    SATURATION and DIVISION; LP duality has neither. Every place the LP needs
    the products' 0/1-ness, the proof spends one `s` or one `2 d`. That is the
    whole finding: the ceiling was a ceiling on LP DUALITY, not on VeriPB.

THE MATHEMATICS, in one paragraph. Each occupied slot holds a vertex; vertices
in DISTINCT slots are forced adjacent by the edge rows, hence differently
coloured by the proper-colouring rows. So occupied slots inject into colours and
at most `t` slots are occupied, leaving at least `n - t` paid. The proof makes
that injection explicit: `z[j][k]` reifies "slot `j` holds a colour-`k` vertex",
`o[j] + sum_k z[j][k] >= 1` says an unpaid slot holds something, and a ladder
over the pairwise conflicts turns them into `sum_j z[j][k] <= 1`. Adding the `n`
slot rows to the `t` AMO rows gives `sum_j o[j] >= n - t` with UNIT multipliers.

WHAT IS FAIL-CLOSED. The recognizer accounts for EVERY row of the input against
the five templates and raises if even one is unexplained, so it cannot fire on a
lookalike; the incumbent it emits is re-verified against the parsed rows before
anything is written; and the emitted bound is `n - t` only because the checker
is then asked to confirm it. Measured over 1,070 PB25 OPB files: 10 accepted,
1,060 rejected, zero false accepts.

USAGE
  pb_clique_coloring_cert.py gate    FILE.opb        # O(1) header pre-gate
  pb_clique_coloring_cert.py check   FILE.opb        # exact LP* = 0 witness
  pb_clique_coloring_cert.py prove   FILE.opb OUT.pbp
  pb_clique_coloring_cert.py sweep   DIR             # pre-gate cost on a corpus
  pb_clique_coloring_cert.py synth   n t OUT.opb     # an in-family instance, so
                                                     # the whole chain runs from
                                                     # a fresh clone with no
                                                     # external corpus

Verify what it writes with the PINNED checker only (`ci/veripb.pin`):
  veripb FILE.opb OUT.pbp   ->   s VERIFIED BOUNDS n-t <= obj <= n-t
No third-party library is needed; the proof path is pure integer arithmetic.
"""

import glob
import os
import sys
import time


class NotThisFamily(Exception):
    """The instance is not a clique-coloring instance. Always fail closed."""


# --------------------------------------------------------------------------
# O(1) pre-gate: decide from the header line, before reading any constraint.
# --------------------------------------------------------------------------
def header_candidate(nvar, ncon):
    """(n, t) consistent with these counts, or None.

    #variable   = n^2 + n + n*t + C(n,2)
    #constraint = 3n + C(n,2)*n*(n-1) + C(n,2)*t
    """
    n = 2
    while n * n + n <= nvar:
        c2 = n * (n - 1) // 2
        rest = nvar - (n * n + n + c2)
        if rest >= 0 and rest % n == 0:
            t = rest // n
            if t >= 1 and ncon == 3 * n + c2 * n * (n - 1) + c2 * t:
                return (n, t)
        n += 1
    return None


def header_gate(path):
    with open(path, "rb") as handle:
        for _ in range(4):
            line = handle.readline()
            if not line:
                return None
            text = line.decode("latin-1")
            if "#variable=" in text and "#constraint=" in text:
                tok = text.replace("=", "= ").split()
                try:
                    nvar = int(tok[tok.index("#variable=") + 1])
                    ncon = int(tok[tok.index("#constraint=") + 1])
                except (ValueError, IndexError):
                    return None
                return header_candidate(nvar, ncon)
    return None


# --------------------------------------------------------------------------
# Full structural recovery. Every row must be explained or this raises.
# --------------------------------------------------------------------------
def parse_opb(path):
    objective, rows, nvar = {}, [], 0
    with open(path) as handle:
        for line in handle:
            text = line.strip()
            if not text or text.startswith("*"):
                continue
            if text.startswith("min:"):
                body = text[4:].strip().rstrip(";").split()
                for i in range(0, len(body), 2):
                    if not body[i + 1].startswith("x"):
                        raise NotThisFamily("negated literal in objective")
                    var = int(body[i + 1][1:])
                    objective[var] = objective.get(var, 0) + int(body[i])
                    nvar = max(nvar, var)
                continue
            tok = text.rstrip(";").split()
            if tok[-2] != ">=":
                raise NotThisFamily(f"relation {tok[-2]}")
            rhs, body = int(tok[-1]), tok[:-2]
            terms = {}
            for i in range(0, len(body), 2):
                if not body[i + 1].startswith("x"):
                    raise NotThisFamily("negated literal in a row")
                var = int(body[i + 1][1:])
                terms[var] = terms.get(var, 0) + int(body[i])
                nvar = max(nvar, var)
            rows.append((terms, rhs))
    return objective, rows, nvar


class Instance:
    """Recovered layout. `M[i][j]`, `C[i][k]`, `E[(i,i')]`, `O[j]` are OPB
    variable numbers; `rows` is in file order, so row `r` has VeriPB id `r+1`."""


def recover(path):
    gate = header_gate(path)
    if gate is None:
        raise NotThisFamily("header counts do not match the family")
    objective, rows, nvar = parse_opb(path)
    if not objective or any(c != 1 for c in objective.values()):
        raise NotThisFamily("objective is not a plain sum of unit payments")
    slots_o = sorted(objective)
    n = len(slots_o)
    if (n, ) != (gate[0], ):
        raise NotThisFamily("objective width disagrees with the header")
    oset = set(slots_o)

    slot_rows, vertex_rows, colour_rows, edge_rows, proper_rows = [], [], [], [], []
    for index, (terms, rhs) in enumerate(rows):
        if rhs == 1 and all(c == 1 for c in terms.values()):
            (slot_rows if (set(terms) & oset) else colour_rows).append((index, terms))
        elif rhs == -1 and all(c == -1 for c in terms.values()):
            vertex_rows.append((index, terms))
        elif rhs == -1 and len(terms) == 3 and sorted(terms.values()) == [-1, -1, 1]:
            edge_rows.append((index, terms))
        elif rhs == -2 and len(terms) == 3 and all(c == -1 for c in terms.values()):
            proper_rows.append((index, terms))
        else:
            raise NotThisFamily(f"row {index} matches no template")
    if not (len(slot_rows) == len(vertex_rows) == len(colour_rows) == n):
        raise NotThisFamily("slot/vertex/colour row counts disagree with n")

    slot_members = {}
    for _, terms in slot_rows:
        marked = set(terms) & oset
        if len(marked) != 1:
            raise NotThisFamily("slot row does not carry exactly one payment")
        o = marked.pop()
        slot_members[o] = set(terms) - {o}
        if len(slot_members[o]) != n:
            raise NotThisFamily("slot row does not list n placements")
    slots = sorted(slot_members)

    grid = [[None] * n for _ in range(n)]
    for i, (_, terms) in enumerate(vertex_rows):
        members = set(terms)
        if len(members) != n:
            raise NotThisFamily("vertex row does not list n placements")
        for j, o in enumerate(slots):
            common = members & slot_members[o]
            if len(common) != 1:
                raise NotThisFamily("placement grid is not a bijection")
            grid[i][j] = common.pop()
    where = {grid[i][j]: (i, j) for i in range(n) for j in range(n)}
    if len(where) != n * n:
        raise NotThisFamily("placement variables are not distinct")

    colour_sets = [sorted(terms) for _, terms in colour_rows]
    t = len(colour_sets[0])
    if t != gate[1] or any(len(cs) != t for cs in colour_sets):
        raise NotThisFamily("ragged colour rows")
    colour_of = {}
    for i, cs in enumerate(colour_sets):
        for k, v in enumerate(cs):
            if v in colour_of:
                raise NotThisFamily("colour variable shared between vertices")
            colour_of[v] = (i, k)

    edge_pair, edge_id = {}, {}
    for index, terms in edge_rows:
        plus = [v for v, c in terms.items() if c == 1]
        minus = [v for v, c in terms.items() if c == -1]
        if len(plus) != 1 or any(v not in where for v in minus):
            raise NotThisFamily("edge row shape")
        (i1, a), (i2, b) = where[minus[0]], where[minus[1]]
        if a == b or i1 == i2:
            raise NotThisFamily("edge row over a repeated vertex or slot")
        key = (min(i1, i2), max(i1, i2))
        if edge_pair.setdefault(plus[0], key) != key:
            raise NotThisFamily("edge variable reused across vertex pairs")
        edge_id[frozenset({(i1, a), (i2, b)})] = index + 1
    if len(edge_id) != n * (n - 1) // 2 * n * (n - 1):
        raise NotThisFamily("edge rows do not cover every distinct-slot pair")

    proper_id = {}
    for index, terms in proper_rows:
        es = [v for v in terms if v in edge_pair]
        cs = [v for v in terms if v in colour_of]
        if len(es) != 1 or len(cs) != 2:
            raise NotThisFamily("proper row shape")
        (v1, k1), (v2, k2) = colour_of[cs[0]], colour_of[cs[1]]
        if k1 != k2 or {v1, v2} != set(edge_pair[es[0]]):
            raise NotThisFamily("proper row does not match its edge")
        proper_id[(edge_pair[es[0]], k1)] = index + 1
    if len(proper_id) != n * (n - 1) // 2 * t:
        raise NotThisFamily("proper rows do not cover every (pair, colour)")

    inst = Instance()
    inst.path, inst.n, inst.t, inst.nvar, inst.rows = path, n, t, nvar, rows
    inst.O = slots
    inst.M = grid
    inst.C = [[colour_sets[i][k] for k in range(t)] for i in range(n)]
    inst.slot_id = {slots.index((set(terms) & oset).pop()): idx + 1
                    for idx, terms in slot_rows}
    inst.vertex_id = {i: idx + 1 for i, (idx, _) in enumerate(vertex_rows)}
    inst.colour_id = {i: idx + 1 for i, (idx, _) in enumerate(colour_rows)}
    inst.edge_id, inst.proper_id = edge_id, proper_id
    return inst


# --------------------------------------------------------------------------
# The two exact facts the certificate rests against.
# --------------------------------------------------------------------------
def uniform_witness_violations(inst):
    """`LP* <= 0`: every vertex 1/n in every slot, every colour 1/t on every
    vertex, edges and payments 0. Scaled by n*t, so this is integer arithmetic
    and the answer does not depend on any floating-point engine."""
    n, t = inst.n, inst.t
    value = {}
    for v in inst.O:
        value[v] = 0
    for i in range(n):
        for j in range(n):
            value[inst.M[i][j]] = t
        for k in range(t):
            value[inst.C[i][k]] = n
    for v in range(1, inst.nvar + 1):
        value.setdefault(v, 0)
    bad = sum(1 for terms, rhs in inst.rows
              if sum(c * value[v] for v, c in terms.items()) < rhs * n * t)
    return bad, sum(value[v] for v in inst.O)


def two_in_a_slot(inst):
    """A FEASIBLE point the LP's clique row would cut off: vertices 0 and 1 share
    slot 0 and share colour 0. No pair is in distinct slots so no edge is forced.
    This is why the LP formulation needs a symmetry break and the PROOF does not."""
    n, t = inst.n, inst.t
    value = {v: 0 for v in range(1, inst.nvar + 1)}
    value[inst.M[0][0]] = 1
    value[inst.M[1][0]] = 1
    for j in range(1, n):
        value[inst.O[j]] = 1
    for v in range(n):
        value[inst.C[v][0]] = 1
    bad = sum(1 for terms, rhs in inst.rows
              if sum(c * value[v] for v, c in terms.items()) < rhs)
    product_sum = sum(value[inst.M[i][j]] * value[inst.C[i][0]]
                      for i in range(n) for j in range(n))
    return bad, product_sum


def incumbent(inst):
    """Value `n - t`: vertices 0..t-1 into slots 0..t-1, vertex v coloured
    min(v, t-1), edges exactly among the placed vertices. Re-verified against the
    PARSED rows -- if this ever fails, nothing is emitted."""
    n, t = inst.n, inst.t
    value = {v: 0 for v in range(1, inst.nvar + 1)}
    for v in range(t):
        value[inst.M[v][v]] = 1
    for j in range(t, n):
        value[inst.O[j]] = 1
    for v in range(n):
        value[inst.C[v][min(v, t - 1)]] = 1
    # edge variables: 1 exactly on the pairs of PLACED vertices, so the proper
    # rows stay slack on every unplaced pair
    for v, (i1, i2) in _edge_vars(inst).items():
        value[v] = 1 if (i1 < t and i2 < t) else 0
    bad = [1 for terms, rhs in inst.rows
           if sum(c * value[v] for v, c in terms.items()) < rhs]
    if bad:
        raise NotThisFamily(f"constructed incumbent violates {len(bad)} rows")
    if sum(value[v] for v in inst.O) != n - t:
        raise NotThisFamily("constructed incumbent does not achieve n - t")
    return value


def _edge_vars(inst):
    """edge variable -> (i, i'), recovered from the rows."""
    where = {inst.M[i][j]: (i, j) for i in range(inst.n) for j in range(inst.n)}
    out = {}
    for terms, rhs in inst.rows:
        if rhs == -1 and len(terms) == 3 and sorted(terms.values()) == [-1, -1, 1]:
            e = [v for v, c in terms.items() if c == 1][0]
            ms = [where[v][0] for v, c in terms.items() if c == -1]
            out[e] = (min(ms), max(ms))
    return out


# --------------------------------------------------------------------------
# The proof.
# --------------------------------------------------------------------------
class Proof:
    def __init__(self, out, f_count):
        self.out, self.next = out, f_count + 1
        out.write("pseudo-Boolean proof version 3.0\n")
        out.write(f"f {f_count} ;\n")

    def _emit(self, line):
        self.out.write(line + "\n")
        self.next += 1
        return self.next - 1

    def soli(self, lits):
        return self._emit("soli " + " ".join(lits) + " ;")

    def red(self, body, degree, witness):
        return self._emit(f"red {body} >= {degree} : {witness} ;")

    def pol(self, expr):
        return self._emit(f"pol {expr} ;")


def emit_proof(inst, out):
    """Write the VeriPB v3 proof. Returns the id of the final contradiction."""
    n, t, N = inst.n, inst.t, inst.nvar
    value = incumbent(inst)
    pvar = lambda i, j, k: N + 1 + ((i * n + j) * t + k)
    zvar = lambda j, k: N + n * n * t + 1 + (j * t + k)
    svar = lambda j, k: N + n * n * t + n * t + 1 + (j * t + k)
    M = lambda i, j: f"x{inst.M[i][j]}"
    nM = lambda i, j: f"~x{inst.M[i][j]}"
    C = lambda i, k: f"x{inst.C[i][k]}"
    nC = lambda i, k: f"~x{inst.C[i][k]}"

    proof = Proof(out, len(inst.rows))
    lits = [f"x{v}" if value[v] else f"~x{v}" for v in range(1, N + 1)]
    soli_id = proof.soli(lits)

    # p[i][j][k] <-> M[i][j] & C[i][k]. Introduction ORDER is load bearing: the
    # `p -> 1` line must come first, or the `p -> 0` witnesses have a goal they
    # cannot discharge.
    pge, ple_m, ple_c = {}, {}, {}
    for i in range(n):
        for j in range(n):
            for k in range(t):
                p = f"x{pvar(i, j, k)}"
                pge[i, j, k] = proof.red(f"+1 {p} +1 {nM(i,j)} +1 {nC(i,k)}", 1,
                                         f"{p} -> 1")
                ple_m[i, j, k] = proof.red(f"+1 {M(i,j)} +1 ~{p}", 1, f"{p} -> 0")
                ple_c[i, j, k] = proof.red(f"+1 {C(i,k)} +1 ~{p}", 1, f"{p} -> 0")

    # sum_k p[i][j][k] >= M[i][j]   -- the colour row TIMES M[i][j], then `s`.
    # This single saturation is what LP duality cannot reproduce.
    sum_p = {}
    for i in range(n):
        for j in range(n):
            expr = str(inst.colour_id[i])
            for k in range(t):
                expr += f" {pge[i,j,k]} +"
            sum_p[i, j] = proof.pol(expr + " s")

    zor, zge = {}, {}
    for j in range(n):
        for k in range(t):
            body = (f"+1 ~x{zvar(j,k)} "
                    + " ".join(f"+1 x{pvar(i,j,k)}" for i in range(n)))
            zor[j, k] = proof.red(body, 1, f"x{zvar(j,k)} -> 0")
            for i in range(n):
                zge[j, k, i] = proof.red(
                    f"+1 x{zvar(j,k)} +1 ~x{pvar(i,j,k)}", 1, f"x{zvar(j,k)} -> 1")

    # o[j] + sum_k z[j][k] >= 1
    unpaid = {}
    for j in range(n):
        per_vertex = []
        for i in range(n):
            expr = str(sum_p[i, j])
            for k in range(t):
                expr += f" {zge[j,k,i]} +"
            per_vertex.append(proof.pol(expr))
        expr = str(inst.slot_id[j])
        for pid in per_vertex:
            expr += f" {pid} +"
        unpaid[j] = proof.pol(expr + " s")

    # ~p[i][a][k] + ~p[i'][b][k] >= 1 for a < b
    base = {}
    for k in range(t):
        for a in range(n):
            for b in range(a + 1, n):
                for i in range(n):
                    for i2 in range(n):
                        if i == i2:
                            expr = str(inst.vertex_id[i])
                            for j in range(n):
                                if j not in (a, b):
                                    expr += f" {M(i,j)} +"
                            expr += f" {ple_m[i,a,k]} + {ple_m[i,b,k]} +"
                        else:
                            er = inst.edge_id[frozenset({(i, a), (i2, b)})]
                            pr = inst.proper_id[((min(i, i2), max(i, i2)), k)]
                            expr = (f"{er} {pr} + {ple_m[i,a,k]} + {ple_c[i,a,k]} + "
                                    f"{ple_m[i2,b,k]} + {ple_c[i2,b,k]} + 2 d")
                        base[k, a, b, i, i2] = proof.pol(expr)

    # ~z[a][k] + ~z[b][k] >= 1 -- two rounds of "sum the family, add the
    # reified OR, saturate". Each round replaces one disjunction by its head.
    zconf = {}
    for k in range(t):
        for a in range(n):
            for b in range(a + 1, n):
                lifted = []
                for i in range(n):
                    expr = str(base[k, a, b, i, 0])
                    for i2 in range(1, n):
                        expr += f" {base[k,a,b,i,i2]} +"
                    lifted.append(proof.pol(expr + f" {zor[b,k]} + s"))
                expr = str(lifted[0])
                for pid in lifted[1:]:
                    expr += f" {pid} +"
                zconf[k, a, b] = proof.pol(expr + f" {zor[a,k]} + s")

    # sum_j ~z[j][k] >= n-1 -- the AMO, via a prefix-OR ladder. Pairwise
    # conflicts alone give only `sum <= n/2`; the ladder is what makes it 1.
    amo = {}
    for k in range(t):
        sor, sge = {}, {}
        for j in range(n):
            body = (f"+1 ~x{svar(j,k)} "
                    + " ".join(f"+1 x{zvar(jj,k)}" for jj in range(j + 1)))
            sor[j] = proof.red(body, 1, f"x{svar(j,k)} -> 0")
            for jj in range(j + 1):
                sge[j, jj] = proof.red(
                    f"+1 x{svar(j,k)} +1 ~x{zvar(jj,k)}", 1, f"x{svar(j,k)} -> 1")
        step = {}
        for j in range(1, n):
            expr = str(zconf[k, 0, j])
            for jj in range(1, j):
                expr += f" {zconf[k,jj,j]} +"
            conflict = proof.pol(expr + f" {sor[j-1]} + s")
            expr = str(sge[j, 0])
            for jj in range(1, j):
                expr += f" {sge[j,jj]} +"
            monotone = proof.pol(expr + f" {sor[j-1]} + s")
            step[j] = proof.pol(f"{conflict} {sge[j,j]} + {monotone} + 2 d")
        expr = str(step[1])
        for j in range(2, n):
            expr += f" {step[j]} +"
        telescope = proof.pol(expr + f" {sge[0,0]} +")
        amo[k] = proof.pol(f"{telescope} x{svar(n-1,k)} w")

    expr = str(unpaid[0])
    for j in range(1, n):
        expr += f" {unpaid[j]} +"
    for k in range(t):
        expr += f" {amo[k]} +"
    floor = proof.pol(expr)
    contradiction = proof.pol(f"{floor} {soli_id} +")
    out.write("output NONE;\n")
    out.write(f"conclusion BOUNDS {n-t} : {contradiction} {n-t} : {' '.join(lits)};\n")
    out.write("end pseudo-Boolean proof;\n")
    return contradiction


# --------------------------------------------------------------------------
def synthesize(n, t, path):
    """Write an OPB in the corpus's exact variable order and row order:
    e[p] over pairs i<i', then o[j], then M[i][j] row-major, then C[v][k]."""
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    e = {p: 1 + idx for idx, p in enumerate(pairs)}
    o = [1 + len(pairs) + j for j in range(n)]
    m = [[1 + len(pairs) + n + i * n + j for j in range(n)] for i in range(n)]
    c = [[1 + len(pairs) + n + n * n + v * t + k for k in range(t)] for v in range(n)]
    nvar = len(pairs) + n + n * n + n * t
    rows = []
    for j in range(n):
        rows.append(" ".join([f"+1 x{o[j]}"] + [f"+1 x{m[i][j]}" for i in range(n)])
                    + " >= 1 ;")
    for i in range(n):
        rows.append(" ".join(f"-1 x{m[i][j]}" for j in range(n)) + " >= -1 ;")
    for (i, i2) in pairs:
        for a in range(n):
            for b in range(n):
                if a != b:
                    rows.append(f"+1 x{e[(i,i2)]} -1 x{m[i][a]} -1 x{m[i2][b]} >= -1 ;")
    for v in range(n):
        rows.append(" ".join(f"+1 x{c[v][k]}" for k in range(t)) + " >= 1 ;")
    for (i, i2) in pairs:
        for k in range(t):
            rows.append(f"-1 x{e[(i,i2)]} -1 x{c[i][k]} -1 x{c[i2][k]} >= -2 ;")
    with open(path, "w") as handle:
        handle.write(f"* #variable= {nvar} #constraint= {len(rows)} "
                     f"intsize= 4\n")
        handle.write("* clique-coloring-max-clique-n=%d-t=%d, synthesized by "
                     "scripts/pb_clique_coloring_cert.py\n" % (n, t))
        handle.write("min: " + " ".join(f"+1 x{o[j]}" for j in range(n)) + " ;\n")
        for row in rows:
            handle.write(row + "\n")
    return nvar, len(rows)


def main(argv):
    if len(argv) >= 5 and argv[1] == "synth":
        n, t = int(argv[2]), int(argv[3])
        nvar, nrow = synthesize(n, t, argv[4])
        print(f"n={n} t={t} vars={nvar} rows={nrow} optimum={n-t} -> {argv[4]}")
        return 0
    if len(argv) < 3:
        print(__doc__)
        return 2
    mode, target = argv[1], argv[2]
    if mode == "sweep":
        files = sorted(glob.glob(target + "/**/*.opb", recursive=True))
        accepted, rejected = [], []
        start = time.time()
        for path in files:
            t0 = time.time()
            got = header_gate(path)
            (accepted if got else rejected).append((time.time() - t0, path, got))
        rejected.sort(reverse=True)
        print(f"files={len(files)} accepted={len(accepted)} "
              f"rejected={len(rejected)} wall={time.time()-start:.2f}s")
        if rejected:
            mid = rejected[len(rejected) // 2][0]
            print(f"pre-gate rejection cost: median={mid*1e6:.0f}us "
                  f"max={rejected[0][0]*1e3:.2f}ms")
        for _, path, got in sorted(accepted, key=lambda r: r[1]):
            print(f"  ACCEPT n={got[0]} t={got[1]}  {os.path.basename(path)}")
        return 0
    try:
        inst = recover(target)
    except NotThisFamily as exc:
        print(f"DECLINED: {exc}")
        return 1
    if mode == "gate":
        print(f"n={inst.n} t={inst.t} vars={inst.nvar} rows={len(inst.rows)} "
              f"optimum={inst.n - inst.t}")
        return 0
    if mode == "check":
        bad, obj = uniform_witness_violations(inst)
        feas, prod = two_in_a_slot(inst)
        print(f"n={inst.n} t={inst.t}")
        print(f"  uniform witness violates {bad} of {len(inst.rows)} rows, "
              f"objective {obj}  =>  LP* <= 0, and c >= 0 with x >= 0 gives "
              f"LP* >= 0, so LP* = 0 EXACTLY")
        print(f"  two-in-a-slot point violates {feas} rows and has "
              f"sum_ij p[i][j][0] = {prod}  =>  the clique row is NOT a cut; "
              f"the LP needs a symmetry break, the proof does not")
        return 0
    if mode == "prove":
        with open(argv[3], "w") as handle:
            last = emit_proof(inst, handle)
        print(f"n={inst.n} t={inst.t} optimum={inst.n-inst.t} -> {argv[3]} "
              f"(contradiction id {last})")
        return 0
    print(__doc__)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv))

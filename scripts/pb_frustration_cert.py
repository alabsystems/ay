#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
"""Frustrated-cycle optimality certificates for the signed-graph (sign
consistency / FRUSTRATION INDEX) family: `macrophage`, `methanosarcina`.

WHY THIS EXISTS.  These instances have `LP* = 0` EXACTLY -- the half-integral
point (every sign variable 1/2, every error variable 0) satisfies every row with
objective 0, and every objective coefficient is +1 with x >= 0, so `LP* = 0` is
pinned from both sides in exact rational arithmetic.  Weak duality therefore caps
EVERY LP-dual floor at `ceil(0) = 0 < 374`, permanently.  `macrophage` was the
named exemplar of the "genuine converged integrality gap" class: the class the
project assumed was uncertifiable.

That is a fact about LP DUALITY, not about the proof system.  Cutting planes has
SATURATION and DIVISION, neither of which has an LP dual, and with them a
frustrated cycle's inequality is THREE `pol` lines:

    A' = (one row per edge, one polarity) summed, then `s`   ->  sum_C e +  v1 >= 1
    B' = the mirrored sum,                     then `s`      ->  sum_C e + ~v1 >= 1
    A' + B' = 2 sum_C e + 1 >= 2 = 2 sum_C e >= 1  --`2 d`-->  sum_C e >= 1

The un-saturated sums are `sum_C e + 2*v1 >= 1` and `sum_C e + 2*~v1 >= 1`; the
`+2` is exactly the residue of a cycle whose sign product is -1.  Saturation is
what removes it, and saturation is the operation the LP cannot perform.  This is
the same shape as `pb_clique_coloring_cert.py`: where the LP formulation needs a
lift or a symmetry break, the proof spends one `s` and one `d`.

THE BOUND.  Frustrated cycles are separated exactly in the signed DOUBLE COVER
(two copies of each node; a DIFFER edge crosses copies, an EQUAL edge does not),
where a frustrated closed walk through `v` is a path `(v,0) -> (v,1)`.  The
fractional cycle PACKING over the separated pool is the certificate's multiplier
vector, and its value is a valid lower bound on the optimum for ANY non-negative
packing -- nothing has to converge for the emitted proof to be sound.

  measured, `macrophage`: the cycle relaxation converges at 1120/3 = 373.333...,
  and `ceil(1120/3) = 374` is the optimum.  So the cut family that the LP cannot
  see is EXACTLY strong enough, to the unit.

WHAT IS FAIL-CLOSED.  The recognizer accounts for EVERY row against the two
templates and raises if one is unexplained.  Every emitted `pol` line is
re-derived here in exact integer arithmetic under VeriPB's own literal-normal-form
semantics (add with x/~x cancellation, saturate, divide with rounding up) and
compared against what the line must produce; a mismatch raises before anything is
written.  The packing is re-checked exactly after rounding: no edge may carry more
than the denominator.

VERIFY WHAT IT WRITES WITH THE PINNED CHECKER ONLY (`ci/veripb.pin`).

USAGE
  pb_frustration_cert.py recover  FILE.opb
  pb_frustration_cert.py lpstar   FILE.opb              # the exact LP* = 0 witness
  pb_frustration_cert.py pool     FILE.opb POOL.pkl SECONDS
  pb_frustration_cert.py prove    FILE.opb POOL.pkl OUT.pbp DENOM LITS_FILE UB

Needs scipy (HiGHS) for the separation LP only: the LP chooses WHICH cycles to
pack and with what weights, and every choice it makes is then re-verified in
exact arithmetic.  A wrong LP answer can only make the emitted bound weaker or
make this script raise -- it can never make an unsound proof.
"""


def parse(path):
    obj = {}
    rows = []
    nv = None
    with open(path) as fh:
        for line in fh:
            line = line.strip()
            if not line or line.startswith('*'):
                if line.startswith('* #variable'):
                    nv = int(line.split('#variable=')[1].split()[0])
                continue
            if line.startswith('min:'):
                body = line[4:].strip().rstrip(';').split()
                for i in range(0, len(body), 2):
                    obj[body[i+1]] = obj.get(body[i+1], 0) + int(body[i])
                continue
            t = line.rstrip(';').split()
            rel, rhs = t[-2], int(t[-1])
            assert rel == '>=', rel
            terms = {}
            body = t[:-2]
            for i in range(0, len(body), 2):
                terms[body[i+1]] = terms.get(body[i+1], 0) + int(body[i])
            rows.append((terms, rhs))
    return obj, rows, nv


import sys, os, time, heapq, collections, pickle
from fractions import Fraction
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))


# ---------------------------------------------------------------- recovery
class Sign:
    def __init__(self, path):
        obj, rows, nv = parse(path)
        if not obj or any(c != 1 for c in obj.values()):
            raise SystemExit('objective is not a plain sum of unit payments')
        self.path, self.obj, self.rows, self.nv = path, obj, rows, nv
        objvars = set(obj)
        by = collections.defaultdict(list)
        for rid, (terms, rhs) in enumerate(rows, start=1):     # VeriPB ids are 1-based
            errs = [v for v in terms if v in objvars]
            if len(errs) != 1:
                raise SystemExit(f'row {rid}: {len(errs)} objective vars')
            by[errs[0]].append((rid, terms, rhs))
        self.edge = {}     # e -> (u, v, kind)
        self.rowof = {}    # (e, u, coef_at_u) -> rid
        for e, rr in by.items():
            if len(rr) != 2:
                raise SystemExit(f'{e}: {len(rr)} rows')
            pairs = []
            for rid, terms, rhs in rr:
                rest = sorted((v, c) for v, c in terms.items() if v != e)
                if terms[e] != 1 or len(rest) != 2:
                    raise SystemExit(f'{e}: bad row shape')
                pairs.append((rid, rest, rhs))
            (u, cu0), (v, cv0) = pairs[0][1]
            (u1, cu1), (v1, cv1) = pairs[1][1]
            if (u, v) != (u1, v1):
                raise SystemExit(f'{e}: rows over different pairs')
            cs = {(cu0, cv0), (cu1, cv1)}
            if cs == {(-1, 1), (1, -1)} and pairs[0][2] == pairs[1][2] == 0:
                kind = 'EQUAL'
            elif cs == {(1, 1), (-1, -1)} and sorted([pairs[0][2], pairs[1][2]]) == [-1, 1]:
                kind = 'DIFFER'
            else:
                raise SystemExit(f'{e}: unknown template {pairs}')
            self.edge[e] = (u, v, kind)
            for rid, rest, rhs in pairs:
                self.rowof[(e, rest[0][0], rest[0][1])] = rid
                self.rowof[(e, rest[1][0], rest[1][1])] = rid
        self.nodes = sorted({n for u, v, _ in self.edge.values() for n in (u, v)},
                            key=lambda s: int(s[1:]))
        self.eids = sorted(self.edge, key=lambda s: int(s[1:]))
        if len(self.eids) + len(self.nodes) != nv:
            raise SystemExit('variables unaccounted for')
        if 2 * len(self.eids) != len(rows):
            raise SystemExit('rows unaccounted for')


# ---------------------------------------------- VeriPB literal-normal-form PB
class PB:
    """Constraint over LITERALS with non-negative coefficients, `>= degree`."""
    __slots__ = ('c', 'd')

    def __init__(self, c=None, d=0):
        self.c = dict(c or {})
        self.d = d

    @staticmethod
    def from_row(terms, rhs):
        c, d = {}, rhs
        for v, k in terms.items():
            if k >= 0:
                c[v] = c.get(v, 0) + k
            else:
                c['~' + v] = c.get('~' + v, 0) - k
                d += -k
        return PB({k: v for k, v in c.items() if v}, d)

    @staticmethod
    def axiom(lit):
        return PB({lit: 1}, 0)

    def __add__(self, o):
        c = dict(self.c)
        d = self.d + o.d
        for l, k in o.c.items():
            c[l] = c.get(l, 0) + k
        # cancel x / ~x
        for l in [l for l in c if not l.startswith('~')]:
            n = '~' + l
            if n in c:
                m = min(c[l], c[n])
                c[l] -= m; c[n] -= m; d -= m
                if not c[l]: del c[l]
                if not c[n]: del c[n]
        return PB({k: v for k, v in c.items() if v}, d)

    def mul(self, k):
        return PB({l: v * k for l, v in self.c.items()}, self.d * k)

    def sat(self):
        d = self.d
        return PB({l: min(v, d) for l, v in self.c.items()}, d)

    def div(self, k):
        return PB({l: -(-v // k) for l, v in self.c.items()}, -(-self.d // k))

    def key(self):
        return (tuple(sorted(self.c.items())), self.d)


# ------------------------------------------------------------- cycle finding
def double_cover(sg):
    nidx = {n: i for i, n in enumerate(sg.nodes)}
    eidx = {e: i for i, e in enumerate(sg.eids)}
    adj = collections.defaultdict(list)
    for e, (u, v, kind) in sg.edge.items():
        iu, iv, ie = nidx[u], nidx[v], eidx[e]
        cr = 1 if kind == 'DIFFER' else 0
        for L in (0, 1):
            adj[(iu, L)].append((iv, L ^ cr, ie))
            adj[(iv, L)].append((iu, L ^ cr, ie))
    return nidx, eidx, adj


def find_cycles(sg, x, adj, nidx, limit=1.0 - 1e-7):
    """Shortest frustrated closed walk through each node under weights `x`.
    Returns SIMPLE frustrated cycles only, as ordered edge-index lists."""
    out, seen = [], set()
    n = len(sg.nodes)
    rev = {i: n for n, i in nidx.items()}
    for src in range(n):
        dist = {(src, 0): 0.0}; prev = {}; pq = [(0.0, src, 0)]; tgt = (src, 1); best = None
        while pq:
            d, a, L = heapq.heappop(pq)
            if d > dist.get((a, L), 1e18) + 1e-12: continue
            if (a, L) == tgt: best = d; break
            if d >= limit: break
            for (b, L2, ie) in adj[(a, L)]:
                nd = d + x[ie]
                if nd < dist.get((b, L2), 1e18) - 1e-12:
                    dist[(b, L2)] = nd; prev[(b, L2)] = (a, L, ie)
                    heapq.heappush(pq, (nd, b, L2))
        if best is None or best >= limit: continue
        cur, seq = tgt, []
        while cur != (src, 0):
            p = prev[cur]; seq.append((p[2], p[0]))   # (edge, from-node-index)
            cur = (p[0], p[1])
        seq.reverse()
        ei = [e for e, _ in seq]
        nn = [a for _, a in seq]
        if len(set(nn)) != len(nn) or len(set(ei)) != len(ei):
            continue                                   # not a simple cycle: skip
        key = tuple(sorted(ei))
        if key in seen: continue
        seen.add(key)
        out.append(tuple(ei))
    return out


def order_cycle(sg, eidx_rev, ecycle):
    """(edge-name, node-name) walk for a simple cycle given as edge indices."""
    edges = [eidx_rev[i] for i in ecycle]
    inc = collections.defaultdict(list)
    for e in edges:
        u, v, _ = sg.edge[e]
        inc[u].append(e); inc[v].append(e)
    if any(len(l) != 2 for l in inc.values()):
        return None
    start = sg.edge[edges[0]][0]
    walk, cur, used = [], start, set()
    while True:
        nxt = [e for e in inc[cur] if e not in used]
        if not nxt:
            break
        e = nxt[0]; used.add(e)
        u, v, _ = sg.edge[e]
        other = v if u == cur else u
        walk.append((e, cur, other))
        cur = other
        if cur == start:
            break
    if len(walk) != len(edges) or cur != start:
        return None
    ndiff = sum(1 for e, _, _ in walk if sg.edge[e][2] == 'DIFFER')
    if ndiff % 2 == 0:
        return None                                    # balanced: not a cut
    return walk


# ------------------------------------------------------------------- emitter
class Proof:
    def __init__(self, out, f_count):
        self.out, self.next = out, f_count + 1
        out.write('pseudo-Boolean proof version 3.0\n')
        out.write(f'f {f_count} ;\n')

    def pol(self, expr):
        self.out.write('pol ' + expr + ' ;\n')
        self.next += 1
        return self.next - 1


def cycle_cut(sg, walk, db, proof):
    """Emit the 3 pol lines for one frustrated cycle; return the cut id.
    Every intermediate is recomputed here and asserted."""
    ids = {}
    for pol in (+1, -1):
        s = pol
        chain = []
        for (e, a, b) in walk:
            rid = sg.rowof[(e, a, s)]
            chain.append(rid)
            kind = sg.edge[e][2]
            s = s * (1 if kind == 'EQUAL' else -1)
        acc = db[chain[0]]
        for rid in chain[1:]:
            acc = acc + db[rid]
        want_lit = walk[0][1] if pol == +1 else '~' + walk[0][1]
        want = {f'{e}': 1 for e, _, _ in walk}
        want[want_lit] = 2
        if acc.key() != PB(want, 1).key():
            raise SystemExit(f'cycle sum mismatch: {acc.c} >= {acc.d}')
        sat = acc.sat()
        want[want_lit] = 1
        if sat.key() != PB(want, 1).key():
            raise SystemExit('saturation mismatch')
        expr = ' '.join(str(chain[0]) if i == 0 else f'{r} +' for i, r in enumerate(chain)) + ' s'
        ids[pol] = proof.pol(expr)
        db[ids[pol]] = sat
    total = db[ids[+1]] + db[ids[-1]]
    want = {f'{e}': 2 for e, _, _ in walk}
    if total.key() != PB(want, 1).key():
        raise SystemExit(f'A+B mismatch: {total.c} >= {total.d}')
    cut = total.div(2)
    if cut.key() != PB({f'{e}': 1 for e, _, _ in walk}, 1).key():
        raise SystemExit('division mismatch')
    cid = proof.pol(f'{ids[+1]} {ids[-1]} + 2 d')
    db[cid] = cut
    return cid


# ------------------------------------------------------------------- driver
def packing(cycles, nedge, denom):
    """max sum lambda_C  s.t.  sum_{C ni e} lambda_C <= 1.  Returns integer
    numerators over `denom` that are re-verified EXACTLY."""
    import numpy as np
    from scipy.optimize import linprog
    m = len(cycles)
    A = np.zeros((nedge, m))
    for j, cc in enumerate(cycles):
        for e in cc:
            A[e, j] = 1.0
    res = linprog(-np.ones(m), A_ub=A, b_ub=np.ones(nedge),
                  bounds=[(0, None)] * m, method='highs')
    assert res.status == 0, res.message
    lam = res.x
    num = [int(v * denom) for v in lam]                  # round DOWN
    load = collections.Counter()
    for j, cc in enumerate(cycles):
        if num[j]:
            for e in cc:
                load[e] += num[j]
    for e, v in load.items():
        assert v <= denom, 'rounding did not preserve feasibility'
    # greedy repair: raise numerators while every edge stays within denom
    improved = True
    while improved:
        improved = False
        for j, cc in enumerate(cycles):
            room = min(denom - load[e] for e in cc)
            if room > 0:
                num[j] += room
                for e in cc:
                    load[e] += room
                improved = True
    for e, v in load.items():
        assert v <= denom
    return num, load, -res.fun


def emit(argv):
    import numpy as np
    path, out_path, denom, rounds = argv[1], argv[2], int(argv[3]), int(argv[4])
    ckpt = argv[5] if len(argv) > 5 else None
    sg = Sign(path)
    print(f'RECOVERED {os.path.basename(path)}: edges={len(sg.eids)} nodes={len(sg.nodes)} '
          f'rows={len(sg.rows)} vars={sg.nv}', flush=True)
    nidx, eidx, adj = double_cover(sg)
    eidx_rev = {i: e for e, i in eidx.items()}
    n = len(sg.eids)

    pool, poolset = [], set()
    x = np.zeros(n)
    if ckpt and os.path.exists(ckpt):
        st = pickle.load(open(ckpt, 'rb'))
        x = st.get('x')
        if x is None:
            x = np.zeros(n)
        for cc in st['rows']:
            w = order_cycle(sg, eidx_rev, cc)
            if w is not None and tuple(sorted(cc)) not in poolset:
                poolset.add(tuple(sorted(cc))); pool.append(cc)
        print(f'checkpoint: {len(st["rows"])} cut sets -> {len(pool)} simple frustrated cycles',
              flush=True)
    from scipy.optimize import linprog
    t0 = time.time()
    for r in range(rounds):
        cyc = find_cycles(sg, x, adj, nidx)
        new = [c for c in cyc if tuple(sorted(c)) not in poolset]
        for c in new:
            poolset.add(tuple(sorted(c))); pool.append(c)
        if not new:
            print(f'round {r}: separation found nothing new', flush=True)
            break
        A = np.zeros((len(pool), n))
        for i, cc in enumerate(pool):
            for e in cc: A[i, e] = -1.0
        res = linprog(np.ones(n), A_ub=A, b_ub=-np.ones(len(pool)),
                      bounds=[(0, 1)] * n, method='highs')
        x = res.x
        print(f'round {r}: pool={len(pool)}  coverLP={res.fun:.4f}  [{time.time()-t0:.0f}s]',
              flush=True)

    num, load, lpval = packing(pool, n, denom)
    P = sum(num)
    L = P // denom
    print(f'PACKING LP = {lpval:.6f}   rounded to /{denom}: P={P} -> bound '
          f'{Fraction(P, denom)} = {L} (floor)   cycles used={sum(1 for v in num if v)}',
          flush=True)

    db = {i: PB.from_row(t, r) for i, (t, r) in enumerate(sg.rows, start=1)}
    t1 = time.time()
    with open(out_path, 'w') as fh:
        proof = Proof(fh, len(sg.rows))
        used = []
        for j, cc in enumerate(pool):
            if not num[j]:
                continue
            w = order_cycle(sg, eidx_rev, cc)
            cid = cycle_cut(sg, w, db, proof)
            used.append((cid, num[j], cc))
        # combine
        expr = f'{used[0][0]} {used[0][1]} *'
        acc = db[used[0][0]].mul(used[0][1])
        for cid, k, _ in used[1:]:
            expr += f' {cid} {k} * +'
            acc = acc + db[cid].mul(k)
        for e in sg.eids:
            a = acc.c.get(e, 0)
            if a < denom:
                expr += f' {e} {denom - a} * +'
                acc = acc + PB.axiom(e).mul(denom - a)
        assert all(acc.c.get(e, 0) == denom for e in sg.eids), 'slack fill failed'
        assert acc.d == P, (acc.d, P)
        summed = proof.pol(expr); db[summed] = acc
        floor = acc.div(denom)
        assert all(v == 1 for v in floor.c.values()) and set(floor.c) == set(sg.eids)
        assert floor.d == -(-P // denom)
        fid = proof.pol(f'{summed} {denom} d'); db[fid] = floor
        LB = floor.d
        lits = open(argv[6]).read().split() if len(argv) > 6 else None
        fh.write('output NONE;\n')
        if lits:
            fh.write(f'conclusion BOUNDS {LB} : {fid} {argv[7]} : {" ".join(lits)};\n')
        else:
            fh.write(f'conclusion BOUNDS {LB} : {fid} INF;\n')
        fh.write('end pseudo-Boolean proof;\n')
    print(f'EMITTED {out_path}  lower bound = {LB}  lines={proof.next - len(sg.rows) - 1} '
          f'bytes={os.path.getsize(out_path)}  [{time.time()-t1:.1f}s]')



import sys, os, time, pickle, heapq, collections, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))


def walk_cycles(seq, sg, eidx_rev):
    """seq = [(edge_idx, from_node_idx)] closed walk.  Decompose into SIMPLE
    cycles; return the frustrated ones as edge-index tuples."""
    out = []
    stack = []          # (node, edge_into_it_index_in_seq)
    pos = {}
    cur = []
    for k, (e, a) in enumerate(seq):
        if a in pos:
            i = pos[a]
            cyc = cur[i:]
            for (_, b) in cyc:
                pos.pop(b, None)
            cur = cur[:i]
            if cyc:
                out.append(cyc)
        pos[a] = len(cur)
        cur.append((e, a))
    if cur:
        out.append(cur)
    res = []
    for cyc in out:
        es = [e for e, _ in cyc]
        if len(set(es)) != len(es) or len(es) < 2:
            continue
        nd = sum(1 for e in es if sg.edge[eidx_rev[e]][2] == 'DIFFER')
        if nd % 2 == 1:
            res.append(tuple(es))
    return res


def sep_all(sg, adj, x, eidx_rev, limit):
    out = []
    n = len(sg.nodes)
    for src in range(n):
        dist = {(src, 0): 0.0}; prev = {}; pq = [(0.0, src, 0)]; tgt = (src, 1); best = None
        while pq:
            d, a, L = heapq.heappop(pq)
            if d > dist.get((a, L), 1e18) + 1e-12: continue
            if (a, L) == tgt: best = d; break
            if d >= limit: break
            for (b, L2, ie) in adj[(a, L)]:
                nd = d + x[ie]
                if nd < dist.get((b, L2), 1e18) - 1e-12:
                    dist[(b, L2)] = nd; prev[(b, L2)] = (a, L, ie)
                    heapq.heappush(pq, (nd, b, L2))
        if best is None or best >= limit: continue
        cur, seq = tgt, []
        while cur != (src, 0):
            p = prev[cur]; seq.append((p[2], p[0])); cur = (p[0], p[1])
        seq.reverse()
        out.extend(walk_cycles(seq, sg, eidx_rev))
    return out


def packbound(pool, n):
    m = len(pool)
    A = np.zeros((n, m))
    for j, cc in enumerate(pool):
        for e in cc: A[e, j] = 1.0
    r = linprog(-np.ones(m), A_ub=A, b_ub=np.ones(n), bounds=[(0, None)] * m, method='highs')
    assert r.status == 0
    return -r.fun


def grow(path, ckpt, budget_s):
    sg = Sign(path)
    nidx, eidx, adj = double_cover(sg)
    eidx_rev = {i: e for e, i in eidx.items()}
    n = len(sg.eids)
    pool, poolset = [], set()
    if os.path.exists(ckpt):
        st = pickle.load(open(ckpt, 'rb'))
        pool = st['pool']; poolset = set(tuple(sorted(c)) for c in pool)
        print(f'resumed pool={len(pool)}', flush=True)
    x = np.zeros(n)
    t0 = time.time(); r = 0; best = 0.0
    while time.time() - t0 < budget_s:
        found = sep_all(sg, adj, x, eidx_rev, 1.0 - 1e-7)
        if r % 3 == 2:               # diversify
            xp = np.clip(x + np.random.uniform(-0.25, 0.25, n), 0, 1)
            found += sep_all(sg, adj, xp, eidx_rev, 1.0 - 1e-7)
        new = 0
        for c in found:
            k = tuple(sorted(c))
            if k not in poolset:
                poolset.add(k); pool.append(c); new += 1
        # cover LP over the pool -> next x
        A = np.zeros((len(pool), n))
        for i, cc in enumerate(pool):
            for e in cc: A[i, e] = -1.0
        res = linprog(np.ones(n), A_ub=A, b_ub=-np.ones(len(pool)),
                      bounds=[(0, 1)] * n, method='highs')
        assert res.status == 0
        x = res.x
        print(f'r{r}: +{new} pool={len(pool)} coverLP={res.fun:.4f} [{time.time()-t0:.0f}s]',
              flush=True)
        pickle.dump({'pool': pool}, open(ckpt, 'wb'))
        if new == 0:
            print('CONVERGED: no violated frustrated cycle'); break
        r += 1
    pb = packbound(pool, n)
    print(f'FINAL pool={len(pool)}  packing LP = {pb:.6f}')
    pickle.dump({'pool': pool}, open(ckpt, 'wb'))




# --------------------------------------------------------------------------
def cli(argv):
    from fractions import Fraction as Fr
    if len(argv) < 3:
        raise SystemExit(__doc__)
    mode = argv[1]
    if mode == 'recover':
        sg = Sign(argv[2])
        eq = sum(1 for _, _, k in sg.edge.values() if k == 'EQUAL')
        print(f'edges={len(sg.eids)} (EQUAL={eq} DIFFER={len(sg.eids)-eq}) '
              f'nodes={len(sg.nodes)} rows={len(sg.rows)} vars={sg.nv}')
        return 0
    if mode == 'lpstar':
        sg = Sign(argv[2])
        val = {e: Fr(0) for e in sg.eids}
        for n in sg.nodes:
            val[n] = Fr(1, 2)
        bad = sum(1 for t, r in sg.rows if sum(c * val[v] for v, c in t.items()) < r)
        if bad:
            print(f'NOT THIS FAMILY: the half-integral witness violates {bad} rows')
            return 1
        print(f'half-integral witness violates 0 of {len(sg.rows)} rows at objective '
              f'{sum(val[e] for e in sg.eids)}; all objective coefficients are +1 and '
              f'x >= 0, so LP* = 0 EXACTLY')
        return 0
    if mode == 'pool':
        grow(argv[2], argv[3], float(argv[4]))
        return 0
    if mode == 'prove':
        # POOL.pkl holds {'pool': [...]}; the emitter reads {'rows': [...]}
        st = pickle.load(open(argv[3], 'rb'))
        rows_path = argv[3] + '.rows'
        pickle.dump({'rows': st['pool'], 'x': None}, open(rows_path, 'wb'))
        emit(['', argv[2], argv[4], argv[5], '0', rows_path] + list(argv[6:8]))
        return 0
    raise SystemExit(__doc__)


if __name__ == '__main__':
    sys.exit(cli(sys.argv))

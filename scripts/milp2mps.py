#!/usr/bin/env python3
# ay-script: milp2mps
"""milp2mps.py — convert the downstream optimization consumer's `.milp` serialization to standard MPS.

Each numeric field in `.milp` is an IEEE-754 f64 stored as its 16-hex-digit bit
pattern. We decode to a Python float, then emit its EXACT decimal expansion
(`decimal.Decimal(f)`) into the MPS. That makes ay's exact-rational MPS reader
and HiGHS's float MPS reader see the identical number: ay parses the exact
decimal to the exact dyadic rational that IS the f64, and HiGHS rounds the same
decimal back to the same nearest f64. Emitting a short repr (e.g. "0.1") would
instead give ay the rational 1/10 and HiGHS the f64 0.1000...055 — different
instances, spurious disagreements.

Row `lb..ub`:
  lb == ub            -> E row, rhs = lb
  lb == -inf, ub fin  -> L row, rhs = ub
  lb fin,     ub +inf -> G row, rhs = lb
  both finite, lb<ub  -> G row, rhs = lb, RANGES = ub - lb
  both infinite       -> dropped (constrains nothing)

Usage: milp2mps.py in.milp > out.mps
"""
import sys
import struct
from decimal import Decimal

NEG_INF = float("-inf")
POS_INF = float("inf")


def h2f(h: str) -> float:
    return struct.unpack(">d", bytes.fromhex(h))[0]


def dec(f: float) -> str:
    # Exact decimal of the f64 (finite dyadic rational). Never inf/nan here.
    return format(Decimal(f), "f")


def parse(path):
    lines = [ln.rstrip("\n") for ln in open(path)]
    it = iter(lines)
    assert next(it).strip().startswith("milp"), "not a .milp file"
    cols = []  # (lb, ub, obj, integral)
    rows = []  # (lb, ub, [(col, coeff), ...])
    ncols = 0
    for ln in it:
        s = ln.split("#", 1)[0].split()
        if not s:
            continue
        if s[0] == "cols":
            ncols = int(s[1])
            for _ in range(ncols):
                cs = next(it).split("#", 1)[0].split()
                lb, ub, obj, integral = h2f(cs[0]), h2f(cs[1]), h2f(cs[2]), cs[3] == "1"
                cols.append((lb, ub, obj, integral))
        elif s[0] == "rows":
            nrows = int(s[1])
            for _ in range(nrows):
                rs = next(it).split("#", 1)[0].split()
                lb, ub = h2f(rs[0]), h2f(rs[1])
                nnz = int(rs[2])
                terms = []
                k = 3
                for _ in range(nnz):
                    ci = int(rs[k])
                    cv = h2f(rs[k + 1])
                    terms.append((ci, cv))
                    k += 2
                rows.append((lb, ub, terms))
    return cols, rows


def emit(cols, rows, name="NY"):
    out = []
    out.append(f"NAME          {name}")
    out.append("OBJSENSE")
    out.append("    MIN")
    # ---- ROWS ----
    out.append("ROWS")
    out.append(" N  COST")
    row_meta = []  # (emitted, kind, rhs, range) index-aligned with `rows`; kind in {E,L,G,None}
    for i, (lb, ub, _terms) in enumerate(rows):
        if lb == NEG_INF and ub == POS_INF:
            row_meta.append((False, None, None, None))
            continue
        rn = f"R{i}"
        if lb == ub:
            out.append(f" E  {rn}")
            row_meta.append((True, "E", lb, None))
        elif lb == NEG_INF:
            out.append(f" L  {rn}")
            row_meta.append((True, "L", ub, None))
        elif ub == POS_INF:
            out.append(f" G  {rn}")
            row_meta.append((True, "G", lb, None))
        else:
            out.append(f" G  {rn}")
            row_meta.append((True, "G", lb, ub - lb))
    # ---- COLUMNS ---- (grouped per column; integer cols wrapped in markers)
    # Build per-column row incidence.
    col_terms = {j: [] for j in range(len(cols))}
    for i, (_lb, _ub, terms) in enumerate(rows):
        if not row_meta[i][0]:
            continue  # dropped free row
        for (ci, cv) in terms:
            col_terms[ci].append((f"R{i}", cv))
    out.append("COLUMNS")
    mk = 0
    for j, (_lb, _ub, obj, integral) in enumerate(cols):
        cn = f"X{j}"
        if integral:
            out.append(f"    MARKER{mk:04d}  'MARKER'  'INTORG'")
        # objective entry (always emit, forces column creation even if 0 and rowless)
        out.append(f"    {cn}  COST  {dec(obj)}")
        for (rn, cv) in col_terms[j]:
            out.append(f"    {cn}  {rn}  {dec(cv)}")
        if integral:
            out.append(f"    MARKER{mk:04d}  'MARKER'  'INTEND'")
            mk += 1
    # ---- RHS ----
    out.append("RHS")
    for i, (emitted, kind, rhs, _rng) in enumerate(row_meta):
        if not emitted:
            continue
        if rhs == 0.0:
            # still emit so the row is anchored; 0 rhs is default but explicit is safe
            out.append(f"    RHS  R{i}  0")
        else:
            out.append(f"    RHS  R{i}  {dec(rhs)}")
    # ---- RANGES ----
    rng_lines = [(i, r) for i, (emitted, _k, _rhs, r) in enumerate(row_meta) if emitted and r is not None]
    if rng_lines:
        out.append("RANGES")
        for i, r in rng_lines:
            out.append(f"    RNG  R{i}  {dec(r)}")
    # ---- BOUNDS ----
    out.append("BOUNDS")
    for j, (lb, ub, _obj, integral) in enumerate(cols):
        cn = f"X{j}"
        # normalize -0.0
        if lb == 0.0:
            lb = 0.0
        if ub == 0.0:
            ub = 0.0
        if integral:
            if lb == ub:
                out.append(f" FX BND  {cn}  {dec(lb)}")
            else:
                if lb == NEG_INF:
                    out.append(f" MI BND  {cn}")
                elif lb != 0.0:
                    out.append(f" LO BND  {cn}  {dec(lb)}")
                if ub == POS_INF:
                    out.append(f" PL BND  {cn}")
                else:
                    out.append(f" UP BND  {cn}  {dec(ub)}")
        else:
            if lb == ub:
                out.append(f" FX BND  {cn}  {dec(lb)}")
            elif lb == NEG_INF and ub == POS_INF:
                out.append(f" FR BND  {cn}")
            elif lb == NEG_INF:
                out.append(f" MI BND  {cn}")
                out.append(f" UP BND  {cn}  {dec(ub)}")
            elif ub == POS_INF:
                if lb != 0.0:
                    out.append(f" LO BND  {cn}  {dec(lb)}")
                # else default [0, +inf], emit nothing
            else:
                if lb != 0.0:
                    out.append(f" LO BND  {cn}  {dec(lb)}")
                out.append(f" UP BND  {cn}  {dec(ub)}")
    out.append("ENDATA")
    return "\n".join(out) + "\n"


if __name__ == "__main__":
    cols, rows = parse(sys.argv[1])
    sys.stdout.write(emit(cols, rows))

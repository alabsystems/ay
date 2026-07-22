# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
#
# Graph k-coloring in IDIOMATIC z3py. Each node gets an Int color in 0..k-1;
# adjacent nodes must differ. The same body runs on `import ayz3 as z` or
# `import z3 as z`.
#
# The default graph is the Petersen graph, whose chromatic number is 3: it is
# 3-colorable (sat) but NOT 2-colorable (unsat) — a clean sat/unsat boundary.
#
# Run directly to 3-color the Petersen graph on ayz3:
#     python -m examples.graph_coloring

# Petersen graph: 10 nodes, 15 edges. Outer 5-cycle, inner 5-cycle (pentagram),
# spokes connecting them.
PETERSEN_EDGES = [
    (0, 1), (1, 2), (2, 3), (3, 4), (4, 0),          # outer pentagon
    (5, 7), (7, 9), (9, 6), (6, 8), (8, 5),          # inner pentagram
    (0, 5), (1, 6), (2, 7), (3, 8), (4, 9),          # spokes
]
PETERSEN_NODES = 10


def solve(z, k, n_nodes=PETERSEN_NODES, edges=PETERSEN_EDGES):
    """Try to k-color the graph with SMT module `z` (ayz3 or z3py).

    Returns (result_str, coloring) where coloring[v] is node v's color (int) in
    0..k-1 when sat, else None.
    """
    color = [z.Int("c_%d" % v) for v in range(n_nodes)]

    s = z.Solver()

    # Each node's color is in 0..k-1.
    for v in range(n_nodes):
        s.add(color[v] >= 0, color[v] <= k - 1)

    # Adjacent nodes get different colors.
    for (u, v) in edges:
        s.add(color[u] != color[v])

    res = s.check()
    if str(res) != "sat":
        return str(res), None
    m = s.model()
    coloring = [m[color[v]].as_long() for v in range(n_nodes)]
    return "sat", coloring


def is_valid_coloring(coloring, k, n_nodes=PETERSEN_NODES, edges=PETERSEN_EDGES):
    """Independently VALIDATE a coloring."""
    if coloring is None or len(coloring) != n_nodes:
        return False
    for c in coloring:
        if not (0 <= c <= k - 1):
            return False
    for (u, v) in edges:
        if coloring[u] == coloring[v]:
            return False
    return True


if __name__ == "__main__":
    import ayz3 as z

    # NOTE: ayz3 binds a Solver to a Context whose assertion stack is shared, so
    # independent problems each need a fresh Context (z3py gives this for free).
    # We scope each solve here; the `solve` body itself stays z3py-identical.
    for k in (2, 3):
        with z._ctx_scope(z.Context()):
            res, coloring = solve(z, k)
        print("k=%d -> %s" % (k, res))
        if coloring:
            print("  coloring:", coloring)
            print("  valid:", is_valid_coloring(coloring, k))

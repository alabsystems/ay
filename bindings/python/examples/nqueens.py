# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
#
# The N-Queens problem in IDIOMATIC z3py. `Q[i]` is the column (0..N-1) of the
# queen on row i; queens on distinct columns (Distinct) and no two on the same
# diagonal. The same body runs on `import ayz3 as z` or `import z3 as z`.
#
# Run directly to place 8 queens on ayz3:
#     python -m examples.nqueens


def solve(z, n=8):
    """Place `n` non-attacking queens with SMT module `z` (ayz3 or z3py).

    Returns (result_str, placement) where placement[i] is the column of the
    queen on row i (a list of ints) when sat, else None.
    """
    Q = [z.Int("q_%d" % i) for i in range(n)]

    s = z.Solver()

    # Each queen sits in a valid column 0..n-1.
    for i in range(n):
        s.add(Q[i] >= 0, Q[i] <= n - 1)

    # No two queens share a column (one queen per row is implicit in the model).
    s.add(z.Distinct(Q))

    # No two queens share a diagonal: |Q[i]-Q[j]| != |i-j|.
    for i in range(n):
        for j in range(i + 1, n):
            s.add(Q[i] - Q[j] != i - j)
            s.add(Q[i] - Q[j] != j - i)

    res = s.check()
    if str(res) != "sat":
        return str(res), None
    m = s.model()
    placement = [m[Q[i]].as_long() for i in range(n)]
    return "sat", placement


def is_valid_solution(placement, n=8):
    """Independently VALIDATE an N-Queens placement."""
    if placement is None or len(placement) != n:
        return False
    for c in placement:
        if not (0 <= c <= n - 1):
            return False
    # Distinct columns.
    if len(set(placement)) != n:
        return False
    # No shared diagonals.
    for i in range(n):
        for j in range(i + 1, n):
            if abs(placement[i] - placement[j]) == abs(i - j):
                return False
    return True


if __name__ == "__main__":
    import ayz3 as z

    with z._ctx_scope(z.Context()):
        res, placement = solve(z, 8)
    print("result:", res)
    if placement:
        n = len(placement)
        for i in range(n):
            print("".join("Q" if placement[i] == c else "." for c in range(n)))
        print("placement:", placement)
        print("valid:", is_valid_solution(placement, n))

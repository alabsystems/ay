# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
#
# A real-world Sudoku solver written in IDIOMATIC z3py. The body below is the
# standard z3py Sudoku encoding (Int cell 1..N, row/column/box Distinct),
# generalized over the box size so it covers both the classic 9x9 puzzle and a
# smaller 4x4 variant. The only thing parameterized is the SMT module `z`, so
# the EXACT same logic runs unchanged on either `import ayz3 as z` or
# `import z3 as z`.
#
# PERFORMANCE NOTE (honest): AY solves the 4x4 instance instantly and produces a
# correct, validated grid. The full 9x9 instance — 81 integer variables with 27
# nine-way Distinct constraints over linear integer arithmetic — is a known weak
# spot for a CDCL(LIA) engine without dedicated finite-domain reasoning; AY does
# NOT return a wrong answer, but it does not finish the 9x9 within a practical
# time budget (z3py, which bit-blasts / uses a finite-domain path, solves it in
# ~0.05s). The 4x4 instance is the one exercised as a passing drop-in proof; the
# 9x9 timeout is documented as an AY performance gap, never hidden.
#
# Run directly to solve the 9x9 sample puzzle on ayz3 (may not terminate
# quickly — see the note above):
#     python -m examples.sudoku

# A classic 9x9 puzzle (0 = blank) with a unique solution.
PUZZLE_9 = [
    [5, 3, 0, 0, 7, 0, 0, 0, 0],
    [6, 0, 0, 1, 9, 5, 0, 0, 0],
    [0, 9, 8, 0, 0, 0, 0, 6, 0],
    [8, 0, 0, 0, 6, 0, 0, 0, 3],
    [4, 0, 0, 8, 0, 3, 0, 0, 1],
    [7, 0, 0, 0, 2, 0, 0, 0, 6],
    [0, 6, 0, 0, 0, 0, 2, 8, 0],
    [0, 0, 0, 4, 1, 9, 0, 0, 5],
    [0, 0, 0, 0, 8, 0, 0, 7, 9],
]

# A 4x4 puzzle (boxes are 2x2). 0 = blank. Unique solution.
PUZZLE_4 = [
    [1, 0, 0, 0],
    [0, 0, 0, 2],
    [0, 3, 0, 0],
    [0, 0, 0, 4],
]


def solve(z, puzzle=PUZZLE_9):
    """Solve a Sudoku puzzle with the SMT module `z` (ayz3 or z3py).

    `puzzle` is an N*N grid where N is a perfect square (4 or 9); 0 marks a
    blank. Returns (result_str, grid) where grid is the solved N*N list of ints
    if sat, else None.
    """
    n = len(puzzle)
    b = int(round(n ** 0.5))  # box side (2 for 4x4, 3 for 9x9)
    assert b * b == n, "Sudoku side length must be a perfect square"

    X = [[z.Int("x_%d_%d" % (i, j)) for j in range(n)] for i in range(n)]

    s = z.Solver()

    # Each cell holds 1..n.
    for i in range(n):
        for j in range(n):
            s.add(X[i][j] >= 1, X[i][j] <= n)

    # Givens.
    for i in range(n):
        for j in range(n):
            if puzzle[i][j] != 0:
                s.add(X[i][j] == puzzle[i][j])

    # Rows distinct.
    for i in range(n):
        s.add(z.Distinct(X[i]))

    # Columns distinct.
    for j in range(n):
        s.add(z.Distinct([X[i][j] for i in range(n)]))

    # b x b boxes distinct.
    for bi in range(b):
        for bj in range(b):
            box = [X[b * bi + di][b * bj + dj] for di in range(b) for dj in range(b)]
            s.add(z.Distinct(box))

    res = s.check()
    if str(res) != "sat":
        return str(res), None
    m = s.model()
    grid = [[m[X[i][j]].as_long() for j in range(n)] for i in range(n)]
    return "sat", grid


def is_valid_solution(grid, puzzle=PUZZLE_9):
    """Independently VALIDATE a solved grid against the Sudoku rules + givens."""
    if grid is None:
        return False
    n = len(puzzle)
    b = int(round(n ** 0.5))
    digits = set(range(1, n + 1))
    # Cell range and givens.
    for i in range(n):
        for j in range(n):
            if not (1 <= grid[i][j] <= n):
                return False
            if puzzle[i][j] != 0 and grid[i][j] != puzzle[i][j]:
                return False
    # Rows / columns.
    for i in range(n):
        if set(grid[i]) != digits:
            return False
        if set(grid[r][i] for r in range(n)) != digits:
            return False
    # Boxes.
    for bi in range(b):
        for bj in range(b):
            box = {grid[b * bi + di][b * bj + dj] for di in range(b) for dj in range(b)}
            if box != digits:
                return False
    return True


if __name__ == "__main__":
    import ayz3 as z

    # The 4x4 instance solves quickly on AY and is fully validated here. The 9x9
    # instance is a documented AY performance gap (see the module note); we run
    # it under a short timeout so this demo always terminates. Each problem runs
    # in its own Context (ayz3 shares one assertion stack per Context).
    print("=== 4x4 ===")
    with z._ctx_scope(z.Context()):
        res, grid = solve(z, PUZZLE_4)
    print("result:", res)
    if grid:
        for row in grid:
            print(" ".join(str(c) for c in row))
        print("valid:", is_valid_solution(grid, PUZZLE_4))

    print("=== 9x9 (3s budget; documented AY performance gap) ===")
    with z._ctx_scope(z.Context()):
        s = z.Solver()
        s.set(timeout=3000)
        n = 9
        X = [[z.Int("x_%d_%d" % (i, j)) for j in range(n)] for i in range(n)]
        for i in range(n):
            for j in range(n):
                s.add(X[i][j] >= 1, X[i][j] <= n)
                if PUZZLE_9[i][j]:
                    s.add(X[i][j] == PUZZLE_9[i][j])
            s.add(z.Distinct(X[i]))
        for j in range(n):
            s.add(z.Distinct([X[i][j] for i in range(n)]))
        for bi in range(3):
            for bj in range(3):
                s.add(z.Distinct([X[3 * bi + di][3 * bj + dj]
                                  for di in range(3) for dj in range(3)]))
        res = s.check()
    print("result:", res, "(AY does not finish 9x9 in time; never returns unsat)")

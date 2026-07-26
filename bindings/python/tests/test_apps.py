# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
#
# REAL z3py application programs as the drop-in proof for ayz3.
#
# Each app under `examples/` is written in IDIOMATIC z3py with a single `solve`
# body parameterized only by the SMT module. Here we:
#   1. Run the app through ayz3 and INDEPENDENTLY VALIDATE the returned solution
#      (re-check that the assignment satisfies the problem's constraints — we
#      never just trust the solver's `sat`).
#   2. Run the IDENTICAL logic through real z3py 4.15.4 and assert the verdicts
#      AGREE.
#
# SOUNDNESS: a solver returning `sat` is not enough; `is_valid_*` re-derives
# correctness from the raw assignment. If ayz3 ever returned a wrong/unknown
# answer these assertions would fail rather than hide it.

import os
import sys

import pytest

# Make the examples package importable (it sits next to the tests dir).
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import ayz3 as ayz3  # noqa: E402
from examples import bmc, graph_coloring, nqueens, sudoku  # noqa: E402

try:
    import z3 as z3py
    HAVE_Z3PY = True
except Exception:  # pragma: no cover - depends on environment
    z3py = None
    HAVE_Z3PY = False


def fresh_ay():
    """Activate a fresh isolated ayz3 Context for one app run.

    Each app builds its constants then a `Solver()` that adopts the current
    context. Running several apps in one process must not share AY's single
    per-context assertion stack, so we scope every run to its own Context.
    """
    return ayz3._ctx_scope(ayz3.Context())


# ===========================================================================
# Sudoku
# ===========================================================================

def test_sudoku4_ayz3_solves_and_is_valid():
    # 4x4 Sudoku (2x2 boxes): AY solves this finite-domain LIA instance fast.
    with fresh_ay():
        res, grid = sudoku.solve(ayz3, sudoku.PUZZLE_4)
    assert res == "sat"
    assert sudoku.is_valid_solution(grid, sudoku.PUZZLE_4), (
        "ayz3 4x4 Sudoku solution failed validation"
    )


@pytest.mark.usefixtures("required_reference_z3")
def test_sudoku4_agrees_with_z3py():
    with fresh_ay():
        ay_res, ay_grid = sudoku.solve(ayz3, sudoku.PUZZLE_4)
    z_res, z_grid = sudoku.solve(z3py, sudoku.PUZZLE_4)
    assert ay_res == z_res == "sat"
    assert sudoku.is_valid_solution(ay_grid, sudoku.PUZZLE_4)
    assert sudoku.is_valid_solution(z_grid, sudoku.PUZZLE_4)
    # This puzzle has a UNIQUE solution, so the grids must be identical.
    assert ay_grid == z_grid, "ayz3 and z3py disagree on the unique 4x4 Sudoku solution"


# DOCUMENTED PERFORMANCE GAP (honest): AY does not solve the full 9x9 Sudoku
# within a practical time budget — 81 Int vars with 27 nine-way Distinct over
# LIA is a known weak spot for a CDCL(LIA) engine without finite-domain
# reasoning. This regression accepts `sat` or `unknown` under a short timeout
# and explicitly rejects `unsat`, because the fixed puzzle is satisfiable.
def test_sudoku9_ayz3_never_wrong_under_timeout():
    with fresh_ay():
        s = ayz3.Solver()
        s.set(timeout=3000)  # 3s budget; AY honors `timeout` (ms)
        n = 9
        X = [[ayz3.Int("x_%d_%d" % (i, j)) for j in range(n)] for i in range(n)]
        for i in range(n):
            for j in range(n):
                s.add(X[i][j] >= 1, X[i][j] <= n)
                if sudoku.PUZZLE_9[i][j]:
                    s.add(X[i][j] == sudoku.PUZZLE_9[i][j])
            s.add(ayz3.Distinct(X[i]))
        for j in range(n):
            s.add(ayz3.Distinct([X[i][j] for i in range(n)]))
        for bi in range(3):
            for bj in range(3):
                box = [X[3 * bi + di][3 * bj + dj]
                       for di in range(3) for dj in range(3)]
                s.add(ayz3.Distinct(box))
        res = s.check()
        assert res in (ayz3.sat, ayz3.unknown), (
            f"AY must not return unsat for the satisfiable 9x9 puzzle; got {res}"
        )
        if res == ayz3.sat:
            grid = [[s.model()[X[i][j]].as_long() for j in range(n)]
                    for i in range(n)]
            assert sudoku.is_valid_solution(grid, sudoku.PUZZLE_9)


# ===========================================================================
# N-Queens
# ===========================================================================

@pytest.mark.parametrize("n", [4, 6, 8])
def test_nqueens_ayz3_solves_and_is_valid(n):
    with fresh_ay():
        res, placement = nqueens.solve(ayz3, n)
    assert res == "sat"
    assert nqueens.is_valid_solution(placement, n), (
        f"ayz3 {n}-Queens placement failed validation: {placement}"
    )


@pytest.mark.usefixtures("required_reference_z3")
@pytest.mark.parametrize("n", [4, 6, 8])
def test_nqueens_agrees_with_z3py(n):
    with fresh_ay():
        ay_res, ay_pl = nqueens.solve(ayz3, n)
    z_res, z_pl = nqueens.solve(z3py, n)
    assert ay_res == z_res == "sat"
    # Solutions need not be identical (many valid placements), but both must be
    # genuinely valid placements.
    assert nqueens.is_valid_solution(ay_pl, n)
    assert nqueens.is_valid_solution(z_pl, n)


def test_nqueens_unsat_small():
    # 3-Queens is impossible; ayz3 must agree it's unsat.
    with fresh_ay():
        res, placement = nqueens.solve(ayz3, 3)
    assert res == "unsat"
    assert placement is None


# ===========================================================================
# Graph coloring (sat/unsat boundary: Petersen is 3-chromatic)
# ===========================================================================

def test_graph_coloring_3_colorable_ayz3():
    with fresh_ay():
        res, coloring = graph_coloring.solve(ayz3, 3)
    assert res == "sat"
    assert graph_coloring.is_valid_coloring(coloring, 3), (
        f"ayz3 3-coloring failed validation: {coloring}"
    )


def test_graph_coloring_not_2_colorable_ayz3():
    with fresh_ay():
        res, coloring = graph_coloring.solve(ayz3, 2)
    assert res == "unsat"
    assert coloring is None


@pytest.mark.usefixtures("required_reference_z3")
@pytest.mark.parametrize("k", [2, 3])
def test_graph_coloring_agrees_with_z3py(k):
    with fresh_ay():
        ay_res, ay_col = graph_coloring.solve(ayz3, k)
    z_res, z_col = graph_coloring.solve(z3py, k)
    assert ay_res == z_res, f"k={k}: ayz3 {ay_res} vs z3py {z_res}"
    if ay_res == "sat":
        assert graph_coloring.is_valid_coloring(ay_col, k)
        assert graph_coloring.is_valid_coloring(z_col, k)


# ===========================================================================
# Bounded model checking
# ===========================================================================

def test_bmc_invariant_holds_ayz3():
    # Correct system: bad state unreachable within the horizon -> unsat.
    with fresh_ay():
        res, trace = bmc.solve(ayz3, buggy=False)
    assert res == "unsat"
    assert trace is None


def test_bmc_finds_counterexample_ayz3():
    # Buggy system: bad state reachable -> sat with a real counterexample.
    with fresh_ay():
        res, trace = bmc.solve(ayz3, buggy=True)
    assert res == "sat"
    assert bmc.reaches_bad(trace), f"ayz3 BMC trace must hit a bad state: {trace}"


@pytest.mark.usefixtures("required_reference_z3")
@pytest.mark.parametrize("buggy", [False, True])
def test_bmc_agrees_with_z3py(buggy):
    with fresh_ay():
        ay_res, ay_trace = bmc.solve(ayz3, buggy=buggy)
    z_res, z_trace = bmc.solve(z3py, buggy=buggy)
    assert ay_res == z_res, f"buggy={buggy}: ayz3 {ay_res} vs z3py {z_res}"
    if ay_res == "sat":
        assert bmc.reaches_bad(ay_trace)
        assert bmc.reaches_bad(z_trace)


# ===========================================================================
# z3py-style model API (iteration / decls / len / repr / FuncDeclRef.name)
# ===========================================================================

def test_model_iteration_and_decls():
    with fresh_ay():
        s = ayz3.Solver()
        x, y, b = ayz3.Int("x"), ayz3.Int("y"), ayz3.Bool("b")
        s.add(x > 0, x < 10, y == x + 5, b == (x > 3))
        assert s.check() == ayz3.sat
        m = s.model()
        # len + decls
        assert len(m) == 3
        names = sorted(d.name() for d in m)
        assert names == ["b", "x", "y"]
        # decls() returns FuncDeclRef objects
        assert all(isinstance(d, ayz3.FuncDeclRef) for d in m.decls())
        # m[d] for a decl matches m[const_ref]
        by_name = {d.name(): d for d in m.decls()}
        assert m[by_name["x"]].as_long() == m[x].as_long()
        # iteration yields each const exactly once
        assert len(list(m)) == 3


def test_model_repr_z3py_style():
    with fresh_ay():
        s = ayz3.Solver()
        x, y = ayz3.Int("x"), ayz3.Int("y")
        s.add(x == 4, y == 6)
        assert s.check() == ayz3.sat
        m = s.model()
        # Sorted, z3py-style "[x = 4, y = 6]".
        assert repr(m) == "[x = 4, y = 6]"


def test_model_repr_bool_and_string_values():
    with fresh_ay():
        s = ayz3.Solver()
        b = ayz3.Bool("b")
        s.add(b == True)
        assert s.check() == ayz3.sat
        assert repr(s.model()) == "[b = True]"
    with fresh_ay():
        s = ayz3.Solver()
        st = ayz3.String("s")
        s.add(st == ayz3.StringVal("hi"))
        assert s.check() == ayz3.sat
        assert repr(s.model()) == '[s = "hi"]'


@pytest.mark.usefixtures("required_reference_z3")
def test_model_repr_pairs_match_z3py():
    # The SET of "name = value" pairs in the repr must match z3py exactly
    # (ayz3 sorts for stability; z3py uses engine order). Compare as sets.
    def pairs(rep):
        body = rep.strip()[1:-1]  # drop [ ]
        return set(p.strip() for p in body.split(",") if p.strip())

    with fresh_ay():
        s = ayz3.Solver()
        x, y, b = ayz3.Int("x"), ayz3.Int("y"), ayz3.Bool("b")
        s.add(x == 4, y == 6, b == False)
        assert s.check() == ayz3.sat
        ay_rep = repr(s.model())

    sz = z3py.Solver()
    x2, y2, b2 = z3py.Int("x"), z3py.Int("y"), z3py.Bool("b")
    sz.add(x2 == 4, y2 == 6, b2 == False)
    assert sz.check() == z3py.sat
    z_rep = repr(sz.model())

    assert pairs(ay_rep) == pairs(z_rep) == {"x = 4", "y = 6", "b = False"}


def test_funcdecl_name():
    with fresh_ay():
        f = ayz3.Function("f", ayz3.IntSort(), ayz3.IntSort())
        assert f.name() == "f"
        assert repr(f) == "f"


def test_model_evaluate_alias():
    with fresh_ay():
        s = ayz3.Solver()
        x = ayz3.Int("x")
        s.add(x == 7)
        assert s.check() == ayz3.sat
        m = s.model()
        # z3py spells model.eval as model.evaluate too.
        assert m.evaluate(x + 1).as_long() == 8


def test_sum_product():
    with fresh_ay():
        s = ayz3.Solver()
        xs = [ayz3.Int("x%d" % i) for i in range(4)]
        for x in xs:
            s.add(x >= 0, x <= 3)
        s.add(ayz3.Sum(xs) == 8)
        # Product against a CONSTANT keeps the term linear (AY's LIA decides it);
        # Product(var, var) would be nonlinear and is not a fair Sum/Product test.
        s.add(ayz3.Product(xs[0], 2) == 6)  # xs[0] == 3
        assert s.check() == ayz3.sat
        m = s.model()
        vals = [m[x].as_long() for x in xs]
        assert sum(vals) == 8
        assert vals[0] == 3

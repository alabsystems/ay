# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
#
# End-to-end tests for the ayz3 core slice, run through AY's real solver via the
# C ABI. Where real z3py is installed, the SAME snippet is cross-checked against
# z3py and the verdicts (and determinate model values) must agree.
#
# Run:  cargo build -p ay-ffi   &&   pytest bindings/python/tests -v

from fractions import Fraction

import pytest

import ayz3 as z

# Detect real z3py for cross-checking (optional).
try:
    import z3 as _z3
    HAVE_Z3PY = True
except Exception:  # pragma: no cover - depends on environment
    _z3 = None
    HAVE_Z3PY = False


def fresh_solver():
    """A Solver with its own isolated Context (independent assertion stack)."""
    return z.Solver(z.Context())


# ---------------------------------------------------------------------------
# Core: Int
# ---------------------------------------------------------------------------

def test_int_sat_canonical():
    # The canonical z3py snippet, verbatim, on the bare main context.
    x = z.Int('x')
    s = z.Solver()
    s.add(x > 0, x < 10)
    assert s.check() == z.sat
    m = s.model()
    assert 0 < m[x].as_long() < 10


def test_int_unsat():
    s = fresh_solver()
    with s.using():
        y = z.Int('y')
        s.add(y > 5, y < 3)
    assert s.check() == z.unsat


def test_int_arithmetic_solution():
    s = fresh_solver()
    with s.using():
        x = z.Int('x')
        y = z.Int('y')
        s.add(x + y == 10, x - y == 4)
    assert s.check() == z.sat
    m = s.model()
    assert m[x].as_long() == 7
    assert m[y].as_long() == 3


def test_int_literals_and_coercion():
    s = fresh_solver()
    with s.using():
        x = z.Int('x')
        s.add(x == z.IntVal(42))
        s.add(2 * x >= 80)   # python-int coercion on the left of *
    assert s.check() == z.sat
    assert s.model()[x].as_long() == 42


# ---------------------------------------------------------------------------
# Core: Bool
# ---------------------------------------------------------------------------

def test_bool_or_not():
    s = fresh_solver()
    with s.using():
        p, q = z.Bool('p'), z.Bool('q')
        s.add(z.Or(p, q), z.Not(p))
    assert s.check() == z.sat
    m = s.model()
    assert m[p].as_bool() is False
    assert m[q].as_bool() is True


def test_bool_implies_unsat():
    s = fresh_solver()
    with s.using():
        p, q = z.Bool('p'), z.Bool('q')
        s.add(z.Implies(p, q), p, z.Not(q))
    assert s.check() == z.unsat


def test_bool_and_xor():
    s = fresh_solver()
    with s.using():
        a, b = z.Bool('a'), z.Bool('b')
        s.add(z.And(a, z.Xor(a, b)))
    assert s.check() == z.sat
    m = s.model()
    assert m[a].as_bool() is True
    assert m[b].as_bool() is False


# ---------------------------------------------------------------------------
# Core: Real
# ---------------------------------------------------------------------------

def test_real_half():
    s = fresh_solver()
    with s.using():
        r = z.Real('r')
        s.add(r * 2 == 1)
    assert s.check() == z.sat
    assert s.model()[r].as_fraction() == Fraction(1, 2)


def test_real_inequalities():
    s = fresh_solver()
    with s.using():
        r = z.Real('r')
        s.add(r > z.RealVal("1/3"), r < z.RealVal("1/2"))
    assert s.check() == z.sat
    v = s.model()[r].as_fraction()
    assert Fraction(1, 3) < v < Fraction(1, 2)


# ---------------------------------------------------------------------------
# Core: BitVec
# ---------------------------------------------------------------------------

def test_bitvec_wraparound():
    # 8-bit: a + 1 == 0  =>  a == 255.
    s = fresh_solver()
    with s.using():
        a = z.BitVec('a', 8)
        s.add(a + 1 == 0)
    assert s.check() == z.sat
    assert s.model()[a].as_long() == 255


def test_bitvec_bitops():
    s = fresh_solver()
    with s.using():
        a = z.BitVec('a', 8)
        b = z.BitVec('b', 8)
        s.add((a & b) == 0x0F, a == 0xFF)
    assert s.check() == z.sat
    m = s.model()
    assert m[a].as_long() == 0xFF
    assert (m[a].as_long() & m[b].as_long()) == 0x0F


def test_bitvec_signed_compare_default():
    # Default BitVec < is SIGNED (z3py semantics): 0xFF == -1 (signed) IS < 1.
    s = fresh_solver()
    with s.using():
        a = z.BitVec('a', 8)
        s.add(a == 0xFF, a < 1)
    assert s.check() == z.sat


def test_bitvec_unsigned_compare_ult():
    # Unsigned ULT: 0xFF (=255) is NOT < 1, so this is unsat.
    s = fresh_solver()
    with s.using():
        a = z.BitVec('a', 8)
        s.add(a == 0xFF, z.ULT(a, 1))
    assert s.check() == z.unsat


# ---------------------------------------------------------------------------
# Optimize
# ---------------------------------------------------------------------------

def test_optimize_maximize():
    o = z.Optimize(z.Context())
    with o.using():
        x = z.Int('x')
        o.add(x <= 7, x >= 0)
        obj = o.maximize(x)
    assert o.check() == z.sat
    assert obj.value().as_long() == 7


def test_optimize_minimize():
    o = z.Optimize(z.Context())
    with o.using():
        x = z.Int('x')
        o.add(x >= 3, x <= 20)
        obj = o.minimize(x)
    assert o.check() == z.sat
    assert obj.value().as_long() == 3


# ---------------------------------------------------------------------------
# Model.eval
# ---------------------------------------------------------------------------

def test_model_eval_compound():
    s = fresh_solver()
    with s.using():
        x = z.Int('x')
        y = z.Int('y')
        s.add(x == 5, y == 9)
        expr = x + y
    assert s.check() == z.sat
    m = s.model()
    assert m.eval(expr).as_long() == 14


# ---------------------------------------------------------------------------
# Honesty: gaps raise clearly rather than returning wrong answers
# ---------------------------------------------------------------------------

def test_simplify_folds_and_is_equivalent():
    # Z3_simplify now does REAL simplification: it rebuilds the term through AY's
    # folding constructors. AY also folds eagerly at construction, so for terms
    # built via this binding the result is already in normal form (a fixpoint) —
    # but the folds below must hold, and the result must be EQUIVALENT to input.
    s = fresh_solver()
    with s.using():
        x = z.Int('x')
        e = x + 0
        se = z.simplify(e)
        assert isinstance(se, z.AstRef)
        # x + 0 simplifies to x (same interned AST).
        assert se.ast == x.ast
        # And it is equivalent on all models: negating equality is unsat.
        s.add(se != e)
    assert s.check() == z.unsat


def test_simplify_closed_arithmetic_to_numeral():
    s = fresh_solver()
    with s.using():
        e = z.IntVal(2) + z.IntVal(3)
        se = z.simplify(e)
        assert se.as_long() == 5


def test_simplify_mul_one_and_and_true():
    s = fresh_solver()
    with s.using():
        x = z.Int('x')
        assert z.simplify(x * 1).ast == x.ast
        p = z.Bool('p')
        assert z.simplify(z.And(z.BoolVal(True), p)).ast == p.ast
        assert z.simplify(z.Or(z.BoolVal(False), p)).ast == p.ast


def test_simplify_ite_and_store_select():
    s = fresh_solver()
    with s.using():
        a = z.Int('a')
        b = z.Int('b')
        assert z.simplify(z.If(z.BoolVal(True), a, b)).ast == a.ast
        arr = z.Array('arr', z.IntSort(), z.IntSort())
        i = z.Int('i')
        v = z.Int('v')
        sel = z.Select(z.Store(arr, i, v), i)
        assert z.simplify(sel).ast == v.ast


@pytest.mark.skipif(not HAVE_Z3PY, reason="real z3py not installed")
def test_simplify_crosscheck_against_z3py():
    # The RESULT need not be syntactically identical to z3's, but the obvious
    # constant/identity folds must agree on the concrete value/structure. We
    # compare ayz3's fold by AST identity (AY hash-conses, so the fold lands on
    # the SAME interned node as the target) and confirm z3py folds identically.
    x_ay = z.Int('x')
    x_z3 = _z3.Int('x')

    # Closed arithmetic -> numeral (compare numeric values).
    assert z.simplify(z.IntVal(2) + z.IntVal(3)).as_long() == \
        _z3.simplify(_z3.IntVal(2) + _z3.IntVal(3)).as_long() == 5

    # x + 0 -> x in both.
    assert z.simplify(x_ay + 0).ast == x_ay.ast            # ayz3 folds to x
    assert _z3.simplify(x_z3 + 0).eq(x_z3)                  # z3py folds to x

    # And(True, p) -> p in both.
    p_ay, p_z3 = z.Bool('p'), _z3.Bool('p')
    assert z.simplify(z.And(z.BoolVal(True), p_ay)).ast == p_ay.ast
    assert _z3.simplify(_z3.And(True, p_z3)).eq(p_z3)

    # If(True, a, b) -> a in both.
    a_ay, b_ay = z.Int('a'), z.Int('b')
    a_z3, b_z3 = _z3.Int('a'), _z3.Int('b')
    assert z.simplify(z.If(z.BoolVal(True), a_ay, b_ay)).ast == a_ay.ast
    assert _z3.simplify(_z3.If(True, a_z3, b_z3)).eq(a_z3)


def test_model_index_compound_raises():
    s = fresh_solver()
    with s.using():
        x = z.Int('x')
        s.add(x == 1)
        expr = x + x
    s.check()
    m = s.model()
    with pytest.raises(NotImplementedError):
        _ = m[expr]   # compound expression, not a declared constant


# ---------------------------------------------------------------------------
# Cross-check against real z3py (skipped if not installed)
# ---------------------------------------------------------------------------

CROSS_SNIPPETS = [
    "int_box", "int_arith", "int_unsat",
    "bool_or_not", "bool_implies_unsat",
    "real_half", "bitvec_wrap",
    "bitvec_signed_sat", "bitvec_unsigned_unsat",
]


def _run_ayz3(name):
    """Return (result_str, {var: value}) for ayz3."""
    s = fresh_solver()
    with s.using():
        if name == "int_box":
            x = z.Int('x'); s.add(x == 5, x > 0, x < 10); vars_ = {"x": x}
        elif name == "int_arith":
            x = z.Int('x'); y = z.Int('y')
            s.add(x + y == 10, x - y == 4); vars_ = {"x": x, "y": y}
        elif name == "int_unsat":
            x = z.Int('x'); s.add(x > 5, x < 3); vars_ = {}
        elif name == "bool_or_not":
            p = z.Bool('p'); q = z.Bool('q')
            s.add(z.Or(p, q), z.Not(p)); vars_ = {"p": p, "q": q}
        elif name == "bool_implies_unsat":
            p = z.Bool('p'); q = z.Bool('q')
            s.add(z.Implies(p, q), p, z.Not(q)); vars_ = {}
        elif name == "real_half":
            r = z.Real('r'); s.add(r * 2 == 1); vars_ = {"r": r}
        elif name == "bitvec_wrap":
            a = z.BitVec('a', 8); s.add(a + 1 == 0); vars_ = {"a": a}
        elif name == "bitvec_signed_sat":
            a = z.BitVec('a', 8); s.add(a == 0xFF, a < 1); vars_ = {"a": a}
        elif name == "bitvec_unsigned_unsat":
            a = z.BitVec('a', 8); s.add(a == 0xFF, z.ULT(a, 1)); vars_ = {}
        else:
            raise AssertionError(name)
    res = s.check()
    if res != z.sat:
        return repr(res), {}
    m = s.model()
    out = {}
    for k, v in vars_.items():
        mv = m[v]
        if isinstance(mv, z.BoolRef):
            out[k] = mv.as_bool()
        elif v.sort().kind == "Real":
            out[k] = mv.as_fraction()
        else:
            out[k] = mv.as_long()
    return repr(res), out


def _run_z3py(name):
    s = _z3.Solver()
    if name == "int_box":
        x = _z3.Int('x'); s.add(x == 5, x > 0, x < 10); vars_ = {"x": x}
    elif name == "int_arith":
        x = _z3.Int('x'); y = _z3.Int('y')
        s.add(x + y == 10, x - y == 4); vars_ = {"x": x, "y": y}
    elif name == "int_unsat":
        x = _z3.Int('x'); s.add(x > 5, x < 3); vars_ = {}
    elif name == "bool_or_not":
        p = _z3.Bool('p'); q = _z3.Bool('q')
        s.add(_z3.Or(p, q), _z3.Not(p)); vars_ = {"p": p, "q": q}
    elif name == "bool_implies_unsat":
        p = _z3.Bool('p'); q = _z3.Bool('q')
        s.add(_z3.Implies(p, q), p, _z3.Not(q)); vars_ = {}
    elif name == "real_half":
        r = _z3.Real('r'); s.add(r * 2 == 1); vars_ = {"r": r}
    elif name == "bitvec_wrap":
        a = _z3.BitVec('a', 8); s.add(a + 1 == 0); vars_ = {"a": a}
    elif name == "bitvec_signed_sat":
        a = _z3.BitVec('a', 8); s.add(a == 0xFF, a < 1); vars_ = {"a": a}
    elif name == "bitvec_unsigned_unsat":
        a = _z3.BitVec('a', 8); s.add(a == 0xFF, _z3.ULT(a, 1)); vars_ = {}
    else:
        raise AssertionError(name)
    res = s.check()
    if str(res) != "sat":
        return str(res), {}
    m = s.model()
    out = {}
    for k, v in vars_.items():
        mv = m[v]
        if _z3.is_bool(v):
            out[k] = _z3.is_true(mv)
        elif name == "real_half":
            out[k] = Fraction(mv.as_fraction())
        else:
            out[k] = mv.as_long()
    return str(res), out


@pytest.mark.skipif(not HAVE_Z3PY, reason="real z3py not installed")
@pytest.mark.parametrize("name", CROSS_SNIPPETS)
def test_crosscheck_against_z3py(name):
    ay_res, ay_vals = _run_ayz3(name)
    z3_res, z3_vals = _run_z3py(name)
    assert ay_res == z3_res, f"{name}: ayz3 said {ay_res}, z3py said {z3_res}"
    # Where both are sat, determinate single-solution snippets must agree on
    # values. (All snippets above with a model are uniquely determined.)
    if ay_res == "sat":
        assert ay_vals == z3_vals, (
            f"{name}: model values differ: ayz3={ay_vals} z3py={z3_vals}"
        )

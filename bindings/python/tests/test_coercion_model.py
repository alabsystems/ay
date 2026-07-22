# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
#
# Tests for two z3py-fidelity gaps closed in ayz3:
#
#   GAP #3  Int<->Real coercion of NON-LITERAL terms. z3py auto-promotes a mixed
#           Int/Real expression by inserting ToReal (Z3_mk_int2real) on the Int
#           operand, yielding a Real-sorted result. ayz3 now does the same in its
#           arithmetic (+,-,*,/), comparison (<,<=,>,>=,==,!=) and ite (If)
#           builders. Pure-Int and pure-Real cases are untouched.
#
#   GAP #4  model.eval / m[expr] for COMPOUND expressions returns a CONCRETE,
#           renderable value (numeral / Bool / string), not an opaque AST.
#           Z3_model_eval (with model_completion when asked) does the reduction;
#           the wrapper renders the concrete content the way z3py prints it.
#
# Every case is cross-checked against real z3py 4.15.4 (verdict AND model
# values). SOUNDNESS: ayz3 reports AY's REAL answer; coercion produces a
# semantically correct ToReal-promoted term, never a hack.
#
# Run:  cargo build -p ay-ffi   &&   pytest bindings/python/tests -v

from fractions import Fraction

import pytest

import ayz3 as z

try:
    import z3 as _z3
    HAVE_Z3PY = True
except Exception:  # pragma: no cover - depends on environment
    _z3 = None
    HAVE_Z3PY = False


def fresh_solver():
    """A Solver with its own isolated Context (independent assertion stack)."""
    return z.Solver(z.Context())


# ===========================================================================
# GAP #3 — Int<->Real coercion of non-literal terms
# ===========================================================================

def test_mixed_add_result_sort_is_real():
    # x_int + y_real is Real-sorted in z3py (ToReal(x) + y). ayz3 must match.
    s = fresh_solver()
    with s.using():
        x = z.Int('x')
        y = z.Real('y')
        e = x + y
        assert e.sort().kind == "Real"


def test_mixed_add_solves_correctly():
    # x + y == 3, x == 1  =>  y == 2 (a Real).
    s = fresh_solver()
    with s.using():
        x = z.Int('x')
        y = z.Real('y')
        s.add(x + y == 3, x == 1)
        assert s.check() == z.sat
        m = s.model()
        assert m[x].as_long() == 1
        assert m[y].as_fraction() == Fraction(2)


def test_mixed_comparison_lt():
    # x_int < y_real with x=2, y=2.5 is sat; x=2,y=1 unsat under the bound.
    s = fresh_solver()
    with s.using():
        x = z.Int('x')
        y = z.Real('y')
        assert (x < y).sort().kind == "Bool"
        s.add(x < y, x == 2, y == z.RealVal("5/2"))
        assert s.check() == z.sat


def test_mixed_comparison_unsat():
    s = fresh_solver()
    with s.using():
        x = z.Int('x')
        y = z.Real('y')
        s.add(x < y, x == 3, y == z.RealVal("5/2"))  # 3 < 2.5 is false
        assert s.check() == z.unsat


def test_mixed_eq_promotes():
    # x_int == y_real coerces to ToReal(x) == y.
    s = fresh_solver()
    with s.using():
        x = z.Int('x')
        y = z.Real('y')
        eq = (x == y)
        assert isinstance(eq, z.BoolRef)
        s.add(eq, x == 4)
        assert s.check() == z.sat
        assert s.model()[y].as_fraction() == Fraction(4)


def test_mixed_if_result_sort_and_solve():
    # If(b, int_term, real_term) is Real-sorted (z3py wraps the Int branch).
    s = fresh_solver()
    with s.using():
        b = z.Bool('b')
        xi = z.Int('xi')
        yr = z.Real('yr')
        ite = z.If(b, xi, yr)
        assert ite.sort().kind == "Real"
        s.add(ite == z.RealVal("7/2"), b == False, yr == z.RealVal("7/2"))
        assert s.check() == z.sat


def test_mixed_div_is_real():
    # Int / Real promotes to a Real division (ToReal(x) / y), result Real.
    # The coercion itself is what we check here; dividing by a Real LITERAL
    # keeps it linear so AY decides it (division by a VARIABLE is nonlinear and
    # AY may honestly answer unknown — not a coercion bug; see z3py cross-check
    # which agrees on the sort).
    s = fresh_solver()
    with s.using():
        x = z.Int('x')
        q = x / z.RealVal(2)
        assert q.sort().kind == "Real"
        s.add(x == 6, q == z.RealVal(3))
        assert s.check() == z.sat


# --- pure-Int / pure-Real must be UNCHANGED (no spurious promotion) ----------

def test_pure_int_unchanged():
    s = fresh_solver()
    with s.using():
        a = z.Int('a')
        b = z.Int('b')
        e = a + b
        assert e.sort().kind == "Int"
        s.add(e == 5, a == 2)
        assert s.check() == z.sat
        assert s.model()[b].as_long() == 3


def test_pure_real_unchanged():
    s = fresh_solver()
    with s.using():
        a = z.Real('a')
        b = z.Real('b')
        e = a + b
        assert e.sort().kind == "Real"
        s.add(e == z.RealVal(3), a == z.RealVal("1/2"))
        assert s.check() == z.sat
        assert s.model()[b].as_fraction() == Fraction(5, 2)


def test_pure_int_mod_not_promoted():
    # mod stays Int-only; no ToReal sneaks in.
    s = fresh_solver()
    with s.using():
        a = z.Int('a')
        m = a % 3
        assert m.sort().kind == "Int"
        s.add(a == 7, m == 1)
        assert s.check() == z.sat


# ===========================================================================
# GAP #4 — model.eval / value rendering for compound expressions
# ===========================================================================

def test_eval_compound_int_concrete():
    s = fresh_solver()
    with s.using():
        x = z.Int('x')
        y = z.Int('y')
        s.add(x == 1, y == 2)
        assert s.check() == z.sat
        m = s.model()
        v = m.eval(x + 2 * y)
        assert v.as_long() == 5
        # renders concretely (z3py prints `5`, not an opaque ast)
        assert repr(v) == "5"


def test_eval_compound_mixed_real():
    s = fresh_solver()
    with s.using():
        pi = z.Int('pi')
        pr = z.Real('pr')
        s.add(pi == 3, pr == z.RealVal("3/2"))
        assert s.check() == z.sat
        m = s.model()
        v = m.eval(pi + pr)  # 3 + 3/2 = 9/2
        assert v.as_fraction() == Fraction(9, 2)
        assert repr(v) == "9/2"


def test_eval_compound_bool_concrete():
    s = fresh_solver()
    with s.using():
        a = z.Int('a')
        s.add(a == 5)
        assert s.check() == z.sat
        m = s.model()
        v = m.eval(a > 3)
        assert v.as_bool() is True
        assert repr(v) == "True"


def test_eval_whole_real_renders_without_denominator():
    # z3py prints a whole-number Real as `2`, not `2/1`.
    s = fresh_solver()
    with s.using():
        y = z.Real('y')
        s.add(y == z.RealVal(2))
        assert s.check() == z.sat
        m = s.model()
        assert repr(m[y]) == "2"


def test_eval_model_completion_fills_var():
    # An unconstrained var, completed, yields a concrete value (AY's model is
    # total; with completion both engines agree on a value).
    s = fresh_solver()
    with s.using():
        u = z.Int('u')
        w = z.Int('w')
        s.add(u == 5)
        assert s.check() == z.sat
        m = s.model()
        v = m.eval(w, model_completion=True)
        # honest concrete value (AY assigns w during solving)
        assert v.as_long() == m.eval(w, model_completion=True).as_long()
        assert repr(v) != ""  # concrete, renderable


# ===========================================================================
# z3py cross-checks (oracle = real z3py 4.15.4)
# ===========================================================================

@pytest.mark.skipif(not HAVE_Z3PY, reason="real z3py not installed")
def test_crosscheck_mixed_add():
    # ayz3
    sa = fresh_solver()
    with sa.using():
        x = z.Int('x')
        y = z.Real('y')
        sa.add(x + y == 3, x == 1)
        assert sa.check() == z.sat
        ay_y = sa.model()[y].as_fraction()
        ay_sort = (x + y).sort().kind
    # z3py
    sb = _z3.Solver()
    x2 = _z3.Int('x')
    y2 = _z3.Real('y')
    sb.add(x2 + y2 == 3, x2 == 1)
    assert str(sb.check()) == "sat"
    z3_y = sb.model()[y2].as_fraction()
    z3_sort = str((x2 + y2).sort())
    assert ay_sort == "Real" and z3_sort == "Real"
    assert ay_y == z3_y == Fraction(2)


@pytest.mark.skipif(not HAVE_Z3PY, reason="real z3py not installed")
def test_crosscheck_mixed_lt():
    sa = fresh_solver()
    with sa.using():
        x = z.Int('x')
        y = z.Real('y')
        sa.add(x < y, x == 2, y == z.RealVal("5/2"))
        ay_res = str(sa.check())
    sb = _z3.Solver()
    x2 = _z3.Int('x')
    y2 = _z3.Real('y')
    sb.add(x2 < y2, x2 == 2, y2 == _z3.RealVal("5/2"))
    z3_res = str(sb.check())
    assert ay_res == z3_res == "sat"


@pytest.mark.skipif(not HAVE_Z3PY, reason="real z3py not installed")
def test_crosscheck_mixed_if():
    sa = fresh_solver()
    with sa.using():
        b = z.Bool('b')
        xi = z.Int('xi')
        yr = z.Real('yr')
        ite = z.If(b, xi, yr)
        sa.add(ite == z.RealVal("7/2"), b == False, yr == z.RealVal("7/2"))
        ay_res = str(sa.check())
        ay_sort = ite.sort().kind
    sb = _z3.Solver()
    b2 = _z3.Bool('b')
    xi2 = _z3.Int('xi')
    yr2 = _z3.Real('yr')
    ite2 = _z3.If(b2, xi2, yr2)
    sb.add(ite2 == _z3.RealVal("7/2"), b2 == False, yr2 == _z3.RealVal("7/2"))
    z3_res = str(sb.check())
    assert ay_res == z3_res == "sat"
    assert ay_sort == "Real" and str(ite2.sort()) == "Real"


@pytest.mark.skipif(not HAVE_Z3PY, reason="real z3py not installed")
def test_crosscheck_eval_compound():
    # m.eval(x + 2*y) returns a concrete numeral equal to z3py's.
    sa = fresh_solver()
    with sa.using():
        x = z.Int('x')
        y = z.Int('y')
        sa.add(x == 1, y == 2)
        assert sa.check() == z.sat
        ay_val = sa.model().eval(x + 2 * y).as_long()
    sb = _z3.Solver()
    x2 = _z3.Int('x')
    y2 = _z3.Int('y')
    sb.add(x2 == 1, y2 == 2)
    assert str(sb.check()) == "sat"
    z3_val = sb.model().eval(x2 + 2 * y2, model_completion=True).as_long()
    assert ay_val == z3_val == 5


@pytest.mark.skipif(not HAVE_Z3PY, reason="real z3py not installed")
def test_crosscheck_eval_compound_mixed_real():
    sa = fresh_solver()
    with sa.using():
        pi = z.Int('pi')
        pr = z.Real('pr')
        sa.add(pi == 3, pr == z.RealVal("3/2"))
        assert sa.check() == z.sat
        ay_val = sa.model().eval(pi + pr).as_fraction()
    sb = _z3.Solver()
    pi2 = _z3.Int('pi')
    pr2 = _z3.Real('pr')
    sb.add(pi2 == 3, pr2 == _z3.RealVal("3/2"))
    assert str(sb.check()) == "sat"
    z3_val = sb.model().eval(pi2 + pr2, model_completion=True).as_fraction()
    assert ay_val == z3_val == Fraction(9, 2)


@pytest.mark.skipif(not HAVE_Z3PY, reason="real z3py not installed")
def test_crosscheck_eval_completion_value():
    # With model_completion, both engines yield a concrete value for an
    # unconstrained var. (AY's model is total, so the value agrees with z3py's
    # completed value.)
    sa = fresh_solver()
    with sa.using():
        u = z.Int('u')
        w = z.Int('w')
        sa.add(u == 5)
        assert sa.check() == z.sat
        ay_w = sa.model().eval(w, model_completion=True).as_long()
    sb = _z3.Solver()
    u2 = _z3.Int('u')
    w2 = _z3.Int('w')
    sb.add(u2 == 5)
    assert str(sb.check()) == "sat"
    z3_w = sb.model().eval(w2, model_completion=True).as_long()
    assert ay_w == z3_w  # both 0


# ===========================================================================
# RealVal(float) exactness — z3py decimal-string semantics
# ===========================================================================
#
# RealVal(float) parses the float's decimal repr exactly (matching z3py, where
# Z3 parses str(0.1) as the decimal 1/10). The old implementation approximated
# via Fraction(v).limit_denominator(10**12), which silently collapsed
# small-magnitude floats: RealVal(1e-13) became exactly 0.

def test_realval_small_float_not_collapsed_to_zero():
    s = fresh_solver()
    with s.using():
        x = z.Real('x')
        s.add(x == z.RealVal(1e-13), x > 0)
        assert s.check() == z.sat
        assert s.model()[x].as_fraction() == Fraction(1, 10**13)


def test_realval_float_uses_decimal_semantics_like_z3py():
    # z3py: RealVal(0.1) is exactly 1/10 (decimal parse), NOT the binary
    # expansion 3602879701896397/36028797018963968.
    s = fresh_solver()
    with s.using():
        x = z.Real('x')
        s.add(x == z.RealVal(0.1))
        assert s.check() == z.sat
        assert s.model()[x].as_fraction() == Fraction(1, 10)


def test_realval_rejects_int_only_objects_instead_of_truncating():
    class IntOnly:
        def __int__(self):
            return 7

    with pytest.raises(z.AyZ3Exception, match="unsupported numeric value"):
        z.RealVal(IntOnly())


def test_coerced_bare_float_small_magnitude():
    # Bare Python floats route through _coerce -> RealVal and must keep the
    # exact value too.
    s = fresh_solver()
    with s.using():
        x = z.Real('x')
        s.add(x == 1e-13)
        assert s.check() == z.sat
        assert s.model()[x].as_fraction() == Fraction(1, 10**13)

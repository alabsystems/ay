# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
#
# B-8: z3py module helper functions (solve / prove / substitute / ToReal /
# ToInt / IsInt / IntToStr / StrToInt / Fresh* / Sqrt / Cbrt / Q / is_*).
#
# Every helper is exercised through AY's real solver via the C ABI and, where
# real z3py is installed, cross-checked against z3py in the SAME test. Exact
# byte matches are asserted where AY and z3py agree; the few SOUND rendering
# divergences (commutative operand order, rational `(/ 1 2)` vs `(/ 1.0 2.0)`,
# engine-internal Fresh* name suffixes) are asserted for semantic equivalence
# and documented inline.
#
# Run:  AYZ3_LIB=<dylib> pytest bindings/python/tests/test_helpers_b8.py -v

import contextlib
import io
import re

import pytest

import ayz3 as z

try:
    import z3 as _z3
    HAVE_Z3PY = True
except Exception:  # pragma: no cover - depends on environment
    _z3 = None
    HAVE_Z3PY = False


def _capture(fn):
    """Run `fn`, returning whatever it prints to stdout (stripped)."""
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        fn()
    return buf.getvalue().strip()


# ---------------------------------------------------------------------------
# solve
# ---------------------------------------------------------------------------

def test_solve_sat_prints_model_line():
    out = _capture(lambda: z.solve(z.Int('x') > 2, z.Int('x') < 5))
    # z3py prints `[x = 3]`; AY prints a satisfying value in (2, 5).
    m = re.fullmatch(r"\[x = (\d+)\]", out)
    assert m is not None, out
    assert 2 < int(m.group(1)) < 5
    if HAVE_Z3PY:
        zout = _capture(lambda: _z3.solve(_z3.Int('x') > 2, _z3.Int('x') < 5))
        assert re.fullmatch(r"\[x = \d+\]", zout)


def test_solve_unsat_prints_no_solution():
    out = _capture(lambda: z.solve(z.Int('x') > 5, z.Int('x') < 2))
    assert out == "no solution"
    if HAVE_Z3PY:
        zout = _capture(lambda: _z3.solve(_z3.Int('x') > 5, _z3.Int('x') < 2))
        assert out == zout


# ---------------------------------------------------------------------------
# prove
# ---------------------------------------------------------------------------

def test_prove_valid_prints_proved():
    def claim(M):
        x, y = M.Int('x'), M.Int('y')
        return M.Implies(M.And(x > 0, y > 0), x + y > 0)
    out = _capture(lambda: z.prove(claim(z)))
    assert out == "proved"
    if HAVE_Z3PY:
        assert _capture(lambda: _z3.prove(claim(_z3))) == "proved"


def test_prove_invalid_prints_counterexample():
    out = _capture(lambda: z.prove(z.Int('x') > 0))
    assert out.splitlines()[0] == "counterexample"
    if HAVE_Z3PY:
        zout = _capture(lambda: _z3.prove(_z3.Int('x') > 0))
        assert zout.splitlines()[0] == "counterexample"


def test_prove_non_bool_raises():
    with pytest.raises(z.AyZ3Exception):
        z.prove(z.Int('x'))  # not a Bool claim


# ---------------------------------------------------------------------------
# substitute
# ---------------------------------------------------------------------------

def test_substitute_single_pair():
    x, y = z.Int('x'), z.Int('y')
    sub = z.substitute(x + y, (x, z.IntVal(3)))
    # AY canonicalizes a commutative `+` with the numeral last: `(+ y 3)`.
    # That is exactly AY's own rendering of `3 + y`, and it is semantically the
    # value z3py prints as `(+ 3 y)`.
    assert sub.sexpr() == (z.IntVal(3) + y).sexpr()
    # Prove the substituted term equals `3 + y` (Not(equal) is unsat).
    s = z.Solver()
    s.add(z.Not(sub == (z.IntVal(3) + y)))
    assert s.check() == z.unsat
    if HAVE_Z3PY:
        zx, zy = _z3.Int('x'), _z3.Int('y')
        zsub = _z3.substitute(zx + zy, (zx, _z3.IntVal(3)))
        assert zsub.sexpr() == "(+ 3 y)"  # z3py's commutative order


def test_substitute_simultaneous_swap():
    x, y = z.Int('x'), z.Int('y')
    swapped = z.substitute(x - y, (x, y), (y, x))
    # Simultaneous: x<->y turns `x - y` into `y - x`.
    s = z.Solver()
    s.add(z.Not(swapped == (y - x)))
    assert s.check() == z.unsat


def test_substitute_list_of_pairs_form():
    x, y = z.Int('x'), z.Int('y')
    # Accepts a single list of pairs, like z3py.
    out = z.substitute(x + y, [(x, z.IntVal(3)), (y, z.IntVal(4))])
    # AY folds 3 + 4 eagerly to 7 (a sound simplification); value is 7 either way.
    s = z.Solver()
    s.add(z.Not(out == z.IntVal(7)))
    assert s.check() == z.unsat


def test_substitute_sort_mismatch_raises():
    x = z.Int('x')
    with pytest.raises(z.AyZ3Exception):
        z.substitute(x, (x, z.Real('rr')))


# --- AC substitution: sound support + honest error on the unrecoverable case -
#
# z3py's `substitute` is STRUCTURAL on the build tree. AY flattens, collects
# like terms and SORTS a `+`/`*` at construction, so a `from` that survives only
# as a PROPER sub-multiset of a flattened node (it shares operands with the node
# but is not the whole node) is UNRECOVERABLE: the associativity/order z3py needs
# is gone, and many distinct z3py sources -- which z3py substitutes DIFFERENTLY
# -- collapse to the same AY node. ayz3 therefore reproduces z3py EXACTLY for the
# recoverable cases (non-AC `from`s, exact whole-node matches, genuine-absent)
# and raises a clear error -- never a wrong value -- for the unrecoverable case.
# Each "unrecoverable" test PROVES the ambiguity with real z3py: two AY-identical
# sibling sources get different z3py results, so no single value could be right.


def _equiv(ay_expr, expected):
    """True iff ayz3 proves `ay_expr == expected` on every assignment."""
    s = z.Solver()
    s.add(z.Not(ay_expr == expected))
    return s.check() == z.unsat


# ---- SUPPORTED (recoverable): byte/semantically exact against real z3py ----

def test_substitute_ac_exact_whole_node():
    x, y = z.Int('x'), z.Int('y')
    # A whole-node `+` match collapses to the `to` value (the from IS the node,
    # so there is no lost sub-structure).
    out = z.substitute(x + y, (x + y, z.IntVal(10)))
    assert out.sexpr() == "10"
    if HAVE_Z3PY:
        zx, zy = _z3.Int('x'), _z3.Int('y')
        assert _z3.substitute(zx + zy, (zx + zy, _z3.IntVal(10))).sexpr() == "10"


def test_substitute_ac_exact_whole_node_nested_in_function():
    # The from is the WHOLE `+` node, kept intact as a genuine subterm under f;
    # this IS recoverable and matches z3py exactly.
    x, y = z.Int('x'), z.Int('y')
    f = z.Function('f', z.IntSort(), z.IntSort())
    out = z.substitute(f(x + y), (x + y, z.IntVal(10)))
    assert _equiv(out, f(z.IntVal(10)))
    if HAVE_Z3PY:
        zx, zy = _z3.Int('x'), _z3.Int('y')
        zf = _z3.Function('f', _z3.IntSort(), _z3.IntSort())
        assert _z3.substitute(
            zf(zx + zy), (zx + zy, _z3.IntVal(10))).sexpr() == "(f 10)"


def test_substitute_ac_genuine_absent_is_noop():
    x, y, d = z.Int('x'), z.Int('y'), z.Int('d')
    # {x, y} is NOT a sub-multiset of {x, d}: a correct no-op, exactly z3py.
    out = z.substitute(x + d, (x + y, z.IntVal(10)))
    assert _equiv(out, x + d)
    if HAVE_Z3PY:
        zx, zy, zd = _z3.Int('x'), _z3.Int('y'), _z3.Int('d')
        zout = _z3.substitute(zx + zd, (zx + zy, _z3.IntVal(10)))
        assert zout.sexpr() == "(+ x d)"       # z3py: unchanged
        assert out.sexpr() == zout.sexpr()     # ayz3 matches z3py byte-for-byte


def test_substitute_function_subterm_still_correct():
    # A non-AC compound `from` (f(x)) keeps the exact-node semantics.
    x, d = z.Int('x'), z.Int('d')
    f = z.Function('f', z.IntSort(), z.IntSort())
    out = z.substitute(f(x) + d, (f(x), z.IntVal(7)))
    assert _equiv(out, z.IntVal(7) + d)
    if HAVE_Z3PY:
        zx, zd = _z3.Int('x'), _z3.Int('d')
        zf = _z3.Function('f', _z3.IntSort(), _z3.IntSort())
        zout = _z3.substitute(zf(zx) + zd, (zf(zx), _z3.IntVal(7)))
        assert zout.sexpr() == "(+ 7 d)"


def test_substitute_supported_exact_propagates_to_solve():
    # A SUPPORTED substitute flows into a solve with the SAME verdict as z3py:
    # substitute(x+y, (x+y,10)) is 10, so `== 5` is UNSAT ("no solution").
    x, y = z.Int('x'), z.Int('y')
    out = _capture(lambda: z.solve(
        z.substitute(x + y, (x + y, z.IntVal(10))) == 5))
    assert out == "no solution"
    if HAVE_Z3PY:
        zx, zy = _z3.Int('x'), _z3.Int('y')
        zout = _capture(lambda: _z3.solve(
            _z3.substitute(zx + zy, (zx + zy, _z3.IntVal(10))) == 5))
        assert out == zout


# ---- UNRECOVERABLE (proper sub-multiset): honest error, NEVER a wrong value -

def test_substitute_ac_proper_submultiset_plus_raises():
    x, y, d = z.Int('x'), z.Int('y'), z.Int('d')
    with pytest.raises(z.AyZ3Exception, match="sub-multiset"):
        z.substitute((x + y) + d, (x + y, z.IntVal(10)))
    # `(x+y)+d` and `x+(y+d)` are the SAME AY node...
    assert ((x + y) + d).sexpr() == (x + (y + d)).sexpr()
    if HAVE_Z3PY:
        zx, zy, zd = _z3.Int('x'), _z3.Int('y'), _z3.Int('d')
        # ...yet z3py substitutes them DIFFERENTLY (assoc. AY discarded):
        assert _z3.substitute(
            (zx + zy) + zd, (zx + zy, _z3.IntVal(10))).sexpr() == "(+ 10 d)"
        assert _z3.substitute(
            zx + (zy + zd), (zx + zy, _z3.IntVal(10))).sexpr() == "(+ x y d)"


def test_substitute_ac_repeated_operand_plus_raises():
    # The review-flagged repeated-operand cases: a+b+b+c and x+y+x+y.
    # Fresh Context: 'b' is declared Bool elsewhere in this shared session.
    ctx = z.Context()
    a, b, c = z.Int('a', ctx), z.Int('b', ctx), z.Int('c', ctx)
    with pytest.raises(z.AyZ3Exception, match="sub-multiset"):
        z.substitute(a + b + b + c, (a + b, z.IntVal(10, ctx)))
    x, y = z.Int('x', ctx), z.Int('y', ctx)
    with pytest.raises(z.AyZ3Exception, match="sub-multiset"):
        z.substitute(x + y + x + y, (x + y, z.IntVal(10, ctx)))
    # x+y+x+y and x+x+y+y collapse to the SAME AY node...
    assert (x + y + x + y).sexpr() == (x + x + y + y).sexpr()
    if HAVE_Z3PY:
        za, zb, zc = _z3.Int('a'), _z3.Int('b'), _z3.Int('c')
        # z3py replaces a+b+b+c but leaves the AY-identical a+(b+b)+c UNCHANGED:
        assert _z3.substitute(
            za + zb + zb + zc, (za + zb, _z3.IntVal(10))).sexpr() == "(+ 10 b c)"
        assert _z3.substitute(
            za + (zb + zb) + zc, (za + zb, _z3.IntVal(10))).sexpr() == "(+ a b b c)"
        zx, zy = _z3.Int('x'), _z3.Int('y')
        # z3py replaces x+y+x+y (-> (+ 10 x y)) but leaves x+x+y+y UNCHANGED:
        assert _z3.substitute(
            zx + zy + zx + zy, (zx + zy, _z3.IntVal(10))).sexpr() == "(+ 10 x y)"
        assert _z3.substitute(
            zx + zx + zy + zy, (zx + zy, _z3.IntVal(10))).sexpr() == "(+ x x y y)"


def test_substitute_ac_repeated_operand_star_raises():
    # Fresh Context: 'b' is declared Bool elsewhere in this shared session.
    ctx = z.Context()
    a, b, c = z.Int('a', ctx), z.Int('b', ctx), z.Int('c', ctx)
    with pytest.raises(z.AyZ3Exception, match="sub-multiset"):
        z.substitute(a * b * b * c, (a * b, z.IntVal(10, ctx)))
    with pytest.raises(z.AyZ3Exception, match="sub-multiset"):
        z.substitute((a * b) * c, (a * b, z.IntVal(10, ctx)))
    if HAVE_Z3PY:
        za, zb, zc = _z3.Int('a'), _z3.Int('b'), _z3.Int('c')
        # z3py replaces a*b*b*c but leaves the AY-identical b*a*b*c UNCHANGED:
        assert _z3.substitute(
            za * zb * zb * zc, (za * zb, _z3.IntVal(10))).sexpr() == "(* 10 b c)"
        assert _z3.substitute(
            zb * za * zb * zc, (za * zb, _z3.IntVal(10))).sexpr() == "(* b a b c)"


def test_substitute_ac_proper_submultiset_under_function_raises():
    # The flattened `+` sub-multiset is buried under an uninterpreted function;
    # still unrecoverable, so still an honest error (not a guessed value).
    x, y, d = z.Int('x'), z.Int('y'), z.Int('d')
    f = z.Function('f', z.IntSort(), z.IntSort())
    with pytest.raises(z.AyZ3Exception, match="sub-multiset"):
        z.substitute(f((x + y) + d), (x + y, z.IntVal(10)))


def test_substitute_ac_to_is_compound_still_raises_when_submultiset():
    # A compound `to` does not make the sub-multiset match recoverable.
    ctx = z.Context()
    x, y, w = z.Int('x', ctx), z.Int('y', ctx), z.Int('w', ctx)
    a, b = z.Int('a', ctx), z.Int('b', ctx)
    with pytest.raises(z.AyZ3Exception, match="sub-multiset"):
        z.substitute((x + y) + w, (x + y, a + b))


def test_solve_show_prints_bracketed_assertion_list():
    # The honest `show=True`: a z3py-shaped bracketed list `[c1, c2]`. Since B-4
    # each element renders in the z3py-style INFIX form (not the old prefix
    # s-expression), so the list is z3py-shaped down to the element level. It
    # differs from z3py's `[x > 0, x < 10]` only where AY canonicalizes the term:
    # `x > 0` is stored `(< 0 x)`, so it prints `0 < x` (documented divergence);
    # `x < 10` is stored as-is and prints identically to z3py.
    x = z.Int('x')
    out = _capture(lambda: z.solve(x > 0, x < 10, show=True))
    lines = out.splitlines()
    assert lines[0] == "[0 < x, x < 10]"
    assert re.fullmatch(r"\[x = \d+\]", lines[1])
    if HAVE_Z3PY:
        # z3py keeps the surface orientation (`x > 0`); AY's `0 < x` is the sound
        # canonicalization. The second constraint matches z3py byte-for-byte.
        assert str(_z3.Int('x') > 0) == "x > 0"
        assert str(_z3.Int('x') < 10) == "x < 10" == str(x < 10)


# ---------------------------------------------------------------------------
# ToReal / ToInt / IsInt
# ---------------------------------------------------------------------------

def test_toreal_sexpr_matches_z3py():
    assert z.ToReal(z.Int('x')).sexpr() == "(to_real x)"
    assert z.ToReal(z.Int('x')).sort().kind == "Real"
    if HAVE_Z3PY:
        assert z.ToReal(z.Int('x')).sexpr() == _z3.ToReal(_z3.Int('x')).sexpr()


def test_toreal_of_bool_is_ite():
    ctx = z.Context()  # isolate: 'b' is interned at other sorts in this session
    b = z.Bool('b', ctx)
    assert z.ToReal(b).sexpr() == "(ite b 1.0 0.0)"
    if HAVE_Z3PY:
        assert z.ToReal(b).sexpr() == _z3.ToReal(_z3.Bool('b')).sexpr()


def test_toreal_requires_int_or_bool():
    with pytest.raises(z.AyZ3Exception):
        z.ToReal(z.Real('r'))


def test_toint_sexpr_matches_z3py():
    assert z.ToInt(z.Real('r')).sexpr() == "(to_int r)"
    assert z.ToInt(z.Real('r')).sort().kind == "Int"
    if HAVE_Z3PY:
        assert z.ToInt(z.Real('r')).sexpr() == _z3.ToInt(_z3.Real('r')).sexpr()


def test_toint_requires_real():
    with pytest.raises(z.AyZ3Exception):
        z.ToInt(z.Int('x'))


def test_isint_sexpr_matches_z3py():
    assert z.IsInt(z.Real('r')).sexpr() == "(is_int r)"
    assert z.IsInt(z.Real('r')).sort().kind == "Bool"
    if HAVE_Z3PY:
        assert z.IsInt(z.Real('r')).sexpr() == _z3.IsInt(_z3.Real('r')).sexpr()


def test_isint_requires_real():
    with pytest.raises(z.AyZ3Exception):
        z.IsInt(z.Int('x'))


def test_isint_solve_example_matches_z3py():
    # The z3py IsInt docstring example: the only value of w in (0,1) with
    # w + 1/2 integral is 1/2.
    def run(M):
        w = M.Real('w')
        M.solve(M.IsInt(w + "1/2"), w > 0, w < 1)
    out = _capture(lambda: run(z))
    assert out == "[w = 1/2]"
    if HAVE_Z3PY:
        assert out == _capture(lambda: run(_z3))


def test_toreal_composes_in_solve():
    def run(M):
        n = M.Int('n')
        M.solve(M.ToReal(n) > 2.5, n < 4)
    out = _capture(lambda: run(z))
    assert out == "[n = 3]"
    if HAVE_Z3PY:
        assert out == _capture(lambda: run(_z3))


# ---------------------------------------------------------------------------
# IntToStr / StrToInt
# ---------------------------------------------------------------------------

def test_inttostr_sexpr_matches_z3py():
    assert z.IntToStr(z.Int('x')).sexpr() == "(str.from_int x)"
    assert z.IntToStr(z.Int('x')).sort().kind == "String"
    if HAVE_Z3PY:
        assert z.IntToStr(z.Int('x')).sexpr() == _z3.IntToStr(_z3.Int('x')).sexpr()


def test_strtoint_sexpr_matches_z3py():
    assert z.StrToInt(z.String('s')).sexpr() == "(str.to_int s)"
    assert z.StrToInt(z.String('s')).sort().kind == "Int"
    if HAVE_Z3PY:
        assert z.StrToInt(z.String('s')).sexpr() == _z3.StrToInt(_z3.String('s')).sexpr()


def test_inttostr_lifts_python_int():
    # A bare Python int is lifted to an Int literal.
    assert z.IntToStr(7).sort().kind == "String"


# ---------------------------------------------------------------------------
# Fresh*
# ---------------------------------------------------------------------------

def test_fresh_int_unique_and_usable_in_model():
    a, b = z.FreshInt(), z.FreshInt()
    assert a.ast != b.ast
    assert a.sexpr() != b.sexpr()
    assert a.sort().kind == "Int"
    # A fresh const is a real declared constant: it appears in a model.
    s = z.Solver()
    s.add(a == 7)
    assert s.check() == z.sat
    assert s.model()[a].as_long() == 7


def test_fresh_two_can_be_distinct():
    a, b = z.FreshInt(), z.FreshInt()
    s = z.Solver()
    s.add(a == 1, b == 2, a != b)
    assert s.check() == z.sat


def test_fresh_bool_sort():
    fb = z.FreshBool()
    assert fb.sort().kind == "Bool"


def test_fresh_real_sort():
    fr = z.FreshReal()
    assert fr.sort().kind == "Real"


def test_fresh_const_arbitrary_sort():
    fc = z.FreshConst(z.BitVecSort(8))
    assert fc.sort().kind == "BitVec"
    assert fc.sort().bv_size == 8


# ---------------------------------------------------------------------------
# Sqrt / Cbrt / Q  (rational-rendering divergence: AY `(/ 1 2)`, z3py `(/ 1.0 2.0)`)
# ---------------------------------------------------------------------------

def _strip_real_dot_zero(text):
    """Normalize `1.0` -> `1` so AY's `(/ 1 2)` and z3py's `(/ 1.0 2.0)` compare
    equal. The bare base of Sqrt(2) is `2.0` in both, so only the exponent's
    rational-component rendering differs."""
    return re.sub(r"(?<=\d)\.0(?=\D|$)", "", text)


def test_sqrt_is_power_half():
    e = z.Sqrt(2)
    assert e.sexpr() == "(^ 2.0 (/ 1 2))"
    if HAVE_Z3PY:
        # Same term modulo AY's `(/ 1 2)` vs z3py's `(/ 1.0 2.0)` rendering.
        assert _strip_real_dot_zero(e.sexpr()) == _strip_real_dot_zero(_z3.Sqrt(2).sexpr())


def test_cbrt_is_power_third():
    e = z.Cbrt(2)
    assert e.sexpr() == "(^ 2.0 (/ 1 3))"
    if HAVE_Z3PY:
        assert _strip_real_dot_zero(e.sexpr()) == _strip_real_dot_zero(_z3.Cbrt(2).sexpr())


def test_sqrt_of_real_expr():
    r = z.Real('r')
    assert z.Sqrt(r).sexpr() == "(^ r (/ 1 2))"


def test_sqrt_of_int_expr_rejected_like_z3py():
    # z3py itself raises on `IntRef ** '1/2'`; we match that (wrap in ToReal).
    with pytest.raises(z.AyZ3Exception):
        z.Sqrt(z.Int('x'))
    if HAVE_Z3PY:
        with pytest.raises(Exception):
            _z3.Sqrt(_z3.Int('x'))


def test_q_is_a_real_rational():
    q = z.Q(1, 3)
    assert q.sort().kind == "Real"
    # Q(1,3) * 3 == 1 is valid.
    s = z.Solver()
    s.add(z.Not(q * z.RealVal(3) == z.RealVal(1)))
    assert s.check() == z.unsat
    if HAVE_Z3PY:
        assert _strip_real_dot_zero(q.sexpr()) == _strip_real_dot_zero(_z3.Q(1, 3).sexpr())


# ---------------------------------------------------------------------------
# is_* predicates
# ---------------------------------------------------------------------------

def test_is_predicates():
    ctx = z.Context()  # isolate: 'b' is interned at other sorts in this session
    x, r, b, s = (z.Int('x', ctx), z.Real('r', ctx),
                  z.Bool('b', ctx), z.String('s', ctx))
    assert z.is_expr(x) and z.is_int(x) and not z.is_real(x)
    assert z.is_real(r) and not z.is_int(r)
    assert z.is_bool(b) and not z.is_bool(x)
    assert z.is_string(s)
    assert not z.is_expr(3)

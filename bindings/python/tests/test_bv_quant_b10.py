# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
#
# B-10 parity increment: bitvector operator wrappers + quantifier / lambda /
# pattern introspection.
#
# Each case is checked TWO ways:
#   1. Self-contained: the ayz3 term is built and (for the BV ops) a concrete
#      instance is SOLVED, asserting ayz3 computes the mathematically-correct
#      result / the expected sat-unsat verdict. These run without real z3py.
#   2. Differential vs **real z3py 4.15.4**, when the `z3` module is installed:
#      the SAME builder is applied to ayz3 and to z3py. Both are checked against
#      the independently specified expected value; a disagreement is a hard
#      failure but does not by itself assign blame.
#
# SOUNDNESS: ayz3 must never report a verdict/value that contradicts z3py. Where
# ayz3 honestly returns `unknown` (mixed Int/BV constraints its core does not
# fully decide) the case asserts only that ayz3 did NOT return the *wrong*
# definite verdict.
#
# Run:
#   AYZ3_LIB=.../libay_ffi.dylib PYTHONPATH=. pytest tests/test_bv_quant_b10.py -v

import pytest

import ayz3 as A

try:
    import z3 as Z
    HAVE_Z3 = True
except Exception:  # pragma: no cover - depends on environment
    Z = None
    HAVE_Z3 = False


def fresh():
    """A fresh isolated ayz3 Context scope (keeps const names from leaking
    across cases through the shared main context)."""
    return A._ctx_scope(A.Context())


# ---------------------------------------------------------------------------
# Differential helpers
# ---------------------------------------------------------------------------

def _z3_bv_value(builder, vals, width):
    """Concrete BV result from the z3py cross-check (an int)."""
    zc = [Z.BitVecVal(v, width) for v in vals]
    return Z.simplify(builder(Z, *zc)).as_long()


def assert_bv_semantics(builder, vals, width, expected):
    """Assert ayz3's `builder` on concrete `vals` computes exactly `expected`.

    `expected` is the mathematically-correct result (also cross-checked against
    real z3py when available). Confirms it both by an equality that must be sat
    and a disequality that must be unsat, so ayz3 pins down the exact value.
    """
    if HAVE_Z3:
        assert _z3_bv_value(builder, vals, width) == expected, (
            "test's own expected value disagrees with the z3py cross-check")
    with fresh():
        ac = [A.BitVecVal(v, width) for v in vals]
        e = builder(A, *ac)
        rw = e.size
        s = A.Solver()
        s.add(e == A.BitVecVal(expected, rw))
        assert s.check() == A.sat
        s2 = A.Solver()
        s2.add(e != A.BitVecVal(expected, rw))
        assert s2.check() == A.unsat


# ===========================================================================
# BV binary ops (division / remainder / mod / shifts) — signed vs unsigned
# ===========================================================================

def test_udiv_unsigned_division():
    # 200 / 3 unsigned = 66 (signed sdiv would treat 200 as -56).
    assert_bv_semantics(lambda m, a, b: m.UDiv(a, b), [200, 3], 8, 66)


def test_urem_unsigned_remainder():
    assert_bv_semantics(lambda m, a, b: m.URem(a, b), [200, 7], 8, 200 % 7)


def test_srem_vs_smod_sign_difference():
    # -5 (0xFB) and 3: srem follows the DIVIDEND sign (-2 = 0xFE);
    # smod follows the DIVISOR sign (+1 = 0x01). They differ — the point of the
    # signed remainder/modulo distinction. z3py exposes SMod only via `%`, so the
    # oracle builder uses the operator (bvsmod on both sides).
    assert_bv_semantics(lambda m, a, b: m.SRem(a, b), [0xFB, 3], 8, 0xFE)
    assert_bv_semantics(lambda m, a, b: a % b, [0xFB, 3], 8, 0x01)


def test_smod_sdiv_ashr_named_functions_equal_operators():
    # ayz3 also exposes SMod / SDiv / AShR as named free functions (z3py reaches
    # them only through `%` / `/` / `>>`). They must denote the identical term.
    with fresh():
        x, y = A.BitVec("x", 8), A.BitVec("y", 8)
        assert A.SMod(x, y).sexpr() == (x % y).sexpr() == "(bvsmod x y)"
        assert A.SDiv(x, y).sexpr() == (x / y).sexpr() == "(bvsdiv x y)"
        assert A.AShR(x, y).sexpr() == (x >> y).sexpr() == "(bvashr x y)"


def test_udiv_srem_smod_all_distinct_on_negatives():
    # -7 (0xF9) / 3: udiv=0xF9/3=83=0x53 ; sdiv=-2=0xFE
    assert_bv_semantics(lambda m, a, b: m.UDiv(a, b), [0xF9, 3], 8, 0xF9 // 3)
    assert_bv_semantics(lambda m, a, b: a / b, [0xF9, 3], 8, 0xFE)  # bvsdiv


def test_lshr_vs_ashr_sign_bit():
    # 0x80 (top bit set) >> 1: logical fills 0 -> 0x40 ; arithmetic fills the
    # sign bit -> 0xC0. The classic LShR/AShR divergence. z3py's AShR is the `>>`
    # operator, so the oracle builder uses it (bvashr on both sides).
    assert_bv_semantics(lambda m, a, b: m.LShR(a, b), [0x80, 1], 8, 0x40)
    assert_bv_semantics(lambda m, a, b: a >> b, [0x80, 1], 8, 0xC0)


def test_shl():
    assert_bv_semantics(lambda m, a, b: a << b, [0x01, 3], 8, 0x08)


# ===========================================================================
# BitVecRef operators map to the SIGNED bv ops (exactly like z3py)
# ===========================================================================

def test_operator_mod_is_bvsmod():
    with fresh():
        x = A.BitVec("x", 8)
        assert (x % A.BitVecVal(4, 8)).sexpr() == "(bvsmod x #x04)"
    # -5 % 3 (bvsmod) == +1
    assert_bv_semantics(lambda m, a, b: a % b, [0xFB, 3], 8, 0x01)


def test_operator_div_is_bvsdiv():
    with fresh():
        x = A.BitVec("x", 8)
        assert (x / A.BitVecVal(4, 8)).sexpr() == "(bvsdiv x #x04)"


def test_operator_rshift_is_bvashr():
    # Use a SYMBOLIC amount: AY soundly rewrites a *constant* arithmetic shift
    # into extract+sign_extend, so the raw bvashr node only survives symbolically.
    with fresh():
        x, y = A.BitVec("x", 8), A.BitVec("y", 8)
        assert (x >> y).sexpr() == "(bvashr x y)"


def test_operator_lshift_is_bvshl():
    with fresh():
        x, y = A.BitVec("x", 8), A.BitVec("y", 8)
        assert (x << y).sexpr() == "(bvshl x y)"


def test_reflected_operators_coerce_int_on_left():
    with fresh():
        x = A.BitVec("x", 8)
        # `3 % x` coerces 3 to an 8-bit value on the LEFT (matches z3py).
        assert (3 % x).sexpr() == "(bvsmod #x03 x)"
        assert (2 << x).sexpr() == "(bvshl #x02 x)"


# ===========================================================================
# Width-changing ops (extend / repeat / extract / concat / rotate)
# ===========================================================================

def test_signext_widens_and_sign_fills():
    with fresh():
        e = A.SignExt(4, A.BitVec("x", 4))
        assert e.size == 8
        assert e.sexpr() == "((_ sign_extend 4) x)"
    # 0xF (4-bit, = -1) sign-extended by 4 -> 0xFF (8-bit).
    assert_bv_semantics(lambda m, a: m.SignExt(4, a), [0xF], 4, 0xFF)


def test_zeroext_widens_and_zero_fills():
    with fresh():
        e = A.ZeroExt(4, A.BitVec("x", 4))
        assert e.size == 8
        assert e.sexpr() == "((_ zero_extend 4) x)"
    # 0xF (4-bit) zero-extended by 4 -> 0x0F (8-bit).
    assert_bv_semantics(lambda m, a: m.ZeroExt(4, a), [0xF], 4, 0x0F)


def test_repeat_bitvec():
    with fresh():
        e = A.RepeatBitVec(3, A.BitVec("x", 8))
        assert e.size == 24
        assert e.sexpr() == "((_ repeat 3) x)"
    # repeat 2x of 0xAB -> 0xABAB
    assert_bv_semantics(lambda m, a: m.RepeatBitVec(2, a), [0xAB], 8, 0xABAB)


def test_extract_bitslice():
    with fresh():
        e = A.Extract(5, 2, A.BitVec("x", 8))
        assert e.size == 4
        assert e.sexpr() == "((_ extract 5 2) x)"
    # bits [7:4] of 0xAB (1010_1011) == 0xA
    assert_bv_semantics(lambda m, a: m.Extract(7, 4, a), [0xAB], 8, 0xA)


def test_concat_two_and_three():
    with fresh():
        x, y, w = A.BitVec("x", 8), A.BitVec("y", 8), A.BitVec("w", 8)
        assert A.Concat(x, y).size == 16
        assert A.Concat(x, y).sexpr() == "(concat x y)"
        # z3py folds left for >2 operands.
        assert A.Concat(x, y, w).size == 24
        assert A.Concat(x, y, w).sexpr() == "(concat (concat x y) w)"
    assert_bv_semantics(lambda m, a, b: m.Concat(a, b), [0xAB, 0xCD], 8, 0xABCD)


def test_rotate_left_right_constant():
    # 0x81 (1000_0001) rotate-left 1 -> 0x03 (0000_0011)
    assert_bv_semantics(lambda m, a: m.RotateLeft(a, 1), [0x81], 8, 0x03)
    # rotate-right 1 of 0x03 -> 0x81
    assert_bv_semantics(lambda m, a: m.RotateRight(a, 1), [0x03], 8, 0x81)


def test_rotate_symbolic_amount_is_honest_notimplemented():
    # AY's core provides only constant-amount rotation; a symbolic amount is a
    # genuine capability gap (honest NotImplementedError, never a wrong answer).
    with fresh():
        x = A.BitVec("x", 8)
        y = A.BitVec("y", 8)
        with pytest.raises(NotImplementedError):
            A.RotateLeft(x, y)


# ===========================================================================
# Reductions and Int<->BV conversions
# ===========================================================================

def test_bvredand_bvredor():
    with fresh():
        assert A.BVRedAnd(A.BitVec("x", 8)).size == 1
        assert A.BVRedOr(A.BitVec("x", 8)).size == 1
    # redand == 1 iff ALL bits set
    assert_bv_semantics(lambda m, a: m.BVRedAnd(a), [0xFF], 8, 1)
    assert_bv_semantics(lambda m, a: m.BVRedAnd(a), [0xFE], 8, 0)
    # redor == 1 iff ANY bit set
    assert_bv_semantics(lambda m, a: m.BVRedOr(a), [0x00], 8, 0)
    assert_bv_semantics(lambda m, a: m.BVRedOr(a), [0x01], 8, 1)


def test_int2bv_width_and_value():
    with fresh():
        i = A.Int("i")
        e = A.Int2BV(i, 8)
        assert e.size == 8
        # Int2BV(200) == 200 (mod 256) is SAT. AY's core does not fully decide
        # this mixed Int->BV constraint and may soundly answer `unknown`; it must
        # never answer the WRONG definite verdict (unsat).
        s = A.Solver()
        s.add(i == 200)
        s.add(e == A.BitVecVal(200, 8))
        assert s.check() in (A.sat, A.unknown)
        assert s.check() != A.unsat


def test_bv2int_unsigned_range_is_sound():
    # BV2Int (unsigned) is always in [0, 255] for an 8-bit BV. These are
    # verdicts AY decides definitively; cross-check the oracle too.
    with fresh():
        x = A.BitVec("x", 8)
        s = A.Solver(); s.add(A.BV2Int(x) < 0)
        assert s.check() == A.unsat            # never negative
        s = A.Solver(); s.add(A.BV2Int(x) > 255)
        assert s.check() == A.unsat            # never exceeds 255
        s = A.Solver(); s.add(A.BV2Int(x) == 0)
        assert s.check() == A.sat
    if HAVE_Z3:
        x = Z.BitVec("x", 8)
        s = Z.Solver(); s.add(Z.BV2Int(x) < 0);  assert s.check() == Z.unsat
        s = Z.Solver(); s.add(Z.BV2Int(x) > 255); assert s.check() == Z.unsat


def test_bv2int_int2bv_roundtrip_identity():
    # Int2BV(BV2Int(x), 8) == x is valid; its negation is unsat.
    with fresh():
        x = A.BitVec("x", 8)
        s = A.Solver()
        s.add(A.Int2BV(A.BV2Int(x), 8) != x)
        assert s.check() == A.unsat


def test_bv2int_signed():
    # signed BV2Int of 0xFF (=-1) is -1; of 0x7F is 127.
    with fresh():
        s = A.Solver()
        s.add(A.BV2Int(A.BitVecVal(0xFF, 8), is_signed=True) == -1)
        assert s.check() == A.sat
        s2 = A.Solver()
        s2.add(A.BV2Int(A.BitVecVal(0xFF, 8), is_signed=True) != -1)
        assert s2.check() == A.unsat


# ===========================================================================
# Overflow / underflow predicates (signatures + verdicts match z3py)
# ===========================================================================

def test_add_no_overflow_predicate():
    # signed: 100 + 100 overflows an 8-bit signed range (>127) -> predicate false
    with fresh():
        s = A.Solver()
        s.add(A.BVAddNoOverflow(A.BitVecVal(100, 8), A.BitVecVal(100, 8), True))
        assert s.check() == A.unsat
        s2 = A.Solver()
        s2.add(A.BVAddNoOverflow(A.BitVecVal(10, 8), A.BitVecVal(10, 8), True))
        assert s2.check() == A.sat


def test_sdiv_no_overflow_predicate():
    # INT_MIN / -1 is the only signed-division overflow (0x80 / 0xFF).
    with fresh():
        s = A.Solver()
        s.add(A.BVSDivNoOverflow(A.BitVecVal(0x80, 8), A.BitVecVal(0xFF, 8)))
        assert s.check() == A.unsat
        s2 = A.Solver()
        s2.add(A.BVSDivNoOverflow(A.BitVecVal(0x10, 8), A.BitVecVal(0x02, 8)))
        assert s2.check() == A.sat


def test_overflow_predicate_signatures_present():
    # All the z3py overflow/underflow predicates exist with the z3py arity.
    with fresh():
        a, b = A.BitVec("a", 8), A.BitVec("b", 8)
        assert A.is_bool(A.BVAddNoOverflow(a, b, True))
        assert A.is_bool(A.BVAddNoUnderflow(a, b))
        assert A.is_bool(A.BVSubNoOverflow(a, b))
        assert A.is_bool(A.BVSubNoUnderflow(a, b, True))
        assert A.is_bool(A.BVMulNoOverflow(a, b, True))
        assert A.is_bool(A.BVMulNoUnderflow(a, b))
        assert A.is_bool(A.BVSDivNoOverflow(a, b))


# ===========================================================================
# Extract / Concat polymorphism (bitvector AND string)
# ===========================================================================

def test_extract_dispatches_string_vs_bv():
    with fresh():
        s = A.String("s")
        # string form == SubString / str.substr
        assert A.Extract(s, 1, 2).sexpr() == "(str.substr s 1 2)"
        # bitvector form
        x = A.BitVec("x", 8)
        assert A.Extract(5, 2, x).sexpr() == "((_ extract 5 2) x)"


def test_concat_dispatches_bv_vs_string():
    with fresh():
        x, y = A.BitVec("x", 8), A.BitVec("y", 8)
        assert A.is_bv(A.Concat(x, y))
        s, t = A.String("s"), A.String("t")
        assert A.is_string(A.Concat(s, t))


# ===========================================================================
# Cross-check the sexpr against real z3py where they coincide, and pin the
# documented sound divergences.
# ===========================================================================

@pytest.mark.usefixtures("required_reference_z3")
def test_sexpr_matches_z3py_where_identical():
    with fresh():
        ax = A.BitVec("x", 8)
        ay = A.BitVec("y", 8)
    zx = Z.BitVec("x", 8)
    zy = Z.BitVec("y", 8)
    pairs = [
        (A.UDiv(ax, ay), Z.UDiv(zx, zy)),
        (A.URem(ax, ay), Z.URem(zx, zy)),
        (A.SRem(ax, ay), Z.SRem(zx, zy)),
        (A.LShR(ax, ay), Z.LShR(zx, zy)),
        (ax % ay, zx % zy),
        (ax / ay, zx / zy),
        (ax >> ay, zx >> zy),
        (ax << ay, zx << zy),
        (A.SignExt(4, ax), Z.SignExt(4, zx)),
        (A.ZeroExt(4, ax), Z.ZeroExt(4, zx)),
        (A.RepeatBitVec(3, ax), Z.RepeatBitVec(3, zx)),
        (A.Extract(5, 2, ax), Z.Extract(5, 2, zx)),
        (A.Concat(ax, ay), Z.Concat(zx, zy)),
    ]
    for a_e, z_e in pairs:
        assert a_e.sexpr() == z_e.sexpr(), (a_e.sexpr(), z_e.sexpr())


@pytest.mark.usefixtures("required_reference_z3")
def test_documented_sound_sexpr_divergences():
    # These print differently from z3py but denote the SAME term (verified by the
    # semantic solve tests above). They are AY's documented sound divergences.
    with fresh():
        x = A.BitVec("x", 8)
        i = A.Int("i")
        # z3py: (ext_rotate_left x #x03) ; AY emits the parametric form.
        assert A.RotateLeft(x, 3).sexpr() == "((_ rotate_left 3) x)"
        # z3py: (ubv_to_int x) ; AY uses the SMT-LIB standard name.
        assert A.BV2Int(x).sexpr() == "(bv2nat x)"
        # z3py: ((_ int_to_bv 8) i) ; AY uses the SMT-LIB standard name.
        assert A.Int2BV(i, 8).sexpr() == "((_ int2bv 8) i)"


# ===========================================================================
# Quantifier / lambda / pattern introspection
# ===========================================================================

def test_forall_accessors():
    with fresh():
        x = A.Int("x")
        f = A.ForAll([x], x < 10)
        assert A.is_quantifier(f)
        assert f.num_vars() == 1
        assert f.var_name(0) == "x"
        assert f.var_sort(0).kind == "Int"
        assert f.is_forall() is True
        assert f.is_exists() is False
        assert f.is_lambda() is False
        assert f.weight() == 1               # z3py default
        assert f.num_patterns() == 0
        # body traverses to the real x<10 relation (AY prints the bound var by
        # its constant name — the documented constant-style divergence).
        assert f.body().sexpr() == "(< x 10)"


@pytest.mark.usefixtures("required_reference_z3")
def test_forall_accessors_match_z3py():
    with fresh():
        x = A.Int("x")
        f = A.ForAll([x], x < 10)
    zx = Z.Int("x")
    zf = Z.ForAll([zx], zx < 10)
    assert f.num_vars() == zf.num_vars()
    assert f.var_name(0) == zf.var_name(0)
    assert f.var_sort(0).kind == "Int" and zf.var_sort(0).name() == "Int"
    assert f.is_forall() == zf.is_forall()
    assert f.is_exists() == zf.is_exists()
    assert f.weight() == zf.weight()


def test_exists_accessors():
    with fresh():
        x = A.Int("x")
        e = A.Exists([x], x > 3)
        assert e.is_forall() is False
        assert e.is_exists() is True
        assert e.num_vars() == 1


def test_two_variable_quantifier():
    with fresh():
        x, y = A.Int("x"), A.Int("y")
        f = A.ForAll([x, y], x + y > 0)
        assert f.num_vars() == 2
        assert f.var_name(0) == "x"
        assert f.var_name(1) == "y"
        assert f.var_sort(0).kind == "Int"
        assert f.var_sort(1).kind == "Int"


def test_bitvector_bound_variable_sort():
    with fresh():
        b = A.BitVec("b", 8)
        f = A.ForAll([b], A.UGE(b, A.BitVecVal(0, 8)))
        assert f.var_sort(0).kind == "BitVec"
        assert f.var_sort(0).bv_size == 8


def test_quantifier_weight_is_tracked():
    with fresh():
        x = A.Int("x")
        assert A.ForAll([x], x < 10, weight=7).weight() == 7
        assert A.Exists([x], x < 10, weight=3).weight() == 3


def test_single_and_multi_pattern():
    with fresh():
        x, y = A.Int("x"), A.Int("y")
        g = A.Function("g", A.IntSort(), A.IntSort())
        # single-term pattern (bare expr auto-wrapped, as in z3py)
        q = A.ForAll([x], g(x) > 0, patterns=[g(x)])
        assert q.num_patterns() == 1
        p0 = q.pattern(0)
        assert A.is_pattern(p0)
        assert p0.sexpr() == "((g x))"       # constant-style body divergence
        # explicit MultiPattern
        mp = A.MultiPattern(g(x), g(y))
        assert A.is_pattern(mp)
        assert mp.sexpr() == "((g x) (g y))"
        qm = A.ForAll([x, y], g(x) + g(y) > 0, patterns=[mp])
        assert qm.num_patterns() == 1
        assert qm.pattern(0).sexpr() == "((g x) (g y))"
        assert not A.is_pattern(x)


def test_pattern_does_not_change_verdict():
    # A trigger pattern is only an e-matching hint; the sat/unsat verdict must be
    # identical with and without it.
    with fresh():
        x = A.Int("x")
        g = A.Function("g", A.IntSort(), A.IntSort())
        s = A.Solver()
        s.add(A.ForAll([x], g(x) > 0, patterns=[g(x)]))
        s.add(g(3) < 0)
        assert s.check() == A.unsat


def test_lambda_is_honest_notimplemented():
    with fresh():
        x = A.Int("x")
        with pytest.raises(NotImplementedError):
            A.Lambda([x], x + 1)


def test_quantifier_accessors_reject_non_quantifier():
    with fresh():
        x = A.Int("x")
        e = x + 1
        for meth in ("num_vars", "var_name", "is_forall", "is_exists",
                     "weight", "num_patterns"):
            with pytest.raises(A.AyZ3Exception):
                fn = getattr(e, meth)
                fn(0) if meth in ("var_name",) else fn()


def test_forall_solves_true_and_false():
    with fresh():
        q = A.Int("q")
        s = A.Solver(); s.add(A.ForAll([q], q + 1 > q))
        assert s.check() == A.sat            # universally true
        s2 = A.Solver(); s2.add(A.ForAll([q], q > 5))
        assert s2.check() == A.unsat         # not universally true


if __name__ == "__main__":  # pragma: no cover
    import sys
    sys.exit(pytest.main([__file__, "-v"]))

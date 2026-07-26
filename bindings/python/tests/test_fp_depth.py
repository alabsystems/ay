# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
#
# Deep floating-point parity tests for ayz3's NATIVE FP layer (Z3_mk_fpa_*
# handles), cross-checked value-for-value against real z3py 4.15.4.
#
# Every determinate fact is checked under BOTH ayz3 and z3py and the verdicts
# (and, where read out, the concrete values / reprs) are diffed. A wrong FP
# value or rounding is DISQUALIFYING, so nothing here asserts ay-only facts
# for behavior z3py also decides.
#
# NOTE on const names: ayz3 interns consts by NAME process-wide (shared main
# context), so all FP consts in this file use the file-unique `fpd_` prefix.
#
# Run:  AYZ3_LIB=.../libay_ffi.dylib pytest bindings/python/tests/test_fp_depth.py -v

import math
import struct

import pytest

import ayz3 as z

try:
    import z3 as _z3
    HAVE_Z3PY = True
except Exception:  # pragma: no cover
    _z3 = None
    HAVE_Z3PY = False

requires_z3 = pytest.mark.usefixtures("required_reference_z3")


def _f32(x):
    return struct.unpack("<f", struct.pack("<f", x))[0]


def _check(c):
    s = z.Solver()
    s.add(c)
    return str(s.check())


def _z3_check(c):
    s = _z3.Solver()
    s.add(c)
    return str(s.check())


# Rounding-mode pairs (ayz3 builder, z3py builder), asserted over ALL modes.
_RMS = [
    ("RNE", lambda: z.RNE(), lambda: _z3.RNE()),
    ("RNA", lambda: z.RNA(), lambda: _z3.RNA()),
    ("RTP", lambda: z.RTP(), lambda: _z3.RTP()),
    ("RTN", lambda: z.RTN(), lambda: _z3.RTN()),
    ("RTZ", lambda: z.RTZ(), lambda: _z3.RTZ()),
]


# ---------------------------------------------------------------------------
# Sorts and rounding modes
# ---------------------------------------------------------------------------


def test_fp_sort_surface_matches_z3py():
    for mk_ay, mk_z3 in [
        (z.Float16, _z3.Float16), (z.FloatHalf, _z3.FloatHalf),
        (z.Float32, _z3.Float32), (z.FloatSingle, _z3.FloatSingle),
        (z.Float64, _z3.Float64), (z.FloatDouble, _z3.FloatDouble),
        (z.Float128, _z3.Float128), (z.FloatQuadruple, _z3.FloatQuadruple),
    ] if HAVE_Z3PY else []:
        a, b = mk_ay(), mk_z3()
        assert a.ebits() == b.ebits() and a.sbits() == b.sbits()
        assert repr(a) == repr(b)
    s = z.FPSort(9, 30)
    assert s.ebits() == 9 and s.sbits() == 30
    assert z.is_fp_sort(s) and not z.is_fprm_sort(s)


@requires_z3
def test_fp_rounding_mode_reprs_match_z3py():
    for name, mk_ay, mk_z3 in _RMS:
        assert repr(mk_ay()) == repr(mk_z3())
    assert repr(z.RoundNearestTiesToEven()) == repr(_z3.RoundNearestTiesToEven())
    assert repr(z.RoundTowardZero()) == repr(_z3.RoundTowardZero())
    assert z.is_fprm(z.RNE()) and z.is_fprm_value(z.RTN())
    rm = z.FP("fpd_rmnot", z.Float32())
    assert not z.is_fprm(rm)


@requires_z3
def test_fp_default_rounding_mode_and_sort():
    assert repr(z.get_default_rounding_mode()) == repr(_z3.get_default_rounding_mode())
    assert repr(z.get_default_fp_sort()) == repr(_z3.get_default_fp_sort())


# ---------------------------------------------------------------------------
# Values: repr / accessors, value-for-value vs z3py
# ---------------------------------------------------------------------------


@requires_z3
@pytest.mark.parametrize("v", [1.0, 1.5, 2.0, 3.75, -2.5, 0.1, 100.0, 0.5,
                               -0.0, 0.0, 6.5e-4, 1e-45, 3.14159, -1e38])
def test_fpval_repr_and_fields_match_z3py_float32(v):
    a = z.FPVal(v, z.Float32())
    b = _z3.FPVal(v, _z3.Float32())
    assert repr(a) == repr(b)
    if v == v and abs(v) != float("inf") and v != 0.0:
        assert a.sign() == b.sign()
        assert a.significand() == b.significand()
        assert a.exponent() == b.exponent()
        assert a.significand_as_long() == b.significand_as_long()
        assert a.exponent_as_long() == b.exponent_as_long()
        assert a.exponent_as_long(False) == b.exponent_as_long(False)


@requires_z3
@pytest.mark.parametrize("v", [1.0, 0.1, 3.141592653589793, -2.5e300, 5e-324])
def test_fpval_repr_matches_z3py_float64(v):
    assert repr(z.FPVal(v, z.Float64())) == repr(_z3.FPVal(v, _z3.Float64()))


@requires_z3
def test_fpval_specials_match_z3py():
    f, g = z.Float32(), _z3.Float32()
    assert repr(z.fpNaN(f)) == repr(_z3.fpNaN(g))
    assert repr(z.fpPlusInfinity(f)) == repr(_z3.fpPlusInfinity(g))
    assert repr(z.fpMinusInfinity(f)) == repr(_z3.fpMinusInfinity(g))
    assert repr(z.fpPlusZero(f)) == repr(_z3.fpPlusZero(g))
    assert repr(z.fpMinusZero(f)) == repr(_z3.fpMinusZero(g))
    assert repr(z.fpInfinity(f, True)) == repr(_z3.fpInfinity(g, True))
    assert repr(z.fpZero(f, True)) == repr(_z3.fpZero(g, True))
    assert repr(z.FPVal("NaN", f)) == repr(_z3.FPVal("NaN", g))


@requires_z3
def test_fpval_from_string_matches_z3py():
    for s in ["1.5", "-2.5", "0.1", "100"]:
        assert repr(z.FPVal(s, z.Float32())) == repr(_z3.FPVal(s, _z3.Float32()))


def test_fp_num_predicates():
    f = z.Float32()
    assert z.fpNaN(f).isNaN() and not z.fpNaN(f).isInf()
    assert z.fpPlusInfinity(f).isInf() and z.fpPlusInfinity(f).isPositive()
    assert z.fpMinusZero(f).isZero() and z.fpMinusZero(f).isNegative()
    assert z.FPVal(1.5, f).isNormal() and not z.FPVal(1.5, f).isSubnormal()
    assert z.FPVal(1e-45, f).isSubnormal()
    assert z.is_fp_value(z.FPVal(1.5, f))
    assert not z.is_fp_value(z.FP("fpd_notval", f))


# ---------------------------------------------------------------------------
# Arithmetic under EVERY rounding mode, value-for-value vs z3py
# ---------------------------------------------------------------------------


@requires_z3
@pytest.mark.parametrize("rm_name,ay_rm,z3_rm", _RMS)
@pytest.mark.parametrize("op_name", ["add", "sub", "mul", "div", "sqrt", "rti"])
def test_fp_ops_all_rounding_modes_match_z3py(rm_name, ay_rm, z3_rm, op_name):
    # Operand pairs chosen so rounding direction matters (inexact results).
    f, g = z.Float32(), _z3.Float32()
    pairs = [(1.0, 3.0), (0.1, 0.2), (-1.0, 3.0), (2.5, -0.7)]
    for (p, q) in pairs:
        pa, qa = z.FPVal(p, f), z.FPVal(q, f)
        pz, qz = _z3.FPVal(p, g), _z3.FPVal(q, g)
        if op_name == "add":
            ea, ez = z.fpAdd(ay_rm(), pa, qa), _z3.fpAdd(z3_rm(), pz, qz)
        elif op_name == "sub":
            ea, ez = z.fpSub(ay_rm(), pa, qa), _z3.fpSub(z3_rm(), pz, qz)
        elif op_name == "mul":
            ea, ez = z.fpMul(ay_rm(), pa, qa), _z3.fpMul(z3_rm(), pz, qz)
        elif op_name == "div":
            ea, ez = z.fpDiv(ay_rm(), pa, qa), _z3.fpDiv(z3_rm(), pz, qz)
        elif op_name == "sqrt":
            if p < 0:
                continue
            ea, ez = z.fpSqrt(ay_rm(), pa), _z3.fpSqrt(z3_rm(), pz)
        else:
            ea, ez = z.fpRoundToIntegral(ay_rm(), qa), _z3.fpRoundToIntegral(z3_rm(), qz)
        # Read the concrete result from each side's model and compare reprs.
        xa = z.FP(f"fpd_r_{rm_name}_{op_name}", f)
        sa = z.Solver(); sa.add(xa == ea)
        assert sa.check() == z.sat
        xz = _z3.FP("res", g)
        sz = _z3.Solver(); sz.add(xz == ez)
        assert str(sz.check()) == "sat"
        assert repr(sa.model()[xa]) == repr(sz.model()[xz]), (rm_name, op_name, p, q)


@requires_z3
def test_fp_fma_single_rounding_matches_z3py():
    # fma rounds ONCE: fma(a, b, c) != round(a*b)+c in general.
    f, g = z.Float64(), _z3.Float64()
    cases = [(0.1, 0.2, 0.3), (1e16, 1e16, -1e32), (3.0, 7.0, -21.0)]
    for (a, b, c) in cases:
        ea = z.fpFMA(z.RNE(), z.FPVal(a, f), z.FPVal(b, f), z.FPVal(c, f))
        ez = _z3.fpFMA(_z3.RNE(), _z3.FPVal(a, g), _z3.FPVal(b, g), _z3.FPVal(c, g))
        xa = z.FP("fpd_fma", f); sa = z.Solver(); sa.add(xa == ea)
        xz = _z3.FP("res", g); sz = _z3.Solver(); sz.add(xz == ez)
        assert sa.check() == z.sat and str(sz.check()) == "sat"
        assert repr(sa.model()[xa]) == repr(sz.model()[xz]), (a, b, c)
        # And the independently calculated Python-float expectation (FMA rounds once).
        assert float(sa.model()[xa]) == float(math.fma(a, b, c))


@requires_z3
def test_fp_min_max_rem_abs_neg_match_z3py():
    f, g = z.Float32(), _z3.Float32()
    for (p, q) in [(2.0, 3.0), (-2.0, 3.0), (5.0, 3.0), (-7.5, -2.5)]:
        for mk_ay, mk_z3 in [(z.fpMin, _z3.fpMin), (z.fpMax, _z3.fpMax), (z.fpRem, _z3.fpRem)]:
            xa = z.FP("fpd_mmr", f); sa = z.Solver()
            sa.add(xa == mk_ay(z.FPVal(p, f), z.FPVal(q, f)))
            xz = _z3.FP("res", g); sz = _z3.Solver()
            sz.add(xz == mk_z3(_z3.FPVal(p, g), _z3.FPVal(q, g)))
            assert sa.check() == z.sat and str(sz.check()) == "sat"
            assert repr(sa.model()[xa]) == repr(sz.model()[xz]), (mk_ay, p, q)
    assert _check(z.fpEQ(z.fpAbs(z.FPVal(-2.5, f)), z.FPVal(2.5, f))) == "sat"
    assert _check(z.fpEQ(z.fpNeg(z.FPVal(-2.5, f)), z.FPVal(2.5, f))) == "sat"
    assert _z3_check(_z3.fpEQ(_z3.fpAbs(_z3.FPVal(-2.5, g)), _z3.FPVal(2.5, g))) == "sat"


@requires_z3
def test_fp_div_by_zero_and_overflow_match_z3py():
    f, g = z.Float32(), _z3.Float32()
    # 1/ +0 -> +oo ; 1 / -0 -> -oo ; 0/0 -> NaN ; overflow -> +oo.
    facts = [
        (z.fpEQ(z.fpDiv(z.RNE(), z.FPVal(1.0, f), z.fpPlusZero(f)), z.fpPlusInfinity(f)),
         _z3.fpEQ(_z3.fpDiv(_z3.RNE(), _z3.FPVal(1.0, g), _z3.fpPlusZero(g)), _z3.fpPlusInfinity(g))),
        (z.fpEQ(z.fpDiv(z.RNE(), z.FPVal(1.0, f), z.fpMinusZero(f)), z.fpMinusInfinity(f)),
         _z3.fpEQ(_z3.fpDiv(_z3.RNE(), _z3.FPVal(1.0, g), _z3.fpMinusZero(g)), _z3.fpMinusInfinity(g))),
        (z.fpIsNaN(z.fpDiv(z.RNE(), z.fpPlusZero(f), z.fpPlusZero(f))),
         _z3.fpIsNaN(_z3.fpDiv(_z3.RNE(), _z3.fpPlusZero(g), _z3.fpPlusZero(g)))),
        (z.fpEQ(z.fpMul(z.RNE(), z.FPVal(3e38, f), z.FPVal(3e38, f)), z.fpPlusInfinity(f)),
         _z3.fpEQ(_z3.fpMul(_z3.RNE(), _z3.FPVal(3e38, g), _z3.FPVal(3e38, g)), _z3.fpPlusInfinity(g))),
    ]
    for ac, zc in facts:
        assert _check(ac) == _z3_check(zc) == "sat"


@requires_z3
def test_fp_float64_famous_inequality_matches_z3py():
    # 0.1 + 0.2 != 0.3 in float64 — both solvers must agree it is UNSAT to
    # assert equality.
    f, g = z.Float64(), _z3.Float64()
    ac = z.fpEQ(z.fpAdd(z.RNE(), z.FPVal(0.1, f), z.FPVal(0.2, f)), z.FPVal(0.3, f))
    zc = _z3.fpEQ(_z3.fpAdd(_z3.RNE(), _z3.FPVal(0.1, g), _z3.FPVal(0.2, g)), _z3.FPVal(0.3, g))
    assert _check(ac) == _z3_check(zc) == "unsat"


# ---------------------------------------------------------------------------
# Predicates and comparisons, verdict-for-verdict vs z3py
# ---------------------------------------------------------------------------


@requires_z3
def test_fp_classification_predicates_match_z3py():
    f, g = z.Float32(), _z3.Float32()
    vals = [1.5, -1.5, 0.0, -0.0, 1e-45, float("inf"), float("-inf"), float("nan")]
    preds = [
        (z.fpIsNaN, _z3.fpIsNaN), (z.fpIsInf, _z3.fpIsInf),
        (z.fpIsZero, _z3.fpIsZero), (z.fpIsNormal, _z3.fpIsNormal),
        (z.fpIsSubnormal, _z3.fpIsSubnormal),
        (z.fpIsNegative, _z3.fpIsNegative), (z.fpIsPositive, _z3.fpIsPositive),
    ]
    for v in vals:
        for pa, pz in preds:
            assert _check(pa(z.FPVal(v, f))) == _z3_check(pz(_z3.FPVal(v, g))), (v, pz)


@requires_z3
def test_fp_comparison_operators_match_z3py():
    f, g = z.Float32(), _z3.Float32()
    import operator
    for (p, q) in [(1.0, 2.0), (2.0, 2.0), (3.0, 2.0), (float("nan"), 2.0), (-0.0, 0.0)]:
        for op in (operator.lt, operator.le, operator.gt, operator.ge):
            ac = op(z.FPVal(p, f), z.FPVal(q, f))
            zc = op(_z3.FPVal(p, g), _z3.FPVal(q, g))
            assert _check(ac) == _z3_check(zc), (p, q, op)
    # fpNEQ is Not(fp.eq) on both sides.
    assert _check(z.fpNEQ(z.fpNaN(f), z.fpNaN(f))) == \
        _z3_check(_z3.fpNEQ(_z3.fpNaN(g), _z3.fpNaN(g))) == "sat"


# ---------------------------------------------------------------------------
# Conversions, value-for-value
# ---------------------------------------------------------------------------


@requires_z3
@pytest.mark.parametrize("rm_name,ay_rm,z3_rm", _RMS)
def test_fp_narrowing_conversion_matches_z3py(rm_name, ay_rm, z3_rm):
    # Float64 -> Float32 narrowing rounds per rounding mode.
    for v in [0.1, 1.0 / 3.0, -2.5000000001, 1e-40]:
        xa = z.FP(f"fpd_nar_{rm_name}", z.Float32())
        sa = z.Solver()
        sa.add(xa == z.fpToFP(ay_rm(), z.FPVal(v, z.Float64()), z.Float32()))
        xz = _z3.FP("res", _z3.Float32())
        sz = _z3.Solver()
        sz.add(xz == _z3.fpToFP(z3_rm(), _z3.FPVal(v, _z3.Float64()), _z3.Float32()))
        assert sa.check() == z.sat and str(sz.check()) == "sat"
        assert repr(sa.model()[xa]) == repr(sz.model()[xz]), (rm_name, v)


@requires_z3
def test_fp_signed_bv_roundtrip_matches_z3py():
    # signed BV -> FP for every 8-bit value class: negative, zero, positive.
    for n in [-128, -5, -1, 0, 1, 7, 127]:
        xa = z.FP("fpd_sbv", z.Float32())
        sa = z.Solver()
        sa.add(xa == z.fpToFP(z.RNE(), z.BitVecVal(n, 8), z.Float32()))
        xz = _z3.FP("res", _z3.Float32())
        sz = _z3.Solver()
        sz.add(xz == _z3.fpToFP(_z3.RNE(), _z3.BitVecVal(n, 8), _z3.Float32()))
        assert sa.check() == z.sat and str(sz.check()) == "sat"
        assert repr(sa.model()[xa]) == repr(sz.model()[xz]) and float(sa.model()[xa]) == float(n)


@requires_z3
def test_fp_to_fp_python_number_rejected_like_z3py():
    # z3py 4.15.4 rejects fpToFP(rm, <python float>, sort) ("Unsupported
    # combination..."); ayz3 mirrors that shape exactly. FPVal(v, sort) is the
    # supported way to land a Python number, and it rounds identically (see
    # the FPVal repr/field parity tests above).
    with pytest.raises(_z3.Z3Exception):
        _z3.fpToFP(_z3.RNE(), 1.5, _z3.Float32())
    with pytest.raises(z.AyZ3Exception):
        z.fpToFP(z.RNE(), 1.5, z.Float32())


# ---------------------------------------------------------------------------
# Solving with FP unknowns / model interaction (incl. one full SOLVE)
# ---------------------------------------------------------------------------


def test_fp_solve_sat_with_model():
    # The acceptance SOLVE: sat + a model that satisfies the constraint.
    f = z.Float32()
    x, a, b = z.FPs("fpd_sx fpd_sa fpd_sb", f)
    s = z.Solver()
    s.add(a == z.FPVal(1.5, f))
    s.add(b == z.FPVal(2.25, f))
    s.add(z.fpEQ(x, z.fpAdd(z.RNE(), a, b)))
    assert s.check() == z.sat
    m = s.model()
    assert float(m[x]) == 3.75
    assert repr(m[x]) == "1.875*(2**1)"
    if HAVE_Z3PY:
        g = _z3.Float32()
        xz, az, bz = _z3.FPs("x a b", g)
        sz = _z3.Solver()
        sz.add(az == _z3.FPVal(1.5, g), bz == _z3.FPVal(2.25, g),
               _z3.fpEQ(xz, _z3.fpAdd(_z3.RNE(), az, bz)))
        assert str(sz.check()) == "sat"
        assert repr(sz.model()[xz]) == repr(m[x])


def test_fp_model_eval_expression():
    f = z.Float32()
    x = z.FP("fpd_ev_x", f)
    y = z.FP("fpd_ev_y", f)
    s = z.Solver()
    s.add(x == z.FPVal(2.0, f))
    s.add(y == z.fpMul(z.RNE(), x, x))
    assert s.check() == z.sat
    m = s.model()
    # m.eval of a declared FP const reduces to a concrete FPNumRef.
    assert float(m.eval(x)) == 2.0
    assert float(m[y]) == 4.0
    # DOCUMENTED DIVERGENCE: AY's Z3_model_eval substitutes but does not
    # constant-fold a COMPOUND FP term (z3py folds it to a numeral). ayz3
    # returns the honest, unreduced term rather than fabricating a value.
    v = m.eval(z.fpMul(z.RNE(), x, x))
    assert z.is_fp(v)


def test_fp_mixed_with_bool_and_bv():
    # FP constraints coexist with Bool/BV constraints in ONE solver (native
    # handles; no fragment splitting).
    f = z.Float32()
    x = z.FP("fpd_mix_x", f)
    p = z.Bool("fpd_mix_p")
    n = z.BitVec("fpd_mix_n", 8)
    s = z.Solver()
    s.add(z.Implies(p, z.fpGT(x, z.FPVal(1.0, f))))
    s.add(p)
    s.add(n == z.BitVecVal(3, 8))
    s.add(z.fpLT(x, z.FPVal(2.0, f)))
    assert s.check() == z.sat
    m = s.model()
    assert 1.0 < float(m[x]) < 2.0
    assert m[n].as_long() == 3


def test_fp_push_pop():
    f = z.Float32()
    x = z.FP("fpd_pp_x", f)
    s = z.Solver()
    s.add(z.fpGT(x, z.FPVal(0.0, f)))
    assert s.check() == z.sat
    s.push()
    s.add(z.fpLT(x, z.FPVal(0.0, f)))
    assert s.check() == z.unsat
    s.pop()
    assert s.check() == z.sat


def test_fp_operator_default_rm_is_rne():
    # x = 0.1 + 0.2 via Python operators (default RNE), checked in float64.
    f = z.Float64()
    x = z.FP("fpd_dflt_x", f)
    s = z.Solver()
    s.add(x == z.FPVal(0.1, f) + z.FPVal(0.2, f))
    assert s.check() == z.sat
    assert float(s.model()[x]) == 0.1 + 0.2  # exact double semantics


def test_fp_python_number_coercion():
    # Bare Python numbers coerce to the FP operand's sort (like z3py).
    f = z.Float32()
    x = z.FP("fpd_co_x", f)
    s = z.Solver()
    s.add(z.fpEQ(x + 1.0, z.FPVal(2.5, f)))
    assert s.check() == z.sat
    assert _f32(float(s.model()[x]) + 1.0) == 2.5


def test_fp_cross_context_reuse():
    # A constraint built once (main context) is added to TWO independent
    # solvers — exercising the cross-context FP rebuild path end-to-end.
    f = z.Float32()
    x = z.FP("fpd_cc_x", f)
    c = z.fpEQ(z.fpAdd(z.RNE(), x, z.FPVal(1.0, f)), z.FPVal(2.0, f))
    s1, s2 = z.Solver(), z.Solver()
    s1.add(c)
    s2.add(c)
    s2.add(z.fpLT(x, z.FPVal(0.0, f)))
    assert s1.check() == z.sat
    assert s2.check() == z.unsat


def test_fp_cross_context_ops_roundtrip():
    # Rebuild coverage for sqrt/fma/min/max/rem/rti/abs/neg/specials/to_fp.
    f = z.Float32()
    x = z.FP("fpd_ops_x", f)
    c = z.And(
        z.fpEQ(z.fpSqrt(z.RTZ(), z.FPVal(2.0, f)), z.fpSqrt(z.RTZ(), z.FPVal(2.0, f))),
        z.fpEQ(z.fpFMA(z.RNE(), x, z.FPVal(1.0, f), z.fpPlusZero(f)), x),
        z.fpEQ(z.fpMin(x, x), z.fpMax(x, x)),
        z.fpEQ(z.fpRoundToIntegral(z.RTN(), z.FPVal(2.5, f)), z.FPVal(2.0, f)),
        z.fpEQ(z.fpAbs(z.fpNeg(x)), z.fpAbs(x)),
        z.fpLT(z.fpMinusInfinity(f), z.FPVal(0.0, f)),
        z.fpEQ(z.fpToFP(z.RNE(), z.BitVecVal(2, 8), f), z.FPVal(2.0, f)),
        z.fpEQ(x, z.FPVal(4.25, f)),
        z.Not(z.fpIsNaN(x)),
        z.fpIsNormal(x),
    )
    s = z.Solver()
    s.add(c)
    assert s.check() == z.sat
    assert float(s.model()[x]) == 4.25


def test_fp_unsat_core_of_fp_constraints():
    f = z.Float32()
    x = z.FP("fpd_core_x", f)
    s = z.Solver()
    p1, p2 = z.Bools("fpd_core_p1 fpd_core_p2")
    s.assert_and_track(z.fpGT(x, z.FPVal(1.0, f)), p1)
    s.assert_and_track(z.fpLT(x, z.FPVal(0.0, f)), p2)
    assert s.check() == z.unsat
    core = s.unsat_core()
    assert len(core) >= 1


# ---------------------------------------------------------------------------
# Sort/expression predicates and misc parity
# ---------------------------------------------------------------------------


@requires_z3
def test_fp_is_predicates_match_z3py():
    f, g = z.Float32(), _z3.Float32()
    xa, xz = z.FP("fpd_isp_x", f), _z3.FP("x", g)
    va, vz = z.FPVal(1.5, f), _z3.FPVal(1.5, g)
    for (aa, zz) in [(xa, xz), (va, vz)]:
        assert z.is_fp(aa) == _z3.is_fp(zz)
        assert z.is_fp_value(aa) == _z3.is_fp_value(zz)
    assert z.is_fp_sort(f) == _z3.is_fp_sort(g) is True
    assert z.is_fp_sort(z.IntSort()) == _z3.is_fp_sort(_z3.IntSort()) is False
    assert z.is_fprm_value(z.RNE()) == _z3.is_fprm_value(_z3.RNE()) is True
    assert z.is_fprm_value(xa) == _z3.is_fprm_value(xz) is False


@requires_z3
def test_fp_sort_of_expression_matches_z3py():
    f = z.FPSort(5, 11)
    x = z.FP("fpd_srt_x", f)
    zx = _z3.FP("x", _z3.FPSort(5, 11))
    assert repr(x.sort()) == repr(zx.sort())
    assert x.ebits() == zx.ebits() and x.sbits() == zx.sbits()
    assert x.sort() == z.Float16()


def test_fpval_int_and_fraction():
    from fractions import Fraction
    f = z.Float32()
    assert float(z.FPVal(2, f)) == 2.0
    assert float(z.FPVal(Fraction(15, 4), f)) == 3.75
    assert float(z.FPVal("15/4", f)) == 3.75


def test_fp_wrong_sort_mix_raises():
    with pytest.raises(z.AyZ3Exception):
        z.fpAdd(z.RNE(), z.FPVal(1.0, z.Float32()), z.FPVal(1.0, z.Float64()))
    with pytest.raises(z.AyZ3Exception):
        z.fpAdd(z.FPVal(1.0, z.Float32()), z.FPVal(1.0, z.Float32()),
                z.FPVal(1.0, z.Float32()))  # first arg must be an RM


@requires_z3
def test_fp_real_to_fp_now_native():
    # FIXED-BUG PIN (flipped): fpToFP(rm, RealRef, sort) used to raise the
    # honest NotImplementedError while Z3_mk_fpa_to_fp_real was absent from
    # libay_ffi; the FPA completion exports it, so it must now MATCH z3py.
    a = z.fpToFP(z.RNE(), z.RealVal("1/3"), z.Float32())
    b = _z3.fpToFP(_z3.RNE(), _z3.RealVal("1/3"), _z3.Float32())
    assert _z3.is_fp(b)
    assert isinstance(a, z.FPRef)
    sa, sb = z.Solver(), _z3.Solver()
    xa = z.FP("fpc_r2f_pin", z.Float32())
    xb = _z3.FP("fpc_r2f_pin", _z3.Float32())
    sa.add(xa == a)
    sb.add(xb == b)
    assert str(sa.check()) == str(sb.check()) == "sat"
    assert repr(sa.model()[xa]) == repr(sb.model()[xb])
    a2 = z.fpRealToFP(z.RNE(), z.RealVal("1/3"), z.Float32())
    assert isinstance(a2, z.FPRef)


# ---------------------------------------------------------------------------
# Conversion set (stage-2 wiring of the FPA C-API completion): every verdict
# and model repr cross-checked against z3py. Const names use unique fpc_
# prefixes (ayz3 interns consts by name process-wide).
# ---------------------------------------------------------------------------


def _model_of(mk_ay, mk_z3, name, mk_sort_ay, mk_sort_z3):
    """Solve `var == <term>` under both stacks; return (verdicts, reprs)."""
    sa, sb = z.Solver(), _z3.Solver()
    xa = mk_sort_ay(name)
    xb = mk_sort_z3(name)
    sa.add(xa == mk_ay())
    sb.add(xb == mk_z3())
    ra, rb = str(sa.check()), str(sb.check())
    va = repr(sa.model()[xa]) if ra == "sat" else None
    vb = repr(sb.model()[xb]) if rb == "sat" else None
    return (ra, rb), (va, vb)


def _fp32(name):
    return z.FP(name, z.Float32())


def _zfp32(name):
    return _z3.FP(name, _z3.Float32())


_RM5 = [("RNE", lambda m: getattr(z, m)(), lambda m: getattr(_z3, m)())
        for m in ["RNE", "RNA", "RTP", "RTN", "RTZ"]]


@requires_z3
@pytest.mark.parametrize("bits", [0x3f800000, 0xbf000000, 0x00000001,
                                  0x7f800000, 0xff800000, 0x7fc00000,
                                  0x80000000, 0x40490fdb])
def test_fpc_bv_to_fp_ieee_bits(bits):
    (ra, rb), (va, vb) = _model_of(
        lambda: z.fpBVToFP(z.BitVecVal(bits, 32), z.Float32()),
        lambda: _z3.fpBVToFP(_z3.BitVecVal(bits, 32), _z3.Float32()),
        f"fpc_b2f_{bits:08x}", _fp32, _zfp32)
    assert ra == rb == "sat"
    assert va == vb


@requires_z3
def test_fpc_to_fp_dispatch_bv_sort():
    # fpToFP(bv, fpsort) is the IEEE reinterpretation.
    (ra, rb), (va, vb) = _model_of(
        lambda: z.fpToFP(z.BitVecVal(0x3fc00000, 32), z.Float32()),
        lambda: _z3.fpToFP(_z3.BitVecVal(0x3fc00000, 32), _z3.Float32()),
        "fpc_disp_bv", _fp32, _zfp32)
    assert ra == rb == "sat" and va == vb


@requires_z3
@pytest.mark.parametrize("mname", ["RNE", "RNA", "RTP", "RTN", "RTZ"])
@pytest.mark.parametrize("rat", ["1/3", "-7/2", "0", "1000000"])
def test_fpc_real_to_fp(mname, rat):
    (ra, rb), (va, vb) = _model_of(
        lambda: z.fpRealToFP(getattr(z, mname)(), z.RealVal(rat), z.Float32()),
        lambda: _z3.fpRealToFP(getattr(_z3, mname)(), _z3.RealVal(rat), _z3.Float32()),
        f"fpc_r2f_{mname}_{rat.replace('/', 'd').replace('-', 'm')}",
        _fp32, _zfp32)
    assert ra == rb == "sat"
    assert va == vb


@requires_z3
@pytest.mark.parametrize("uval", [0, 1, 7, 200, 255])
def test_fpc_unsigned_to_fp(uval):
    (ra, rb), (va, vb) = _model_of(
        lambda: z.fpUnsignedToFP(z.RNE(), z.BitVecVal(uval, 8), z.Float32()),
        lambda: _z3.fpUnsignedToFP(_z3.RNE(), _z3.BitVecVal(uval, 8), _z3.Float32()),
        f"fpc_u2f_{uval}", _fp32, _zfp32)
    assert ra == rb == "sat" and va == vb


def _bv8(name):
    return z.BitVec(name, 8)


def _zbv8(name):
    return _z3.BitVec(name, 8)


@requires_z3
@pytest.mark.parametrize("mname", ["RNE", "RNA", "RTP", "RTN", "RTZ"])
@pytest.mark.parametrize("v", [1.5, 3.7, -3.7, 2.5, -2.5, 0.0])
def test_fpc_to_sbv_all_modes(mname, v):
    key = f"fpc_sbv_{mname}_{str(v).replace('.', '_').replace('-', 'm')}"
    (ra, rb), (va, vb) = _model_of(
        lambda: z.fpToSBV(getattr(z, mname)(), z.FPVal(v, z.Float32()),
                          z.BitVecSort(8)),
        lambda: _z3.fpToSBV(getattr(_z3, mname)(), _z3.FPVal(v, _z3.Float32()),
                            _z3.BitVecSort(8)),
        key, _bv8, _zbv8)
    # AY decides fp.to_sbv under ALL five rounding modes (exact rational
    # rounding in the model evaluator + all-mode bit-blast circuits); the
    # value must match z3py exactly.
    assert ra == rb == "sat"
    assert va == vb


@requires_z3
@pytest.mark.parametrize("mname", ["RNE", "RNA", "RTP", "RTN", "RTZ"])
@pytest.mark.parametrize("v", [1.5, 3.7, 2.5, 200.0, 0.25])
def test_fpc_to_ubv_all_modes(mname, v):
    key = f"fpc_ubv_{mname}_{str(v).replace('.', '_')}"
    (ra, rb), (va, vb) = _model_of(
        lambda: z.fpToUBV(getattr(z, mname)(), z.FPVal(v, z.Float32()),
                          z.BitVecSort(8)),
        lambda: _z3.fpToUBV(getattr(_z3, mname)(), _z3.FPVal(v, _z3.Float32()),
                            _z3.BitVecSort(8)),
        key, _bv8, _zbv8)
    # Same contract as to_sbv: AY decides fp.to_ubv under ALL five rounding
    # modes; the value must match z3py exactly.
    assert ra == rb == "sat"
    assert va == vb


@requires_z3
@pytest.mark.parametrize("v", [1.5, -3.75, 0.1, 1e-42, 100.0])
def test_fpc_to_real(v):
    key = f"fpc_2real_{str(v).replace('.', '_').replace('-', 'm')}"
    (ra, rb), (va, vb) = _model_of(
        lambda: z.fpToReal(z.FPVal(v, z.Float32())),
        lambda: _z3.fpToReal(_z3.FPVal(v, _z3.Float32())),
        key, lambda n: z.Real(n), lambda n: _z3.Real(n))
    assert ra == rb == "sat"
    assert va == vb


@requires_z3
@pytest.mark.parametrize("v", [1.5, -2.5, 0.0, -0.0, 1e-42])
def test_fpc_to_ieee_bv(v):
    key = f"fpc_ieee_{str(v).replace('.', '_').replace('-', 'm')}"
    (ra, rb), (va, vb) = _model_of(
        lambda: z.fpToIEEEBV(z.FPVal(v, z.Float32())),
        lambda: _z3.fpToIEEEBV(_z3.FPVal(v, _z3.Float32())),
        key, lambda n: z.BitVec(n, 32), lambda n: _z3.BitVec(n, 32))
    assert ra == rb == "sat"
    assert va == vb


@requires_z3
@pytest.mark.parametrize("sgn,e,m", [(0, 127, 0), (1, 128, 1 << 22),
                                     (0, 0, 1), (1, 255, 0), (0, 254, (1 << 23) - 1)])
def test_fpc_fp_from_fields(sgn, e, m):
    key = f"fpc_fpfp_{sgn}_{e}_{m}"
    (ra, rb), (va, vb) = _model_of(
        lambda: z.fpFP(z.BitVecVal(sgn, 1), z.BitVecVal(e, 8), z.BitVecVal(m, 23)),
        lambda: _z3.fpFP(_z3.BitVecVal(sgn, 1), _z3.BitVecVal(e, 8),
                         _z3.BitVecVal(m, 23)),
        key, _fp32, _zfp32)
    assert ra == rb == "sat"
    assert va == vb


@requires_z3
def test_fpc_fp_sort_inference_and_arg_checks():
    f = z.fpFP(z.BitVecVal(0, 1), z.BitVecVal(1023, 11), z.BitVecVal(0, 52))
    g = _z3.fpFP(_z3.BitVecVal(0, 1), _z3.BitVecVal(1023, 11), _z3.BitVecVal(0, 52))
    assert repr(f.sort()) == repr(g.sort())
    with pytest.raises(z.AyZ3Exception):
        z.fpFP(z.BitVecVal(0, 2), z.BitVecVal(0, 8), z.BitVecVal(0, 23))


@requires_z3
def test_fpc_to_sbv_roundtrip_signed():
    # signed BV -> FP -> signed BV is the identity for in-range integers.
    for n in [-5, 0, 7, 100, -128]:
        key = f"fpc_rt_{str(n).replace('-', 'm')}"
        (ra, rb), (va, vb) = _model_of(
            lambda n=n: z.fpToSBV(z.RTZ(),
                                  z.fpSignedToFP(z.RNE(), z.BitVecVal(n, 8),
                                                 z.Float32()),
                                  z.BitVecSort(8)),
            lambda n=n: _z3.fpToSBV(_z3.RTZ(),
                                    _z3.fpSignedToFP(_z3.RNE(),
                                                     _z3.BitVecVal(n, 8),
                                                     _z3.Float32()),
                                    _z3.BitVecSort(8)),
            key, _bv8, _zbv8)
        # Round-trip uses RTZ, which AY's fp.to_sbv now decides
        # (all five rounding modes; see the all-modes contract above).
        assert ra == rb == "sat"
        assert va == vb


@requires_z3
def test_fpc_numref_accessors_native_vs_parsed_reference():
    # The native Z3_fpa_get_numeral_* accessor path must be BYTE-IDENTICAL to
    # the textual reference parser across the value classes + subnormals.
    from ayz3.fp import _fp_ref_fields
    vals = [1.5, -2.5, 0.0, -0.0, float("inf"), float("-inf"), float("nan"),
            1e-42, -1e-42, 1e38, 6.5e-4]
    for v in vals:
        a = z.FPVal(v, z.Float32())
        assert a._fields() == _fp_ref_fields(a), f"field mismatch for {v}"
        b = _z3.FPVal(v, _z3.Float32())
        assert repr(a) == repr(b)
        if v == v:  # skip z3py NaN accessor quirks
            assert a.isNaN() == b.isNaN()
            assert a.isInf() == b.isInf()
            assert a.isZero() == b.isZero()
            assert a.isSubnormal() == b.isSubnormal()
            assert a.isNormal() == b.isNormal()
            assert a.isNegative() == b.isNegative()
            assert a.isPositive() == b.isPositive()
        if v == v and abs(v) != float("inf") and v != 0.0:
            assert a.sign() == b.sign()
            assert a.exponent() == b.exponent()
            assert a.exponent_as_long(False) == b.exponent_as_long(False)
            assert a.significand() == b.significand()
            assert a.significand_as_long() == b.significand_as_long()


@requires_z3
def test_fpc_float128_fpval_exact_fields():
    # Float128 numerals land through Z3_mk_fpa_fp with exact fields; the
    # accessors fall back to the textual reference parser (>64-bit mantissa).
    for s in ["1.5", "-2.5", "1/3", "100"]:
        a = z.FPVal(s, z.Float128())
        b = _z3.FPVal(s, _z3.Float128())
        assert a.sign() == b.sign()
        assert a.exponent() == b.exponent()
        # z3py's significand_as_long() itself errors for >64-bit mantissas
        # (Z3_fpa_get_numeral_significand_uint64 limit), so compare the exact
        # decimal significand strings instead.
        assert a.significand() == b.significand()
        assert repr(a) == repr(b)


@requires_z3
def test_fpc_model_value_accessors_match_z3py():
    # FPNumRef accessors on MODEL values (the `(fp #b..)` shape) must go
    # through the native numeral accessors and agree with z3py.
    sa, sb = z.Solver(), _z3.Solver()
    xa, xb = _fp32("fpc_mv_x"), _zfp32("fpc_mv_x")
    sa.add(z.fpToIEEEBV(xa) == z.BitVecVal(0x40490fdb, 32))
    sb.add(_z3.fpToIEEEBV(xb) == _z3.BitVecVal(0x40490fdb, 32))
    assert str(sa.check()) == str(sb.check()) == "sat"
    va, vb = sa.model()[xa], sb.model()[xb]
    assert repr(va) == repr(vb)
    assert va.sign() == vb.sign()
    assert va.exponent() == vb.exponent()
    assert va.exponent_as_long(False) == vb.exponent_as_long(False)
    assert va.significand() == vb.significand()
    assert va.significand_as_long() == vb.significand_as_long()

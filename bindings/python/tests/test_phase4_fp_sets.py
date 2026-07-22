# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
#
# Phase-4 floating-point and finite-set tests for ayz3, cross-checked against
# real z3py 4.15.4 where available.
#
# FP is NATIVE: libay_ffi exports the Z3_mk_fpa_* term-constructor surface, so
# FP constraints are ordinary BoolRefs solved by the regular Solver, and model
# values come back as FPNumRef through the regular ModelRef — matching z3py.
# The conversions whose C fn is absent from the dylib (to_fp from IEEE bits,
# Real<->FP, FP->BV) raise NotImplementedError naming the missing export.
#
# NOTE on const names: ayz3 interns consts by NAME process-wide (shared main
# context), so FP consts here use the file-unique `fpp_` prefix.
#
# Run:  cargo build -p ay-ffi  &&  pytest bindings/python/tests/test_phase4_fp_sets.py -v

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

requires_z3 = pytest.mark.skipif(not HAVE_Z3PY, reason="z3py 4.15.4 not installed")


def _f32(x):
    """The float32 rounding of Python float x."""
    return struct.unpack("<f", struct.pack("<f", x))[0]


def _z3_f32(x):
    """A z3py Float32 value equal to the float32 rounding of Python float x."""
    b = struct.unpack("<I", struct.pack("<f", x))[0]
    return _z3.fpFP(
        _z3.BitVecVal((b >> 31) & 1, 1),
        _z3.BitVecVal((b >> 23) & 0xFF, 8),
        _z3.BitVecVal(b & 0x7FFFFF, 23),
    )


def _z3_check(build):
    s = _z3.Solver()
    s.add(build())
    return str(s.check())


def _check(constraint):
    s = z.Solver()
    s.add(constraint)
    return s.check()


# ===========================================================================
# FP: sorts / values / surface
# ===========================================================================


def test_fpsort_constructors():
    assert z.Float16().ebits() == 5 and z.Float16().sbits() == 11
    assert z.Float32().ebits() == 8 and z.Float32().sbits() == 24
    assert z.Float64().ebits() == 11 and z.Float64().sbits() == 53
    assert z.Float128().ebits() == 15 and z.Float128().sbits() == 113
    assert z.FPSort(8, 24) == z.Float32()
    assert z.FPSort(8, 24) != z.Float64()


def test_fpval_fields_float32():
    # FPVal must land the exact IEEE-754 single fields.
    v = z.FPVal(-2.5, z.Float32())
    assert z.is_fp_value(v)
    assert v.sign() is True
    assert v.exponent_as_long() == 128        # biased
    assert v.exponent_as_long(False) == 1     # unbiased
    assert v.significand_as_long() == 0x200000
    assert repr(v) == "-1.25*(2**1)"


def test_fpval_special_values():
    f = z.Float32()
    assert repr(z.FPVal("nan", f)) == "NaN"
    assert repr(z.FPVal("+oo", f)) == "+oo"
    assert repr(z.FPVal("-oo", f)) == "-oo"
    assert repr(z.FPVal(float("inf"), f)) == "+oo"
    assert repr(z.FPVal(float("-inf"), f)) == "-oo"
    assert repr(z.FPVal(float("nan"), f)) == "NaN"
    assert repr(z.FPVal(-0.0, f)) == "-0.0"
    assert repr(z.FPVal(0.0, f)) == "+0.0"


# ===========================================================================
# FP: arithmetic (sat/unsat + determinate model), cross-checked vs z3py
# ===========================================================================


def test_fp_add_solves_for_x():
    # x + 1.0 == 2.0 is sat; the witness must itself satisfy the equation.
    s = z.Solver()
    x = z.FP("fpp_x", z.Float32())
    one, two = z.FPVal(1.0, z.Float32()), z.FPVal(2.0, z.Float32())
    s.add(z.fpEQ(z.fpAdd(z.RNE(), x, one), two))
    assert s.check() == z.sat
    xv = float(s.model()[x])
    assert _f32(xv + 1.0) == 2.0


@requires_z3
def test_fp_arith_matches_z3py_determinate():
    facts = [
        (lambda: z.fpEQ(z.fpAdd(z.RNE(), z.FPVal(1.0, z.Float32()), z.FPVal(1.0, z.Float32())), z.FPVal(2.0, z.Float32())),
         lambda: _z3.fpEQ(_z3.fpAdd(_z3.RNE(), _z3_f32(1.0), _z3_f32(1.0)), _z3_f32(2.0))),
        (lambda: z.fpEQ(z.fpAdd(z.RNE(), z.FPVal(1.0, z.Float32()), z.FPVal(1.0, z.Float32())), z.FPVal(3.0, z.Float32())),
         lambda: _z3.fpEQ(_z3.fpAdd(_z3.RNE(), _z3_f32(1.0), _z3_f32(1.0)), _z3_f32(3.0))),
        (lambda: z.fpEQ(z.fpSub(z.RNE(), z.FPVal(3.0, z.Float32()), z.FPVal(1.0, z.Float32())), z.FPVal(2.0, z.Float32())),
         lambda: _z3.fpEQ(_z3.fpSub(_z3.RNE(), _z3_f32(3.0), _z3_f32(1.0)), _z3_f32(2.0))),
        (lambda: z.fpEQ(z.fpMul(z.RNE(), z.FPVal(2.0, z.Float32()), z.FPVal(3.0, z.Float32())), z.FPVal(6.0, z.Float32())),
         lambda: _z3.fpEQ(_z3.fpMul(_z3.RNE(), _z3_f32(2.0), _z3_f32(3.0)), _z3_f32(6.0))),
        (lambda: z.fpEQ(z.fpDiv(z.RNE(), z.FPVal(6.0, z.Float32()), z.FPVal(2.0, z.Float32())), z.FPVal(3.0, z.Float32())),
         lambda: _z3.fpEQ(_z3.fpDiv(_z3.RNE(), _z3_f32(6.0), _z3_f32(2.0)), _z3_f32(3.0))),
        # 0.1+0.2==0.3 is TRUE in float32 (the famous inequality is float64).
        (lambda: z.fpEQ(z.fpAdd(z.RNE(), z.FPVal(0.1, z.Float32()), z.FPVal(0.2, z.Float32())), z.FPVal(0.3, z.Float32())),
         lambda: _z3.fpEQ(_z3.fpAdd(_z3.RNE(), _z3_f32(0.1), _z3_f32(0.2)), _z3_f32(0.3))),
    ]
    for ay_build, z3_build in facts:
        assert str(_check(ay_build())) == _z3_check(z3_build)


def test_fp_unsat_arith():
    assert _check(
        z.fpEQ(z.fpMul(z.RNE(), z.FPVal(2.0, z.Float32()), z.FPVal(3.0, z.Float32())),
               z.FPVal(7.0, z.Float32()))
    ) == z.unsat


def test_fp_operator_overloads():
    x = z.FP("fpp_op_x", z.Float32())
    s = z.Solver()
    s.add(z.fpEQ(x + z.FPVal(1.0, z.Float32()), z.FPVal(2.0, z.Float32())))
    assert s.check() == z.sat


# ===========================================================================
# FP: sqrt / fma / rem / min / max / roundToIntegral (now natively backed)
# ===========================================================================


def test_fp_sqrt():
    f = z.Float32()
    assert _check(z.fpEQ(z.fpSqrt(z.RNE(), z.FPVal(4.0, f)), z.FPVal(2.0, f))) == z.sat
    assert _check(z.fpEQ(z.fpSqrt(z.RNE(), z.FPVal(2.0, f)),
                         z.FPVal(_f32(math.sqrt(2.0)), f))) == z.sat
    assert _check(z.fpEQ(z.fpSqrt(z.RNE(), z.FPVal(4.0, f)), z.FPVal(3.0, f))) == z.unsat


def test_fp_fma_rem_min_max_rti():
    f = z.Float32()
    assert _check(z.fpEQ(z.fpFMA(z.RNE(), z.FPVal(2.0, f), z.FPVal(3.0, f), z.FPVal(1.0, f)),
                         z.FPVal(7.0, f))) == z.sat
    assert _check(z.fpEQ(z.fpRem(z.FPVal(5.0, f), z.FPVal(3.0, f)),
                         z.FPVal(-1.0, f))) == z.sat
    assert _check(z.fpEQ(z.fpMin(z.FPVal(2.0, f), z.FPVal(3.0, f)), z.FPVal(2.0, f))) == z.sat
    assert _check(z.fpEQ(z.fpMax(z.FPVal(2.0, f), z.FPVal(3.0, f)), z.FPVal(3.0, f))) == z.sat
    assert _check(z.fpEQ(z.fpRoundToIntegral(z.RTZ(), z.FPVal(2.7, f)), z.FPVal(2.0, f))) == z.sat
    assert _check(z.fpEQ(z.fpRoundToIntegral(z.RTP(), z.FPVal(2.2, f)), z.FPVal(3.0, f))) == z.sat


# ===========================================================================
# FP: NaN / Inf / signed-zero edge cases, cross-checked vs z3py
# ===========================================================================


def test_fp_nan_not_equal_itself():
    f = z.Float32()
    # IEEE fp.eq: NaN == NaN is false.
    assert _check(z.fpEQ(z.fpNaN(f), z.fpNaN(f))) == z.unsat
    # SMT `=` (object equality): NaN = NaN is true — matching z3py's ==.
    assert _check(z.fpNaN(f) == z.fpNaN(f)) == z.sat
    if HAVE_Z3PY:
        assert _z3_check(lambda: _z3.fpEQ(_z3.fpNaN(_z3.Float32()), _z3.fpNaN(_z3.Float32()))) == "unsat"
        assert _z3_check(lambda: _z3.fpNaN(_z3.Float32()) == _z3.fpNaN(_z3.Float32())) == "sat"


def test_fp_isnan():
    assert _check(z.fpIsNaN(z.fpNaN(z.Float32()))) == z.sat
    assert _check(z.fpIsNaN(z.FPVal(1.0, z.Float32()))) == z.unsat
    if HAVE_Z3PY:
        assert _z3_check(lambda: _z3.fpIsNaN(_z3.fpNaN(_z3.Float32()))) == "sat"
        assert _z3_check(lambda: _z3.fpIsNaN(_z3_f32(1.0))) == "unsat"


def test_fp_nan_ordering_unsat():
    f = z.Float32()
    assert _check(z.fpLT(z.fpNaN(f), z.FPVal(1.0, f))) == z.unsat
    x = z.FP("fpp_nan_x", f)
    assert _check(z.fpGT(z.fpNaN(f), x)) == z.unsat


def test_fp_infinity():
    f = z.Float32()
    assert _check(z.fpIsInf(z.fpPlusInfinity(f))) == z.sat
    assert _check(z.fpLT(z.FPVal(1.0, f), z.fpPlusInfinity(f))) == z.sat
    assert _check(z.fpEQ(z.fpAdd(z.RNE(), z.fpPlusInfinity(f), z.FPVal(1.0, f)),
                         z.fpPlusInfinity(f))) == z.sat
    if HAVE_Z3PY:
        assert _z3_check(lambda: _z3.fpIsInf(_z3.fpPlusInfinity(_z3.Float32()))) == "sat"
        assert _z3_check(lambda: _z3.fpLT(_z3_f32(1.0), _z3.fpPlusInfinity(_z3.Float32()))) == "sat"


def test_fp_signed_zero():
    f = z.Float32()
    # IEEE fp.eq: +0 == -0 true; SMT `=`: false (different bit patterns).
    assert _check(z.fpEQ(z.fpPlusZero(f), z.fpMinusZero(f))) == z.sat
    assert _check(z.fpPlusZero(f) == z.fpMinusZero(f)) == z.unsat
    assert _check(z.fpIsZero(z.fpMinusZero(f))) == z.sat
    if HAVE_Z3PY:
        assert _z3_check(lambda: _z3.fpEQ(_z3.fpPlusZero(_z3.Float32()), _z3.fpMinusZero(_z3.Float32()))) == "sat"
        assert _z3_check(lambda: _z3.fpPlusZero(_z3.Float32()) == _z3.fpMinusZero(_z3.Float32())) == "unsat"


@requires_z3
def test_fp_ordering_matches_z3py():
    f = z.Float32()
    cases = [
        (lambda: z.fpLT(z.FPVal(1.0, f), z.FPVal(2.0, f)),
         lambda: _z3.fpLT(_z3_f32(1.0), _z3_f32(2.0))),
        (lambda: z.fpLEQ(z.FPVal(2.0, f), z.FPVal(2.0, f)),
         lambda: _z3.fpLEQ(_z3_f32(2.0), _z3_f32(2.0))),
        (lambda: z.fpGT(z.FPVal(3.0, f), z.FPVal(2.0, f)),
         lambda: _z3.fpGT(_z3_f32(3.0), _z3_f32(2.0))),
        (lambda: z.fpGEQ(z.FPVal(2.0, f), z.FPVal(3.0, f)),
         lambda: _z3.fpGEQ(_z3_f32(2.0), _z3_f32(3.0))),
        (lambda: z.fpLT(z.FPVal(-1.5, f), z.FPVal(0.5, f)),
         lambda: _z3.fpLT(_z3_f32(-1.5), _z3_f32(0.5))),
    ]
    for ay_build, z3_build in cases:
        assert str(_check(ay_build())) == _z3_check(z3_build)


# ===========================================================================
# FP: model readout (determinate values) via the regular ModelRef
# ===========================================================================


@pytest.mark.parametrize("val", [2.5, 1.0, -3.0, 0.5, 100.0, 0.0, -0.0])
def test_fp_model_readout_float32(val):
    s = z.Solver()
    x = z.FP(f"fpp_ro_{repr(val).replace('-', 'm').replace('.', '_')}", z.Float32())
    s.add(x == z.FPVal(val, z.Float32()))
    assert s.check() == z.sat
    got = float(s.model()[x])
    expect = _f32(val)
    assert got == expect and math.copysign(1.0, got) == math.copysign(1.0, expect)


@requires_z3
@pytest.mark.parametrize("v", [1.5, 0.1, 100.0, -2.75, 0.333])
def test_fpval_float16_bits_match_z3py(v):
    # The exact-bignum RNE encoder must round identically to z3.
    ay = z.FPVal(v, z.Float16())
    ay_bits = ((1 if ay.sign() else 0) << 15) | (ay.exponent_as_long() << 10) | ay.significand_as_long()
    fp16 = _z3.FPSort(5, 11)
    zfp = _z3.fpToFP(_z3.RNE(), _z3.RealVal(v), fp16)
    sv = _z3.Solver()
    bv = _z3.Const("b", _z3.BitVecSort(16))
    sv.add(bv == _z3.fpToIEEEBV(zfp))
    assert str(sv.check()) == "sat"
    assert ay_bits == sv.model()[bv].as_long()


def test_fp_model_readout_float16():
    s = z.Solver()
    h = z.FP("fpp_h16", z.Float16())
    s.add(h == z.FPVal(1.5, z.Float16()))
    assert s.check() == z.sat
    assert float(s.model()[h]) == 1.5


def test_fp_model_readout_float64():
    s = z.Solver()
    d = z.FP("fpp_d64", z.Float64())
    s.add(d == z.FPVal(3.141592653589793, z.Float64()))
    assert s.check() == z.sat
    assert float(s.model()[d]) == 3.141592653589793


def test_fp_model_readout_special():
    s = z.Solver()
    x = z.FP("fpp_inf_x", z.Float32())
    s.add(x == z.fpPlusInfinity(z.Float32()))
    assert s.check() == z.sat
    v = s.model()[x]
    assert v.isInf() and float(v) == float("inf")


def test_fp_constrained_unique_witness():
    # x*x == 4.0 and 0 < x < 3  =>  x == 2.0 (the only float32 witness here).
    f = z.Float32()
    s = z.Solver()
    x = z.FP("fpp_sq_x", f)
    s.add(z.fpEQ(z.fpMul(z.RNE(), x, x), z.FPVal(4.0, f)))
    s.add(z.fpGT(x, z.FPVal(0.0, f)))
    s.add(z.fpLT(x, z.FPVal(3.0, f)))
    assert s.check() == z.sat
    assert float(s.model()[x]) == 2.0


def test_fp_compound_and_or():
    f = z.Float32()
    x = z.FP("fpp_band_x", f)
    s = z.Solver()
    s.add(z.And(z.fpGT(x, z.FPVal(1.0, f)), z.fpLT(x, z.FPVal(2.0, f))))
    assert s.check() == z.sat
    v = float(s.model()[x])
    assert 1.0 < v < 2.0


def test_fp_unsat_compound():
    f = z.Float32()
    x = z.FP("fpp_uc_x", f)
    s = z.Solver()
    s.add(z.fpGT(x, z.FPVal(2.0, f)))
    s.add(z.fpLT(x, z.FPVal(1.0, f)))
    assert s.check() == z.unsat


# ===========================================================================
# FP: conversions — backed vs honestly-absent
# ===========================================================================


def test_fp_to_fp_backed_shapes():
    f32, f64 = z.Float32(), z.Float64()
    # FP -> FP narrowing.
    x = z.FP("fpp_conv_x", f32)
    assert _check(x == z.fpToFP(z.RNE(), z.FPVal(0.1, f64), f32)) == z.sat
    # signed BV -> FP.
    assert _check(z.fpEQ(z.fpToFP(z.RNE(), z.BitVecVal(-5, 8), f32),
                         z.FPVal(-5.0, f32))) == z.sat
    assert _check(z.fpEQ(z.fpSignedToFP(z.RNE(), z.BitVecVal(7, 8), f32),
                         z.FPVal(7.0, f32))) == z.sat


def test_fp_conversions_now_native():
    # FIXED-BUG PIN (flipped): these conversions used to raise the honest
    # NotImplementedError while the Z3_mk_fpa_to_* C fns were absent from
    # libay_ffi; the FPA completion exports them all, so each must build a
    # real term of the right sort.
    f = z.Float32()
    x = z.FP("fpp_abs_x", f)
    assert repr(z.fpToFP(z.BitVecVal(0x3FC00000, 32), f).sort()) == repr(f)
    assert z.fpToIEEEBV(x).sort().size() == 32
    assert z.fpToSBV(z.RNE(), x, z.BitVecSort(32)).sort().size() == 32
    assert z.fpToUBV(z.RNE(), x, z.BitVecSort(32)).sort().size() == 32
    assert z.fpToReal(x).sort().kind == "Real"
    assert repr(z.fpRealToFP(z.RNE(), z.RealVal("1/3"), f).sort()) == repr(f)
    assert repr(z.fpUnsignedToFP(z.RNE(), z.BitVecVal(5, 8), f).sort()) == repr(f)


def test_fp_bad_operand_raises():
    with pytest.raises(z.AyZ3Exception):
        z.fpAdd(z.RNE(), "not-an-fp", z.FPVal(1.0, z.Float32()))


# ===========================================================================
# Sets (sets-as-arrays) — cross-checked vs z3py
# ===========================================================================


def fresh_solver():
    return z.Solver(z.Context())


def test_set_membership_sat():
    s = fresh_solver()
    with s.using():
        I = z.IntSort()
        s1 = z.SetAdd(z.EmptySet(I), 1)
        s.add(z.And(z.IsMember(1, s1), z.Not(z.IsMember(2, s1))))
    assert s.check() == z.sat


def test_set_membership_unsat():
    s = fresh_solver()
    with s.using():
        I = z.IntSort()
        s1 = z.SetAdd(z.EmptySet(I), 1)
        s.add(z.IsMember(2, s1))  # 2 in {1} is false
    assert s.check() == z.unsat


def test_emptyset_no_members():
    s = fresh_solver()
    with s.using():
        I = z.IntSort()
        x = z.Int("x")
        s.add(z.IsMember(x, z.EmptySet(I)))  # nothing is in the empty set
    assert s.check() == z.unsat


def test_fullset_all_members():
    s = fresh_solver()
    with s.using():
        I = z.IntSort()
        x = z.Int("x")
        s.add(z.Not(z.IsMember(x, z.FullSet(I))))  # everything is in the full set
    assert s.check() == z.unsat


def test_set_del():
    s = fresh_solver()
    with s.using():
        I = z.IntSort()
        s12 = z.SetAdd(z.SetAdd(z.EmptySet(I), 1), 2)
        s2 = z.SetDel(s12, 1)
        s.add(z.And(z.Not(z.IsMember(1, s2)), z.IsMember(2, s2)))
    assert s.check() == z.sat


def test_set_union_membership():
    # 1 in ({1} u {2}) sat; 3 in ({1} u {2}) unsat.
    s = fresh_solver()
    with s.using():
        I = z.IntSort()
        a = z.SetAdd(z.EmptySet(I), 1)
        b = z.SetAdd(z.EmptySet(I), 2)
        u = z.SetUnion(a, b)
        s.add(z.IsMember(1, u))
    assert s.check() == z.sat

    s2 = fresh_solver()
    with s2.using():
        I = z.IntSort()
        a = z.SetAdd(z.EmptySet(I), 1)
        b = z.SetAdd(z.EmptySet(I), 2)
        u = z.SetUnion(a, b)
        s2.add(z.IsMember(3, u))
    assert s2.check() == z.unsat


def test_set_intersect_membership():
    # 1 in ({1} n {2}) unsat; 1 in ({1,2} n {1,3}) sat.
    s = fresh_solver()
    with s.using():
        I = z.IntSort()
        a = z.SetAdd(z.EmptySet(I), 1)
        b = z.SetAdd(z.EmptySet(I), 2)
        s.add(z.IsMember(1, z.SetIntersect(a, b)))
    assert s.check() == z.unsat

    s2 = fresh_solver()
    with s2.using():
        I = z.IntSort()
        a = z.SetAdd(z.SetAdd(z.EmptySet(I), 1), 2)
        b = z.SetAdd(z.SetAdd(z.EmptySet(I), 1), 3)
        s2.add(z.IsMember(1, z.SetIntersect(a, b)))
    assert s2.check() == z.sat


def test_set_difference_membership():
    # 1 in ({1,2} \ {2}) sat; 2 in ({1,2} \ {2}) unsat.
    s = fresh_solver()
    with s.using():
        I = z.IntSort()
        a = z.SetAdd(z.SetAdd(z.EmptySet(I), 1), 2)
        b = z.SetAdd(z.EmptySet(I), 2)
        s.add(z.IsMember(1, z.SetDifference(a, b)))
    assert s.check() == z.sat

    s2 = fresh_solver()
    with s2.using():
        I = z.IntSort()
        a = z.SetAdd(z.SetAdd(z.EmptySet(I), 1), 2)
        b = z.SetAdd(z.EmptySet(I), 2)
        s2.add(z.IsMember(2, z.SetDifference(a, b)))
    assert s2.check() == z.unsat


def test_set_complement_membership():
    # 1 in complement({2}) sat; 2 in complement({2}) unsat.
    s = fresh_solver()
    with s.using():
        I = z.IntSort()
        b = z.SetAdd(z.EmptySet(I), 2)
        s.add(z.IsMember(1, z.SetComplement(b)))
    assert s.check() == z.sat

    s2 = fresh_solver()
    with s2.using():
        I = z.IntSort()
        b = z.SetAdd(z.EmptySet(I), 2)
        s2.add(z.IsMember(2, z.SetComplement(b)))
    assert s2.check() == z.unsat


@requires_z3
def test_set_membership_matches_z3py():
    # Cross-check membership facts against z3py's native set ops.
    def ay():
        I = z.IntSort()
        a = z.SetAdd(z.EmptySet(I), 1)
        b = z.SetAdd(z.EmptySet(I), 2)
        return z.IsMember(1, z.SetUnion(a, b))

    def z3b():
        I = _z3.IntSort()
        a = _z3.SetAdd(_z3.EmptySet(I), 1)
        b = _z3.SetAdd(_z3.EmptySet(I), 2)
        return _z3.IsMember(1, _z3.SetUnion(a, b))

    s = fresh_solver()
    with s.using():
        s.add(ay())
    assert str(s.check()) == _z3_check(z3b)


def test_set_symbolic_membership():
    # A symbolic set const: assert 5 is a member, then it must be.
    s = fresh_solver()
    with s.using():
        I = z.IntSort()
        a = z.Const("a", z.SetSort(I))
        s.add(z.IsMember(5, a))
        s.add(z.Not(z.IsMember(5, a)))  # contradiction
    assert s.check() == z.unsat


def test_is_subset_deferred():
    with pytest.raises(NotImplementedError):
        I = z.IntSort()
        z.IsSubset(z.EmptySet(I), z.FullSet(I))


def test_quantified_array_solver_path_fails_closed():
    s = fresh_solver()
    with s.using():
        i = z.Int("i")
        a = z.Array("a", z.IntSort(), z.IntSort())
        s.add(z.ForAll([i], z.Select(a, i) == 0))
    assert s.check() == z.unknown
    assert "quantified array" in s.reason_unknown()

# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
#
# B-11: string code-point / character-theory / sequence-sort constructor surface.
#
# Exercises the z3py-shaped names newly added to ayz3 whose underlying AY ops
# solve soundly:
#   SeqSort, StrToCode, StrFromCode, CharVal, CharToInt, CharToBv, CharIsDigit.
#
# SOUNDNESS CONTRACT (the point of this suite): every verdict ayz3 DECIDES
# (sat/unsat) must equal z3py's; a sound `unknown` is accepted, but a WRONG
# sat/unsat is a hard failure. Each op also carries a wrong-fact probe that MUST
# be unsat, so a mis-built term cannot pass as sat.
#
# (z3py's `LastIndexOf` is intentionally absent: AY leaves `seq.last_indexof`
# unconstrained on ground inputs, so exposing it would give wrong verdicts.)

import pytest

import ayz3 as z

try:
    import z3 as _z3
    HAVE_Z3PY = True
except Exception:  # pragma: no cover - depends on environment
    _z3 = None
    HAVE_Z3PY = False

requires_z3py = pytest.mark.usefixtures("required_reference_z3")


def fresh_solver():
    """A Solver with its own isolated Context (own assertion stack)."""
    return z.Solver(z.Context())


def _ay_verdict(build):
    s = fresh_solver()
    with s.using():
        s.add(build(z))
    return str(s.check())


def _z3_verdict(build):
    s = _z3.Solver()
    s.add(build(_z3))
    return str(s.check())


def _assert_parity(build, expect):
    """ayz3 must equal `expect` (and z3py); a sound `unknown` is accepted."""
    ay = _ay_verdict(build)
    assert ay in (expect, "unknown"), (
        f"verdict mismatch: want={expect} ayz3={ay} (a wrong sat/unsat is disqualifying)"
    )
    if HAVE_Z3PY:
        zz = _z3_verdict(build)
        assert zz == expect, f"z3py oracle drift: want={expect} z3py={zz}"
        assert ay in (zz, "unknown"), f"ayz3={ay} disagrees with z3py={zz}"


# ---------------------------------------------------------------------------
# SeqSort  ((Seq elem))
# ---------------------------------------------------------------------------

def test_seqsort_observable_shape():
    s = z.SeqSort(z.IntSort())
    assert repr(s) == "Seq(Int)"
    assert s.sexpr() == "(Seq Int)"
    assert s.name() == "Seq"
    assert s.basis() == z.IntSort() or s.basis().kind == "Int"


@requires_z3py
def test_seqsort_matches_z3py_observable():
    a = z.SeqSort(z.IntSort())
    b = _z3.SeqSort(_z3.IntSort())
    assert repr(a) == repr(b)
    assert a.sexpr() == b.sexpr()
    assert a.name() == b.name()


def test_seqsort_equality_sat():
    def build(m):
        a = m.Const("a", m.SeqSort(m.IntSort()))
        b = m.Const("b", m.SeqSort(m.IntSort()))
        return a == b
    _assert_parity(build, "sat")


def test_seqsort_self_disequality_unsat_SOUNDNESS():
    def build(m):
        a = m.Const("a", m.SeqSort(m.IntSort()))
        return a != a
    _assert_parity(build, "unsat")


# ---------------------------------------------------------------------------
# StrToCode  (str.to_code : length-1 String -> Int)
# ---------------------------------------------------------------------------

@requires_z3py
def test_strtocode_sexpr_matches_z3py():
    assert (z.StrToCode(z.StringVal("A")).sexpr()
            == _z3.StrToCode(_z3.StringVal("A")).sexpr())


def test_strtocode_true_fact_sat():
    _assert_parity(lambda m: m.StrToCode(m.StringVal("A")) == 65, "sat")


def test_strtocode_wrong_fact_unsat_SOUNDNESS():
    _assert_parity(lambda m: m.StrToCode(m.StringVal("A")) == 66, "unsat")


# ---------------------------------------------------------------------------
# StrFromCode  (str.from_code : Int -> length-1 String)
# ---------------------------------------------------------------------------

@requires_z3py
def test_strfromcode_sexpr_matches_z3py():
    assert (z.StrFromCode(z.IntVal(65)).sexpr()
            == _z3.StrFromCode(_z3.IntVal(65)).sexpr())


def test_strfromcode_true_fact_sat():
    _assert_parity(
        lambda m: m.StrFromCode(m.IntVal(65)) == m.StringVal("A"), "sat")


def test_strfromcode_wrong_fact_unsat_SOUNDNESS():
    _assert_parity(
        lambda m: m.StrFromCode(m.IntVal(65)) == m.StringVal("B"), "unsat")


# ---------------------------------------------------------------------------
# CharToInt  (char.to_int)
# ---------------------------------------------------------------------------

def test_chartoint_true_fact_sat():
    _assert_parity(lambda m: m.CharToInt(m.CharVal(65)) == 65, "sat")


def test_chartoint_wrong_fact_unsat_SOUNDNESS():
    _assert_parity(lambda m: m.CharToInt(m.CharVal(65)) == 66, "unsat")


def test_chartoint_str_coercion():
    # z3py coerces a length-1 str to a char before to_int.
    _assert_parity(lambda m: m.CharToInt("A") == 65, "sat")


# ---------------------------------------------------------------------------
# CharToBv  (char.to_bv : BitVec 18)
# ---------------------------------------------------------------------------

def test_chartobv_width_is_18():
    assert z.CharToBv(z.CharVal(65)).sort_ref.size() == 18


def test_chartobv_true_fact_sat():
    _assert_parity(
        lambda m: m.CharToBv(m.CharVal(65)) == m.BitVecVal(65, 18), "sat")


def test_chartobv_wrong_fact_unsat_SOUNDNESS():
    _assert_parity(
        lambda m: m.CharToBv(m.CharVal(65)) == m.BitVecVal(66, 18), "unsat")


# ---------------------------------------------------------------------------
# CharIsDigit  (char.is_digit)
# ---------------------------------------------------------------------------

def test_charisdigit_digit_sat():
    _assert_parity(lambda m: m.CharIsDigit(m.CharVal(53)), "sat")  # '5'


def test_charisdigit_nondigit_unsat_SOUNDNESS():
    _assert_parity(lambda m: m.CharIsDigit(m.CharVal(65)), "unsat")  # 'A'


def test_charisdigit_boundary():
    # '0' (48) and '9' (57) are digits; '/' (47) and ':' (58) are not.
    _assert_parity(lambda m: m.CharIsDigit(m.CharVal(48)), "sat")
    _assert_parity(lambda m: m.CharIsDigit(m.CharVal(57)), "sat")
    _assert_parity(lambda m: m.CharIsDigit(m.CharVal(47)), "unsat")
    _assert_parity(lambda m: m.CharIsDigit(m.CharVal(58)), "unsat")


# ---------------------------------------------------------------------------
# CharVal argument handling (matches z3py: int code point or length-1 str)
# ---------------------------------------------------------------------------

def test_charval_accepts_str_and_int_equivalently():
    _assert_parity(lambda m: m.CharToInt(m.CharVal("A")) == 65, "sat")


def test_charval_rejects_bad_input():
    with pytest.raises(z.AyZ3Exception):
        z.CharVal("AB")   # not length-1
    with pytest.raises(z.AyZ3Exception):
        z.CharVal(-1)     # out of range


def test_lastindexof_is_not_exposed():
    # Honest absence: AY's seq.last_indexof is unsound on ground inputs.
    assert not hasattr(z, "LastIndexOf")
    assert "LastIndexOf" not in z.__all__

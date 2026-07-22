# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
#
# Self-contained core-surface tests for the ayz3 z3py-shaped binding.
#
# Unlike the other suites (which cross-check against the *z3py* Python module
# when it happens to be installed), this file:
#
#   1. Builds a battery of small problems through the ayz3 Python API exercising
#      the core z3py surface -- Solver push/pop, Int/Real/Bool/BitVec consts,
#      And/Or/Not/Implies/Xor/If/Distinct, arithmetic + comparisons, add/check,
#      model readout and model.eval -- and asserts the EXPECTED sat/unsat verdict
#      and (where determinate) the expected model values.
#
#   2. Independently cross-checks a representative subset against the **z3 CLI**
#      (the `z3` binary), by emitting the equivalent SMT-LIB and comparing the
#      verdict. This is a *different oracle* from z3py: it needs no Python z3
#      module, only the `z3` executable on PATH, so it runs in environments
#      where z3py is absent.
#
# SOUNDNESS: every cross-checked case asserts ayz3's verdict EQUALS z3's. A
# disagreement (sat-vs-unsat) is a hard failure. Cases where ayz3 honestly
# returns `unknown` are surfaced (skipped, not failed) -- ayz3 must never report
# a verdict that contradicts z3.
#
# Run:  cargo build -p ay-ffi  &&  pytest bindings/python/tests/test_z3cli_crosscheck.py -v

import shutil
import subprocess
from fractions import Fraction

import pytest

import ayz3 as z


# ---------------------------------------------------------------------------
# z3 CLI oracle (independent of the z3py Python module)
# ---------------------------------------------------------------------------

_Z3_BIN = shutil.which("z3")
HAVE_Z3_CLI = _Z3_BIN is not None


def _z3_cli_verdict(smt2: str) -> str:
    """Run the z3 binary on an SMT-LIB2 string; return 'sat'/'unsat'/'unknown'."""
    proc = subprocess.run(
        [_Z3_BIN, "-smt2", "-in"],
        input=smt2,
        capture_output=True,
        text=True,
        timeout=30,
    )
    out = proc.stdout.strip().splitlines()
    for line in out:
        line = line.strip()
        if line in ("sat", "unsat", "unknown"):
            return line
    return "unknown"


def _ayz3_verdict_token(res) -> str:
    return {z.sat: "sat", z.unsat: "unsat", z.unknown: "unknown"}[res]


def fresh():
    """A Solver with its own isolated Context (independent assertion stack).

    Each problem gets a fresh Context so re-using a const NAME across problems
    (even with a different sort) can never collide on the shared main context.
    """
    return z.Solver(z.Context())


def _crosscheck(ayz3_res, smt2: str, label: str):
    """Assert ayz3's verdict does not contradict the z3 CLI on `smt2`.

    Agreement (both sat / both unsat) passes. If EITHER side is `unknown`, that
    is sound incompleteness, not a bug -> skip. A genuine sat-vs-unsat clash is
    a hard failure.
    """
    if not HAVE_Z3_CLI:
        pytest.skip("z3 CLI not on PATH")
    ay = _ayz3_verdict_token(ayz3_res)
    zz = _z3_cli_verdict(smt2)
    if ay == "unknown" or zz == "unknown":
        pytest.skip(f"{label}: incomplete (ayz3={ay}, z3={zz}) -- not a soundness bug")
    assert ay == zz, f"{label}: VERDICT CLASH ayz3={ay} z3={zz}\nSMT-LIB:\n{smt2}"


# ===========================================================================
# Int: arithmetic, comparisons, model values
# ===========================================================================

def test_int_linear_system_sat_and_model():
    s = fresh()
    with s.using():
        x = z.Int("x")
        y = z.Int("y")
        s.add(x + y == 10, x - y == 4)
    assert s.check() == z.sat
    m = s.model()
    assert m[x].as_long() == 7
    assert m[y].as_long() == 3
    _crosscheck(
        s.check(),
        "(declare-const x Int)(declare-const y Int)"
        "(assert (= (+ x y) 10))(assert (= (- x y) 4))(check-sat)",
        "int_linear_system",
    )


def test_int_range_unsat():
    s = fresh()
    with s.using():
        x = z.Int("x")
        s.add(x > 5, x < 3)
    assert s.check() == z.unsat
    _crosscheck(
        s.check(),
        "(declare-const x Int)(assert (> x 5))(assert (< x 3))(check-sat)",
        "int_range_unsat",
    )


def test_int_multiplication_and_coercion():
    s = fresh()
    with s.using():
        x = z.Int("x")
        s.add(x == z.IntVal(6), 2 * x >= 12, 3 * x <= 18)
    assert s.check() == z.sat
    assert s.model()[x].as_long() == 6
    _crosscheck(
        s.check(),
        "(declare-const x Int)(assert (= x 6))"
        "(assert (>= (* 2 x) 12))(assert (<= (* 3 x) 18))(check-sat)",
        "int_mul_coercion",
    )


def test_int_mod():
    s = fresh()
    with s.using():
        x = z.Int("x")
        s.add(x % 5 == 2, x > 10, x < 20)
    assert s.check() == z.sat
    v = s.model()[x].as_long()
    assert v % 5 == 2 and 10 < v < 20
    _crosscheck(
        s.check(),
        "(declare-const x Int)(assert (= (mod x 5) 2))"
        "(assert (> x 10))(assert (< x 20))(check-sat)",
        "int_mod",
    )


# ===========================================================================
# Real: rational model values
# ===========================================================================

def test_real_rational_model():
    s = fresh()
    with s.using():
        r = z.Real("r")
        s.add(2 * r == 3)
    assert s.check() == z.sat
    assert s.model()[r].as_fraction() == Fraction(3, 2)
    _crosscheck(
        s.check(),
        "(declare-const r Real)(assert (= (* 2 r) 3))(check-sat)",
        "real_rational",
    )


def test_real_strict_bounds_sat():
    s = fresh()
    with s.using():
        a = z.Real("a")
        b = z.Real("b")
        s.add(a < b, a > 0, b < 1)
    assert s.check() == z.sat
    m = s.model()
    assert 0 < m[a].as_fraction() < m[b].as_fraction() < 1
    _crosscheck(
        s.check(),
        "(declare-const a Real)(declare-const b Real)"
        "(assert (< a b))(assert (> a 0))(assert (< b 1))(check-sat)",
        "real_strict_bounds",
    )


def test_real_unsat():
    s = fresh()
    with s.using():
        a = z.Real("a")
        s.add(a > 1, a < 1)
    assert s.check() == z.unsat
    _crosscheck(
        s.check(),
        "(declare-const a Real)(assert (> a 1))(assert (< a 1))(check-sat)",
        "real_unsat",
    )


# ===========================================================================
# Bool: And/Or/Not/Implies/Xor/If, model eval
# ===========================================================================

def test_bool_and_or_not():
    s = fresh()
    with s.using():
        p = z.Bool("p")
        q = z.Bool("q")
        s.add(z.Or(p, q), z.Not(p))
    assert s.check() == z.sat
    m = s.model()
    # ~p forces p False; Or(p,q) then forces q True.
    assert z.is_true(m.eval(q))
    assert z.is_false(m.eval(p))
    _crosscheck(
        s.check(),
        "(declare-const p Bool)(declare-const q Bool)"
        "(assert (or p q))(assert (not p))(check-sat)",
        "bool_and_or_not",
    )


def test_bool_implies_modus_ponens_unsat():
    # (p -> q) and p and ~q is unsatisfiable.
    s = fresh()
    with s.using():
        p = z.Bool("p")
        q = z.Bool("q")
        s.add(z.Implies(p, q), p, z.Not(q))
    assert s.check() == z.unsat
    _crosscheck(
        s.check(),
        "(declare-const p Bool)(declare-const q Bool)"
        "(assert (=> p q))(assert p)(assert (not q))(check-sat)",
        "bool_modus_ponens",
    )


def test_bool_xor():
    s = fresh()
    with s.using():
        p = z.Bool("p")
        q = z.Bool("q")
        s.add(z.Xor(p, q), p)
    assert s.check() == z.sat
    m = s.model()
    assert z.is_true(m.eval(p)) and z.is_false(m.eval(q))
    _crosscheck(
        s.check(),
        "(declare-const p Bool)(declare-const q Bool)"
        "(assert (xor p q))(assert p)(check-sat)",
        "bool_xor",
    )


def test_bool_xor_both_or_neither_unsat():
    # Xor(p,q) with p==q forced is unsat.
    s = fresh()
    with s.using():
        p = z.Bool("p")
        q = z.Bool("q")
        s.add(z.Xor(p, q), p == q)
    assert s.check() == z.unsat
    _crosscheck(
        s.check(),
        "(declare-const p Bool)(declare-const q Bool)"
        "(assert (xor p q))(assert (= p q))(check-sat)",
        "bool_xor_unsat",
    )


def test_if_then_else_over_int():
    # abs(x) == 5 with x < 0 forces x == -5.
    s = fresh()
    with s.using():
        x = z.Int("x")
        s.add(z.If(x > 0, x, -x) == 5, x < 0)
    assert s.check() == z.sat
    assert s.model()[x].as_long() == -5
    _crosscheck(
        s.check(),
        "(declare-const x Int)"
        "(assert (= (ite (> x 0) x (- x)) 5))(assert (< x 0))(check-sat)",
        "ite_abs",
    )


# ===========================================================================
# Distinct
# ===========================================================================

def test_distinct_sat():
    s = fresh()
    with s.using():
        a, b, c = z.Int("a"), z.Int("b"), z.Int("c")
        s.add(z.Distinct(a, b, c),
              a >= 0, a <= 2, b >= 0, b <= 2, c >= 0, c <= 2)
    assert s.check() == z.sat
    m = s.model()
    vals = {m[a].as_long(), m[b].as_long(), m[c].as_long()}
    assert len(vals) == 3  # genuinely distinct
    _crosscheck(
        s.check(),
        "(declare-const a Int)(declare-const b Int)(declare-const c Int)"
        "(assert (distinct a b c))"
        "(assert (>= a 0))(assert (<= a 2))"
        "(assert (>= b 0))(assert (<= b 2))"
        "(assert (>= c 0))(assert (<= c 2))(check-sat)",
        "distinct_sat",
    )


def test_distinct_pigeonhole_unsat():
    # 3 distinct values pinned to {0,1} cannot exist (pigeonhole).
    s = fresh()
    with s.using():
        a, b, c = z.Int("a"), z.Int("b"), z.Int("c")
        s.add(z.Distinct(a, b, c),
              a >= 0, a <= 1, b >= 0, b <= 1, c >= 0, c <= 1)
    assert s.check() == z.unsat
    _crosscheck(
        s.check(),
        "(declare-const a Int)(declare-const b Int)(declare-const c Int)"
        "(assert (distinct a b c))"
        "(assert (>= a 0))(assert (<= a 1))"
        "(assert (>= b 0))(assert (<= b 1))"
        "(assert (>= c 0))(assert (<= c 1))(check-sat)",
        "distinct_pigeonhole",
    )


# ===========================================================================
# BitVec: arithmetic, signed vs unsigned comparison, model values
# ===========================================================================

def test_bitvec_add_model():
    s = fresh()
    with s.using():
        bv = z.BitVec("bv", 8)
        s.add(bv + z.BitVecVal(1, 8) == z.BitVecVal(5, 8))
    assert s.check() == z.sat
    assert s.model()[bv].as_long() == 4
    _crosscheck(
        s.check(),
        "(declare-const bv (_ BitVec 8))"
        "(assert (= (bvadd bv #x01) #x05))(check-sat)",
        "bv_add",
    )


def test_bitvec_signed_default_compare():
    # z3py default BitVec '<' is SIGNED: 0xFF (== -1 signed) < 1 is TRUE.
    s = fresh()
    with s.using():
        x = z.BitVec("x", 8)
        s.add(x == z.BitVecVal(0xFF, 8), x < z.BitVecVal(1, 8))
    assert s.check() == z.sat  # signed -1 < 1
    _crosscheck(
        s.check(),
        "(declare-const x (_ BitVec 8))"
        "(assert (= x #xFF))(assert (bvslt x #x01))(check-sat)",
        "bv_signed_lt",
    )


def test_bitvec_unsigned_compare():
    # The SAME 0xFF is NOT unsigned-< 1 (it is 255). Forcing ULT -> unsat.
    s = fresh()
    with s.using():
        x = z.BitVec("x", 8)
        s.add(x == z.BitVecVal(0xFF, 8), z.ULT(x, z.BitVecVal(1, 8)))
    assert s.check() == z.unsat  # unsigned 255 < 1 is false
    _crosscheck(
        s.check(),
        "(declare-const x (_ BitVec 8))"
        "(assert (= x #xFF))(assert (bvult x #x01))(check-sat)",
        "bv_unsigned_ult",
    )


def test_bitvec_overflow_wraparound():
    # 8-bit wraparound: 0xFF + 1 == 0x00.
    s = fresh()
    with s.using():
        x = z.BitVec("x", 8)
        s.add(x == z.BitVecVal(0xFF, 8),
              x + z.BitVecVal(1, 8) == z.BitVecVal(0, 8))
    assert s.check() == z.sat
    _crosscheck(
        s.check(),
        "(declare-const x (_ BitVec 8))"
        "(assert (= x #xFF))(assert (= (bvadd x #x01) #x00))(check-sat)",
        "bv_wraparound",
    )


# ===========================================================================
# Solver push / pop : incremental backtracking
# ===========================================================================

def test_push_pop_recovers_satisfiability():
    s = fresh()
    with s.using():
        x = z.Int("x")
        s.add(x > 0)
        assert s.check() == z.sat
        s.push()
        s.add(x < 0)            # contradicts x > 0 within this frame
        assert s.check() == z.unsat
        s.pop()                 # discard the contradictory frame
        assert s.check() == z.sat
        s.add(x == 7)           # still satisfiable after pop
        assert s.check() == z.sat
        assert s.model()[x].as_long() == 7


def test_push_pop_nested():
    s = fresh()
    with s.using():
        x = z.Int("x")
        y = z.Int("y")
        s.add(x + y == 10)
        s.push()
        s.add(x == 3)
        assert s.check() == z.sat
        assert s.model()[y].as_long() == 7
        s.push()
        s.add(y == 0)           # 3 + 0 != 10
        assert s.check() == z.unsat
        s.pop()                 # back to x == 3 frame
        assert s.check() == z.sat
        s.pop()                 # back to just x + y == 10
        s.add(x == 4)
        assert s.check() == z.sat
        assert s.model()[y].as_long() == 6


# ===========================================================================
# check() with assumptions (z3py s.check(a, b, ...))
# ===========================================================================

def test_check_with_assumptions():
    s = fresh()
    with s.using():
        p = z.Bool("p")
        q = z.Bool("q")
        s.add(z.Implies(p, q))
    # Assuming p and ~q contradicts the implication -> unsat under assumptions.
    assert s.check(p, z.Not(q)) == z.unsat
    # Assuming just p is fine (q can be True) -> sat.
    assert s.check(p) == z.sat
    # No assumptions: the bare implication is satisfiable.
    assert s.check() == z.sat


# ===========================================================================
# model.eval on a compound expression
# ===========================================================================

def test_model_eval_compound():
    s = fresh()
    with s.using():
        a = z.Int("a")
        b = z.Int("b")
        s.add(a == 3, b == 4)
    assert s.check() == z.sat
    m = s.model()
    assert m.eval(a + b).as_long() == 7
    assert m.eval(a * b).as_long() == 12
    assert z.is_true(m.eval(a < b))
    assert z.is_false(m.eval(a > b))


# ===========================================================================
# A small combined / mixed problem touching several features at once
# ===========================================================================

def test_mixed_bool_int_problem():
    # If the flag is set, x is large; else small. We force the flag and read x.
    s = fresh()
    with s.using():
        flag = z.Bool("flag")
        x = z.Int("x")
        s.add(z.Implies(flag, x >= 100))
        s.add(z.Implies(z.Not(flag), x < 10))
        s.add(flag, x <= 100)
    assert s.check() == z.sat
    m = s.model()
    assert z.is_true(m.eval(flag))
    assert m[x].as_long() == 100
    _crosscheck(
        s.check(),
        "(declare-const flag Bool)(declare-const x Int)"
        "(assert (=> flag (>= x 100)))"
        "(assert (=> (not flag) (< x 10)))"
        "(assert flag)(assert (<= x 100))(check-sat)",
        "mixed_bool_int",
    )


# ===========================================================================
# Meta: the z3 CLI oracle itself is wired and used (guards against silent skip)
# ===========================================================================

def test_z3_cli_available_and_self_consistent():
    if not HAVE_Z3_CLI:
        pytest.skip("z3 CLI not on PATH")
    assert _z3_cli_verdict("(declare-const x Int)(assert (> x 0))(check-sat)") == "sat"
    assert _z3_cli_verdict(
        "(declare-const x Int)(assert (> x 0))(assert (< x 0))(check-sat)"
    ) == "unsat"


# ===========================================================================
# Soundness guard: re-declaring a const NAME at a different sort.
#
# AY hash-conses a const purely by name within a context, so `Int('v')` after
# `Bool('v')` used to silently return the Bool handle (wrong sort) and then
# panic inside the Rust core when compared. The binding now fails CLOSED to a
# clear Python exception instead of returning a type-confused expression.
# ===========================================================================

def test_const_name_sort_collision_raises_not_crashes():
    ctx = z.Context()
    z.Bool("v", ctx)
    with pytest.raises(z.AyZ3Exception):
        z.Int("v", ctx)        # same name, different sort -> clean error


def test_const_bitvec_width_collision_raises():
    ctx = z.Context()
    z.BitVec("w", 8, ctx)
    with pytest.raises(z.AyZ3Exception):
        z.BitVec("w", 16, ctx)  # same name, different width -> clean error


def test_const_same_sort_redeclare_is_allowed():
    # z3py allows declaring the same const twice (it is the same node).
    ctx = z.Context()
    a = z.Int("a", ctx)
    b = z.Int("a", ctx)
    assert a.ast == b.ast       # genuinely the same interned const


def test_const_name_reuse_across_contexts_is_independent():
    # Different contexts -> the same name may take any sort.
    c1, c2 = z.Context(), z.Context()
    z.Int("n", c1)
    z.Bool("n", c2)             # must NOT raise: different context

# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
#
# End-to-end tests for the ayz3 pseudo-boolean / cardinality surface
# (AtMost / AtLeast / PbLe / PbGe / PbEq), run through AY's real solver via the
# C ABI. Where real z3py is installed the SAME snippet is cross-checked against
# z3py and the verdicts must agree.
#
# Run:  cargo build -p ay-ffi   &&   pytest bindings/python/tests -v

import random

import pytest

import ayz3 as z

try:
    import z3 as _z3
    HAVE_Z3PY = True
except Exception:  # pragma: no cover - depends on environment
    _z3 = None
    HAVE_Z3PY = False


def fresh_solver():
    return z.Solver(z.Context())


# ---------------------------------------------------------------------------
# Cardinality: AtMost / AtLeast
# ---------------------------------------------------------------------------

def test_atmost_atleast_conflict_unsat():
    a, b, c = z.Bool("a"), z.Bool("b"), z.Bool("c")
    s = fresh_solver()
    # positional (z3py) form: bound is the last argument
    s.add(z.AtMost(a, b, c, 1))
    s.add(z.AtLeast(a, b, c, 2))
    assert s.check() == z.unsat


def test_atmost_keyword_bound():
    # ayz3 also accepts an explicit k= keyword (superset of z3py's positional form).
    a, b, c = z.Bool("a"), z.Bool("b"), z.Bool("c")
    s = fresh_solver()
    s.add(z.AtMost(a, b, c, k=1))
    s.add(z.AtLeast(a, b, c, k=2))
    assert s.check() == z.unsat


def test_atmost_sat():
    a, b, c = z.Bool("a"), z.Bool("b"), z.Bool("c")
    s = fresh_solver()
    s.add(z.AtMost(a, b, c, 2))
    assert s.check() == z.sat


def test_atleast_forces_true():
    a, b, c = z.Bool("a"), z.Bool("b"), z.Bool("c")
    s = fresh_solver()
    s.add(z.AtLeast(a, b, c, 3))
    assert s.check() == z.sat
    m = s.model()
    assert all(
        m.eval(v, model_completion=True).as_bool() for v in (a, b, c)
    ), "at-least 3 of 3 forces all true"


# ---------------------------------------------------------------------------
# Weighted PB: PbLe / PbGe / PbEq
# ---------------------------------------------------------------------------

def test_pble_pbge_conflict_unsat():
    a, b, c = z.Bool("a"), z.Bool("b"), z.Bool("c")
    s = fresh_solver()
    s.add(z.PbLe(((a, 2), (b, 3), (c, 4)), 3))
    s.add(z.PbGe(((a, 2), (b, 3), (c, 4)), 5))
    assert s.check() == z.unsat


def test_pbeq_sat_model():
    a, b, c = z.Bool("a"), z.Bool("b"), z.Bool("c")
    s = fresh_solver()
    s.add(z.PbEq(((a, 2), (b, 3), (c, 4)), 5))
    assert s.check() == z.sat
    m = s.model()
    val = {v: m.eval(v, model_completion=True).as_bool() for v in (a, b, c)}
    total = 2 * val[a] + 3 * val[b] + 4 * val[c]
    assert total == 5


def test_pb_negative_coefficient():
    # Signed coefficients are supported (Z3's pb coeffs are `int`).
    a, b = z.Bool("a"), z.Bool("b")
    s = fresh_solver()
    # -1*a + 2*b >= 2  =>  requires b true and a false (0-1 range: max 2, needs 2).
    s.add(z.PbGe(((a, -1), (b, 2)), 2))
    assert s.check() == z.sat
    m = s.model()
    assert m.eval(b, model_completion=True).as_bool()
    assert not m.eval(a, model_completion=True).as_bool()


# ---------------------------------------------------------------------------
# Input validation
# ---------------------------------------------------------------------------

def test_atmost_requires_bound():
    with pytest.raises(z.AyZ3Exception):
        z.AtMost()  # no literals, no bound


def test_pb_requires_pairs():
    a = z.Bool("a")
    with pytest.raises(z.AyZ3Exception):
        z.PbLe([a], 1)  # not a (lit, coeff) pair


# ---------------------------------------------------------------------------
# Differential vs real z3py on random cardinality/PB instances.
# ---------------------------------------------------------------------------

@pytest.mark.skipif(not HAVE_Z3PY, reason="real z3py not installed")
def test_pb_differential_vs_z3py():
    def build(mod, seed):
        random.seed(seed)
        n = random.randint(2, 6)
        vs = [mod.Bool(f"v{i}") for i in range(n)]
        s = mod.Solver()
        for _ in range(random.randint(1, 4)):
            kind = random.choice(["atmost", "atleast", "pble", "pbge", "pbeq"])
            m = random.randint(1, n)
            idx = random.sample(range(n), m)
            lits = [mod.Not(vs[i]) if random.random() < 0.35 else vs[i] for i in idx]
            if kind in ("atmost", "atleast"):
                k = random.randint(0, m + 1)
                con = (mod.AtMost(*lits, k) if kind == "atmost"
                       else mod.AtLeast(*lits, k))
            else:
                coeffs = [random.randint(0, 5) for _ in range(m)]
                k = random.randint(0, sum(coeffs) + 2)
                pairs = list(zip(lits, coeffs))
                con = {"pble": mod.PbLe, "pbge": mod.PbGe,
                       "pbeq": mod.PbEq}[kind](pairs, k)
            if random.random() < 0.25:
                con = mod.Not(con)
            s.add(con)
        for _ in range(random.randint(0, 2)):
            i, j = random.sample(range(n), 2)
            s.add(mod.Or(vs[i], vs[j]))
        return s

    disagreements = []
    for seed in range(60):
        ay_v = str(build(z, seed).check())
        z3_v = str(build(_z3, seed).check())
        if ay_v != z3_v:
            disagreements.append((seed, ay_v, z3_v))
    assert not disagreements, f"ayz3 vs z3py PB disagreements: {disagreements}"


# ---------------------------------------------------------------------------
# 32-bit range validation: the C ABI takes coefficients as c_int and
# cardinality bounds as c_uint. Out-of-range Python ints used to WRAP silently
# in ctypes (e.g. 2**31 -> -2**31, AtMost bound -1 -> 4294967295), building a
# DIFFERENT constraint than the user wrote. They must raise instead.
# ---------------------------------------------------------------------------

def test_pb_coefficient_out_of_range_raises():
    a = z.Bool("pb_range_a")
    with pytest.raises(z.AyZ3Exception, match="signed 32-bit"):
        z.PbLe(((a, 2**31),), 0)
    with pytest.raises(z.AyZ3Exception, match="signed 32-bit"):
        z.PbGe(((a, -(2**31) - 1),), 0)


def test_pb_threshold_out_of_range_raises():
    a = z.Bool("pb_range_b")
    with pytest.raises(z.AyZ3Exception, match="signed 32-bit"):
        z.PbEq(((a, 1),), 2**31)
    with pytest.raises(z.AyZ3Exception, match="signed 32-bit"):
        z.PbLe(((a, 1),), -(2**31) - 1)


def test_cardinality_bound_out_of_range_raises():
    a, b = z.Bool("pb_range_c"), z.Bool("pb_range_d")
    # The AtMost/AtLeast bound is unsigned at the C level: -1 used to wrap to
    # 4294967295 (a trivially-true AtMost).
    with pytest.raises(z.AyZ3Exception, match="unsigned 32-bit"):
        z.AtMost(a, b, -1)
    with pytest.raises(z.AyZ3Exception, match="unsigned 32-bit"):
        z.AtLeast(a, b, 2**32)


def test_pb_boundary_values_still_accepted():
    # Extremes that DO fit in the C types must keep working.
    a = z.Bool("pb_range_e")
    s = fresh_solver()
    s.add(z.PbGe(((a, 2**31 - 1),), 1))
    assert s.check() == z.sat
    s2 = fresh_solver()
    s2.add(z.AtMost(z.Bool("pb_range_f"), z.Bool("pb_range_g"), 0))
    assert s2.check() == z.sat

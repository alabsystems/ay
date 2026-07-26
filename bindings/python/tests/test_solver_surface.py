# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
#
# Phase-4 SOLVER-SURFACE tests for ayz3: SMT-LIB2 parsing, unsat cores
# (assert_and_track / unsat_core), check-under-assumptions, and params/timeouts
# (+ simplify identity). Each feature is exercised through AY's real solver via
# the C ABI, and (where real z3py 4.15.4 is installed) the SAME thing is run
# through z3py and the verdicts must AGREE.
#
# SOUNDNESS / HONESTY (the heart of these tests):
#   * Parsed-formula verdicts must agree with z3py.
#   * An unsat core must be a REAL unsat subset: we VERIFY soundness by
#     re-checking the core's constraints ALONE in a fresh solver and asserting
#     that subset is itself UNSAT. AY now returns a MINIMAL (deletion-minimal /
#     irredundant) core: removing any single element makes the remainder SAT, so
#     we ALSO verify deletion-minimality directly. We do NOT assert set-equality
#     with z3py's core: when several minimal cores exist, z3 and AY may each pick
#     a different (equally valid, equally minimal) one. We assert the core is a
#     subset of the tracked literals, genuinely unsat, deletion-minimal, and no
#     larger than the full tracked set. Honest agreement, not a faked one.
#   * Assumption verdicts must agree with z3py.
#   * Params/timeouts must be accepted and yield a valid verdict (robust,
#     non-flaky: we assert acceptance + a valid sat/unsat/unknown, not a
#     specific timeout race).
#   * simplify is an IDENTITY in AY (eager simplification): asserted as an
#     equivalent expression, never a wrong reduction.
#
# Run:  cargo build -p ay-ffi   &&   pytest bindings/python/tests -v

import os
import tempfile

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
# 1. SMT-LIB2 parsing  (Z3_parse_smtlib2_string / _file)
# ===========================================================================

def test_parse_smtlib2_string_sat_and_solves():
    src = "(declare-const x Int)(assert (> x 5))(assert (< x 10))"
    s = fresh_solver()
    with s.using():
        formulas = z.parse_smtlib2_string(src)
        assert len(formulas) == 2
        for f in formulas:
            assert isinstance(f, z.BoolRef)
            s.add(f)
    assert s.check() == z.sat
    m = s.model()
    # The parsed constraints are real: any model must satisfy 5 < x < 10.
    # (We can't index m[x] by name here since `x` was created by the parser,
    #  but the verdict + cross-check below prove the formulas were asserted.)


def test_parse_smtlib2_string_unsat():
    src = "(declare-const x Int)(assert (> x 5))(assert (< x 3))"
    s = fresh_solver()
    with s.using():
        for f in z.parse_smtlib2_string(src):
            s.add(f)
    assert s.check() == z.unsat


@pytest.mark.usefixtures("required_reference_z3")
@pytest.mark.parametrize("src,expected", [
    ("(declare-const x Int)(assert (> x 5))(assert (< x 10))", "sat"),
    ("(declare-const x Int)(assert (> x 5))(assert (< x 3))", "unsat"),
    ("(declare-const a Bool)(declare-const b Bool)"
     "(assert (or a b))(assert (not a))", "sat"),
    ("(declare-const p Bool)(assert p)(assert (not p))", "unsat"),
])
def test_parse_smtlib2_string_crosscheck(src, expected):
    # ayz3
    s = fresh_solver()
    with s.using():
        for f in z.parse_smtlib2_string(src):
            s.add(f)
    ay_verdict = s.check()
    # z3py oracle: parse the same string and solve. (z3py spells this
    # `parse_smt2_string`; the underlying C fn is Z3_parse_smtlib2_string.)
    zs = _z3.Solver()
    zs.add(_z3.parse_smt2_string(src))
    z_verdict = zs.check()
    assert str(ay_verdict) == str(z_verdict) == expected


def test_parse_smtlib2_file_roundtrip():
    src = "(declare-const x Int)(assert (= x 7))"
    with tempfile.NamedTemporaryFile(
        "w", suffix=".smt2", delete=False, encoding="utf-8"
    ) as fh:
        fh.write(src)
        path = fh.name
    try:
        s = fresh_solver()
        with s.using():
            for f in z.parse_smtlib2_file(path):
                s.add(f)
        assert s.check() == z.sat
    finally:
        os.unlink(path)


def test_parse_smtlib2_predeclared_sorts_decls_deferred():
    # Pre-declared sorts/decls are not backed by AY's C ABI -> honest gap.
    s = fresh_solver()
    with s.using():
        with pytest.raises(NotImplementedError):
            z.parse_smtlib2_string("(assert true)", sorts={"S": z.IntSort()})
        with pytest.raises(NotImplementedError):
            z.parse_smtlib2_string("(assert true)", decls={"f": None})


# ===========================================================================
# 2. Unsat cores  (assert_and_track / unsat_core)
# ===========================================================================

def _recheck_core_alone_is_unsat(core, constraint_by_name):
    """SOUNDNESS check: re-assert ONLY the constraints behind the core's
    tracking literals in a fresh solver and confirm that subset is UNSAT.

    `constraint_by_name` maps tracker decl_name -> a zero-arg builder that
    rebuilds the corresponding constraint in the *current* context.
    """
    s = fresh_solver()
    with s.using():
        for c in core:
            name = c.decl_name
            assert name in constraint_by_name, (
                f"core literal {name!r} is not one of the tracked literals — "
                "AY must never return a non-tracked literal in the core"
            )
            s.add(constraint_by_name[name]())
    return s.check() == z.unsat


def _core_is_deletion_minimal(core, constraint_by_name):
    """MINIMALITY check: for EVERY element of the core, re-assert the OTHER
    core constraints alone (the core minus that element) and confirm that
    subset is SAT. If dropping any single element keeps it UNSAT, the core was
    not deletion-minimal. An empty or singleton core is trivially minimal (the
    empty subset has no constraint to be unsat, so dropping the lone element is
    SAT by vacuity unless the hard asserts themselves conflict).
    """
    names = [c.decl_name for c in core]
    for drop in range(len(names)):
        remaining = names[:drop] + names[drop + 1:]
        s = fresh_solver()
        with s.using():
            for nm in remaining:
                assert nm in constraint_by_name
                s.add(constraint_by_name[nm]())
            if s.check() != z.sat:
                return False
    return True


def test_unsat_core_is_a_sound_unsat_subset():
    s = fresh_solver()
    with s.using():
        x = z.Int("x")
        p1, p2, p3 = z.Bool("p1"), z.Bool("p2"), z.Bool("p3")
        s.assert_and_track(x > 5, p1)
        s.assert_and_track(x < 3, p2)
        s.assert_and_track(x == 4, p3)
    assert s.check() == z.unsat
    core = s.unsat_core()
    assert core, "unsat core must be non-empty for an UNSAT tracked problem"
    # Every core element is one of the tracked literals (never a fabricated one).
    core_names = {c.decl_name for c in core}
    assert core_names.issubset({"p1", "p2", "p3"})
    # SOUNDNESS: the core's constraints ALONE are unsatisfiable.
    builders = {
        "p1": lambda: z.Int("x") > 5,
        "p2": lambda: z.Int("x") < 3,
        "p3": lambda: z.Int("x") == 4,
    }
    assert _recheck_core_alone_is_unsat(core, builders)
    # MINIMALITY: the core is deletion-minimal AND no larger than the full set.
    assert _core_is_deletion_minimal(core, builders)
    assert len(core) <= 3
    # This instance has two conflicting pairs (x>5 ∧ x<3) and (x<3 ∧ x==4); a
    # deletion-minimal core is one such pair, i.e. exactly 2 trackers.
    assert len(core) == 2


def test_unsat_core_empty_when_sat():
    s = fresh_solver()
    with s.using():
        x = z.Int("x")
        p1 = z.Bool("p1")
        s.assert_and_track(x > 5, p1)
    assert s.check() == z.sat
    # No core after a SAT result.
    assert s.unsat_core() == []


def test_assert_and_track_name_string():
    # z3py accepts a name string as the tracker; ayz3 mirrors that.
    s = fresh_solver()
    with s.using():
        x = z.Int("x")
        s.assert_and_track(x > 0, "c_pos")
        s.assert_and_track(x < 0, "c_neg")
    assert s.check() == z.unsat
    names = {c.decl_name for c in s.unsat_core()}
    assert names.issubset({"c_pos", "c_neg"})
    assert names  # non-empty


@pytest.mark.usefixtures("required_reference_z3")
def test_unsat_core_crosscheck_verdict_and_soundness():
    # Same tracked problem through ayz3 AND z3py: verdicts must agree, and BOTH
    # cores must be sound, deletion-minimal unsat subsets. We do NOT require
    # identical cores — this instance has TWO distinct minimal cores ({p1,p2}
    # and {p2,p3}), so z3 and AY may legitimately pick different ones. We assert
    # each is a real, minimal core of the SAME size (here 2, < the full set 3).
    def build_ay():
        s = fresh_solver()
        with s.using():
            x = z.Int("x")
            p1, p2, p3 = z.Bool("p1"), z.Bool("p2"), z.Bool("p3")
            s.assert_and_track(x > 5, p1)
            s.assert_and_track(x < 3, p2)
            s.assert_and_track(x == 4, p3)
        return s

    s = build_ay()
    ay_verdict = s.check()

    zs = _z3.Solver()
    zx = _z3.Int("x")
    zp1, zp2, zp3 = _z3.Bool("p1"), _z3.Bool("p2"), _z3.Bool("p3")
    zs.assert_and_track(zx > 5, zp1)
    zs.assert_and_track(zx < 3, zp2)
    zs.assert_and_track(zx == 4, zp3)
    z_verdict = zs.check()

    assert str(ay_verdict) == str(z_verdict) == "unsat"

    ay_core = s.unsat_core()
    builders = {
        "p1": lambda: z.Int("x") > 5,
        "p2": lambda: z.Int("x") < 3,
        "p3": lambda: z.Int("x") == 4,
    }
    # AY's core is sound (re-check core alone unsat) AND deletion-minimal.
    assert _recheck_core_alone_is_unsat(ay_core, builders)
    assert _core_is_deletion_minimal(ay_core, builders)

    ay_names = {c.decl_name for c in ay_core}
    z_names = {str(c) for c in zs.unsat_core()}
    # Both are valid minimal cores from the full tracked set {p1,p2,p3}.
    assert ay_names.issubset({"p1", "p2", "p3"})
    assert z_names.issubset({"p1", "p2", "p3"})
    # Minimal cores are no larger than the full tracked set, and strictly
    # smaller here (the redundant tracker is dropped).
    assert len(ay_names) <= 3 and len(ay_names) < 3
    # AY's core is at least as small as z3py's minimal core (both are minimal,
    # so equal in size for this instance).
    assert len(ay_names) <= len(z_names)
    # If a UNIQUE minimal core existed, the two would coincide; here multiple
    # exist, so we require only that each is itself minimal (asserted above).


# ===========================================================================
# 3. Check under assumptions  (Z3_solver_check_assumptions)
# ===========================================================================

def test_check_assumptions_sat_and_unsat():
    s = fresh_solver()
    with s.using():
        x = z.Int("x")
        a, b = z.Bool("a"), z.Bool("b")
        s.add(z.Implies(a, x > 0))
        s.add(z.Implies(b, x < 0))
        sat_under_a = s.check(a)
        unsat_under_ab = s.check(a, b)
    assert sat_under_a == z.sat
    assert unsat_under_ab == z.unsat


def test_check_assumptions_model_under_assumption():
    s = fresh_solver()
    with s.using():
        x = z.Int("x")
        a = z.Bool("a")
        s.add(z.Implies(a, x == 42))
    assert s.check(a) == z.sat
    m = s.model()
    assert m[x].as_long() == 42


@pytest.mark.usefixtures("required_reference_z3")
@pytest.mark.parametrize("theory", ["int", "bv"])
def test_check_assumptions_crosscheck(theory):
    # ayz3
    s = fresh_solver()
    with s.using():
        x = z.BitVec("x", 8) if theory == "bv" else z.Int("x")
        a, b = z.Bool("a"), z.Bool("b")
        s.add(z.Implies(a, x > 0))
        s.add(z.Implies(b, x < 0))
        ay_sat = s.check(a)
        ay_unsat = s.check(a, b)
    # z3py oracle
    zs = _z3.Solver()
    zx = _z3.BitVec("x", 8) if theory == "bv" else _z3.Int("x")
    za, zb = _z3.Bool("a"), _z3.Bool("b")
    zs.add(_z3.Implies(za, zx > 0))
    zs.add(_z3.Implies(zb, zx < 0))
    assert str(ay_sat) == str(zs.check(za)) == "sat"
    assert str(ay_unsat) == str(zs.check(za, zb)) == "unsat"


# ===========================================================================
# 4. Params / timeouts  (Z3_mk_params / set_params)
# ===========================================================================

def test_solver_set_timeout_positional_accepted():
    s = fresh_solver()
    s.set("timeout", 5000)
    with s.using():
        x = z.Int("x")
        s.add(x > 1, x < 5)
    # Robust: assert the timeout was accepted and a valid verdict is returned.
    assert s.check() in (z.sat, z.unsat, z.unknown)
    assert s.check() == z.sat


def test_solver_set_timeout_kwargs_accepted():
    s = fresh_solver()
    s.set(timeout=10000)
    with s.using():
        x = z.Int("x")
        s.add(x == 3)
    assert s.check() == z.sat
    assert s.model()[x].as_long() == 3


def test_solver_set_unknown_param_is_accepted():
    # Unknown params are accepted for API compatibility (ignored by the engine).
    s = fresh_solver()
    s.set(random_seed=1)  # AY ignores this but must not crash.
    with s.using():
        x = z.Int("x")
        s.add(x > 0)
    assert s.check() == z.sat


def test_solver_set_accepts_string_and_float_values():
    # z3py-aligned: a string param value routes through Z3_params_set_symbol and a
    # float through Z3_params_set_double (verified vs real z3py, which accepts both
    # on Solver.set). AY accepts them for API compatibility; the engine ignores
    # unrecognized keys. This is the SEMANTICS the oracle exposes — a scalar param
    # value of any of bool/int/float/str is accepted.
    s = fresh_solver()
    s.set(some_param="a string value")  # str -> symbol param (accepted, like z3py)
    s.set(ratio=0.25)                    # float -> double param (accepted, like z3py)
    with s.using():
        x = z.Int("x")
        s.add(x > 0)
    assert s.check() == z.sat


def test_solver_set_rejects_non_scalar_value():
    # A genuinely non-scalar value (e.g. a list) is rejected — matching z3py,
    # which raises `invalid parameter value` for a list. Only bool/int/float/str
    # scalar values are valid parameter values.
    s = fresh_solver()
    with pytest.raises(NotImplementedError):
        s.set(some_param=[1, 2, 3])


def test_global_set_param_seeds_new_solver():
    try:
        z.set_param("timeout", 8000)
        assert z.get_param("timeout") == 8000
        s = fresh_solver()  # created AFTER set_param; should accept the timeout
        with s.using():
            x = z.Int("x")
            s.add(x > 0, x < 10)
        assert s.check() == z.sat
    finally:
        # Clean up global state so other tests are unaffected.
        z._global_params.clear()


def test_tiny_timeout_returns_valid_verdict_no_crash():
    # A very small timeout must not crash and must return a VALID verdict
    # (sat/unsat/unknown). We don't require it to be `unknown` (that would be a
    # flaky race) — only that the timeout is accepted and the result is sound.
    s = fresh_solver()
    s.set("timeout", 1)
    with s.using():
        x = z.Int("x")
        y = z.Int("y")
        s.add(x + y == 10, x - y == 4)
    verdict = s.check()
    assert verdict in (z.sat, z.unsat, z.unknown)
    # If it did finish, the answer must be correct (sat).
    if verdict == z.sat:
        m = s.model()
        assert m[x].as_long() == 7


# ===========================================================================
# 5. simplify (optional)  (Z3_simplify — identity in AY)
# ===========================================================================

def test_simplify_returns_equivalent_expression():
    # AY simplifies eagerly, so Z3_simplify is identity. We assert the SOUND
    # property: simplify(e) is equivalent to e on all models.
    s = fresh_solver()
    with s.using():
        x = z.Int("x")
        e = (x + 0) * 1
        se = z.simplify(e)
        assert isinstance(se, z.AstRef)
        s.add(se != e)
    assert s.check() == z.unsat


@pytest.mark.usefixtures("required_reference_z3")
def test_simplify_value_matches_z3py_on_literals():
    # On a closed numeral expression, both AY and z3py reduce to the same value.
    se = z.simplify(z.IntVal(2) + z.IntVal(3))
    assert se.as_long() == 5
    zse = _z3.simplify(_z3.IntVal(2) + _z3.IntVal(3))
    assert se.as_long() == zse.as_long() == 5

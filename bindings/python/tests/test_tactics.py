# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
#
# Tests for ayz3's z3py-compatible tactic surface (Tactic / Then / OrElse /
# Tactic.solver()), backed by AY's tactic framework through the Z3-shaped C
# ABI (Z3_mk_tactic / Z3_tactic_and_then / Z3_tactic_or_else /
# Z3_mk_solver_from_tactic).
#
# SOUNDNESS: every tactic AY exposes is equivalence-preserving, so solving a goal
# via Tactic(...).solver() MUST give the SAME sat/unsat verdict (and a valid
# model) as a plain Solver on that goal. These tests assert exactly that on sat
# and unsat goals with NESTED ANDs (which elim-and actually rewrites), via
# both Tactic('elim-and').solver() and Then(...).solver(). Where real z3py
# 4.15.4 is importable, the same programs are cross-checked against z3py; absent
# z3py, the cross-check is skipped gracefully (and the skip is reported).
#
# Run:  cargo build -p ay-ffi  &&  \
#       AYZ3_LIB=target/debug/libay_ffi.dylib pytest bindings/python/tests/test_tactics.py -v

import pytest

import ayz3 as z

try:
    import z3 as _z3
    HAVE_Z3PY = True
except Exception:  # pragma: no cover - depends on environment
    _z3 = None
    HAVE_Z3PY = False


def _ayz3_nested_and_sat(ctx):
    # (and (and a b) c) — SAT (only model: a,b,c all true).
    a, b, c = z.Bool("a", ctx), z.Bool("b", ctx), z.Bool("c", ctx)
    return z.And(z.And(a, b), c), (a, b, c)


def _ayz3_nested_and_unsat(ctx):
    # (and (and a (not a)) b) — UNSAT (a and not a).
    a, b = z.Bool("a", ctx), z.Bool("b", ctx)
    return z.And(z.And(a, z.Not(a)), b), (a, b)


def _ayz3_nested_and_unsat_int(ctx):
    # (and (and (x>1) (x<1)) (a)) — UNSAT (empty interval).
    x = z.Int("x", ctx)
    a = z.Bool("a", ctx)
    return z.And(z.And(x > 1, x < 1), a), (x, a)


def _ayz3_nested_and_sat_int(ctx):
    # (and (and (x>0) (x<2)) (or a b)) — SAT (x=1).
    x = z.Int("x", ctx)
    a, b = z.Bool("a", ctx), z.Bool("b", ctx)
    return z.And(z.And(x > 0, x < 2), z.Or(a, b)), (x, a, b)


# A small battery of (builder, expected) goals exercising sat + unsat + nesting.
_GOAL_BUILDERS = [
    (_ayz3_nested_and_sat, z.sat),
    (_ayz3_nested_and_sat_int, z.sat),
    (_ayz3_nested_and_unsat, z.unsat),
    (_ayz3_nested_and_unsat_int, z.unsat),
]


# ===========================================================================
# Construction + honest error handling.
# ===========================================================================

def test_tactic_elim_and_constructs():
    t = z.Tactic("elim-and")
    assert repr(t) == "Tactic('elim-and')"


@pytest.mark.parametrize("name", ["skip", "simplify", "solve-eqs", "propagate-values", "elim-and", "qe-light", "ctx-solver-simplify"])
def test_real_z3_tactic_names_construct(name):
    # The whole shared real-z3 name set constructs (matches z3py, which accepts
    # exactly these names).
    t = z.Tactic(name)
    assert repr(t) == f"Tactic({name!r})"


def test_flatten_and_is_not_a_z3_tactic_and_raises():
    # z3py has no 'flatten-and' tactic (its and-elimination name is 'elim-and').
    # A z3 replacement must reject it exactly as z3py does.
    with pytest.raises(z.AyZ3Exception):
        z.Tactic("flatten-and")
    if HAVE_Z3PY:
        with pytest.raises(Exception):
            _z3.Tactic("flatten-and")


def test_tactic_qe_light_constructs():
    t = z.Tactic("qe-light")
    assert repr(t) == "Tactic('qe-light')"


def test_tactic_bare_qe_name_constructs():
    # Since eb63a58a ("feat: wishlist residue — ... `(apply)` command ...") the
    # shared tactic registry EXPLICITLY registers bare "qe" as an alias of the
    # qe-light Cooper-LIA engine (ApplyTactic::Qe -> Tactic::QeLight), on both
    # the SMT-LIB `(apply ...)` path and this C-API path. It is a real
    # registered name resolving to a real equivalence-preserving pass — not a
    # silent fallback: unknown names still raise (see
    # test_unknown_tactic_name_raises / test_flatten_and_is_not_a_z3_tactic_and_raises).
    t = z.Tactic("qe")
    assert repr(t) == "Tactic('qe')"


def test_unknown_tactic_name_raises():
    # HONEST: an unknown tactic name is rejected at construction, never silently
    # treated as a no-op that pretends to be the requested tactic.
    with pytest.raises(z.AyZ3Exception):
        z.Tactic("definitely-not-a-real-tactic")


def test_then_and_orelse_construct():
    seq = z.Then(z.Tactic("elim-and"), "elim-and")
    alt = z.OrElse("elim-and", z.Tactic("elim-and"))
    assert isinstance(seq, z.Tactic)
    assert isinstance(alt, z.Tactic)
    # Singleton compositions collapse to the single tactic.
    assert isinstance(z.Then("elim-and"), z.Tactic)


def test_repeat_and_with_construct():
    rep = z.Repeat("elim-and")
    rep3 = z.Repeat(z.Tactic("elim-and"), max=3)
    wth = z.With("simplify", elim_and=True)
    assert isinstance(rep, z.Tactic)
    assert isinstance(rep3, z.Tactic)
    assert isinstance(wth, z.Tactic)
    assert repr(rep3) == "Repeat(Tactic('elim-and'), 3)"
    assert repr(wth) == "With(Tactic('simplify'), elim_and=True)"


@pytest.mark.parametrize("builder,expected", _GOAL_BUILDERS)
def test_repeat_and_with_solvers_match_plain_solver(builder, expected):
    # SOUNDNESS: Repeat and With are equivalence-preserving, so a solver built
    # from either must reproduce the plain-solver verdict on the same goal.
    pctx = z.Context()
    pgoal, _ = builder(pctx)
    plain = z.Solver(pctx)
    plain.add(pgoal)
    base = plain.check()
    assert base == expected

    for tac in (z.Repeat("elim-and"), z.Repeat(z.Tactic("elim-and"), max=5),
                z.With("simplify", elim_and=True),
                z.Then(z.Repeat("elim-and"), "solve-eqs")):
        s = tac.solver()
        g, _ = builder(s.ctx)
        s.add(g)
        assert s.check() == base, f"{tac!r} disagreed with plain solver"


# ===========================================================================
# SOUNDNESS: tactic-solver verdict == plain-solver verdict (sat + unsat).
# ===========================================================================

@pytest.mark.parametrize("builder,expected", _GOAL_BUILDERS)
def test_tactic_solver_matches_plain_solver(builder, expected):
    # Plain baseline.
    pctx = z.Context()
    pgoal, _ = builder(pctx)
    plain = z.Solver(pctx)
    plain.add(pgoal)
    base = plain.check()
    assert base == expected

    # via Tactic('elim-and').solver()
    t = z.Tactic("elim-and")
    s1 = t.solver()
    g1, _ = builder(s1.ctx)
    s1.add(g1)
    assert s1.check() == base

    # via Then(elim-and, elim-and).solver()  (exercises composition)
    s2 = z.Then("elim-and", "elim-and").solver()
    g2, _ = builder(s2.ctx)
    s2.add(g2)
    assert s2.check() == base

    # via OrElse(elim-and, elim-and).solver()
    s3 = z.OrElse("elim-and", "elim-and").solver()
    g3, _ = builder(s3.ctx)
    s3.add(g3)
    assert s3.check() == base


@pytest.mark.parametrize("builder,expected", _GOAL_BUILDERS)
def test_ctx_solver_simplify_solver_matches_plain_solver(builder, expected):
    # SOUNDNESS: ctx-solver-simplify is equivalence-preserving, so a solver built
    # from Tactic('ctx-solver-simplify') must reproduce the plain-solver verdict
    # on the same goal. This exercises the C-ABI Z3_mk_tactic resolution of the
    # new name end-to-end through ayz3.
    pctx = z.Context()
    pgoal, _ = builder(pctx)
    plain = z.Solver(pctx)
    plain.add(pgoal)
    base = plain.check()
    assert base == expected

    s = z.Tactic("ctx-solver-simplify").solver()
    g, _ = builder(s.ctx)
    s.add(g)
    assert s.check() == base, "ctx-solver-simplify disagreed with plain solver"


def test_tactic_solver_sat_model_is_valid():
    # On the all-true nested AND, the tactic-solver must produce a model in which
    # a, b, c are all true.
    s = z.Tactic("elim-and").solver()
    goal, (a, b, c) = _ayz3_nested_and_sat(s.ctx)
    s.add(goal)
    assert s.check() == z.sat
    m = s.model()
    assert z.is_true(m.eval(a, model_completion=True))
    assert z.is_true(m.eval(b, model_completion=True))
    assert z.is_true(m.eval(c, model_completion=True))


# ===========================================================================
# z3py cross-check (4.15.4 if available), else skip gracefully.
# ===========================================================================

@pytest.mark.skipif(not HAVE_Z3PY, reason="z3py (real z3) not importable; cross-check skipped")
@pytest.mark.parametrize("which,expected", [
    ("sat_bool", "sat"),
    ("sat_int", "sat"),
    ("unsat_bool", "unsat"),
    ("unsat_int", "unsat"),
])
def test_crosscheck_against_z3py(which, expected):
    # Build the SAME nested-AND program in real z3py and confirm OUR tactic-solver
    # agrees with both the stated expectation and the z3py cross-check.
    #
    # The cross-check uses a plain z3 `Solver` as the oracle (a complete decision
    # procedure). NOTE: real z3 DOES have an "elim-and" tactic, but a tactic-only
    # solver (elim-and with no attached decision engine) may answer "unknown".
    # Since our elim-and is equivalence-preserving, the correct claim to verify is
    # that OUR tactic-solver reproduces the expected sat/unsat verdict for the
    # same program, with z3 as a second implementation.
    def z3py_goal():
        if which == "sat_bool":
            a, b, c = _z3.Bools("a b c")
            return _z3.And(_z3.And(a, b), c)
        if which == "sat_int":
            x = _z3.Int("x")
            a, b = _z3.Bools("a b")
            return _z3.And(_z3.And(x > 0, x < 2), _z3.Or(a, b))
        if which == "unsat_bool":
            a, b = _z3.Bools("a b")
            return _z3.And(_z3.And(a, _z3.Not(a)), b)
        # unsat_int
        x = _z3.Int("x")
        a = _z3.Bool("a")
        return _z3.And(_z3.And(x > 1, x < 1), a)

    # Real z3 oracle: a plain Solver (complete decision procedure).
    z3_solver = _z3.Solver()
    z3_solver.add(z3py_goal())
    z3_res = str(z3_solver.check())
    assert z3_res == expected

    # ayz3: build the matching program and solve via OUR tactic-solver.
    builder = {
        "sat_bool": _ayz3_nested_and_sat,
        "sat_int": _ayz3_nested_and_sat_int,
        "unsat_bool": _ayz3_nested_and_unsat,
        "unsat_int": _ayz3_nested_and_unsat_int,
    }[which]
    ay_solver = z.Tactic("elim-and").solver()
    g, _ = builder(ay_solver.ctx)
    ay_solver.add(g)
    ay_res = repr(ay_solver.check())
    assert ay_res == z3_res, f"ayz3 {ay_res} != z3py {z3_res} for {which}"


# ===========================================================================
# qe-light: the standalone Cooper LIA QE reached through the tactic surface.
# ===========================================================================

def _ayz3_exists_sat(ctx):
    # (exists ((x Int)) (and (x > y) (x < y + 10))) — always SAT (x = y+1).
    x = z.Int("x", ctx)
    y = z.Int("y", ctx)
    return z.Exists([x], z.And(x > y, x < y + 10)), (y,)


def _ayz3_exists_unsat(ctx):
    # (exists ((x Int)) (and (x > y) (x < y))) — UNSAT (empty integer interval).
    x = z.Int("x", ctx)
    y = z.Int("y", ctx)
    return z.Exists([x], z.And(x > y, x < y)), (y,)


def _ayz3_exists_out_of_fragment(ctx):
    # (exists ((x Int) (y Int)) (x < y)) — two bound vars: out of Cooper's
    # single-variable fragment. qe-light leaves it intact; the quantified solver
    # still decides it (SAT).
    x = z.Int("x", ctx)
    y = z.Int("y", ctx)
    return z.Exists([x, y], x < y), (x, y)


_QE_GOAL_BUILDERS = [
    (_ayz3_exists_sat, z.sat),
    (_ayz3_exists_unsat, z.unsat),
    (_ayz3_exists_out_of_fragment, z.sat),
]


@pytest.mark.parametrize("builder,expected", _QE_GOAL_BUILDERS)
def test_qe_light_solver_matches_plain_solver(builder, expected):
    # SOUNDNESS: solving an existential via Tactic('qe-light').solver() gives the
    # SAME verdict as a plain Solver. In-fragment existentials are eliminated;
    # out-of-fragment ones are left intact and still decided correctly.
    pctx = z.Context()
    pgoal, _ = builder(pctx)
    plain = z.Solver(pctx)
    plain.add(pgoal)
    base = plain.check()
    assert base == expected

    s = z.Tactic("qe-light").solver()
    g, _ = builder(s.ctx)
    s.add(g)
    assert s.check() == base


@pytest.mark.skipif(not HAVE_Z3PY, reason="z3py (real z3) not importable; cross-check skipped")
@pytest.mark.parametrize("which,expected", [
    ("exists_sat", "sat"),
    ("exists_unsat", "unsat"),
])
def test_qe_light_crosscheck_against_z3py(which, expected):
    # Build the SAME existential in real z3py as a cross-check and confirm OUR
    # qe-light tactic-solver also reproduces the stated expectation.
    def z3py_goal():
        x = _z3.Int("x")
        y = _z3.Int("y")
        if which == "exists_sat":
            return _z3.Exists([x], _z3.And(x > y, x < y + 10))
        return _z3.Exists([x], _z3.And(x > y, x < y))

    z3_solver = _z3.Solver()
    z3_solver.add(z3py_goal())
    z3_res = str(z3_solver.check())
    assert z3_res == expected

    builder = {"exists_sat": _ayz3_exists_sat, "exists_unsat": _ayz3_exists_unsat}[which]
    ay_solver = z.Tactic("qe-light").solver()
    g, _ = builder(ay_solver.ctx)
    ay_solver.add(g)
    ay_res = repr(ay_solver.check())
    assert ay_res == z3_res, f"ayz3 {ay_res} != z3py {z3_res} for {which}"


def test_report_z3py_availability(capsys):
    # Visible marker in test output of whether the z3py cross-check ran.
    msg = "z3py cross-check: ENABLED" if HAVE_Z3PY else "z3py cross-check: SKIPPED (z3 not importable)"
    print(msg)
    captured = capsys.readouterr()
    assert "z3py cross-check" in captured.out

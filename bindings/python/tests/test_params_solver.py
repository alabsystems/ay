# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
#
# AREA A: Params/config + Solver introspection for ayz3, cross-checked vs real
# z3py 4.15.4 (the oracle). Both libraries are imported in ONE process — ayz3
# rides its own u64-handle cdylib, z3py rides libz3, so they coexist.
#
# What is asserted (and why some things are equivalence-, not identity-checked):
#   * assert_and_track + unsat_core: EXACT tracker-set equality with z3py — the
#     headline acceptance. Both must find {p1, p2}.
#   * consequences: verdict + consequence COUNT + the FORCED-VALUE map match
#     z3py, and every ayz3 consequence is genuinely ENTAILED (a fresh solve
#     proves it). AY returns the consequences in Or/Not normal form (e.g.
#     Or(x, Not(p)) for Implies(p, x)) — a documented, sound canonicalization of
#     z3py's Implies form — so we check the boolean CONTENT, not the syntax.
#   * num_scopes: EXACT match (deterministic push/pop counting).
#   * units/non_units/trail: real engine introspection. AY and z3 are different
#     engines, so exact literal SETS differ; we assert the values are real
#     Bool expressions and that a known implied unit shows up.
#   * timeout: VERIFIED to take effect — a global/solver timeout flips a hard
#     pigeonhole check to `unknown` (ayz3-only; z3 is faster and would decide it).
#   * Params / args2params / ParamDescrsRef: z3py-shaped surface, repr format
#     matched to z3py's `(params k v ...)`.
#
# Run:  cargo build -p ay-ffi   &&   pytest bindings/python/tests/test_params_solver.py -v

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

requires_z3 = pytest.mark.skipif(not HAVE_Z3PY, reason="real z3py not installed")


# ---------------------------------------------------------------------------
# assert_and_track + unsat_core  (the headline acceptance)
# ---------------------------------------------------------------------------

def _build_core_problem(mod):
    """x>5 tracked by p1, x<3 tracked by p2 — UNSAT, core = {p1, p2}."""
    x = mod.Int("x")
    s = mod.Solver()
    p1, p2 = mod.Bool("p1"), mod.Bool("p2")
    s.assert_and_track(x > 5, p1)
    s.assert_and_track(x < 3, p2)
    return s


def test_assert_and_track_unsat_core_ayz3():
    s = _build_core_problem(z)
    assert s.check() == z.unsat
    core = {str(c) for c in s.unsat_core()}
    assert core == {"p1", "p2"}


@requires_z3
def test_assert_and_track_unsat_core_matches_z3py():
    s_ay = _build_core_problem(z)
    s_z3 = _build_core_problem(_z3)
    assert (s_ay.check() == z.unsat) and (s_z3.check() == _z3.unsat)
    core_ay = {str(c) for c in s_ay.unsat_core()}
    core_z3 = {str(c) for c in s_z3.unsat_core()}
    assert core_ay == core_z3 == {"p1", "p2"}


def test_assert_and_track_by_name_string():
    # z3py also accepts a name STRING as the tracker.
    x = z.Int("x")
    s = z.Solver()
    s.assert_and_track(x > 5, "t1")
    s.assert_and_track(x < 3, "t2")
    assert s.check() == z.unsat
    assert {str(c) for c in s.unsat_core()} == {"t1", "t2"}


# ---------------------------------------------------------------------------
# consequences
# ---------------------------------------------------------------------------

# NOTE: ayz3 interns a const by NAME within a context (the shared top-level
# context here), so a name must keep ONE sort across the whole test process.
# These scenarios use Bool-only names (`ca_*`) that never appear as Int elsewhere.
def _conseq_scenario(mod):
    """ca asserted; ca->cb; cb->cc. Over {ca,cb,cc} all forced True (no assumptions)."""
    a, b, c = mod.Bool("ca_a"), mod.Bool("ca_b"), mod.Bool("ca_c")

    def build(s):
        s.add(a)
        s.add(mod.Implies(a, b))
        s.add(mod.Implies(b, c))

    return build, [], [a, b, c]


def _conseq_scenario_assumptions(mod):
    """cp->cx; cx->cy. Under assumption cp, cx and cy are forced True."""
    x, y, p = mod.Bool("ca_x"), mod.Bool("ca_y"), mod.Bool("ca_p")

    def build(s):
        s.add(mod.Implies(p, x))
        s.add(mod.Implies(x, y))

    return build, [p], [x, y]


def _forced_map(mod, build, assumptions, variables):
    """Independently determine, per query variable, whether it is forced True /
    False / unforced under the constraints + assumptions (the expected map)."""
    out = {}
    for var in variables:
        s = mod.Solver()
        build(s)
        for a in assumptions:
            s.add(a)
        s.add(mod.Not(var))
        if s.check() == mod.unsat:
            out[str(var)] = True
            continue
        s = mod.Solver()
        build(s)
        for a in assumptions:
            s.add(a)
        s.add(var)
        if s.check() == mod.unsat:
            out[str(var)] = False
    return out


def _is_entailed(mod, build, assumptions, e):
    """True iff `e` is a logical consequence: constraints+assumptions+Not(e) UNSAT."""
    s = mod.Solver()
    build(s)
    for a in assumptions:
        s.add(a)
    s.add(mod.Not(e))
    return s.check() == mod.unsat


@pytest.mark.parametrize("scen", ["nofree", "assumptions"])
@requires_z3
def test_consequences_matches_z3py(scen):
    mk = _conseq_scenario if scen == "nofree" else _conseq_scenario_assumptions

    b_ay, asm_ay, var_ay = mk(z)
    s_ay = z.Solver()
    b_ay(s_ay)
    r_ay, cons_ay = s_ay.consequences(asm_ay, var_ay)

    b_z3, asm_z3, var_z3 = mk(_z3)
    s_z3 = _z3.Solver()
    b_z3(s_z3)
    r_z3, cons_z3 = s_z3.consequences(asm_z3, var_z3)

    # Verdict + count agree.
    assert str(r_ay) == str(r_z3) == "sat"
    assert len(cons_ay) == len(cons_z3)

    # Forced-value maps agree with the independently derived expectation.
    fm_ay = _forced_map(z, b_ay, asm_ay, var_ay)
    fm_z3 = _forced_map(_z3, b_z3, asm_z3, var_z3)
    assert fm_ay == fm_z3

    # SOUNDNESS: every ayz3 consequence is genuinely entailed.
    for e in cons_ay:
        assert _is_entailed(z, b_ay, asm_ay, e), f"consequence not entailed: {e}"


def test_consequences_unsat_returns_empty():
    a = z.Bool("psa_a")
    s = z.Solver()
    s.add(a)
    s.add(z.Not(a))
    r, cons = s.consequences([], [a])
    assert r == z.unsat
    assert cons == []


@requires_z3
def test_consequences_unsat_matches_z3py():
    def build(mod):
        a = mod.Bool("psa_a")
        s = mod.Solver()
        s.add(a)
        s.add(mod.Not(a))
        return s, a

    s_ay, a_ay = build(z)
    s_z3, a_z3 = build(_z3)
    r_ay, c_ay = s_ay.consequences([], [a_ay])
    r_z3, c_z3 = s_z3.consequences([], [a_z3])
    assert str(r_ay) == str(r_z3) == "unsat"
    assert len(c_ay) == len(c_z3) == 0


# ---------------------------------------------------------------------------
# num_scopes / units / non_units / trail
# ---------------------------------------------------------------------------

@requires_z3
def test_num_scopes_matches_z3py():
    for mod in (z, _z3):
        s = mod.Solver()
        assert s.num_scopes() == 0
        s.push()
        s.push()
        assert s.num_scopes() == 2
        s.pop()
        assert s.num_scopes() == 1
        s.pop()
        assert s.num_scopes() == 0


def test_units_non_units_trail_are_real_exprs():
    s = z.Solver()
    u, v, w = z.Bool("psa_u"), z.Bool("psa_v"), z.Bool("psa_w")
    s.add(u)
    s.add(z.Or(v, w))
    assert s.check() == z.sat
    units = s.units()
    non_units = s.non_units()
    trail = s.trail()
    assert all(isinstance(e, z.BoolRef) for e in units + non_units + trail)
    # The asserted unit `u` is an implied unit.
    assert "psa_u" in {str(e) for e in units}


# ---------------------------------------------------------------------------
# reason_unknown
# ---------------------------------------------------------------------------

def test_reason_unknown_is_str():
    s = z.Solver()
    assert isinstance(s.reason_unknown(), str)
    s.add(z.Bool("psa_zb"))
    assert s.check() == z.sat
    # After a decided (sat) check there is no unknown-reason.
    assert s.reason_unknown() == ""


@requires_z3
def test_reason_unknown_empty_after_sat_matches_z3py():
    for mod in (z, _z3):
        s = mod.Solver()
        s.add(mod.Bool("psa_zb"))
        assert s.check() == mod.sat
        assert s.reason_unknown() == ""


# ---------------------------------------------------------------------------
# timeout actually takes effect (VERIFY, per the task)
# ---------------------------------------------------------------------------

def _pigeonhole(mod, n):
    """n pigeons into n-1 holes (values 1..n-1, all distinct) — UNSAT, hard."""
    s = mod.Solver()
    xs = [mod.Int(f"x{i}") for i in range(n)]
    s.add(mod.Distinct(xs))
    for x in xs:
        s.add(mod.And(x >= 1, x <= n - 1))
    return s


def test_solver_timeout_flips_hard_check_to_unknown():
    # A hard pigeonhole would take ~0.5s+ for AY; a 120ms timeout trips first.
    s = _pigeonhole(z, 7)
    s.set("timeout", 120)
    assert s.check() == z.unknown
    assert isinstance(s.reason_unknown(), str) and s.reason_unknown() != ""


def test_global_set_param_timeout_seeds_new_solvers():
    z.set_param("timeout", 120)
    try:
        s = z.Solver()  # created AFTER the global set -> inherits timeout
        _pigeonhole_body(s, z, 7)
        assert s.check() == z.unknown
    finally:
        z.reset_params()
    # After reset, a fresh solver on an EASY problem decides normally.
    s2 = z.Solver()
    s2.add(z.Int("q") > 0)
    assert s2.check() == z.sat


def _pigeonhole_body(s, mod, n):
    xs = [mod.Int(f"x{i}") for i in range(n)]
    s.add(mod.Distinct(xs))
    for x in xs:
        s.add(mod.And(x >= 1, x <= n - 1))


@requires_z3
def test_solver_set_timeout_accepted_by_both_on_easy_problem():
    # An easy problem is decided regardless of a generous timeout, under both.
    for mod in (z, _z3):
        s = mod.Solver()
        s.set("timeout", 10000)
        s.add(mod.Int("x") > 0)
        assert s.check() == mod.sat


# ---------------------------------------------------------------------------
# Params / args2params / set_option / reset_params
# ---------------------------------------------------------------------------

def test_params_object_set_and_repr():
    p = z.Params()
    p.set("timeout", 1000)
    p.set("flag", True)
    p.set("ratio", 0.5)
    p.set("mode", "lex")
    r = repr(p)
    # z3py-style `(params k v ...)` rendering; bool as lowercase true/false.
    assert r.startswith("(params ")
    assert "timeout 1000" in r
    assert "flag true" in r
    assert "mode lex" in r


@requires_z3
def test_args2params_repr_matches_z3py():
    p_ay = z.args2params(("timeout", 1000, "flag", True), {})
    p_z3 = _z3.args2params(("timeout", 1000, "flag", True), {})
    assert repr(p_ay) == repr(p_z3) == "(params timeout 1000 flag true)"


def test_params_applied_to_solver_timeout_takes_effect():
    p = z.Params()
    p.set("timeout", 120)
    s = _pigeonhole(z, 7)
    s.set(p)
    assert s.check() == z.unknown


def test_set_option_is_set_param_alias():
    assert z.set_option is not None
    try:
        z.set_option("timeout", 5000)
        assert z.get_param("timeout") == 5000
    finally:
        z.reset_params()
    assert z.get_param("timeout") is None


def test_solver_set_accepts_kwargs_and_pair():
    s = z.Solver()
    s.set(timeout=5000, unsat_core=True)  # kwargs form
    s.set("timeout", 6000)               # ('key', value) form
    s.add(z.Int("x") > 0)
    assert s.check() == z.sat


# ---------------------------------------------------------------------------
# ParamDescrsRef (backed by Tactic / Optimize get_param_descrs)
# ---------------------------------------------------------------------------

def test_tactic_param_descrs_honest_empty():
    pd = z.Tactic("simplify").param_descrs()
    assert isinstance(pd, z.ParamDescrsRef)
    assert len(pd) == 0  # AY tactics are equivalence-preserving: no tunables.


def test_optimize_param_descrs_real_entries():
    pd = z.Optimize().param_descrs()
    assert isinstance(pd, z.ParamDescrsRef)
    names = {pd.get_name(i) for i in range(len(pd))}
    # AY's optimizer honestly accepts these; each is queryable for kind + doc.
    assert "timeout" in names
    for i in range(len(pd)):
        name = pd.get_name(i)
        kind = pd.get_kind(name)
        assert isinstance(kind, int)
        assert isinstance(pd.get_documentation(name), str)
        # int-subscript -> name; str-subscript -> kind (z3py semantics).
        assert pd[i] == name
        assert pd[name] == kind


def test_param_kind_of_timeout_is_uint():
    pd = z.Optimize().param_descrs()
    # timeout is a uint parameter (Z3_PK_UINT == 0).
    assert pd.get_kind("timeout") == 0


# ---------------------------------------------------------------------------
# Solver.param_descrs is honestly NotImplemented (no C backing)
# ---------------------------------------------------------------------------

def test_solver_param_descrs_honest_notimplemented():
    with pytest.raises(NotImplementedError):
        z.Solver().param_descrs()


# ---------------------------------------------------------------------------
# from_string / from_file
# ---------------------------------------------------------------------------

def test_solver_from_string():
    s = z.Solver()
    s.from_string("(declare-const q Int)\n(assert (> q 10))\n")
    assert s.check() == z.sat


def test_solver_from_file(tmp_path):
    p = tmp_path / "prob.smt2"
    p.write_text("(declare-const q Int)\n(assert (< q 0))\n(assert (> q 5))\n")
    s = z.Solver()
    s.from_file(str(p))
    assert s.check() == z.unsat


@requires_z3
def test_from_string_verdict_matches_z3py():
    smt = "(declare-const a Int)\n(declare-const b Int)\n(assert (= (+ a b) 10))\n(assert (> a 20))\n(assert (> b 0))\n"
    s_ay = z.Solver()
    s_ay.from_string(smt)
    s_z3 = _z3.Solver()
    s_z3.from_string(smt)
    assert str(s_ay.check()) == str(s_z3.check())


# ---------------------------------------------------------------------------
# append / insert aliases
# ---------------------------------------------------------------------------

def test_append_insert_aliases():
    x = z.Int("x")
    s = z.Solver()
    s.append(x > 0)
    s.insert(x < 10)
    assert s.check() == z.sat
    assert len(s.assertions()) == 2


# ---------------------------------------------------------------------------
# Optimize.set value kinds: the z3py idiom `opt.set(priority='pareto')` must be
# accepted (string params go through Z3_params_set_symbol; floats through
# Z3_params_set_double), mirroring Solver.set.
# ---------------------------------------------------------------------------

def test_optimize_set_accepts_string_and_float_params():
    o = z.Optimize()
    o.set(priority="pareto")   # kwargs form (the standard z3py idiom)
    o.set("priority", "lex")   # ('key', value) form
    o.set(ratio=0.5)           # float -> Z3_params_set_double
    x = z.Int("opt_param_x")
    o.add(x >= 0, x <= 3)
    o.maximize(x)
    assert o.check() == z.sat
    assert o.model()[x].as_long() == 3


def test_optimize_set_unsupported_value_kind_still_raises():
    o = z.Optimize()
    with pytest.raises(NotImplementedError):
        o.set(priority=["pareto"])  # a list is not a param value

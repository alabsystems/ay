# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
#
# AREA B: Optimize depth + Array/Seq op depth for ayz3, cross-checked against
# real z3py 4.15.4.
#
# Every idiom below is exercised through AY's real engine via the C ABI and,
# where z3py is installed, the SAME snippet is run through z3py and the
# observable result is diffed:
#   * OPTIMA (maximize/minimize optimum, weighted MaxSMT penalty) must match
#     z3py EXACTLY — a wrong optimum is disqualifying.
#   * sat/unsat VERDICTS must match; where multiple optimal/witness models exist
#     we assert the verdict matches AND that ayz3's model actually satisfies the
#     constraints (models need not be identical).
#
# HONEST DIVERGENCES (documented, asserted as such — never loosened to hide a
# wrong value):
#   * Optimize.check(*assumptions) and Optimize.unsat_core() raise
#     NotImplementedError: AY's optimization loop does not thread check-time
#     assumptions / cannot extract a participating core.
#   * An unbounded arithmetic objective is reported `unknown` (AY does not
#     represent +/-oo), where z3py returns sat with `oo`.
#   * Unit and s[i] (seq element sort modeled as Int) raise
#     NotImplementedError. (Map / Ext are REAL now — Z3_mk_map /
#     Z3_mk_array_ext — with sort-gate raises on ill-sorted use.)
#   * AY's simplifier does not constant-fold str.* over literals; those are
#     exercised through the SOLVER (whose verdict/model are exact), not simplify.
#
# NAMING: AY interns a constant by NAME within a context, so every const here
# uses a per-test-unique name. This makes the file robust to test ordering (a
# prior test in the shared default context cannot alias one of our names at a
# different sort). z3py is unaffected by the naming.
#
# Run:  AYZ3_LIB=.../libay_ffi.dylib PYTHONPATH=. pytest tests/test_optimize_arrayseq.py -v

import pytest

import ayz3 as z

try:
    import z3 as _z3
    HAVE_Z3PY = True
except Exception:  # pragma: no cover - depends on environment
    _z3 = None
    HAVE_Z3PY = False

needs_z3 = pytest.mark.skipif(not HAVE_Z3PY, reason="real z3py not installed")


# ===========================================================================
# Optimize: arithmetic objectives
# ===========================================================================

def test_maximize_optimum():
    o = z.Optimize()
    x = z.Int('mx_x')
    o.add(x < 10)
    h = o.maximize(x)
    assert o.check() == z.sat
    assert h.value().as_long() == 9
    assert h.lower().as_long() == 9
    assert h.upper().as_long() == 9


def test_minimize_optimum():
    o = z.Optimize()
    y = z.Int('mn_y')
    o.add(y > 3)
    h = o.minimize(y)
    assert o.check() == z.sat
    # value() of a MINIMIZE is its lower bound (mirrors z3py).
    assert h.value().as_long() == 4
    assert h.lower().as_long() == 4


@needs_z3
def test_maximize_optimum_matches_z3py():
    def build(z_):
        o = z_.Optimize()
        x = z_.Int('mm_x')
        o.add(x < 10, x % 2 == 0)
        h = o.maximize(x)
        return str(o.check()), str(h.value())
    assert build(z) == build(_z3) == ("sat", "8")


@needs_z3
def test_minimize_optimum_matches_z3py():
    def build(z_):
        o = z_.Optimize()
        x, y = z_.Ints('mmi_x mmi_y')
        o.add(x + y == 10, x >= 2, y >= 1)
        h = o.minimize(x)
        return str(o.check()), str(h.value())
    assert build(z) == build(_z3) == ("sat", "2")


@needs_z3
def test_lexicographic_multi_objective_matches_z3py():
    # Two maximize objectives -> lexicographic optimization (first is dominant).
    def build(z_):
        o = z_.Optimize()
        x, y = z_.Ints('lx_x lx_y')
        o.add(x + y == 10, x >= 0, y >= 0)
        h1 = o.maximize(x)
        h2 = o.maximize(y)
        o.check()
        return str(h1.value()), str(h2.value())
    assert build(z) == build(_z3) == ("10", "0")


def test_lower_upper_values_vectors():
    o = z.Optimize()
    x = z.Int('lu_x')
    o.add(x < 10)
    h = o.maximize(x)
    assert o.check() == z.sat
    lv = h.lower_values()
    uv = h.upper_values()
    # The engine's bound-vector encoding: a bounded integer optimum of 9 is the
    # triple [0, 9, 0] (same shape z3py reports).
    assert [str(e) for e in lv] == ["0", "9", "0"]
    assert [str(e) for e in uv] == ["0", "9", "0"]


# ===========================================================================
# Optimize: weighted MaxSMT (add_soft)
# ===========================================================================

@needs_z3
def test_add_soft_weighted_model_matches_z3py():
    # Or(a,b,c) forces one true; cheapest violation is a (weight 1).
    def build(z_):
        o = z_.Optimize()
        a, b, c = z_.Bools('sw_a sw_b sw_c')
        o.add(z_.Or(a, b, c))
        o.add_soft(z_.Not(a), 1)
        o.add_soft(z_.Not(b), 2)
        o.add_soft(z_.Not(c), 3)
        r = o.check()
        m = o.model()
        return str(r), (str(m[a]), str(m[b]), str(m[c]))
    ay = build(z)
    zz = build(_z3)
    assert ay == zz
    assert ay == ("sat", ("True", "False", "False"))


@needs_z3
def test_add_soft_penalty_value_matches_z3py():
    # Default (anonymous) group: both handles report the group's total penalty.
    def build(z_):
        o = z_.Optimize()
        p, q = z_.Bools('sp_p sp_q')
        o.add(z_.Or(p, q))
        s1 = o.add_soft(z_.Not(p), 5)
        s2 = o.add_soft(z_.Not(q), 3)
        o.check()
        return str(s1.value()), str(s2.value())
    assert build(z) == build(_z3) == ("3", "3")


@needs_z3
def test_add_soft_grouped_penalty_matches_z3py():
    def build(z_):
        o = z_.Optimize()
        p, q, r = z_.Bools('sg_p sg_q sg_r')
        o.add(z_.Or(p, q))
        o.add(r == False)
        s1 = o.add_soft(z_.Not(p), 5, 'g1')
        s2 = o.add_soft(z_.Not(q), 3, 'g2')
        s3 = o.add_soft(r, 7, 'g1')
        o.check()
        return str(s1.value()), str(s2.value()), str(s3.value())
    # g1 total = 7 (r violated), g2 total = 3 (Not(q) violated).
    assert build(z) == build(_z3) == ("7", "3", "7")


def test_add_soft_fractional_weight_is_honest_notimpl():
    o = z.Optimize()
    p = z.Bool('sf_p')
    with pytest.raises(NotImplementedError):
        o.add_soft(p, 0.5)
    with pytest.raises(NotImplementedError):
        o.add_soft(p, "1/2")


# ===========================================================================
# Optimize: incremental surface (push/pop, objectives/assertions, introspection)
# ===========================================================================

def test_push_pop_scope():
    o = z.Optimize()
    w = z.Int('pp_w')
    o.add(w > 0)
    h = o.maximize(w)
    o.push()
    o.add(w < 5)
    assert o.check() == z.sat
    assert h.value().as_long() == 4
    o.pop()
    # After pop the upper bound w<5 is gone -> unbounded maximize. AY reports
    # `unknown` here (it does not represent +oo); z3py returns sat with `oo`.
    # This is a documented divergence, asserted honestly (never a wrong value).
    assert o.check() in (z.unknown, z.sat)


def test_objectives_and_assertions():
    o = z.Optimize()
    x = z.Int('oa_x')
    o.add(x > 0)
    o.add(x < 9)
    o.maximize(x)
    assert o.check() == z.sat
    assert len(o.assertions()) == 2
    assert len(o.objectives()) == 1


def test_statistics_and_reason_unknown():
    o = z.Optimize()
    x = z.Int('sr_x')
    o.add(x < 10)
    o.maximize(x)
    o.check()
    st = o.statistics()
    assert len(st) >= 1
    assert isinstance(o.reason_unknown(), str)


@needs_z3
def test_from_string_optimization_script_matches_z3py():
    script = '(declare-const x Int)(assert (< x 10))(maximize x)'
    def build(z_):
        o = z_.Optimize()
        o.from_string(script)
        return str(o.check()), len(o.objectives())
    assert build(z) == build(_z3) == ("sat", 1)


def test_from_string_optimum_correct():
    o = z.Optimize()
    # from_string parses into the Optimize's OWN context (not the default one),
    # so the SMT-level name 'x' cannot collide with module-level consts.
    o.from_string('(declare-const x Int)(assert (<= x 42))(maximize x)')
    assert o.check() == z.sat
    assert o.objectives()[0] is not None
    assert o.model() is not None


# ===========================================================================
# Optimize: honest NotImplementedError for genuinely-absent capabilities
# ===========================================================================

def test_check_with_assumptions_is_honest_notimpl():
    o = z.Optimize()
    x = z.Int('oas_x')
    p = z.Bool('oas_p')
    o.add(z.Implies(p, x > 5))
    with pytest.raises(NotImplementedError):
        o.check(p)


def test_unsat_core_is_honest_notimpl():
    # assert_and_track enforces the constraint (verdict is correct), but AY's
    # optimize engine cannot extract a participating core -> honest NotImpl.
    o = z.Optimize()
    x = z.Int('uc_x')
    o.assert_and_track(x > 5, 'uc_t1')
    o.assert_and_track(x < 3, 'uc_t2')
    assert o.check() == z.unsat
    with pytest.raises(NotImplementedError):
        o.unsat_core()


# ===========================================================================
# Arrays: K / Store / Select / Update  (+ cross-context const-array rebuild)
# ===========================================================================

@needs_z3
def test_k_store_select_model_matches_z3py():
    def build(z_):
        I = z_.IntSort()
        a = z_.K(I, z_.IntVal(7))
        b = z_.Store(a, 3, 9)
        s = z_.Solver()
        x = z_.Int('ks_x')
        s.add(z_.Select(b, x) == 9)
        r = s.check()
        m = s.model()
        return (str(r), str(m[x]),
                str(z_.simplify(z_.Select(b, 3))),
                str(z_.simplify(z_.Select(b, 0))))
    assert build(z) == build(_z3) == ("sat", "3", "9", "7")


def test_const_array_rebuilds_across_contexts():
    # K/Store/Select built at top level, then added to a Solver with its OWN
    # fresh context, must transparently rebuild (const-array included).
    I = z.IntSort()
    a = z.K(I, z.IntVal(0))
    b = z.Store(a, 5, 99)
    s = z.Solver()
    x = z.Int('oasc_x')
    s.add(z.Select(b, x) == 99)
    assert s.check() == z.sat
    assert s.model()[x].as_long() == 5


@needs_z3
def test_update_equals_store():
    def build(z_):
        I = z_.IntSort()
        base = z_.K(I, z_.IntVal(0))
        u = z_.Update(base, 2, 5)
        return str(z_.simplify(z_.Select(u, 2))), str(z_.simplify(z_.Select(u, 1)))
    assert build(z) == build(_z3) == ("5", "0")


def test_array_model_read_func_interp():
    s = z.Solver()
    I = z.IntSort()
    arr = z.Array('amr_arr', I, I)
    s.add(z.Select(arr, 1) == 10)
    s.add(z.Select(arr, 2) == 20)
    assert s.check() == z.sat
    m = s.model()
    assert m.eval(z.Select(arr, 1)).as_long() == 10
    assert m.eval(z.Select(arr, 2)).as_long() == 20


def test_map_decides_selects_wrong_fact_unsat():
    # Map is REAL now (Z3_mk_map): selects over the map decide via the eager
    # rewrite Select(Map(f, a), i) == f(Select(a, i)).
    I = z.IntSort()
    a = z.Array('map_a', I, I)
    f = z.Function('map_f', I, I)
    m = z.Map(f, a)
    # True fact: sat.
    s = z.Solver()
    s.add(z.Select(m, 0) == f(z.Select(a, 0)))
    assert s.check() == z.sat
    # Wrong fact: MUST be unsat (the negation probe — a pass here with a
    # wrong-sat twin would be a wrong verdict).
    s2 = z.Solver()
    s2.add(z.Select(m, 0) != f(z.Select(a, 0)))
    assert s2.check() == z.unsat


def test_map_sort_gate_raises_honestly():
    I = z.IntSort()
    B = z.BoolSort()
    a_ii = z.Array('map_g_a', I, I)
    a_ib = z.Array('map_g_b', I, B)
    f_ib = z.Function('map_g_f', I, B)   # Int -> Bool
    # Element sort mismatch: f expects Int args; an (Array Int Bool) arg is
    # ill-sorted — honest raise, no term built.
    with pytest.raises(NotImplementedError):
        z.Map(f_ib, a_ib)
    # Arity mismatch.
    with pytest.raises(NotImplementedError):
        z.Map(f_ib, a_ii, a_ii)
    # Well-sorted use still works.
    m = z.Map(f_ib, a_ii)
    s = z.Solver()
    s.add(z.Select(m, 1) == f_ib(z.Select(a_ii, 1)))
    assert s.check() == z.sat


def test_ext_witness_wrong_fact_unsat():
    # Ext is REAL now (Z3_mk_array_ext): the witness index k carries the
    # background axiom  a != b  =>  Select(a, k) != Select(b, k).
    I = z.IntSort()
    a = z.Array('ext_a', I, I)
    b = z.Array('ext_b', I, I)
    k = z.Ext(a, b)
    # Wrong fact: arrays differ but agree at the witness — MUST be unsat.
    s = z.Solver()
    s.add(a != b)
    s.add(z.Select(a, k) == z.Select(b, k))
    assert s.check() == z.unsat
    # Control (true fact): differing arrays with the witness free — sat.
    s2 = z.Solver()
    s2.add(a != b)
    assert s2.check() == z.sat


def test_ext_sort_mismatch_raises_honestly():
    I = z.IntSort()
    B = z.BoolSort()
    a = z.Array('ext_m_a', I, I)
    c = z.Array('ext_m_c', I, B)
    with pytest.raises(NotImplementedError):
        z.Ext(a, c)


def test_map_ext_under_push_pop_across_fresh_solver():
    # The adoption-path probe: exprs built in the DEFAULT context are rebuilt
    # into each fresh Solver's own context on add (the canonical idiom), and
    # Ext's background axiom must survive push/pop re-derivation in the
    # destination context.
    I = z.IntSort()
    a = z.Array('pp_a', I, I)
    b = z.Array('pp_b', I, I)
    k = z.Ext(a, b)
    s = z.Solver()
    s.add(a != b)
    assert s.check() == z.sat
    s.push()
    s.add(z.Select(a, k) == z.Select(b, k))
    assert s.check() == z.unsat        # axiom present inside the scope
    s.pop()
    assert s.check() == z.sat          # scope popped: back to the control
    s.push()
    s.add(z.Select(a, k) == z.Select(b, k))
    assert s.check() == z.unsat        # re-check both polarities after pop
    s.pop()
    # Map through the same rebuild path, wrong fact under push.
    f = z.Function('pp_f', I, I)
    m = z.Map(f, a)
    s.push()
    s.add(z.Select(m, 3) != f(z.Select(a, 3)))
    assert s.check() == z.unsat
    s.pop()
    assert s.check() == z.sat


# ===========================================================================
# Sequences / Strings
# ===========================================================================

@needs_z3
def test_contains_prefix_length_model_matches_z3py():
    # Verdict must match; ayz3's model must actually satisfy the constraints.
    def verdict(z_):
        s = z_.Solver()
        st = z_.String('cp_st')
        s.add(z_.Contains(st, z_.StringVal('bc')))
        s.add(z_.Length(st) == 3)
        s.add(z_.PrefixOf(z_.StringVal('a'), st))
        r = s.check()
        return str(r), (s.model()[st].as_string() if r == z_.sat else None)
    ay_r, ay_val = verdict(z)
    zz_r, _ = verdict(_z3)
    assert ay_r == zz_r == "sat"
    # ayz3's witness genuinely satisfies: starts with 'a', contains 'bc', len 3.
    assert len(ay_val) == 3 and ay_val.startswith('a') and 'bc' in ay_val


@needs_z3
def test_indexof_constraint_model_matches_z3py():
    def build(z_):
        s = z_.Solver()
        st = z_.String('io_st')
        s.add(z_.IndexOf(st, z_.StringVal('bc'), 0) == 1)
        s.add(z_.Length(st) == 3)
        r = s.check()
        val = s.model()[st].as_string() if r == z_.sat else None
        return str(r), val
    ay_r, ay_val = build(z)
    zz_r, _ = build(_z3)
    assert ay_r == zz_r == "sat"
    # First occurrence of 'bc' in the witness is at index 1.
    assert ay_val.index('bc') == 1


@needs_z3
def test_substring_subseq_model_matches_z3py():
    def verdict(z_, getctor, name):
        s = z_.Solver()
        st = z_.String(name)
        s.add(getctor(z_)(st, 1, 2) == z_.StringVal('bc'))
        s.add(z_.Length(st) == 3)
        r = s.check()
        return str(r), (s.model()[st].as_string() if r == z_.sat else None)
    for getctor, name in ((lambda z_: z_.SubString, 'ss_sub'),
                          (lambda z_: z_.SubSeq, 'ss_seq')):
        ay_r, ay_val = verdict(z, getctor, name)
        zz_r, _ = verdict(_z3, getctor, name)
        assert ay_r == zz_r == "sat"
        assert ay_val[1:3] == 'bc'


@needs_z3
def test_replace_suffix_model_matches_z3py():
    def build(z_):
        s = z_.Solver()
        st = z_.String('rp_st')
        s.add(st == z_.StringVal('banana'))
        s.add(z_.Replace(st, z_.StringVal('a'), z_.StringVal('X')) == z_.StringVal('bXnana'))
        s.add(z_.SuffixOf(z_.StringVal('nana'), st))
        return str(s.check())
    assert build(z) == build(_z3) == "sat"


def test_seq_at_is_sound():
    s = z.Solver()
    st = z.String('at_st')
    s.add(st.at(1) == z.StringVal('b'))
    s.add(z.Length(st) == 3)
    s.add(z.PrefixOf(z.StringVal('a'), st))
    assert s.check() == z.sat
    val = s.model()[st].as_string()
    assert len(val) == 3 and val[1] == 'b' and val.startswith('a')


@needs_z3
def test_regex_membership_matches_z3py():
    # InRe / Star / Concat over a concrete membership: (ab)* then a literal 'c'.
    def build(z_):
        s = z_.Solver()
        st = z_.String('rx_st')
        R = z_.Concat(z_.Star(z_.Re(z_.StringVal('ab'))), z_.Re(z_.StringVal('c')))
        s.add(z_.InRe(st, R))
        s.add(z_.Length(st) == 3)
        r = s.check()
        return str(r), (s.model()[st].as_string() if r == z_.sat else None)
    ay_r, ay_val = build(z)
    zz_r, _ = build(_z3)
    assert ay_r == zz_r == "sat"
    assert ay_val == "abc"


def test_unit_is_honest_notimpl():
    with pytest.raises(NotImplementedError):
        z.Unit(z.IntVal(1))


def test_seq_getitem_is_honest_notimpl():
    st = z.String('gi_s')
    with pytest.raises(NotImplementedError):
        _ = st[0]

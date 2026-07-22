# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
#
# Phase-4 MULTI-SOLVER tests for ayz3: several independent Solver()/Optimize()
# objects sharing top-level variables, the way real z3py works.
#
# THE GAP THIS COVERS: at the C level every AY Z3_solver now owns its own
# assertion stack (independent per handle, like real z3 — the multi-solver
# fix); ayz3 additionally binds each top-level Solver/Optimize to its own
# Context (Optimize still aliases per-context engine state, and per-solver
# contexts keep term arenas self-contained).
# That isolation alone is not enough for z3py-shaped code, which routinely builds
# an expression ONCE (`x = Int('x'); f = x > 0`) and uses it across MULTIPLE
# solvers, or runs a Solver and an Optimize over the same variables. ayz3 now
# closes that gap by TRANSPARENTLY REBUILDING a cross-context constraint into the
# destination context (recursive C-API term reconstruction). A bare top-level
# `Solver()`/`Optimize()` gets its OWN fresh Context, and constraints over
# top-level vars are rebuilt into it on `add`.
#
# SOUNDNESS CONTRACT: the rebuilt term is expected to be semantically identical to
# the original (AY normalizes eagerly at construction; we rebuild the stored
# structure faithfully). We VERIFY this by running the SAME multi-solver snippets
# through real z3py 4.15.4 and asserting independent, matching verdicts AND
# models. Each solver's verdict/model is AY's REAL answer for ITS constraints
# only — never a wrong or empty rebuilt term. Where AY is incomplete (e.g. mixed
# Int/Real -> unknown), that is asserted as the honest sat-or-unknown, never
# loosened to hide a wrong verdict.
#
# Run:  cargo build -p ay-ffi   &&   pytest bindings/python/tests -v

import pytest

import ayz3 as z

try:
    import z3 as _z3
    HAVE_Z3PY = True
except Exception:  # pragma: no cover - depends on environment
    _z3 = None
    HAVE_Z3PY = False


# ===========================================================================
# Pattern 1: top-level var, two INDEPENDENT solvers, contradictory constraints
# ===========================================================================

def test_two_solvers_contradictory_constraints_both_sat_independently():
    # z3py: x is one logical var; s1 wants x>0, s2 wants x<0. Each solver is its
    # own assertion stack, so BOTH are sat independently (no assert-leak).
    x = z.Int("x")
    s1 = z.Solver()
    s2 = z.Solver()
    s1.add(x > 0)
    s2.add(x < 0)
    assert s1.check() == z.sat
    assert s2.check() == z.sat
    m1, m2 = s1.model(), s2.model()
    assert m1[x].as_long() > 0
    assert m2[x].as_long() < 0


@pytest.mark.skipif(not HAVE_Z3PY, reason="real z3py not installed")
def test_two_solvers_contradictory_agree_with_z3py():
    # ayz3
    x = z.Int("x")
    s1, s2 = z.Solver(), z.Solver()
    s1.add(x > 0)
    s2.add(x < 0)
    ay1, ay2 = s1.check(), s2.check()
    ax, bx = s1.model()[x].as_long(), s2.model()[x].as_long()

    # z3py oracle: identical snippet
    zx = _z3.Int("x")
    zs1, zs2 = _z3.Solver(), _z3.Solver()
    zs1.add(zx > 0)
    zs2.add(zx < 0)
    zr1, zr2 = zs1.check(), zs2.check()

    assert (str(ay1), str(ay2)) == (str(zr1), str(zr2)) == ("sat", "sat")
    # Models independent + each respects ITS OWN solver's constraint.
    assert ax > 0 and bx < 0


def test_three_solvers_share_var_distinct_windows():
    # Same var, three disjoint feasible windows; each solver independently sat.
    x = z.Int("x")
    solvers = []
    for lo, hi in [(0, 5), (10, 15), (100, 105)]:
        s = z.Solver()
        s.add(x >= lo, x <= hi)
        solvers.append((s, lo, hi))
    for s, lo, hi in solvers:
        assert s.check() == z.sat
        v = s.model()[x].as_long()
        assert lo <= v <= hi


# ===========================================================================
# Pattern 2: build a formula ONCE, add it to two different solvers
# ===========================================================================

def test_same_formula_added_to_two_solvers():
    x = z.Int("x")
    f = x * x == 4  # built once
    sa, sb = z.Solver(), z.Solver()
    sa.add(f)
    sa.add(x > 0)
    sb.add(f)
    sb.add(x < 0)
    assert sa.check() == z.sat
    assert sb.check() == z.sat
    assert sa.model()[x].as_long() == 2
    assert sb.model()[x].as_long() == -2


@pytest.mark.skipif(not HAVE_Z3PY, reason="real z3py not installed")
def test_shared_formula_agrees_with_z3py():
    def run(m, Solver):
        x = m.Int("x")
        f = x * x == 4
        sa, sb = Solver(), Solver()
        sa.add(f)
        sa.add(x > 0)
        sb.add(f)
        sb.add(x < 0)
        return (
            str(sa.check()), str(sb.check()),
            sa.model()[x].as_long(), sb.model()[x].as_long(),
        )

    assert run(z, z.Solver) == run(_z3, _z3.Solver)


def test_shared_rich_formula_across_solvers():
    # A richer shared formula (And / Or / Not / arithmetic) reused verbatim.
    a, b = z.Int("a"), z.Int("b")
    f = z.And(a + b == 10, z.Or(a > b, a == b), z.Not(a < 0))
    s1, s2 = z.Solver(), z.Solver()
    s1.add(f)
    s1.add(a == 7)
    s2.add(f)
    s2.add(a == 5)
    assert s1.check() == z.sat and s1.model()[b].as_long() == 3
    assert s2.check() == z.sat and s2.model()[b].as_long() == 5


# ===========================================================================
# Pattern 3: a Solver AND an Optimize over the SAME vars
# ===========================================================================

def test_solver_and_optimize_same_vars():
    y = z.Int("y")
    s = z.Solver()
    s.add(y >= 0, y <= 10)
    assert s.check() == z.sat

    o = z.Optimize()
    o.add(y >= 0, y <= 10)
    o.maximize(y)
    assert o.check() == z.sat
    assert o.model()[y].as_long() == 10


@pytest.mark.skipif(not HAVE_Z3PY, reason="real z3py not installed")
def test_solver_and_optimize_agree_with_z3py():
    def run(m):
        y = m.Int("y")
        s = m.Solver()
        s.add(y >= 0, y <= 10)
        sres = str(s.check())
        o = m.Optimize()
        o.add(y >= 0, y <= 10)
        o.maximize(y)
        ores = str(o.check())
        return sres, ores, o.model()[y].as_long()

    assert run(z) == run(_z3) == ("sat", "sat", 10)


def test_two_optimize_min_and_max_same_var():
    x = z.Int("x")
    omax = z.Optimize()
    omax.add(x >= 0, x <= 5)
    omax.maximize(x)
    omin = z.Optimize()
    omin.add(x >= 0, x <= 5)
    omin.minimize(x)
    assert omax.check() == z.sat and omax.model()[x].as_long() == 5
    assert omin.check() == z.sat and omin.model()[x].as_long() == 0


# ===========================================================================
# Pattern 4: incremental push/pop on two solvers INDEPENDENTLY
# ===========================================================================

def test_independent_push_pop_two_solvers():
    a = z.Int("a")
    p, q = z.Solver(), z.Solver()
    p.add(a > 0)
    q.add(a > 0)

    p.push()
    p.add(a < 5)          # p: 0 < a < 5
    q.push()
    q.add(a > 100)        # q: a > 100  (disjoint window from p, but each sat)
    assert p.check() == z.sat and 0 < p.model()[a].as_long() < 5
    assert q.check() == z.sat and q.model()[a].as_long() > 100

    p.pop()               # back to just a > 0
    q.pop()
    assert p.check() == z.sat and q.check() == z.sat
    # After popping q's a>100, q can now agree with p's window.
    q.add(a < 5)
    assert q.check() == z.sat and 0 < q.model()[a].as_long() < 5


@pytest.mark.skipif(not HAVE_Z3PY, reason="real z3py not installed")
def test_push_pop_unsat_then_recover_agrees_with_z3py():
    def run(m):
        a = m.Int("a")
        s = m.Solver()
        s.add(a > 0)
        s.push()
        s.add(a < 0)          # contradiction within the frame
        r_in = str(s.check())  # unsat
        s.pop()
        r_out = str(s.check())  # sat again
        return r_in, r_out

    assert run(z) == run(_z3) == ("unsat", "sat")


# ===========================================================================
# Model independence: one solver's model must NOT reflect another's constraints
# ===========================================================================

def test_models_are_independent():
    x, y = z.Int("x"), z.Int("y")
    s1, s2 = z.Solver(), z.Solver()
    s1.add(x == 10, y == 20)
    s2.add(x == 99)
    s1.check()
    s2.check()
    m1, m2 = s1.model(), s2.model()
    assert m1[x].as_long() == 10 and m1[y].as_long() == 20
    assert m2[x].as_long() == 99  # s2 sees its own x, not s1's


# ===========================================================================
# Cross-context rebuild fidelity across theories (vs z3py)
# ===========================================================================

# Each case uses UNIQUE, sort-stable variable names. NOTE (documented AY
# limitation, unrelated to multi-solver): AY interns a constant by NAME and
# crashes if the SAME name is reused with a DIFFERENT sort in one context. The
# rebuild source here is a fresh per-case Context (not the shared _main_ctx), so
# cases never accumulate colliding names — and the source-ctx != solver-ctx
# difference still forces the cross-context rebuild path under test.
@pytest.mark.skipif(not HAVE_Z3PY, reason="real z3py not installed")
@pytest.mark.parametrize("name,buildf", [
    ("bv_add", lambda m: m.BitVec("bv_p", 8) + m.BitVec("bv_q", 8) == 5),
    ("bv_signed_lt", lambda m: m.BitVec("bv_r", 8) < m.BitVec("bv_s", 8)),
    ("array_rw", lambda m: m.Select(
        m.Store(m.Array("arr_A", m.IntSort(), m.IntSort()),
                m.Int("arr_i"), m.Int("arr_v")),
        m.Int("arr_i")) != m.Int("arr_v")),
    ("real_div", lambda m: m.Real("rd_r") / 2 == m.RealVal("3/2")),
    ("int_mod", lambda m: m.Int("im_n") % 3 == 1),
    ("bool_combinators", lambda m: m.And(
        m.Or(m.Bool("bc_b"), m.Not(m.Bool("bc_c"))),
        m.Implies(m.Bool("bc_b"), m.Bool("bc_c")))),
    ("distinct_pigeonhole", lambda m: m.And(
        m.Distinct(m.Int("dp_a"), m.Int("dp_b"), m.Int("dp_c")),
        m.Int("dp_a") > 0, m.Int("dp_b") > 0, m.Int("dp_c") > 0,
        m.Int("dp_a") < 3, m.Int("dp_b") < 3, m.Int("dp_c") < 3)),
    ("str_len", lambda m: m.Length(m.String("sl_w")) == 3),
    ("str_contains", lambda m: m.Contains(m.String("sc_w"), m.StringVal("ab"))),
    ("uf_inconsistent", lambda m: (lambda f, x: m.And(f(x) == 1, f(x) == 2))(
        m.Function("uf_f", m.IntSort(), m.IntSort()), m.Int("uf_x"))),
    ("forall_trivial", lambda m: m.ForAll([m.Int("fa_k")], m.Int("fa_k") * 0 == 0)),
    ("ite", lambda m: m.If(m.Int("ite_z") > 0, m.Int("ite_z"), -m.Int("ite_z")) < 0),
])
def test_rebuild_fidelity_matches_z3py(name, buildf):
    # ayz3: build in a fresh source Context, then add to a SEPARATE-context
    # Solver(). source-ctx != solver-ctx forces the cross-context rebuild path.
    # The verdict must match z3py building the same formula natively.
    src = z.Context()
    with z._ctx_scope(src):
        f = buildf(z)
    s = z.Solver()              # its own fresh context
    s.add(f)                    # triggers rebuild from `src` into the solver ctx
    ay = str(s.check())

    zf = buildf(_z3)
    zs = _z3.Solver()
    zs.add(zf)
    zz = str(zs.check())

    assert ay == zz, f"{name}: ayz3={ay} z3py={zz}"


def test_rebuild_matches_ay_native_for_incomplete_case():
    # AY is incomplete on mixed Int/Real arithmetic (returns `unknown`). The
    # rebuild must reproduce AY's REAL native answer for this formula, not a
    # fabricated verdict: native and rebuilt must AGREE (both unknown here).
    s_native = z.Solver(z.Context())
    with s_native.using():
        ii, rr = z.Int("ii"), z.Real("rr")
        s_native.add(ii + rr > 5)
    native = s_native.check()

    ii2, rr2 = z.Int("ii2"), z.Real("rr2")
    s_rebuilt = z.Solver()
    s_rebuilt.add(ii2 + rr2 > 5)
    rebuilt = s_rebuilt.check()

    assert native == rebuilt  # rebuild is faithful to AY's own behavior


# ===========================================================================
# Shared subterm identity is preserved across the rebuild
# ===========================================================================

def test_shared_subterm_rebuilt_consistently():
    x, y = z.Int("x"), z.Int("y")
    shared = x + y                      # appears 3x in `big`
    big = z.And(shared > 0, shared < 100, x == 30)
    s = z.Solver()
    s.add(big)
    assert s.check() == z.sat
    m = s.model()
    total = m[x].as_long() + m[y].as_long()
    assert 0 < total < 100 and m[x].as_long() == 30


# ===========================================================================
# Assumptions and assert_and_track from a different context
# ===========================================================================

def test_check_under_assumption_built_elsewhere():
    asm = z.Bool("asm_y")
    w = z.Int("asm_w")
    s = z.Solver()
    s.add(z.Implies(asm, w > 100))
    s.add(w < 50)
    assert s.check(asm) == z.unsat   # assuming asm forces w>100 ∧ w<50
    assert s.check() == z.sat        # without the assumption, satisfiable


def test_assert_and_track_cross_context_unsat_core():
    trk = z.Bool("trk_p")
    n = z.Int("trk_n")
    s = z.Solver()
    s.add(n > 0)
    s.assert_and_track(n < 0, trk)   # tracker + constraint built at top level
    assert s.check() == z.unsat
    core = s.unsat_core()
    # A sound, MINIMAL core: here the conflict is (n>0 hard) ∧ (n<0 tracked),
    # so the deletion-minimal core is exactly {trk_p} (n>0 is an untracked hard
    # assert, never in the core).
    assert len(core) == 1
    names = {c.decl_name for c in core if c.decl_name is not None}
    assert names == {"trk_p"}


# ===========================================================================
# Honesty: an unrebuildable node raises (never a silent wrong/empty term)
# ===========================================================================

def test_unregistered_const_cannot_be_silently_rebuilt():
    # A constant the binding never declared has no recorded name, so a rebuild
    # cannot fabricate it: it must raise NotImplementedError rather than produce
    # a wrong/empty term. We synthesize this by handing the rebuilder a const
    # whose metadata we deliberately remove from the registry.
    x = z.Int("ghost_x")
    f = x > 0
    # Drop the registry entry so the rebuild has no name to reconstruct from.
    x.ctx._const_meta.pop(x.ast, None)
    s = z.Solver()
    with pytest.raises(NotImplementedError):
        s.add(f)


# ===========================================================================
# Existing one-context-per-Solver idiom is unchanged (regression guard)
# ===========================================================================

def test_explicit_shared_context_solvers_are_independent():
    # HISTORY: this test used to assert the OLD (buggy) shared-stack behavior —
    # two Solvers over one explicit Context observed each other's assertions
    # (both unsat below). That C-level aliasing was the multi-solver soundness
    # bug: real z3 gives every Z3_solver its own assertion stack even on a
    # shared context. AY's C API now does the same, so two Solvers over the
    # SAME explicit Context are independent (matching z3py, cross-checked in
    # test_explicit_shared_context_matches_z3py below).
    c = z.Context()
    sa, sb = z.Solver(c), z.Solver(c)
    with sa.using():
        a = z.Int("a")
        sa.add(a > 0)
        sb.add(a < 0)
    # Independent stacks -> each side is sat on its own constraint.
    assert sa.check() == z.sat
    assert sb.check() == z.sat
    assert sa.model()[a].as_long() > 0
    assert sb.model()[a].as_long() < 0


@pytest.mark.skipif(not HAVE_Z3PY, reason="real z3py not installed")
def test_explicit_shared_context_matches_z3py():
    # Oracle for the corrected behavior above: in real z3py, two Solvers on
    # ONE shared Context are independent assertion stacks.
    zc = _z3.Context()
    za = _z3.Int("a", ctx=zc)
    zs1, zs2 = _z3.Solver(ctx=zc), _z3.Solver(ctx=zc)
    zs1.add(za > 0)
    zs2.add(za < 0)
    z3_verdicts = (str(zs1.check()), str(zs2.check()))

    c = z.Context()
    sa, sb = z.Solver(c), z.Solver(c)
    with sa.using():
        a = z.Int("a")
        sa.add(a > 0)
        sb.add(a < 0)
    ay_verdicts = (str(sa.check()), str(sb.check()))

    assert ay_verdicts == z3_verdicts == ("sat", "sat")


def test_using_scope_native_path_unaffected():
    # The canonical isolated idiom (fresh Context + using()) keeps working with
    # NO rebuild, since vars are built directly in the solver's context.
    s = z.Solver(z.Context())
    with s.using():
        x = z.Int("x")
        s.add(x > 0, x < 10)
    assert s.check() == z.sat
    assert 0 < s.model()[x].as_long() < 10


# ---------------------------------------------------------------------------
# Context lifecycle: each Solver/Optimize/Tactic Context owns a full native
# solver engine. Context.__del__ must free it via Z3_del_context once no
# wrapper references the Context (it used to leak for process lifetime), and
# must be double-free safe.
# ---------------------------------------------------------------------------

def test_context_del_frees_native_context(monkeypatch):
    import gc

    real_lib = z.lib
    freed = []

    class _RecordingLib:
        def __getattr__(self, name):
            fn = getattr(real_lib, name)
            if name == "Z3_del_context":
                def wrapped(ref):
                    freed.append(ref)
                    return fn(ref)
                return wrapped
            return fn

    monkeypatch.setattr(z, "lib", _RecordingLib())
    ctx = z.Context()
    ref = ctx.ref
    del ctx
    gc.collect()
    assert ref in freed, "Context.__del__ did not free the native Z3_context"


def test_context_del_is_double_free_safe():
    ctx = z.Context()
    ctx.__del__()
    assert ctx.ref is None
    # A second invocation must be a no-op (ref was nulled before the free).
    ctx.__del__()


def test_solver_keeps_its_context_alive_and_usable():
    # The Solver holds the only reference to its fresh Context; solving and
    # model readout must work long after any temporary references are gone.
    import gc

    s = z.Solver()
    with s.using():
        x = z.Int("ctx_keepalive_x")
        s.add(x > 3, x < 5)
    gc.collect()  # must NOT reclaim the context out from under the solver
    assert s.check() == z.sat
    assert s.model()[x].as_long() == 4

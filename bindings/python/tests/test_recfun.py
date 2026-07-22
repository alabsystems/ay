# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
#
# P1.1 battery (design Step 8, item 8): RecFunction / RecAddDefinition through
# `import ayz3` — the REAL binding path (z3py-on-AY-dylib
# can be sound where ayz3 is not, so this file tests ayz3 itself).
#
# Soundness contract under test:
#   * fully-expanded ground goals DECIDE (fact(5)==120 -> sat), and every sat
#     probe here is paired with its wrong-fact twin, which MUST be unsat —
#     a fix that passes only the headline probe is a wrong verdict;
#   * the canonical cross-context idiom (build in the default context, assert
#     into a Solver that owns another Context) REPLAYS the definition — and
#     when the definition has not been supplied yet, the rebuild RAISES
#     instead of silently rebuilding a plain UF (the wrong-`sat` trap);
#   * a goal whose rec applications cannot be fully expanded (symbolic
#     argument) fail-closes to `unknown` — never a plain-UF/quantifier-luck
#     `sat`, and never a wrong `unsat`.
#
# Run:  cargo build --release -p ay-ffi  &&  pytest bindings/python/tests/test_recfun.py -v

import pytest

import ayz3 as z

try:
    import z3 as _z3
    HAVE_Z3PY = True
except Exception:  # pragma: no cover - depends on environment
    _z3 = None
    HAVE_Z3PY = False


def _sum_def(name="f"):
    """f(x) = if x <= 0 then 0 else x + f(x-1)  (triangular sum)."""
    f = z.RecFunction(name, z.IntSort(), z.IntSort())
    x = z.Int("x")
    z.RecAddDefinition(f, [x], z.If(x <= 0, 0, x + f(x - 1)))
    return f


def _fact_def(name="fact"):
    f = z.RecFunction(name, z.IntSort(), z.IntSort())
    x = z.Int("x")
    z.RecAddDefinition(f, [x], z.If(x <= 1, 1, x * f(x - 1)))
    return f


def _mutual_defs():
    ev = z.RecFunction("ev", z.IntSort(), z.BoolSort())
    od = z.RecFunction("od", z.IntSort(), z.BoolSort())
    x = z.Int("x")
    z.RecAddDefinition(ev, [x], z.If(x <= 0, True, od(x - 1)))
    z.RecAddDefinition(od, [x], z.If(x <= 0, False, ev(x - 1)))
    return ev, od


# ---------------------------------------------------------------------------
# Same-context ground decisions (with wrong-fact twins for every sat)
# ---------------------------------------------------------------------------

def test_sum_ground_sat_and_wrong_fact_unsat():
    f = _sum_def()
    s = z.Solver()
    s.add(f(5) == 15)
    assert str(s.check()) == "sat"
    s2 = z.Solver()
    s2.add(f(5) == 16)
    assert str(s2.check()) == "unsat"


def test_fact_ground_sat_wrong_fact_unsat_and_model_eval():
    fact = _fact_def()
    s = z.Solver()
    s.add(fact(5) == 120)
    assert str(s.check()) == "sat"
    m = s.model()
    # m.eval over a rec application must EXPAND, not fabricate / plain-UF.
    ev = m.eval(fact(3))
    assert str(ev) == "6", f"m.eval(fact(3)) = {ev!r}, expected 6"
    s2 = z.Solver()
    s2.add(fact(5) == 121)
    assert str(s2.check()) == "unsat"


def test_mutual_recursion_ground():
    ev, od = _mutual_defs()
    s = z.Solver()
    s.add(ev(4))
    assert str(s.check()) == "sat"
    s2 = z.Solver()
    s2.add(ev(3))
    assert str(s2.check()) == "unsat"
    s3 = z.Solver()
    s3.add(od(3))
    assert str(s3.check()) == "sat"
    s4 = z.Solver()
    s4.add(od(4))
    assert str(s4.check()) == "unsat"


def test_zero_ary_def_and_redefinition_rejected():
    c = z.RecFunction("c0", z.IntSort())
    z.RecAddDefinition(c, [], z.IntVal(5))
    s = z.Solver()
    s.add(c() == 5)
    assert str(s.check()) == "sat"
    s2 = z.Solver()
    s2.add(c() == 6)
    assert str(s2.check()) == "unsat"
    # Redefinition is REJECTED (z3 parity: "function ... has already been
    # given a definition"). The original definition stays authoritative —
    # this is what makes live model handles' stale-eval protection sound.
    with pytest.raises(z.AyZ3Exception):
        z.RecAddDefinition(c, [], z.IntVal(6))
    s3 = z.Solver()
    s3.add(c() == 5)
    assert str(s3.check()) == "sat"
    s4 = z.Solver()
    s4.add(c() == 6)
    assert str(s4.check()) == "unsat"


def test_def_after_apps_built_same_context():
    """The z3py idiom: applications built BEFORE the definition arrives."""
    f = z.RecFunction("g", z.IntSort(), z.IntSort())
    goal_true = f(4) == 10   # sum(4) = 10; built while f has no body
    goal_wrong = f(4) == 11
    x = z.Int("x")
    z.RecAddDefinition(f, [x], z.If(x <= 0, 0, x + f(x - 1)))
    s = z.Solver()
    s.add(goal_true)
    assert str(s.check()) == "sat"
    s2 = z.Solver()
    s2.add(goal_wrong)
    assert str(s2.check()) == "unsat"


# ---------------------------------------------------------------------------
# Fail-closed residual path (symbolic argument)
# ---------------------------------------------------------------------------

def test_symbolic_arg_fails_closed_to_unknown():
    """f(n)==4 with free n: today's contract is honest `unknown` (residual
    mode demotes any engine sat; unsat would be WRONG since the goal is
    satisfiable — n=... exists for the sum shape). If bounded symbolic
    expansion is ever completed, this may legitimately become `sat` — then
    update this test WITH model re-assert validation, never by loosening."""
    f = _sum_def()
    n = z.Int("n")
    s = z.Solver()
    s.set("timeout", 4000)
    s.add(n >= 0, n <= 3, f(n) == 3)   # satisfiable: n = 2 (sum(2) = 3)
    r = str(s.check())
    assert r == "unknown", f"symbolic-arg residual must fail closed, got {r}"


# ---------------------------------------------------------------------------
# Canonical cross-context idiom — BOTH orders (design Step 8 item 8)
# ---------------------------------------------------------------------------

def test_cross_context_def_before_add_decides():
    fact = _fact_def()
    goal = fact(5) == 120
    s = z.Solver(z.Context())      # Solver owning a DIFFERENT context
    s.add(goal)                    # rebuild must replay the definition
    assert str(s.check()) == "sat"
    m = s.model()
    # ModelRef.eval adopts the foreign-context expr, replaying the definition.
    assert str(m.eval(fact(3))) == "6"
    sw = z.Solver(z.Context())
    sw.add(fact(5) == 121)         # wrong-fact twin
    assert str(sw.check()) == "unsat"


def test_cross_context_add_before_def_raises_never_sat():
    h = z.RecFunction("h", z.IntSort(), z.IntSort())
    goal = h(3) == 7               # h has NO definition yet
    s = z.Solver(z.Context())
    with pytest.raises(NotImplementedError):
        s.add(goal)                # fail-closed: never a plain-UF rebuild
    # Nothing was asserted; and no half-built decl may linger in the target
    # context: after the definition arrives, the SAME idiom must now decide.
    x = z.Int("x")
    z.RecAddDefinition(h, [x], z.If(x <= 0, 1, h(x - 1)))  # h(k) == 1 for all k
    s2 = z.Solver(z.Context())
    s2.add(h(3) == 1)
    assert str(s2.check()) == "sat"
    s3 = z.Solver(z.Context())
    s3.add(h(3) == 7)
    assert str(s3.check()) == "unsat"


def test_cross_context_mutual_recursion():
    ev, od = _mutual_defs()
    s = z.Solver(z.Context())
    s.add(ev(4))
    assert str(s.check()) == "sat"
    s2 = z.Solver(z.Context())
    s2.add(ev(3))
    assert str(s2.check()) == "unsat"
    s3 = z.Solver(z.Context())
    s3.add(od(5))
    assert str(s3.check()) == "sat"
    s4 = z.Solver(z.Context())
    s4.add(od(2))
    assert str(s4.check()) == "unsat"


def test_cross_context_zero_ary_replays_definition():
    """A 0-ary rec function's application is a nullary app — exactly the shape
    the declared-constant rebuild path would capture and strip the definition
    from. It must replay the definition instead."""
    c = z.RecFunction("cz", z.IntSort())
    z.RecAddDefinition(c, [], z.IntVal(5))
    s = z.Solver(z.Context())
    s.add(c() == 6)
    assert str(s.check()) == "unsat"   # plain-const rebuild would say sat
    s2 = z.Solver(z.Context())
    s2.add(c() == 5)
    assert str(s2.check()) == "sat"


def test_cross_context_zero_ary_without_def_raises():
    d = z.RecFunction("dz", z.IntSort())
    s = z.Solver(z.Context())
    with pytest.raises(NotImplementedError):
        s.add(d() == 1)


def test_redefinition_rejected_and_replayed_context_stays_consistent():
    """Z3_add_rec_def REJECTS a second definition of the same name (z3
    parity). A context that already replayed the one real definition keeps
    deciding with it — there is no stale-definition window because the
    registry is add-only."""
    ctx = z.Context()
    r = z.RecFunction("rr_refresh", z.IntSort(), z.IntSort())
    x = z.Int("x")
    z.RecAddDefinition(r, [x], z.If(x <= 0, 1, r(x - 1)))   # rr(k) == 1
    s = z.Solver(ctx)
    s.push()
    s.add(r(3) == 1)
    assert str(s.check()) == "sat"          # replays the definition into ctx
    s.pop()
    with pytest.raises(z.AyZ3Exception):
        z.RecAddDefinition(r, [x], z.If(x <= 0, 2, r(x - 1)))
    s.push()
    s.add(r(3) == 1)
    assert str(s.check()) == "sat"          # the one real definition holds
    s.pop()
    s.push()
    s.add(r(3) == 2)
    assert str(s.check()) == "unsat"
    s.pop()


def test_builtin_operator_name_rec_def_rejected_and_builtins_unharmed():
    """Skeptic reproducer: RecFunction('+') + RecAddDefinition('+', x*y) made
    2+3==6 sat with an invalid model (the expander spliced the body into
    builtin arithmetic). The definition must be REJECTED and builtin +/-/*
    must answer exactly as before."""
    for op, body_fn in (("+", lambda a, b: a * b),
                        ("-", lambda a, b: a + b),
                        ("*", lambda a, b: a - b)):
        C = z.Context()
        with z._ctx_scope(C):
            fd = z.RecFunction(op, z.IntSort(), z.IntSort(), z.IntSort())
            x, y = z.Int("x"), z.Int("y")
            with pytest.raises(z.AyZ3Exception):
                z.RecAddDefinition(fd, [x, y], body_fn(x, y))
            a, b = z.Int("a"), z.Int("b")
            s = z.Solver()
            s.add(a == 2, b == 3, a + b == 5, a - b == -1, a * b == 6)
            assert str(s.check()) == "sat"
            s2 = z.Solver()
            s2.add(a == 2, b == 3, a + b == 6)
            assert str(s2.check()) == "unsat"


def test_stale_model_eval_refused_after_new_definition():
    """A model minted BEFORE the definition registry grew must never
    re-answer rec-mentioning terms through the live registry (skeptic
    finding 3's surface). Uses the shared-context idiom — a fresh Solver owns
    its own context, whose registry only ever holds replayed definitions."""
    C = z.Context()
    with z._ctx_scope(C):
        f = z.RecFunction("fstale", z.IntSort(), z.IntSort())
        x = z.Int("x")
        z.RecAddDefinition(f, [x], x + 1)
        s = z.Solver()
        s.add(f(3) == 4)
        assert str(s.check()) == "sat"
        m = s.model()
        assert str(m.eval(f(3))) == "4"     # live model, same epoch: fine
        # A NEW definition arrives in the SAME context (different name;
        # redefinition is rejected, so growth is the only registry change).
        g = z.RecFunction("gstale", z.IntSort(), z.IntSort())
        z.RecAddDefinition(g, [x], x + 2)
        # The old model predates gstale: any rec-mentioning eval is refused
        # honestly (never a value the model did not certify).
        with pytest.raises(z.AyZ3Exception):
            m.eval(f(3))


def test_rec_name_collision_with_plain_uf_fails_closed():
    """If a name already lives in the target context as a PLAIN uninterpreted
    function, rebuilding a rec decl of the same name there must raise — reusing
    the plain decl would silently drop the definition (wrong-`sat` source)."""
    ctx = z.Context()
    pf = z.Function("pc_collide", z.IntSort(), z.IntSort())
    s = z.Solver(ctx)
    s.push()
    s.add(pf(1) >= 0)
    assert str(s.check()) == "sat"          # plain decl now lives in ctx
    s.pop()
    rf = z.RecFunction("pc_collide", z.IntSort(), z.IntSort())
    x = z.Int("x")
    z.RecAddDefinition(rf, [x], z.If(x <= 0, 0, rf(x - 1)))
    s.push()
    with pytest.raises(NotImplementedError):
        s.add(rf(3) == 0)                   # plain-UF reuse would drop the def
    s.pop()


# ---------------------------------------------------------------------------
# Differential vs real z3py (same probes, independent verdicts)
# ---------------------------------------------------------------------------

@pytest.mark.skipif(not HAVE_Z3PY, reason="real z3py not installed")
def test_differential_fact_vs_real_z3():
    # ayz3 side.
    fact = _fact_def()
    sa = z.Solver()
    sa.add(fact(5) == 120)
    ra_true = str(sa.check())
    sb = z.Solver()
    sb.add(fact(5) == 121)
    ra_wrong = str(sb.check())
    # real z3 side (unique name: z3's rec-def registry is context-global for
    # the whole pytest process, and a second definition of the same decl
    # errors).
    zf = _z3.RecFunction("fact_xdiff_recfun_ay", _z3.IntSort(), _z3.IntSort())
    zx = _z3.Int("x")
    _z3.RecAddDefinition(zf, [zx], _z3.If(zx <= 1, 1, zx * zf(zx - 1)))
    zs = _z3.Solver()
    zs.add(zf(5) == 120)
    rz_true = str(zs.check())
    zs2 = _z3.Solver()
    zs2.add(zf(5) == 121)
    rz_wrong = str(zs2.check())
    assert (ra_true, ra_wrong) == (rz_true, rz_wrong) == ("sat", "unsat")

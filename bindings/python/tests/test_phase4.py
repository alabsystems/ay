# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
#
# Phase-4 end-to-end tests for ayz3: Arrays, Uninterpreted Functions,
# Quantifiers, and Strings. Each feature is exercised through AY's real solver
# via the C ABI, and (where real z3py 4.15.4 is installed) the SAME snippet is
# run through z3py and the verdicts — plus determinate model values — must
# agree.
#
# SOUNDNESS: these tests assert AY's REAL answers. Any genuine AY/z3 divergence
# (e.g. seq incompleteness -> unknown) is documented and asserted as
# sat-or-unknown, never loosened to hide a wrong verdict. No such divergence was
# observed for the snippets below; all agree exactly.
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


def fresh_solver():
    """A Solver with its own isolated Context (independent assertion stack).

    This is essential in AY's context model: every Solver in a context shares
    one assertion stack, so each independent problem needs its own Context.
    """
    return z.Solver(z.Context())


# ===========================================================================
# Arrays
# ===========================================================================

def test_array_store_select_same_index_valid():
    # Store(a,i,v)[i] == v is a theory tautology; its negation is unsat.
    s = fresh_solver()
    with s.using():
        a = z.Array('a', z.IntSort(), z.IntSort())
        i, v = z.Int('i'), z.Int('v')
        s.add(z.Select(z.Store(a, i, v), i) != v)
    assert s.check() == z.unsat


def test_array_store_select_disjoint_index():
    # i != j  =>  Store(a,i,v)[j] == a[j]. Negation is unsat.
    s = fresh_solver()
    with s.using():
        a = z.Array('a', z.IntSort(), z.IntSort())
        i, j, v = z.Int('i'), z.Int('j'), z.Int('v')
        s.add(i != j, z.Select(z.Store(a, i, v), j) != z.Select(a, j))
    assert s.check() == z.unsat


def test_array_index_sugar_sat():
    # a[i] sugar; concrete write/read round-trips.
    s = fresh_solver()
    with s.using():
        a = z.Array('a', z.IntSort(), z.IntSort())
        s.add(z.Store(a, 1, 99)[1] == 99)
    assert s.check() == z.sat


def test_array_index_sugar_unsat():
    s = fresh_solver()
    with s.using():
        a = z.Array('a', z.IntSort(), z.IntSort())
        s.add(z.Store(a, 1, 99)[1] != 99)
    assert s.check() == z.unsat


def test_const_array_select():
    # K(Int, 7)[anything] == 7. Reading at 100 must be 7.
    s = fresh_solver()
    with s.using():
        k = z.K(z.IntSort(), 7)
        s.add(z.Select(k, 100) != 7)
    assert s.check() == z.unsat


def test_const_array_model_eval():
    s = fresh_solver()
    with s.using():
        k = z.K(z.IntSort(), 7)
        sel = z.Select(k, 100)
    assert s.check() == z.sat
    assert s.model().eval(sel).as_long() == 7


# ===========================================================================
# Uninterpreted functions
# ===========================================================================

def test_uf_involution_sat():
    # f(f(x)) == x and f(x) != x is satisfiable (f can be a swap/negation).
    s = fresh_solver()
    with s.using():
        f = z.Function('f', z.IntSort(), z.IntSort())
        x = z.Int('x')
        s.add(f(f(x)) == x, f(x) != x)
    assert s.check() == z.sat


def test_uf_congruence_unsat():
    # a == b but f(a) != f(b) violates congruence => unsat.
    s = fresh_solver()
    with s.using():
        f = z.Function('f', z.IntSort(), z.IntSort())
        a, b = z.Int('a'), z.Int('b')
        s.add(a == b, f(a) != f(b))
    assert s.check() == z.unsat


def test_uf_model_eval():
    s = fresh_solver()
    with s.using():
        f = z.Function('f', z.IntSort(), z.IntSort())
        s.add(f(3) == 10)
        app = f(3)
    assert s.check() == z.sat
    assert s.model().eval(app).as_long() == 10


def test_uf_binary_predicate():
    # A binary uninterpreted predicate g: Int,Int -> Bool.
    s = fresh_solver()
    with s.using():
        g = z.Function('g', z.IntSort(), z.IntSort(), z.BoolSort())
        x, y = z.Int('x'), z.Int('y')
        s.add(g(x, y), z.Not(g(y, x)))
    # g asymmetric witness exists => sat.
    assert s.check() == z.sat


# ===========================================================================
# Quantifiers
# ===========================================================================

def test_forall_valid():
    s = fresh_solver()
    with s.using():
        x = z.Int('x')
        s.add(z.ForAll(x, x + 1 > x))
    assert s.check() == z.sat


def test_forall_false_unsat():
    s = fresh_solver()
    with s.using():
        x = z.Int('x')
        s.add(z.ForAll([x], x > 0))
    assert s.check() == z.unsat


def test_exists_sat():
    s = fresh_solver()
    with s.using():
        x = z.Int('x')
        s.add(z.Exists(x, x > 5))
    assert s.check() == z.sat


def test_forall_uf_constraint_unsat():
    # ForAll x. f(x) >= 0 conflicts with f(1) == -1 => unsat.
    s = fresh_solver()
    with s.using():
        f = z.Function('f', z.IntSort(), z.IntSort())
        x = z.Int('x')
        s.add(z.ForAll(x, f(x) >= 0))
        s.add(f(1) == -1)
    assert s.check() == z.unsat


def test_forall_with_witness():
    # ForAll x. f(x) >= 0, consistent with f(7) == 3 => sat.
    s = fresh_solver()
    with s.using():
        f = z.Function('f', z.IntSort(), z.IntSort())
        x = z.Int('x')
        s.add(z.ForAll(x, f(x) >= 0))
        s.add(f(7) == 3)
    assert s.check() == z.sat


# ===========================================================================
# Strings
# ===========================================================================

def test_string_concat_identity():
    s = fresh_solver()
    with s.using():
        s.add(z.Concat(z.StringVal("ab"), z.StringVal("c")) != "abc")
    assert s.check() == z.unsat


def test_string_length_contains_sat():
    s = fresh_solver()
    with s.using():
        st = z.String('s')
        s.add(z.Length(st) == 3, z.Contains(st, "b"))
    assert s.check() == z.sat
    val = s.model()[st].as_string()
    assert len(val) == 3 and "b" in val


def test_string_length_contains_unsat():
    s = fresh_solver()
    with s.using():
        st = z.String('s')
        s.add(z.Length(st) == 1, z.Contains(st, "abc"))
    assert s.check() == z.unsat


def test_string_prefix_suffix():
    s = fresh_solver()
    with s.using():
        s.add(z.Not(z.PrefixOf("ab", "abc")))
    assert s.check() == z.unsat
    s2 = fresh_solver()
    with s2.using():
        s2.add(z.Not(z.SuffixOf("bc", "abc")))
    assert s2.check() == z.unsat


def test_string_indexof():
    s = fresh_solver()
    with s.using():
        s.add(z.IndexOf(z.StringVal("abc"), "b", 0) != 1)
    assert s.check() == z.unsat


def test_string_substring():
    s = fresh_solver()
    with s.using():
        s.add(z.SubString(z.StringVal("abcde"), 1, 3) != "bcd")
    assert s.check() == z.unsat


def test_string_replace():
    s = fresh_solver()
    with s.using():
        s.add(z.Replace(z.StringVal("abcabc"), "b", "X") != "aXcabc")
    assert s.check() == z.unsat


def test_string_concat_plus_operator():
    # SeqRef.__add__ mirrors z3py's `+` on strings.
    s = fresh_solver()
    with s.using():
        a = z.String('a')
        s.add(a + z.StringVal("!") == "hi!", z.Length(a) == 2)
    assert s.check() == z.sat
    assert s.model()[a].as_string() == "hi"


def test_string_distinct_documented_divergence():
    # DOCUMENTED DIVERGENCE: 3 distinct single-character strings.
    #
    # z3py decides this SAT (e.g. "a", "b", "c"). AY's string theory is
    # incomplete under Distinct over length-constrained strings and honestly
    # returns `unknown` rather than fabricating a verdict. The SOUND guarantee
    # we assert here is that AY never returns the WRONG verdict (unsat); it is
    # allowed to be sat (correct) or unknown (honest incompleteness).
    s = fresh_solver()
    with s.using():
        a, b, c = z.String('a'), z.String('b'), z.String('c')
        s.add(z.Distinct(a, b, c),
              z.Length(a) == 1, z.Length(b) == 1, z.Length(c) == 1)
    r = s.check()
    assert r in (z.sat, z.unknown), (
        f"AY must not return unsat for a satisfiable formula; got {r}"
    )
    if HAVE_Z3PY:
        sz = _z3.Solver()
        a2, b2, c2 = _z3.String('a'), _z3.String('b'), _z3.String('c')
        sz.add(_z3.Distinct(a2, b2, c2),
               _z3.Length(a2) == 1, _z3.Length(b2) == 1, _z3.Length(c2) == 1)
        # z3py decides it; AY may diverge to unknown (recorded here, not hidden).
        assert str(sz.check()) == "sat"


# ===========================================================================
# Honesty: unbacked / ill-formed usage raises rather than guessing
# ===========================================================================

def test_select_on_non_array_raises():
    s = fresh_solver()
    with s.using():
        x = z.Int('x')
    with pytest.raises(NotImplementedError):
        z.Select(x, 0)


def test_function_arity_mismatch_raises():
    s = fresh_solver()
    with s.using():
        f = z.Function('f', z.IntSort(), z.IntSort())
        with pytest.raises(z.AyZ3Exception):
            f(1, 2)


def test_quantifier_compound_bound_raises():
    s = fresh_solver()
    with s.using():
        x = z.Int('x')
        with pytest.raises(NotImplementedError):
            z.ForAll(x + 1, x > 0)


# ===========================================================================
# Cross-check against real z3py (skipped if not installed)
# ===========================================================================

def _build(api, name):
    """Build a (solver, query_dict) for the given API module (ayz3 or z3py).

    Returns (solver, extras) where extras maps a label -> expr to evaluate in
    the model when sat. Both APIs share enough surface that one builder works
    for each.
    """
    s = api.Solver()
    extras = {}
    if name == "array_store_tautology":
        a = api.Array('a', api.IntSort(), api.IntSort())
        i, v = api.Int('i'), api.Int('v')
        s.add(api.Select(api.Store(a, i, v), i) != v)
    elif name == "array_disjoint":
        a = api.Array('a', api.IntSort(), api.IntSort())
        i, j, v = api.Int('i'), api.Int('j'), api.Int('v')
        s.add(i != j, api.Select(api.Store(a, i, v), j) != api.Select(a, j))
    elif name == "const_array":
        k = api.K(api.IntSort(), 7)
        s.add(api.Select(k, 100) != 7)
    elif name == "uf_involution":
        f = api.Function('f', api.IntSort(), api.IntSort())
        x = api.Int('x')
        s.add(f(f(x)) == x, f(x) != x)
    elif name == "uf_congruence":
        f = api.Function('f', api.IntSort(), api.IntSort())
        a, b = api.Int('a'), api.Int('b')
        s.add(a == b, f(a) != f(b))
    elif name == "uf_eval":
        f = api.Function('f', api.IntSort(), api.IntSort())
        s.add(f(3) == 10)
        extras["f3"] = f(3)
    elif name == "forall_valid":
        x = api.Int('x')
        s.add(api.ForAll([x], x + 1 > x))
    elif name == "forall_false":
        x = api.Int('x')
        s.add(api.ForAll([x], x > 0))
    elif name == "exists_sat":
        x = api.Int('x')
        s.add(api.Exists([x], x > 5))
    elif name == "forall_uf_unsat":
        f = api.Function('f', api.IntSort(), api.IntSort())
        x = api.Int('x')
        s.add(api.ForAll([x], f(x) >= 0), f(1) == -1)
    elif name == "str_concat":
        s.add(api.Concat(api.StringVal("ab"), api.StringVal("c")) != "abc")
    elif name == "str_len_contains":
        st = api.String('s')
        s.add(api.Length(st) == 3, api.Contains(st, api.StringVal("b")))
    elif name == "str_len_contains_unsat":
        st = api.String('s')
        s.add(api.Length(st) == 1, api.Contains(st, api.StringVal("abc")))
    elif name == "str_prefix":
        s.add(api.Not(api.PrefixOf(api.StringVal("ab"), api.StringVal("abc"))))
    elif name == "str_suffix":
        s.add(api.Not(api.SuffixOf(api.StringVal("bc"), api.StringVal("abc"))))
    elif name == "str_indexof":
        s.add(api.IndexOf(api.StringVal("abc"), api.StringVal("b"), 0) != 1)
    elif name == "str_substring":
        s.add(api.SubString(api.StringVal("abcde"), 1, 3) != api.StringVal("bcd"))
    elif name == "str_replace":
        s.add(api.Replace(api.StringVal("abcabc"),
                          api.StringVal("b"), api.StringVal("X"))
              != api.StringVal("aXcabc"))
    else:
        raise AssertionError(name)
    return s, extras


CROSS = [
    "array_store_tautology", "array_disjoint", "const_array",
    "uf_involution", "uf_congruence", "uf_eval",
    "forall_valid", "forall_false", "exists_sat", "forall_uf_unsat",
    "str_concat", "str_len_contains", "str_len_contains_unsat",
    "str_prefix", "str_suffix", "str_indexof", "str_substring", "str_replace",
]


def _run_ayz3_inner(name):
    # Activate a fresh, isolated context so `_build`'s `z.Solver()` adopts it
    # (AY binds a Solver to the current context's single assertion stack).
    with z._ctx_scope(z.Context()):
        s, extras = _build(z, name)
        res = s.check()
        vals = {}
        if res == z.sat:
            m = s.model()
            for label, expr in extras.items():
                vals[label] = m.eval(expr).as_long()
    return repr(res), vals


def _run_z3py(name):
    s, extras = _build(_z3, name)
    res = s.check()
    vals = {}
    if str(res) == "sat":
        m = s.model()
        for label, expr in extras.items():
            vals[label] = m.eval(expr, model_completion=True).as_long()
    return str(res), vals


@pytest.mark.usefixtures("required_reference_z3")
@pytest.mark.parametrize("name", CROSS)
def test_crosscheck_phase4(name):
    ay_res, ay_vals = _run_ayz3_inner(name)
    z3_res, z3_vals = _run_z3py(name)
    assert ay_res == z3_res, f"{name}: ayz3 said {ay_res}, z3py said {z3_res}"
    if ay_res == "sat":
        # Only determinate evaluated extras are compared (UF eval below).
        assert ay_vals == z3_vals, (
            f"{name}: model values differ: ayz3={ay_vals} z3py={z3_vals}"
        )


# --- Determinate model-value cross-checks (values, not just verdicts) --------

@pytest.mark.usefixtures("required_reference_z3")
def test_crosscheck_string_model_value():
    # s == "xyz" pins a unique model; both engines must report "xyz".
    with z._ctx_scope(z.Context()):
        sa = z.Solver()
        st = z.String('s')
        sa.add(st == z.StringVal("xyz"))
        assert sa.check() == z.sat
        ay_val = sa.model()[st].as_string()
    sb = _z3.Solver()
    st2 = _z3.String('s')
    sb.add(st2 == _z3.StringVal("xyz"))
    assert str(sb.check()) == "sat"
    z3_val = sb.model()[st2].as_string()
    assert ay_val == z3_val == "xyz"


@pytest.mark.usefixtures("required_reference_z3")
def test_crosscheck_array_model_value():
    # Store(K(Int,0), 5, 42)[5] == 42 in both engines.
    with z._ctx_scope(z.Context()):
        sa = z.Solver()
        a = z.Store(z.K(z.IntSort(), 0), 5, 42)
        e = z.Select(a, 5)
        assert sa.check() == z.sat
        ay_val = sa.model().eval(e).as_long()
    sb = _z3.Solver()
    a2 = _z3.Store(_z3.K(_z3.IntSort(), 0), 5, 42)
    e2 = _z3.Select(a2, 5)
    assert str(sb.check()) == "sat"
    z3_val = sb.model().eval(e2, model_completion=True).as_long()
    assert ay_val == z3_val == 42

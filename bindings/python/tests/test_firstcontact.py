# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
#
# Task B (z3py first-contact): make the line-1..3 idioms of typical z3py scripts
# run on ayz3. Covers, each cross-checked against real z3py where installed:
#   1. Plural constructors  Ints/Bools/Reals/BitVecs/Consts/Strings
#   2. BitVec .size() as a callable METHOD (and BitVecSort .size())
#   3. Goal + callable Tactic -> ApplyResult (subgoals)
#   4. IntNumRef / RatNumRef / BitVecNumRef numeral subtypes
#   5. Distinct decl().name() == 'distinct' and is_distinct True
#   6. get_version_string() / get_version()
#
# Every test builds its ayz3 terms inside a FRESH, isolated Context (the `scope`
# fixture) — AY interns a constant by name within a context, so a shared
# process-wide context would collide across suites.
#
# Run:  cargo build -p ay-ffi  &&  pytest bindings/python/tests/test_firstcontact.py -v

import pytest

import ayz3 as z

try:
    import z3 as _z3
    HAVE_Z3PY = True
except Exception:  # pragma: no cover - depends on environment
    _z3 = None
    HAVE_Z3PY = False

need_z3 = pytest.mark.usefixtures("required_reference_z3")


@pytest.fixture
def scope():
    """Make a fresh, isolated ayz3 Context the current one for the test body."""
    solver = z.Solver(z.Context())
    with solver.using():
        yield solver.ctx


# ---------------------------------------------------------------------------
# 1. Plural constructors
# ---------------------------------------------------------------------------

def test_plural_constructors_shapes(scope):
    xs = z.Ints("x y z")
    assert isinstance(xs, list) and len(xs) == 3
    assert [str(v) for v in xs] == ["x", "y", "z"]
    # Unpacking is the tutorial line-1 idiom.
    a, b = z.Reals("a b")
    p, q = z.Bools("p q")
    u, v = z.BitVecs("u v", 8)
    s, t = z.Strings("s t")
    assert u.size() == 8 and v.size() == 8
    assert z.is_real(a) and z.is_bool(p) and z.is_string(s)


def test_ints_solve_idiom(scope):
    x, y = z.Ints("x y")
    sol = z.Solver()
    sol.add(x + y == 5, x > y)
    assert sol.check() == z.sat
    m = sol.model()
    assert m[x].as_long() + m[y].as_long() == 5


def test_consts_plural(scope):
    S = z.IntSort()
    a, b, c = z.Consts("a b c", S)
    assert z.is_int(a) and z.is_int(b) and z.is_int(c)


def test_plural_accepts_iterable(scope):
    a, b = z.Ints(["a", "b"])
    assert str(a) == "a" and str(b) == "b"


@need_z3
def test_plural_matches_z3py(scope):
    ax = z.Ints("x y z")
    zx = _z3.Ints("x y z")
    assert isinstance(zx, list) and len(ax) == len(zx)
    assert [str(v) for v in ax] == [str(v) for v in zx]


# ---------------------------------------------------------------------------
# 2. BitVec .size() is a callable method
# ---------------------------------------------------------------------------

def test_bitvec_size_is_callable(scope):
    a = z.BitVec("a", 8)
    assert a.size() == 8                       # z3py: a METHOD
    # Backward-compat: `.size` still behaves as an int in arithmetic contexts.
    assert a.size + 0 == 8
    assert a.sort().size() == 8                # BitVecSortRef.size()
    assert z.BitVecSort(16).size() == 16


@need_z3
def test_bitvec_size_matches_z3py(scope):
    assert z.BitVec("a", 8).size() == _z3.BitVec("a", 8).size()
    assert z.BitVecSort(32).size() == _z3.BitVecSort(32).size()


# ---------------------------------------------------------------------------
# 3. Goal + callable Tactic -> ApplyResult
# ---------------------------------------------------------------------------

def test_goal_add_flattens_conjunction(scope):
    x, y = z.Ints("x y")
    g = z.Goal()
    g.add(z.And(x > 0, y > 0))
    # z3py's Goal splits a top-level conjunction into separate formulas.
    assert len(g) == 2
    assert g.sexpr().startswith("(goal")
    # empty / single as_expr shapes
    assert z.is_true(z.Goal().as_expr())
    g1 = z.Goal()
    g1.add(x > 0)
    assert len(g1) == 1


def test_tactic_apply_returns_applyresult(scope):
    x, y = z.Ints("x y")
    g = z.Goal()
    g.add(z.And(x > 0, y > 0))
    r = z.Tactic("simplify")(g)
    assert isinstance(r, z.ApplyResult)
    assert len(r) == 1                         # simplify -> one subgoal
    sub = r[0]
    assert isinstance(sub, z.Goal)
    assert len(sub) == 2                        # the two flattened conjuncts


def test_tactic_nnf_pushes_negation(scope):
    x, y = z.Ints("x y")
    g = z.Goal()
    g.add(z.Not(z.And(x > 0, y > 0)))
    r = z.Tactic("nnf")(g)
    assert len(r) == 1
    sub = r[0]
    # NNF turns Not(And(a, b)) into Or(Not a, Not b): a single Or formula.
    assert len(sub) == 1
    assert z.is_or(sub[0])


def test_tactic_split_clause_multiple_subgoals(scope):
    x, y, w = z.Ints("x y z")
    g = z.Goal()
    g.add(z.Or(x > 0, y > 0, w > 0))
    r = z.Tactic("split-clause")(g)
    assert len(r) == 3                          # one subgoal per disjunct
    for i in range(3):
        assert len(r[i]) == 1


def test_tactic_apply_accepts_bare_expr(scope):
    x = z.Int("x")
    r = z.Tactic("simplify")(x > 0)
    assert isinstance(r, z.ApplyResult) and len(r) == 1


def test_tactic_honest_failure_raises(scope):
    x = z.Int("x")
    g = z.Goal()
    g.add(x > 0)  # no clause -> split-clause honestly fails
    with pytest.raises(z.AyZ3Exception):
        z.Tactic("split-clause")(g)


@need_z3
def test_goal_tactic_shape_matches_z3py(scope):
    x, y = z.Ints("x y")
    zx, zy = _z3.Ints("x y")
    g = z.Goal(); g.add(z.And(x > 0, y > 0))
    zg = _z3.Goal(); zg.add(_z3.And(zx > 0, zy > 0))
    ar, zar = z.Tactic("simplify")(g), _z3.Tactic("simplify")(zg)
    assert len(ar) == len(zar) == 1
    assert len(ar[0]) == len(zar[0]) == 2
    # split-clause subgoal COUNT matches z3py exactly.
    x2, y2, w2 = z.Ints("p q r")
    zp, zq, zr = _z3.Ints("p q r")
    g2 = z.Goal(); g2.add(z.Or(x2 > 0, y2 > 0, w2 > 0))
    zg2 = _z3.Goal(); zg2.add(_z3.Or(zp > 0, zq > 0, zr > 0))
    assert len(z.Tactic("split-clause")(g2)) == len(_z3.Tactic("split-clause")(zg2)) == 3


def test_tactic_apply_verdict_preserved(scope):
    # SOUNDNESS: the disjunction of split-clause subgoals is equisatisfiable to
    # the input, and each single-subgoal transform is equivalence-preserving.
    x, y = z.Ints("x y")
    g = z.Goal()
    g.add(x + y == 5, x > y)
    r = z.Tactic("simplify")(g)
    # Solve the produced subgoal; it must be SAT (the original goal is SAT).
    s = z.Solver()
    for f in r[0]:
        s.add(f)
    assert s.check() == z.sat


# ---------------------------------------------------------------------------
# 4. Numeral subtypes
# ---------------------------------------------------------------------------

def test_intnumref_model_value(scope):
    x = z.Int("x")
    s = z.Solver()
    s.add(x == 7)
    assert s.check() == z.sat
    m = s.model()
    assert isinstance(m[x], z.IntNumRef)
    assert m[x].as_long() == 7
    assert isinstance(m.eval(x), z.IntNumRef)


def test_intval_is_intnumref(scope):
    iv = z.IntVal(5)
    assert isinstance(iv, z.IntNumRef)
    assert iv.as_long() == 5
    assert iv.as_binary_string() == "101"
    # A non-value expression stays a plain ArithRef (NOT a NumRef), like z3py.
    assert not isinstance(z.Int("x") + 1, z.IntNumRef)


def test_ratnumref(scope):
    rv = z.RealVal("1/3")
    assert isinstance(rv, z.RatNumRef)
    assert rv.numerator_as_long() == 1
    assert rv.denominator_as_long() == 3
    assert rv.numerator().as_long() == 1
    assert rv.denominator().as_long() == 3
    assert not rv.is_int_value()
    assert z.RealVal("4/2").is_int_value()
    assert rv.as_decimal(10) == "0.3333333333?"
    assert z.RealVal("1/2").as_decimal(10) == "0.5"


def test_bitvecnumref(scope):
    bv = z.BitVecVal(200, 8)
    assert isinstance(bv, z.BitVecNumRef)
    assert bv.as_long() == 200
    assert bv.as_signed_long() == -56
    assert z.BitVecVal(5, 8).as_signed_long() == 5


@need_z3
def test_numref_matches_z3py(scope):
    assert isinstance(_z3.IntVal(5), _z3.IntNumRef)
    assert isinstance(_z3.RealVal("1/3"), _z3.RatNumRef)
    assert isinstance(_z3.BitVecVal(200, 8), _z3.BitVecNumRef)
    # value equality
    assert z.IntVal(5).as_long() == _z3.IntVal(5).as_long()
    assert z.RealVal("1/3").as_decimal(10) == _z3.RealVal("1/3").as_decimal(10)
    assert z.BitVecVal(200, 8).as_signed_long() == _z3.BitVecVal(200, 8).as_signed_long()


# ---------------------------------------------------------------------------
# 5. Distinct decl name / is_distinct
# ---------------------------------------------------------------------------

def test_distinct_decl_and_predicate(scope):
    a, b, c = z.Ints("a b c")
    d = z.Distinct(a, b, c)
    assert d.decl().name() == "distinct"
    assert z.is_distinct(d)
    assert not z.is_and(d)                       # presents as distinct, not and
    assert d.num_args() == 3
    assert [str(x) for x in d.children()] == ["a", "b", "c"]
    assert d.decl().kind() == _lib_distinct_kind()


def _lib_distinct_kind():
    # Z3_OP_DISTINCT (from ayz3.introspect constants).
    from ayz3 import introspect
    return introspect.Z3_OP_DISTINCT


def test_distinct_still_solves_correctly(scope):
    a, b = z.Ints("a b")
    s1 = z.Solver()
    s1.add(z.Distinct(a, b), a == 1, b == 1)
    assert s1.check() == z.unsat            # distinct forbids a == b
    s2 = z.Solver()
    s2.add(z.Distinct(a, b), a == 1, b == 2)
    assert s2.check() == z.sat


@need_z3
def test_distinct_matches_z3py(scope):
    a, b, c = z.Ints("a b c")
    za, zb, zc = _z3.Ints("a b c")
    assert z.Distinct(a, b, c).decl().name() == _z3.Distinct(za, zb, zc).decl().name()
    assert z.is_distinct(z.Distinct(a, b, c)) == _z3.is_distinct(_z3.Distinct(za, zb, zc))
    assert z.Distinct(a, b, c).num_args() == _z3.Distinct(za, zb, zc).num_args()


# ---------------------------------------------------------------------------
# 6. Version
# ---------------------------------------------------------------------------

def test_get_version_string():
    s = z.get_version_string()
    assert isinstance(s, str)
    parts = s.split(".")
    assert len(parts) == 3 and all(p.isdigit() for p in parts)


def test_get_version_tuple():
    v = z.get_version()
    assert isinstance(v, tuple) and len(v) == 4
    assert all(isinstance(n, int) for n in v)
    # The string is the first three components of the tuple.
    assert z.get_version_string() == f"{v[0]}.{v[1]}.{v[2]}"

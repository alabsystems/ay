# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
#
# B-3 regression: z3py-shaped AST introspection over AY's C ABI.
#
# Covers the module predicates (is_add/is_and/is_const/...) and the
# AstRef/FuncDeclRef accessors (.decl()/.children()/.arg(i)/.num_args()/.sexpr()
# and FuncDeclRef .name()/.arity()/.domain(i)/.range()/.kind()/.params()).
#
# The suite is self-contained (it hardcodes AY's honest predicate verdicts) AND,
# where real z3py is installed, cross-checks EVERY expression against z3py so any
# drift is caught. AY normalizes a handful of operators to an equivalent normal
# form at construction (a documented, sound canonicalization shared with B-1's
# printing path); those expressions are listed in CANON and asserted to AY's
# honest verdict, with z3py's differing verdict recorded so the divergence stays
# intentional rather than silent.
#
# Every test builds its ayz3 terms inside a FRESH, isolated Context (the `scope`
# fixture) — like the other suites' `Solver(Context()).using()` idiom. AY interns
# a constant by name within a context (a soundness feature), so sharing the
# process-wide main context across suites would collide when two modules declare
# the same name at different sorts. A per-test context sidesteps that entirely.
#
# Run:  cargo build -p ay-ffi  &&  pytest bindings/python/tests/test_introspect.py -v

import pytest

import ayz3 as z

try:
    import z3 as _z3
    HAVE_Z3PY = True
except Exception:  # pragma: no cover - depends on environment
    _z3 = None
    HAVE_Z3PY = False


@pytest.fixture
def scope():
    """Make a fresh, isolated ayz3 Context the current one for the test body."""
    solver = z.Solver(z.Context())
    with solver.using():
        yield solver.ctx


# The required predicate surface (task B-3), routed on the real ast/decl kind.
CORE_PREDS = [
    "is_int", "is_real", "is_bool", "is_bv", "is_array", "is_string",
    "is_const", "is_app", "is_expr", "is_var",
    "is_and", "is_or", "is_not", "is_add", "is_mul", "is_sub",
    "is_eq", "is_distinct", "is_le", "is_lt", "is_ge", "is_gt",
    "is_select", "is_store", "is_quantifier", "is_true", "is_false",
    "is_int_value", "is_rational_value",
]


def _build(mod):
    """Build the shared ~24-expression corpus in either ayz3 or z3py."""
    x, y = mod.Int("x"), mod.Int("y")
    zc = mod.Int("z")
    p, q = mod.Bool("p"), mod.Bool("q")
    a = mod.Array("a", mod.IntSort(), mod.IntSort())
    bv = mod.BitVec("bv", 8)
    f = mod.Function("f", mod.IntSort(), mod.IntSort())
    s = mod.String("s")
    return {
        "x": x,
        "IntVal5": mod.IntVal(5),
        "RealVal": mod.RealVal("1/2"),
        "x+2*y": x + 2 * y,
        "x*y": x * y,
        "And": mod.And(p, q),
        "Or": mod.Or(p, q),
        "Not": mod.Not(p),
        "p&q": p & q,
        "x<y": x < y,
        "x<=y": x <= y,
        "x>y": x > y,
        "x>=y": x >= y,
        "x==y": x == y,
        "Distinct3": mod.Distinct(x, y, zc),
        "x!=y": x != y,
        "Select": mod.Select(a, x),
        "Store": mod.Store(a, x, x),
        "bv+bv": bv + bv,
        "BitVecVal": mod.BitVecVal(5, 8),
        "f(x)": f(x),
        "ForAll": mod.ForAll([x], x == y),
        "x-y": x - y,
        "-x": -x,
        "Implies": mod.Implies(p, q),
        "BoolTrue": mod.BoolVal(True),
        "BoolFalse": mod.BoolVal(False),
        "String": s,
        "StringVal": mod.StringVal("hi"),
    }


def _true_preds(mod, e):
    out = set()
    for name in CORE_PREDS:
        fn = getattr(mod, name, None)
        try:
            if fn is not None and fn(e):
                out.add(name)
        except Exception:
            pass
    return out


# AY's honest TRUE-predicate set (among CORE_PREDS) for each corpus expression.
AYZ3_EXPECTED = {
    "x": {"is_app", "is_const", "is_expr", "is_int"},
    "IntVal5": {"is_app", "is_const", "is_expr", "is_int", "is_int_value"},
    "RealVal": {"is_app", "is_const", "is_expr", "is_real", "is_rational_value"},
    "x+2*y": {"is_add", "is_app", "is_expr", "is_int"},
    "x*y": {"is_app", "is_expr", "is_int", "is_mul"},
    "And": {"is_and", "is_app", "is_bool", "is_expr"},
    "Or": {"is_app", "is_bool", "is_expr", "is_or"},
    "Not": {"is_app", "is_bool", "is_expr", "is_not"},
    "p&q": {"is_and", "is_app", "is_bool", "is_expr"},
    "x<y": {"is_app", "is_bool", "is_expr", "is_lt"},
    "x<=y": {"is_app", "is_bool", "is_expr", "is_le"},
    "x==y": {"is_app", "is_bool", "is_eq", "is_expr"},
    "Select": {"is_app", "is_expr", "is_int", "is_select"},
    "Store": {"is_app", "is_array", "is_expr", "is_store"},
    "bv+bv": {"is_app", "is_bv", "is_expr"},
    "BitVecVal": {"is_app", "is_bv", "is_const", "is_expr"},
    "f(x)": {"is_app", "is_expr", "is_int"},
    "ForAll": {"is_bool", "is_expr", "is_quantifier"},
    "BoolTrue": {"is_app", "is_bool", "is_const", "is_expr", "is_true"},
    "BoolFalse": {"is_app", "is_bool", "is_const", "is_expr", "is_false"},
    "String": {"is_app", "is_const", "is_expr", "is_string"},
    "StringVal": {"is_app", "is_const", "is_expr", "is_string"},
    # --- documented sound-canonicalization normal forms (AY-stored term) ------
    # z3py keeps the surface operator; AY stores an equivalent normal form, so
    # the predicate honestly reflects AY's term. z3py's verdict is in the
    # comment for each.
    "x>y": {"is_app", "is_bool", "is_expr", "is_lt"},   # z3py: is_gt  ((< y x))
    "x>=y": {"is_app", "is_bool", "is_expr", "is_le"},  # z3py: is_ge  ((<= y x))
    # Distinct(x, y, z) now matches z3py EXACTLY: even though AY stores the
    # eager-expanded `and`, the wrapper carries a distinct marker so the
    # introspection surface presents it as `distinct` (is_distinct True, NOT
    # is_and) — so this is no longer a CANON divergence (see CANON below).
    "Distinct3": {"is_app", "is_bool", "is_expr", "is_distinct"},
    "x!=y": {"is_app", "is_bool", "is_expr", "is_not"},  # z3py: is_distinct
    "x-y": {"is_add", "is_app", "is_expr", "is_int"},   # z3py: is_sub  ((+ x (- y)))
    "-x": {"is_app", "is_expr", "is_int"},              # z3py: same preds; decl kind differs
    "Implies": {"is_app", "is_bool", "is_expr", "is_or"},  # z3py: (no extra); AY -> (or q (not p))
}

# Expressions AY stores in a normal form differing from z3py's surface form.
# (Distinct3 is NOT here: its wrapper's distinct marker makes the introspection
# surface match z3py exactly, so it is cross-checked for equality below.)
CANON = {"x>y", "x>=y", "x!=y", "x-y", "Implies", "-x"}


# ---------------------------------------------------------------------------
# Predicate surface
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("label", list(AYZ3_EXPECTED))
def test_predicate_verdicts_are_honest(scope, label):
    """Each predicate reflects AY's actual stored term (self-contained)."""
    corpus = _build(z)
    got = _true_preds(z, corpus[label])
    assert got == AYZ3_EXPECTED[label], f"{label}: {got}"


@pytest.mark.usefixtures("required_reference_z3")
@pytest.mark.parametrize("label", list(AYZ3_EXPECTED))
def test_predicates_cross_check_z3py(scope, label):
    """Side-by-side vs z3py: exact match, or a documented CANON divergence."""
    a_corpus, z_corpus = _build(z), _build(_z3)
    a_preds = _true_preds(z, a_corpus[label])
    z_preds = _true_preds(_z3, z_corpus[label])
    if label in CANON:
        # AY's honest verdict is asserted; where it actually differs from z3py
        # (all but -x, which diverges only in decl kind) the divergence is the
        # documented sound canonicalization, not a bug.
        assert a_preds == AYZ3_EXPECTED[label]
    else:
        assert a_preds == z_preds, f"{label}: ayz3={a_preds} z3py={z_preds}"


# ---------------------------------------------------------------------------
# Acceptance corpus (task B-3), self-contained
# ---------------------------------------------------------------------------

def test_acceptance_add_expr(scope):
    x, y = z.Int("x"), z.Int("y")
    e = x + 2 * y
    assert z.is_add(e)
    assert z.is_app(e)
    assert z.is_int(e)
    assert e.decl().name() == "+"
    assert e.decl().kind() == 518  # Z3_OP_ADD
    assert e.num_args() == 2
    assert e.arg(0).sexpr() == "x"
    kids = e.children()
    assert len(kids) == 2
    assert kids[0].sexpr() == "x"
    # children[1] is `2*y` up to AY's commutative operand-order canonicalization.
    assert z.is_mul(kids[1])


def test_acceptance_and_select_bv(scope):
    p, q = z.Bool("p"), z.Bool("q")
    assert z.is_and(p & q)
    assert z.is_and(z.And(p, q))
    a, i = z.Array("a", z.IntSort(), z.IntSort()), z.Int("i")
    sel = z.Select(a, i)
    assert z.is_select(sel)
    assert sel.decl().name() == "select"
    assert z.is_bv(z.BitVecVal(5, 8))
    assert z.is_bv_value(z.BitVecVal(5, 8))
    assert z.is_quantifier(z.ForAll([z.Int("w")], z.Int("w") == 0))


def test_acceptance_funcdecl(scope):
    f = z.Function("f", z.IntSort(), z.RealSort(), z.BoolSort())
    assert f.name() == "f"
    assert f.arity() == 2
    assert f.domain(0).kind == "Int"
    assert f.domain(1).kind == "Real"
    assert f.range().kind == "Bool"
    assert f.kind() == 49167  # Z3_OP_UNINTERPRETED (Z3 5.0.0)
    assert f.params() == []
    # The decl recovered from an application is the same declaration.
    app = f(z.Int("u"), z.Real("w"))
    assert app.decl().name() == "f"
    assert app.decl().arity() == 2


@pytest.mark.usefixtures("required_reference_z3")
def test_acceptance_funcdecl_cross_check(scope):
    f = z.Function("f", z.IntSort(), z.RealSort(), z.BoolSort())
    zf = _z3.Function("f", _z3.IntSort(), _z3.RealSort(), _z3.BoolSort())
    assert f.name() == zf.name()
    assert f.arity() == zf.arity()
    assert f.kind() == zf.kind()
    assert str(f.domain(0)) == str(zf.domain(0))
    assert str(f.range()) == str(zf.range())


# ---------------------------------------------------------------------------
# Declaration / children accessors
# ---------------------------------------------------------------------------

def test_declared_const_decl(scope):
    x = z.Int("x")
    d = x.decl()
    assert d.name() == "x"
    assert d.arity() == 0
    assert d.kind() == 49167  # a declared constant is a 0-arity uninterpreted decl
    assert x.num_args() == 0
    assert x.children() == []
    assert x.sexpr() == "x"


def test_numeral_decls(scope):
    assert z.IntVal(7).decl().name() == "Int"
    assert z.IntVal(7).decl().kind() == 512   # Z3_OP_ANUM
    assert z.RealVal("1/2").decl().name() == "Real"
    assert z.BitVecVal(5, 8).decl().name() == "bv"
    assert z.BitVecVal(5, 8).decl().kind() == 1024  # Z3_OP_BNUM
    assert z.BoolVal(True).decl().name() == "true"
    assert z.BoolVal(True).decl().kind() == 256   # Z3_OP_TRUE
    assert z.BoolVal(False).decl().name() == "false"
    assert z.BoolVal(False).decl().kind() == 257  # Z3_OP_FALSE


@pytest.mark.usefixtures("required_reference_z3")
def test_numeral_decls_cross_check(scope):
    for a, b in [
        (z.IntVal(7), _z3.IntVal(7)),
        (z.RealVal("1/2"), _z3.RealVal("1/2")),
        (z.BitVecVal(5, 8), _z3.BitVecVal(5, 8)),
        (z.BoolVal(True), _z3.BoolVal(True)),
        (z.BoolVal(False), _z3.BoolVal(False)),
    ]:
        assert a.decl().name() == b.decl().name()
        assert a.decl().kind() == b.decl().kind()


def test_children_and_args(scope):
    x, y = z.Int("x"), z.Int("y")
    e = z.And(x < y, x == y)
    assert e.num_args() == 2
    assert z.is_lt(e.arg(0))
    assert z.is_eq(e.arg(1))
    assert [c.sexpr() for c in e.children()] == [e.arg(0).sexpr(), e.arg(1).sexpr()]
    with pytest.raises(IndexError):
        e.arg(2)


def test_arg_hash_cons_identity(scope):
    # A shared sub-term recovered via arg() is the same declared constant.
    x, y = z.Int("x"), z.Int("y")
    e = x + 2 * y
    assert e.arg(0).decl().name() == "x"
    assert z.is_const(e.arg(0))


# ---------------------------------------------------------------------------
# Quantifier accessors
# ---------------------------------------------------------------------------

def test_quantifier_accessors(scope):
    x, y = z.Int("x"), z.Int("y")
    qf = z.ForAll([x, y], x == y)
    assert z.is_quantifier(qf)
    assert not z.is_app(qf)
    assert qf.is_forall()
    assert qf.num_vars() == 2
    assert qf.var_name(0) == "x"
    assert qf.var_sort(0).kind == "Int"
    assert qf.var_name(1) == "y"
    assert z.is_eq(qf.body())
    assert len(qf.children()) == 1

    qe = z.Exists([x], x > 0)
    assert z.is_quantifier(qe)
    assert not qe.is_forall()


# ---------------------------------------------------------------------------
# Documented sound-canonicalization divergences (kept intentional)
# ---------------------------------------------------------------------------

def test_canonicalization_gt_flips_to_lt(scope):
    # AY orients comparisons to </<= : `x > y` is stored as `(< y x)`.
    x, y = z.Int("x"), z.Int("y")
    e = x > y
    assert z.is_lt(e) and not z.is_gt(e)
    assert e.decl().name() == "<"
    assert [c.sexpr() for c in e.children()] == ["y", "x"]


def test_canonicalization_sub_folds_to_add(scope):
    x, y = z.Int("x"), z.Int("y")
    e = x - y
    assert z.is_add(e) and not z.is_sub(e)
    assert e.decl().name() == "+"


def test_canonicalization_ne_folds_to_not_eq(scope):
    x, y = z.Int("x"), z.Int("y")
    e = x != y
    assert z.is_not(e) and not z.is_distinct(e)
    assert z.is_eq(e.arg(0))


@pytest.mark.usefixtures("required_reference_z3")
def test_canonicalization_divergences_are_real():
    # Confirm z3py genuinely classifies these differently, so the CANON handling
    # is compensating for a real, sound normal-form divergence (not dead code).
    zx, zy = _z3.Int("x"), _z3.Int("y")
    assert _z3.is_gt(zx > zy) and not _z3.is_lt(zx > zy)
    assert _z3.is_sub(zx - zy)
    assert _z3.is_distinct(zx != zy)


# ---------------------------------------------------------------------------
# is_var honesty (AY constant-style quantifiers expose no de-Bruijn variables)
# ---------------------------------------------------------------------------

def test_is_var_always_false(scope):
    x = z.Int("x")
    assert not z.is_var(x)
    assert not z.is_var(x + 1)
    qf = z.ForAll([x], x == 0)
    # The body's variable is a declared constant, not a de-Bruijn var.
    assert not z.is_var(qf.body().arg(0))


# ---------------------------------------------------------------------------
# Broadened parity corpus (B-3 rework): the three cases the original 29-expr
# corpus missed, plus BV bitwise. Division is SORT-POLYMORPHIC in z3 (and now in
# AY): `x / y` for Int x,y is the SMT-LIB integer-division operator `div`
# (Z3_OP_IDIV=523, is_idiv, NOT is_div); for Real it is `/` (Z3_OP_DIV=522,
# is_div). If/ITE's canonical z3py decl NAME is "if" (kind Z3_OP_ITE=260). Each
# case pins decl kind + name + the relevant is_* predicate, side-by-side vs real
# z3py.
# ---------------------------------------------------------------------------

# label -> builder(mod): the same construction in either ayz3 or z3py.
_PARITY_BUILDERS = {
    "int_div":  lambda m: m.Int("x") / m.Int("y"),
    "real_div": lambda m: m.Real("r") / m.Real("s"),
    "ite":      lambda m: m.If(m.Bool("c"), m.Int("x"), m.Int("y")),
    "bvand":    lambda m: m.BitVec("a", 8) & m.BitVec("b", 8),
    "bvor":     lambda m: m.BitVec("a", 8) | m.BitVec("b", 8),
    "bvxor":    lambda m: m.BitVec("a", 8) ^ m.BitVec("b", 8),
}

# Expected (name, decl_kind) pairs, also cross-checked with z3py 4.15.4.
_PARITY_EXPECTED = {
    "int_div":  ("div", 523),    # Z3_OP_IDIV
    "real_div": ("/",   522),    # Z3_OP_DIV
    "ite":      ("if",  260),    # Z3_OP_ITE
    "bvand":    ("bvand", 1049),  # Z3_OP_BAND
    "bvor":     ("bvor",  1050),  # Z3_OP_BOR
    "bvxor":    ("bvxor", 1052),  # Z3_OP_BXOR
}


@pytest.mark.parametrize("label", list(_PARITY_BUILDERS))
def test_broadened_corpus_self_contained(scope, label):
    """Decl kind + name + is_div/is_idiv, hardcoded to z3py's verdict."""
    e = _PARITY_BUILDERS[label](z)
    assert (e.decl().name(), e.decl().kind()) == _PARITY_EXPECTED[label]
    if label == "int_div":
        # Integer division is is_idiv, and (matching z3py) NOT is_div.
        assert z.is_idiv(e)
        assert not z.is_div(e)
    if label == "real_div":
        # Real division is is_div, and NOT is_idiv.
        assert z.is_div(e)
        assert not z.is_idiv(e)
    if label == "ite":
        assert z.is_app_of(e, 260)  # Z3_OP_ITE


@pytest.mark.usefixtures("required_reference_z3")
@pytest.mark.parametrize("label", list(_PARITY_BUILDERS))
def test_broadened_corpus_cross_check(scope, label):
    """Side-by-side vs z3py: decl kind + name + is_div/is_idiv all match, 0 DIFF."""
    a = _PARITY_BUILDERS[label](z)
    b = _PARITY_BUILDERS[label](_z3)
    assert a.decl().kind() == b.decl().kind(), f"{label}: kind"
    assert a.decl().name() == b.decl().name(), f"{label}: name"
    assert z.is_div(a) == _z3.is_div(b), f"{label}: is_div"
    assert z.is_idiv(a) == _z3.is_idiv(b), f"{label}: is_idiv"


def test_int_vs_real_division_are_distinct_operators(scope):
    """The Int/Real division split is real: same `/` syntax, different decl."""
    idiv = z.Int("x") / z.Int("y")
    rdiv = z.Real("r") / z.Real("s")
    assert idiv.decl().kind() != rdiv.decl().kind()
    assert idiv.decl().kind() == 523 and idiv.decl().name() == "div"
    assert rdiv.decl().kind() == 522 and rdiv.decl().name() == "/"


def test_ite_decl_name_is_if(scope):
    """If/ITE reports z3py's canonical decl name 'if' while keeping kind ITE."""
    e = z.If(z.Bool("c"), z.Int("x"), z.Int("y"))
    assert e.decl().name() == "if"
    assert e.decl().kind() == 260  # Z3_OP_ITE
    assert e.num_args() == 3

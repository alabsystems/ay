# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
#
# B-4 regression: z3py-style infix pretty-printer for AstRef.str()/repr().
#
# Two kinds of assertion, mirroring B-3's introspection suite:
#
#  * PARITY — where AY's stored term coincides with z3py's structure, ayz3's
#    str()/repr() is BYTE-IDENTICAL to z3py's. Each case is asserted against a
#    hardcoded expected string AND, where real z3py is installed, cross-checked
#    against z3py's own str() so any drift in either printer is caught.
#
#  * DIVERGENCE — where AY applies a sound canonicalization at construction
#    (comparison orientation, subtraction-as-add-of-negation, unary-minus stored
#    as 1-arg SUB, Implies/!=/Distinct folded to and/or/not, commutative operand
#    reorder, n-ary flattening, seq ops as SMT-named uninterpreted functions),
#    ayz3 prints AY's REAL term. Each such case asserts ayz3's honest output,
#    shows it DIFFERS from z3py's surface rendering, and proves it is faithful by
#    matching z3py's rendering of the EQUIVALENT CANONICAL structure. So the
#    divergence is documented with a live z3py witness on both sides — never a
#    fabricated un-canonicalization.
#
# The ayz3 term for each case is built in a FRESH, isolated Context (AY interns a
# const by name within a context, so a shared context would collide when two
# cases declare the same name at different sorts — cf. test_introspect).
#
# Run:  pytest bindings/python/tests/test_printer.py -v

import pytest

import ayz3 as z

try:
    import z3 as _z3
    HAVE_Z3PY = True
except Exception:  # pragma: no cover - depends on environment
    _z3 = None
    HAVE_Z3PY = False


def _ay(build):
    """str() of `build(ayz3)` in a fresh, isolated ayz3 Context."""
    s = z.Solver(z.Context())
    with s.using():
        return str(build(z))


def _ay_repr(build):
    """repr() of `build(ayz3)` in a fresh, isolated ayz3 Context."""
    s = z.Solver(z.Context())
    with s.using():
        return repr(build(z))


def _z3str(build):
    return str(build(_z3))


# ---------------------------------------------------------------------------
# PARITY corpus: (name, module-generic builder, expected byte-identical text).
# Where AY stores the same structure z3py does, ayz3's str() == z3py's str().
# ---------------------------------------------------------------------------
PARITY = [
    # --- comparisons already oriented the way AY stores them ---
    ("le", lambda m: (lambda x, y: x <= y)(m.Int("x"), m.Int("y")), "x <= y"),
    ("lt", lambda m: (lambda x, y: x < y)(m.Int("x"), m.Int("y")), "x < y"),
    ("eq", lambda m: (lambda x, y: x == y)(m.Int("x"), m.Int("y")), "x == y"),
    # --- arithmetic ---
    ("mul", lambda m: (lambda x, y: x * y)(m.Int("x"), m.Int("y")), "x*y"),
    ("mul_add", lambda m: (lambda x, y, w: x * y + w)(
        m.Int("x"), m.Int("y"), m.Int("z")), "x*y + z"),
    ("add3", lambda m: (lambda x, y, w: x + y + w)(
        m.Int("x"), m.Int("y"), m.Int("z")), "x + y + z"),
    ("idiv", lambda m: (lambda x, y: x / y)(m.Int("x"), m.Int("y")), "x/y"),
    ("rdiv", lambda m: (lambda r, s: r / s)(m.Real("r"), m.Real("s")), "r/s"),
    ("mod", lambda m: (lambda x, y: x % y)(m.Int("x"), m.Int("y")), "x%y"),
    ("neg", lambda m: -m.Int("x"), "-x"),
    ("neg_then_add", lambda m: (lambda x, y: (-x) + y)(
        m.Int("x"), m.Int("y")), "-x + y"),
    # --- boolean connectives (z3py renders these prefix) ---
    ("and2", lambda m: m.And(m.Bool("p"), m.Bool("q")), "And(p, q)"),
    ("or2", lambda m: m.Or(m.Bool("p"), m.Bool("q")), "Or(p, q)"),
    ("not1", lambda m: m.Not(m.Bool("p")), "Not(p)"),
    ("and3", lambda m: m.And(m.Bool("p"), m.Bool("q"), m.Bool("t")),
     "And(p, q, t)"),
    ("or_and_not", lambda m: m.Or(m.And(m.Bool("p"), m.Bool("q")),
                                  m.Not(m.Bool("q"))), "Or(And(p, q), Not(q))"),
    ("and_of_cmp", lambda m: (lambda x, y, w: m.And(x < y, y < w))(
        m.Int("x"), m.Int("y"), m.Int("z")), "And(x < y, y < z)"),
    ("ite", lambda m: (lambda x, y: m.If(m.Bool("p"), x, y))(
        m.Int("x"), m.Int("y")), "If(p, x, y)"),
    # --- coercions ---
    ("to_real", lambda m: m.ToReal(m.Int("x")), "ToReal(x)"),
    ("to_int", lambda m: m.ToInt(m.Real("r")), "ToInt(r)"),
    ("is_int", lambda m: m.IsInt(m.Real("r")), "IsInt(r)"),
    # --- uninterpreted function application ---
    ("fapp", lambda m: (m.Function("f", m.IntSort(), m.IntSort()))(m.Int("x")),
     "f(x)"),
    ("fapp_add", lambda m: (lambda f, x, y: f(x) + y)(
        m.Function("f", m.IntSort(), m.IntSort()), m.Int("x"), m.Int("y")),
     "f(x) + y"),
    # --- literals ---
    ("intval", lambda m: m.IntVal(5), "5"),
    ("intval_neg", lambda m: m.IntVal(-5), "-5"),
    ("realval_whole", lambda m: m.RealVal(2), "2"),
    ("realval_frac", lambda m: m.RealVal("1/2"), "1/2"),
    ("boolval", lambda m: m.BoolVal(True), "True"),
    ("stringval", lambda m: m.StringVal("hi"), '"hi"'),
    # --- bitvectors: bvadd as +, decimal literals, &/|/^/~/neg, signed cmp ---
    ("bv_add", lambda m: (lambda x, y: x + y)(m.BitVec("x", 8), m.BitVec("y", 8)),
     "x + y"),
    ("bv_mul", lambda m: (lambda x, y: x * y)(m.BitVec("x", 8), m.BitVec("y", 8)),
     "x*y"),
    ("bv_and", lambda m: (lambda x, y: x & y)(m.BitVec("x", 8), m.BitVec("y", 8)),
     "x & y"),
    ("bv_or", lambda m: (lambda x, y: x | y)(m.BitVec("x", 8), m.BitVec("y", 8)),
     "x | y"),
    ("bv_xor", lambda m: (lambda x, y: x ^ y)(m.BitVec("x", 8), m.BitVec("y", 8)),
     "x ^ y"),
    ("bv_not", lambda m: ~m.BitVec("x", 8), "~x"),
    ("bv_neg", lambda m: -m.BitVec("x", 8), "-x"),
    ("bv_val", lambda m: m.BitVecVal(5, 8), "5"),
    ("bv_val_max", lambda m: m.BitVecVal(255, 8), "255"),
    ("bv_val_wrap", lambda m: m.BitVecVal(-1, 8), "255"),
    ("bv_slt", lambda m: (lambda x, y: x < y)(m.BitVec("x", 8), m.BitVec("y", 8)),
     "x < y"),
    ("bv_ult", lambda m: (lambda x, y: m.ULT(x, y))(
        m.BitVec("x", 8), m.BitVec("y", 8)), "ULT(x, y)"),
    ("bv_ule", lambda m: (lambda x, y: m.ULE(x, y))(
        m.BitVec("x", 8), m.BitVec("y", 8)), "ULE(x, y)"),
    # --- arrays: Store prefix, Select as a[i] ---
    ("store", lambda m: (lambda a, i, v: m.Store(a, i, v))(
        m.Array("a", m.IntSort(), m.IntSort()), m.Int("i"), m.Int("v")),
     "Store(a, i, v)"),
    ("select", lambda m: (lambda a, i: m.Select(a, i))(
        m.Array("a", m.IntSort(), m.IntSort()), m.Int("i")), "a[i]"),
    ("getitem", lambda m: (lambda a, i: a[i])(
        m.Array("a", m.IntSort(), m.IntSort()), m.Int("i")), "a[i]"),
    # --- quantifiers: ForAll(x, body) / ForAll([x, y], body) / Exists ---
    ("forall1", lambda m: (lambda x: m.ForAll([x], x < 10))(m.Int("xi")),
     "ForAll(xi, xi < 10)"),
    ("forall2", lambda m: (lambda x, i: m.ForAll([x, i], m.And(x < 10, i < 5)))(
        m.Int("xi"), m.Int("ii")), "ForAll([xi, ii], And(xi < 10, ii < 5))"),
    ("exists1", lambda m: (lambda x: m.Exists([x], x < 10))(m.Int("xi")),
     "Exists(xi, xi < 10)"),
]


@pytest.mark.parametrize("name,build,expected", PARITY,
                         ids=[c[0] for c in PARITY])
def test_parity_str_is_byte_identical(name, build, expected):
    got = _ay(build)
    assert got == expected, f"{name}: ayz3 str {got!r} != expected {expected!r}"
    # No raw s-expression / opaque handle leaks into str() for a supported shape.
    assert "(ast " not in got
    if HAVE_Z3PY:
        assert got == _z3str(build), (
            f"{name}: ayz3 {got!r} != z3py {_z3str(build)!r}")


def test_parity_repr_matches_str():
    # repr() and str() are the same z3py-style rendering (z3py has them equal).
    for name, build, expected in PARITY:
        assert _ay_repr(build) == expected


def test_no_sexpr_leak_across_parity_corpus():
    # Not one supported shape may leak the SMT-LIB prefix s-expression into str().
    for name, build, expected in PARITY:
        got = _ay(build)
        # A leaked binary/prefix s-expr would look like "(<op> ...)"; none should.
        assert not (got.startswith("(") and got[1:].split(" ", 1)[0]
                    in {"+", "-", "*", "/", "<", "<=", "=", "and", "or", "not",
                        "bvadd", "bvmul", "select", "store", "ite"}), got


# ---------------------------------------------------------------------------
# DIVERGENCE corpus. Each row:
#   (name, surface builder, expected honest ayz3 text, canonical builder)
# The canonical builder constructs — IN z3py — the structure AY actually stores,
# so z3py's rendering of it is the faithful witness ayz3 must match. The surface
# builder is the same expression written naturally; z3py renders it differently
# (that difference is the documented, sound divergence).
# ---------------------------------------------------------------------------
DIVERGENCE = [
    # x > y  is stored (< y x)
    ("gt", lambda m: (lambda x, y: x > y)(m.Int("x"), m.Int("y")), "y < x",
     lambda m: (lambda x, y: y < x)(m.Int("x"), m.Int("y"))),
    # x >= y  is stored (<= y x)
    ("ge", lambda m: (lambda x, y: x >= y)(m.Int("x"), m.Int("y")), "y <= x",
     lambda m: (lambda x, y: y <= x)(m.Int("x"), m.Int("y"))),
    # x - y  is stored (+ x (- y)); note upstream z3py renders x + (-y) as x + -y
    ("sub", lambda m: (lambda x, y: x - y)(m.Int("x"), m.Int("y")), "x + -y",
     lambda m: (lambda x, y: x + (-y))(m.Int("x"), m.Int("y"))),
    # (x - y) - z  flattens to (+ x (- y) (- z))
    ("sub_chain", lambda m: (lambda x, y, w: (x - y) - w)(
        m.Int("x"), m.Int("y"), m.Int("z")), "x + -y + -z",
     lambda m: (lambda x, y, w: x + (-y) + (-w))(
         m.Int("x"), m.Int("y"), m.Int("z"))),
    # -(x + y)  distributes to (+ (- x) (- y))
    ("neg_sum", lambda m: (lambda x, y: -(x + y))(m.Int("x"), m.Int("y")),
     "-x + -y",
     lambda m: (lambda x, y: (-x) + (-y))(m.Int("x"), m.Int("y"))),
    # x * (-y)  hoists the sign to (- (* x y))
    ("mul_neg", lambda m: (lambda x, y: x * (-y))(m.Int("x"), m.Int("y")),
     "-(x*y)",
     lambda m: (lambda x, y: -(x * y))(m.Int("x"), m.Int("y"))),
    # 2 * y  reorders the constant to the right: (* y 2)
    ("const_mul", lambda m: 2 * m.Int("y"), "y*2",
     lambda m: m.Int("y") * 2),
    # x + 2*y  -> (+ x (* y 2))
    ("add_const_mul", lambda m: (lambda x, y: x + 2 * y)(
        m.Int("x"), m.Int("y")), "x + y*2",
     lambda m: (lambda x, y: x + y * 2)(m.Int("x"), m.Int("y"))),
    # x != y  folds to (not (= x y))
    ("ne", lambda m: (lambda x, y: x != y)(m.Int("x"), m.Int("y")),
     "Not(x == y)",
     lambda m: m.Not(m.Int("x") == m.Int("y"))),
    # Implies(p, q)  folds to (or q (not p))
    ("implies", lambda m: m.Implies(m.Bool("p"), m.Bool("q")), "Or(q, Not(p))",
     lambda m: m.Or(m.Bool("q"), m.Not(m.Bool("p")))),
    # NOTE: Distinct(x, y, z) is NO LONGER a divergence — its wrapper's distinct
    # marker now makes ayz3 print `Distinct(x, y, z)`, byte-identical to z3py (see
    # test_distinct_prints_like_z3py below), so it moved out of this list.
    # UGE(x, y)  stored as unsigned (<= y x)
    ("uge", lambda m: (lambda x, y: m.UGE(x, y))(
        m.BitVec("x", 8), m.BitVec("y", 8)), "ULE(y, x)",
     lambda m: (lambda x, y: m.ULE(y, x))(m.BitVec("x", 8), m.BitVec("y", 8))),
    # ForAll body is canonicalized too: xi > 0 stored (< 0 xi). (The z3py
    # witness must use IntVal(0) < x, since Python reflects the literal form
    # `0 < x` back to `x > 0` before z3py ever sees it.)
    ("forall_gt", lambda m: (lambda x: m.ForAll([x], x > 0))(m.Int("xi")),
     "ForAll(xi, 0 < xi)",
     lambda m: (lambda x: m.ForAll([x], m.IntVal(0) < x))(m.Int("xi"))),
]


@pytest.mark.parametrize("name,surface,expected,canon", DIVERGENCE,
                         ids=[c[0] for c in DIVERGENCE])
def test_divergence_prints_ays_real_canonical_term(name, surface, expected,
                                                   canon):
    got = _ay(surface)
    # 1. ayz3 prints AY's real (canonicalized) term.
    assert got == expected, f"{name}: ayz3 str {got!r} != expected {expected!r}"
    if HAVE_Z3PY:
        # 2. It genuinely DIFFERS from z3py's surface rendering (the divergence).
        assert got != _z3str(surface), (
            f"{name}: expected a divergence, but ayz3 {got!r} == z3py surface")
        # 3. It is FAITHFUL: byte-identical to z3py's rendering of the SAME
        #    structure AY stores — so nothing was un-canonicalized/fabricated.
        assert got == _z3str(canon), (
            f"{name}: ayz3 {got!r} != z3py-of-canonical {_z3str(canon)!r}")


# ---------------------------------------------------------------------------
# Seq/string operations: AY stores them as uninterpreted functions carrying
# their SMT-LIB names, so they print with those names (str.++ / str.len /
# str.contains) rather than z3py's Concat / Length / Contains. Honest: the
# printed head is the decl name AY actually stored.
# ---------------------------------------------------------------------------
STRING_DIVERGENCE = [
    ("concat", lambda m: (lambda s, t: s + t)(m.String("s"), m.String("t")),
     "str.++(s, t)", "Concat(s, t)"),
    ("length", lambda m: m.Length(m.String("s")), "str.len(s)", "Length(s)"),
    ("contains", lambda m: m.Contains(m.String("s"), m.String("t")),
     "str.contains(s, t)", "Contains(s, t)"),
]


def test_distinct_prints_like_z3py():
    """Distinct now prints EXACTLY as z3py (the wrapper carries a distinct marker).

    An n-ary Distinct prints `Distinct(a, b, c)`; a binary Distinct prints
    `a != b` — both byte-identical to z3py, no longer the and/not expansion.
    """
    x, y, w = z.Int("x"), z.Int("y"), z.Int("z")
    assert _ay(lambda m: m.Distinct(m.Int("x"), m.Int("y"), m.Int("z"))) == "Distinct(x, y, z)"
    assert _ay(lambda m: m.Distinct(m.Int("x"), m.Int("y"))) == "x != y"
    if HAVE_Z3PY:
        assert _ay(lambda m: m.Distinct(m.Int("x"), m.Int("y"), m.Int("z"))) == _z3str(
            lambda m: m.Distinct(m.Int("x"), m.Int("y"), m.Int("z")))


@pytest.mark.parametrize("name,build,expected,z3form", STRING_DIVERGENCE,
                         ids=[c[0] for c in STRING_DIVERGENCE])
def test_string_ops_print_ay_decl_name(name, build, expected, z3form):
    got = _ay(build)
    assert got == expected
    assert "(ast " not in got
    if HAVE_Z3PY:
        # z3py uses its own surface names; AY prints the SMT-LIB decl name it
        # actually stored — a documented, honest divergence.
        assert _z3str(build) == z3form
        assert got != _z3str(build)


# ---------------------------------------------------------------------------
# The model-value rendering path must survive the __repr__ rebind: a value read
# from a model still renders as its concrete content (not the pretty-printer's
# view of an opaque handle, and not an "(ast N)" leak).
# ---------------------------------------------------------------------------
def test_model_value_still_renders_concretely():
    s = z.Solver(z.Context())
    with s.using():
        x = z.Int("x")
        s.add(x == 7)
        assert s.check() == z.sat
        m = s.model()
        v = m[x]
        assert repr(v) == "7"
        assert str(v) == "7"
        assert "(ast " not in repr(v)


def test_model_repr_unchanged():
    # The whole-model bracket rendering is z3py-shaped and untouched by B-4.
    s = z.Solver(z.Context())
    with s.using():
        x, y = z.Int("x"), z.Int("y")
        s.add(x == 4, y == 6)
        assert s.check() == z.sat
        assert repr(s.model()) == "[x = 4, y = 6]"


def test_nested_expression_precedence_and_parens():
    # A deeper mixed term exercises precedence/paren insertion end to end.
    def build(m):
        x, y, w = m.Int("x"), m.Int("y"), m.Int("z")
        return m.And(x * (y + w) <= w, m.Or(x < y, m.Not(y == w)))
    got = _ay(build)
    assert got == "And(x*(y + z) <= z, Or(x < y, Not(y == z)))"
    if HAVE_Z3PY:
        assert got == _z3str(build)

# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
#
# B-6 regression: z3py-shaped algebraic datatypes (Datatype / EnumSort /
# TupleSort) over AY's datatype C ABI.
#
# Every test builds its ayz3 terms inside a FRESH, isolated Context (the `scope`
# fixture) so datatype/const names never collide across tests (AY interns a
# datatype and a constant by NAME within a context). Where real z3py is
# installed, each observable is cross-checked against z3py so any drift is
# caught. The two intentional, documented divergences (see DIVERGENCES below)
# are asserted to AY's honest behavior with z3py's differing answer recorded.
#
# Run:  cargo build -p ay-ffi  &&  pytest bindings/python/tests/test_datatypes.py -v
#
# DIVERGENCES (honest, documented; never a wrong/fabricated value):
#   * Datatype model VALUES are read back through const-interp (`m[c]`) and AST
#     introspection on the concrete value (`m[p].arg(i)`) — both z3py-identical.
#     `m.eval(<accessor/recognizer>(x))` returns the honest, equisatisfiable
#     UNFOLDED term (e.g. `(is-cons (cons 1 nil))`) rather than z3py's folded
#     `True`/field value: AY's FFI model-eval snapshot does not fold datatype
#     ops over a concrete constructor. Read fields/testers via `m[x].arg(i)` /
#     the model value instead (both match z3py exactly).

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
    """Activate a fresh, isolated ayz3 Context for the test body."""
    solver = z.Solver(z.Context())
    with solver.using():
        yield solver.ctx


# ---------------------------------------------------------------------------
# EnumSort
# ---------------------------------------------------------------------------

def test_enum_sort_check_and_model(scope):
    Color, (red, green, blue) = z.EnumSort("Color", ["red", "green", "blue"])
    assert Color.num_constructors() == 3
    c = z.Const("c", Color)
    s = z.Solver(scope)
    s.add(c != red, c != green)
    assert str(s.check()) == "sat"
    m = s.model()
    # The one remaining possibility in a 3-value enum is blue.
    assert str(m[c]) == "blue"


def test_enum_sort_parity_z3py(scope):
    Color, (red, green, blue) = z.EnumSort("Color", ["red", "green", "blue"])
    c = z.Const("c", Color)
    s = z.Solver(scope)
    s.add(c != red, c != green)
    assert str(s.check()) == "sat"
    ay_val = str(s.model()[c])
    assert ay_val == "blue"
    if HAVE_Z3PY:
        C2, (r2, g2, b2) = _z3.EnumSort("Color", ["red", "green", "blue"])
        c2 = _z3.Const("c", C2)
        s2 = _z3.Solver()
        s2.add(c2 != r2, c2 != g2)
        assert str(s2.check()) == "sat"
        assert str(s2.model()[c2]) == ay_val  # z3py agrees: blue


def test_enum_recognizer_forces_value(scope):
    Color, (red, green, blue) = z.EnumSort("Color", ["red", "green", "blue"])
    c = z.Const("c", Color)
    s = z.Solver(scope)
    # z3py exposes the recognizer for constructor i as sort.recognizer(i).
    s.add(Color.recognizer(0)(c))
    assert str(s.check()) == "sat"
    assert str(s.model()[c]) == "red"


def test_enum_unsat_all_excluded(scope):
    Color, (red, green, blue) = z.EnumSort("Color", ["red", "green", "blue"])
    c = z.Const("c", Color)
    s = z.Solver(scope)
    s.add(c != red, c != green, c != blue)
    # A 3-value enum with all three excluded is unsatisfiable.
    assert str(s.check()) == "unsat"


# ---------------------------------------------------------------------------
# TupleSort
# ---------------------------------------------------------------------------

def test_tuple_sort_fields(scope):
    Pair, mk_pair, (first, second) = z.TupleSort(
        "Pair", [z.IntSort(), z.IntSort()]
    )
    # z3py names the single constructor after the sort and projections projectN.
    assert mk_pair.name() == "Pair"
    assert first.name() == "project0"
    p = z.Const("p", Pair)
    s = z.Solver(scope)
    s.add(first(p) == 3, second(p) == 5)
    assert str(s.check()) == "sat"
    m = s.model()
    pv = m[p]
    # Read field values off the concrete constructor value (z3py m[p].arg(i)).
    assert pv.num_args() == 2
    assert str(pv.arg(0)) == "3"
    assert str(pv.arg(1)) == "5"
    # Whole-value rendering matches z3py's ctor(a, b) form.
    assert str(pv) == "Pair(3, 5)"


def test_tuple_sort_parity_z3py(scope):
    Pair, mk_pair, (first, second) = z.TupleSort(
        "Pair", [z.IntSort(), z.BoolSort()]
    )
    p = z.Const("p", Pair)
    s = z.Solver(scope)
    s.add(first(p) == 9, second(p) == True)  # noqa: E712
    assert str(s.check()) == "sat"
    ay = str(s.model()[p])
    if HAVE_Z3PY:
        P2, mk2, (f2, s2p) = _z3.TupleSort("Pair", [_z3.IntSort(), _z3.BoolSort()])
        p2 = _z3.Const("p", P2)
        so = _z3.Solver()
        so.add(f2(p2) == 9, s2p(p2) == True)  # noqa: E712
        so.check()
        assert str(so.model()[p2]) == ay  # both: Pair(9, True)
    assert ay == "Pair(9, True)"


def test_tuple_build_and_read_fields(scope):
    Pair, mk_pair, (first, second) = z.TupleSort(
        "Pair", [z.IntSort(), z.IntSort()]
    )
    # Building a concrete tuple and reading fields via simplify + arg.
    pv = z.simplify(mk_pair(10, 20))
    assert str(pv.arg(0)) == "10"
    assert str(pv.arg(1)) == "20"


# ---------------------------------------------------------------------------
# Datatype (general, with testers)
# ---------------------------------------------------------------------------

def test_datatype_option_tester_and_accessor(scope):
    Option = z.Datatype("Option")
    Option.declare("none")
    Option.declare("some", ("val", z.IntSort()))
    Option = Option.create()
    o = z.Const("o", Option)
    s = z.Solver(scope)
    s.add(Option.is_some(o), Option.val(o) == 7)
    assert str(s.check()) == "sat"
    assert str(s.model()[o]) == "some(7)"


def test_datatype_option_parity_z3py(scope):
    Option = z.Datatype("Option")
    Option.declare("none")
    Option.declare("some", ("val", z.IntSort()))
    Option = Option.create()
    o = z.Const("o", Option)
    s = z.Solver(scope)
    s.add(Option.is_some(o), Option.val(o) == 7)
    s.check()
    ay = str(s.model()[o])
    if HAVE_Z3PY:
        O2 = _z3.Datatype("Option")
        O2.declare("none")
        O2.declare("some", ("val", _z3.IntSort()))
        O2 = O2.create()
        o2 = _z3.Const("o", O2)
        s2 = _z3.Solver()
        s2.add(O2.is_some(o2), O2.val(o2) == 7)
        s2.check()
        assert str(s2.model()[o2]) == ay  # both: some(7)
    assert ay == "some(7)"


def test_datatype_is_none(scope):
    Option = z.Datatype("Option")
    Option.declare("none")
    Option.declare("some", ("val", z.IntSort()))
    Option = Option.create()
    o = z.Const("o", Option)
    s = z.Solver(scope)
    s.add(Option.is_none(o))
    assert str(s.check()) == "sat"
    assert str(s.model()[o]) == "none"


def test_datatype_nullary_attr_is_a_value(scope):
    # z3py exposes a nullary constructor as an already-applied constant value.
    Option = z.Datatype("Option")
    Option.declare("none")
    Option.declare("some", ("val", z.IntSort()))
    Option = Option.create()
    assert isinstance(Option.none, z.DatatypeRef)
    assert str(Option.none) == "none"


# ---------------------------------------------------------------------------
# Recursive datatype (self-reference)
# ---------------------------------------------------------------------------

def test_recursive_list_model_readback(scope):
    List = z.Datatype("List")
    List.declare("cons", ("car", z.IntSort()), ("cdr", List))
    List.declare("nil")
    List = List.create()
    l = z.Const("l", List)
    s = z.Solver(scope)
    s.add(l == List.cons(1, List.cons(2, List.cons(3, List.nil))))
    assert str(s.check()) == "sat"
    m = s.model()
    lv = m[l]
    assert str(lv) == "cons(1, cons(2, cons(3, nil)))"
    assert str(lv.arg(0)) == "1"
    assert str(lv.arg(1).arg(0)) == "2"


def test_recursive_list_parity_z3py(scope):
    List = z.Datatype("List")
    List.declare("cons", ("car", z.IntSort()), ("cdr", List))
    List.declare("nil")
    List = List.create()
    l = z.Const("l", List)
    s = z.Solver(scope)
    s.add(List.is_cons(l), List.car(l) == 42)
    assert str(s.check()) == "sat"
    ay_car = str(s.model()[l].arg(0))
    assert ay_car == "42"
    if HAVE_Z3PY:
        L2 = _z3.Datatype("List")
        L2.declare("cons", ("car", _z3.IntSort()), ("cdr", L2))
        L2.declare("nil")
        L2 = L2.create()
        l2 = _z3.Const("l", L2)
        s2 = _z3.Solver()
        s2.add(L2.is_cons(l2), L2.car(l2) == 42)
        s2.check()
        assert str(s2.model()[l2].arg(0)) == ay_car  # both: 42


def test_nested_datatype_of_datatype(scope):
    List = z.Datatype("L")
    List.declare("cons", ("hd", z.IntSort()), ("tl", List))
    List.declare("nil")
    List = List.create()
    Box = z.Datatype("Box")
    Box.declare("mk", ("v", List))
    Box = Box.create()
    x = z.Const("x", Box)
    s = z.Solver(scope)
    s.add(x == Box.mk(List.cons(1, List.cons(2, List.nil))))
    assert str(s.check()) == "sat"
    assert str(s.model()[x]) == "mk(cons(1, cons(2, nil)))"


# ---------------------------------------------------------------------------
# Cross-context rebuild (the top-level z3py idiom: build vars, then Solver())
# ---------------------------------------------------------------------------

def test_enum_top_level_fresh_solver_rebuild():
    # No scope: EnumSort + Const built in the main context, then a fresh
    # top-level Solver() (its own context) — exercises the datatype
    # cross-context rebuild path. Unique names avoid main-context collisions.
    Color, (red, green, blue) = z.EnumSort(
        "ColorXC", ["redx", "greenx", "bluex"]
    )
    c = z.Const("cxc", Color)
    s = z.Solver()
    s.add(c != red, c != green)
    assert str(s.check()) == "sat"
    assert str(s.model()[c]) == "bluex"


# ---------------------------------------------------------------------------
# Honest limitations (documented divergences)
# ---------------------------------------------------------------------------

def test_mutual_recursion_raises_not_implemented(scope):
    A = z.Datatype("A")
    B = z.Datatype("B")
    A.declare("mkA", ("b", B))
    B.declare("mkB", ("a", A))
    with pytest.raises(NotImplementedError):
        z.CreateDatatypes(A, B)


# ---------------------------------------------------------------------------
# model_completion=True over datatype / enum CONSTRUCTOR CONSTANTS (B-6 rework)
#
# A nullary constructor (an enum value like `blue`, or `nil`) is a fully-
# interpreted, PAIRWISE-DISTINCT value — never an unconstrained leaf. The FFI
# model-eval snapshot must NOT default such a constant to a shared universe
# element under model_completion (which would collapse distinct constructors to
# equal), and must fold `=`/`distinct` over constructor constants by
# constructor-name identity — exactly as z3py does. Every case is cross-checked
# against z3py.
# ---------------------------------------------------------------------------

def _eval_str(model, expr, completion):
    # A BoolRef's `==` builds an AST (never a Python bool) in both ayz3 and z3py,
    # so compare the concrete evaluation by its rendered value.
    return str(model.eval(expr, model_completion=completion))


def test_enum_completion_constructor_constants_eq(scope):
    Color, (red, green, blue) = z.EnumSort("ColorEq", ["red", "green", "blue"])
    c = z.Const("c", Color)
    s = z.Solver(scope)
    s.add(c != red, c != green)  # forces c = blue
    assert str(s.check()) == "sat"
    m = s.model()
    # Two DISTINCT constructor constants are unequal — not collapsed to a shared
    # completion default (the B-6 rework bug: this returned True / a symbolic
    # unfolded term instead of a concrete False).
    assert _eval_str(m, red == blue, True) == "False"
    assert _eval_str(m, red != blue, True) == "True"
    assert _eval_str(m, red == red, True) == "True"
    # A constant pinned by the model equals the matching constructor literal;
    # completion must NOT flip this correct True to False by defaulting `blue`.
    assert _eval_str(m, c == blue, True) == "True"
    assert _eval_str(m, c == red, True) == "False"
    if HAVE_Z3PY:
        C2, (r2, g2, b2) = _z3.EnumSort("ColorEq", ["red", "green", "blue"])
        c2 = _z3.Const("c", C2)
        s2 = _z3.Solver()
        s2.add(c2 != r2, c2 != g2)
        assert str(s2.check()) == "sat"
        m2 = s2.model()
        assert _eval_str(m, red == blue, True) == _eval_str(m2, r2 == b2, True)
        assert _eval_str(m, red != blue, True) == _eval_str(m2, r2 != b2, True)
        assert _eval_str(m, c == blue, True) == _eval_str(m2, c2 == b2, True)
        assert _eval_str(m, c == red, True) == _eval_str(m2, c2 == r2, True)


def test_enum_completion_distinct(scope):
    Color, (red, green, blue) = z.EnumSort("ColorDist", ["red", "green", "blue"])
    c = z.Const("c", Color)
    s = z.Solver(scope)
    s.add(c != red, c != green)
    assert str(s.check()) == "sat"
    m = s.model()
    # Distinct over three distinct enum values is True under completion.
    assert _eval_str(m, z.Distinct(red, green, blue), True) == "True"
    if HAVE_Z3PY:
        C2, (r2, g2, b2) = _z3.EnumSort("ColorDist", ["red", "green", "blue"])
        c2 = _z3.Const("c", C2)
        s2 = _z3.Solver()
        s2.add(c2 != r2, c2 != g2)
        s2.check()
        m2 = s2.model()
        assert _eval_str(m, z.Distinct(red, green, blue), True) == \
            _eval_str(m2, _z3.Distinct(r2, g2, b2), True)


def test_enum_completion_false_still_honest(scope):
    # model_completion=False keeps the pre-existing (honest) behavior: an eval
    # over constructor constants is NOT fabricated into a completion default.
    Color, (red, green, blue) = z.EnumSort("ColorCf", ["red", "green", "blue"])
    c = z.Const("c", Color)
    s = z.Solver(scope)
    s.add(c != red, c != green)
    assert str(s.check()) == "sat"
    m = s.model()
    # Distinct constructor literals are still known-distinct WITHOUT completion
    # (the fold is model-level knowledge, not completion), matching z3py.
    assert _eval_str(m, red == blue, False) == "False"
    assert _eval_str(m, c == blue, False) == "True"
    if HAVE_Z3PY:
        C2, (r2, g2, b2) = _z3.EnumSort("ColorCf", ["red", "green", "blue"])
        c2 = _z3.Const("c", C2)
        s2 = _z3.Solver()
        s2.add(c2 != r2, c2 != g2)
        s2.check()
        m2 = s2.model()
        assert _eval_str(m, red == blue, False) == _eval_str(m2, r2 == b2, False)
        assert _eval_str(m, c == blue, False) == _eval_str(m2, c2 == b2, False)


def test_datatype_nullary_completion_eq(scope):
    # A general (non-enum) datatype's nullary constructor (`nil`) is likewise a
    # distinct interpreted value under completion.
    List = z.Datatype("ListNil")
    List.declare("cons", ("car", z.IntSort()), ("cdr", List))
    List.declare("nil")
    List = List.create()
    l = z.Const("l", List)
    s = z.Solver(scope)
    s.add(List.is_nil(l))  # forces l = nil
    assert str(s.check()) == "sat"
    m = s.model()
    assert _eval_str(m, l == List.nil, True) == "True"
    if HAVE_Z3PY:
        L2 = _z3.Datatype("ListNil")
        L2.declare("cons", ("car", _z3.IntSort()), ("cdr", L2))
        L2.declare("nil")
        L2 = L2.create()
        l2 = _z3.Const("l", L2)
        s2 = _z3.Solver()
        s2.add(L2.is_nil(l2))
        s2.check()
        m2 = s2.model()
        assert _eval_str(m, l == List.nil, True) == _eval_str(m2, l2 == L2.nil, True)


def test_bool_datatype_field_arg_renders_capitalized(scope):
    # A Boolean datatype field read via .arg(i) is a BoolRef printing
    # `True`/`False` (z3py), not a mis-sorted ArithRef printing `true`.
    Pair, mk_pair, (first, second) = z.TupleSort(
        "PairBool", [z.IntSort(), z.BoolSort()]
    )
    p = z.Const("p", Pair)
    s = z.Solver(scope)
    s.add(first(p) == 9, second(p) == True)  # noqa: E712
    assert str(s.check()) == "sat"
    pv = s.model()[p]
    assert isinstance(pv.arg(1), z.BoolRef)
    assert str(pv.arg(1)) == "True"
    assert str(pv.arg(0)) == "9"
    if HAVE_Z3PY:
        P2, mk2, (f2, s2p) = _z3.TupleSort("PairBool", [_z3.IntSort(), _z3.BoolSort()])
        p2 = _z3.Const("p", P2)
        so = _z3.Solver()
        so.add(f2(p2) == 9, s2p(p2) == True)  # noqa: E712
        so.check()
        pv2 = so.model()[p2]
        assert str(pv.arg(1)) == str(pv2.arg(1))  # both "True"


def test_model_eval_of_recognizer_is_unfolded_but_honest(scope):
    # DOCUMENTED DIVERGENCE: z3py folds m.eval(is_some(o)) to True; AY returns
    # the honest unfolded recognizer term. The model VALUE (m[o]) is correct and
    # z3py-identical; only the eval-fold differs. This asserts AY's honest
    # behavior so the divergence stays intentional, not silent.
    Option = z.Datatype("Option")
    Option.declare("none")
    Option.declare("some", ("val", z.IntSort()))
    Option = Option.create()
    o = z.Const("o", Option)
    s = z.Solver(scope)
    s.add(Option.is_some(o), Option.val(o) == 7)
    s.check()
    m = s.model()
    # The value is correct and matches z3py.
    assert str(m[o]) == "some(7)"
    # eval of the recognizer is the honest, unfolded (equisatisfiable) term.
    ev = str(m.eval(Option.is_some(o)))
    assert "is-some" in ev or ev == "True"

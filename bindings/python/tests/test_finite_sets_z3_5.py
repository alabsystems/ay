# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0

"""Z3 5.0.0 differential coverage for the distinct FiniteSet theory."""

import pytest

import ayz3 as z
from ayz3 import _lib


@pytest.fixture
def scope():
    solver = z.Solver(z.Context())
    with solver.using():
        yield solver.ctx


def _corpus(mod):
    int_sort = mod.IntSort()
    finite_int = mod.FiniteSetSort(int_sort)
    empty = mod.FiniteSetEmpty(finite_int)
    singleton = mod.Singleton(mod.IntVal(1))
    const_seven = mod.K(int_sort, mod.IntVal(7))
    const_true = mod.K(int_sort, mod.BoolVal(True))
    return {
        "sort": finite_int,
        "empty": empty,
        "singleton": singleton,
        "union": mod.FiniteSetUnion(singleton, empty),
        "intersect": mod.FiniteSetIntersect(singleton, empty),
        "difference": mod.FiniteSetDifference(singleton, empty),
        "member": mod.FiniteSetMember(mod.IntVal(1), singleton),
        "size": mod.FiniteSetSize(singleton),
        "subset": mod.FiniteSetSubset(empty, singleton),
        "map": mod.FiniteSetMap(const_seven, singleton),
        "filter": mod.FiniteSetFilter(const_true, singleton),
        "range": mod.FiniteSetRange(mod.IntVal(1), mod.IntVal(3)),
    }


EXPECTED_KINDS = {
    "empty": 49152,
    "singleton": 49153,
    "union": 49154,
    "intersect": 49155,
    "difference": 49156,
    "member": 49157,
    "size": 49158,
    "subset": 49159,
    "map": 49160,
    "filter": 49161,
    "range": 49162,
}


def test_all_fourteen_public_apis_and_exact_decl_registry(scope):
    corpus = _corpus(z)
    assert z.is_finite_set_sort(corpus["sort"])
    assert corpus["sort"].element_sort().sexpr() == "Int"
    assert corpus["sort"].sexpr() == "(FiniteSet Int)"
    assert z.is_finite_set(corpus["empty"])

    for label, kind in EXPECTED_KINDS.items():
        term = corpus[label]
        assert term.decl().kind() == kind
        assert term.decl().name() == {
            "empty": "set.empty",
            "singleton": "set.singleton",
            "union": "set.union",
            "intersect": "set.intersect",
            "difference": "set.difference",
            "member": "set.in",
            "size": "set.size",
            "subset": "set.subset",
            "map": "set.map",
            "filter": "set.filter",
            "range": "set.range",
        }[label]

    assert z.In(z.IntVal(1), corpus["singleton"]).sexpr() == corpus["member"].sexpr()
    for symbol in (
        "Z3_mk_finite_set_sort",
        "Z3_is_finite_set_sort",
        "Z3_get_finite_set_sort_basis",
        "Z3_mk_finite_set_empty",
        "Z3_mk_finite_set_singleton",
        "Z3_mk_finite_set_union",
        "Z3_mk_finite_set_intersect",
        "Z3_mk_finite_set_difference",
        "Z3_mk_finite_set_member",
        "Z3_mk_finite_set_size",
        "Z3_mk_finite_set_subset",
        "Z3_mk_finite_set_map",
        "Z3_mk_finite_set_filter",
        "Z3_mk_finite_set_range",
    ):
        assert hasattr(_lib.lib, symbol)

    constants = [
        "Z3_OP_FINITE_SET_EMPTY",
        "Z3_OP_FINITE_SET_SINGLETON",
        "Z3_OP_FINITE_SET_UNION",
        "Z3_OP_FINITE_SET_INTERSECT",
        "Z3_OP_FINITE_SET_DIFFERENCE",
        "Z3_OP_FINITE_SET_IN",
        "Z3_OP_FINITE_SET_SIZE",
        "Z3_OP_FINITE_SET_SUBSET",
        "Z3_OP_FINITE_SET_MAP",
        "Z3_OP_FINITE_SET_FILTER",
        "Z3_OP_FINITE_SET_RANGE",
        "Z3_OP_FINITE_SET_EXT",
        "Z3_OP_FINITE_SET_MAP_INVERSE",
        "Z3_OP_INTERNAL",
        "Z3_OP_RECURSIVE",
        "Z3_OP_UNINTERPRETED",
    ]
    assert [getattr(z, name) for name in constants] == list(range(49152, 49168))
    namespace = {}
    exec("from ayz3 import *", namespace)
    assert all(name in namespace for name in constants)


@pytest.mark.usefixtures("required_reference_z3")
def test_exact_z3_500_strings_kinds_and_sort_parameter(scope, required_reference_z3):
    ay = _corpus(z)
    reference = _corpus(required_reference_z3)
    assert ay["sort"].sexpr() == reference["sort"].sexpr()
    for label in EXPECTED_KINDS:
        assert ay[label].sexpr() == reference[label].sexpr(), label
        assert ay[label].decl().kind() == reference[label].decl().kind(), label
        assert ay[label].decl().name() == reference[label].decl().name(), label

    ay_params = ay["empty"].decl().params()
    z3_params = reference["empty"].decl().params()
    assert len(ay_params) == len(z3_params) == 1
    assert ay_params[0].sexpr() == z3_params[0].sexpr() == "(FiniteSet Int)"


def _generic_working_dispatch_corpus(mod):
    int_sort = mod.IntSort()
    finite_int = mod.FiniteSetSort(int_sort)
    empty = mod.EmptySet(finite_int)
    one = mod.Singleton(mod.IntVal(1))
    two = mod.Singleton(mod.IntVal(2))
    return {
        "empty": empty,
        "union": mod.SetUnion(one, two),
        "intersect": mod.SetIntersect(one, two),
        "difference": mod.SetDifference(one, two),
    }


@pytest.mark.usefixtures("required_reference_z3")
def test_generic_helpers_match_working_z3_500_finite_dispatch(
    scope, required_reference_z3
):
    ay = _generic_working_dispatch_corpus(z)
    reference = _generic_working_dispatch_corpus(required_reference_z3)
    for label, term in ay.items():
        assert z.is_finite_set(term), label
        assert term.sexpr() == reference[label].sexpr(), label


@pytest.mark.usefixtures("required_reference_z3")
def test_generic_helpers_fix_four_z3_500_python_naming_typos(
    scope, required_reference_z3
):
    # Pinned z3py 5.0 enters each finite-set dispatch branch below but calls
    # names that do not exist (`FiniteSetSingleton`, `FiniteSetIsMember`, and
    # `FiniteSetIsSubset`). AY intentionally fixes those Python-only naming
    # bugs by routing to its correctly named finite-set primitives.
    ref_one = required_reference_z3.Singleton(required_reference_z3.IntVal(1))
    ref_empty = required_reference_z3.EmptySet(
        required_reference_z3.FiniteSetSort(required_reference_z3.IntSort())
    )
    for invoke in (
        lambda: required_reference_z3.SetAdd(
            ref_one, required_reference_z3.IntVal(2)
        ),
        lambda: required_reference_z3.SetDel(
            ref_one, required_reference_z3.IntVal(1)
        ),
        lambda: required_reference_z3.IsMember(
            required_reference_z3.IntVal(1), ref_one
        ),
        lambda: required_reference_z3.IsSubset(ref_empty, ref_one),
    ):
        with pytest.raises(NameError):
            invoke()

    finite_int = z.FiniteSetSort(z.IntSort())
    empty = z.EmptySet(finite_int)
    one = z.Singleton(z.IntVal(1))
    added = z.SetAdd(one, 2)
    deleted = z.SetDel(one, 1)
    member = z.IsMember(1, one)
    subset = z.IsSubset(empty, one)

    assert added.sexpr() == z.FiniteSetUnion(
        z.Singleton(z.IntVal(2)), one
    ).sexpr()
    assert deleted.sexpr() == z.FiniteSetDifference(
        one, z.Singleton(z.IntVal(1))
    ).sexpr()
    assert member.sexpr() == z.FiniteSetMember(z.IntVal(1), one).sexpr()
    assert subset.sexpr() == z.FiniteSetSubset(empty, one).sexpr()


def _prove(formula):
    solver = z.Solver()
    solver.add(z.Not(formula))
    assert solver.check() == z.unsat


def test_ground_constructor_cardinality_filter_map_and_inclusive_range_laws(scope):
    int_sort = z.IntSort()
    finite_int = z.FiniteSetSort(int_sort)
    empty = z.FiniteSetEmpty(finite_int)
    singleton = z.Singleton(z.IntVal(1))
    inclusive = z.FiniteSetRange(z.IntVal(1), z.IntVal(3))

    _prove(z.FiniteSetSize(empty) == 0)
    _prove(z.FiniteSetSize(singleton) == 1)
    _prove(z.In(1, singleton))
    _prove(z.FiniteSetSize(inclusive) == 3)
    _prove(z.In(1, inclusive))
    _prove(z.In(3, inclusive))
    _prove(z.Not(z.In(4, inclusive)))

    mapped = z.FiniteSetMap(z.K(int_sort, z.IntVal(7)), singleton)
    _prove(z.In(7, mapped))
    _prove(z.Not(z.In(8, mapped)))

    kept = z.FiniteSetFilter(z.K(int_sort, z.BoolVal(True)), singleton)
    rejected = z.FiniteSetFilter(z.K(int_sort, z.BoolVal(False)), singleton)
    _prove(z.In(1, kept))
    _prove(z.Not(z.In(1, rejected)))


def test_nested_sort_render_generic_projection_and_legacy_array_isolation(
    scope, monkeypatch
):
    finite_int = z.FiniteSetSort(z.IntSort())
    nested = z.FiniteSetSort(finite_int)
    empty = z.FiniteSetEmpty(finite_int)
    nested_singleton = z.Singleton(empty)
    assert nested.sexpr() == "(FiniteSet (FiniteSet Int))"
    assert nested_singleton.sexpr() == (
        "(set.singleton (as set.empty (FiniteSet Int)))"
    )

    composed = z.If(z.Bool("p"), z.Singleton(z.IntVal(1)), empty)
    assert "(set.singleton 1)" in composed.sexpr()
    assert "(as set.empty (FiniteSet Int))" in composed.sexpr()
    assert "finite_set_app" not in composed.sexpr()

    legacy_empty = z.EmptySet(z.IntSort())
    def ffi_equality_must_not_run(*_args):
        raise AssertionError("finite-set sort mismatch reached the C FFI")

    monkeypatch.setattr(_lib.lib, "Z3_mk_eq", ffi_equality_must_not_run)
    monkeypatch.setattr(_lib.lib, "Z3_mk_distinct", ffi_equality_must_not_run)
    with pytest.raises(z.AyZ3Exception, match="sort mismatch"):
        _ = empty == legacy_empty
    with pytest.raises(z.AyZ3Exception, match="sort mismatch"):
        _ = empty != legacy_empty
    with pytest.raises(z.AyZ3Exception, match="sort mismatch"):
        z.Select(empty, z.IntVal(1))


def test_same_and_cross_context_rebuild_all_retained_apps():
    source = z.Context()
    with z.Solver(source).using():
        corpus = _corpus(z)
    destination = z.Context()
    for label, term in corpus.items():
        if label == "sort":
            continue
        assert term.translate(source) is term
        rebuilt = term.translate(destination)
        assert rebuilt.ctx is destination
        assert rebuilt.sexpr() == term.sexpr(), label


def test_cross_context_rebuild_does_not_capture_user_set_operator_names():
    source = z.Context()
    with z.Solver(source).using():
        int_sort = z.IntSort()
        singleton_uf = z.Function("set.singleton", int_sort, int_sort)
        empty_uf = z.Function("set.empty", int_sort)
        singleton_app = singleton_uf(z.IntVal(7))
        empty_app = empty_uf()

    destination = z.Context()
    for original in (singleton_app, empty_app):
        rebuilt = original.translate(destination)
        assert rebuilt.sort().sexpr() == "Int"
        assert rebuilt.decl().kind() == z.Z3_OP_UNINTERPRETED
        assert rebuilt.decl().name() == original.decl().name()
        assert rebuilt.sexpr() == original.sexpr()


@pytest.mark.usefixtures("required_reference_z3")
def test_funcdecl_map_filter_translate_preserves_as_array_text_and_semantics(
    required_reference_z3,
):
    source = z.Context()
    with z.Solver(source).using():
        int_sort = z.IntSort()
        one = z.Singleton(z.IntVal(1))
        mapper = z.Function("finite_translate_mapper", int_sort, int_sort)
        predicate = z.Function(
            "finite_translate_predicate", int_sort, z.BoolSort()
        )
        mapped = z.FiniteSetMap(mapper, one)
        filtered = z.FiniteSetFilter(predicate, one)
        quoted_mapper = z.Function("finite map|quoted", int_sort, int_sort)
        quoted_as_array = z.AsArray(quoted_mapper)
        quoted_mapped = z.FiniteSetMap(quoted_mapper, one)
        laws = (
            z.Implies(mapper(1) == 7, z.In(7, mapped)),
            z.In(1, filtered) == predicate(1),
        )

    ref_int = required_reference_z3.IntSort()
    ref_one = required_reference_z3.Singleton(required_reference_z3.IntVal(1))
    ref_mapper = required_reference_z3.Function(
        "finite_translate_mapper", ref_int, ref_int
    )
    ref_predicate = required_reference_z3.Function(
        "finite_translate_predicate", ref_int, required_reference_z3.BoolSort()
    )
    ref_quoted_mapper = required_reference_z3.Function(
        "finite map|quoted", ref_int, ref_int
    )
    assert z.AsArray(mapper).sexpr() == required_reference_z3.AsArray(
        ref_mapper
    ).sexpr()
    assert mapped.sexpr() == required_reference_z3.FiniteSetMap(
        ref_mapper, ref_one
    ).sexpr()
    assert filtered.sexpr() == required_reference_z3.FiniteSetFilter(
        ref_predicate, ref_one
    ).sexpr()
    assert quoted_as_array.sexpr() == required_reference_z3.AsArray(
        ref_quoted_mapper
    ).sexpr()
    assert quoted_mapped.sexpr() == required_reference_z3.FiniteSetMap(
        ref_quoted_mapper, ref_one
    ).sexpr()
    assert repr(mapped) == mapped.sexpr()
    assert repr(filtered) == filtered.sexpr()

    destination = z.Context()
    rebuilt_mapped = mapped.translate(destination)
    rebuilt_filtered = filtered.translate(destination)
    rebuilt_quoted = quoted_mapped.translate(destination)
    assert rebuilt_mapped.sexpr() == mapped.sexpr()
    assert rebuilt_filtered.sexpr() == filtered.sexpr()
    assert rebuilt_quoted.sexpr() == quoted_mapped.sexpr()

    expected_results = (z.unsat, z.unsat)
    for law, expected in zip(laws, expected_results):
        source_solver = z.Solver(source)
        source_solver.add(z.Not(law))
        assert source_solver.check() == expected

        rebuilt_law = law.translate(destination)
        solver = z.Solver(destination)
        solver.add(z.Not(rebuilt_law))
        # FuncDecl-backed map is an honest `unknown` in AY's current finite-set
        # engine, while filter decides this ground law. Translation must
        # preserve both outcomes and must never weaken either to a verdict.
        assert solver.check() == expected

    # Destination metadata must support another translation hop as well.
    third = z.Context()
    assert rebuilt_mapped.translate(third).sexpr() == mapped.sexpr()
    assert rebuilt_filtered.translate(third).sexpr() == filtered.sexpr()
    assert rebuilt_quoted.translate(third).sexpr() == quoted_mapped.sexpr()

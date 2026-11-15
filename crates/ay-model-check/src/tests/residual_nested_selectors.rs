// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Source-shaped residual recovery, followed by the ordinary fresh model gate.

use super::*;

fn record(name: &str, constructor: &str, fields: Vec<DatatypeField>) -> Sort {
    Sort::Datatype(DatatypeSort::new(
        name,
        vec![DatatypeConstructor::new(constructor, fields)],
    ))
}

fn bv(value: u64) -> ModelValue {
    ModelValue::bitvec(BigInt::from(value), 64)
}

fn vector(length: u64) -> ModelValue {
    ModelValue::Datatype {
        ctor: "mkVecPbLit".into(),
        args: vec![
            bv(0),
            bv(length),
            bv(length),
            ModelValue::Array(Box::new(ArrayValue {
                default: ModelValue::Datatype {
                    ctor: "mkPbLit".into(),
                    args: vec![bv(0), ModelValue::Bool(false)],
                },
                store: vec![],
            })),
        ],
    }
}

fn term_value(coefficient: u64, length: u64) -> ModelValue {
    ModelValue::Datatype {
        ctor: "mkPbTerm".into(),
        args: vec![bv(coefficient), vector(length)],
    }
}

struct Fixture {
    vector: Sort,
    term: Sort,
    array: Sort,
    a: TermId,
    b: TermId,
    index: TermId,
}

impl Fixture {
    fn new(terms: &mut TermStore) -> Self {
        let lit = record(
            "PbLit",
            "mkPbLit",
            vec![
                DatatypeField::new("fld_variable", Sort::bitvec(64)),
                DatatypeField::new("fld_positive", Sort::Bool),
            ],
        );
        let vector = record(
            "VecPbLit",
            "mkVecPbLit",
            vec![
                DatatypeField::new("fld_ptr", Sort::bitvec(64)),
                DatatypeField::new("fld_len", Sort::bitvec(64)),
                DatatypeField::new("fld_cap", Sort::bitvec(64)),
                DatatypeField::new("fld_data", Sort::array(Sort::bitvec(64), lit)),
            ],
        );
        let term = record(
            "PbTerm",
            "mkPbTerm",
            vec![
                DatatypeField::new("fld_coeff", Sort::bitvec(64)),
                DatatypeField::new("fld_lits", vector.clone()),
            ],
        );
        let array = Sort::array(Sort::bitvec(64), term.clone());
        let a = terms.mk_var("a", array.clone());
        let b = terms.mk_var("b", array.clone());
        let index = terms.mk_bitvec(BigInt::from(0x8000_0000_0000_0001u64), 64);
        Self {
            vector,
            term,
            array,
            a,
            b,
            index,
        }
    }

    fn read(&self, terms: &mut TermStore, array: TermId, index: TermId) -> [TermId; 3] {
        let element = app(terms, "select", &[array, index], self.term.clone());
        let vector = app(terms, "fld_lits", &[element], self.vector.clone());
        let length = app(terms, "fld_len", &[vector], Sort::bitvec(64));
        [element, vector, length]
    }
}

fn equals(terms: &mut TermStore, left: TermId, right: TermId) -> TermId {
    app(terms, "=", &[left, right], Sort::Bool)
}

fn equals_bv(terms: &mut TermStore, value: TermId, expected: u64) -> TermId {
    let expected = terms.mk_bitvec(BigInt::from(expected), 64);
    equals(terms, value, expected)
}

#[test]
fn nested_pbterm_vec_length_recovers_free_arrays_and_semantic_index_aliases() {
    let mut terms = TermStore::new();
    let f = Fixture::new(&mut terms);
    let alias_index = terms.mk_var("index_alias", Sort::bitvec(64));
    let next = terms.mk_bitvec(BigInt::from(0x8000_0000_0000_0002u64), 64);
    let [element, _, a_length] = f.read(&mut terms, f.a, f.index);
    let [_, _, b_length] = f.read(&mut terms, f.b, alias_index);
    let [_, _, next_length] = f.read(&mut terms, f.a, next);
    let coefficient = app(&mut terms, "fld_coeff", &[element], Sort::bitvec(64));
    let alias = equals(&mut terms, f.a, f.b);
    let a_five = equals_bv(&mut terms, a_length, 5);
    let b_five = equals_bv(&mut terms, b_length, 5);
    let b_six = equals_bv(&mut terms, b_length, 6);
    let next_six = equals_bv(&mut terms, next_length, 6);
    let coefficient = equals_bv(&mut terms, coefficient, 7);
    let model = StubModel::new().with(alias_index, bv(0x8000_0000_0000_0001));
    assert_confirmed(&verdict(
        &terms,
        &model,
        &[alias, a_five, b_five, next_six, coefficient],
    ));
    assert_cannot(&verdict(&terms, &model, &[alias, a_five, b_six]));
}

#[test]
fn nested_whole_ancestor_and_descendant_requirements_reconcile_every_level() {
    let mut terms = TermStore::new();
    let f = Fixture::new(&mut terms);
    let [element, vector, length] = f.read(&mut terms, f.a, f.index);
    let whole = terms.mk_var("whole", f.term.clone());
    let ancestor = terms.mk_var("ancestor", f.vector.clone());
    let whole_eq = equals(&mut terms, element, whole);
    let ancestor_eq = equals(&mut terms, vector, ancestor);
    let five = equals_bv(&mut terms, length, 5);
    for (whole_length, ancestor_length) in [(5, 5), (4, 5), (5, 4), (4, 4)] {
        let model = StubModel::new()
            .with(whole, term_value(7, whole_length))
            .with(ancestor, self::vector(ancestor_length));
        let result = verdict(&terms, &model, &[whole_eq, ancestor_eq, five]);
        if whole_length == 5 && ancestor_length == 5 {
            assert_confirmed(&result);
        } else {
            assert_cannot(&result);
        }
    }
}

#[test]
fn nested_paths_with_the_same_terminal_field_keep_distinct_ancestors() {
    let mut terms = TermStore::new();
    let f = Fixture::new(&mut terms);
    let pair = record(
        "Pair",
        "mkPair",
        vec![
            DatatypeField::new("left", f.vector.clone()),
            DatatypeField::new("right", f.vector.clone()),
        ],
    );
    let array = terms.mk_var("pair_array", Sort::array(Sort::bitvec(64), pair.clone()));
    let selected = app(&mut terms, "select", &[array, f.index], pair);
    let left = app(&mut terms, "left", &[selected], f.vector.clone());
    let right = app(&mut terms, "right", &[selected], f.vector.clone());
    let left_length = app(&mut terms, "fld_len", &[left], Sort::bitvec(64));
    let right_length = app(&mut terms, "fld_len", &[right], Sort::bitvec(64));
    let left_five = equals_bv(&mut terms, left_length, 5);
    let right_seven = equals_bv(&mut terms, right_length, 7);
    let right_five = equals_bv(&mut terms, right_length, 5);
    assert_confirmed(&verdict(
        &terms,
        &StubModel::new(),
        &[left_five, right_seven],
    ));
    assert_cannot(&verdict(
        &terms,
        &StubModel::new(),
        &[left_five, right_seven, right_five],
    ));
}

#[test]
fn nested_constructor_choice_must_fit_the_entire_path() {
    let mut terms = TermStore::new();
    let choice = Sort::Datatype(DatatypeSort::new(
        "Choice",
        vec![
            DatatypeConstructor::unit("empty"),
            DatatypeConstructor::new("full", vec![DatatypeField::new("length", Sort::bitvec(64))]),
        ],
    ));
    let outer = record(
        "OuterChoice",
        "wrap",
        vec![DatatypeField::new("choice", choice.clone())],
    );
    let array = terms.mk_var("choices", Sort::array(Sort::bitvec(64), outer.clone()));
    let zero = terms.mk_bitvec(BigInt::from(0), 64);
    let selected = app(&mut terms, "select", &[array, zero], outer);
    let selected_choice = app(&mut terms, "choice", &[selected], choice.clone());
    let length = app(&mut terms, "length", &[selected_choice], Sort::bitvec(64));
    let length_five = equals_bv(&mut terms, length, 5);
    assert_confirmed(&verdict(&terms, &StubModel::new(), &[length_five]));
    let pinned = terms.mk_var("pinned_choice", choice);
    let ancestor = equals(&mut terms, selected_choice, pinned);
    let empty = StubModel::new().with(
        pinned,
        ModelValue::Datatype {
            ctor: "empty".into(),
            args: vec![],
        },
    );
    assert_cannot(&verdict(&terms, &empty, &[ancestor, length_five]));
    let full = StubModel::new().with(
        pinned,
        ModelValue::Datatype {
            ctor: "full".into(),
            args: vec![bv(5)],
        },
    );
    assert_confirmed(&verdict(&terms, &full, &[ancestor, length_five]));
}

#[test]
fn ambiguous_nested_selector_names_cannot_choose_an_unproved_constructor() {
    for constructor_count in [1, 2] {
        let mut terms = TermStore::new();
        let inner = Sort::Datatype(DatatypeSort::new(
            "AmbiguousInner",
            (0..constructor_count)
                .map(|index| {
                    DatatypeConstructor::new(
                        format!("inner{index}"),
                        vec![DatatypeField::new("value", Sort::bitvec(64))],
                    )
                })
                .collect(),
        ));
        let outer = record(
            "AmbiguousOuter",
            "outer",
            vec![DatatypeField::new("inner", inner.clone())],
        );
        let array = terms.mk_var("ambiguous", Sort::array(Sort::bitvec(64), outer.clone()));
        let zero = terms.mk_bitvec(int(0), 64);
        let selected = app(&mut terms, "select", &[array, zero], outer);
        let selected = app(&mut terms, "inner", &[selected], inner);
        let value = app(&mut terms, "value", &[selected], Sort::bitvec(64));
        let assertion = equals_bv(&mut terms, value, 5);
        let result = verdict(&terms, &StubModel::new(), &[assertion]);
        if constructor_count == 1 {
            assert_confirmed(&result);
        } else {
            assert_cannot(&result);
        }
    }
}

#[test]
fn nested_symbolic_projection_precedes_selector_paths_and_application_pins() {
    let mut terms = TermStore::new();
    let f = Fixture::new(&mut terms);
    let [_, vector, length] = f.read(&mut terms, f.a, f.index);
    let [_, _, other_length] = f.read(&mut terms, f.b, f.index);
    let assertion = equals_bv(&mut terms, length, 5);
    let alias = equals(&mut terms, f.a, f.b);
    let other = equals_bv(&mut terms, other_length, 5);
    let assertions = [assertion, alias, other];
    assert_confirmed(&verdict(&terms, &StubModel::new(), &assertions));
    assert_confirmed(&verdict(
        &terms,
        &UfStubModel::new().uf(length, bv(5)),
        &assertions,
    ));
    for site in [vector, length] {
        // Both selected arguments have a different sort from the application.
        // A symbolic projection must refuse, not be replaced by the selector
        // interpretation or by its otherwise usable committed application pin.
        let model = UfStubModel::new().projection(site, 0).uf(length, bv(5));
        assert!(matches!(
            evaluate_term(&terms, &model, site),
            EvalOutcome::Unevaluable(_)
        ));
        assert_cannot(&verdict(&terms, &model, &assertions));
        let model = UfStubModel::new()
            .projection_error(site, "inconsistent declaration identity")
            .uf(length, bv(5));
        assert_cannot(&verdict(&terms, &model, &assertions));
    }
}

#[test]
fn nested_selector_metadata_and_malformed_ancestor_values_cannot_be_laundered() {
    let mut terms = TermStore::new();
    let f = Fixture::new(&mut terms);
    let [element, vector, length] = f.read(&mut terms, f.a, f.index);
    let no = terms.mk_bool(false);
    let malformed = app(&mut terms, "fld_len", &[vector], Sort::Bool);
    let malformed = equals(&mut terms, malformed, no);
    let unknown = app(&mut terms, "missing_field", &[vector], Sort::bitvec(64));
    let unknown = equals_bv(&mut terms, unknown, 5);
    let wrong_middle = app(&mut terms, "fld_lits", &[element], f.term.clone());
    let wrong_middle = app(&mut terms, "fld_coeff", &[wrong_middle], Sort::bitvec(64));
    let wrong_middle = equals_bv(&mut terms, wrong_middle, 5);
    for assertion in [malformed, unknown, wrong_middle] {
        assert_cannot(&verdict(&terms, &StubModel::new(), &[assertion]));
    }
    let pin = terms.mk_var("malformed_vector", f.vector.clone());
    let ancestor = equals(&mut terms, vector, pin);
    let length = equals_bv(&mut terms, length, 5);
    for args in [
        vec![bv(0), bv(5)],
        vec![bv(0), bv(5), ModelValue::Bool(false), bv(0)],
    ] {
        let model = StubModel::new().with(
            pin,
            ModelValue::Datatype {
                ctor: "mkVecPbLit".into(),
                args,
            },
        );
        assert_cannot(&verdict(&terms, &model, &[ancestor, length]));
    }
}

#[derive(Clone, Copy)]
enum Pin {
    Whole,
    Ancestor,
    Descendant,
}

#[test]
fn committed_nested_pins_only_narrow_the_formula_derived_witness() {
    let mut terms = TermStore::new();
    let f = Fixture::new(&mut terms);
    let [element, vector, length] = f.read(&mut terms, f.a, f.index);
    let [_, _, other_length] = f.read(&mut terms, f.b, f.index);
    let alias = equals(&mut terms, f.a, f.b);
    let committed_true = equals_bv(&mut terms, length, 5);
    let same = equals_bv(&mut terms, other_length, 5);
    let conflict = equals_bv(&mut terms, other_length, 6);
    for pin in [Pin::Whole, Pin::Ancestor, Pin::Descendant] {
        let model = match pin {
            Pin::Whole => UfStubModel::new().sel(element, term_value(7, 5)),
            Pin::Ancestor => UfStubModel::new().uf(vector, self::vector(5)),
            Pin::Descendant => UfStubModel::new().uf(length, bv(5)),
        };
        assert!(
            matches!(evaluate_term(&terms, &model, length), EvalOutcome::Value(ModelValue::BitVec { width: 64, value }) if value == int(5))
        );
        assert_confirmed(&verdict(&terms, &model, &[committed_true, alias, same]));
        assert_cannot(&verdict(&terms, &model, &[committed_true, alias, conflict]));
    }
}

#[test]
fn nested_missing_ground_values_and_nonlocalized_pin_contexts_stay_refused() {
    let mut terms = TermStore::new();
    let f = Fixture::new(&mut terms);
    let [_, vector, length] = f.read(&mut terms, f.a, f.index);
    let missing = terms.mk_var("missing", Sort::bitvec(64));
    let missing = equals(&mut terms, length, missing);
    assert_cannot(&verdict(&terms, &StubModel::new(), &[missing]));
    let index = terms.mk_var("missing_index", Sort::bitvec(64));
    let [_, _, read] = f.read(&mut terms, f.a, index);
    let read = equals_bv(&mut terms, read, 5);
    assert_cannot(&verdict(&terms, &StubModel::new(), &[read]));
    let yes = terms.mk_bool(true);
    let other_vector = terms.mk_var("other_vector", f.vector.clone());
    let conditional = terms.mk_ite_raw(yes, vector, other_vector);
    let unlocalized = app(&mut terms, "fld_len", &[conditional], Sort::bitvec(64));
    let pinned_true = equals_bv(&mut terms, unlocalized, 5);
    let requirement = equals_bv(&mut terms, length, 5);
    let model = UfStubModel::new().uf(unlocalized, bv(5));
    assert_cannot(&verdict(&terms, &model, &[pinned_true, requirement]));
}

#[test]
fn nested_store_disequality_and_read_versus_read_contexts_remain_outside_residue() {
    let mut terms = TermStore::new();
    let f = Fixture::new(&mut terms);
    let [element, _, length] = f.read(&mut terms, f.a, f.index);
    let [_, _, other_length] = f.read(&mut terms, f.b, f.index);
    let read_to_read = equals(&mut terms, length, other_length);
    let one = terms.mk_bitvec(BigInt::from(1), 64);
    let unequal = app(&mut terms, "distinct", &[length, one], Sort::Bool);
    let stored = app(
        &mut terms,
        "store",
        &[f.a, f.index, element],
        f.array.clone(),
    );
    let store_eq = equals(&mut terms, f.b, stored);
    for assertion in [read_to_read, unequal, store_eq] {
        assert_cannot(&verdict(&terms, &StubModel::new(), &[assertion]));
    }
}

#[test]
fn nested_path_and_requirement_budgets_refuse_without_partial_recovery() {
    for depth in [4usize, residual::MAX_CLASSIFY_DEPTH + 2] {
        let mut terms = TermStore::new();
        let mut sorts = vec![Sort::bitvec(64)];
        for level in 0..depth {
            sorts.push(record(
                &format!("D{level}"),
                &format!("mk{level}"),
                vec![DatatypeField::new(
                    format!("field{level}"),
                    sorts[level].clone(),
                )],
            ));
        }
        let array = terms.mk_var("deep", Sort::array(Sort::bitvec(64), sorts[depth].clone()));
        let index = terms.mk_bitvec(int(0), 64);
        let mut selected = app(&mut terms, "select", &[array, index], sorts[depth].clone());
        for level in (0..depth).rev() {
            selected = app(
                &mut terms,
                &format!("field{level}"),
                &[selected],
                sorts[level].clone(),
            );
        }
        let assertion = equals_bv(&mut terms, selected, 5);
        let result = verdict(&terms, &StubModel::new(), &[assertion]);
        if depth == 4 {
            assert_confirmed(&result);
        } else {
            assert_cannot(&result);
        }
    }
    let mut terms = TermStore::new();
    let f = Fixture::new(&mut terms);
    let mut assertions = Vec::new();
    for ordinal in 0..=residual::MAX_WITNESS_ENTRIES {
        let index = terms.mk_bitvec(BigInt::from(ordinal), 64);
        let [_, _, length] = f.read(&mut terms, f.a, index);
        assertions.push(equals_bv(&mut terms, length, 5));
    }
    assert_confirmed(&verdict(&terms, &StubModel::new(), &assertions[..1]));
    assert_cannot(&verdict(&terms, &StubModel::new(), &assertions));
    assert_confirmed(&verdict(&terms, &StubModel::new(), &assertions[..1]));
}

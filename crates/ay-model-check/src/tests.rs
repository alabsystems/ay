// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Hand-constructed `(assertions, model)` pairs exercising the gate:
//!
//! * (a) models that SATISFY ⇒ `ConfirmedSat`;
//! * (b) models that VIOLATE an assertion ⇒ `ModelViolates` — including
//!   analogues of real wrong-`sat` bugs (seq prefix, array select, datatype
//!   recognizer, seq.indexof);
//! * (c) under-specified / unimplemented / unpinned / quantified ⇒
//!   `CannotConfirm` (never a false `ConfirmedSat`).

use super::*;
use ay_core::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort, Symbol, TermId, TermStore};
use num_bigint::BigInt;
use num_rational::BigRational;
use std::cell::Cell;
use std::collections::HashMap;

/// A trivial stub model: a fixed map from leaf `TermId` to value.
struct StubModel {
    leaves: HashMap<TermId, ModelValue>,
    datatypes: HashMap<String, DatatypeSort>,
}

impl StubModel {
    fn new() -> Self {
        Self {
            leaves: HashMap::new(),
            datatypes: HashMap::new(),
        }
    }
    fn with(mut self, t: TermId, v: ModelValue) -> Self {
        self.leaves.insert(t, v);
        self
    }
    fn with_datatype(mut self, datatype: DatatypeSort) -> Self {
        self.datatypes.insert(datatype.name.clone(), datatype);
        self
    }
}

impl ModelView for StubModel {
    fn leaf_value(&self, t: TermId) -> Option<ModelValue> {
        self.leaves.get(&t).cloned()
    }

    fn datatype_def(&self, name: &str) -> Option<DatatypeSort> {
        self.datatypes.get(name).cloned()
    }
}

fn int(n: i64) -> BigInt {
    BigInt::from(n)
}

fn sqrt_two_between(lo: BigRational, hi: BigRational) -> ModelValue {
    ModelValue::Algebraic(Box::new(
        algebraic::Algebraic::root_of(algebraic::integer_poly(&[-2, 0, 1]), lo, hi)
            .expect("the interval isolates positive sqrt(2)"),
    ))
}

fn app(ts: &mut TermStore, name: &str, args: &[TermId], sort: Sort) -> TermId {
    ts.mk_app(Symbol::named(name), args, sort)
}

fn verdict(ts: &TermStore, model: &dyn ModelView, asserts: &[TermId]) -> GateVerdict {
    confirm_model(ts, model, asserts)
}

fn assert_confirmed(v: &GateVerdict) {
    assert!(
        matches!(v, GateVerdict::ConfirmedSat),
        "expected ConfirmedSat, got {v:?}"
    );
}
fn assert_violates(v: &GateVerdict) {
    assert!(
        matches!(v, GateVerdict::ModelViolates { .. }),
        "expected ModelViolates, got {v:?}"
    );
}
fn assert_cannot(v: &GateVerdict) {
    assert!(
        matches!(v, GateVerdict::CannotConfirm { .. }),
        "expected CannotConfirm, got {v:?}"
    );
}

/// Structured datatype fields compare recursively at their declared sort, so
/// exact Array/Seq values preserve ordinary datatype equality. Constructor
/// identity remains decisive, while opaque and wrong-arity encodings are still
/// rejected instead of being coerced into the declared datatype.
#[test]
fn datatype_extensional_fields_are_typed_and_noncanonical_values_fail_closed() {
    let cases = [
        (
            "ArrayBox",
            "ArrayBox_mk",
            Sort::array(Sort::Int, Sort::Int),
            ModelValue::Array(Box::new(ArrayValue {
                default: ModelValue::Int(int(0)),
                store: Vec::new(),
            })),
            ModelValue::Array(Box::new(ArrayValue {
                default: ModelValue::Int(int(1)),
                store: Vec::new(),
            })),
        ),
        (
            "SeqBox",
            "SeqBox_mk",
            Sort::seq(Sort::Int),
            ModelValue::Seq(vec![ModelValue::Int(int(0))]),
            ModelValue::Seq(vec![ModelValue::Int(int(1))]),
        ),
    ];

    for (datatype_name, constructor_name, field_sort, field_value, different_field_value) in cases {
        let mut terms = TermStore::new();
        let datatype = Sort::Datatype(DatatypeSort::new(
            datatype_name,
            vec![DatatypeConstructor::new(
                constructor_name,
                vec![DatatypeField::new("payload", field_sort)],
            )],
        ));
        let left = terms.mk_var(format!("{datatype_name}_left"), datatype.clone());
        let right = terms.mk_var(format!("{datatype_name}_right"), datatype.clone());
        let equality = app(&mut terms, "=", &[left, right], Sort::Bool);
        let canonical = ModelValue::Datatype {
            ctor: constructor_name.to_string(),
            args: vec![field_value],
        };
        assert_confirmed(&verdict(
            &terms,
            &StubModel::new()
                .with(left, canonical.clone())
                .with(right, canonical.clone()),
            &[equality],
        ));
        assert_violates(&verdict(
            &terms,
            &StubModel::new().with(left, canonical).with(
                right,
                ModelValue::Datatype {
                    ctor: constructor_name.to_string(),
                    args: vec![different_field_value],
                },
            ),
            &[equality],
        ));

        let wrong_arity = ModelValue::Datatype {
            ctor: constructor_name.to_string(),
            args: Vec::new(),
        };
        assert_cannot(&verdict(
            &terms,
            &StubModel::new()
                .with(left, wrong_arity.clone())
                .with(right, wrong_arity),
            &[equality],
        ));
        assert_cannot(&verdict(
            &terms,
            &StubModel::new()
                .with(left, ModelValue::Uninterpreted("@opaque!0".to_string()))
                .with(right, ModelValue::Uninterpreted("@opaque!0".to_string())),
            &[equality],
        ));
    }
}

#[test]
fn datatype_constructor_identity_remains_decisive_with_extensional_fields() {
    let mut terms = TermStore::new();
    let array_sort = Sort::array(Sort::Int, Sort::Int);
    let datatype = Sort::Datatype(DatatypeSort::new(
        "ChoiceBox",
        vec![
            DatatypeConstructor::new(
                "ChoiceBox_left",
                vec![DatatypeField::new("left_payload", array_sort.clone())],
            ),
            DatatypeConstructor::new(
                "ChoiceBox_right",
                vec![DatatypeField::new("right_payload", array_sort)],
            ),
        ],
    ));
    let left = terms.mk_var("choice_left", datatype.clone());
    let right = terms.mk_var("choice_right", datatype);
    let equality = app(&mut terms, "=", &[left, right], Sort::Bool);
    let array = || {
        ModelValue::Array(Box::new(ArrayValue {
            default: ModelValue::Int(int(0)),
            store: Vec::new(),
        }))
    };
    assert_violates(&verdict(
        &terms,
        &StubModel::new()
            .with(
                left,
                ModelValue::Datatype {
                    ctor: "ChoiceBox_left".to_string(),
                    args: vec![array()],
                },
            )
            .with(
                right,
                ModelValue::Datatype {
                    ctor: "ChoiceBox_right".to_string(),
                    args: vec![array()],
                },
            ),
        &[equality],
    ));
}

fn assert_identical_value_cannot_confirm(context: &str, sort: Sort, value: ModelValue) {
    let mut terms = TermStore::new();
    let left = terms.mk_var("typed_left", sort.clone());
    let right = terms.mk_var("typed_right", sort);
    let equality = app(&mut terms, "=", &[left, right], Sort::Bool);
    let result = verdict(
        &terms,
        &StubModel::new()
            .with(left, value.clone())
            .with(right, value),
        &[equality],
    );
    assert!(
        matches!(result, GateVerdict::CannotConfirm { .. }),
        "{context}: expected CannotConfirm, got {result:?}"
    );
}

/// Identical payloads are not enough to confirm equality: both operands must
/// recursively inhabit the sort attached to the equality. These are the exact
/// scalar, sequence, array, and datatype-field mutations that the former
/// shape-erasing fallback accepted as equal.
#[test]
fn typed_equality_rejects_identical_malformed_nested_values() {
    let malformed_datatype_sort = Sort::Datatype(DatatypeSort::new(
        "TypedBox",
        vec![DatatypeConstructor::new(
            "TypedBox_mk",
            vec![DatatypeField::new("payload", Sort::Int)],
        )],
    ));

    let cases = vec![
        ("scalar", Sort::Int, ModelValue::Bool(true)),
        (
            "bitvector width",
            Sort::bitvec(16),
            ModelValue::BitVec {
                width: 8,
                value: int(1),
            },
        ),
        (
            "bitvector range",
            Sort::bitvec(8),
            ModelValue::BitVec {
                width: 8,
                value: BigInt::from(256u16),
            },
        ),
        (
            "floating-point payload",
            Sort::FloatingPoint(8, 24),
            ModelValue::FloatingPoint {
                sign: false,
                exponent: 256,
                significand: 0,
                exponent_bits: 8,
                significand_bits: 24,
            },
        ),
        (
            "character range",
            Sort::Char,
            ModelValue::Int(BigInt::from(0x3_0000u32)),
        ),
        (
            "finite-domain range",
            Sort::FiniteDomain("Tiny".to_string(), 2),
            ModelValue::Int(int(2)),
        ),
        (
            "regular-language carrier",
            Sort::RegLan,
            ModelValue::Uninterpreted("@regex!0".to_string()),
        ),
        (
            "sequence element",
            Sort::seq(Sort::Int),
            ModelValue::Seq(vec![ModelValue::Bool(true)]),
        ),
        (
            "array default",
            Sort::array(Sort::Int, Sort::Int),
            ModelValue::Array(Box::new(ArrayValue {
                default: ModelValue::Bool(false),
                store: Vec::new(),
            })),
        ),
        (
            "array key",
            Sort::array(Sort::Int, Sort::Int),
            ModelValue::Array(Box::new(ArrayValue {
                default: ModelValue::Int(int(0)),
                store: vec![(ModelValue::Bool(false), ModelValue::Int(int(1)))],
            })),
        ),
        (
            "array cell",
            Sort::array(Sort::Int, Sort::Int),
            ModelValue::Array(Box::new(ArrayValue {
                default: ModelValue::Int(int(0)),
                store: vec![(ModelValue::Int(int(1)), ModelValue::Bool(true))],
            })),
        ),
        (
            "datatype field",
            malformed_datatype_sort,
            ModelValue::Datatype {
                ctor: "TypedBox_mk".to_string(),
                args: vec![ModelValue::Bool(true)],
            },
        ),
    ];

    for (description, sort, value) in cases {
        assert_identical_value_cannot_confirm(description, sort, value);
    }
}

/// Preserve canonical nested witnesses, including the exact Int-to-Real value
/// coercion used by `to_real`, while authenticating every aggregate layer.
#[test]
fn typed_equality_accepts_valid_nested_values() {
    let payload_sort = Sort::seq(Sort::array(Sort::Int, Sort::seq(Sort::Real)));
    let datatype_sort = Sort::Datatype(DatatypeSort::new(
        "NestedBox",
        vec![DatatypeConstructor::new(
            "NestedBox_mk",
            vec![DatatypeField::new("payload", payload_sort.clone())],
        )],
    ));
    let payload = ModelValue::Seq(vec![ModelValue::Array(Box::new(ArrayValue {
        default: ModelValue::Seq(vec![
            ModelValue::Int(int(1)),
            ModelValue::Real(BigRational::new(int(3), int(2))),
        ]),
        store: vec![(
            ModelValue::Int(int(4)),
            ModelValue::Seq(vec![ModelValue::Real(BigRational::from_integer(int(7)))]),
        )],
    }))]);
    let canonical = ModelValue::Datatype {
        ctor: "NestedBox_mk".to_string(),
        args: vec![payload],
    };

    let mut terms = TermStore::new();
    let left = terms.mk_var("nested_left", datatype_sort.clone());
    let right = terms.mk_var("nested_right", datatype_sort);
    let equality = app(&mut terms, "=", &[left, right], Sort::Bool);
    assert_confirmed(&verdict(
        &terms,
        &StubModel::new()
            .with(left, canonical.clone())
            .with(right, canonical),
        &[equality],
    ));
}

/// Sequence equality must retain the element sort while descending: otherwise
/// a nested array falls back to the shape-only comparator and cannot prove that
/// stores covering every Bool index make differing defaults unreachable.
#[test]
fn typed_sequence_elements_retain_nested_array_extensionality() {
    let sequence_sort = Sort::seq(Sort::array(Sort::Bool, Sort::Int));
    let array = |default: i64, true_value: i64| {
        ModelValue::Array(Box::new(ArrayValue {
            default: ModelValue::Int(int(default)),
            store: vec![
                (ModelValue::Bool(false), ModelValue::Int(int(7))),
                (ModelValue::Bool(true), ModelValue::Int(int(true_value))),
            ],
        }))
    };

    let mut terms = TermStore::new();
    let left = terms.mk_var("array_seq_left", sequence_sort.clone());
    let right = terms.mk_var("array_seq_right", sequence_sort);
    let equality = app(&mut terms, "=", &[left, right], Sort::Bool);
    let left_value = ModelValue::Seq(vec![array(0, 8)]);
    let extensionally_equal = ModelValue::Seq(vec![array(99, 8)]);
    assert_confirmed(&verdict(
        &terms,
        &StubModel::new()
            .with(left, left_value.clone())
            .with(right, extensionally_equal),
        &[equality],
    ));

    let different = ModelValue::Seq(vec![array(99, 9)]);
    assert_violates(&verdict(
        &terms,
        &StubModel::new()
            .with(left, left_value)
            .with(right, different),
        &[equality],
    ));
}

#[test]
fn registered_enum_indices_retain_finite_array_coverage() {
    let datatype = DatatypeSort::new(
        "RegisteredColor",
        vec![
            DatatypeConstructor::unit("RegisteredRed"),
            DatatypeConstructor::unit("RegisteredBlue"),
        ],
    );
    let array_sort = Sort::array(Sort::Uninterpreted(datatype.name.clone()), Sort::Int);
    let constructor = |name: &str| ModelValue::Datatype {
        ctor: name.to_string(),
        args: Vec::new(),
    };
    let array = |default: i64| {
        ModelValue::Array(Box::new(ArrayValue {
            default: ModelValue::Int(int(default)),
            store: vec![
                (constructor("RegisteredRed"), ModelValue::Int(int(7))),
                (constructor("RegisteredBlue"), ModelValue::Int(int(8))),
            ],
        }))
    };

    let mut terms = TermStore::new();
    let left = terms.mk_var("registered_array_left", array_sort.clone());
    let right = terms.mk_var("registered_array_right", array_sort);
    let equality = app(&mut terms, "=", &[left, right], Sort::Bool);
    assert_confirmed(&verdict(
        &terms,
        &StubModel::new()
            .with_datatype(datatype)
            .with(left, array(0))
            .with(right, array(99)),
        &[equality],
    ));
}

/// Array equality must not materialise the full cardinality of a model-provided
/// bitvector index sort merely to prove that an empty key set does not cover it.
#[test]
fn huge_bitvector_index_cardinality_is_not_allocated() {
    let array_sort = Sort::array(Sort::bitvec(u32::MAX), Sort::Int);
    let mut terms = TermStore::new();
    let left = terms.mk_var("huge_bv_array_left", array_sort.clone());
    let right = terms.mk_var("huge_bv_array_right", array_sort);
    let equality = app(&mut terms, "=", &[left, right], Sort::Bool);
    let array = |default: i64| {
        ModelValue::Array(Box::new(ArrayValue {
            default: ModelValue::Int(int(default)),
            store: Vec::new(),
        }))
    };
    assert_violates(&verdict(
        &terms,
        &StubModel::new().with(left, array(0)).with(right, array(1)),
        &[equality],
    ));
}

#[test]
fn typed_array_comparison_budget_bounds_quadratic_unique_key_search() {
    let array_sort = Sort::array(Sort::Int, Sort::Int);
    let array = |stores: usize| {
        ModelValue::Array(Box::new(ArrayValue {
            default: ModelValue::Int(int(0)),
            store: (0..stores)
                .map(|index| {
                    let value = BigInt::from(index);
                    (ModelValue::Int(value.clone()), ModelValue::Int(value))
                })
                .collect(),
        }))
    };

    // 300 authenticated stores fit comfortably inside the 8192-node shape
    // budget, but two ordered-table searches for every union key are
    // quadratic and must stop at the separate comparison meter.
    assert_identical_value_cannot_confirm(
        "typed array comparison budget",
        array_sort.clone(),
        array(300),
    );

    // Preserve useful headroom below the meter; this still exercises thousands
    // of semantic key comparisons rather than a trivial short path.
    let mut terms = TermStore::new();
    let left = terms.mk_var("bounded_array_left", array_sort.clone());
    let right = terms.mk_var("bounded_array_right", array_sort);
    let equality = app(&mut terms, "=", &[left, right], Sort::Bool);
    let value = array(100);
    assert_confirmed(&verdict(
        &terms,
        &StubModel::new()
            .with(left, value.clone())
            .with(right, value),
        &[equality],
    ));
}

#[test]
fn typed_array_comparison_budget_counts_nested_key_work() {
    let key_sort = Sort::seq(Sort::Int);
    let array_sort = Sort::array(key_sort, Sort::Int);
    let mut stores = Vec::new();
    for index in 0..30 {
        let mut key = vec![ModelValue::Int(int(0)); 99];
        key.push(ModelValue::Int(BigInt::from(index)));
        stores.push((ModelValue::Seq(key), ModelValue::Int(BigInt::from(index))));
    }
    let value = ModelValue::Array(Box::new(ArrayValue {
        default: ModelValue::Int(int(0)),
        store: stores,
    }));

    // Each pair of distinct keys shares a 99-element prefix. Charging only
    // top-level array comparisons would miss this multiplicative work; the
    // recursive meter must decline the equality deterministically.
    assert_identical_value_cannot_confirm("nested array-key comparison budget", array_sort, value);
}

#[test]
fn typed_value_depth_and_work_limits_fail_closed() {
    let oversized = ModelValue::Seq(
        (0..9000)
            .map(|index| ModelValue::Int(BigInt::from(index)))
            .collect(),
    );
    assert_identical_value_cannot_confirm(
        "typed value work budget",
        Sort::seq(Sort::Int),
        oversized,
    );

    let mut deep_sort = Sort::Int;
    let mut deep_value = ModelValue::Int(int(0));
    for _ in 0..300 {
        deep_sort = Sort::seq(deep_sort);
        deep_value = ModelValue::Seq(vec![deep_value]);
    }
    assert_identical_value_cannot_confirm("typed value depth budget", deep_sort, deep_value);
}

// ===========================================================================
// (a) Satisfying models ⇒ ConfirmedSat
// ===========================================================================

include!("tests/scalar_regex_and_fp.rs");

include!("tests/division_and_fallbacks.rs");

include!("tests/arrays_and_lambda.rs");

include!("tests/violations_and_short_circuit.rs");

// ===========================================================================
// (d) Uninterpreted-function applications — value-keyed function graph
//
// An uninterpreted function is single-valued: two applications whose ARGUMENTS
// evaluate to equal values must return the same value. The gate builds a
// value-keyed graph as it evaluates (`uf_app_value` supplies the committed
// per-application value); the FIRST application to reach a given
// `(name, arg-values)` key fixes the value for every later application with the
// same key. This is what catches the QF_UFLIA / array-select wrong-model class
// where a degenerate integer assignment collapses two distinct applications'
// arguments to the same value while the model pins them to different results.
// ===========================================================================

/// A model implementing only the original one-argument unconstrained hook.
///
/// Its tests protect source compatibility and, more importantly, prove that
/// the new typed default does not silently extend this legacy authority to
/// division-by-zero applications.
struct LegacyUnconstrainedModel {
    leaves: HashMap<TermId, ModelValue>,
    unconstrained_apps: HashMap<TermId, ModelValue>,
    unconstrained_calls: Cell<usize>,
}

impl LegacyUnconstrainedModel {
    fn new() -> Self {
        Self {
            leaves: HashMap::new(),
            unconstrained_apps: HashMap::new(),
            unconstrained_calls: Cell::new(0),
        }
    }

    fn leaf(mut self, t: TermId, v: ModelValue) -> Self {
        self.leaves.insert(t, v);
        self
    }

    fn unconstrained(mut self, t: TermId, v: ModelValue) -> Self {
        self.unconstrained_apps.insert(t, v);
        self
    }
}

impl ModelView for LegacyUnconstrainedModel {
    fn leaf_value(&self, t: TermId) -> Option<ModelValue> {
        self.leaves.get(&t).cloned()
    }

    fn unconstrained_app_value(&self, t: TermId) -> Option<ModelValue> {
        self.unconstrained_calls
            .set(self.unconstrained_calls.get() + 1);
        self.unconstrained_apps.get(&t).cloned()
    }
}

/// A stub model that also answers `uf_app_value` for whole application terms.
struct UfStubModel {
    leaves: HashMap<TermId, ModelValue>,
    uf_apps: HashMap<TermId, ModelValue>,
    unconstrained_apps: HashMap<TermId, (ProvenUnconstrainedKind, ModelValue)>,
    unconstrained_calls: Cell<usize>,
    selects: HashMap<TermId, ModelValue>,
    projections: HashMap<TermId, usize>,
    projection_errors: HashMap<TermId, String>,
}

impl UfStubModel {
    fn new() -> Self {
        Self {
            leaves: HashMap::new(),
            uf_apps: HashMap::new(),
            unconstrained_apps: HashMap::new(),
            unconstrained_calls: Cell::new(0),
            selects: HashMap::new(),
            projections: HashMap::new(),
            projection_errors: HashMap::new(),
        }
    }
    fn leaf(mut self, t: TermId, v: ModelValue) -> Self {
        self.leaves.insert(t, v);
        self
    }
    fn uf(mut self, t: TermId, v: ModelValue) -> Self {
        self.uf_apps.insert(t, v);
        self
    }
    fn unconstrained(mut self, t: TermId, kind: ProvenUnconstrainedKind, v: ModelValue) -> Self {
        self.unconstrained_apps.insert(t, (kind, v));
        self
    }
    fn sel(mut self, t: TermId, v: ModelValue) -> Self {
        self.selects.insert(t, v);
        self
    }
    fn projection(mut self, t: TermId, selected: usize) -> Self {
        self.projections.insert(t, selected);
        self
    }
    fn projection_error(mut self, t: TermId, detail: &str) -> Self {
        self.projection_errors.insert(t, detail.to_string());
        self
    }
}

impl ModelView for UfStubModel {
    fn leaf_value(&self, t: TermId) -> Option<ModelValue> {
        self.leaves.get(&t).cloned()
    }
    fn projection_argument(&self, t: TermId) -> Result<Option<usize>, ProjectionLookupError> {
        if let Some(detail) = self.projection_errors.get(&t) {
            return Err(ProjectionLookupError::inconsistent_model(detail.clone()));
        }
        Ok(self.projections.get(&t).copied())
    }
    fn uf_app_value(&self, t: TermId) -> Option<ModelValue> {
        self.uf_apps.get(&t).cloned()
    }
    fn proven_unconstrained_app_value(
        &self,
        t: TermId,
        kind: ProvenUnconstrainedKind,
    ) -> Option<ModelValue> {
        self.unconstrained_calls
            .set(self.unconstrained_calls.get() + 1);
        self.unconstrained_apps
            .get(&t)
            .and_then(|(expected, value)| (*expected == kind).then(|| value.clone()))
    }
    fn array_select_value(&self, t: TermId) -> Option<ModelValue> {
        self.selects.get(&t).cloned()
    }
}

include!("tests/uf_congruence_and_projection.rs");

// ===========================================================================
// (e) Array-`select` reads via the model — value-keyed select graph
//
// `select` over an array is a single-valued function of the index. When the
// gate cannot resolve the array operand to a concrete `(default, finite-store)`
// value (a partial / unreconstructable array leaf), it reads the model's
// committed per-read value (`array_select_value`) but keys reads by
// `(array-term, index-value)` and takes the first committed value per key. Two
// reads of the SAME array at index values that evaluate EQUAL therefore resolve
// to one element — exposing (rather than honouring) a model that pins them to
// different values — and, because the gate evaluates indices itself, a
// degenerate array whose reads contradict an asserted (in)equality evaluates the
// assertion to `false`. This is the array analogue of the UF value-keyed graph
// above, closing the array-`select` wrong-model class (#array-select-collapse)
// at the gate even when the theory's array interpretation is unavailable.
// ===========================================================================

/// A stub model that pins scalar leaves and answers `array_select_value` for
/// whole `(select A i)` application terms — but deliberately does NOT pin the
/// array leaf itself, so the gate must go through the `select`-via-model fallback
/// (mirroring the real gate, whose fallback fires exactly when the theory array
/// interpretation cannot be reconstructed).
struct ArraySelectStubModel {
    leaves: HashMap<TermId, ModelValue>,
    selects: HashMap<TermId, ModelValue>,
}

impl ArraySelectStubModel {
    fn new() -> Self {
        Self {
            leaves: HashMap::new(),
            selects: HashMap::new(),
        }
    }
    fn leaf(mut self, t: TermId, v: ModelValue) -> Self {
        self.leaves.insert(t, v);
        self
    }
    fn sel(mut self, t: TermId, v: ModelValue) -> Self {
        self.selects.insert(t, v);
        self
    }
}

impl ModelView for ArraySelectStubModel {
    fn leaf_value(&self, t: TermId) -> Option<ModelValue> {
        self.leaves.get(&t).cloned()
    }
    fn array_select_value(&self, t: TermId) -> Option<ModelValue> {
        self.selects.get(&t).cloned()
    }
}

include!("tests/array_select_models.rs");

// ===========================================================================
// (d) The model-INDEPENDENT datatype-congruence NORMALIZER
//     (`is_datatype_tautology_with`): it must PROVE genuine free-datatype
//     tautologies AND REJECT every near-miss non-tautology (soundness).
// ===========================================================================

/// `Option`-like datatype: `None` (nullary) + `Some(value: Int)`.
fn option_sort() -> Sort {
    Sort::Datatype(DatatypeSort::new(
        "Opt",
        vec![
            DatatypeConstructor::new("None", vec![]),
            DatatypeConstructor::new("Some", vec![DatatypeField::new("value", Sort::Int)]),
        ],
    ))
}

/// Single-constructor datatype `Box = Mk(fst: Int, snd: Int)`.
fn box_sort() -> Sort {
    Sort::Datatype(DatatypeSort::new(
        "Box",
        vec![DatatypeConstructor::new(
            "Mk",
            vec![
                DatatypeField::new("fst", Sort::Int),
                DatatypeField::new("snd", Sort::Int),
            ],
        )],
    ))
}

fn is_taut(ts: &TermStore, t: TermId) -> bool {
    is_datatype_tautology_with(ts, t, &|_| None)
}

include!("tests/datatype_normalization.rs");

// ===========================================================================
// (e) Residual free-datatype-array joint-satisfiability
//     (#free-dt-array-residual): a residue consisting ONLY of alias
//     equalities and ground element reads over FREE datatype-element arrays
//     confirms iff no two constraints force different values at one
//     (class, index, field) slot. Everything else stays fail-closed.
// ===========================================================================

/// Datatype `S = mk(f: Int, g: Int)` and its array sort `(Array Int S)`.
fn struct_sort() -> Sort {
    Sort::Datatype(DatatypeSort::new(
        "S",
        vec![DatatypeConstructor::new(
            "mk",
            vec![
                DatatypeField::new("f", Sort::Int),
                DatatypeField::new("g", Sort::Int),
            ],
        )],
    ))
}

/// `(= <ground-int> (fld (select arr idx)))` — a field read over `arr`.
fn field_read_eq(
    ts: &mut TermStore,
    fld: &str,
    arr: TermId,
    idx: TermId,
    ground: TermId,
) -> TermId {
    let sel = app(ts, "select", &[arr, idx], struct_sort());
    let prj = app(ts, fld, &[sel], Sort::Int);
    app(ts, "=", &[ground, prj], Sort::Bool)
}

include!("tests/datatype_array_residuals.rs");

// --- seq.last_indexof / seq.replace_all value-level parity (#p0.1-seq) ------
//
// These VALUE-level tests pin the independent-gate evaluator's semantics for
// `seq.last_indexof` and `seq.replace_all` against HAND-COMPUTED SMT-LIB
// results. z3 4.15.4 is deliberately NOT used as the oracle here: it does not
// recognise `seq.replace_all` at all ("unknown constant") and it computes
// WRONG `seq.last_indexof` values (its rightmost-of-[5,5] for [5] is neither 0
// nor 1). The gate must therefore be validated against the specification, and
// its implementation is kept independent of the solver's own evaluator
// (crate::seq uses `match_at`; the solver uses inline loops) so a shared bug
// cannot mutually confirm a wrong `sat`.

fn mvseq_i(xs: &[i64]) -> ModelValue {
    ModelValue::Seq(xs.iter().map(|&n| ModelValue::Int(int(n))).collect())
}

fn li(s: &[i64], sub: &[i64]) -> BigInt {
    match seq::eval("seq.last_indexof", &[mvseq_i(s), mvseq_i(sub)]).unwrap() {
        ModelValue::Int(n) => n,
        other => panic!("expected Int, got {other:?}"),
    }
}

fn ra(s: &[i64], src: &[i64], dst: &[i64]) -> Vec<i64> {
    match seq::eval("seq.replace_all", &[mvseq_i(s), mvseq_i(src), mvseq_i(dst)]).unwrap() {
        ModelValue::Seq(v) => v
            .into_iter()
            .map(|e| match e {
                ModelValue::Int(n) => n.try_into().unwrap(),
                other => panic!("expected Int element, got {other:?}"),
            })
            .collect(),
        other => panic!("expected Seq, got {other:?}"),
    }
}

include!("tests/sequence_last_indexof.rs");

// ---------------------------------------------------------------------------
// Higher-order combinators (#ho-seq).
//
// The function operand is a FUNCTION-AS-ARRAY, curried exactly as
// `Z3_mk_seq_map` / `Z3_mk_seq_foldl` build it. Before these, the gate reported
// `unsupported sequence operator seq.map` for EVERY assertion mentioning one,
// so a genuine `sat` over a ground `seq.map` could never be confirmed and
// always degraded to `unknown`. Values are hand-computed from the combinator
// definitions; the fail-closed corners (non-array function operand, an
// unevaluable curried layer) are pinned alongside.

/// An `(Array Int Int)` value from explicit `index -> value` pins.
fn mvarr_i(default: i64, pins: &[(i64, i64)]) -> ModelValue {
    ModelValue::Array(Box::new(ArrayValue {
        default: ModelValue::Int(int(default)),
        store: pins
            .iter()
            .map(|&(k, v)| (ModelValue::Int(int(k)), ModelValue::Int(int(v))))
            .collect(),
    }))
}

/// An `(Array Int (Array Int Int))` value from a default inner array plus pins.
fn mvarr2_i(default_inner: ModelValue, pins: &[(i64, ModelValue)]) -> ModelValue {
    ModelValue::Array(Box::new(ArrayValue {
        default: default_inner,
        store: pins
            .iter()
            .map(|(k, v)| (ModelValue::Int(int(*k)), v.clone()))
            .collect(),
    }))
}

fn int_of(value: &ModelValue) -> BigInt {
    match value {
        ModelValue::Int(n) => n.clone(),
        other => panic!("expected Int, got {other:?}"),
    }
}

fn ints_of(value: &ModelValue) -> Vec<i64> {
    match value {
        ModelValue::Seq(v) => v
            .iter()
            .map(|e| match e {
                ModelValue::Int(n) => n.try_into().unwrap(),
                other => panic!("expected Int element, got {other:?}"),
            })
            .collect(),
        other => panic!("expected Seq, got {other:?}"),
    }
}

include!("tests/sequence_higher_order.rs");

// ===========================================================================
// str.replace_re / str.replace_re_all
//
// SMT-LIB 2.6 Unicode Strings decomposes `s = x ++ w ++ z` with `w` in `[[r]]`,
// `|x|` minimal and THEN `|w|` minimal (leftmost, then shortest).
// `str.replace_re` rewrites that one occurrence; `str.replace_re_all` recurses
// on `z`, under the extra `w != ""` side condition. A regex that accepts the
// empty word is where the two clauses come apart, and this gate deliberately
// fails closed there — see `crate::regex::replace`.
//
// Every case below is fully ground, so the verdict is decided entirely by this
// crate's evaluator and its own interval matcher.
// ===========================================================================

fn re_lit(ts: &mut TermStore, text: &str) -> TermId {
    let s = ts.mk_string(text.to_string());
    app(ts, "str.to_re", &[s], Sort::RegLan)
}

fn re_range(ts: &mut TermStore, lo: &str, hi: &str) -> TermId {
    let lo = ts.mk_string(lo.to_string());
    let hi = ts.mk_string(hi.to_string());
    app(ts, "re.range", &[lo, hi], Sort::RegLan)
}

/// Gate `(= (<op> <subject> <regex> <replacement>) <expected>)`.
fn replace_re_verdict(
    op: &str,
    build_regex: impl FnOnce(&mut TermStore) -> TermId,
    subject: &str,
    replacement: &str,
    expected: &str,
) -> GateVerdict {
    let mut ts = TermStore::new();
    let regex = build_regex(&mut ts);
    let s = ts.mk_string(subject.to_string());
    let t = ts.mk_string(replacement.to_string());
    let call = app(&mut ts, op, &[s, regex, t], Sort::String);
    let want = ts.mk_string(expected.to_string());
    let eq = app(&mut ts, "=", &[call, want], Sort::Bool);
    verdict(&ts, &StubModel::new(), &[eq])
}

// ── the shape the group_strings regression exercised: a union pattern ──

include!("tests/regex_replacement.rs");

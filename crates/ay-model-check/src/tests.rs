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

fn identical_value_verdict(sort: Sort, value: ModelValue) -> GateVerdict {
    let mut terms = TermStore::new();
    let left = terms.mk_var("typed_left", sort.clone());
    let right = terms.mk_var("typed_right", sort);
    let equality = app(&mut terms, "=", &[left, right], Sort::Bool);
    verdict(
        &terms,
        &StubModel::new()
            .with(left, value.clone())
            .with(right, value),
        &[equality],
    )
}

fn assert_identical_value_cannot_confirm(context: &str, sort: Sort, value: ModelValue) {
    let result = identical_value_verdict(sort, value);
    assert!(
        matches!(result, GateVerdict::CannotConfirm { .. }),
        "{context}: expected CannotConfirm, got {result:?}"
    );
}

fn assert_identical_value_confirmed(context: &str, sort: Sort, value: ModelValue) {
    let result = identical_value_verdict(sort, value);
    assert!(
        matches!(result, GateVerdict::ConfirmedSat),
        "{context}: expected ConfirmedSat, got {result:?}"
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

/// The comparison meter still bounds the ordered-rescan union search, and the
/// canonical-key fast lane decides the shapes it can encode instead of
/// exhausting that meter.
///
/// The 300-store `Int`-indexed case was pinned as `CannotConfirm` when the only
/// algorithm was the quadratic rescan. It is not stale coverage of a
/// limitation that still exists -- the limitation is GONE for an encodable
/// index sort, so the pin is strengthened to the decision the checker now owes:
/// two identical arrays are provably equal. The meter itself is re-pinned below
/// on `Real` indices, which the fast lane must decline because one real number
/// has several `ModelValue` encodings, leaving the quadratic rescan and its
/// budget exactly as `7b7c826068` wrote them.
#[test]
fn typed_array_comparison_budget_bounds_quadratic_unique_key_search() {
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
    // budget. Two ordered-table searches per union key would be quadratic and
    // exhaust the comparison meter; canonical `Int` keys make the union search
    // linear, so the equality is decided rather than abandoned.
    let int_indexed = Sort::array(Sort::Int, Sort::Int);
    assert_identical_value_confirmed(
        "typed array comparison budget",
        int_indexed.clone(),
        array(300),
    );

    // Preserve useful headroom below the meter; this still exercises thousands
    // of semantic key comparisons rather than a trivial short path.
    assert_identical_value_confirmed("bounded array comparison", int_indexed, array(100));

    // Re-pin the meter on a shape that is still genuinely quadratic. `Int`,
    // `Real` and `Algebraic` payloads all denote reals, so equality at `Real`
    // is not structural and the fast lane must decline -- leaving the ordered
    // rescan, whose 300-key union search the meter has to stop.
    assert_identical_value_cannot_confirm(
        "unencodable index sort keeps the quadratic meter",
        Sort::array(Sort::Real, Sort::Int),
        array(300),
    );
}

/// Nested aggregate key work is still charged multiplicatively, and encoding a
/// nested key is charged too.
///
/// As above, the `Seq Int` case is strengthened from "declines" to "decides":
/// a sequence of canonical elements is itself canonical, so the fast lane
/// linearises it. The multiplicative-work pin moves to `Seq Real` keys, whose
/// elements the fast lane must decline, restoring the exact quadratic shape
/// `7b7c826068` metered.
#[test]
fn typed_array_comparison_budget_counts_nested_key_work() {
    let nested_keys = |element_sort: Sort| {
        let mut stores = Vec::new();
        for index in 0..30 {
            let mut key = vec![ModelValue::Int(int(0)); 99];
            key.push(ModelValue::Int(BigInt::from(index)));
            stores.push((ModelValue::Seq(key), ModelValue::Int(BigInt::from(index))));
        }
        (
            Sort::array(Sort::seq(element_sort), Sort::Int),
            ModelValue::Array(Box::new(ArrayValue {
                default: ModelValue::Int(int(0)),
                store: stores,
            })),
        )
    };

    // Each pair of distinct keys shares a 99-element prefix, so encoding the
    // keys is itself 3000 charged steps -- still far below the meter, and the
    // equality is decided.
    let (array_sort, value) = nested_keys(Sort::Int);
    assert_identical_value_confirmed("nested array-key comparison budget", array_sort, value);

    // The same 30 keys over an unencodable element sort fall back to the
    // ordered rescan, where the shared 99-element prefixes multiply the work
    // for every candidate pair. Charging only top-level array comparisons
    // would miss that; the recursive meter must decline deterministically.
    let (array_sort, value) = nested_keys(Sort::Real);
    assert_identical_value_cannot_confirm(
        "nested unencodable array-key comparison budget",
        array_sort,
        value,
    );
}

/// The canonical-key fast lane must agree with extensional array equality on
/// every shape it accepts -- it is a performance rewrite of
/// `array_select_at_sort`, so any disagreement is a wrong gate answer.
///
/// The oracle is independent of the evaluator: over `(_ BitVec 4)` the index
/// carrier has 16 elements, so equality is decided by reading all 16 indices
/// under plain last-write-wins. Store chains are generated with a fixed LCG and
/// deliberately contain repeated keys, so overwrites and the "later store wins"
/// rule are exercised rather than assumed.
#[test]
fn canonical_index_fast_lane_agrees_with_extensional_array_equality() {
    const WIDTH: u32 = 4;
    const INDICES: u64 = 1 << WIDTH;

    let bv = |value: u64| ModelValue::BitVec {
        width: WIDTH,
        value: BigInt::from(value % INDICES),
    };
    let read = |array: &ArrayValue, index: u64| -> u64 {
        for (key, value) in array.store.iter().rev() {
            let ModelValue::BitVec { value: key, .. } = key else {
                unreachable!("bitvector keys only")
            };
            if *key == BigInt::from(index) {
                let ModelValue::BitVec { value, .. } = value else {
                    unreachable!("bitvector elements only")
                };
                return u64::try_from(value).expect("small element");
            }
        }
        let ModelValue::BitVec { value, .. } = &array.default else {
            unreachable!("bitvector default only")
        };
        u64::try_from(value).expect("small default")
    };

    let mut seed = 0x2545_f491_4f6c_dd1du64;
    let mut next = move || {
        seed = seed
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        seed >> 33
    };

    let array_sort = Sort::array(Sort::bitvec(WIDTH), Sort::bitvec(WIDTH));
    let (mut equal_cases, mut unequal_cases) = (0u32, 0u32);
    for case in 0..64 {
        let chain = |length: u64, next: &mut dyn FnMut() -> u64| ArrayValue {
            default: bv(next()),
            store: (0..length).map(|_| (bv(next()), bv(next()))).collect(),
        };
        let left = chain(24, &mut next);
        // Half the cases rebuild the right operand as a semantically identical
        // chain: every entry is preceded by a redundant write at the SAME key,
        // which last-write-wins must discard.
        let right = if case % 2 == 0 {
            ArrayValue {
                default: left.default.clone(),
                store: left
                    .store
                    .iter()
                    .flat_map(|(key, value)| {
                        [(key.clone(), bv(next())), (key.clone(), value.clone())]
                    })
                    .collect(),
            }
        } else {
            chain(24, &mut next)
        };

        let extensionally_equal =
            (0..INDICES).all(|index| read(&left, index) == read(&right, index));
        if extensionally_equal {
            equal_cases += 1;
        } else {
            unequal_cases += 1;
        }

        let mut terms = TermStore::new();
        let left_term = terms.mk_var("fast_lane_left", array_sort.clone());
        let right_term = terms.mk_var("fast_lane_right", array_sort.clone());
        let equality = app(&mut terms, "=", &[left_term, right_term], Sort::Bool);
        let result = verdict(
            &terms,
            &StubModel::new()
                .with(left_term, ModelValue::Array(Box::new(left)))
                .with(right_term, ModelValue::Array(Box::new(right))),
            &[equality],
        );
        if extensionally_equal {
            assert!(
                matches!(result, GateVerdict::ConfirmedSat),
                "case {case}: extensionally equal arrays must confirm, got {result:?}"
            );
        } else {
            assert!(
                matches!(result, GateVerdict::ModelViolates { .. }),
                "case {case}: extensionally distinct arrays must violate, got {result:?}"
            );
        }
    }
    assert!(
        equal_cases > 0 && unequal_cases > 0,
        "the differential sweep must cover both outcomes, saw {equal_cases}/{unequal_cases}"
    );
}

/// A TOTAL bitvector-indexed array interpretation must stay decidable.
///
/// AY's model completion materialises one store entry per index value, so a
/// `(Array (_ BitVec 8) (_ BitVec 8))` model arrives with 256 entries per
/// operand. Two ordered rescans per union key is ~131k comparisons against a
/// 65_536 meter, which is what downgraded correct `QF_ABV` `sat` answers to
/// `unknown`. Raising the meter is not the fix -- the rescan grows as
/// `4 * (2^width)^2` -- so this pins the linear lane at the width that broke.
#[test]
fn total_bitvector_array_interpretation_is_decidable() {
    let total = |element: &dyn Fn(u64) -> u64| {
        ModelValue::Array(Box::new(ArrayValue {
            default: ModelValue::BitVec {
                width: 8,
                value: int(0),
            },
            store: (0..256u64)
                .map(|index| {
                    (
                        ModelValue::BitVec {
                            width: 8,
                            value: BigInt::from(index),
                        },
                        ModelValue::BitVec {
                            width: 8,
                            value: BigInt::from(element(index)),
                        },
                    )
                })
                .collect(),
        }))
    };
    let array_sort = Sort::array(Sort::bitvec(8), Sort::bitvec(8));
    assert_identical_value_confirmed(
        "total bitvector array interpretation",
        array_sort.clone(),
        total(&|index| index),
    );

    // The same size must still be able to report a genuine disagreement.
    let mut terms = TermStore::new();
    let left = terms.mk_var("total_left", array_sort.clone());
    let right = terms.mk_var("total_right", array_sort);
    let equality = app(&mut terms, "=", &[left, right], Sort::Bool);
    assert_violates(&verdict(
        &terms,
        &StubModel::new()
            .with(left, total(&|index| index))
            .with(right, total(&|index| if index == 200 { 7 } else { index })),
        &[equality],
    ));
}

/// AY's sequence-class carrier inhabits exactly the sequence sort it was minted
/// for, and nothing else does.
///
/// `ay_dpll`'s independent gate reifies a sequence term whose only model
/// evidence is an EUF equivalence class as
/// `@ay-seq-euf-class:{sort:?}:{len}:{class}`. Authenticating nested carriers
/// (`db026aa507`) started rejecting that pre-existing token, which made every
/// `=`/`distinct` over a sequence-sorted EUF leaf unevaluable. The admission is
/// a CARRIER admission and is deliberately keyed to the minted sort: an ad-hoc
/// uninterpreted value, a token minted for another sequence sort, and a token
/// compared against a concrete sequence all stay fail-closed.
#[test]
fn sequence_euf_class_carrier_inhabits_only_its_minted_sort() {
    let class_token = |sort: &Sort, class: &str| {
        ModelValue::Uninterpreted(format!(
            "@ay-seq-euf-class:{sort:?}:{}:{class}",
            class.len()
        ))
    };
    let seq_int = Sort::seq(Sort::Int);
    let seq_bool = Sort::seq(Sort::Bool);

    // Same class in the sort it was minted for: exact, decidable equality.
    assert_identical_value_confirmed(
        "sequence-class carrier",
        seq_int.clone(),
        class_token(&seq_int, "e0"),
    );

    let pair_verdict = |sort: Sort, left_value: ModelValue, right_value: ModelValue| {
        let mut terms = TermStore::new();
        let left = terms.mk_var("seq_carrier_left", sort.clone());
        let right = terms.mk_var("seq_carrier_right", sort);
        let equality = app(&mut terms, "=", &[left, right], Sort::Bool);
        verdict(
            &terms,
            &StubModel::new()
                .with(left, left_value)
                .with(right, right_value),
            &[equality],
        )
    };

    // Distinct classes are distinct elements, so `=` is provably violated.
    assert_violates(&pair_verdict(
        seq_int.clone(),
        class_token(&seq_int, "e0"),
        class_token(&seq_int, "e1"),
    ));

    // A token minted for `(Seq Int)` does not inhabit `(Seq Bool)`: the sort is
    // part of the token, so the same printable class name never aliases across
    // carriers.
    assert_cannot(&pair_verdict(
        seq_bool.clone(),
        class_token(&seq_int, "e0"),
        class_token(&seq_bool, "e0"),
    ));

    // An uninterpreted value that is not a minted carrier inhabits no sequence
    // sort at all.
    assert_identical_value_cannot_confirm(
        "ad-hoc uninterpreted value at a sequence sort",
        seq_int.clone(),
        ModelValue::Uninterpreted("e0".to_string()),
    );

    // The class name is evidence of an equivalence class, never of a
    // sequence's elements, so token-vs-sequence stays incomparable.
    assert_cannot(&pair_verdict(
        seq_int.clone(),
        class_token(&seq_int, "e0"),
        ModelValue::Seq(vec![ModelValue::Int(int(0))]),
    ));

    // The carrier is admitted at sequence sorts only.
    assert_identical_value_cannot_confirm(
        "sequence-class carrier at a non-sequence sort",
        Sort::Int,
        class_token(&seq_int, "e0"),
    );
}

/// Unreachable defaults over a finite index carrier are decided from the
/// distinct keys of BOTH operands, not one side's.
///
/// When the defaults differ but every explicit read agrees, the arrays are
/// equal exactly when the stored keys cover the whole carrier and both defaults
/// are therefore unreachable. The two operands here store DISJOINT halves of a
/// `(_ BitVec 2)` index: each side's own table covers only half the carrier, so
/// a coverage count taken from one table alone would wrongly report the arrays
/// distinct.
#[test]
fn fast_lane_default_coverage_counts_both_operands() {
    let index = |value: u64| ModelValue::BitVec {
        width: 2,
        value: BigInt::from(value),
    };
    let array_sort = Sort::array(Sort::bitvec(2), Sort::Int);
    // `left` reads 1 at {0,1} and its default 0 at {2,3}; `right` reads its
    // default 1 at {0,1} and 0 at {2,3}. Every index agrees, and the union
    // {0,1,2,3} covers the carrier, so the two arrays ARE equal.
    let covering = |keys: [u64; 2], stored: i64, default: i64| {
        ModelValue::Array(Box::new(ArrayValue {
            default: ModelValue::Int(int(default)),
            store: keys
                .iter()
                .map(|&key| (index(key), ModelValue::Int(int(stored))))
                .collect(),
        }))
    };
    let equality_verdict = |left_value: ModelValue, right_value: ModelValue| {
        let mut terms = TermStore::new();
        let left = terms.mk_var("coverage_left", array_sort.clone());
        let right = terms.mk_var("coverage_right", array_sort.clone());
        let equality = app(&mut terms, "=", &[left, right], Sort::Bool);
        verdict(
            &terms,
            &StubModel::new()
                .with(left, left_value)
                .with(right, right_value),
            &[equality],
        )
    };

    assert_confirmed(&equality_verdict(
        covering([0, 1], 1, 0),
        covering([2, 3], 0, 1),
    ));

    // Drop one key: {0,1,2} leaves index 3 reading both differing defaults, so
    // the arrays are provably distinct and the coverage rule must say so.
    let partial_right = ModelValue::Array(Box::new(ArrayValue {
        default: ModelValue::Int(int(1)),
        store: vec![(index(2), ModelValue::Int(int(0)))],
    }));
    assert_violates(&equality_verdict(covering([0, 1], 1, 0), partial_right));
}

/// The fast lane must visit every key EITHER operand stores, not just the left
/// operand's.
///
/// A key that only one side overrides still separates the arrays: the other
/// side reads its default there. A visit order built from one operand alone
/// would compare nothing at such a key, find every visited key in agreement,
/// and — with equal defaults — wrongly answer `ConfirmedSat`. Both directions
/// are pinned, because the union loop is the only thing making the lane
/// symmetric.
#[test]
fn fast_lane_visits_keys_stored_by_only_one_operand() {
    let array_sort = Sort::array(Sort::Int, Sort::Int);
    let array = |store: Vec<(i64, i64)>| {
        ModelValue::Array(Box::new(ArrayValue {
            default: ModelValue::Int(int(0)),
            store: store
                .into_iter()
                .map(|(key, value)| (ModelValue::Int(int(key)), ModelValue::Int(int(value))))
                .collect(),
        }))
    };
    let equality_verdict = |left_value: ModelValue, right_value: ModelValue| {
        let mut terms = TermStore::new();
        let left = terms.mk_var("one_sided_left", array_sort.clone());
        let right = terms.mk_var("one_sided_right", array_sort.clone());
        let equality = app(&mut terms, "=", &[left, right], Sort::Bool);
        verdict(
            &terms,
            &StubModel::new()
                .with(left, left_value)
                .with(right, right_value),
            &[equality],
        )
    };

    // Only the RIGHT operand overrides index 4; the left reads 0 there.
    assert_violates(&equality_verdict(array(vec![]), array(vec![(4, 5)])));
    // ...and the mirror image.
    assert_violates(&equality_verdict(array(vec![(4, 5)]), array(vec![])));

    // Control: a one-sided override that restates the shared default leaves the
    // two arrays extensionally equal, so the same union walk must CONFIRM.
    assert_confirmed(&equality_verdict(array(vec![(4, 0)]), array(vec![])));
}

/// Canonical key encodings must be injective: two DIFFERENT nested sequence
/// keys may never encode alike.
///
/// `[[1],[2]]` and `[[1,2]]` hold the same integers in the same order and
/// differ only in their nesting, so an encoding that dropped the per-sequence
/// length and brackets would merge them into one table entry and report two
/// genuinely different arrays as equal.
#[test]
fn canonical_index_keys_separate_differently_nested_sequences() {
    let seq = |elements: &[i64]| {
        ModelValue::Seq(elements.iter().map(|&e| ModelValue::Int(int(e))).collect())
    };
    let array = |key: ModelValue| {
        ModelValue::Array(Box::new(ArrayValue {
            default: ModelValue::Int(int(0)),
            store: vec![(key, ModelValue::Int(int(10)))],
        }))
    };
    let distinct_keys_violate = |element_sort: Sort, left_key, right_key| {
        let array_sort = Sort::array(Sort::seq(element_sort), Sort::Int);
        let mut terms = TermStore::new();
        let left = terms.mk_var("nested_key_left", array_sort.clone());
        let right = terms.mk_var("nested_key_right", array_sort);
        let equality = app(&mut terms, "=", &[left, right], Sort::Bool);
        assert_violates(&verdict(
            &terms,
            &StubModel::new()
                .with(left, array(left_key))
                .with(right, array(right_key)),
            &[equality],
        ));
    };

    // Nesting alone distinguishes these two keys.
    distinct_keys_violate(
        Sort::seq(Sort::Int),
        ModelValue::Seq(vec![seq(&[1]), seq(&[2])]),
        ModelValue::Seq(vec![seq(&[1, 2])]),
    );

    // Adjacent numerals must stay separable: `[1, 23]` and `[12, 3]` share
    // every digit in order, so an encoding whose leaves are not terminated
    // would run them together into one key.
    distinct_keys_violate(Sort::Int, seq(&[1, 23]), seq(&[12, 3]));

    let bv = |value: u64| ModelValue::BitVec {
        width: 8,
        value: BigInt::from(value),
    };
    distinct_keys_violate(
        Sort::bitvec(8),
        ModelValue::Seq(vec![bv(1), bv(23)]),
        ModelValue::Seq(vec![bv(12), bv(3)]),
    );

    // The same requirement for the length-prefixed variants: `["a", "bc"]` and
    // `["ab", "c"]` concatenate to the same text.
    let text = |value: &str| ModelValue::Str(value.to_string());
    distinct_keys_violate(
        Sort::String,
        ModelValue::Seq(vec![text("a"), text("bc")]),
        ModelValue::Seq(vec![text("ab"), text("c")]),
    );

    let opaque = |value: &str| ModelValue::Uninterpreted(value.to_string());
    distinct_keys_violate(
        Sort::Uninterpreted("Opaque".to_string()),
        ModelValue::Seq(vec![opaque("a"), opaque("bc")]),
        ModelValue::Seq(vec![opaque("ab"), opaque("c")]),
    );
}

/// Two distinct index keys that collided in the encoding must never be able to
/// CONFIRM an array equality.
///
/// This probes the masking shape the single-key test above cannot reach: the
/// table keeps only the LAST store position per encoded key. Both operands here
/// hold the same two keys and differ ONLY at the first one; the second is
/// stored last and carries the SAME value in both. Under an injective encoding
/// that first disagreement is visible and the only sound answer is
/// `ModelViolates`. If the two keys encoded alike, the agreeing entry would
/// overwrite the disagreement in BOTH tables, every read would agree, and the
/// gate would wrongly answer `ConfirmedSat`.
///
/// The value layout is load-bearing. A swapped-value probe (`k1 -> 1, k2 -> 7`
/// against `k1 -> 7, k2 -> 1`) still reports `ModelViolates` under a colliding
/// encoding, because the two surviving last writes differ; only a probe whose
/// colliding partner agrees separates the two encodings.
#[test]
fn colliding_index_keys_can_never_confirm_an_array_equality() {
    let text = |value: &str| ModelValue::Str(value.to_string());
    let opaque = |value: &str| ModelValue::Uninterpreted(value.to_string());
    let bv = |value: i64| ModelValue::BitVec {
        width: 8,
        value: int(value),
    };

    // A pair that the byte-length prefix -- and only that prefix -- keeps
    // apart. The tag letter is a legal payload byte, so with the length gone
    // `"a" ++ "Tbb"` and `"aT" ++ "bb"` both render `TaTTbb`.
    let tag_aliasing = |tag: char| {
        [
            "a".to_string(),
            format!("{tag}bb"),
            format!("a{tag}"),
            "bb".to_string(),
        ]
    };
    // A pair that the `:` between the length and the payload -- and only that
    // `:` -- keeps apart. Without it the digits re-split: 1|"5" then
    // 20|"xxxxxxxxxxxxT6abcdef" reads equally well as 15|"T20xxxxxxxxxxxx"
    // then 6|"abcdef".
    let length_aliasing = |tag: char| {
        [
            "5".to_string(),
            format!("xxxxxxxxxxxx{tag}6abcdef"),
            format!("{tag}20xxxxxxxxxxxx"),
            "abcdef".to_string(),
        ]
    };
    let pair = |build: fn(&str) -> ModelValue, [a, b, c, d]: [String; 4]| {
        (
            ModelValue::Seq(vec![build(&a), build(&b)]),
            ModelValue::Seq(vec![build(&c), build(&d)]),
        )
    };
    let str_of = |value: &str| ModelValue::Str(value.to_string());
    let opaque_of = |value: &str| ModelValue::Uninterpreted(value.to_string());

    let (tag_str_left, tag_str_right) = pair(str_of, tag_aliasing('s'));
    let (tag_opq_left, tag_opq_right) = pair(opaque_of, tag_aliasing('u'));
    let (len_str_left, len_str_right) = pair(str_of, length_aliasing('s'));
    let (len_opq_left, len_opq_right) = pair(opaque_of, length_aliasing('u'));

    let opaque_sort = || Sort::Uninterpreted("Opaque".to_string());

    let cases: Vec<(&str, Sort, ModelValue, ModelValue)> = vec![
        (
            "seq string: [a,sbb] vs [as,bb] -- string length prefix",
            Sort::seq(Sort::String),
            tag_str_left,
            tag_str_right,
        ),
        (
            "seq uninterpreted: [a,ubb] vs [au,bb] -- token length prefix",
            Sort::seq(opaque_sort()),
            tag_opq_left,
            tag_opq_right,
        ),
        (
            "seq string: re-splittable lengths -- string length separator",
            Sort::seq(Sort::String),
            len_str_left,
            len_str_right,
        ),
        (
            "seq uninterpreted: re-splittable lengths -- token length separator",
            Sort::seq(opaque_sort()),
            len_opq_left,
            len_opq_right,
        ),
        (
            "string keys: a payload spelling another key's prefix",
            Sort::String,
            text("2:ab"),
            text("ab"),
        ),
        (
            "uninterpreted keys: a payload spelling another key's prefix",
            opaque_sort(),
            opaque("2:ab"),
            opaque("ab"),
        ),
        (
            "nested seq: [[1],[2]] vs [[1,2]]",
            Sort::seq(Sort::seq(Sort::Int)),
            ModelValue::Seq(vec![
                ModelValue::Seq(vec![ModelValue::Int(int(1))]),
                ModelValue::Seq(vec![ModelValue::Int(int(2))]),
            ]),
            ModelValue::Seq(vec![ModelValue::Seq(vec![
                ModelValue::Int(int(1)),
                ModelValue::Int(int(2)),
            ])]),
        ),
        (
            "nested seq: [[],[1]] vs [[1],[]]",
            Sort::seq(Sort::seq(Sort::Int)),
            ModelValue::Seq(vec![
                ModelValue::Seq(vec![]),
                ModelValue::Seq(vec![ModelValue::Int(int(1))]),
            ]),
            ModelValue::Seq(vec![
                ModelValue::Seq(vec![ModelValue::Int(int(1))]),
                ModelValue::Seq(vec![]),
            ]),
        ),
        (
            // The count prefix and the closing paren are each redundant given
            // the other, but TOGETHER they are what closes a sequence. Strip
            // both and `[[[1]],[]]` and `[[[1],[]]]` render alike, so this pair
            // is what makes the framing load-bearing rather than decorative.
            "twice-nested seq: [[[1]],[]] vs [[[1],[]]]",
            Sort::seq(Sort::seq(Sort::seq(Sort::Int))),
            ModelValue::Seq(vec![
                ModelValue::Seq(vec![ModelValue::Seq(vec![ModelValue::Int(int(1))])]),
                ModelValue::Seq(vec![]),
            ]),
            ModelValue::Seq(vec![ModelValue::Seq(vec![
                ModelValue::Seq(vec![ModelValue::Int(int(1))]),
                ModelValue::Seq(vec![]),
            ])]),
        ),
        (
            "seq int: [1,23] vs [12,3]",
            Sort::seq(Sort::Int),
            ModelValue::Seq(vec![ModelValue::Int(int(1)), ModelValue::Int(int(23))]),
            ModelValue::Seq(vec![ModelValue::Int(int(12)), ModelValue::Int(int(3))]),
        ),
        (
            "seq bitvec: [1,23] vs [12,3]",
            Sort::seq(Sort::bitvec(8)),
            ModelValue::Seq(vec![bv(1), bv(23)]),
            ModelValue::Seq(vec![bv(12), bv(3)]),
        ),
        (
            "seq bool: [T,F] vs [F,T]",
            Sort::seq(Sort::Bool),
            ModelValue::Seq(vec![ModelValue::Bool(true), ModelValue::Bool(false)]),
            ModelValue::Seq(vec![ModelValue::Bool(false), ModelValue::Bool(true)]),
        ),
    ];

    for (name, index_sort, first_key, second_key) in cases {
        let array_sort = Sort::array(index_sort, Sort::Int);
        let mut terms = TermStore::new();
        let left = terms.mk_var("collide_left", array_sort.clone());
        let right = terms.mk_var("collide_right", array_sort);
        let equality = app(&mut terms, "=", &[left, right], Sort::Bool);
        // Differ only at `first_key`; `second_key` is stored LAST and agrees.
        let array = |at_first_key: i64| {
            ModelValue::Array(Box::new(ArrayValue {
                default: ModelValue::Int(int(0)),
                store: vec![
                    (first_key.clone(), ModelValue::Int(int(at_first_key))),
                    (second_key.clone(), ModelValue::Int(int(7))),
                ],
            }))
        };
        let observed = verdict(
            &terms,
            &StubModel::new().with(left, array(1)).with(right, array(9)),
            &[equality],
        );
        assert!(
            matches!(observed, GateVerdict::ModelViolates { .. }),
            "KEY COLLISION on {name}: distinct keys were treated as one, got {observed:?}"
        );
    }
}

/// A datatype-sorted array index is outside the canonical encoding, so it keeps
/// the ordered-rescan comparison — and must still decide correctly.
#[test]
fn datatype_indexed_arrays_decide_through_the_rescan_lane() {
    let color = DatatypeSort::new(
        "Color",
        vec![
            DatatypeConstructor::new("red", Vec::new()),
            DatatypeConstructor::new("green", Vec::new()),
        ],
    );
    let key = |ctor: &str| ModelValue::Datatype {
        ctor: ctor.to_string(),
        args: Vec::new(),
    };
    let array = |green: i64| {
        ModelValue::Array(Box::new(ArrayValue {
            default: ModelValue::Int(int(0)),
            store: vec![
                (key("red"), ModelValue::Int(int(1))),
                (key("green"), ModelValue::Int(int(green))),
            ],
        }))
    };
    let array_sort = Sort::array(Sort::Uninterpreted("Color".to_string()), Sort::Int);
    let equality_verdict = |left_value: ModelValue, right_value: ModelValue| {
        let mut terms = TermStore::new();
        let left = terms.mk_var("dt_index_left", array_sort.clone());
        let right = terms.mk_var("dt_index_right", array_sort.clone());
        let equality = app(&mut terms, "=", &[left, right], Sort::Bool);
        verdict(
            &terms,
            &StubModel::new()
                .with_datatype(color.clone())
                .with(left, left_value)
                .with(right, right_value),
            &[equality],
        )
    };

    assert_confirmed(&equality_verdict(array(2), array(2)));
    assert_violates(&equality_verdict(array(2), array(3)));
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

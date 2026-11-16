// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::{confirm_model, GateVerdict};

struct Pinned {
    application: TermId,
    value: Option<ModelValue>,
}

#[test]
fn declared_array_operator_keeps_its_committed_array_on_a_lazy_read() {
    struct Arrays {
        base: TermId,
        application: TermId,
    }
    impl ModelView for Arrays {
        fn leaf_value(&self, term: TermId) -> Option<ModelValue> {
            (term == self.base).then(|| {
                ModelValue::Array(Box::new(ArrayValue {
                    default: ModelValue::Int(0.into()),
                    store: Vec::new(),
                }))
            })
        }
        fn uf_app_value(&self, term: TermId) -> Option<ModelValue> {
            (term == self.application).then(|| {
                ModelValue::Array(Box::new(ArrayValue {
                    default: ModelValue::Int(2.into()),
                    store: Vec::new(),
                }))
            })
        }
    }
    let mut terms = TermStore::new();
    let array_sort = Sort::array(Sort::Int, Sort::Int);
    let base = terms.mk_var("array_base", array_sort.clone());
    let zero = terms.mk_int(0.into());
    let one = terms.mk_int(1.into());
    let two = terms.mk_int(2.into());
    let application =
        terms.mk_app_structural(Symbol::named("store"), &[base, zero, one], array_sort);
    let read = terms.mk_app_structural(Symbol::named("select"), &[application, zero], Sort::Int);
    let bad = terms.mk_eq(read, one);
    let good = terms.mk_eq(read, two);
    let model = Arrays { base, application };
    assert!(matches!(
        confirm_model(&terms, &model, &[bad]),
        GateVerdict::ConfirmedSat
    ));
    terms.register_declared_function("store");
    assert!(!matches!(
        confirm_model(&terms, &model, &[bad]),
        GateVerdict::ConfirmedSat
    ));
    assert!(matches!(
        confirm_model(&terms, &model, &[good]),
        GateVerdict::ConfirmedSat
    ));
}

#[test]
fn declared_regex_operator_cannot_supply_an_uncommitted_language() {
    struct NoLanguage;
    impl ModelView for NoLanguage {
        fn leaf_value(&self, _: TermId) -> Option<ModelValue> {
            None
        }
    }
    let mut terms = TermStore::new();
    let text = terms.mk_string("a".into());
    let all = terms.mk_app_structural(Symbol::named("re.all"), &[], Sort::RegLan);
    let none = terms.mk_app_structural(Symbol::named("re.none"), &[], Sort::RegLan);
    let member = terms.mk_app_structural(Symbol::named("str.in_re"), &[text, all], Sort::Bool);
    let equality = terms.mk_app_structural(Symbol::named("="), &[all, none], Sort::Bool);
    let distinct = terms.mk_not_raw(equality);
    for root in [member, distinct] {
        assert!(matches!(
            confirm_model(&terms, &NoLanguage, &[root]),
            GateVerdict::ConfirmedSat
        ));
    }
    terms.register_declared_function("re.all");
    for root in [member, distinct] {
        assert!(!matches!(
            confirm_model(&terms, &NoLanguage, &[root]),
            GateVerdict::ConfirmedSat
        ));
    }
}

#[test]
fn declared_connective_cannot_supply_a_quantified_integer_range_theorem() {
    struct FalseFunction;
    impl ModelView for FalseFunction {
        fn leaf_value(&self, _: TermId) -> Option<ModelValue> {
            None
        }
        fn uf_app_value(&self, _: TermId) -> Option<ModelValue> {
            Some(ModelValue::Bool(false))
        }
    }
    let mut terms = TermStore::new();
    let x = terms.mk_var("range_bound", Sort::Int);
    let zero = terms.mk_int(0.into());
    let below = terms.mk_app_structural(Symbol::named("<"), &[x, zero], Sort::Bool);
    let above = terms.mk_app_structural(Symbol::named(">="), &[x, zero], Sort::Bool);
    let body = terms.mk_app_structural(Symbol::named("or"), &[below, above], Sort::Bool);
    let quantified = terms.mk_forall(vec![("range_bound".into(), Sort::Int)], body);
    terms.register_declared_function("or");
    assert!(!matches!(
        confirm_model(&terms, &FalseFunction, &[quantified]),
        GateVerdict::ConfirmedSat
    ));
}

#[test]
fn declared_equality_under_finite_quantification_keeps_its_function_interpretation() {
    struct FalseFunction;
    impl ModelView for FalseFunction {
        fn leaf_value(&self, _: TermId) -> Option<ModelValue> {
            None
        }
        fn uf_app_value(&self, _: TermId) -> Option<ModelValue> {
            Some(ModelValue::Bool(false))
        }
    }
    let mut terms = TermStore::new();
    let no = terms.mk_bool(false);
    let yes = terms.mk_bool(true);
    let variable = terms.mk_var("bound", Sort::Bool);
    let first = terms.mk_app_structural(Symbol::named("="), &[no, no], Sort::Bool);
    let second = terms.mk_app_structural(Symbol::named("="), &[yes, yes], Sort::Bool);
    let body = terms.mk_app_structural(Symbol::named("="), &[variable, variable], Sort::Bool);
    let quantified = terms.mk_forall(vec![("bound".into(), Sort::Bool)], body);
    let first = terms.mk_not_raw(first);
    let second = terms.mk_not_raw(second);
    terms.register_declared_function("=");
    assert!(
        matches!(confirm_model(&terms, &FalseFunction, &[first, second, quantified]),
        GateVerdict::ModelViolates { assertion } if assertion == quantified)
    );
}
impl ModelView for Pinned {
    fn leaf_value(&self, _: TermId) -> Option<ModelValue> {
        None
    }
    fn uf_app_value(&self, term: TermId) -> Option<ModelValue> {
        (term == self.application)
            .then(|| self.value.clone())
            .flatten()
    }
}

#[test]
fn declared_operator_names_use_committed_function_models_instead_of_builtin_arithmetic() {
    for name in ["and", "=", "bvadd", "ff.mul", "abs"] {
        let mut terms = TermStore::new();
        let (application, bad, good, value) = match name {
            "and" | "=" => {
                let yes = terms.mk_bool(true);
                let app = terms.mk_app_structural(Symbol::named(name), &[yes, yes], Sort::Bool);
                // Keep the authored UF negation structural; the ordinary
                // constructor may fold a still-builtin AND before registration.
                let good = terms.mk_not_raw(app);
                (app, app, good, ModelValue::Bool(false))
            }
            "bvadd" => {
                let zero = terms.mk_bitvec(0.into(), 8);
                let one = terms.mk_bitvec(1.into(), 8);
                let app =
                    terms.mk_app_structural(Symbol::named(name), &[zero, zero], Sort::bitvec(8));
                let bad = terms.mk_eq(app, zero);
                let good = terms.mk_eq(app, one);
                (
                    app,
                    bad,
                    good,
                    ModelValue::BitVec {
                        width: 8,
                        value: 1.into(),
                    },
                )
            }
            "ff.mul" => {
                let field = ay_core::FiniteFieldSort::new(7).unwrap();
                let zero = terms.mk_finite_field(0, field);
                let one = terms.mk_finite_field(1, field);
                let app = terms.mk_app_structural(
                    Symbol::named(name),
                    &[zero, zero],
                    Sort::FiniteField(field),
                );
                let bad = terms.mk_eq(app, zero);
                let good = terms.mk_eq(app, one);
                (app, bad, good, ModelValue::Int(1.into()))
            }
            _ => {
                let negative = terms.mk_int((-1).into());
                let zero = terms.mk_int(0.into());
                let one = terms.mk_int(1.into());
                let app = terms.mk_app_structural(Symbol::named(name), &[negative], Sort::Int);
                let bad = terms.mk_eq(app, one);
                let good = terms.mk_eq(app, zero);
                (app, bad, good, ModelValue::Int(0.into()))
            }
        };
        let model = Pinned {
            application,
            value: Some(value),
        };
        assert!(
            matches!(
                confirm_model(&terms, &model, &[bad]),
                GateVerdict::ConfirmedSat
            ),
            "genuine builtin {name}"
        );
        terms.register_declared_function(name);
        for store in [&terms, &terms.clone()] {
            assert!(
                matches!(
                    confirm_model(store, &model, &[bad]),
                    GateVerdict::ModelViolates { .. }
                ),
                "registered {name} must use its committed function interpretation"
            );
            assert!(
                matches!(
                    confirm_model(store, &model, &[good]),
                    GateVerdict::ConfirmedSat
                ),
                "registered {name} has a genuine consistent model"
            );
            let missing = Pinned {
                application,
                value: None,
            };
            assert!(
                matches!(
                    confirm_model(store, &missing, &[bad]),
                    GateVerdict::CannotConfirm { .. }
                ),
                "missing {name} interpretation cannot inherit builtin behavior"
            );
        }
    }
}

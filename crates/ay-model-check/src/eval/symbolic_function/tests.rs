// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::SymbolicFunctionView;

struct Function {
    symbol: Symbol,
    parameters: Vec<TermId>,
    body: TermId,
}
struct View<'a> {
    terms: &'a TermStore,
    functions: Vec<Function>,
}
impl ModelView for View<'_> {
    fn leaf_value(&self, _: TermId) -> Option<ModelValue> {
        None
    }
    fn uf_app_value(&self, _: TermId) -> Option<ModelValue> {
        Some(ModelValue::Bool(true))
    }
    fn symbolic_function(&self, term: TermId) -> Result<Option<SymbolicFunctionView<'_>>, String> {
        let TermData::App(symbol, _) = self.terms.get(term) else {
            return Ok(None);
        };
        Ok(self
            .functions
            .iter()
            .find(|function| &function.symbol == symbol)
            .map(|function| SymbolicFunctionView {
                symbol: &function.symbol,
                parameters: &function.parameters,
                body: function.body,
            }))
    }
}

fn app(t: &mut TermStore, name: &str, args: &[TermId], sort: Sort) -> TermId {
    t.mk_app_structural(Symbol::named(name), args, sort)
}
fn boolean(e: &Evaluator<'_>, term: TermId, expected: bool) {
    assert!(
        matches!(e.evaluate(term),EvalOutcome::Value(ModelValue::Bool(value)) if value==expected)
    );
}

#[test]
fn symbolic_function_same_body_at_seven_and_negative_one_never_reuses_parameter_memo() {
    let mut t = TermStore::new();
    let parameter = t.mk_var("parameter", Sort::Int);
    let zero = t.mk_int(0.into());
    let body = app(&mut t, "<=", &[zero, parameter], Sort::Bool);
    let seven = t.mk_int(7.into());
    let negative = t.mk_int((-1).into());
    let a = app(&mut t, "range", &[seven], Sort::Bool);
    let b = app(&mut t, "range", &[negative], Sort::Bool);
    let view = View {
        terms: &t,
        functions: vec![Function {
            symbol: Symbol::named("range"),
            parameters: vec![parameter],
            body,
        }],
    };
    let evaluator = Evaluator::new(&t, &view);
    boolean(&evaluator, a, true);
    boolean(&evaluator, b, false);
    boolean(&evaluator, a, true);
    assert!(evaluator.local_bindings.borrow().is_empty());
}

#[test]
fn symbolic_function_exact_formal_ids_preserve_same_spelling_and_argument_permutation() {
    let mut t = TermStore::new();
    let left = t.mk_var("same", Sort::Int);
    let right = t.mk_fresh_named_var("same", Sort::Int);
    let body = app(&mut t, "-", &[left, right], Sort::Int);
    let seven = t.mk_int(7.into());
    let two = t.mk_int(2.into());
    let a = app(&mut t, "difference", &[seven, two], Sort::Int);
    let b = app(&mut t, "difference", &[two, seven], Sort::Int);
    let view = View {
        terms: &t,
        functions: vec![Function {
            symbol: Symbol::named("difference"),
            parameters: vec![left, right],
            body,
        }],
    };
    let evaluator = Evaluator::new(&t, &view);
    assert!(
        matches!(evaluator.evaluate(a),EvalOutcome::Value(ModelValue::Int(value)) if value==5.into())
    );
    assert!(
        matches!(evaluator.evaluate(b),EvalOutcome::Value(ModelValue::Int(value)) if value==(-5).into())
    );
}

#[test]
fn symbolic_function_arrays_are_read_and_compared_extensionally_in_the_binding_frame() {
    let mut t = TermStore::new();
    let array_sort = Sort::array(Sort::Int, Sort::Bool);
    let array = t.mk_var("array", array_sort.clone());
    let index = t.mk_var("index", Sort::Int);
    let peer = t.mk_var("peer", array_sort.clone());
    let read = app(&mut t, "select", &[array, index], Sort::Bool);
    let equal = app(&mut t, "=", &[array, peer], Sort::Bool);
    let no = t.mk_bool(false);
    let yes = t.mk_bool(true);
    let seven = t.mk_int(7.into());
    let eight = t.mk_int(8.into());
    let empty = app(&mut t, "const-array", &[no], array_sort.clone());
    let changed = app(&mut t, "store", &[empty, seven, yes], array_sort.clone());
    let redundant = app(&mut t, "store", &[empty, seven, no], array_sort.clone());
    let a = app(&mut t, "read", &[changed, seven], Sort::Bool);
    let b = app(&mut t, "read", &[changed, eight], Sort::Bool);
    let same = app(&mut t, "same_array", &[empty, redundant], Sort::Bool);
    let different = app(&mut t, "same_array", &[empty, changed], Sort::Bool);
    let view = View {
        terms: &t,
        functions: vec![
            Function {
                symbol: Symbol::named("read"),
                parameters: vec![array, index],
                body: read,
            },
            Function {
                symbol: Symbol::named("same_array"),
                parameters: vec![array, peer],
                body: equal,
            },
        ],
    };
    let evaluator = Evaluator::new(&t, &view);
    boolean(&evaluator, a, true);
    boolean(&evaluator, b, false);
    boolean(&evaluator, same, true);
    boolean(&evaluator, different, false);
}

#[test]
fn symbolic_function_foreign_same_name_and_wrong_argument_sort_refuse_without_leaking_bindings() {
    let mut t = TermStore::new();
    let parameter = t.mk_var("same", Sort::Int);
    let foreign = t.mk_fresh_named_var("same", Sort::Int);
    let seven = t.mk_int(7.into());
    let leaked = app(&mut t, "bad_capture", &[seven], Sort::Int);
    let boolean = t.mk_var("boolean", Sort::Bool);
    let wrong = app(&mut t, "wrong_sort", &[seven], Sort::Bool);
    let view = View {
        terms: &t,
        functions: vec![
            Function {
                symbol: Symbol::named("bad_capture"),
                parameters: vec![parameter],
                body: foreign,
            },
            Function {
                symbol: Symbol::named("wrong_sort"),
                parameters: vec![boolean],
                body: boolean,
            },
        ],
    };
    let evaluator = Evaluator::new(&t, &view);
    assert!(matches!(
        evaluator.evaluate(leaked),
        EvalOutcome::Unevaluable(_)
    ));
    assert!(matches!(
        evaluator.evaluate(wrong),
        EvalOutcome::Unevaluable(_)
    ));
    assert!(evaluator.local_bindings.borrow().is_empty());
    assert!(evaluator.symbolic_active.borrow().is_empty());
}

#[test]
fn symbolic_function_finite_nested_applications_are_not_recursive_definitions() {
    let mut t = TermStore::new();
    let parameter = t.mk_var("x", Sort::Int);
    let one = t.mk_int(1.into());
    let body = app(&mut t, "+", &[parameter, one], Sort::Int);
    let seven = t.mk_int(7.into());
    let inner = app(&mut t, "successor", &[seven], Sort::Int);
    let outer = app(&mut t, "successor", &[inner], Sort::Int);
    let view = View {
        terms: &t,
        functions: vec![Function {
            symbol: Symbol::named("successor"),
            parameters: vec![parameter],
            body,
        }],
    };
    assert!(
        matches!(Evaluator::new(&t,&view).evaluate(outer),EvalOutcome::Value(ModelValue::Int(value)) if value==9.into())
    );
}

#[test]
fn symbolic_function_mutual_cycles_are_refused_before_native_stack_exhaustion() {
    let mut t = TermStore::new();
    let parameter = t.mk_var("x", Sort::Int);
    let f = app(&mut t, "f", &[parameter], Sort::Int);
    let g = app(&mut t, "g", &[parameter], Sort::Int);
    let seven = t.mk_int(7.into());
    let query = app(&mut t, "f", &[seven], Sort::Int);
    let view = View {
        terms: &t,
        functions: vec![
            Function {
                symbol: Symbol::named("f"),
                parameters: vec![parameter],
                body: g,
            },
            Function {
                symbol: Symbol::named("g"),
                parameters: vec![parameter],
                body: f,
            },
        ],
    };
    let evaluator = Evaluator::new(&t, &view);
    assert!(matches!(
        evaluator.evaluate(query),
        EvalOutcome::Unevaluable(_)
    ));
    assert!(evaluator.local_bindings.borrow().is_empty());
    assert!(evaluator.symbolic_active.borrow().is_empty());
}

#[test]
fn symbolic_function_malformed_unused_ite_branch_does_not_create_a_typed_body() {
    let mut t = TermStore::new();
    let parameter = t.mk_var("x", Sort::Int);
    let truth = t.mk_bool(true);
    let one = t.mk_int(1.into());
    // An actual Ite node also has its raw branch metadata checked. Build it in
    // a checker-only snapshot so an ordinary typed builder cannot repair it.
    let (true_id, false_id) = t.boolean_constant_ids();
    let mut entries = t.entries_snapshot();
    let id = TermId(u32::try_from(entries.len()).unwrap());
    entries.push((TermData::Ite(truth, one, truth), Sort::Int));
    let query = TermId(u32::try_from(entries.len()).unwrap());
    entries.push((
        TermData::App(Symbol::named("malformed"), vec![one]),
        Sort::Int,
    ));
    let t = TermStore::from_entries(entries, true_id, false_id, 0);
    let view = View {
        terms: &t,
        functions: vec![Function {
            symbol: Symbol::named("malformed"),
            parameters: vec![parameter],
            body: id,
        }],
    };
    assert!(matches!(
        Evaluator::new(&t, &view).evaluate(query),
        EvalOutcome::Unevaluable(_)
    ));
}

#[test]
fn symbolic_function_cannot_appear_or_disappear_between_applications() {
    use std::cell::Cell;
    struct Switching<'a> {
        view: View<'a>,
        first: Cell<bool>,
        first_some: bool,
    }
    impl ModelView for Switching<'_> {
        fn leaf_value(&self, _: TermId) -> Option<ModelValue> {
            None
        }
        fn uf_app_value(&self, _: TermId) -> Option<ModelValue> {
            Some(ModelValue::Bool(true))
        }
        fn symbolic_function(
            &self,
            term: TermId,
        ) -> Result<Option<SymbolicFunctionView<'_>>, String> {
            if self.first.replace(false) == self.first_some {
                self.view.symbolic_function(term)
            } else {
                Ok(None)
            }
        }
    }
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Int);
    let zero = t.mk_int(0.into());
    let body = app(&mut t, "<=", &[zero, x], Sort::Bool);
    let seven = t.mk_int(7.into());
    let negative = t.mk_int((-1).into());
    let first = app(&mut t, "changing", &[seven], Sort::Bool);
    let second = app(&mut t, "changing", &[negative], Sort::Bool);
    for first_some in [false, true] {
        let view = Switching {
            view: View {
                terms: &t,
                functions: vec![Function {
                    symbol: Symbol::named("changing"),
                    parameters: vec![x],
                    body,
                }],
            },
            first: Cell::new(true),
            first_some,
        };
        let evaluator = Evaluator::new(&t, &view);
        boolean(&evaluator, first, true);
        assert!(matches!(
            evaluator.evaluate(second),
            EvalOutcome::Unevaluable(_)
        ));
        assert!(evaluator.local_bindings.borrow().is_empty());
    }
}

#[test]
fn symbolic_function_expanded_dag_and_raw_constant_typing_refuse_before_body_evaluation() {
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Bool);
    let yes = t.mk_bool(true);
    let mut body = x;
    for _ in 0..13 {
        body = app(&mut t, "and", &[body, body], Sort::Bool);
    }
    let query = app(&mut t, "large", &[yes], Sort::Bool);
    let view = View {
        terms: &t,
        functions: vec![Function {
            symbol: Symbol::named("large"),
            parameters: vec![x],
            body,
        }],
    };
    assert!(matches!(
        Evaluator::new(&t, &view).evaluate(query),
        EvalOutcome::Unevaluable(_)
    ));

    let parameter = t.mk_var("int_parameter", Sort::Int);
    let int = t.mk_int(7.into());
    let (true_id, false_id) = t.boolean_constant_ids();
    let mut entries = t.entries_snapshot();
    let malformed = TermId(u32::try_from(entries.len()).unwrap());
    entries.push((
        TermData::Const(ay_core::term::Constant::Bool(true)),
        Sort::Int,
    ));
    let call = TermId(u32::try_from(entries.len()).unwrap());
    entries.push((
        TermData::App(Symbol::named("bad_constant"), vec![int]),
        Sort::Int,
    ));
    let t = TermStore::from_entries(entries, true_id, false_id, 0);
    let view = View {
        terms: &t,
        functions: vec![Function {
            symbol: Symbol::named("bad_constant"),
            parameters: vec![parameter],
            body: malformed,
        }],
    };
    assert!(matches!(
        Evaluator::new(&t, &view).evaluate(call),
        EvalOutcome::Unevaluable(_)
    ));
}

#[test]
fn symbolic_function_identical_application_and_cached_parent_recheck_currency() {
    use std::cell::Cell;
    struct MutableView<'a> {
        terms: &'a TermStore,
        mode: Cell<u8>,
        symbol: Symbol,
        parameters: Vec<TermId>,
        body: TermId,
        replacement: TermId,
    }
    impl ModelView for MutableView<'_> {
        fn leaf_value(&self, _: TermId) -> Option<ModelValue> {
            None
        }
        fn symbolic_function(
            &self,
            term: TermId,
        ) -> Result<Option<SymbolicFunctionView<'_>>, String> {
            let TermData::App(head, _) = self.terms.get(term) else {
                return Ok(None);
            };
            if head != &self.symbol || self.mode.get() == 1 {
                return Ok(None);
            }
            Ok(Some(SymbolicFunctionView {
                symbol: &self.symbol,
                parameters: &self.parameters,
                body: if self.mode.get() == 2 {
                    self.replacement
                } else {
                    self.body
                },
            }))
        }
    }
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Int);
    let zero = t.mk_int(0.into());
    let body = app(&mut t, "<=", &[zero, x], Sort::Bool);
    let replacement = t.mk_not(body);
    let seven = t.mk_int(7.into());
    let application = app(&mut t, "current", &[seven], Sort::Bool);
    let parent = t.mk_not(application);
    for mode in [1, 2] {
        let view = MutableView {
            terms: &t,
            mode: Cell::new(0),
            symbol: Symbol::named("current"),
            parameters: vec![x],
            body,
            replacement,
        };
        let evaluator = Evaluator::new(&t, &view);
        boolean(&evaluator, application, true);
        boolean(&evaluator, parent, false);
        view.mode.set(mode);
        assert!(matches!(
            evaluator.evaluate(application),
            EvalOutcome::Unevaluable(_)
        ));
        assert!(matches!(
            evaluator.evaluate(parent),
            EvalOutcome::Unevaluable(_)
        ));
        assert!(evaluator.local_bindings.borrow().is_empty());
    }
}

#[test]
fn symbolic_function_malformed_unary_builtins_refuse_even_in_an_unused_branch() {
    let mut t = TermStore::new();
    let condition = t.mk_var("condition", Sort::Bool);
    let one = t.mk_int(1.into());
    let yes = t.mk_bool(true);
    for name in ["abs", "to_int"] {
        let malformed = app(&mut t, name, &[], Sort::Int);
        for unused in [false, true] {
            let body = if unused {
                t.mk_ite(condition, one, malformed)
            } else {
                malformed
            };
            let query = app(&mut t, "bad_unary", &[yes], Sort::Int);
            let view = View {
                terms: &t,
                functions: vec![Function {
                    symbol: Symbol::named("bad_unary"),
                    parameters: vec![condition],
                    body,
                }],
            };
            assert!(matches!(
                Evaluator::new(&t, &view).evaluate(query),
                EvalOutcome::Unevaluable(_)
            ));
        }
    }
}

#[test]
fn symbolic_function_well_typed_abs_and_to_int_keep_native_arithmetic() {
    let mut t = TermStore::new();
    let integer = t.mk_var("integer", Sort::Int);
    let real = t.mk_var("real", Sort::Real);
    let abs = app(&mut t, "abs", &[integer], Sort::Int);
    let floor = app(&mut t, "to_int", &[real], Sort::Int);
    let negative = t.mk_int((-7).into());
    let fraction = t.mk_rational(num_rational::BigRational::new((-3).into(), 2.into()));
    let a = app(&mut t, "absolute", &[negative], Sort::Int);
    let b = app(&mut t, "floor_value", &[fraction], Sort::Int);
    let view = View {
        terms: &t,
        functions: vec![
            Function {
                symbol: Symbol::named("absolute"),
                parameters: vec![integer],
                body: abs,
            },
            Function {
                symbol: Symbol::named("floor_value"),
                parameters: vec![real],
                body: floor,
            },
        ],
    };
    let evaluator = Evaluator::new(&t, &view);
    assert!(
        matches!(evaluator.evaluate(a),EvalOutcome::Value(ModelValue::Int(value)) if value==7.into())
    );
    assert!(
        matches!(evaluator.evaluate(b),EvalOutcome::Value(ModelValue::Int(value)) if value==(-2).into())
    );
}

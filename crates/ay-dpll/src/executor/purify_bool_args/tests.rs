// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::term::TermStore;
use ay_core::Sort;

/// A compound Boolean argument to an uninterpreted function is replaced by a
/// fresh proxy variable, and a defining equality is appended.
#[test]
fn purifies_compound_bool_arg_of_uf() {
    let mut terms = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let conj = terms.mk_and(vec![a, b]);
    let fapp = terms.mk_app(Symbol::named("f"), [conj], u.clone());
    let t = terms.mk_var("t", u);
    let assertion = terms.mk_eq(fapp, t);

    let mut assertions = vec![assertion];
    let orphan_index = purify_bool_args(&mut terms, &mut assertions);

    assert!(
        !orphan_index.is_empty(),
        "pass should fire on a compound Bool UF argument"
    );
    // The rewritten `f(<compound>)` is indexed to `f(proxy)` — the ONLY term a
    // model will pin, since the original appears in no assertion the solver sees.
    assert_eq!(
        orphan_index.get(&fapp).copied(),
        Some(match terms.get(assertions[0]) {
            TermData::App(_, args) => args[0],
            _ => panic!("assertion should still be the equality"),
        }),
        "the rewritten UF application must be indexed to its solver-visible twin"
    );
    assert_eq!(assertions.len(), 2, "a proxy definition should be appended");
}

/// Plain Boolean-variable arguments are left untouched (no spurious proxies).
#[test]
fn leaves_plain_bool_var_arg_untouched() {
    let mut terms = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());
    let p = terms.mk_var("p", Sort::Bool);
    let fapp = terms.mk_app(Symbol::named("f"), [p], u.clone());
    let t = terms.mk_var("t", u);
    let assertion = terms.mk_eq(fapp, t);

    let mut assertions = vec![assertion];
    let orphan_index = purify_bool_args(&mut terms, &mut assertions);

    assert!(
        orphan_index.is_empty(),
        "plain Bool-var arguments need no purification"
    );
    assert_eq!(assertions.len(), 1);
}

/// `purify_new_bool_args` rewrites only the assertions outside `settled`: a
/// settled assertion that still holds the same compound argument (here, as
/// an operand of a proxy definition) is left exactly as it was.
#[test]
fn purify_new_bool_args_leaves_settled_assertions_untouched() {
    let mut terms = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let conj = terms.mk_and(vec![a, b]);
    let p = terms.mk_var("p", Sort::Bool);
    let settled_def = terms.mk_eq(p, conj);
    let fapp = terms.mk_app(Symbol::named("f"), [conj], u.clone());
    let t = terms.mk_var("t", u);
    let instance = terms.mk_eq(fapp, t);

    let settled: DetHashSet<TermId> = [settled_def].into_iter().collect();
    let mut assertions = vec![settled_def, instance];
    let orphan_index = purify_new_bool_args(&mut terms, &mut assertions, &settled);

    assert_eq!(
        assertions[0], settled_def,
        "a settled assertion is not rewritten"
    );
    assert_ne!(assertions[1], instance, "the new assertion is purified");
    assert!(orphan_index.contains_key(&fapp), "its rewrite is indexed");
    assert_eq!(assertions.len(), 3, "one proxy definition is appended");
}

/// Nothing new, nothing done.
#[test]
fn purify_new_bool_args_without_new_assertions_is_a_no_op() {
    let mut terms = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let conj = terms.mk_or(vec![a, b]);
    let fapp = terms.mk_app(Symbol::named("f"), [conj], u.clone());
    let t = terms.mk_var("t", u);
    let assertion = terms.mk_eq(fapp, t);

    let settled: DetHashSet<TermId> = [assertion].into_iter().collect();
    let mut assertions = vec![assertion];
    let orphan_index = purify_new_bool_args(&mut terms, &mut assertions, &settled);

    assert!(orphan_index.is_empty());
    assert_eq!(assertions, vec![assertion]);
}

/// These controls compare the source formula's meaning with the rewritten
/// formula under every tiny Boolean model. They do not ask the solver to
/// accept raw Let terms, whose native solver support is a separate boundary.
mod let_closure_semantics {
    use super::*;
    use ay_core::term::Constant;

    fn eval(
        terms: &TermStore,
        term: TermId,
        values: &[(TermId, bool)],
        scope: &[(String, bool)],
        f: [bool; 2],
    ) -> bool {
        assert_eq!(
            terms.sort(term),
            &Sort::Bool,
            "the semantic control is Boolean"
        );
        match terms.get(term) {
            TermData::Const(Constant::Bool(value)) => *value,
            TermData::Var(name, _) => scope
                .iter()
                .rev()
                .find_map(|(bound, value)| (bound == name).then_some(*value))
                .or_else(|| {
                    values
                        .iter()
                        .find_map(|(variable, value)| (*variable == term).then_some(*value))
                })
                .expect("every free Boolean variable has a model value"),
            TermData::Not(inner) => !eval(terms, *inner, values, scope, f),
            TermData::Ite(condition, then_term, else_term) => {
                let selected = if eval(terms, *condition, values, scope, f) {
                    *then_term
                } else {
                    *else_term
                };
                eval(terms, selected, values, scope, f)
            }
            TermData::App(Symbol::Named(name), args) => match name.as_str() {
                "f" => match args.as_slice() {
                    [argument] => f[usize::from(eval(terms, *argument, values, scope, f))],
                    _ => panic!("the control's f has type Bool -> Bool"),
                },
                "and" => args.iter().all(|&arg| eval(terms, arg, values, scope, f)),
                "or" => args.iter().any(|&arg| eval(terms, arg, values, scope, f)),
                "=" => match args.as_slice() {
                    [left, right] => {
                        eval(terms, *left, values, scope, f)
                            == eval(terms, *right, values, scope, f)
                    }
                    _ => panic!("the control's equality has two Boolean operands"),
                },
                other => panic!("unexpected operator in finite Boolean control: {other}"),
            },
            TermData::Let(bindings, body) => {
                // SMT-LIB bindings are simultaneous: every RHS sees precisely
                // the outer environment, including the old value of a shadowed
                // name. Only the body sees this level's new bindings.
                let values_here: Vec<_> = bindings
                    .iter()
                    .map(|(name, value)| (name.clone(), eval(terms, *value, values, scope, f)))
                    .collect();
                let mut inner = scope.to_vec();
                inner.extend(values_here);
                eval(terms, *body, values, &inner, f)
            }
            TermData::Forall(bindings, body, _) | TermData::Exists(bindings, body, _) => {
                assert!(bindings.len() <= 4);
                assert!(bindings.iter().all(|(_, sort)| sort == &Sort::Bool));
                let evaluate_assignment =
                    |bits: usize| {
                        let mut inner = scope.to_vec();
                        inner.extend(bindings.iter().enumerate().map(|(index, (name, _))| {
                            (name.clone(), bits & (1usize << index) != 0)
                        }));
                        eval(terms, *body, values, &inner, f)
                    };
                if matches!(terms.get(term), TermData::Exists(..)) {
                    (0..(1usize << bindings.len())).any(evaluate_assignment)
                } else {
                    (0..(1usize << bindings.len())).all(evaluate_assignment)
                }
            }
            other => panic!("unexpected term in finite Boolean control: {other:?}"),
        }
    }

    fn variables(terms: &TermStore, begin: usize, end: usize) -> Vec<TermId> {
        (begin..end)
            .filter_map(|index| {
                let term = TermId(u32::try_from(index).expect("tiny control arena"));
                if matches!(terms.get(term), TermData::Var(..)) {
                    assert_eq!(terms.sort(term), &Sort::Bool);
                    Some(term)
                } else {
                    None
                }
            })
            .collect()
    }

    fn valuation(variables: &[TermId], bits: usize) -> Vec<(TermId, bool)> {
        variables
            .iter()
            .enumerate()
            .map(|(index, &term)| (term, bits & (1usize << index) != 0))
            .collect()
    }

    fn conservative_extension(
        mut terms: TermStore,
        roots: Vec<TermId>,
        require_purification: bool,
    ) {
        let old_len = terms.len();
        let old_variables = variables(&terms, 0, old_len);
        let mut rewritten = roots.clone();
        let orphans = purify_bool_args(&mut terms, &mut rewritten);
        if require_purification {
            assert!(
                !orphans.is_empty(),
                "this safe occurrence must still be purified"
            );
        }
        let proxies = variables(&terms, old_len, terms.len());
        assert!(old_variables.len() <= 6 && proxies.len() <= 6);
        let mut observed_true = false;
        let mut observed_false = false;
        for old_bits in 0..(1usize << old_variables.len()) {
            let old_values = valuation(&old_variables, old_bits);
            for function_bits in 0..4 {
                // Enumerate every total Bool -> Bool interpretation, including
                // both constants, identity and negation.
                let f = [function_bits & 1 != 0, function_bits & 2 != 0];
                let original = roots
                    .iter()
                    .all(|&root| eval(&terms, root, &old_values, &[], f));
                observed_true |= original;
                observed_false |= !original;
                let extension = (0..(1usize << proxies.len())).any(|proxy_bits| {
                    let mut values = old_values.clone();
                    values.extend(valuation(&proxies, proxy_bits));
                    rewritten
                        .iter()
                        .all(|&root| eval(&terms, root, &values, &[], f))
                });
                assert_eq!(
                    extension, original,
                    "changed source meaning: old_bits={old_bits}, f={f:?}, roots={roots:?}, rewritten={rewritten:?}"
                );
            }
        }
        assert!(
            observed_true && observed_false,
            "the control distinguishes models"
        );
    }

    fn apply_f(terms: &mut TermStore, argument: TermId) -> TermId {
        terms.mk_app(Symbol::named("f"), [argument], Sort::Bool)
    }

    #[test]
    fn closed_let_does_not_hoist_a_binding_dependent_boolean_argument() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Bool);
        let not_x = terms.mk_not(x);
        let application = apply_f(&mut terms, not_x);
        let value = terms.mk_bool(false);
        let root = terms.mk_let(vec![("x".to_string(), value)], application);
        conservative_extension(terms, vec![root], false);
    }

    #[test]
    fn one_term_id_used_free_and_captured_keeps_both_source_meanings() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Bool);
        let not_x = terms.mk_not(x);
        let application = apply_f(&mut terms, not_x);
        let negated = terms.mk_not(application);
        let value = terms.mk_bool(true);
        let captured = terms.mk_let(vec![("x".to_string(), value)], negated);
        // The same DAG node occurs inside and outside Let. Both root orders
        // force correctness before AND after a later lexical-context union.
        conservative_extension(terms.clone(), vec![captured, application], false);
        conservative_extension(terms, vec![application, captured], false);
    }

    #[test]
    fn a_safe_compound_argument_inside_let_still_gets_a_proxy() {
        let mut terms = TermStore::new();
        let y = terms.mk_var("y", Sort::Bool);
        let not_y = terms.mk_not(y);
        let application = apply_f(&mut terms, not_y);
        let value = terms.mk_bool(false);
        let root = terms.mk_let(vec![("x".to_string(), value)], application);
        conservative_extension(terms, vec![root], true);
    }

    #[test]
    fn simultaneous_let_rhs_keeps_its_outer_free_variable_and_is_purified() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Bool);
        let y = terms.mk_var("y", Sort::Bool);
        let not_x = terms.mk_not(x);
        let application = apply_f(&mut terms, not_x);
        let value = terms.mk_bool(false);
        let root = terms.mk_let(
            vec![("x".to_string(), value), ("y".to_string(), application)],
            y,
        );
        conservative_extension(terms, vec![root], true);
    }

    #[test]
    fn a_nested_let_can_close_the_argument_without_capturing_the_proxy() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Bool);
        let not_x = terms.mk_not(x);
        let inner_value = terms.mk_bool(true);
        let inner = terms.mk_let(vec![("x".to_string(), inner_value)], not_x);
        let application = apply_f(&mut terms, inner);
        let outer_value = terms.mk_bool(false);
        let root = terms.mk_let(vec![("x".to_string(), outer_value)], application);
        conservative_extension(terms, vec![root], true);
    }

    #[test]
    fn nested_shadowing_does_not_close_a_rhs_that_uses_the_outer_binding() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Bool);
        let not_x = terms.mk_not(x);
        let application = apply_f(&mut terms, not_x);
        let inner = terms.mk_let(vec![("x".to_string(), application)], not_x);
        let value = terms.mk_bool(false);
        let root = terms.mk_let(vec![("x".to_string(), value)], inner);
        conservative_extension(terms, vec![root], false);
    }

    #[test]
    fn a_let_binds_by_name_even_when_the_body_has_a_distinct_var_id() {
        let mut terms = TermStore::new();
        let declaration = terms.mk_var("x", Sort::Bool);
        let body_variable = terms.mk_fresh_named_var("x", Sort::Bool);
        assert_ne!(declaration, body_variable);
        let not_x = terms.mk_not(body_variable);
        let application = apply_f(&mut terms, not_x);
        let value = terms.mk_bool(false);
        let root = terms.mk_let(vec![("x".to_string(), value)], application);
        conservative_extension(terms, vec![root], false);
    }

    #[test]
    fn a_generated_proxy_spelling_cannot_be_captured_by_an_existing_let() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Bool);
        let not_x = terms.mk_not(x);
        let application = apply_f(&mut terms, not_x);
        // Obtain the exact would-be fresh spelling through the actual fresh
        // variable API on an otherwise identical arena, rather than guessing
        // a counter value. Adding the binder below does not mint a variable.
        let mut probe = terms.clone();
        let would_be_proxy = probe.mk_fresh_var("boolarg", Sort::Bool);
        let TermData::Var(collision, _) = probe.get(would_be_proxy) else {
            panic!("fresh variable API returned a non-variable");
        };
        let value = terms.mk_bool(false);
        let root = terms.mk_let(vec![(collision.clone(), value)], application);
        conservative_extension(terms, vec![root], true);
    }

    #[test]
    fn a_sibling_binder_does_not_close_a_simultaneous_rhs_free_name() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Bool);
        let y = terms.mk_var("y", Sort::Bool);
        let not_x = terms.mk_not(x);
        let value = terms.mk_bool(false);
        // y in x's RHS is OUTER y, despite the sibling binding named y.
        let argument = terms.mk_let(vec![("x".to_string(), y), ("y".to_string(), value)], not_x);
        let application = apply_f(&mut terms, argument);
        let negated = terms.mk_not(application);
        let inner_value = terms.mk_bool(true);
        let captured = terms.mk_let(vec![("y".to_string(), inner_value)], negated);
        conservative_extension(terms.clone(), vec![captured, application], false);
        conservative_extension(terms, vec![application, captured], false);
    }

    #[test]
    fn a_shared_target_in_a_quantifier_body_is_vetoed_without_collecting_it() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Bool);
        let not_x = terms.mk_not(x);
        let application = apply_f(&mut terms, not_x);
        let negated = terms.mk_not(application);
        let quantified = terms.mk_exists(vec![("x".to_string(), Sort::Bool)], negated);
        // Candidate discovery skips this body, but the existing GLOBAL
        // substitute recorder still descends into it. Finite Bool semantics
        // distinguishes the source's two lexical meanings without a solver.
        conservative_extension(terms.clone(), vec![quantified, application], false);
        conservative_extension(terms, vec![application, quantified], false);
    }
}

// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn distinct_same_name(terms: &mut TermStore) -> (TermId, TermId) {
    let first = terms.intern(TermData::Var("same_name".to_owned(), 100_000), Sort::Int);
    let second = terms.intern(TermData::Var("same_name".to_owned(), 100_001), Sort::Int);
    assert_ne!(first, second);
    (first, second)
}

#[test]
fn lambda_substitution_nested_same_identity_keeps_inner_binding() {
    let mut terms = TermStore::new();
    let bound = terms.mk_var("bound", Sort::Int);
    let zero = terms.mk_int(0.into());
    let one = terms.mk_int(1.into());
    let two = terms.mk_int(2.into());
    let successor = terms.mk_add(vec![bound, one]);
    let inner = terms.mk_lambda_array(bound, successor);
    let outer = terms.mk_lambda_array(bound, inner);

    let selected = terms.mk_select(outer, zero);
    assert_eq!(selected, inner);
    assert_eq!(terms.mk_select(selected, one), two);
}

#[test]
fn lambda_substitution_same_name_distinct_identities_remain_distinct() {
    let mut terms = TermStore::new();
    let (outer, inner) = distinct_same_name(&mut terms);
    let three = terms.mk_int(3.into());
    let five = terms.mk_int(5.into());
    let eight = terms.mk_int(8.into());
    let body = terms.mk_add(vec![outer, inner]);
    let lambda = terms.mk_lambda_array(inner, body);

    let substituted = terms.substitute_var(lambda, outer, three);
    assert_eq!(terms.get_lambda_array(substituted).unwrap().0, inner);
    assert_eq!(terms.mk_select(substituted, five), eight);
}

#[test]
fn lambda_substitution_freshens_a_binder_that_would_capture_the_replacement() {
    let mut terms = TermStore::new();
    let outer = terms.mk_var("outer", Sort::Int);
    let free = terms.mk_var("free", Sort::Int);
    let one = terms.mk_int(1.into());
    let body = terms.mk_add(vec![outer, free]);
    let inner = terms.mk_lambda_array(free, body);
    let lambda = terms.mk_lambda_array(outer, inner);

    let selected = terms.mk_select(lambda, free);
    let (binder, _) = terms.get_lambda_array(selected).unwrap();
    assert_ne!(binder, free);
    assert!(matches!(terms.get(binder), TermData::Var(..)));
    let result = terms.mk_select(selected, one);
    let expected = terms.mk_add(vec![free, one]);
    assert_eq!(result, expected);
}

#[test]
fn lambda_substitution_same_spelling_does_not_capture_a_distinct_replacement() {
    let mut terms = TermStore::new();
    let source = terms.mk_var("source", Sort::Int);
    let (bound, replacement) = distinct_same_name(&mut terms);
    let one = terms.mk_int(1.into());
    let body = terms.mk_add(vec![source, bound]);
    let lambda = terms.mk_lambda_array(bound, body);

    let substituted = terms.substitute_var(lambda, source, replacement);
    assert_eq!(terms.get_lambda_array(substituted).unwrap().0, bound);
    let result = terms.mk_select(substituted, one);
    let expected = terms.mk_add(vec![replacement, one]);
    assert_eq!(result, expected);
}

#[test]
fn lambda_substitution_shared_free_occurrences_survive_both_walk_orders() {
    for binder_first in [true, false] {
        let mut terms = TermStore::new();
        let source = terms.mk_var("source", Sort::Int);
        let one = terms.mk_int(1.into());
        let seven = terms.mk_int(7.into());
        let body = terms.mk_add(vec![source, one]);
        let lambda = terms.mk_lambda_array(source, body);
        let args = if binder_first {
            [lambda, source]
        } else {
            [source, lambda]
        };
        let observed = terms.mk_app(Symbol::named("observe"), args, Sort::Bool);

        let rewritten = terms.substitute_var(observed, source, seven);
        let TermData::App(_, actual) = terms.get(rewritten) else {
            panic!("retain the observation application");
        };
        let lambda_index = usize::from(!binder_first);
        assert_eq!(actual[lambda_index], lambda);
        assert_eq!(actual[1 - lambda_index], seven);
    }
}

#[test]
fn lambda_substitution_preserves_name_bound_quantifiers_and_simultaneous_lets() {
    let mut terms = TermStore::new();
    let (source, differently_identified) = distinct_same_name(&mut terms);
    let zero = terms.mk_int(0.into());
    let three = terms.mk_int(3.into());
    let predicate = terms.mk_eq(source, zero);
    let forall = terms.mk_forall(vec![("same_name".to_owned(), Sort::Int)], predicate);
    let exists = terms.mk_exists(vec![("same_name".to_owned(), Sort::Int)], predicate);
    assert_eq!(terms.substitute_var(forall, source, three), forall);
    assert_eq!(terms.substitute_var(exists, source, three), exists);
    // Both same-spelled IDs are name-bound in the SMT quantifier body.
    let other_predicate = terms.mk_eq(differently_identified, zero);
    let other = terms.mk_forall(vec![("same_name".to_owned(), Sort::Int)], other_predicate);
    assert_eq!(
        terms.substitute_var(other, differently_identified, three),
        other
    );
    let let_term = terms.mk_let(vec![("same_name".to_owned(), source)], source);
    let rewritten = terms.substitute_var(let_term, source, three);
    assert!(matches!(terms.get(rewritten), TermData::Let(bindings, body)
        if bindings == &vec![("same_name".to_owned(), three)] && *body == source));
}

#[test]
fn lambda_substitution_requires_a_variable_target() {
    let mut terms = TermStore::new();
    let zero = terms.mk_int(0.into());
    let one = terms.mk_int(1.into());
    assert_eq!(terms.substitute_var(zero, zero, one), zero);
}

#[test]
fn lambda_substitution_avoids_named_capture_of_all_same_spelled_var_ids() {
    for universal in [true, false] {
        let mut terms = TermStore::new();
        let source = terms.mk_var("source", Sort::Int);
        let (first, second) = distinct_same_name(&mut terms);
        let body = terms.mk_app(
            Symbol::named("predicate"),
            [source, first, second],
            Sort::Bool,
        );
        let hint = terms.mk_app(Symbol::named("hint"), [first, second], Sort::Int);
        let bindings = vec![("same_name".to_owned(), Sort::Int)];
        let quantifier = if universal {
            terms.mk_forall_with_triggers(bindings, body, vec![vec![hint]])
        } else {
            terms.mk_exists_with_triggers(bindings, body, vec![vec![hint]])
        };
        terms.set_quantifier_id(quantifier, "preserve-qid".to_owned());
        terms.set_quantifier_no_patterns(quantifier, vec![hint]);
        let lambda = terms.mk_lambda_array(source, quantifier);

        let rewritten = terms.mk_select(lambda, first);
        let (bindings, body, triggers) = match terms.get(rewritten) {
            TermData::Forall(bindings, body, triggers)
            | TermData::Exists(bindings, body, triggers) => (bindings, *body, triggers),
            other => panic!("retain quantifier: {other:?}"),
        };
        assert_ne!(bindings[0].0, "same_name");
        let TermData::App(_, args) = terms.get(body) else {
            panic!("retain predicate");
        };
        assert_eq!(args[0], first);
        assert_eq!(args[1], args[2]);
        assert_ne!(args[1], first);
        assert_ne!(args[1], second);
        assert!(matches!(terms.get(args[1]), TermData::Var(name, _) if name == &bindings[0].0));
        let TermData::App(_, trigger_args) = terms.get(triggers[0][0]) else {
            panic!("retain trigger");
        };
        assert_eq!(trigger_args.as_slice(), [args[1], args[1]]);
        assert_eq!(terms.quantifier_no_patterns(rewritten), &[triggers[0][0]]);
        assert_eq!(terms.quantifier_id(rewritten), Some("preserve-qid"));
        assert_eq!(terms.quantifier_no_patterns(quantifier), &[hint]);
    }
}

#[test]
fn lambda_substitution_mixed_name_and_exact_lambda_scopes_avoid_capture() {
    let mut terms = TermStore::new();
    let source = terms.mk_var("source", Sort::Int);
    let (inner_bound, replacement) = distinct_same_name(&mut terms);
    let zero = terms.mk_int(0.into());
    let body = terms.mk_add(vec![source, inner_bound, replacement]);
    let inner = terms.mk_lambda_array(inner_bound, body);
    let predicate = terms.mk_app(
        Symbol::named("observe"),
        [source, inner, replacement],
        Sort::Bool,
    );
    let quantified = terms.mk_forall(vec![("same_name".to_owned(), Sort::Int)], predicate);

    let rewritten = terms.substitute_var(quantified, source, replacement);
    let TermData::Forall(bindings, predicate, _) = terms.get(rewritten) else {
        panic!("retain outer quantifier");
    };
    let name = bindings[0].0.clone();
    let TermData::App(_, args) = terms.get(*predicate) else {
        panic!("retain observation");
    };
    let args = args.clone();
    assert_eq!(args[0], replacement);
    let outer_bound = args[2];
    assert!(matches!(terms.get(outer_bound), TermData::Var(bound, _) if bound == &name));
    let (lambda_bound, _) = terms.get_lambda_array(args[1]).unwrap();
    // Its distinct exact identity is local even though the outer binder
    // used the same original spelling.
    assert_eq!(lambda_bound, inner_bound);
    let selected = terms.mk_select(args[1], zero);
    let expected = terms.mk_add(vec![replacement, outer_bound]);
    assert_eq!(selected, expected);
}

#[test]
fn lambda_substitution_named_let_capture_keeps_rhs_in_enclosing_scope() {
    let mut terms = TermStore::new();
    let source = terms.mk_var("source", Sort::Int);
    let bound = terms.mk_var("bound", Sort::Int);
    let body = terms.mk_add(vec![source, bound]);
    let let_term = terms.mk_let(vec![("bound".to_owned(), source)], body);
    let lambda = terms.mk_lambda_array(source, let_term);

    let rewritten = terms.mk_select(lambda, bound);
    let TermData::Let(bindings, body) = terms.get(rewritten) else {
        panic!("retain simultaneous let");
    };
    assert_ne!(bindings[0].0, "bound");
    assert_eq!(bindings[0].1, bound);
    let TermData::App(_, args) = terms.get(*body) else {
        panic!("retain sum");
    };
    assert!(args.contains(&bound));
    let renamed = args.iter().copied().find(|&arg| arg != bound).unwrap();
    assert!(matches!(terms.get(renamed), TermData::Var(name, _) if name == &bindings[0].0));
}

#[test]
fn lambda_substitution_preserves_inner_named_shadows_and_annotation_identity() {
    let mut terms = TermStore::new();
    let source = terms.mk_var("source", Sort::Int);
    let bound = terms.mk_var("bound", Sort::Int);
    let local = terms.mk_var("local", Sort::Int);
    let zero = terms.mk_int(0.into());
    let inner_body = terms.mk_eq(bound, zero);
    let shadow = terms.mk_exists(vec![("bound".to_owned(), Sort::Int)], inner_body);
    let truth = terms.mk_bool(true);
    let hint_only = terms.mk_forall(vec![("local".to_owned(), Sort::Int)], truth);
    let hint = terms.mk_app(Symbol::named("hint"), [bound, local], Sort::Int);
    terms.set_quantifier_no_patterns(hint_only, vec![hint]);
    let predicate = terms.mk_app(
        Symbol::named("observe"),
        [source, bound, shadow, hint_only],
        Sort::Bool,
    );
    let outer = terms.mk_forall(vec![("bound".to_owned(), Sort::Int)], predicate);

    let rewritten = terms.substitute_var(outer, source, bound);
    let TermData::Forall(_, body, _) = terms.get(rewritten) else {
        panic!("retain outer binder");
    };
    let TermData::App(_, args) = terms.get(*body) else {
        panic!("retain observation");
    };
    assert_eq!(args[0], bound);
    assert_eq!(args[2], shadow);
    assert_ne!(args[3], hint_only);
    let renamed_hint = terms.quantifier_no_patterns(args[3])[0];
    let TermData::App(_, hint_args) = terms.get(renamed_hint) else {
        panic!("retain hint");
    };
    assert_eq!(hint_args[0], args[1]);
    assert_ne!(hint_args[1], local);
    assert_eq!(terms.quantifier_no_patterns(hint_only), &[hint]);
}

#[test]
fn lambda_substitution_fresh_names_avoid_unused_nested_smt_binders() {
    let mut terms = TermStore::new();
    let source = terms.mk_var("source", Sort::Int);
    let replacement = terms.mk_var("bound", Sort::Int);
    let body = terms.mk_app(
        Symbol::named("predicate"),
        [source, replacement],
        Sort::Bool,
    );
    let occupied: Vec<_> = (0..32)
        .map(|index| {
            (
                format!("__ay_quantifier_substitution_bound_{index}"),
                Sort::Int,
            )
        })
        .collect();
    let inner = terms.mk_forall(occupied.clone(), body);
    let outer = terms.mk_forall(vec![("bound".to_owned(), Sort::Int)], inner);

    let rewritten = terms.substitute_var(outer, source, replacement);
    let TermData::Forall(bindings, _, _) = terms.get(rewritten) else {
        panic!("retain outer binder");
    };
    assert!(occupied.iter().all(|(name, _)| name != &bindings[0].0));
}

#[test]
fn lambda_substitution_updates_body_triggers_and_no_patterns_together() {
    let mut terms = TermStore::new();
    let source = terms.mk_var("source", Sort::Int);
    let replacement = terms.mk_var("replacement", Sort::Int);
    let bound = terms.mk_var("bound", Sort::Int);
    let body = terms.mk_app(Symbol::named("predicate"), [source, bound], Sort::Bool);
    let hint = terms.mk_app(Symbol::named("hint"), [source, bound], Sort::Int);
    let quantifier = terms.mk_forall_with_triggers(
        vec![("bound".to_owned(), Sort::Int)],
        body,
        vec![vec![hint]],
    );
    terms.set_quantifier_no_patterns(quantifier, vec![hint]);
    terms.set_quantifier_id(quantifier, "transport-qid".to_owned());

    let rewritten = terms.substitute_var(quantifier, source, replacement);
    let TermData::Forall(_, body, triggers) = terms.get(rewritten) else {
        panic!("retain quantifier");
    };
    let TermData::App(_, args) = terms.get(*body) else {
        panic!("retain predicate");
    };
    assert_eq!(args.as_slice(), [replacement, bound]);
    let TermData::App(_, args) = terms.get(triggers[0][0]) else {
        panic!("retain trigger");
    };
    assert_eq!(args.as_slice(), [replacement, bound]);
    assert_eq!(terms.quantifier_no_patterns(rewritten), &[triggers[0][0]]);
    assert_eq!(terms.quantifier_id(rewritten), Some("transport-qid"));
    assert_eq!(terms.quantifier_no_patterns(quantifier), &[hint]);
    assert!(
        matches!(terms.get(quantifier), TermData::Forall(_, _, triggers)
        if triggers[0][0] == hint)
    );
}

#[test]
fn lambda_substitution_retains_hint_only_updates_without_mutating_old_metadata() {
    for in_trigger in [false, true] {
        for captures_bound_name in [false, true] {
            let mut terms = TermStore::new();
            let source = terms.mk_var("source", Sort::Int);
            let bound = terms.mk_var("bound", Sort::Int);
            let replacement = if captures_bound_name {
                bound
            } else {
                terms.mk_var("replacement", Sort::Int)
            };
            let truth = terms.mk_bool(true);
            let hint = terms.mk_app(Symbol::named("hint"), [source, bound], Sort::Int);
            let triggers = if in_trigger {
                vec![vec![hint]]
            } else {
                Vec::new()
            };
            let quantifier = terms.mk_forall_with_triggers(
                vec![("bound".to_owned(), Sort::Int)],
                truth,
                triggers,
            );
            terms.set_quantifier_no_patterns(quantifier, vec![hint, TermId::SENTINEL]);

            let rewritten = terms.substitute_var(quantifier, source, replacement);
            assert_ne!(rewritten, quantifier);
            let TermData::Forall(_, body, triggers) = terms.get(rewritten) else {
                panic!("retain quantifier");
            };
            assert_eq!(*body, truth);
            let new_hint = terms.quantifier_no_patterns(rewritten)[0];
            let TermData::App(_, args) = terms.get(new_hint) else {
                panic!("retain annotation");
            };
            assert_eq!(args[0], replacement);
            if captures_bound_name || !in_trigger {
                assert_ne!(args[1], bound);
            } else {
                assert_eq!(args[1], bound);
            }
            if in_trigger {
                assert_eq!(triggers[0][0], new_hint);
            }
            assert_eq!(terms.quantifier_no_patterns(rewritten)[1], TermId::SENTINEL);
            assert_eq!(
                terms.quantifier_no_patterns(quantifier),
                &[hint, TermId::SENTINEL]
            );
        }
    }
}

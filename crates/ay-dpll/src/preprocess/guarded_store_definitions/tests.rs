// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::ProofStep;

mod fixtures;
use fixtures::{evaluate, Fixture, Value};

#[test]
fn guarded_and_direct_covers_authenticate_exact_whole_array_definitions() {
    for width in [2, 129] {
        let mut f = Fixture::new(width, [1, 2]);
        let result = f.derive().expect("source-bound guarded cover");
        assert_eq!(result.variable(), f.request.variable);
        assert!(f.authenticate(result.proof().0));
        let TermData::App(Symbol::Named(op), args) = f.terms.get(result.replacement()) else {
            panic!("store definition")
        };
        assert_eq!(op, "store");
        let TermData::Ite(guard, _, _) = f.terms.get(args[2]) else {
            panic!("raw ite")
        };
        assert_eq!(*guard, f.request.cases[0].guard);
        let direct = f.terms.mk_app(
            Symbol::named("or"),
            f.request.cases.map(|case| case.guard),
            Sort::Bool,
        );
        f.request.cover_source = direct;
        f.request.activation = None;
        f.roots[2] = direct;
        f.roots.pop();
        assert!(f.derive().is_some());
    }
}

#[test]
fn exhaustive_tiny_arrays_preserve_overlapping_guards_and_unwritten_cells() {
    use crate::preprocess::{PreprocessingPass, VariableSubstitution};
    for values in [[1, 2], [1, 1]] {
        let mut f = Fixture::new(2, values);
        let derived = f.derive().unwrap();
        let mut rewritten = f.roots.clone();
        rewritten.insert(0, derived.definition());
        let mut substitution = VariableSubstitution::new();
        assert!(substitution.apply(&mut f.terms, &mut rewritten));
        assert_eq!(
            substitution.substitutions().get(&f.request.variable),
            Some(&derived.replacement())
        );
        let mut admitted = 0;
        for first in 0..4 {
            for second in 0..4 {
                for g in [false, true] {
                    for h in [false, true] {
                        let eval = |term| evaluate(&f.terms, term, [first, second], g, h);
                        let original = f.roots.iter().all(|&root| eval(root) == Value::Bool(true));
                        let definition = eval(derived.definition()) == Value::Bool(true);
                        let transformed = rewritten
                            .iter()
                            .all(|&root| eval(root) == Value::Bool(true));
                        assert_eq!(original, definition && transformed);
                        if original {
                            admitted += 1;
                            assert_eq!(second, 0);
                        }
                        if g && h {
                            assert_eq!(transformed, values[0] == values[1]);
                        }
                    }
                }
            }
        }
        assert_eq!(admitted, if values[0] == values[1] { 3 } else { 2 });
    }
}

#[test]
fn missing_original_support_or_activation_cannot_license_a_definition() {
    for omitted in 0..4 {
        let mut f = Fixture::new(2, [1, 2]);
        f.roots.remove(omitted);
        assert!(f.derive().is_none(), "missing original root {omitted}");
    }
    let mut f = Fixture::new(2, [1, 2]);
    let fake = f.terms.mk_var("unasserted", Sort::Bool);
    f.request.activation = Some(fake);
    assert!(f.derive().is_none());
}

#[test]
fn uncovered_or_nonconjunct_branch_hints_are_not_source_authority() {
    let mut f = Fixture::new(2, [1, 2]);
    let g = f.request.cases[0].guard;
    let outsider = f.terms.mk_var("outsider", Sort::Bool);
    let bad_cover = f
        .terms
        .mk_app(Symbol::named("or"), [g, outsider], Sort::Bool);
    f.request.cover_source = bad_cover;
    f.request.activation = None;
    f.roots[2] = bad_cover;
    assert!(f.derive().is_none());

    let mut f = Fixture::new(2, [1, 2]);
    let case = f.request.cases[0];
    let eq = raw_eq(&mut f.terms, f.request.variable, case.store);
    let other = f.terms.mk_var("choice", Sort::Bool);
    let body = f.terms.mk_app(Symbol::named("or"), [other, eq], Sort::Bool);
    let not_g = f.terms.mk_not_raw(case.guard);
    let source = f
        .terms
        .mk_app(Symbol::named("or"), [not_g, body], Sort::Bool);
    f.request.cases[0].source = source;
    f.roots[0] = source;
    assert!(f.derive().is_none());
}

#[test]
fn malformed_or_different_store_skeleton_and_cycles_refuse() {
    for variant in 0..8 {
        let mut f = Fixture::new(2, [1, 2]);
        let case = f.request.cases[1];
        let TermData::App(_, args) = f.terms.get(case.store) else {
            panic!("store")
        };
        let mut args = args.clone();
        let mut sort = f.terms.sort(case.store).clone();
        let mut operator = "store";
        match variant {
            0 => args[1] = f.terms.true_term(),
            1 => args[1] = f.terms.mk_bitvec(0.into(), 2),
            2 => args[2] = f.terms.true_term(),
            3 => args[0] = f.request.variable,
            4 => sort = Sort::Bool,
            5 => {
                args.pop();
            }
            6 => operator = "not_store",
            7 => {
                let fill = f.terms.mk_bitvec(3.into(), 2);
                args[0] = f.terms.mk_const_array(Sort::Bool, fill);
            }
            _ => unreachable!(),
        }
        let malformed = f.terms.mk_app(Symbol::named(operator), args, sort);
        f.request.cases[1].store = malformed;
        // Make the changed term an actual source definition: refusal must
        // exercise shape/typing/independence, not merely a stale source hint.
        let eq = raw_eq(&mut f.terms, f.request.variable, malformed);
        let not_guard = f.terms.mk_not_raw(case.guard);
        let source = f
            .terms
            .mk_app(Symbol::named("or"), [not_guard, eq], Sort::Bool);
        f.request.cases[1].source = source;
        f.roots[1] = source;
        assert!(f.derive().is_none());
    }
}

#[test]
fn proof_mutation_and_source_replacement_fail_independent_authentication() {
    let mut f = Fixture::new(129, [1, 2]);
    let derived = f.derive().unwrap();
    let (proof, conclusion) = derived.proof();
    let mut forged = proof.clone();
    let ProofStep::Step { clause, .. } = &mut forged.steps[conclusion.0 as usize] else {
        panic!("final resolution")
    };
    clause[0] = f.terms.false_term();
    assert!(!f.authenticate(&forged));
    f.roots[0] = f.terms.true_term();
    assert!(!f.authenticate(proof));
}

#[test]
fn shared_progress_limits_both_planning_and_full_source_authentication() {
    let mut f = Fixture::new(2, [1, 2]);
    let mut charges = Vec::new();
    assert!(
        derive(&mut f.terms, &f.roots, f.request, &mut |work, bytes| {
            charges.push((work, bytes));
            true
        })
        .is_some()
    );
    assert!(charges.iter().filter(|(_, bytes)| *bytes > 0).count() > 10);
    for stop in [0, 1, charges.len() / 2, charges.len() - 1] {
        let mut f = Fixture::new(2, [1, 2]);
        let mut calls = 0;
        assert!(
            derive(&mut f.terms, &f.roots, f.request, &mut |_, _| {
                let allowed = calls < stop;
                calls += 1;
                allowed
            })
            .is_none(),
            "refusal at callback {stop}"
        );
        assert!(f.derive().is_some(), "fresh attempt after refusal");
    }
    let totals = charges.iter().fold((0, 0), |(work, bytes), charge| {
        (work + charge.0, bytes + charge.1)
    });
    for (work_limit, byte_limit, succeeds) in [
        (totals.0, totals.1, true),
        (totals.0 - 1, totals.1, false),
        (totals.0, totals.1 - 1, false),
    ] {
        let mut f = Fixture::new(2, [1, 2]);
        let (mut work_left, mut bytes_left) = (work_limit, byte_limit);
        let result = derive(&mut f.terms, &f.roots, f.request, &mut |work, bytes| {
            let (Some(work), Some(bytes)) =
                (work_left.checked_sub(work), bytes_left.checked_sub(bytes))
            else {
                return false;
            };
            (work_left, bytes_left) = (work, bytes);
            true
        });
        assert_eq!(result.is_some(), succeeds);
    }
}

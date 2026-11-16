// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

mod boolean_canonical;
mod fixtures;
mod resources;
use fixtures::*;

#[test]
fn actual_guarded_batch_and_substitution_replay_the_complete_original_branch() {
    for width in [8, 129, 136] {
        let mut f = Fixture::new(width);
        let (proof, id) = f.plan(f.after).expect("recorded canonical scalar equality");
        let checked = authenticate(&f.terms, &f.roots, &proof).unwrap();
        assert_eq!(checked.clause(id), Some([f.after].as_slice()));
        assert!(proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::EqSymmetric,
                ..
            }
        )));
        assert!(!proof.steps.iter().any(|step| matches!(step,
            ProofStep::Assume(term) if *term == f.after || f.units.iter().any(|unit| unit.term() == *term))));

        // A strict source-refutation skeleton, not a native-solver run: the
        // authored opposite of the replayed consequence must close to empty.
        let opposite = f.terms.mk_not_raw(f.after);
        f.roots.push(opposite);
        let (mut proof, derived) = f.plan(f.after).unwrap();
        let opposite_id = proof.add_assume(opposite, None);
        let end = proof.add_resolution(Vec::new(), f.after, derived, opposite_id);
        assert_eq!(
            authenticate(&f.terms, &f.roots, &proof)
                .unwrap()
                .clause(end),
            Some([].as_slice())
        );
    }
}

#[test]
fn expanded_and_changed_guard_targets_are_not_the_recorded_spelling() {
    for change in 0..2 {
        let mut f = Fixture::new(129);
        let scalar = match change {
            0 => {
                let expanded = f.terms.mk_eq_coerce(f.payload, f.high);
                assert_eq!(expanded, f.guard);
                expanded
            }
            1 => {
                let TermData::Ite(_, yes, no) = f.terms.get(f.payload) else {
                    unreachable!()
                };
                let (yes, no) = (*yes, *no);
                let other_guard = f.terms.mk_var("unrelated guard", Sort::Bool);
                let other = f.terms.mk_ite_raw(other_guard, yes, no);
                app(&mut f.terms, "=", &[f.high, other])
            }
            _ => unreachable!(),
        };
        let target = f.replace_scalar_target(scalar);
        assert_ne!(target, f.after);
        assert!(f.plan(target).is_none());
        assert!(
            f.plan(f.after).is_some(),
            "fresh exact replay still succeeds"
        );
    }
}

#[test]
fn legacy_reversed_raw_target_remains_source_authenticated_before_the_retry() {
    let mut f = Fixture::new(129);
    let reversed = app(&mut f.terms, "=", &[f.payload, f.high]);
    let target = f.replace_scalar_target(reversed);
    assert_ne!(target, f.after);
    // This is an authored alternate proof hint, not a spelling emitted by VS.
    // Its old positional congruence proof remains valid and must keep working.
    let (proof, id) = f.plan(target).expect("legacy exact raw record");
    assert_eq!(
        authenticate(&f.terms, &f.roots, &proof).unwrap().clause(id),
        Some([target].as_slice())
    );
    let (proof, id) = f.plan(f.after).expect("actual canonical producer record");
    assert_eq!(
        authenticate(&f.terms, &f.roots, &proof).unwrap().clause(id),
        Some([f.after].as_slice())
    );
}

#[test]
fn missing_unit_channel_activation_branch_and_late_entries_cannot_authorize_replay() {
    for change in 0..4 {
        let mut f = Fixture::new(129);
        match change {
            0 => f.units.clear(),
            1 => f.roots.retain(|&root| root != f.activation),
            2 => {
                let _ = f.roots.remove(1);
            }
            3 => {
                for (_, _, stamp) in f.entries.values_mut() {
                    *stamp = f.stamp + 1;
                }
            }
            _ => unreachable!(),
        }
        assert!(f.plan(f.after).is_none());
    }
}

#[test]
fn strict_checker_rejects_mutated_symmetry_and_removed_original_authority() {
    let mut f = Fixture::new(129);
    let (proof, _) = f.plan(f.after).unwrap();
    let mut mutation = proof.clone();
    let step = mutation
        .steps
        .iter_mut()
        .find(|step| {
            matches!(
                step,
                ProofStep::Step {
                    rule: AletheRule::EqSymmetric,
                    ..
                }
            )
        })
        .unwrap();
    let ProofStep::Step { clause, .. } = step else {
        unreachable!()
    };
    *clause = vec![f.terms.false_term()];
    assert!(authenticate(&f.terms, &f.roots, &mutation).is_err());
    f.roots.retain(|&root| root != f.activation);
    assert!(authenticate(&f.terms, &f.roots, &proof).is_err());
}

#[test]
fn exact_same_and_swapped_operand_shapes_use_existing_rules() {
    let mut f = Fixture::new(129);
    let (prefix, changed) = f.changed_child();
    for (args, rewritten, children) in [
        (
            [f.value, f.high],
            [f.payload, f.high],
            [changed, EqRes::Unchanged],
        ),
        (
            [f.high, f.value],
            [f.high, f.payload],
            [EqRes::Unchanged, changed],
        ),
    ] {
        let term = app(&mut f.terms, "=", &args);
        let set = f.roots.iter().copied().collect();
        let mut cx = PlanCx::new(&set, &f.roots, &f.records, &f.entries, &[], false)
            .with_array_units(&f.units, &allow);
        cx.scalar_equality_mode = ScalarEqualityMode::ArrayCanonical;
        cx.chain = prefix.clone();
        let (target, (equality, id)) = PropagationChainPlanner {
            terms: &mut f.terms,
        }
        .plan_scalar_canonical_fold(
            &mut cx,
            term,
            &Symbol::named("="),
            &args,
            &rewritten,
            &children,
        )
        .unwrap();
        assert!(
            matches!(f.terms.get(target), TermData::App(_, args) if args.as_slice() == [f.high, f.payload])
        );
        assert_eq!(
            authenticate(&f.terms, &f.roots, &cx.chain)
                .unwrap()
                .clause(id),
            Some([equality].as_slice())
        );
    }
}

#[test]
fn nested_record_attempts_restore_mode_and_keep_memoized_spellings_separate() {
    let mut f = Fixture::new(8);
    let raw_scalar = app(&mut f.terms, "=", &[f.payload, f.high]);
    let raw_target = f.replace_scalar_target(raw_scalar);
    let canonical_scalar = app(&mut f.terms, "=", &[f.high, f.payload]);
    let wrong = f.replace_scalar_target(f.terms.true_term());
    let set = f.roots.iter().copied().collect();
    let mut cx = PlanCx::new(&set, &f.roots, &f.records, &f.entries, &[], false)
        .with_array_units(&f.units, &allow);
    cx.scalar_equality_mode = ScalarEqualityMode::ArrayCanonical;
    let mut planner = PropagationChainPlanner {
        terms: &mut f.terms,
    };
    for target in [raw_target, f.after] {
        let id = planner.plan_derive_clause(&mut cx, target).unwrap();
        assert!(cx.scalar_equality_mode == ScalarEqualityMode::ArrayCanonical);
        assert_eq!(
            authenticate(planner.terms, &f.roots, &cx.chain)
                .unwrap()
                .clause(id),
            Some([target].as_slice())
        );
    }
    for (mode, expected) in [
        (ScalarEqualityMode::Legacy, raw_scalar),
        (ScalarEqualityMode::ArrayCanonical, canonical_scalar),
    ] {
        assert!(matches!(cx.eq_memo.get(&(f.scalar, f.stamp, mode)),
            Some(Some(EqRes::Changed { to, .. })) if *to == expected));
    }
    assert!(planner.plan_derive_clause(&mut cx, wrong).is_none());
    assert!(cx.scalar_equality_mode == ScalarEqualityMode::ArrayCanonical);
}

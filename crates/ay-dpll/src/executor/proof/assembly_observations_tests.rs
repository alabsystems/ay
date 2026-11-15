// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Pins for the assembly count (#r30-4a-nested-assembly-count).

use super::*;

fn observe_n(count: u64) -> Vec<bool> {
    (0..count).map(|_| observe()).collect()
}

#[test]
fn an_allowance_admits_exactly_its_observations() {
    assert!(!allowance_spent(), "no allowance, nothing spent");
    let scope = enter_allowance(3);
    assert_eq!(observe_n(3), vec![false; 3], "the third granted one runs");
    assert!(!allowance_spent());
    assert!(
        observe(),
        "the fourth observation finds the allowance spent"
    );
    assert!(allowance_spent());
    assert_eq!(scope.spent(), 4);
    drop(scope);
    assert!(!allowance_spent(), "no stop once the allowance has ended");
    assert!(!observe(), "observing without an allowance never stops");
}

#[test]
fn a_nested_allowance_is_bounded_by_the_enclosing_one_and_restores_it() {
    let outer = enter_allowance(5);
    observe_n(2);
    {
        let inner = enter_allowance(10);
        assert_eq!(observe_n(3), vec![false; 3], "five of the outer five");
        assert!(observe(), "the enclosing allowance bounds nested work");
        assert_eq!(inner.spent(), 4);
    }
    assert!(allowance_spent(), "the outer allowance stays spent");
    assert_eq!(outer.spent(), 6);
    drop(outer);

    let outer = enter_allowance(5);
    {
        let _inner = enter_allowance(1);
        observe_n(1);
        assert!(observe(), "the tighter inner allowance binds first");
    }
    assert!(
        !allowance_spent(),
        "the outer one is in force again: 2 of 5"
    );
    assert_eq!(observe_n(3), vec![false; 3]);
    assert!(observe());
    drop(outer);
}

#[test]
fn the_count_is_per_thread_and_monotone() {
    let before = thread_observations();
    let scope = enter_allowance(1);
    std::thread::spawn(|| {
        let other = thread_observations();
        assert!(
            (0..100).all(|_| !observe()),
            "another thread is not bound by this thread's allowance"
        );
        assert_eq!(thread_observations() - other, 100);
    })
    .join()
    .expect("the other thread ran");
    assert!(
        !allowance_spent(),
        "work on another thread spends nothing here"
    );
    assert!(!observe());
    assert!(observe());
    drop(scope);
    assert_eq!(thread_observations() - before, 2);
}

#[test]
fn a_zero_allowance_stops_at_the_first_observation() {
    let _scope = enter_allowance(0);
    assert!(!allowance_spent(), "nothing observed yet");
    assert!(observe());
}

/// Three `LraFarkas` lemmas with no certificate, each certifiable on its own,
/// in `exec`'s arena.
fn three_uncertified_lemmas(exec: &mut crate::Executor) -> ay_core::Proof {
    use ay_core::{ProofStep, Sort, TheoryLemmaKind};
    let terms = &mut exec.ctx.terms;
    let zero = terms.mk_rational(num_rational::BigRational::from_integer(0.into()));
    let mut proof = ay_core::Proof::new();
    for index in 0..3 {
        let x = terms.mk_var(&format!("observed_x{index}"), Sort::Real);
        let below = terms.mk_lt(x, zero);
        let above = terms.mk_gt(x, zero);
        proof.add_step(ProofStep::TheoryLemma {
            theory: "LRA".to_string(),
            clause: vec![terms.mk_not_raw(below), terms.mk_not_raw(above)],
            farkas: None,
            kind: TheoryLemmaKind::LraFarkas,
            lia: None,
        });
    }
    proof
}

fn certified_kinds(proof: &ay_core::Proof) -> Vec<ay_core::TheoryLemmaKind> {
    proof
        .steps
        .iter()
        .filter_map(|step| match step {
            ay_core::ProofStep::TheoryLemma { kind, .. } => Some(*kind),
            _ => None,
        })
        .collect()
}

/// The assembly's Farkas pass charges one observation per reconstruction
/// attempt, and an allowance ends it at an attempt: with one observation
/// granted, the first lemma is certified and the other two are demoted to
/// `Generic` (trust), the fail-closed direction. Counterfactual: a pass
/// polling only the search's stop charges nothing and certifies all three.
#[test]
fn the_farkas_pass_is_charged_per_attempt_and_an_allowance_ends_it() {
    use ay_core::TheoryLemmaKind::{Generic, LraFarkas};
    let mut exec = crate::Executor::new();
    let mut proof = three_uncertified_lemmas(&mut exec);
    let before = thread_observations();
    exec.reconstruct_missing_farkas_and_demote(&mut proof, &[]);
    assert_eq!(thread_observations() - before, 3, "one per attempt");
    assert_eq!(certified_kinds(&proof), vec![LraFarkas; 3]);

    let mut proof = three_uncertified_lemmas(&mut exec);
    let scope = enter_allowance(1);
    exec.reconstruct_missing_farkas_and_demote(&mut proof, &[]);
    assert_eq!(scope.spent(), 2, "the second attempt found it spent");
    drop(scope);
    assert_eq!(
        certified_kinds(&proof),
        vec![LraFarkas, Generic, Generic],
        "the attempts it never made leave their lemmas demoted"
    );
}

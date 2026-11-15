// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! (#derived-entailment-depth) Instances of a universal entailed only through
//! a derived unit fact, over instance-minted terms, stop at the check-sat's
//! budget and wait in the deferred queue.

use super::*;
use ay_core::term::Symbol;
use ay_core::{Sort, TermStore};
use num_bigint::BigInt;

const GROUND_TERMS: usize = 12;

/// `(forall x. (P x))` behind the guard `g`, and `GROUND_TERMS` ground
/// arguments of `P`, each at generation `generation` (as if an earlier round's
/// instance had minted it). `g` is asserted directly when `guard_asserted`, and
/// otherwise derived from the asserted `grp` through `(=> grp g)` (#unit-bcp).
fn round(guard_asserted: bool, generation: u32) -> EMatchingResult {
    let mut terms = TermStore::new();
    let grp = terms.mk_var("dd_grp", Sort::Bool);
    let g = terms.mk_var("dd_g", Sort::Bool);
    let x = terms.mk_var("x", Sort::Int);
    let p_x = terms.mk_app(Symbol::named("dd_P"), vec![x], Sort::Bool);
    let forall = terms.mk_forall(vec![("x".to_string(), Sort::Int)], p_x);
    let guarded = terms.mk_app(Symbol::named("=>"), [g, forall], Sort::Bool);
    let mut assertions = vec![guarded, grp];
    if guard_asserted {
        assertions.push(g);
    } else {
        assertions.push(terms.mk_app(Symbol::named("=>"), [grp, g], Sort::Bool));
    }
    let mut tracker = GenerationTracker::new();
    for i in 0..GROUND_TERMS {
        let c = terms.mk_var(&format!("dd_c{i}"), Sort::Int);
        let seven = terms.mk_int(BigInt::from(7));
        let q_c = terms.mk_app(Symbol::named("dd_Q"), vec![c, seven], Sort::Bool);
        let p_c = terms.mk_app(Symbol::named("dd_P"), vec![c], Sort::Bool);
        assertions.push(terms.mk_or(vec![q_c, p_c]));
        tracker.set(c, generation);
    }
    let mut state = PersistentMatchState::new();
    perform_ematching_with_generations(
        &mut terms,
        &assertions,
        &[],
        &[],
        &EMatchingConfig::default(),
        tracker,
        None,
        &|| false,
        &mut state,
        None,
    )
}

#[test]
fn deep_instances_of_a_derived_universal_stop_at_the_budget() {
    let result = round(false, DERIVED_ENTAILMENT_FREE_GENERATION);
    assert_eq!(result.instantiations.len(), DERIVED_ENTAILMENT_DEEP_BUDGET);
    assert_eq!(
        result.deferred.len(),
        GROUND_TERMS - DERIVED_ENTAILMENT_DEEP_BUDGET,
        "the rest wait in the deferred queue, which keeps SAT unpublished"
    );
}

#[test]
fn a_derived_universal_is_instantiated_freely_over_input_terms() {
    let result = round(false, 0);
    assert_eq!(result.instantiations.len(), GROUND_TERMS);
    assert!(result.deferred.is_empty());
}

#[test]
fn a_universal_behind_an_asserted_guard_has_no_depth_budget() {
    let result = round(true, DERIVED_ENTAILMENT_FREE_GENERATION);
    assert_eq!(result.instantiations.len(), GROUND_TERMS);
    assert!(result.deferred.is_empty());
}

/// Without derivation the guard is not a fact and the universal is not
/// entailed; with it, it is.
#[test]
fn the_harvest_alone_does_not_entail_a_derived_universal() {
    let mut terms = TermStore::new();
    let grp = terms.mk_var("dh_grp", Sort::Bool);
    let g = terms.mk_var("dh_g", Sort::Bool);
    let x = terms.mk_var("x", Sort::Int);
    let p_x = terms.mk_app(Symbol::named("dh_P"), vec![x], Sort::Bool);
    let forall = terms.mk_forall(vec![("x".to_string(), Sort::Int)], p_x);
    let guarded = terms.mk_app(Symbol::named("=>"), [g, forall], Sort::Bool);
    let link = terms.mk_app(Symbol::named("=>"), [grp, g], Sort::Bool);
    let assertions = [guarded, grp, link];
    assert!(entailed_forall_set_deriving(&mut terms, &assertions, true).contains(&forall));
    assert!(!entailed_forall_set_deriving(&mut terms, &assertions, false).contains(&forall));
}

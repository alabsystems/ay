// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Positive coverage for the STORE-OVER-STORE axiom instances: the shape they
//! mint, the exhaustive sweep every accept is re-checked on by the INDEPENDENT
//! bounded array model, and the caps.
//!
//! The evaluator is `array_row_axiom_model_tests` — the campaign's bounded
//! array-model enumerator. `congruence_derivation_sweep_tests::falsifies`
//! cannot serve here: it treats `select`/`store` as UNINTERPRETED, under which
//! the store-over-store identity is not valid at all.

use super::{mint_store_overwrite_axiom, plan_store_overwrite_instances};
use crate::array_row_axiom::model::{
    array, decidable, element, eq, falsify, index, small, store, Alphabet,
};
use crate::quality::check_proof_strict;
use ay_core::{
    AletheRule, Proof, ProofId, ProofStep, Sort, Symbol, TermId, TermStore, TheoryLemmaKind,
};

/// The UNTOUCHED strict checker, on the instance closed into a self-contained
/// refutation — exactly what the lane's Guard 7 runs.
pub(super) fn strict_checks(terms: &mut TermStore, equality: TermId) -> bool {
    let negated = terms.mk_not(equality);
    let mut proof = Proof::new();
    proof.steps.push(ProofStep::TheoryLemma {
        theory: "ArrayEUF".to_string(),
        clause: vec![equality],
        farkas: None,
        kind: TheoryLemmaKind::ArrayRowChain,
        lia: None,
    });
    proof.steps.push(ProofStep::Assume(negated));
    proof.steps.push(ProofStep::Step {
        rule: AletheRule::Resolution,
        clause: Vec::new(),
        premises: vec![ProofId(0), ProofId(1)],
        args: Vec::new(),
    });
    check_proof_strict(&proof, terms).is_ok()
}

/// Every layer of the bar at once, for one minted instance.
pub(super) fn accept(terms: &mut TermStore, shadowed: TermId, value: TermId) -> TermId {
    let equality = mint_store_overwrite_axiom(terms, shadowed, value)
        .expect("this store/value pair must yield an instance");
    assert!(
        decidable(terms, &[equality], &small()),
        "the array model could not interpret the instance, so its silence is not evidence"
    );
    assert!(
        falsify(terms, &[equality], &small()).is_none(),
        "the INDEPENDENT array model falsified an ACCEPTED store-over-store instance"
    );
    assert!(
        strict_checks(terms, equality),
        "the untouched strict checker refused an ACCEPTED instance"
    );
    assert_eq!(
        crate::recognize_array_theory_lemma(terms, &[equality]),
        Some(TheoryLemmaKind::ArrayRowChain),
        "an accepted instance must be classified as the row-chain kind"
    );
    equality
}

fn definition(terms: &mut TermStore, definiendum: TermId, definiens: TermId) -> TermId {
    terms.mk_app(Symbol::named("="), vec![definiendum, definiens], Sort::Bool)
}

#[test]
fn mk_store_folds_the_node_the_closure_needs() {
    // The whole reason the mint must be RAW: the ordinary builder erases the
    // exact node the congruence closure has to merge on.
    let mut terms = TermStore::new();
    let base = array(&mut terms, "a");
    let at = index(&mut terms, "i");
    let shadowed_value = element(&mut terms, "u");
    let value = element(&mut terms, "v");
    let inner = terms.mk_store(base, at, shadowed_value);
    let folded = terms.mk_store(inner, at, value);
    let direct = terms.mk_store(base, at, value);
    assert_eq!(
        folded, direct,
        "mk_store must fold store-over-store at the same index"
    );
}

#[test]
fn the_minted_instance_is_the_exact_overwrite_shape() {
    let mut terms = TermStore::new();
    let base = array(&mut terms, "a");
    let at = index(&mut terms, "i");
    let shadowed_value = element(&mut terms, "u");
    let value = element(&mut terms, "v");
    let shadowed = store(&mut terms, base, at, shadowed_value);
    let equality = accept(&mut terms, shadowed, value);
    assert_eq!(
        crate::format_term_alethe(&terms, equality),
        "(= (store (store a i u) i v) (store a i v))"
    );
}

#[test]
fn the_shadowed_value_may_equal_the_written_value() {
    // The measured population contains this degenerate instance
    // (`(= (store (store a_160 i3 e_161) i3 e_161) (store a_160 i3 e_161))`);
    // it is the same identity and the two sides are still distinct nodes.
    let mut terms = TermStore::new();
    let base = array(&mut terms, "a");
    let at = index(&mut terms, "i");
    let value = element(&mut terms, "v");
    let shadowed = store(&mut terms, base, at, value);
    let equality = accept(&mut terms, shadowed, value);
    assert_eq!(
        crate::format_term_alethe(&terms, equality),
        "(= (store (store a i v) i v) (store a i v))"
    );
}

#[test]
fn the_mirror_orientation_is_accepted_by_the_checker() {
    let mut terms = TermStore::new();
    let base = array(&mut terms, "a");
    let at = index(&mut terms, "i");
    let shadowed_value = element(&mut terms, "u");
    let value = element(&mut terms, "v");
    let shadowed = store(&mut terms, base, at, shadowed_value);
    let overwrite = store(&mut terms, shadowed, at, value);
    let folded = store(&mut terms, base, at, value);
    let mirrored = eq(&mut terms, folded, overwrite);
    assert!(
        decidable(&terms, &[mirrored], &small()),
        "the model must decide the mirrored clause"
    );
    assert!(
        falsify(&terms, &[mirrored], &small()).is_none(),
        "the mirrored identity is equally valid"
    );
    assert_eq!(
        crate::recognize_array_theory_lemma(&terms, &[mirrored]),
        Some(TheoryLemmaKind::ArrayRowChain),
        "equality is symmetric, so both orientations must be accepted"
    );
    assert!(strict_checks(&mut terms, mirrored));
}

#[test]
fn the_sweep_accepts_every_same_index_overwrite_over_a_bounded_alphabet() {
    // Every `(store B i u)` over 2 arrays x 2 indices x 2 elements at depth one
    // AND depth two, crossed with every written value. Each accept is
    // re-checked by the INDEPENDENT array model, by the untouched strict
    // checker, and by the checker's own recognizer.
    let mut terms = TermStore::new();
    let arrays: Vec<TermId> = ["a0", "a1"]
        .iter()
        .map(|name| array(&mut terms, name))
        .collect();
    let indices: Vec<TermId> = ["i0", "i1"]
        .iter()
        .map(|name| index(&mut terms, name))
        .collect();
    let elements: Vec<TermId> = ["e0", "e1"]
        .iter()
        .map(|name| element(&mut terms, name))
        .collect();
    let mut shadowed: Vec<TermId> = Vec::new();
    for &base in &arrays {
        for &at in &indices {
            for &value in &elements {
                shadowed.push(store(&mut terms, base, at, value));
            }
        }
    }
    let depth_one = shadowed.len();
    for position in 0..depth_one {
        let inner = shadowed[position];
        for &at in &indices {
            for &value in &elements {
                shadowed.push(store(&mut terms, inner, at, value));
            }
        }
    }
    let mut accepted = 0usize;
    for position in 0..shadowed.len() {
        let term = shadowed[position];
        for element_position in 0..elements.len() {
            let value = elements[element_position];
            let _ = accept(&mut terms, term, value);
            accepted += 1;
        }
    }
    assert_eq!(
        accepted,
        (8 + 8 * 4) * 2,
        "the sweep must cover every depth-one and depth-two store crossed with every value"
    );
}

#[test]
fn the_sweep_box_contains_refutable_neighbours() {
    // Silence from the enumerator is only evidence when the box can refute
    // something: the DIFFERENT-index overwrite over the same alphabet is
    // refuted, with the witness asserted to separate the two indices.
    let mut terms = TermStore::new();
    let base = array(&mut terms, "a");
    let at = index(&mut terms, "i");
    let other = index(&mut terms, "j");
    let shadowed_value = element(&mut terms, "u");
    let value = element(&mut terms, "v");
    let shadowed = store(&mut terms, base, at, shadowed_value);
    let overwrite = store(&mut terms, shadowed, other, value);
    let folded = store(&mut terms, base, other, value);
    let unsound = eq(&mut terms, overwrite, folded);
    let witness = falsify(&terms, &[unsound], &small())
        .expect("the different-index overwrite must be REFUTABLE in this box");
    let bound = |term: TermId| {
        witness
            .iter()
            .find(|(id, _)| *id == term)
            .map(|(_, value)| value.clone())
            .expect("bound")
    };
    assert_ne!(
        bound(at),
        bound(other),
        "the witness must separate the two index terms"
    );
}

#[test]
fn a_definition_chain_yields_one_instance_per_level() {
    // Three consecutive same-index writes: `c = store(b, i, u2)`,
    // `b = store(a, i, u1)`, and a reachable `store(c, i, v)`. Folding the
    // fully inlined chain needs BOTH levels, and the walk mints both.
    let mut terms = TermStore::new();
    let a = array(&mut terms, "a");
    let b = array(&mut terms, "b");
    let c = array(&mut terms, "c");
    let at = index(&mut terms, "i");
    let u1 = element(&mut terms, "u1");
    let u2 = element(&mut terms, "u2");
    let v = element(&mut terms, "v");
    let b_def_rhs = store(&mut terms, a, at, u1);
    let c_def_rhs = store(&mut terms, b, at, u2);
    let b_def = definition(&mut terms, b, b_def_rhs);
    let c_def = definition(&mut terms, c, c_def_rhs);
    let root = store(&mut terms, c, at, v);
    let minted = plan_store_overwrite_instances(&mut terms, &[b_def, c_def], &[root]);
    let printed: Vec<String> = minted
        .iter()
        .map(|&term| crate::format_term_alethe(&terms, term))
        .collect();
    assert_eq!(
        printed,
        vec![
            "(= (store (store b i u2) i v) (store b i v))".to_string(),
            "(= (store (store a i u1) i v) (store a i v))".to_string(),
        ],
        "the walk must mint one instance per definition level"
    );
    for &instance in &minted {
        assert!(decidable(&terms, &[instance], &small()));
        assert!(falsify(&terms, &[instance], &small()).is_none());
        assert!(strict_checks(&mut terms, instance));
    }
}

#[test]
fn a_definition_at_a_different_index_mints_nothing() {
    // `mk_store` leaves a write at a DIFFERENT index in place, so there is no
    // fold to bridge and the walk must produce no instance at all.
    let mut terms = TermStore::new();
    let a = array(&mut terms, "a");
    let b = array(&mut terms, "b");
    let at = index(&mut terms, "i");
    let other = index(&mut terms, "j");
    let u = element(&mut terms, "u");
    let v = element(&mut terms, "v");
    let b_def_rhs = store(&mut terms, a, other, u);
    let b_def = definition(&mut terms, b, b_def_rhs);
    let root = store(&mut terms, b, at, v);
    assert!(plan_store_overwrite_instances(&mut terms, &[b_def], &[root]).is_empty());
}

#[test]
fn the_instance_count_is_capped() {
    let mut terms = TermStore::new();
    let at = index(&mut terms, "i");
    let value = element(&mut terms, "v");
    let mut definitions: Vec<TermId> = Vec::new();
    let mut roots: Vec<TermId> = Vec::new();
    // 300 independent one-level definitions, each supplying one instance.
    for position in 0..300u32 {
        let base = array(&mut terms, &format!("a{position}"));
        let named = array(&mut terms, &format!("d{position}"));
        let shadow = element(&mut terms, &format!("u{position}"));
        let rhs = store(&mut terms, base, at, shadow);
        definitions.push(definition(&mut terms, named, rhs));
        roots.push(store(&mut terms, named, at, value));
    }
    let minted = plan_store_overwrite_instances(&mut terms, &definitions, &roots);
    assert_eq!(minted.len(), super::MAX_STORE_OVERWRITE_INSTANCES);
}

#[test]
fn a_wider_alphabet_still_finds_no_countermodel() {
    // The identity is a validity, so widening the box must not change the
    // answer; this also proves the two-index box was not accidentally too
    // small to express the difference.
    let mut terms = TermStore::new();
    let base = array(&mut terms, "a");
    let at = index(&mut terms, "i");
    let shadowed_value = element(&mut terms, "u");
    let value = element(&mut terms, "v");
    let shadowed = store(&mut terms, base, at, shadowed_value);
    let equality =
        mint_store_overwrite_axiom(&mut terms, shadowed, value).expect("instance must mint");
    let wide = Alphabet {
        indices: 3,
        elements: 3,
    };
    assert!(decidable(&terms, &[equality], &wide));
    assert!(falsify(&terms, &[equality], &wide).is_none());
}

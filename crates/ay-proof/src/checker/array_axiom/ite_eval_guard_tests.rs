// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The GUARD MUTATION LEDGER for sub-schema (K), the METER, and the WIRE.
//!
//! # `GUARD_MUTATION_LEDGER`
//!
//! Every guard in [`super::ite_eval`] was deleted or inverted one at a time and
//! the WHOLE `ay-proof` lib suite re-run UNFILTERED (1809 tests in round 1), so
//! no mutation can come back green because the test naming it was filtered out.
//! Guards backstop each other, so every green was re-run PAIRED with the guard
//! that backstops it and — where the pair was still green — a DIRECT two-sided
//! pin was written for the backstop and the mutation re-run against it. Three rounds over 19 guards: **16 observable, 3 honest greens.** The
//! per-guard table is in the `ay-asks` note; here: 13 RED ALONE, 2 RED
//! once this file's pins existed (the premise's shared array sort; the
//! pre-flatten Bool literal check), 1 RED only deleted in a PAIR (the read
//! index's sort shares a source line with the other-root check), and 3 HONEST
//! GREENS pinned directly below — the Bool-fold sort gate (redundant with
//! `equality_sides`' own Bool requirement), the const-array fill's sort check
//! (UNFALSIFIABLE BY CONSTRUCTION: `mk_const_array` derives the element sort
//! FROM the fill and `mk_ite_raw` refuses mismatched branches), and the
//! conclusion's element-sort check (redundant with `well_sorted_select_parts`
//! and both walk terminators, the second of which is RED on its own account).
//!
//! # The meter
//!
//! `ArrayRowChain` takes a `(0, 0)` semantic precharge and debits its ACTUAL
//! work through the strict-check progress callback, so (K)'s eight chain walks
//! have to be charged inside `charge_row_chain_validation` or they are free.
//! [`the_k_walk_is_charged_before_the_schema_search_runs`] pins that the charge
//! happens BEFORE the search (an exhausted budget yields `ResourceLimit`, not an
//! acceptance), and [`an_adversarial_store_spine_fails_closed`] pins that a long
//! spine is refused rather than walked.
//!
//! # The wire
//!
//! A (K) clause is NOT one of the shapes
//! `crate::checker::array_row_chain_printer_terms` can lower compositionally, so
//! the printer must fall through to the honest, externally uncheckable wire name
//! rather than fabricate an `arrays_row`/`arrays_idx`/`trans` derivation the
//! printed clause does not license.
//! [`the_k_lemma_prints_an_honest_hole_and_never_a_fabricated_derivation`] pins
//! the exact wire text.

use super::ite_eval_fixture::*;
use super::recognize_array_row_chain_ite_eval;
use crate::quality::check_proof_strict_with_context_and_progress;
use ay_core::{AletheRule, Proof, ProofId, ProofStep, Sort, TermId, TermStore, TheoryLemmaKind};

/// The corpus clause, plus the pieces a caller needs to re-assemble it.
struct Fixture {
    terms: TermStore,
    clause: Vec<TermId>,
}

/// `(cl (not (= E (store (const false) i true))) (= (select E j) (= i j)))` —
/// the measured corpus shape, built exactly as `ite_eval_tests` builds it.
fn corpus_clause() -> Fixture {
    let mut terms = TermStore::new();
    let falsity = terms.false_term();
    let truth = terms.true_term();
    let base = terms.mk_const_array(index_sort(), falsity);
    let i = terms.mk_var("i", index_sort());
    let j = terms.mk_var("j", index_sort());
    let root = terms.mk_var("E", array_sort(Sort::Bool));
    let chain = store(&mut terms, base, i, truth);
    let value = producer_value(&mut terms, chain, j);
    let (clause, _) = assemble(&mut terms, root, chain, j, value, Spelling::plain());
    assert!(
        recognize_array_row_chain_ite_eval(&terms, &clause),
        "the ledger's baseline clause must be accepted"
    );
    Fixture { terms, clause }
}

/// A chain of `depth` writes at distinct symbolic indices over a variable base,
/// with the producer's own value side. The single knob an adversarial bundle has.
fn deep_chain(depth: usize) -> Fixture {
    let mut terms = TermStore::new();
    let arrays = array_sort(element_sort());
    let root = terms.mk_var("E", arrays.clone());
    let mut chain = terms.mk_var("a", arrays);
    let j = terms.mk_var("j", index_sort());
    for k in 0..depth {
        let at = terms.mk_var(format!("i{k}"), index_sort());
        let value = terms.mk_var(format!("v{k}"), element_sort());
        chain = store(&mut terms, chain, at, value);
    }
    let value = producer_value(&mut terms, chain, j);
    let (clause, _) = assemble(&mut terms, root, chain, j, value, Spelling::plain());
    Fixture { terms, clause }
}

/// The lemma closed into a self-contained refutation, so the whole-proof strict
/// checker runs the lemma's own validator with the caller's meter.
fn closed_refutation(fixture: &mut Fixture) -> Proof {
    let negations: Vec<TermId> = fixture
        .clause
        .iter()
        .map(|&lit| fixture.terms.mk_not_raw(lit))
        .collect();
    let mut proof = Proof::new();
    proof.steps.push(ProofStep::TheoryLemma {
        theory: "arrays".to_string(),
        clause: fixture.clause.clone(),
        farkas: None,
        kind: TheoryLemmaKind::ArrayRowChain,
        lia: None,
    });
    let mut premises = vec![ProofId(0)];
    for (position, negated) in negations.into_iter().enumerate() {
        proof.steps.push(ProofStep::Assume(negated));
        premises.push(ProofId(u32::try_from(position + 1).expect("small fixture")));
    }
    proof.steps.push(ProofStep::Step {
        rule: AletheRule::Resolution,
        clause: Vec::new(),
        premises,
        args: Vec::new(),
    });
    proof
}

/// Run the strict checker with a work budget, returning `(result, work spent)`.
fn strict_under_budget(
    fixture: &mut Fixture,
    budget: usize,
) -> (Result<(), crate::ProofCheckError>, usize) {
    let proof = closed_refutation(fixture);
    let mut spent = 0usize;
    let outcome = check_proof_strict_with_context_and_progress(
        &proof,
        &fixture.terms,
        None,
        None,
        None,
        &mut |work, _bytes| {
            spent += work;
            spent <= budget
        },
    );
    (outcome.map(|_| ()), spent)
}

#[test]
fn the_k_walk_is_charged_before_the_schema_search_runs() {
    // Unbounded: the lemma is accepted and the meter records the work.
    let mut fixture = corpus_clause();
    let (outcome, spent) = strict_under_budget(&mut fixture, usize::MAX);
    assert!(
        outcome.is_ok(),
        "the closed (K) refutation must check strictly: {outcome:?}"
    );
    assert!(spent > 0, "the row-chain validator must debit its walk");

    // The SAME clause under a budget one unit short of what it spends is
    // refused with `ResourceLimit` — so the charge is taken BEFORE the schema
    // search decides, and an accept can never be obtained for free.
    let mut fixture = corpus_clause();
    let (outcome, _) = strict_under_budget(&mut fixture, spent - 1);
    assert!(
        matches!(outcome, Err(crate::ProofCheckError::ResourceLimit)),
        "an exhausted budget must fail closed, not accept: {outcome:?}"
    );
}

#[test]
fn an_adversarial_store_spine_fails_closed() {
    // The (K) charge is `12 * n_max * 64`, so the work a clause debits must GROW
    // with the spine an adversarial bundle can hand the checker. Both depths are
    // accepted when the budget is unbounded; the deeper one costs strictly more,
    // which is what "the walk is priced per node" means operationally.
    let mut shallow = deep_chain(2);
    let mut deep = deep_chain(24);
    let (shallow_outcome, shallow_spent) = strict_under_budget(&mut shallow, usize::MAX);
    let (deep_outcome, deep_spent) = strict_under_budget(&mut deep, usize::MAX);
    assert!(shallow_outcome.is_ok(), "{shallow_outcome:?}");
    assert!(deep_outcome.is_ok(), "{deep_outcome:?}");
    assert!(
        deep_spent > shallow_spent,
        "a 24-store spine must cost more than a 2-store spine ({deep_spent} vs {shallow_spent})"
    );

    // And the deep clause is REFUSED under the shallow clause's budget rather
    // than walked for free.
    let mut deep = deep_chain(24);
    let (outcome, _) = strict_under_budget(&mut deep, shallow_spent);
    assert!(
        matches!(outcome, Err(crate::ProofCheckError::ResourceLimit)),
        "the deep spine must fail closed under the shallow budget: {outcome:?}"
    );
}

#[test]
fn the_k_lemma_prints_an_honest_hole_and_never_a_fabricated_derivation() {
    let mut fixture = corpus_clause();
    let proof = closed_refutation(&mut fixture);
    let wire = crate::try_export_alethe(&proof, &fixture.terms).expect("the (K) proof must print");

    // The compositional `arrays_row`/`arrays_idx`/`trans` lowering is for the
    // sub-schemas whose walk the printer can replay from the PRINTED surface.
    // (K)'s case split lives inside an `ite`, which that lowering cannot
    // reconstruct, so it must decline — and declining means an honest `hole`,
    // never a derivation the printed clause does not license.
    for fabricated in [
        "arrays_row",
        "arrays_idx",
        "arrays_ext",
        "read_over_write_chain",
    ] {
        assert!(
            !wire.contains(fabricated),
            "the printer must not claim `{fabricated}` for a (K) clause:\n{wire}"
        );
    }
    assert_eq!(
        wire.matches(":rule hole").count(),
        1,
        "exactly the (K) lemma prints as a hole:\n{wire}"
    );
    assert!(
        wire.contains(
            "(step t0 (cl (not (= E (store ((as const (Array Index Bool)) false) i true))) \
             (= (select E j) (= i j))) :rule hole)"
        ),
        "the exact (K) wire line moved:\n{wire}"
    );
    // …and the rest of the document is the fixture'"'"'s own closure, pinned so a
    // future change that started emitting extra steps is visible here.
    assert!(
        wire.contains("(step t3 (cl) :rule resolution :premises (t0 t1 t2))"),
        "{wire}"
    );
}

#[test]
fn the_declined_neighbour_is_not_promoted_by_the_printer_either() {
    // The extensionality direction — `(cl (= E C) (not (= (select E j) V)))` —
    // is REFUTABLE (`ite_eval_negative_tests`) and (K) declines it. Labelling it
    // `ArrayRowChain` anyway must be refused by the strict checker, so the
    // decline is not merely a missed opportunity but a closed door.
    let mut terms = TermStore::new();
    let falsity = terms.false_term();
    let truth = terms.true_term();
    let base = terms.mk_const_array(index_sort(), falsity);
    let i = terms.mk_var("i", index_sort());
    let j = terms.mk_var("j", index_sort());
    let root = terms.mk_var("E", array_sort(Sort::Bool));
    let chain = store(&mut terms, base, i, truth);
    let value = producer_value(&mut terms, chain, j);
    let premise = eq(&mut terms, root, chain);
    let read = select(&mut terms, root, j);
    let conclusion_eq = eq(&mut terms, read, value);
    let conclusion = terms.mk_not(conclusion_eq);
    let mut fixture = Fixture {
        terms,
        clause: vec![premise, conclusion],
    };
    assert!(!recognize_array_row_chain_ite_eval(
        &fixture.terms,
        &fixture.clause
    ));
    let (outcome, _) = strict_under_budget(&mut fixture, usize::MAX);
    assert!(
        matches!(
            outcome,
            Err(crate::ProofCheckError::InvalidTheoryLemma { .. })
        ),
        "the strict checker must refuse the extensionality direction: {outcome:?}"
    );
}

// ==========================================================================
// DIRECT, TWO-SIDED pins for the guards whose deletion the first ledger round
// could not observe. A guard that survives a mutation is not evidence-free —
// it is BACKSTOPPED, and a backstop that is never pinned is the thing a future
// change silently removes. Each test below is a complete refutation of the
// clause it names: the schema declines it, and the reason it must is stated.
// ==========================================================================

/// Ledger G2 — the Bool-fold arms are guarded on `Sort::Bool`.
///
/// An `(Array Index Element)` chain whose value side is a Bool-sorted `(= i j)`
/// reaches the fold arms only if the sort gate lets it. It must DECLINE either
/// way: the entry's stored value is `Element`-sorted, and a `BoolConst`
/// denotation can only ever be an actual `Const(Bool(_))`.
#[test]
fn a_bool_shaped_value_side_over_a_non_bool_chain_is_declined() {
    let mut terms = TermStore::new();
    let base = terms.mk_var("a", array_sort(element_sort()));
    let i = terms.mk_var("i", index_sort());
    let j = terms.mk_var("j", index_sort());
    let v = terms.mk_var("v", element_sort());
    let root = terms.mk_var("E", array_sort(element_sort()));
    let chain = store(&mut terms, base, i, v);
    let value = eq(&mut terms, i, j);
    let read = select(&mut terms, root, j);
    let premise_eq = eq(&mut terms, root, chain);
    let premise = terms.mk_not(premise_eq);
    let conclusion = eq(&mut terms, read, value);
    assert_ne!(
        terms.sort(read),
        terms.sort(value),
        "the fixture is only meaningful while the two sides differ in sort"
    );
    assert!(
        !recognize_array_row_chain_ite_eval(&terms, &[premise, conclusion]),
        "a Bool-sorted value side over an Element-sorted chain must be declined"
    );
}

/// Ledger G9 — the const-array fill must carry the base's ELEMENT sort.
///
/// `mk_const_array` DERIVES the element sort from the fill, and `mk_ite_raw`
/// refuses branches of different sorts, so the only way to present a mismatch
/// is a RAW `const-array` application whose operand disagrees with its declared
/// array sort. That is what this builds. The clause is ILL-SORTED — the base
/// claims to hold `Element` and holds an `Index` — so this is a DECLINE
/// assertion and says so, rather than reading a model's silence as evidence.
#[test]
fn a_const_array_whose_fill_is_not_element_sorted_is_declined() {
    let mut terms = TermStore::new();
    let fill = terms.mk_var("bogus", index_sort());
    let base = terms.mk_app(
        ay_core::Symbol::named("const-array"),
        vec![fill],
        array_sort(element_sort()),
    );
    let i = terms.mk_var("i", index_sort());
    let j = terms.mk_var("j", index_sort());
    let v = terms.mk_var("v", element_sort());
    let root = terms.mk_var("E", array_sort(element_sort()));
    let chain = store(&mut terms, base, i, v);
    let base_read = select(&mut terms, base, j);
    let condition = eq(&mut terms, i, j);
    let value = terms.mk_ite_raw(condition, v, base_read);
    let read = select(&mut terms, root, j);
    let premise_eq = eq(&mut terms, root, chain);
    let premise = terms.mk_not(premise_eq);
    let conclusion = eq(&mut terms, read, value);
    assert!(
        terms.get_const_array(base).is_some(),
        "the fixture is only meaningful while the base parses as a const array"
    );
    assert!(
        !recognize_array_row_chain_ite_eval(&terms, &[premise, conclusion]),
        "an ill-sorted const-array fill must be declined"
    );
}

/// Ledger G14/G15 — the premise's two sides must have the SAME array sort.
///
/// The soundness argument starts from `E = C`, which is meaningless when the
/// two sides are arrays over different index sorts. This clause is built so
/// that every OTHER check passes — the read is of the root at a root-sorted
/// index, the chain parses, the fold decodes, and the walk terminates on a
/// const-array whose fill is element-sorted — so nothing but the premise's own
/// sort equality stands between the schema and an ill-sorted accept.
#[test]
fn a_premise_equating_arrays_of_different_sorts_is_declined() {
    let mut terms = TermStore::new();
    let other_index = Sort::Uninterpreted("OtherIndex".to_string());
    let root = terms.mk_var("E", array_sort(element_sort()));
    let fill = terms.mk_var("fill", element_sort());
    let base = terms.mk_const_array(other_index.clone(), fill);
    let foreign = terms.mk_var("i2", other_index);
    let j = terms.mk_var("j", index_sort());
    let v = terms.mk_var("v", element_sort());
    let chain = {
        let sort = terms.sort(base).clone();
        terms.mk_app(
            ay_core::Symbol::named("store"),
            vec![base, foreign, v],
            sort,
        )
    };
    assert_ne!(
        terms.sort(chain),
        terms.sort(root),
        "the fixture is only meaningful while the premise's sides differ in sort"
    );
    let condition = eq(&mut terms, foreign, j);
    let value = terms.mk_ite_raw(condition, v, fill);
    let read = select(&mut terms, root, j);
    let premise_eq = eq(&mut terms, root, chain);
    let premise = terms.mk_not(premise_eq);
    let conclusion = eq(&mut terms, read, value);
    assert!(
        !recognize_array_row_chain_ite_eval(&terms, &[premise, conclusion]),
        "an array equality between different array sorts must be declined"
    );
}

/// Ledger G18 — the read index must carry the array's INDEX sort.
///
/// Pinned directly: a RAW `(select E v)` whose index operand is element-sorted
/// is refused, whichever check gets there first.
#[test]
fn a_read_whose_index_operand_is_ill_sorted_is_declined() {
    let mut terms = TermStore::new();
    let base = terms.mk_var("a", array_sort(element_sort()));
    let i = terms.mk_var("i", index_sort());
    let v = terms.mk_var("v", element_sort());
    let root = terms.mk_var("E", array_sort(element_sort()));
    let chain = store(&mut terms, base, i, v);
    let read = terms.mk_app(
        ay_core::Symbol::named("select"),
        vec![root, v],
        element_sort(),
    );
    let base_read = terms.mk_app(
        ay_core::Symbol::named("select"),
        vec![base, v],
        element_sort(),
    );
    let condition = eq(&mut terms, i, v);
    let value = terms.mk_ite_raw(condition, v, base_read);
    let premise_eq = eq(&mut terms, root, chain);
    let premise = terms.mk_not(premise_eq);
    let conclusion = eq(&mut terms, read, value);
    assert!(
        !recognize_array_row_chain_ite_eval(&terms, &[premise, conclusion]),
        "a select whose index operand is element-sorted must be declined"
    );
}

/// Ledger G19 — every clause literal must be Bool-sorted, checked BEFORE the
/// packed `(cl (or ..))` literal is flattened.
///
/// The load-bearing case is a PACKED clause whose `or` application is declared
/// at a non-Bool sort. Flattening it yields two perfectly Bool literals that
/// the schema would otherwise accept — and the strict checker's own
/// `reject_non_bool_literals` then refuses the lemma outright, converting a
/// RESCUABLE `trust` rejection into a hard `InvalidTheoryLemma` one. That is
/// the exact failure mode the intrinsic battery must never create, so the
/// recognizer has to decline first.
///
/// TWO-SIDED: the well-sorted packing is accepted, the ill-sorted packing is
/// declined by the recognizer, and the checker is shown refusing it for the
/// stated reason.
#[test]
fn a_packed_clause_declared_at_a_non_bool_sort_is_declined_before_flattening() {
    let mut fixture = corpus_clause();
    let [premise, conclusion] = fixture.clause[..] else {
        panic!("the baseline clause is the two-literal spelling");
    };
    let honest = fixture.terms.mk_app(
        ay_core::Symbol::named("or"),
        vec![premise, conclusion],
        Sort::Bool,
    );
    assert!(
        recognize_array_row_chain_ite_eval(&fixture.terms, &[honest]),
        "the well-sorted packing is the accepted baseline"
    );
    let ill_sorted = fixture.terms.mk_app(
        ay_core::Symbol::named("or"),
        vec![premise, conclusion],
        index_sort(),
    );
    assert!(
        !recognize_array_row_chain_ite_eval(&fixture.terms, &[ill_sorted]),
        "a packed clause declared at a non-Bool sort must be declined"
    );
    let forced = Fixture {
        terms: fixture.terms,
        clause: vec![ill_sorted],
    };
    let proof = {
        let mut proof = Proof::new();
        proof.steps.push(ProofStep::TheoryLemma {
            theory: "arrays".to_string(),
            clause: forced.clause.clone(),
            farkas: None,
            kind: TheoryLemmaKind::ArrayRowChain,
            lia: None,
        });
        proof
    };
    let outcome = check_proof_strict_with_context_and_progress(
        &proof,
        &forced.terms,
        None,
        None,
        None,
        &mut |_, _| true,
    );
    let Err(crate::ProofCheckError::InvalidTheoryLemma { reason, .. }) = outcome else {
        panic!("the strict checker must refuse the ill-sorted packing: {outcome:?}");
    };
    assert!(
        reason.contains("non-Bool"),
        "and it must refuse it FOR that reason: {reason}"
    );
    // Keep the forced fixture live through the rejection check and confirm its
    // clause was not consumed or rewritten on the fail-closed path.
    assert_eq!(forced.clause.len(), 1);
}

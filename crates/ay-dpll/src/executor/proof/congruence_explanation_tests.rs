// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the congruence-explanation lowering lane.
//!
//! The pass places no authority of its own — it names rules the strict checker
//! then re-runs — so the headline test is DIFFERENTIAL on the WIRE: a complete
//! refutation that the untouched strict checker accepts BOTH ways, whose
//! exported document carries `:rule hole` before the pass and none after.
//!
//! `GUARD_MUTATION_LEDGER` — each guard deleted or weakened, `ay-dpll --lib`
//! re-run, the named test OBSERVED failing, then restored. Run recorded
//! 2026-08-22 with the harness driving one mutation at a time:
//!
//! | guard | mutation | test observed failing | class |
//! |---|---|---|---|
//! | no anchors | delete the check | `a_proof_carrying_an_anchor_is_left_alone` | RED — fail-closed (remap) |
//! | payload-free `EufCongruenceExplanation` | accept a `farkas`/`lia` payload | `a_lemma_that_still_carries_a_farkas_payload_is_left_alone` | RED — soundness (split authority) |
//! | packed consumer is `AletheRule::Or` | accept any consumer rule | `a_packed_leaf_whose_consumer_is_not_an_or_step_is_repacked_in_place` | RED — the FLAT arm's precondition |
//! | packed consumer clause `== children` | drop the comparison | `a_consumer_whose_clause_is_not_the_flattened_children_is_repacked_in_place` | RED — the FLAT arm's precondition |
//! | exactly one packed consumer | take the FIRST reference | `a_packed_leaf_with_a_second_consumer_is_repacked_in_place` | RED — the FLAT arm's precondition |
//! | RE-PACK width cap | raise `MAX_REPACK_DISJUNCTS` | `a_packed_leaf_wider_than_the_repack_cap_is_left_alone` | RED — scope, fail-closed |
//! | RE-PACK ends on the lemma's own clause | drop the final equality check | `a_repacked_fragment_prints_or_neg_on_the_wire` | RED — consumer safety |
//!
//! **The three `or`-consumer entries changed meaning on 2026-08-22 and the
//! change is recorded here rather than hidden.** They used to pin
//! "left alone"; a packed leaf whose consumer is not the single matching `or`
//! step is now handled by a SECOND arm that rebuilds the packed unit instead
//! of flattening it, so the leaf's clause is byte-identical and no consumer is
//! touched at all. Each mutation still turns its named test RED — it now
//! routes a leaf into the FLAT arm, whose rewrite of the `or` consumer those
//! tests' fixtures cannot survive. The property the old names claimed is
//! pinned directly by `repacked`, which checks the byte-identical leaf clause,
//! every consumer's rule and clause, and `check_proof` on the rebuilt proof.
//! | the fragment RENDERS under the export's overrides | delete the check | `a_lemma_whose_congruence_step_the_printer_refuses_is_left_alone` | RED — publication |
//! | no unrenderable surface override | return `false` | `a_transitivity_only_derivation_with_an_unrenderable_hypothesis_is_left_alone` | RED — external validity |
//! | certification-preserving revert | delete the disjunct | `a_rewrite_that_would_cost_a_certification_is_reverted` | RED — verdict preservation |
//!
//! Three NEGATIVES, recorded rather than hidden:
//!
//! * **`consumer > index`** — deleting it fails no test, and cannot: a premise
//!   reference in a well-formed proof is always to an EARLIER step, so the
//!   condition is unreachable. It stays as a fail-fast structural assertion.
//! * **the closed-fragment strict check** — deleting it fails no test, because
//!   the only clause in these fixtures that the checker would refuse is one
//!   the PLANNER already declines. No test can exercise this gate without an
//!   emitter bug to exercise it with; what pins the agreement is
//!   `congruence_derivation_sweep_tests`, which strict-checks the fragment of
//!   EVERY accept over three bounded alphabets (2 528 of them) and has never
//!   seen the two disagree. It is the lane's whole authority and stays.
//! * **the whole-proof `check_proof` backstop** — deleting it fails no test in
//!   the crate, because every fragment is already strict-checked in isolation
//!   and the splice preserves every other step. Recorded as a BACKSTOP.
//!
//! One METHODOLOGICAL negative, recorded because it invalidated an earlier run
//! of this table: with TRUNCATED fixtures (a lemma and its consumer, with no
//! refutation around them) EIGHT of these mutations were green — the backstop
//! reverted them for the unrelated reason that the proof does not end in the
//! empty clause. Every fixture here is a complete refutation for that reason.

use super::*;

use ay_core::{Sort, Symbol, TermId};

/// `f(a)`, `f(b)` and `a = b` over one uninterpreted sort: the smallest clause
/// whose explanation needs a CONGRUENCE step, which is exactly the link
/// `eq_transitive` cannot supply.
pub(super) struct Congruence {
    eq_ab: TermId,
    not_ab: TermId,
    eq_fab: TermId,
    not_fab: TermId,
}

pub(super) fn congruence(executor: &mut Executor, tag: &str) -> Congruence {
    let sort = Sort::Uninterpreted("EufSort".to_string());
    let a = executor.ctx.terms.mk_var(format!("{tag}_a"), sort.clone());
    let b = executor.ctx.terms.mk_var(format!("{tag}_b"), sort.clone());
    let fa = executor
        .ctx
        .terms
        .mk_app(Symbol::named("f"), vec![a], sort.clone());
    let fb = executor.ctx.terms.mk_app(Symbol::named("f"), vec![b], sort);
    let eq_ab = executor.ctx.terms.mk_eq(a, b);
    let eq_fab = executor.ctx.terms.mk_eq(fa, fb);
    let not_ab = executor.ctx.terms.mk_not_raw(eq_ab);
    let not_fab = executor.ctx.terms.mk_not_raw(eq_fab);
    Congruence {
        eq_ab,
        not_ab,
        eq_fab,
        not_fab,
    }
}

fn or_term(executor: &mut Executor, literals: Vec<TermId>) -> TermId {
    executor
        .ctx
        .terms
        .mk_app(Symbol::named("or"), literals, Sort::Bool)
}

fn explanation_lemma(clause: Vec<TermId>) -> ProofStep {
    ProofStep::TheoryLemma {
        theory: "EUF".to_string(),
        clause,
        farkas: None,
        kind: TheoryLemmaKind::EufCongruenceExplanation,
        lia: None,
    }
}

fn or_step(clause: Vec<TermId>, premise: u32) -> ProofStep {
    ProofStep::Step {
        rule: AletheRule::Or,
        clause,
        premises: vec![ProofId(premise)],
        args: Vec::new(),
    }
}

/// A complete refutation of `a = b ∧ f(a) ≠ f(b)` whose congruence step is the
/// packed explanation leaf plus its `or` consumer.
fn packed_refutation(executor: &mut Executor, link: &Congruence) -> (Proof, Vec<TermId>) {
    let flat = vec![link.not_ab, link.eq_fab];
    let packed = or_term(executor, flat.clone());
    let mut proof = Proof::new();
    proof.add_step(ProofStep::Assume(link.eq_ab)); // t0
    proof.add_step(ProofStep::Assume(link.not_fab)); // t1
    proof.add_step(explanation_lemma(vec![packed])); // t2
    proof.add_step(or_step(flat.clone(), 2)); // t3
    proof.add_step(ProofStep::Resolution {
        clause: vec![link.eq_fab],
        pivot: link.eq_ab,
        clause1: ProofId(3),
        clause2: ProofId(0),
    }); // t4
    proof.add_step(ProofStep::Resolution {
        clause: Vec::new(),
        pivot: link.eq_fab,
        clause1: ProofId(4),
        clause2: ProofId(1),
    }); // t5
    (proof, flat)
}

fn rules(proof: &Proof) -> Vec<String> {
    proof
        .steps
        .iter()
        .map(|step| match step {
            ProofStep::Step { rule, .. } => rule.name().to_string(),
            ProofStep::TheoryLemma { kind, .. } => kind.alethe_rule().to_string(),
            ProofStep::Assume(_) => "assume".to_string(),
            _ => "resolution".to_string(),
        })
        .collect()
}

// ==========================================================================
// 1. The gap, and the differential proof that it closes
// ==========================================================================

/// PRECONDITION, measured rather than assumed: the certified lemma's WIRE form
/// is `hole`, so an external checker learns nothing from it.
#[test]
fn the_certified_kind_still_lowers_to_hole() {
    assert_eq!(
        ay_core::wire_rule_name(TheoryLemmaKind::EufCongruenceExplanation.alethe_rule()),
        "hole"
    );
    assert!(!ay_core::is_checkable_alethe_rule(
        "euf_congruence_explanation"
    ));
}

/// THE HEADLINE. The strict checker accepts the refutation BOTH ways — the
/// lemma was already certified — but the exported DOCUMENT goes from carrying
/// a `hole` to carrying only externally checkable rules.
#[test]
fn a_certified_explanation_becomes_an_externally_checkable_derivation() {
    let mut executor = Executor::new();
    let link = congruence(&mut executor, "wire");
    let (mut proof, flat) = packed_refutation(&mut executor, &link);

    ay_proof::check_proof_strict(&proof, &executor.ctx.terms)
        .expect("precondition: the certified lemma already makes this proof strict-VALID");
    let before = ay_proof::export_alethe(&proof, &executor.ctx.terms);
    assert!(
        before.contains(":rule hole"),
        "precondition: the lemma must print as a hole — {before}"
    );

    assert_eq!(executor.derive_congruence_explanations(&mut proof), 1);

    ay_proof::check_proof_strict(&proof, &executor.ctx.terms)
        .expect("the UNTOUCHED strict checker must still accept the rewritten refutation");
    let after = ay_proof::export_alethe(&proof, &executor.ctx.terms);
    assert!(!after.contains(":rule hole"), "{after}");
    assert!(!after.contains(":rule trust"), "{after}");
    assert!(after.contains(":rule eq_congruent"), "{after}");
    assert!(after.contains(":rule reordering"), "{after}");
    // Every rule the document now names is one the pinned checker implements.
    for line in after.lines() {
        if let Some(rest) = line.split(":rule ").nth(1) {
            let name = rest
                .split_whitespace()
                .next()
                .unwrap_or_default()
                .trim_end_matches(')');
            assert!(
                ay_core::is_checkable_alethe_rule(name),
                "{name} is not externally checkable — {line}"
            );
        }
    }
    // The consumer keeps its clause byte-for-byte; only its justification
    // changes, so every downstream pivot still sees what it saw.
    match proof.steps.iter().find(|step| {
        matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::Reordering,
                ..
            }
        )
    }) {
        Some(ProofStep::Step { clause, .. }) => assert_eq!(clause, &flat),
        other => panic!("expected a reordering consumer, got {other:?}"),
    }
}

/// The FLAT recorded form needs no consumer rewrite at all.
#[test]
fn a_flat_explanation_lemma_is_replaced_in_place() {
    let mut executor = Executor::new();
    let link = congruence(&mut executor, "flat");
    let mut proof = Proof::new();
    proof.add_step(ProofStep::Assume(link.eq_ab)); // t0
    proof.add_step(ProofStep::Assume(link.not_fab)); // t1
    proof.add_step(explanation_lemma(vec![link.not_ab, link.eq_fab])); // t2
    proof.add_step(ProofStep::Resolution {
        clause: vec![link.eq_fab],
        pivot: link.eq_ab,
        clause1: ProofId(2),
        clause2: ProofId(0),
    }); // t3
    proof.add_step(ProofStep::Resolution {
        clause: Vec::new(),
        pivot: link.eq_fab,
        clause1: ProofId(3),
        clause2: ProofId(1),
    }); // t4

    assert_eq!(executor.derive_congruence_explanations(&mut proof), 1);
    assert_eq!(
        rules(&proof),
        vec![
            "assume".to_string(),
            "assume".to_string(),
            "eq_congruent".to_string(),
            "resolution".to_string(),
            "resolution".to_string(),
        ],
        "the lemma becomes one eq_congruent step and the resolutions are remapped onto it"
    );
    ay_proof::check_proof_strict(&proof, &executor.ctx.terms)
        .expect("the rewritten refutation must strict-check");
}

/// A downstream premise reference must follow the lemma to the LAST step of
/// its fragment, whatever the fragment's length.
#[test]
fn downstream_premises_are_remapped_onto_the_fragments_last_step() {
    let mut executor = Executor::new();
    let sort = Sort::Uninterpreted("EufSort".to_string());
    let a = executor.ctx.terms.mk_var("nest_a", sort.clone());
    let b = executor.ctx.terms.mk_var("nest_b", sort.clone());
    let ga = executor
        .ctx
        .terms
        .mk_app(Symbol::named("g"), vec![a], sort.clone());
    let gb = executor
        .ctx
        .terms
        .mk_app(Symbol::named("g"), vec![b], sort.clone());
    let fga = executor
        .ctx
        .terms
        .mk_app(Symbol::named("f"), vec![ga], sort.clone());
    let fgb = executor
        .ctx
        .terms
        .mk_app(Symbol::named("f"), vec![gb], sort);
    let eq_ab = executor.ctx.terms.mk_eq(a, b);
    let not_ab = executor.ctx.terms.mk_not_raw(eq_ab);
    let eq_f = executor.ctx.terms.mk_eq(fga, fgb);
    let not_f = executor.ctx.terms.mk_not_raw(eq_f);
    let mut proof = Proof::new();
    proof.add_step(ProofStep::Assume(eq_ab)); // t0
    proof.add_step(ProofStep::Assume(not_f)); // t1
    proof.add_step(explanation_lemma(vec![not_ab, eq_f])); // t2
    proof.add_step(ProofStep::Resolution {
        clause: vec![eq_f],
        pivot: eq_ab,
        clause1: ProofId(2),
        clause2: ProofId(0),
    }); // t3
    proof.add_step(ProofStep::Resolution {
        clause: Vec::new(),
        pivot: eq_f,
        clause1: ProofId(3),
        clause2: ProofId(1),
    }); // t4

    assert_eq!(executor.derive_congruence_explanations(&mut proof), 1);
    assert!(
        proof.steps.len() > 5,
        "the nested congruence needs more than one step"
    );
    ay_proof::check_proof_strict(&proof, &executor.ctx.terms)
        .expect("the remapped refutation must strict-check");
}

/// Running the pass twice is a no-op: the second call finds no lemma.
#[test]
fn the_pass_is_idempotent() {
    let mut executor = Executor::new();
    let link = congruence(&mut executor, "idem");
    let (mut proof, _flat) = packed_refutation(&mut executor, &link);
    assert_eq!(executor.derive_congruence_explanations(&mut proof), 1);
    let after = format!("{:?}", proof.steps);
    assert_eq!(executor.derive_congruence_explanations(&mut proof), 0);
    assert_eq!(format!("{:?}", proof.steps), after);
}

/// The WIRE for the RE-PACK arm: the packed unit is rebuilt from `or_neg`
/// tautologies and resolutions, the leaf's `hole` is GONE, and the fragment's
/// last clause is the lemma's own — so every consumer resolves against exactly
/// the term it resolved against before.
///
/// This is the arm the corpus residual needed: measured on 2026-08-22, all six
/// surviving `euf_congruence_explanation` lemmas are packed units whose
/// consumers are `Resolution` steps (1-3 of them), never the single matching
/// `or` step the flat arm requires.
#[test]
fn a_repacked_fragment_prints_or_neg_on_the_wire() {
    let mut executor = Executor::new();
    let link = congruence(&mut executor, "wire_repack");
    let flat = vec![link.not_ab, link.eq_fab];
    let packed = or_term(&mut executor, flat.clone());
    let mut proof = Proof::new();
    proof.add_step(ProofStep::Assume(link.eq_ab)); // t0
    proof.add_step(ProofStep::Assume(link.not_fab)); // t1
    proof.add_step(explanation_lemma(vec![packed])); // t2
                                                     // A CONTRACTION consumer, so the flat arm's `or`-consumer precondition
                                                     // fails and the RE-PACK arm is the one under test.
    proof.add_step(ProofStep::Step {
        rule: AletheRule::Contraction,
        clause: flat,
        premises: vec![ProofId(2)],
        args: Vec::new(),
    }); // t3
    proof.add_step(ProofStep::Resolution {
        clause: vec![link.eq_fab],
        pivot: link.eq_ab,
        clause1: ProofId(3),
        clause2: ProofId(0),
    }); // t4
    proof.add_step(ProofStep::Resolution {
        clause: Vec::new(),
        pivot: link.eq_fab,
        clause1: ProofId(4),
        clause2: ProofId(1),
    }); // t5
    let before = ay_proof::try_export_alethe(&proof, &executor.ctx.terms).expect("renders");
    assert!(
        before.contains(":rule hole"),
        "the fixture must start with a hole:\n{before}"
    );
    assert_eq!(executor.derive_congruence_explanations(&mut proof), 1);
    let after = ay_proof::try_export_alethe(&proof, &executor.ctx.terms).expect("renders");
    assert!(
        !after.contains(":rule hole"),
        "the re-packed fragment must not print a hole:\n{after}"
    );
    assert!(
        after.contains(":rule or_neg"),
        "the packed unit is rebuilt from or_neg:\n{after}"
    );
    assert!(
        after.contains(":rule eq_congruent"),
        "the flat clause is a congruence:\n{after}"
    );
    // The lemma's own clause, byte for byte, is still derived.
    assert!(
        proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::Step { clause, .. } if clause.as_slice() == [packed]
        )),
        "the fragment must end on the lemma's own clause"
    );
    assert!(ay_proof::check_proof(&proof, &executor.ctx.terms).is_ok());
}

#[path = "congruence_explanation_repack_tests.rs"]
mod repack;

#[path = "congruence_explanation_guard_tests.rs"]
mod guards;

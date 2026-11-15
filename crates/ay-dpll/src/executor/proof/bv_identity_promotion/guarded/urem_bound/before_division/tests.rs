// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The BvUremBound joint is asked where a pass would pay for an exact
//! divider, and nowhere else; a joint the theorem does not close changes
//! nothing.

use super::*;

/// model-checker-consumer's divider harness obligation over 40 bits: no exact-division
/// sweep closes it in the strict producer's envelope.
const REMAINDER_IN_RANGE_40: &str = "(set-option :produce-proofs true)
    (set-logic QF_BV)
    (declare-const x (_ BitVec 40))
    (assert (not (bvult (bvurem x #x00000f4243) #x00000f4243)))";

/// `1000 < x < 1002` and `x % 7 = 3`: unsat because `1001 % 7 = 0`, which the
/// bound `x % 7 < 7` does not say. Wider than the bounded evaluator's 8 bits.
const REMAINDER_OFF_THE_BOUND_16: &str = "(set-option :produce-proofs true)
    (set-logic QF_BV)
    (declare-const x (_ BitVec 16))
    (assert (bvugt x #x03e8))
    (assert (bvult x #x03ea))
    (assert (= (bvurem x #x0007) #x0003))";

/// `y = x % 7` beside a contradiction over `a + y` and `b` that holds whatever
/// `y` is: the abstracted attempt refutes it, so no pass needs the divider.
const REMAINDER_NEVER_NEEDED_16: &str = "(set-option :produce-proofs true)
    (set-logic QF_BV)
    (declare-const x (_ BitVec 16))
    (declare-const a (_ BitVec 16))
    (declare-const b (_ BitVec 16))
    (declare-const y (_ BitVec 16))
    (assert (= y (bvurem x #x0007)))
    (assert (bvult (bvadd a y) b))
    (assert (bvult b (bvadd a y)))";

fn has_kind(proof: &Proof, wanted: TheoryLemmaKind) -> bool {
    proof
        .steps
        .iter()
        .any(|step| matches!(step, ProofStep::TheoryLemma { kind, .. } if *kind == wanted))
}

fn single_empty_trust() -> Proof {
    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Trust, Vec::new(), Vec::new(), Vec::new());
    proof
}

fn negations(executor: &mut Executor, roots: &[TermId]) -> Vec<TermId> {
    roots
        .iter()
        .map(|&root| executor.ctx.terms.mk_not_raw(root))
        .collect()
}

/// The shape a search with no SAT-level derivation leaves: every authored
/// root assumed and one Generic lemma, their joint negation.
fn one_generic_lemma(executor: &mut Executor) -> Proof {
    let roots = executor.ctx.assertions.clone();
    let mut proof = Proof::new();
    let negated = negations(executor, &roots);
    let mut current = proof.add_theory_lemma("bv", negated.clone());
    let mut remaining = negated;
    for &root in &roots {
        let assumed = proof.add_assume(root, None);
        let _ = remaining.remove(0);
        current = proof.add_resolution(remaining.clone(), root, current, assumed);
    }
    proof
}

/// The executor with `source` asserted, and its authored roots raw-rebuilt as
/// the guarded collapse rebuilds them. Every fixture requests proofs, as the
/// CLI's default posture does: the stage's wire screen renders the joint's
/// lemma only while a document is observable, and with none it reads that
/// lemma as a gap and declines the joint.
fn asserted(source: &str) -> (Executor, Vec<TermId>) {
    let mut executor = Executor::new();
    for command in ay_frontend::parse(source).unwrap() {
        executor.execute(&command).unwrap();
    }
    let roots = (0..executor.ctx.assertions_parsed().len())
        .map(|index| executor.guarded_source_root(index).unwrap().0)
        .collect();
    (executor, roots)
}

/// The joint over exactly the authored roots, strict-complete and trust-free.
fn certified_by_the_bound(executor: &Executor, proof: &Proof, roots: &[TermId]) -> bool {
    has_kind(proof, TheoryLemmaKind::BvUremBound)
        && !has_kind(proof, TheoryLemmaKind::Generic)
        && ay_proof::check_proof_strict_with_context(proof, &executor.ctx.terms, None, None, None)
            .is_ok_and(|quality| quality.is_complete())
        && ay_proof::validate_reachable_assumes_in_problem_scope(proof, roots).is_ok()
        && ay_proof::terminal_trust_report(proof).is_trust_free()
}

/// The rescue's spelling, whole: `:produce-proofs` keeps a SAT trace that
/// collapses to one empty-clause trust step. Through the public solve this is
/// `group_proofs`' `exact_division_sweep_memo` test.
#[test]
fn the_rescue_meets_the_joint_before_its_anchor() {
    let (mut executor, roots) = asserted(REMAINDER_IN_RANGE_40);
    let mut memo = ay_proof::ExactDivisionSweepMemo::new();
    let _build = memo.begin_build();
    let anchor = negations(&mut executor, &roots);
    let mut proof = single_empty_trust();
    assert!(executor.promote_urem_bound_before_rescue_anchor(&mut proof, &anchor));
    assert!(
        certified_by_the_bound(&executor, &proof, &roots),
        "{proof:#?}"
    );
    assert_eq!(memo.failed_signatures(), 0);
    assert_eq!(memo.skipped_sweeps(), 0);
}

/// The Generic promotion's spelling of the same obligation (the default CLI
/// posture keeps no SAT trace): the joint replaces the proof before the
/// promotion would decide its Generic lemma.
#[test]
fn the_generic_promotion_meets_the_joint_first() {
    let (mut executor, roots) = asserted(REMAINDER_IN_RANGE_40);
    let mut memo = ay_proof::ExactDivisionSweepMemo::new();
    let _build = memo.begin_build();
    let mut proof = one_generic_lemma(&mut executor);
    assert!(executor.promote_urem_bound_before_generic_promotion(&mut proof));
    assert!(
        certified_by_the_bound(&executor, &proof, &roots),
        "{proof:#?}"
    );
    assert_eq!(memo.failed_signatures(), 0);
    assert_eq!(memo.skipped_sweeps(), 0);
}

/// The negative twin: the joint needs the exact divider, so it is refused,
/// leaves the incumbent alone at either site, and the same joint is accepted
/// afresh once the exact divider may be used, in the same build: its refusal
/// was remembered nowhere.
#[test]
fn a_joint_the_theorem_does_not_close_is_declined_and_remembered_nowhere() {
    let (mut executor, roots) = asserted(REMAINDER_OFF_THE_BOUND_16);
    let mut memo = ay_proof::ExactDivisionSweepMemo::new();
    let _build = memo.begin_build();
    let anchor = negations(&mut executor, &roots);
    assert!(executor.needs_exact_divider(&anchor), "the joint is asked");
    let mut collapse = single_empty_trust();
    assert!(!executor.promote_urem_bound_before_rescue_anchor(&mut collapse, &anchor));
    assert_eq!(collapse.steps, single_empty_trust().steps);
    let generic = one_generic_lemma(&mut executor);
    let mut proof = generic.clone();
    assert!(!executor.promote_urem_bound_before_generic_promotion(&mut proof));
    assert_eq!(proof.steps, generic.steps);
    let mut control = Control::capture(&executor, &|| false).unwrap();
    let found = collect::occurrences(&executor, &roots, &mut control).unwrap();
    assert_eq!(found.len(), 1);
    let joint = augmented(
        &mut executor.ctx.terms,
        &executor.proof_source_work,
        &roots,
        &found,
        &mut control,
    )
    .unwrap();
    drop(control);
    assert!(
        ay_proof::without_exact_division(|| executor.check_proof_strict_until_stopped(&joint))
            .is_err(),
        "the bound alone does not refute it"
    );
    assert!(executor
        .check_proof_strict_until_stopped(&joint)
        .is_ok_and(|quality| quality.is_complete()));
    assert_eq!(memo.failed_signatures(), 0);
}

/// The other negative twin: an authored `bvurem` the refutation never needs.
/// The abstracted attempt refutes each pass's own lemma, which is remembered
/// as accepted, so neither site asks the joint, and each pass then decides
/// its lemma exactly as before and keeps its certificate (a carcara-valid
/// document: `group_proofs`' `urem_bound_before_division`).
#[test]
fn a_lemma_the_abstracted_attempt_refutes_keeps_its_pass() {
    let (mut executor, roots) = asserted(REMAINDER_NEVER_NEEDED_16);
    let mut memo = ay_proof::ExactDivisionSweepMemo::new();
    let _build = memo.begin_build();
    let anchor = negations(&mut executor, &roots);
    let mut collapse = single_empty_trust();
    assert!(!executor.promote_urem_bound_before_rescue_anchor(&mut collapse, &anchor));
    assert_eq!(collapse.steps, single_empty_trust().steps);
    assert!(executor.ctx.terms.strict_bv_semantics_validated(&anchor));
    let generic = one_generic_lemma(&mut executor);
    let mut proof = generic.clone();
    assert!(!executor.promote_urem_bound_before_generic_promotion(&mut proof));
    assert_eq!(proof.steps, generic.steps);
    let lemma = generic.steps.iter().find_map(|step| match step {
        ProofStep::TheoryLemma { clause, .. } => Some(clause.as_slice()),
        _ => None,
    });
    assert!(lemma.is_some_and(|clause| executor.ctx.terms.strict_bv_semantics_validated(clause)));
    assert_eq!(memo.failed_signatures(), 0);
    assert_eq!(memo.skipped_sweeps(), 0);
}

/// Neither site asks the joint, or interns anything, without an authored
/// `bvurem`: a quotient, or a signed remainder whatever it elaborates to.
#[test]
fn a_query_without_an_authored_remainder_is_left_untouched() {
    for source in [
        "(set-logic QF_BV)
         (declare-const x (_ BitVec 16))
         (assert (bvult (bvudiv x #x0007) #x0001))
         (assert (bvugt x #x0006))",
        "(set-logic QF_BV)
         (declare-const x (_ BitVec 16))
         (assert (bvsgt x #x03e8))
         (assert (bvslt x #x03ea))
         (assert (= (bvsrem x #x0007) #x0003))",
    ] {
        let mut executor = Executor::new();
        for command in ay_frontend::parse(source).unwrap() {
            executor.execute(&command).unwrap();
        }
        let generic = one_generic_lemma(&mut executor);
        let roots = executor.ctx.assertions.clone();
        let anchor = negations(&mut executor, &roots);
        let terms = executor.ctx.terms.len();
        let mut collapse = single_empty_trust();
        assert!(!executor.promote_urem_bound_before_rescue_anchor(&mut collapse, &anchor));
        let mut proof = generic.clone();
        assert!(!executor.promote_urem_bound_before_generic_promotion(&mut proof));
        assert_eq!(executor.ctx.terms.len(), terms, "{source}");
        assert_eq!(collapse.steps, single_empty_trust().steps);
        assert_eq!(proof.steps, generic.steps);
    }
}

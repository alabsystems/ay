// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Stage-by-stage pins for the shared-quantifier fold promoter.

use ay_core::term::TermData;
use ay_core::Proof;

use crate::Executor;

/// The measured class, reduced: `(not (=> (and A r) (=> r A)))` with
/// `A = (=> a Q)` and `Q` a quantifier written twice.
const SHARED: &str = "(set-logic UFLIA)\n\
     (declare-fun a () Bool)\n\
     (declare-fun r () Bool)\n\
     (declare-fun f (Int) Bool)\n\
     (assert (not (=> (and (=> a (forall ((n Int)) (f n))) r)\n\
                      (=> r (=> a (forall ((n Int)) (f n)))))))";

/// The SAME script with the second quantifier's body over a different symbol,
/// so the two quantifiers are NOT one term.
const MUTANT: &str = "(set-logic UFLIA)\n\
     (declare-fun a () Bool)\n\
     (declare-fun r () Bool)\n\
     (declare-fun f (Int) Bool)\n\
     (declare-fun g (Int) Bool)\n\
     (assert (not (=> (and (=> a (forall ((n Int)) (f n))) r)\n\
                      (=> r (=> a (forall ((n Int)) (g n)))))))";

fn executed(script: &str) -> Executor {
    let commands = ay_frontend::parse(script).expect("fixture must parse");
    let mut executor = Executor::new();
    executor.set_produce_proofs(true);
    executor
        .execute_all(&commands)
        .expect("fixture must elaborate");
    executor
}

/// STAGE PIN. Every term the two-step argument mentions must have a `TermId`,
/// or the derivation cannot be an AY `Proof` at all. This walks the stages in
/// order and names the one that fails, because a bare "did not fire" says
/// nothing about which.
#[test]
fn the_authored_root_re_interns_with_the_shared_quantifier_as_a_leaf() {
    let mut executor = executed(SHARED);
    let parsed: Vec<_> = executor.ctx.assertions_parsed().to_vec();
    assert_eq!(parsed.len(), 1, "fixture precondition: one authored root");

    // The folded slot really is the constant `false` — the defect this pass
    // exists for.
    assert_eq!(
        executor.ctx.assertions.as_slice(),
        &[executor.ctx.terms.false_term()],
        "fixture precondition: elaboration folded the authored root away"
    );

    let mut quantifiers = Vec::new();
    let root = executor
        .raw_intern_surface_sharing_quantifiers(&parsed[0], &mut quantifiers)
        .expect("the authored root must re-intern with a quantifier leaf");
    assert_eq!(
        quantifiers.len(),
        1,
        "the two authored occurrences must be ONE shared term, not two"
    );
    assert!(
        executor.install_authored_quantifier_spellings(&quantifiers),
        "the binder's authored spelling must register with the printer"
    );
    assert!(
        matches!(executor.ctx.terms.get(root), TermData::Not(_)),
        "the re-interned root must be the author's outer negation, not a fold"
    );
    let overrides = executor.proof_export_term_overrides().unwrap_or_default();
    let rendered =
        ay_proof::format_term_alethe_with_overrides(&executor.ctx.terms, root, &overrides);
    assert!(
        executor.rebuilt_root_prints_as_authored(root, &parsed[0]),
        "the re-interned root must print back as the author's own assertion; \
         RENDERED = {rendered}\nAUTHORED = {:?}",
        crate::executor::proof_surface_syntax::strip_frontend_annotations(&parsed[0])
    );
    executor.record_rebuilt_authored_proof_premise(root);
    let candidate = executor
        .shared_tautology_candidate(root)
        .expect("the fold's own propositional argument must be constructible");
    assert!(
        Executor::proof_derives_empty_clause(&candidate),
        "the candidate must reach the empty clause"
    );
    let outcome = executor.check_proof_strict_with_datatypes(&candidate);
    let steps: Vec<String> = candidate
        .steps
        .iter()
        .map(|step| format!("{step:?}"))
        .collect();
    assert!(
        outcome.as_ref().is_ok_and(|quality| quality.is_complete()),
        "the UNCHANGED strict checker must accept the candidate as complete; \
         OUTCOME = {outcome:?}\nSTEPS:\n{}",
        steps.join("\n")
    );
}

/// The promoter replaces a bare hole end to end, and the committed document
/// holds no `hole` and no `trust`.
#[test]
fn the_promoter_replaces_the_bare_hole_with_a_derived_refutation() {
    let mut executor = executed(SHARED);
    let mut proof = Proof::new();
    let false_term = executor.ctx.terms.false_term();
    let assume = proof.add_assume(false_term, None);
    proof.add_rule_step(
        ay_core::AletheRule::Hole,
        Vec::new(),
        vec![assume],
        Vec::new(),
    );

    assert!(
        executor.replace_with_exact_authored_shared_tautology_refutation(&mut proof),
        "the promoter must commit a replacement for the shared-quantifier fold"
    );
    assert!(
        !proof.steps.iter().any(|step| matches!(
            step,
            ay_core::ProofStep::Step {
                rule: ay_core::AletheRule::Hole | ay_core::AletheRule::Trust,
                ..
            }
        )),
        "the committed document must carry no hole and no trust step"
    );
    assert!(
        proof
            .steps
            .iter()
            .any(|step| matches!(step, ay_core::ProofStep::Assume(_))),
        "the committed document must rest on an assume, not on nothing"
    );
}

/// FALSIFY-ONCE. The promoter's whole soundness argument is that the two
/// authored quantifiers are ONE term and that the resolution step discharges
/// that identity rather than asserting it. Break the identity by one symbol
/// and the producer must stop applying — if this ever fires, the pass is
/// inventing a refutation the problem does not have.
#[test]
fn a_root_whose_quantifiers_differ_by_one_symbol_is_refused() {
    let mut executor = executed(MUTANT);
    let parsed: Vec<_> = executor.ctx.assertions_parsed().to_vec();
    assert_eq!(parsed.len(), 1, "fixture precondition: one authored root");

    // Control: the mutant's root still re-interns and still prints as
    // authored, so the refusal below is about the ARGUMENT, not about the
    // premise machinery failing for an unrelated reason.
    let mut quantifiers = Vec::new();
    let root = executor
        .raw_intern_surface_sharing_quantifiers(&parsed[0], &mut quantifiers)
        .expect("control: the mutant root must still re-intern");
    assert_eq!(
        quantifiers.len(),
        2,
        "control: the mutant's two quantifiers must be DIFFERENT terms"
    );
    assert!(
        executor.install_authored_quantifier_spellings(&quantifiers),
        "control: the mutant's binders must still register spellings"
    );
    assert!(
        executor.rebuilt_root_prints_as_authored(root, &parsed[0]),
        "control: the mutant root must still print back as authored"
    );
    assert!(
        executor.shared_tautology_candidate(root).is_none(),
        "with the shared identity broken there is no refutation to record"
    );

    let mut proof = Proof::new();
    let false_term = executor.ctx.terms.false_term();
    proof.add_assume(false_term, None);
    assert!(
        !executor.replace_with_exact_authored_shared_tautology_refutation(&mut proof),
        "the promoter must not fire on a root whose quantifiers differ"
    );
}

/// FALSIFY-ONCE, the other direction. A FORGED step — the exact shape the
/// promoter emits, but resolving on a target that is not both a hypothesis
/// conjunct and a tail consequent — must be refused by the UNCHANGED strict
/// checker. This is what stops a future edit to the search from turning the
/// pass into a false-proof machine: the search is not the authority, the
/// checker is.
#[test]
fn a_forged_resolution_over_a_non_matching_target_is_rejected() {
    let mut executor = executed(MUTANT);
    let parsed: Vec<_> = executor.ctx.assertions_parsed().to_vec();
    let root = executor
        .raw_intern_surface_sharing_quantifiers(&parsed[0], &mut Vec::new())
        .expect("the mutant root must re-intern");
    let TermData::Not(tautology) = executor.ctx.terms.get(root) else {
        panic!("fixture precondition: the root is a negation");
    };
    let tautology = *tautology;
    let (hypothesis, consequent) = executor
        .binary_implication(tautology)
        .expect("fixture precondition: the root negates an implication");

    // `(cl H)` and `(cl (not G))` are both honestly derived; the forgery is
    // resolving them against each other on a pivot neither clause holds.
    let mut forged = Proof::new();
    let assume = forged.add_assume(root, None);
    let positive = forged.add_rule_step(
        ay_core::AletheRule::NotImplies1,
        vec![hypothesis],
        vec![assume],
        Vec::new(),
    );
    let negated_consequent = executor.ctx.terms.mk_not_raw(consequent);
    let negative = forged.add_rule_step(
        ay_core::AletheRule::NotImplies2,
        vec![negated_consequent],
        vec![assume],
        Vec::new(),
    );
    forged.add_resolution(Vec::new(), consequent, negative, positive);

    assert!(
        executor
            .check_proof_strict_with_datatypes(&forged)
            .is_err_or_incomplete(),
        "the strict checker must refuse an empty clause the premises do not yield"
    );
}

/// Local helper so the assertion above reads as one predicate.
trait StrictOutcome {
    fn is_err_or_incomplete(&self) -> bool;
}

impl StrictOutcome for Result<ay_proof::ProofQuality, ay_proof::ProofCheckError> {
    fn is_err_or_incomplete(&self) -> bool {
        !self.as_ref().is_ok_and(|quality| quality.is_complete())
    }
}

/// A conjunct reachable only through a UNIT `(and X)`.
///
/// `and_pos` names one conjunct of a FLAT conjunction. AY's strict checker and
/// `validate_reachable_assumes_in_problem_scope` both ACCEPT a 1-ary source,
/// so a candidate built over one passed every gate this pass had and was then
/// refused by the PRINTER (`alethe_printer/surface_and_pos.rs`: "and_pos
/// source is not a flat Boolean and-term"). Measured at `11172f75f3` that cost
/// the whole verdict under `--proof FILE` (exit 1, no verdict published) and
/// dropped the artifact in the default posture where the base still wrote its
/// holey one — the one outcome this module promises never to produce.
const UNIT_AND: &str = "(set-logic UFLIA)\n\
     (declare-fun a () Bool)\n\
     (declare-fun r () Bool)\n\
     (declare-fun f (Int) Bool)\n\
     (assert (not (=> (and r (and (=> a (forall ((n Int)) (f n)))))\n\
                      (=> r (=> a (forall ((n Int)) (f n)))))))";

#[test]
fn a_unit_conjunction_is_never_an_and_pos_source() {
    let mut executor = executed(UNIT_AND);
    let parsed: Vec<_> = executor.ctx.assertions_parsed().to_vec();
    let mut quantifiers = Vec::new();
    let root = executor
        .raw_intern_surface_sharing_quantifiers(&parsed[0], &mut quantifiers)
        .expect("control: the root must still re-intern");
    assert!(
        executor.install_authored_quantifier_spellings(&quantifiers),
        "control: the binder spellings must register"
    );
    assert!(
        executor.rebuilt_root_prints_as_authored(root, &parsed[0]),
        "control: the root must still print back as authored, so the refusal \
         below is about the unit conjunction and nothing else"
    );
    executor.record_raw_authored_problem_assertion(root);
    assert!(
        executor.shared_tautology_candidate(root).is_none(),
        "a conjunct reachable only through a unit `and` has no printable \
         projection, so no candidate may be built for it"
    );

    let mut proof = Proof::new();
    let false_term = executor.ctx.terms.false_term();
    proof.add_assume(false_term, None);
    assert!(
        !executor.replace_with_exact_authored_shared_tautology_refutation(&mut proof),
        "the promoter must decline rather than commit an unrenderable document"
    );
}

/// The RENDER gate is the general invariant; this pins that it is ARMED.
///
/// The arity guard removes the one shape measured to reach the printer's
/// refusal. It cannot remove the CLASS: any later widening of the search could
/// build some other unprintable step, and every gate the pass had before —
/// strict checking and assume-scope validation — would still wave it through.
/// So hand-build the exact 1-ary `and_pos` the guard now prevents, confirm the
/// STRICT checker is happy with it, and require the render gate to refuse it
/// anyway. If this ever passes, the hard-failure path is one edit away from
/// being open again.
#[test]
fn the_render_gate_refuses_a_step_the_printer_cannot_print() {
    let mut executor = executed(UNIT_AND);
    let parsed: Vec<_> = executor.ctx.assertions_parsed().to_vec();
    let root = executor
        .raw_intern_surface_sharing_quantifiers(&parsed[0], &mut Vec::new())
        .expect("the root must re-intern");
    executor.record_raw_authored_problem_assertion(root);
    let TermData::Not(tautology) = executor.ctx.terms.get(root) else {
        panic!("fixture precondition: the root is a negation");
    };
    let tautology = *tautology;
    let (hypothesis, consequent) = executor
        .binary_implication(tautology)
        .expect("fixture precondition: the root negates an implication");
    // `(and r (and A))` — conjunct 1 is the UNIT `(and A)`.
    let TermData::App(_, hypothesis_args) = executor.ctx.terms.get(hypothesis) else {
        panic!("fixture precondition: the hypothesis is an application");
    };
    let unit_and = hypothesis_args[1];
    let TermData::App(_, unit_args) = executor.ctx.terms.get(unit_and) else {
        panic!("fixture precondition: the second conjunct is an application");
    };
    assert_eq!(
        unit_args.len(),
        1,
        "fixture precondition: the second conjunct is a UNIT conjunction"
    );
    let inner = unit_args[0];

    let mut candidate = Proof::new();
    let assume = candidate.add_assume(root, None);
    let hypothesis_step = candidate.add_rule_step(
        ay_core::AletheRule::NotImplies1,
        vec![hypothesis],
        vec![assume],
        Vec::new(),
    );
    // Project the unit conjunction out of the flat hypothesis — legitimate.
    let not_hypothesis = executor.ctx.terms.mk_not_raw(hypothesis);
    let gate = candidate.add_rule_step(
        ay_core::AletheRule::AndPos(1),
        vec![not_hypothesis, unit_and],
        Vec::new(),
        vec![hypothesis],
    );
    let unit_step = candidate.add_resolution(vec![unit_and], hypothesis, gate, hypothesis_step);
    // Now project OUT OF THE UNIT — the step the printer refuses.
    let not_unit = executor.ctx.terms.mk_not_raw(unit_and);
    let bad_gate = candidate.add_rule_step(
        ay_core::AletheRule::AndPos(0),
        vec![not_unit, inner],
        Vec::new(),
        vec![unit_and],
    );
    let inner_step = candidate.add_resolution(vec![inner], unit_and, bad_gate, unit_step);
    // Close it, so the only thing wrong with this document is the 1-ary
    // projection above and the strict checker has no other reason to refuse.
    let not_consequent = executor.ctx.terms.mk_not_raw(consequent);
    let negative = candidate.add_rule_step(
        ay_core::AletheRule::NotImplies2,
        vec![not_consequent],
        vec![assume],
        Vec::new(),
    );
    let (_, tail) = executor
        .binary_implication(consequent)
        .expect("fixture precondition: the consequent is an implication");
    assert_eq!(
        tail, inner,
        "fixture precondition: the tail IS the conjunct"
    );
    let not_tail = executor.ctx.terms.mk_not_raw(tail);
    let negative = candidate.add_rule_step(
        ay_core::AletheRule::NotImplies2,
        vec![not_tail],
        vec![negative],
        Vec::new(),
    );
    candidate.add_resolution(Vec::new(), inner, negative, inner_step);

    // The two gates the pass had BEFORE the render gate both wave this
    // through. That is the whole point: neither of them can see a printer
    // refusal.
    assert!(
        Executor::proof_derives_empty_clause(&candidate),
        "control: the forged document must reach the empty clause"
    );
    assert!(
        executor
            .check_proof_strict_with_datatypes(&candidate)
            .is_ok_and(|quality| quality.is_complete()),
        "control: AY's strict checker ACCEPTS the 1-ary and_pos as COMPLETE — \
         that is exactly why the render gate has to exist"
    );
    assert!(
        ay_proof::validate_reachable_assumes_in_problem_scope(
            &candidate,
            &executor.proof_export_scope_assertions(),
        )
        .is_ok(),
        "control: the export-scope gate accepts it too — it checks the assume, \
         never the render"
    );
    assert!(
        !executor.shared_tautology_candidate_renders(&candidate),
        "the render gate must refuse a document the Alethe printer cannot print"
    );
}

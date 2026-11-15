// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The array-read and joint guarded candidates repair wire gaps. When nobody
//! can observe the rendered Alethe, a candidate that would itself keep a wire
//! gap cannot improve anything the mint checks, so the planner keeps the
//! native refutation instead of paying a full bit-blast replay for it. Paid at
//! both planner call sites of every ghost-pair certification UNSAT, that
//! replay made the MODEL_CHECKER_CONSUMER CHC canaries miss their per-query budgets on slow
//! cores. Whenever the document IS observable every replay stays, because a
//! `hole`-bearing joint renders where the native refutation's render is
//! refused.

use super::*;
use ay_core::{TermData, TermStore};

/// One ghost-pair certification obligation exactly as ay-chc's executor
/// adapter emits it for the MODEL_CHECKER_CONSUMER harder canary, minus its relative timeout
/// and model request. Several raw roots read arrays, no root is contradictory
/// alone, and the conjunction of all roots has no checked Alethe lowering.
const CERTIFICATION: &str = include_str!("chc-certification-query.smt2");

/// One authored root that reads an array and is contradictory on its own.
const ARRAY_READ_SINGLE: &str = include_str!("array-read-single.smt2");

/// `benchmarks/smt/QF_ABV/wide_mul_unsat.smt2` over a 4-bit index. Neither
/// root is contradictory alone; their conjunction is, and elaboration folds
/// the authored read-over-write, so the exact authored BV refutation's lemma
/// is a two-literal complete blast that renders with no unproved step.
const WIDE_MUL_INDEX4: &str = include_str!("wide-mul-index4.smt2");

fn solved(problem: &str, produce_proofs: bool) -> Executor {
    let mut executor = Executor::new();
    if produce_proofs {
        executor.set_produce_proofs(true);
    }
    let results = executor
        .execute_all(&ay_frontend::parse(problem).unwrap())
        .unwrap();
    assert_eq!(results, ["unsat"], "{:?}", executor.unknown_reason());
    executor
}

// The raw root that the planner's single `BvBitBlast` lemma refutes.
fn bitblast_root(terms: &TermStore, proof: &Proof) -> Option<TermId> {
    proof.steps.iter().find_map(|step| match step {
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::BvBitBlast,
            clause,
            ..
        } => match clause.as_slice() {
            [literal] => match terms.get(*literal) {
                TermData::Not(inner) => Some(*inner),
                _ => None,
            },
            _ => None,
        },
        _ => None,
    })
}

// The joint candidate closes `and_neg` over the authored roots with one
// `BvBitBlast` lemma on the negated raw conjunction.
fn installs_joint_bitblast(terms: &TermStore, proof: &Proof) -> bool {
    bitblast_root(terms, proof).is_some_and(|root| {
        matches!(
            terms.get(root),
            TermData::App(symbol, args) if symbol.name() == "and" && args.len() > 1
        )
    })
}

// A single candidate assumes one raw root and refutes exactly that root.
fn installs_single_bitblast(terms: &TermStore, proof: &Proof) -> bool {
    bitblast_root(terms, proof).is_some_and(|root| proof_already_assumes(proof, root))
}

fn rejected_incumbent(executor: &Executor) -> Proof {
    let mut rejected = Proof::new();
    rejected.add_rule_step(AletheRule::Trust, Vec::new(), Vec::new(), Vec::new());
    assert!(executor
        .check_proof_strict_with_datatypes(&rejected)
        .is_err());
    rejected
}

fn planned(executor: &mut Executor, incumbent: &Proof, stage: GuardedCollapseStage) -> Proof {
    let mut proof = incumbent.clone();
    executor.promote_bv_guarded_collapse(&mut proof, stage);
    proof
}

fn strict_complete(executor: &Executor, proof: &Proof) -> bool {
    executor
        .check_proof_strict_with_datatypes(proof)
        .is_ok_and(|quality| quality.is_complete())
}

#[test]
fn unobserved_certification_keeps_the_native_refutation() {
    let mut executor = solved(CERTIFICATION, false);
    let native = executor
        .retained_internal_proof_for_test()
        .cloned()
        .expect("mandatory UNSAT certification retains its proof");
    // What the mint certifies: strict-complete, with a disclosed wire gap that
    // no guarded candidate over these roots could close.
    assert!(strict_complete(&executor, &native));
    assert!(executor.proof_has_known_wire_gap(&native));
    assert!(
        !installs_joint_bitblast(&executor.ctx.terms, &native),
        "an unobserved certification must keep the native refutation"
    );
    for stage in [GuardedCollapseStage::Cascade, GuardedCollapseStage::Final] {
        assert_eq!(
            format!("{:?}", planned(&mut executor, &native, stage).steps),
            format!("{:?}", native.steps),
            "{stage:?}: a gapped candidate cannot improve a strict-complete proof"
        );
    }
}

#[test]
fn requested_certification_proof_keeps_the_rendering_joint_repair() {
    let executor = solved(CERTIFICATION, true);
    let proof = executor.last_proof().expect("requested proof");
    assert!(installs_joint_bitblast(&executor.ctx.terms, proof));
    assert!(strict_complete(&executor, proof));
    // The native refutation's render is refused at a distinct/equality
    // pivot; the joint repair renders with its one bit-blast lemma unproved.
    let document = executor
        .try_export_last_proof_alethe_for_problem_scope()
        .expect("requested proof")
        .expect("the joint repair renders the requested certificate");
    assert_eq!(document.matches(":rule hole").count(), 1, "{document}");
    assert!(!document.contains(":rule trust"), "{document}");
}

#[test]
fn only_the_final_boundary_rescues_an_unobserved_rejected_proof() {
    for (problem, installs) in [
        (
            CERTIFICATION,
            installs_joint_bitblast as fn(&TermStore, &Proof) -> bool,
        ),
        (ARRAY_READ_SINGLE, installs_single_bitblast),
    ] {
        let mut executor = solved(problem, false);
        let rejected = rejected_incumbent(&executor);
        // Mid-pipeline, later cascade members and derivation passes own the
        // repair of a proof nobody renders.
        assert_eq!(
            format!(
                "{:?}",
                planned(&mut executor, &rejected, GuardedCollapseStage::Cascade).steps
            ),
            format!("{:?}", rejected.steps),
            "{problem}"
        );
        // Just before publication, a strict repair still beats a proof the
        // mint would reject, even though it keeps a wire gap.
        let rescued = planned(&mut executor, &rejected, GuardedCollapseStage::Final);
        assert!(installs(&executor.ctx.terms, &rescued), "{problem}");
        assert!(strict_complete(&executor, &rescued), "{problem}");
        assert!(executor.proof_has_known_wire_gap(&rescued), "{problem}");
    }
}

#[test]
fn observed_repairs_preserve_gapped_controls_and_publish_supported_array_reads() {
    let mut executor = solved(CERTIFICATION, true);
    let rejected = rejected_incumbent(&executor);
    let repaired = planned(&mut executor, &rejected, GuardedCollapseStage::Cascade);
    assert!(installs_joint_bitblast(&executor.ctx.terms, &repaired));
    assert!(executor.proof_has_known_wire_gap(&repaired));

    let mut executor = solved(ARRAY_READ_SINGLE, true);
    let rejected = rejected_incumbent(&executor);
    let repaired = planned(&mut executor, &rejected, GuardedCollapseStage::Cascade);
    assert!(installs_single_bitblast(&executor.ctx.terms, &repaired));
    assert!(Executor::proof_derives_empty_clause(&repaired));
    assert!(strict_complete(&executor, &repaired));
    ay_proof::validate_reachable_assumes_in_problem_scope(
        &repaired,
        &executor.proof_export_scope_assertions(),
    )
    .expect("the supported read proof retains its actual authored source scope");
    assert!(executor.proof_renders_without_unproved_step(&repaired));
}

/// A strict-complete incumbent whose document already renders with no
/// unproved step is not what the joint repair is for: the joint lemma keeps
/// the authored array read and prints as `hole`. The known-wire-gap screen
/// reports the incumbent's two-literal bit-blast lemma as a gap by design, so
/// only its render can say so. Measured at 1c4ed9d77 with `--strict-proofs`:
/// the joint was installed and this query answered `unknown (incomplete
/// proof-trusted)`.
#[test]
fn a_cleanly_rendering_refutation_is_not_traded_for_the_joint_hole() {
    let mut executor = solved(WIDE_MUL_INDEX4, true);
    let published = executor.last_proof().cloned().expect("requested proof");
    assert!(
        !installs_joint_bitblast(&executor.ctx.terms, &published),
        "the published refutation must not be the joint repair"
    );
    assert!(strict_complete(&executor, &published));
    assert!(executor.proof_has_known_wire_gap(&published));
    assert!(executor.proof_renders_without_unproved_step(&published));
    let document = executor
        .try_export_last_proof_alethe_for_problem_scope()
        .expect("requested proof")
        .expect("the published refutation renders");
    assert!(!document.contains(":rule hole"), "{document}");
    assert!(!document.contains(":rule trust"), "{document}");
    for rule in ["arrays_idx", "bitblast_mult", "and_neg"] {
        assert!(
            document.contains(&format!(":rule {rule}")),
            "{rule}: {document}"
        );
    }
    for stage in [GuardedCollapseStage::Cascade, GuardedCollapseStage::Final] {
        assert_eq!(
            format!("{:?}", planned(&mut executor, &published, stage).steps),
            format!("{:?}", published.steps),
            "{stage:?}: a cleanly rendering refutation must be kept"
        );
    }
    // The joint is available for these roots: it still rescues a rejected
    // incumbent, which is what it is for.
    let rejected = rejected_incumbent(&executor);
    let rescued = planned(&mut executor, &rejected, GuardedCollapseStage::Final);
    assert!(installs_joint_bitblast(&executor.ctx.terms, &rescued));
    assert!(strict_complete(&executor, &rescued));
    assert!(!executor.proof_renders_without_unproved_step(&rescued));
}

/// The choice render answers a question from inside the solve, so its
/// complete bit-blast answers to the solve's stop as the known-wire-gap
/// screen's does. The screen reports this refutation's two-literal bit-blast
/// lemma as a gap and declines it outright once the stop has fired, and a
/// wire-gap repair candidate it declines is rendered next: that render asked
/// the complete bit-blast as the exporter does, to completion (on a 64-bit
/// product lemma, past 280 s). With the interrupt raised the render is now
/// refused, so nothing is admitted on it; lowered, the same proof renders
/// clean again.
#[test]
fn the_choice_render_answers_to_the_solves_interrupt() {
    use std::sync::atomic::{AtomicBool, Ordering};
    let mut executor = solved(WIDE_MUL_INDEX4, true);
    let published = executor.last_proof().cloned().expect("requested proof");
    assert!(executor.proof_renders_without_unproved_step(&published));
    assert!(executor.wire_repair_candidate_prints_clean(&published));
    let interrupt = std::sync::Arc::new(AtomicBool::new(true));
    executor.solve_interrupt = Some(std::sync::Arc::clone(&interrupt));
    assert!(executor.proof_has_known_wire_gap(&published));
    assert!(!executor.proof_renders_without_unproved_step(&published));
    assert!(!executor.wire_repair_candidate_prints_clean(&published));
    interrupt.store(false, Ordering::Relaxed);
    assert!(executor.proof_renders_without_unproved_step(&published));
    assert!(executor.wire_repair_candidate_prints_clean(&published));
}

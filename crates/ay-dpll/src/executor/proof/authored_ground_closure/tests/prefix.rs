// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::packing::{prepared, retain};
use super::*;

fn fixture(wrong_alias: bool) -> String {
    fixture_with_goal(wrong_alias, "(not (= true (= (bvnot x) (bvnot y))))")
}

fn fixture_with_goal(wrong_alias: bool, goal: &str) -> String {
    let mut pins = vec![format!("(= x {})", if wrong_alias { "z" } else { "y" })];
    // Eight independent 64-frame spines spend the real shared allowance in
    // offset preflight, after congruence has joined the actual goal. Their
    // reflexive source pins grant no arithmetic shortcut to the proof.
    let mut padding_declarations = String::new();
    for index in 0..8 {
        let mut spine = format!("p{index}");
        padding_declarations.push_str(&format!("(declare-const {spine} (_ BitVec 8))\n"));
        for _ in 0..64 {
            spine = format!("(bvadd {spine} (_ bv1 8))");
        }
        pins.push(format!("(= {spine} {spine})"));
    }
    pins.push("(= (select memory (_ bv0 8)) w)".to_string());
    pins.push(goal.to_string());
    format!(
        "(set-option :produce-proofs true)\n(set-logic QF_AUFBV)\n\
         (declare-const x (_ BitVec 8))\n(declare-const y (_ BitVec 8))\n\
         (declare-const z (_ BitVec 8))\n{padding_declarations}(declare-const w (_ BitVec 8))\n\
         (declare-const memory (Array (_ BitVec 8) (_ BitVec 8)))\n\
         (assert (and {}))\n(check-sat)\n",
        pins.join(" ")
    )
}

#[test]
fn a_plain_equality_uses_only_the_completed_bounded_prefix() {
    for (wrong_alias, limit) in [
        (false, work::MAX_SHARED_WORK),
        (true, work::MAX_SHARED_WORK),
        (false, 0),
    ] {
        let input = fixture_with_goal(wrong_alias, "(not (= (bvnot x) (bvnot y)))");
        let (mut exec, root) = prepared(&input);
        let mut search = search(&exec, root);
        let mut work = SharedGroundWork::new(limit);
        let conflict = exec.saturate_ground_search_with_work(&mut search, &[root], &[], &mut work);
        assert!(work.refused());
        if wrong_alias || limit == 0 {
            assert!(conflict.is_none());
            assert!(exec.last_proof().is_none());
            continue;
        }
        assert!(matches!(
            exec.ground_search_final_conflict(&search, &[], &work, &|| true),
            FinalGroundCheck::Stopped
        ));
        let proof = exec
            .emit_ground_closure_refutation(&search, conflict.unwrap())
            .unwrap();
        assert!(ay_proof::check_proof_strict_with_context(
            &proof,
            &exec.ctx.terms,
            None,
            None,
            Some(&[root]),
        )
        .unwrap()
        .is_complete());
        assert!(ay_proof::check_proof_strict_with_context(
            &proof,
            &exec.ctx.terms,
            None,
            None,
            Some(&[]),
        )
        .is_err());
        assert_eq!(
            lemma_count(&proof, |kind, _| matches!(
                kind,
                TheoryLemmaKind::BvBitBlast
            )),
            0
        );
        exec.set_alethe_dialect(ay_proof::AletheDialect::Clean);
        let text = ay_proof::try_export_alethe(&proof, &exec.ctx.terms).unwrap();
        assert!(!text.contains(":rule hole") && !text.contains(":rule trust"));
        retain("budget-prefix-plain-equality", &input, Some(&text));
    }
}

fn search(exec: &Executor, root: TermId) -> GroundSearch {
    let mut search = GroundSearch::default();
    exec.register_ground_subterms(&mut search.closure, root)
        .unwrap();
    search
}

#[test]
fn work_refusal_keeps_a_completed_prefix_with_an_exact_scoped_proof() {
    let input = fixture(false);
    let (mut exec, root) = prepared(&input);
    let mut search = search(&exec, root);
    let mut work = SharedGroundWork::new(work::MAX_SHARED_WORK);
    let conflict = exec
        .saturate_ground_search_with_work(&mut search, &[root], &[], &mut work)
        .expect("the existing final check sees the completed bounded prefix");
    assert!(
        work.refused(),
        "the real default work envelope must be exercised"
    );
    assert!(exec
        .negated_goal_conflict(&search, goal::GoalPhase::Final)
        .is_some());
    assert!(matches!(
        exec.ground_search_final_conflict(&search, &[], &work, &|| true),
        FinalGroundCheck::Stopped
    ));
    let proof = exec
        .emit_ground_closure_refutation(&search, conflict)
        .unwrap();
    assert!(proof
        .steps
        .iter()
        .all(|step| !matches!(step, ProofStep::Assume(term) if *term != root)));
    assert_eq!(
        lemma_count(&proof, |kind, _| matches!(
            kind,
            TheoryLemmaKind::BvBitBlast
        )),
        0
    );
    assert!(ay_proof::check_proof_strict_with_context(
        &proof,
        &exec.ctx.terms,
        None,
        None,
        Some(&[root])
    )
    .unwrap()
    .is_complete());
    assert!(ay_proof::check_proof_strict_with_context(
        &proof,
        &exec.ctx.terms,
        None,
        None,
        Some(&[])
    )
    .is_err());
    exec.set_alethe_dialect(ay_proof::AletheDialect::Clean);
    let overrides = exec.proof_export_term_overrides();
    let surfaces = exec.authored_export_surfaces();
    let text = exec
        .in_alethe_dialect(|| {
            ay_proof::try_export_alethe_with_authored_surfaces(
                &proof,
                &exec.ctx.terms,
                &[root],
                overrides.as_ref(),
                surfaces.channels(),
                None,
            )
        })
        .unwrap();
    ay_proof::check_alethe_document_in_dialect(
        &text,
        &ay_proof::ProblemScope::from_smtlib_source(&input),
        exec.alethe_dialect(),
    )
    .unwrap();
    assert!(!text.contains(":rule hole") && !text.contains(":rule trust"));
    assert!(exec.last_proof().is_none() && exec.last_proof_raw_original_assertions.is_empty());
    retain("budget-prefix-positive", &input, Some(&text));
    println!(
        "ground budget prefix: steps={} work_remaining={} work_refused={}",
        proof.steps.len(),
        work.remaining(),
        work.refused()
    );
}

#[test]
fn work_refusal_needs_the_goal_and_cannot_refill_a_zero_allowance() {
    for (wrong_alias, limit, name) in [
        (true, work::MAX_SHARED_WORK, "budget-prefix-wrong-alias"),
        (false, 0, "budget-prefix-zero-work"),
    ] {
        let input = fixture(wrong_alias);
        let (mut exec, root) = prepared(&input);
        let mut search = search(&exec, root);
        let mut work = SharedGroundWork::new(limit);
        assert!(exec
            .saturate_ground_search_with_work(&mut search, &[root], &[], &mut work)
            .is_none());
        assert!(work.refused());
        assert!(exec
            .negated_goal_conflict(&search, goal::GoalPhase::Final)
            .is_none());
        assert!(exec.last_proof().is_none() && exec.last_proof_raw_original_assertions.is_empty());
        if limit == 0 {
            assert_eq!(work.remaining(), 0);
        }
        retain(name, &input, None);
    }
}

#[test]
fn work_prefix_refuses_foreign_or_popped_custody_and_interruption() {
    for kind in ["foreign-read", "foreign-pack", "popped"] {
        let (mut exec, root) = prepared(&fixture(false));
        let mut search = search(&exec, root);
        let mut empty = GroundClosure::default();
        let mut binding_work = SharedGroundWork::new(work::MAX_SHARED_WORK);
        if kind == "popped" {
            exec.add_ground_read_chain_edges(
                &mut empty,
                &mut search.read_chains,
                &search.facts,
                &mut binding_work,
            )
            .unwrap();
            exec.add_ground_packing_edges(
                &mut empty,
                &mut search.packings,
                &mut 512,
                &mut binding_work,
            )
            .unwrap();
            exec.execute_all(&parse("(push 1)(assert true)(pop 1)").unwrap())
                .unwrap();
        } else {
            let mut foreign = Executor::new();
            if kind == "foreign-read" {
                foreign
                    .add_ground_read_chain_edges(
                        &mut empty,
                        &mut search.read_chains,
                        &search.facts,
                        &mut binding_work,
                    )
                    .unwrap();
            } else {
                foreign
                    .add_ground_packing_edges(
                        &mut empty,
                        &mut search.packings,
                        &mut 512,
                        &mut binding_work,
                    )
                    .unwrap();
            }
        }
        let mut work = SharedGroundWork::new(work::MAX_SHARED_WORK);
        assert!(
            exec.saturate_ground_search_with_work(&mut search, &[root], &[], &mut work)
                .is_none(),
            "{kind}"
        );
        assert!(work.refused());
        assert!(
            exec.negated_goal_conflict(&search, goal::GoalPhase::Final)
                .is_some(),
            "custody, rather than goal absence, must cause refusal"
        );
        assert!(exec.last_proof().is_none() && exec.last_proof_raw_original_assertions.is_empty());
    }
    let (mut exec, root) = prepared(&fixture(false));
    exec.set_interrupt(std::sync::Arc::new(std::sync::atomic::AtomicBool::new(
        true,
    )));
    let mut search = search(&exec, root);
    let mut work = SharedGroundWork::new(work::MAX_SHARED_WORK);
    assert!(exec
        .saturate_ground_search_with_work(&mut search, &[root], &[], &mut work)
        .is_none());
    assert!(!work.refused());
    assert_eq!(work.remaining(), work::MAX_SHARED_WORK);
    assert!(exec.last_proof().is_none() && exec.last_proof_raw_original_assertions.is_empty());
}

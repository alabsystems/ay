// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Native SOS dependency traversal must not bypass authored presentation scope.

use super::*;
use ay_frontend::parse;

fn certified(source: &str) -> Box<Executor> {
    let commands = parse(&format!(
        "(set-option :produce-proofs true) \
         (set-option :check-proofs-strict true) (set-logic ALL) \
         (declare-const foreign Bool) {source}"
    ))
    .expect("source fixture parses");
    let mut executor = Box::new(Executor::new());
    executor
        .execute_all(&commands)
        .expect("install source only");
    // Inject only a provisional decision. The production helper constructs,
    // authenticates and independently checks the actual native certificate.
    assert!(executor
        .certify_native_sos_provisional_for_test()
        .is_unsat());
    let proof = executor.last_proof().expect("requested native proof");
    assert!(proof
        .steps
        .iter()
        .any(|step| matches!(step, ProofStep::NraSos { .. })));
    let bundle = executor
        .strict_native_nra_sos_bundle_for_proof(proof)
        .expect("current native SOS authority");
    let checked = ay_proof::re_check_bundle_strict(bundle).expect("native strict replay");
    assert!(checked.quality.is_complete());
    assert_eq!(checked.assume_terms, bundle.obligation_assertions);
    assert_eq!(checked.quality.hole_count, 0);
    executor
}

const REAL_SQUARE: &str = "(declare-const x Real) (assert (< (* x x) 0.0))";

#[test]
fn native_sos_dependencies_retain_authored_roots_and_render_checked_alethe() {
    for source in ["(declare-const x Int) (assert (< (* x x) 0))", REAL_SQUARE] {
        let executor = certified(source);
        let proof = executor.last_proof().unwrap();
        let bundle = executor
            .strict_native_nra_sos_bundle_for_proof(proof)
            .unwrap();
        assert_eq!(
            reachable_authored_assume_roots(proof),
            Some(bundle.obligation_assertions.clone())
        );
        assert_eq!(bundle.obligation_assertions.len(), 1);
        assert!(executor
            .last_proof_with_authenticated_alethe_surface()
            .is_some());
        let text = executor
            .try_export_last_proof_alethe_for_problem_scope()
            .expect("authenticated source presentation")
            .expect("checked SOS rendering");
        assert_eq!(text.matches(":rule hole").count(), 0, "{text}");
        assert!(text.contains(":rule la_mult_neg"), "{text}");
        assert!(!text.contains(":rule nra_sos"));
        assert!(!text.contains(":rule trust"));
    }
}

/// The native SOS lane installs its proof through the shared exact-source
/// installer, which retires the displaced proof's surface overrides with every
/// other sidecar. Unless the lane rebuilds the authored channel for the proof
/// it installs, `(get-proof)` prints the canonical `(<= 1 x)` for an authored
/// `(>= x 1)`. MEASURED on `QF_NIA/simple_product_unsat.smt2` (this fixture):
/// pinned carcara 1.1.0 refused that document at `t0` ("could not match term to
/// any of the original problem premises") while the strict checker, which
/// compares interned roots, accepted it.
#[test]
fn native_sos_publishes_each_authored_comparison_spelling_at_its_assume() {
    let executor = certified(
        "(declare-const x Int) (declare-const y Int) \
         (assert (>= x 1)) (assert (<= x 2)) (assert (>= y 1)) (assert (<= y 2)) \
         (assert (= (* x y) 7))",
    );
    let assumes = |text: &str, spelling: &str| {
        text.lines()
            .any(|line| line.starts_with("(assume ") && line.ends_with(&format!(" {spelling})")))
    };
    let exported = executor
        .try_export_last_proof_alethe_for_problem_scope()
        .expect("authenticated source presentation")
        .expect("diagnostic SOS rendering");
    let get_proof = executor.get_proof();
    for text in [&exported, &get_proof] {
        for authored in ["(>= x 1)", "(>= y 1)", "(<= x 2)", "(= (* x y) 7)"] {
            assert!(
                assumes(text, authored),
                "{authored} is the problem's premise:\n{text}"
            );
        }
        for canonical in ["(<= 1 x)", "(<= 1 y)"] {
            assert!(
                !assumes(text, canonical),
                "{canonical} is no premise:\n{text}"
            );
        }
        assert!(text.contains(":rule comp_simplify"), "{text}");
    }
}

#[test]
fn reachable_foreign_assume_still_refuses_the_sos_presentation() {
    let mut executor = certified(REAL_SQUARE);
    let foreign = executor.ctx.symbol_info("foreign").unwrap().term.unwrap();
    let mut proof = executor.last_proof().unwrap().clone();
    let mut replaced = 0;
    for step in &mut proof.steps {
        if let ProofStep::Assume(root) = step {
            *root = foreign;
            replaced += 1;
        }
    }
    assert_eq!(replaced, 1);
    assert_eq!(reachable_authored_assume_roots(&proof), Some(vec![foreign]));
    assert!(executor
        .resolve_reachable_authored_sources(&[foreign])
        .is_err());
    // This is deliberately invalid data, not a newly certified refutation.
    executor.last_proof = Some(proof);
    assert!(
        executor.last_proof().is_some(),
        "not an output-request refusal"
    );
    assert!(executor
        .last_proof_with_authenticated_alethe_surface()
        .is_none());
    assert!(executor
        .try_export_last_proof_alethe_for_problem_scope()
        .is_none());
}

#[test]
fn native_sos_does_not_restore_a_discarded_source_presentation() {
    let mut executor = certified(REAL_SQUARE);
    assert!(executor
        .last_proof_with_authenticated_alethe_surface()
        .is_some());
    let roots = reachable_authored_assume_roots(executor.last_proof().unwrap()).unwrap();
    executor.set_retain_parsed_assertions(false);
    assert!(!executor.ctx.retains_parsed_assertions());
    let proof = executor
        .last_proof()
        .expect("native proof remains available");
    assert_eq!(reachable_authored_assume_roots(proof), Some(roots));
    assert!(executor
        .strict_native_nra_sos_bundle_for_proof(proof)
        .is_some());
    assert!(executor
        .last_proof_with_authenticated_alethe_surface()
        .is_none());
    assert!(executor
        .try_export_last_proof_alethe_for_problem_scope()
        .is_none());
}

#[test]
fn sos_traversal_ignores_unreachable_assumes_but_rejects_bad_dependencies() {
    let executor = certified(REAL_SQUARE);
    let mut proof = executor.last_proof().unwrap().clone();
    let roots = reachable_authored_assume_roots(&proof).unwrap();
    let foreign = executor.ctx.symbol_info("foreign").unwrap().term.unwrap();
    proof.steps.push(ProofStep::Assume(foreign));
    assert_eq!(reachable_authored_assume_roots(&proof), Some(roots));

    let mut changed = false;
    for step in &mut proof.steps {
        if let ProofStep::Resolution {
            clause1, clause, ..
        } = step
        {
            if clause.is_empty() {
                *clause1 = ProofId(u32::MAX);
                changed = true;
                break;
            }
        }
    }
    assert!(changed, "genuine native proof resolves to the empty clause");
    assert!(reachable_authored_assume_roots(&proof).is_none());
}

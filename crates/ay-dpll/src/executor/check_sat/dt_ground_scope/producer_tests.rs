// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::Proof;

fn parsed(source: &str) -> Executor {
    let mut exec = Executor::new();
    exec.execute_all(&ay_frontend::parse(source).expect("parse"))
        .expect("declarations and assertions");
    exec.proof_tracker.enable();
    exec
}

#[test]
fn actual_auflia_records_restore_before_original_certification() {
    let mut exec = parsed(
        "(set-logic QF_AUFLIA) (declare-fun f (Int) Int)
         (declare-const x Int) (assert (= (f 0) 42))
         (assert (= x (+ (f 0) 1)))",
    );
    let roots = exec.ctx.assertions.clone();
    let _ = exec.preprocess_auflia_assertions_with_proof_provenance();
    assert!(!exec.propagated_value_provenance.rewrites.is_empty());
    let before = format!("{:?}", exec.propagated_value_provenance);
    let storage = exec.propagated_value_provenance.rewrites.as_ptr();
    let evidence = exec.with_dt_ground_candidate_scope(
        roots.clone(),
        &roots,
        |this| {
            assert!(this.propagated_value_provenance.rewrites.is_empty());
            let _ = this.preprocess_auflia_assertions_with_proof_provenance();
            assert!(!this.propagated_value_provenance.rewrites.is_empty());
            assert_ne!(this.propagated_value_provenance.rewrites.as_ptr(), storage);
            this.last_model = Some(crate::executor::model::Model::empty());
            Ok(SolveResult::Sat)
        },
        |this| {
            assert_eq!(format!("{:?}", this.propagated_value_provenance), before);
            assert_eq!(this.propagated_value_provenance.rewrites.as_ptr(), storage);
            None
        },
    );
    assert!(evidence.is_none());
    assert_eq!(format!("{:?}", exec.propagated_value_provenance), before);
    assert_eq!(exec.propagated_value_provenance.rewrites.as_ptr(), storage);
}

#[derive(Clone, Copy)]
enum PrivateExit {
    Unsat,
    Unwind,
}

fn pigeonhole_roundtrip(exit: PrivateExit) {
    let mut exec = parsed(
        "(declare-datatype E ((A) (B)))
         (declare-const a E) (declare-const b E) (declare-const c E)
         (declare-const d E) (declare-const e E) (declare-const f E)
         (assert (distinct a b c)) (assert (distinct d e f))",
    );
    let roots = exec.ctx.assertions.clone();
    assert!(exec.add_finite_enum_pigeonhole_conflict());
    let before = format!("{:?}", exec.last_finite_enum_pigeonhole);
    let storage = exec
        .last_finite_enum_pigeonhole
        .as_ref()
        .expect("outer witness")
        .members
        .as_ptr();
    let old_members = exec
        .last_finite_enum_pigeonhole
        .as_ref()
        .expect("outer witness")
        .members
        .clone();
    exec.ctx.assertions = roots.clone();
    // Select the other actual clique, rather than replaying an outer witness.
    let private = if old_members
        .iter()
        .any(|term| exec.format_term(*term) == "a")
    {
        roots[1]
    } else {
        roots[0]
    };
    let caught = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        exec.with_dt_ground_candidate_scope(
            vec![private],
            &roots,
            |this| {
                assert!(this.last_finite_enum_pigeonhole.is_none());
                assert!(this.add_finite_enum_pigeonhole_conflict());
                assert_ne!(
                    this.last_finite_enum_pigeonhole
                        .as_ref()
                        .expect("private witness")
                        .members,
                    old_members
                );
                match exit {
                    PrivateExit::Unsat => Ok(SolveResult::unsat()),
                    PrivateExit::Unwind => panic!("private pigeonhole unwind"),
                }
            },
            |_| panic!("a refuted ground candidate cannot grant SAT"),
        )
    }));
    match exit {
        PrivateExit::Unsat => assert!(caught.expect("normal return").is_none()),
        PrivateExit::Unwind => assert!(caught.is_err()),
    }
    assert_eq!(exec.ctx.assertions, roots);
    assert_eq!(format!("{:?}", exec.last_finite_enum_pigeonhole), before);
    assert_eq!(
        exec.last_finite_enum_pigeonhole
            .as_ref()
            .expect("restored witness")
            .members
            .as_ptr(),
        storage
    );
}

#[test]
fn actual_pigeonhole_witness_survives_private_unsat() {
    pigeonhole_roundtrip(PrivateExit::Unsat);
}

#[test]
fn actual_pigeonhole_witness_survives_private_unwind() {
    pigeonhole_roundtrip(PrivateExit::Unwind);
}

#[test]
fn actual_unsat_rebuild_does_not_expand_outer_premise_authority() {
    let mut exec = parsed("(set-logic QF_LIA) (declare-const x Int) (assert (= x 0))");
    exec.rebuild_trust_leaf_proof_from_original_assertions(&mut Proof::new());
    assert_ne!(exec.last_proof_rebuild_originals, [] as [TermId; 0]);
    exec.execute_all(
        &ay_frontend::parse(
            "(assert (= (let ((k (+ x 1))) k) 0))
             (assert (= (ite true (+ x 1) x) 0))",
        )
        .expect("let and raw-ITE assertions"),
    )
    .expect("append");
    let roots = exec.ctx.assertions.clone();
    let before = exec.proof_legit_assume_set();
    let old_rebuild = exec.last_proof_rebuild_originals.clone();
    let old_raw = exec.last_proof_raw_original_assertions.clone();
    let old_lets = exec.last_proof_expanded_let_sources.clone();
    let evidence = exec.with_dt_ground_candidate_scope(
        roots.clone(),
        &roots,
        |this| {
            assert_eq!(this.last_proof_rebuild_originals, [] as [TermId; 0]);
            this.rebuild_trust_leaf_proof_from_original_assertions(&mut Proof::new());
            assert_ne!(this.last_proof_raw_original_assertions, [] as [TermId; 0]);
            assert!(this
                .last_proof_rebuild_originals
                .iter()
                .any(|root| !before.contains(root)));
            let result = this.solve_lia()?;
            assert!(result.is_unsat());
            Ok(result)
        },
        |_| panic!("UNSAT cannot grant a model"),
    );
    assert!(evidence.is_none());
    assert_eq!(exec.proof_legit_assume_set(), before);
    assert_eq!(exec.last_proof_rebuild_originals, old_rebuild);
    assert_eq!(exec.last_proof_raw_original_assertions, old_raw);
    assert_eq!(exec.last_proof_expanded_let_sources, old_lets);
}

#[test]
fn actual_interpolation_and_lrat_outputs_restore_after_private_unsat() {
    let mut exec = parsed(
        "(set-logic QF_UF) (declare-const a Bool) (declare-const b Bool)
         (assert (or a b)) (assert (or (not a) b))
         (assert (or a (not b))) (assert (or (not a) (not b)))",
    );
    exec.set_interpolation_proofs(100_000);
    // This producer performs UNSAT proof assembly before it returns. A
    // second assembly would consume an already-drained trace, clearing LRAT.
    let result = exec.solve_propositional().expect("outer SAT producer");
    assert!(result.is_unsat());
    let roots = exec.ctx.assertions.clone();
    let proof_storage = exec
        .interpolation
        .last_proof
        .as_ref()
        .expect("actual interpolation proof")
        .steps
        .as_ptr();
    let lrat = exec
        .last_lrat_certificate
        .as_ref()
        .expect("actual LRAT")
        .clone();
    let before = format!("{:?}", exec.interpolation.last_proof);
    let evidence = exec.with_dt_ground_candidate_scope(
        roots.clone(),
        &roots,
        |this| {
            assert!(this.interpolation.enabled);
            assert!(this.interpolation.last_proof.is_none());
            assert!(this.last_lrat_certificate.is_none());
            let result = this.solve_propositional()?;
            assert!(result.is_unsat());
            assert!(this.interpolation.last_proof.is_some());
            assert!(this.last_lrat_certificate.is_some());
            Ok(result)
        },
        |_| panic!("UNSAT cannot grant a model"),
    );
    assert!(evidence.is_none());
    assert!(exec.interpolation.enabled);
    assert_eq!(format!("{:?}", exec.interpolation.last_proof), before);
    assert_eq!(
        exec.interpolation
            .last_proof
            .as_ref()
            .expect("outer proof")
            .steps
            .as_ptr(),
        proof_storage
    );
    assert_eq!(exec.last_lrat_certificate, Some(lrat));
}

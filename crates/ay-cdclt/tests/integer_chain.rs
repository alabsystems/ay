// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_cdclt::{Engine, EngineConfig, Guard, ModelVerdict, Verdict};
use ay_core::{Sort, Symbol, TermId, TermStore, TheoryLemmaKind};
use std::time::{Duration, Instant};

fn parity(terms: &mut TermStore, upper: i64, uf: bool) -> [TermId; 3] {
    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(0.into());
    let two = terms.mk_int(2.into());
    let x2 = terms.mk_add(vec![x, two]);
    let q0 = if uf {
        terms.mk_app(Symbol::named("q"), vec![x, two], Sort::Int)
    } else {
        terms.mk_var("a", Sort::Int)
    };
    let q2 = if uf {
        terms.mk_app(Symbol::named("q"), vec![x2, two], Sort::Int)
    } else {
        terms.mk_var("b", Sort::Int)
    };
    let twice0 = terms.mk_mul(vec![two, q0]);
    let twice2 = terms.mk_mul(vec![two, q2]);
    let r0 = terms.mk_sub(vec![x, twice0]);
    let r2 = terms.mk_sub(vec![x2, twice2]);
    let upper = terms.mk_int(upper.into());
    [
        terms.mk_gt(r2, zero),
        terms.mk_eq(r0, zero),
        terms.mk_le(r2, upper),
    ]
}

fn engine(roots: &[TermId], proofs: bool) -> Engine {
    let mut engine = Engine::new(EngineConfig {
        record_proofs: proofs,
        difference_logic: false,
        ..EngineConfig::default()
    });
    for &root in roots {
        engine.assert(root);
    }
    engine
}

#[test]
fn integer_chain_unbounded_scalar_parity_is_one_checked_conflict() {
    for order in [[0, 1, 2], [2, 1, 0], [1, 0, 2]] {
        let mut terms = TermStore::new();
        let original = parity(&mut terms, 1, false);
        let roots = order.map(|index| original[index]);
        let mut engine = engine(&roots, true);
        let guard = Guard::new().with_deadline(Some(Instant::now() + Duration::from_millis(5624)));
        let outcome = engine.check(&mut terms, &[], &guard);
        assert_eq!(outcome.verdict, Verdict::Unsat, "{outcome:?}");
        assert_eq!(engine.stats().solve_calls, 1);
        assert!(engine.stats().final_checks < 10, "{:#?}", engine.stats());
        let recorded = outcome.proof.as_ref().unwrap();
        assert!(recorded
            .steps()
            .iter()
            .any(|step| step.hint.kind == TheoryLemmaKind::IntCgCutChain));
        let proof = recorded.assemble(&mut terms, guard.deadline()).unwrap();
        let quality = ay_proof::check_proof_strict_with_context(
            &proof.proof,
            &terms,
            None,
            None,
            Some(&roots),
        )
        .unwrap();
        assert!(quality.is_complete());
        assert!(
            ay_proof::check_proof_strict_with_context(
                &proof.proof,
                &terms,
                None,
                None,
                Some(&roots[..2])
            )
            .is_err(),
            "omitted original root must revoke the certificate"
        );
        let mut forged = proof.proof.clone();
        forged.steps = vec![ay_core::ProofStep::Step {
            rule: ay_core::AletheRule::Trust,
            clause: vec![],
            premises: vec![],
            args: vec![],
        }];
        assert!(ay_proof::check_proof_strict_with_context(
            &forged,
            &terms,
            None,
            None,
            Some(&roots)
        )
        .is_err());
        if order == [0, 1, 2] {
            let checker = std::env::var_os("CARCARA_PATH")
                .expect("qualification requires the pinned checker");
            let dir = std::env::temp_dir().join(format!("ay-integer-chain-{}", std::process::id()));
            std::fs::create_dir_all(&dir).unwrap();
            let mut problem =
                "(set-logic QF_LIA)\n(declare-fun x () Int)\n(declare-fun a () Int)\n(declare-fun b () Int)\n"
                    .to_owned();
            for &root in &roots {
                problem.push_str(&format!(
                    "(assert {})\n",
                    ay_proof::format_term_alethe(&terms, root)
                ));
            }
            problem.push_str("(check-sat)\n");
            let smt = dir.join("original.smt2");
            let alethe = dir.join("whole.alethe");
            std::fs::write(&smt, problem).unwrap();
            std::fs::write(
                &alethe,
                ay_proof::export_alethe_with_problem_scope(&proof.proof, &terms, &roots),
            )
            .unwrap();
            let checked = std::process::Command::new(checker)
                .arg("check")
                .arg(&alethe)
                .arg(&smt)
                .output()
                .unwrap();
            assert!(
                checked.status.success()
                    && String::from_utf8_lossy(&checked.stdout)
                        .lines()
                        .any(|line| line.trim() == "valid"),
                "checker: {} {}",
                String::from_utf8_lossy(&checked.stdout),
                String::from_utf8_lossy(&checked.stderr)
            );
        }
    }
}

#[test]
fn integer_chain_looser_uf_neighbor_keeps_a_validated_model() {
    let mut terms = TermStore::new();
    let roots = parity(&mut terms, 2, true);
    let mut engine = engine(&roots, false);
    let outcome = engine.check(
        &mut terms,
        &[],
        &Guard::new().with_deadline(Some(Instant::now() + Duration::from_millis(5624))),
    );
    assert_eq!(outcome.verdict, Verdict::Sat, "{outcome:?}");
    assert_eq!(
        engine.check_model(&mut terms, &roots),
        ModelVerdict::Satisfied
    );
    assert_eq!(engine.stats().solve_calls, 1);
}

#[test]
fn integer_chain_does_not_round_real_rows() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let zero = terms.mk_rational(num_rational::BigRational::from_integer(0.into()));
    let one = terms.mk_rational(num_rational::BigRational::from_integer(1.into()));
    let two = terms.mk_rational(num_rational::BigRational::from_integer(2.into()));
    let twice = terms.mk_mul(vec![x, two]);
    let roots = [terms.mk_gt(twice, zero), terms.mk_le(twice, one)];
    let mut engine = engine(&roots, true);
    assert_eq!(
        engine.check(&mut terms, &[], &Guard::new()).verdict,
        Verdict::Sat
    );
    assert_eq!(
        engine.check_model(&mut terms, &roots),
        ModelVerdict::Satisfied
    );
}

#[test]
fn integer_chain_original_uf_decision_avoids_unbounded_branching() {
    let mut terms = TermStore::new();
    let roots = parity(&mut terms, 1, true);
    // The standalone kernel's UF proof-recording boundary is unchanged. Its
    // actual consumer's original UF query/proof is checked in ay-dpll tests.
    let mut engine = engine(&roots, false);
    let outcome = engine.check(
        &mut terms,
        &[],
        &Guard::new().with_deadline(Some(Instant::now() + Duration::from_millis(5624))),
    );
    assert_eq!(outcome.verdict, Verdict::Unsat, "{outcome:?}");
    assert_eq!(engine.stats().solve_calls, 1);
    assert!(engine.stats().final_checks < 10, "{:#?}", engine.stats());
}

#[test]
fn integer_chain_specific_false_cut_for_the_sat_neighbor_is_rejected() {
    let mut terms = TermStore::new();
    let roots = parity(&mut terms, 2, true);
    let clause: Vec<_> = roots.iter().map(|&root| terms.mk_not_raw(root)).collect();
    assert!(ay_core::proof_validation::lia_cut_chain_witness(&terms, &clause).is_none());
    // Every Boolean resolution is valid; the one false arithmetic cut is
    // the reason this otherwise complete purported refutation must fail.
    let mut proof = ay_core::Proof::new();
    let mut tail =
        proof.add_theory_lemma_with_kind("LIA", clause.clone(), TheoryLemmaKind::IntCgCutChain);
    let mut remaining = clause;
    for &root in &roots {
        let source = proof.add_assume(root, None);
        remaining.remove(0);
        tail = proof.add_resolution(remaining.clone(), root, tail, source);
    }
    assert!(remaining.is_empty());
    assert!(
        ay_proof::check_proof_strict_with_context(&proof, &terms, None, None, Some(&roots))
            .is_err()
    );
}

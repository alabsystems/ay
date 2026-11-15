// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn fixture() -> (ExprRefutation, BvExprProofLimits, BvBlastValidateLimits) {
    let expression = BvExpr::const_val(1, 1);
    let limits =
        BvExprProofLimits::conservative_external(Instant::now() + Duration::from_secs(30), 100);
    let preflight = preflight_bv_equality(&expression, &expression, &limits, &mut || true).unwrap();
    let proof = build_bv_expr_refutation(
        &expression,
        &expression,
        Some((&limits, preflight)),
        &mut || true,
    )
    .unwrap();
    let replay = BvBlastValidateLimits {
        deadline: limits.resolution.deadline,
        max_vars: 4096,
        max_bit_lemmas: 4096,
        max_clauses: 16000,
        max_clause_literals: 64,
        max_original_literals: 64000,
        max_resolution_steps: 100,
        max_derived_literals: 10000,
        max_work: 1_000_000,
    };
    (proof, limits, replay)
}

#[test]
fn compact_replay_binds_cnf_and_rejects_changed_gates_and_refutations() {
    let (proof, limits, replay) = fixture();
    proof.validate(&limits, &replay, &mut || true).unwrap();
    for mutation in 0..5 {
        let mut changed = ExprRefutation {
            graph: proof.graph.clone(),
            dag: proof.dag.clone(),
        };
        match mutation {
            0 => changed.dag.num_vars += 1,
            1 => {
                changed.dag.original_clauses[0].1[0] =
                    Literal::from_dimacs(-changed.dag.original_clauses[0].1[0].to_dimacs())
            }
            2 => changed.graph.bit_lemmas[0].kind = BitLemmaKind::Not,
            3 => changed.dag.derived.last_mut().unwrap().rup_hints = vec![u64::MAX],
            4 => changed.dag.empty_clause_id += 1,
            _ => unreachable!(),
        }
        assert!(
            changed.validate(&limits, &replay, &mut || true).is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn compact_replay_preserves_every_caller_refusal() {
    let (proof, limits, replay) = fixture();
    let mut polls = 0;
    proof
        .validate(&limits, &replay, &mut || {
            polls += 1;
            true
        })
        .unwrap();
    for stop in 1..=polls {
        let mut calls = 0;
        assert_eq!(
            proof.validate(&limits, &replay, &mut || {
                calls += 1;
                calls != stop
            }),
            Err(BvExprExportError::Cancelled)
        );
        assert_eq!(calls, stop);
    }
    proof.validate(&limits, &replay, &mut || true).unwrap();
}

#[test]
fn compact_false_equality_and_zero_replay_budget_refuse() {
    let a = BvExpr::leaf("a", 4);
    let b = BvExpr::leaf("b", 4);
    let (proof, mut limits, replay) = fixture();
    assert!(matches!(
        validate_bv_expr_compact(&a, &b, &limits, &replay, &mut || true),
        Err(BvExprExportError::NoRefutation)
    ));
    limits.resolution.validation.max_work = 0;
    assert!(matches!(
        proof.validate(&limits, &replay, &mut || true),
        Err(BvExprExportError::ResourceLimit { .. })
    ));
}

#[test]
fn compact_replay_preserves_an_earlier_validation_deadline() {
    let (proof, mut limits, replay) = fixture();
    limits.resolution.validation.deadline = Some(Instant::now());
    assert!(proof.validate(&limits, &replay, &mut || true).is_err());
}

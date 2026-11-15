// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::bv_blast_export::BvBlastValidateLimits;

mod random_shared_dags;
mod resources;
mod shared_blast;

fn limits() -> BvExprProofLimits {
    BvExprProofLimits::conservative_external(Instant::now() + Duration::from_secs(60), 10_000)
}

fn replay_limits() -> BvBlastValidateLimits {
    BvBlastValidateLimits {
        deadline: Some(Instant::now() + Duration::from_secs(60)),
        max_vars: 4096,
        max_bit_lemmas: 4096,
        max_clauses: 32_000,
        max_clause_literals: 64,
        max_original_literals: 128_000,
        max_resolution_steps: 10_000,
        max_derived_literals: 128_000,
        max_work: 1_000_000,
    }
}

fn build_cnf(lhs: &BvExpr, rhs: &BvExpr) -> BvExprCnf {
    build_bv_expr_cnf(lhs, rhs, &limits(), &mut || true).unwrap()
}

#[test]
fn cnf_only_preserves_frozen_variable_gate_clause_and_literal_order() {
    let a = BvExpr::leaf("a", 1);
    let cnf = build_cnf(&a, &a);
    assert_eq!(cnf.width, 1);
    assert_eq!(
        cnf.vars.roles,
        vec![
            VarRole::InputLeaf { leaf: 0, bit: 0 },
            VarRole::BitEq { bit: 0 },
        ]
    );
    assert_eq!(
        cnf.bit_lemmas,
        vec![BitLemma {
            id: 0,
            kind: BitLemmaKind::XnorEq,
            out: 1,
            ins: vec![0, 0],
        }]
    );
    assert_eq!(
        cnf.clauses,
        vec![
            Clause {
                id: 0,
                lits: vec![Lit::pos(1), Lit::pos(0)],
                provenance: ClauseProvenance::BitLemmaCnf { lemma: 0 }
            },
            Clause {
                id: 1,
                lits: vec![Lit::pos(1), Lit::neg(0)],
                provenance: ClauseProvenance::BitLemmaCnf { lemma: 0 }
            },
            Clause {
                id: 2,
                lits: vec![Lit::neg(1)],
                provenance: ClauseProvenance::Disequality
            },
        ]
    );
    let graph = cnf.into_graph();
    graph
        .validate_cnf_with_limits_and_cancellation(&replay_limits(), &mut || true)
        .unwrap();
    assert!(graph.refutation.steps.is_empty());
    assert!(graph.validate_with_limits(&replay_limits()).is_err());
}

fn equalities() -> Vec<(BvExpr, BvExpr)> {
    let a = BvExpr::leaf("a", 2);
    let b = BvExpr::leaf("b", 2);
    let product = BvExpr::mul(a.clone(), b.clone());
    let compare = BvExpr::Ult(Box::new(a.clone()), Box::new(b.clone()));
    vec![
        (a.clone(), a.clone()),
        (BvExpr::const_val(5, 3), BvExpr::const_val(5, 3)),
        (BvExpr::add(a.clone(), b.clone()), BvExpr::add(b, a)),
        (
            BvExpr::extract(BvExpr::zero_ext(product.clone(), 2), 1, 0),
            product,
        ),
        (BvExpr::not(BvExpr::not(compare.clone())), compare),
    ]
}

#[test]
fn cnf_only_matches_the_producer_and_reconstructs_after_its_owners_drop() {
    for (lhs, rhs) in equalities() {
        let limits = limits();
        let preflight = preflight_bv_equality(&lhs, &rhs, &limits, &mut || true).unwrap();
        let produced =
            build_bv_expr_refutation(&lhs, &rhs, Some((&limits, preflight)), &mut || true).unwrap();
        let independent_lhs = lhs.clone();
        let independent_rhs = rhs.clone();
        let compact::ExprRefutation { graph, dag } = produced;
        let expected = graph.clone();
        drop(graph);
        drop(lhs);
        drop(rhs);
        let rebuilt = build_cnf(&independent_lhs, &independent_rhs).into_graph();
        assert_eq!(rebuilt, expected);
        // A fresh owned graph, not a producer pointer or memo, binds every SAT
        // original ID and literal before the independent refutation replay.
        assert_eq!(dag.num_vars, rebuilt.vars.len());
        assert_eq!(dag.original_clauses.len(), rebuilt.clauses.len());
        for (index, ((id, actual), expected)) in dag
            .original_clauses
            .iter()
            .zip(&rebuilt.clauses)
            .enumerate()
        {
            assert_eq!(*id, index as u64 + 1);
            assert_eq!(
                *actual,
                expected.lits.iter().map(lit_to_sat).collect::<Vec<_>>()
            );
        }
        rebuilt
            .validate_cnf_with_limits_and_cancellation(&replay_limits(), &mut || true)
            .unwrap();
        dag.validate_with_limits_and_cancellation(&limits.resolution.validation, &mut || true)
            .unwrap();
        let mut changed = dag;
        changed.derived.last_mut().unwrap().rup_hints = vec![u64::MAX];
        assert!(changed
            .validate_with_limits_and_cancellation(&limits.resolution.validation, &mut || true,)
            .is_err());
    }
}

#[test]
fn cnf_only_accepts_sat_neighbors_without_claiming_a_refutation() {
    let a = BvExpr::leaf("a", 1);
    let mut capped = limits();
    // These allowances belong to phases this API must never enter. A false
    // identity must still produce CNF instead of invoking SAT and refusing.
    capped.resolution.max_conflicts = Some(0);
    capped.resolution.max_decisions = Some(0);
    capped.resolution.max_proof_output_bytes = 0;
    capped.resolution.max_codec_bytes = 0;
    capped.resolution.max_derived_steps = 0;
    capped.resolution.max_input_bytes = 0; // no duplicate SAT-literal buffer
    capped.resolution.validation.max_work = 0;
    for rhs in [
        BvExpr::leaf("b", 1),
        BvExpr::not(a.clone()),
        BvExpr::const_val(0, 1),
    ] {
        let cnf = build_bv_expr_cnf(&a, &rhs, &capped, &mut || true).unwrap();
        assert_ne!(cnf, build_cnf(&a, &a));
        assert!(cnf
            .into_graph()
            .validate_with_limits(&replay_limits())
            .is_err());
        assert!(matches!(
            export_bv_blast_proof_expr_with_limits(&a, &rhs, &limits()),
            Err(BvExprExportError::NoRefutation)
        ));
    }
}

#[test]
fn cnf_only_source_gate_and_clause_mutations_cannot_reuse_a_proof() {
    let a = BvExpr::leaf("a", 1);
    let proof = export_bv_blast_proof_expr_with_limits(&a, &a, &limits()).unwrap();
    for rhs in [BvExpr::leaf("b", 1), BvExpr::not(a.clone())] {
        let mut changed = build_cnf(&a, &rhs).into_graph();
        changed.refutation = proof.refutation.clone();
        assert!(changed.validate_with_limits(&replay_limits()).is_err());
    }
    for mutation in 0..5 {
        let mut graph = build_cnf(&a, &a).into_graph();
        match mutation {
            0 => graph.bit_lemmas[0].kind = BitLemmaKind::Not,
            1 => graph.bit_lemmas[0].ins[0] = graph.vars.len() as u32,
            2 => graph.clauses[0].lits[0] = Lit::neg(1),
            3 => {
                graph.clauses.last_mut().unwrap().provenance =
                    ClauseProvenance::BitLemmaCnf { lemma: 0 }
            }
            4 => graph.obligation.width += 1,
            _ => unreachable!(),
        }
        assert!(
            graph
                .validate_cnf_with_limits_and_cancellation(&replay_limits(), &mut || true,)
                .is_err(),
            "mutation {mutation}"
        );
    }
    assert_ne!(
        build_cnf(&a, &a),
        build_cnf(&BvExpr::leaf("a", 2), &BvExpr::leaf("a", 2))
    );
    assert!(build_bv_expr_cnf(&a, &BvExpr::leaf("a", 2), &limits(), &mut || true).is_err());
}

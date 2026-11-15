// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn equality(zero_test: u128) -> (BvExpr, BvExpr) {
    let a = BvExpr::leaf("arithmetic_a", 8);
    let b = BvExpr::leaf("arithmetic_b", 8);
    (
        BvExpr::eq(
            BvExpr::sub(a.clone(), b.clone()),
            BvExpr::const_val(zero_test, 8),
        ),
        BvExpr::eq(a, b),
    )
}

fn arithmetic_limits() -> BvExprProofLimits {
    // The existing finite external preset, not relaxed production limits.
    BvExprProofLimits::conservative_external(Instant::now() + Duration::from_secs(60), 4096)
}

fn capture_bytes() -> Vec<u8> {
    let (lhs, rhs) = equality(0);
    let limits = arithmetic_limits();
    let graph = cnf::build_bv_expr_cnf(&lhs, &rhs, &limits, &mut || true)
        .unwrap()
        .into_graph();
    assert_eq!(
        graph
            .vars
            .roles
            .iter()
            .filter(|role| matches!(role, VarRole::InputLeaf { .. }))
            .count(),
        16
    );
    assert!(graph
        .bit_lemmas
        .iter()
        .any(|gate| gate.kind == BitLemmaKind::FullAdderCarry));
    assert!(graph.clauses.len() > 16);
    drop(graph);
    let mut produced =
        capture_bv_expr_refutation(&lhs, &rhs, &limits, &gate_limits(&limits), &mut || true)
            .unwrap();
    assert!(produced.rows.len() > 1);
    assert!(produced.rows.iter().any(|row| !row.literals.is_empty()));
    // Leave derived IDs above either source's original namespace, so the
    // arithmetic neighbor must fail proof replay, not an ID-alias check.
    let first_derived = produced.rows[0].id;
    for row in &mut produced.rows {
        row.id = row.id.checked_add(1_000_000).unwrap();
        for hint in &mut row.hints {
            if *hint >= first_derived {
                *hint = hint.checked_add(1_000_000).unwrap();
            }
        }
    }
    produced.empty_clause_id = produced.empty_clause_id.checked_add(1_000_000).unwrap();
    // JSON allocation remains outside the bounded in-memory transport API.
    serde_json::to_vec(&produced).unwrap()
}

#[test]
fn retained_multibit_arithmetic_replays_offline_without_search() {
    let bytes = capture_bytes(); // All producing expressions and proof owners drop here.
    let independent: RetainedBvRefutation = serde_json::from_slice(&bytes).unwrap();
    let (lhs, rhs) = equality(0); // Fresh owned source, not producer references.
    let mut limits = arithmetic_limits();
    limits.resolution.max_conflicts = Some(0);
    limits.resolution.max_decisions = Some(0);
    limits.resolution.max_backward_reconstruction_bytes = 0;
    limits.resolution.max_pending_deletions = 0;
    let replay = |lhs: &BvExpr, rhs: &BvExpr, payload: &RetainedBvRefutation| {
        replay_bv_expr_refutation(
            lhs,
            rhs,
            Some(payload),
            &limits,
            &gate_limits(&limits),
            &mut || true,
        )
    };
    replay(&lhs, &rhs, &independent).unwrap();
    let mut changed = independent.clone();
    changed.rows.last_mut().unwrap().hints = vec![u64::MAX];
    assert!(replay(&lhs, &rhs, &changed).is_err());
    let mut changed = independent.clone();
    changed.empty_clause_id = u64::MAX;
    assert!(replay(&lhs, &rhs, &changed).is_err());

    // At a=b, (a-b == 1) is false while (a == b) is true: a SAT neighbor.
    let (changed_lhs, changed_rhs) = equality(1);
    let neighbor =
        cnf::build_bv_expr_cnf(&changed_lhs, &changed_rhs, &limits, &mut || true).unwrap();
    assert!((neighbor.clauses.len() as u64) < independent.rows[0].id);
    drop(neighbor);
    assert!(matches!(
        replay(&changed_lhs, &changed_rhs, &independent),
        Err(BvExprExportError::RefutationNotSurfaceable(message))
            if message.starts_with("bounded resolution proof failed:")
    ));
    replay(&lhs, &rhs, &independent).unwrap();
}

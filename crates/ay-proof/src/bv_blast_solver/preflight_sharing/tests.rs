// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use crate::bv_blast_solver::*;

#[test]
fn repeated_expression_fits_actual_gate_budget_and_preserves_every_source_visit() {
    let mut expression = BvExpr::Add(
        Box::new(BvExpr::leaf("a", 8)),
        Box::new(BvExpr::leaf("b", 8)),
    );
    for _ in 0..6 {
        expression = BvExpr::Or(Box::new(expression.clone()), Box::new(expression));
    }
    let mut limits =
        BvExprProofLimits::conservative_external(Instant::now() + Duration::from_secs(30), 1000);
    limits.max_estimated_gate_work = 512;
    let mut census = BvExprPreflight::default();
    assert_eq!(
        preflight_bv_expr(&expression, &limits, &mut census, 1),
        Ok(8)
    );
    // 255 occurrences are 9 distinct nodes: a, b, the add, six ors — 8 + 8
    // leaf inputs, 24 for the ripple-carry add and 8 per or.
    assert_eq!(census.occurrences, 255);
    assert_eq!(census.nodes, 9);
    assert_eq!(census.leaf_name_bytes, 128);
    assert_eq!(census.estimated_gate_work, 88);
    let proof = export_bv_blast_proof_expr_with_limits(&expression, &expression, &limits).unwrap();
    assert!(proof.bit_lemmas.len() <= census.estimated_gate_work + 8);
    proof.validate().unwrap();
}

#[test]
fn shared_preflight_rejects_changed_width_and_zero_memory() {
    let malformed = BvExpr::Add(
        Box::new(BvExpr::leaf("x", 8)),
        Box::new(BvExpr::leaf("x", 7)),
    );
    let mut limits =
        BvExprProofLimits::conservative_external(Instant::now() + Duration::from_secs(30), 1000);
    assert!(preflight_bv_expr(&malformed, &limits, &mut BvExprPreflight::default(), 1).is_err());
    limits.max_construction_bytes = 0;
    assert!(matches!(
        preflight_bv_expr(
            &BvExpr::const_val(0, 8),
            &limits,
            &mut BvExprPreflight::default(),
            1
        ),
        Err(BvExprExportError::ResourceLimit {
            resource: "expression sharing bytes",
            ..
        })
    ));
}

#[test]
fn keys_and_occurrences_are_charged_against_one_byte_ceiling() {
    use super::Sharing;
    use std::mem::size_of;
    let leaf = BvExpr::leaf("x", 8);
    let key_bytes = 2 * size_of::<(super::Key, u32)>() + "x".len();
    let occurrence_bytes = 2 * size_of::<(usize, u32)>();
    let exact = key_bytes + occurrence_bytes;
    let mut sharing = Sharing::default();
    assert_eq!(sharing.intern(&leaf, 8, [0, 0], exact), Ok((0, true)));
    assert_eq!(sharing.bytes(), exact);
    // One byte short: the key fits, its occurrence does not.
    let refused = Err(BvExprExportError::ResourceLimit {
        resource: "expression sharing bytes",
        limit: exact - 1,
        actual: exact,
    });
    assert_eq!(
        Sharing::default().intern(&leaf, 8, [0, 0], exact - 1),
        refused
    );
    // A repeated occurrence is charged its entry and nothing for its key.
    let mut repeated = Sharing::default();
    let again = BvExpr::leaf("x", 8);
    repeated
        .intern(&leaf, 8, [0, 0], exact + occurrence_bytes)
        .unwrap();
    assert_eq!(
        repeated.intern(&again, 8, [0, 0], exact + occurrence_bytes),
        Ok((0, false))
    );
    assert_eq!(repeated.bytes(), exact + occurrence_bytes);
}

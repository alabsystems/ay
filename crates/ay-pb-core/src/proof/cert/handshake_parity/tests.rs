// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the equality-handshake parity certifier.
//!
//! Every instance here is SYNTHESIZED in this file, so the gate needs no
//! external corpus and cannot silently pass because a benchmark went missing —
//! the failure mode recorded in `vacuous-harness-window`.

use super::*;
use crate::types::{PbConstraint, PbLit, PbObjective, PbTerm};

fn term(coeff: i128, var: u32) -> PbTerm {
    PbTerm {
        coeff,
        lits: vec![PbLit {
            var,
            negated: false,
        }],
    }
}

/// The K3 family instance: nodes `1..=3` (slacks `x4 x5 x6` in objective
/// order), edges `x1 = {1,2}`, `x2 = {1,3}`, `x3 = {2,3}`, one row per node
/// `s_v + Σ_{e ∋ v} x_e = 1`. `D = 3` is odd, so `Σ s >= 1`; setting `x1 = 1`
/// satisfies rows 1 and 2 and forces `s_3 = 1`, so the optimum is `w_3`
/// when `w_3 = min w` — the tests choose weights accordingly.
fn k3_instance(weights: [i128; 3]) -> PbInstance {
    let rows = [(4u32, [1u32, 2u32]), (5, [1, 3]), (6, [2, 3])];
    let constraints: Vec<PbConstraint> = rows
        .iter()
        .map(|&(slack, edges)| PbConstraint {
            terms: vec![term(1, slack), term(1, edges[0]), term(1, edges[1])],
            rel: PbRel::Eq,
            rhs: 1,
        })
        .collect();
    PbInstance {
        num_vars: 6,
        num_constraints: 3,
        constraints,
        objective: Some(PbObjective {
            terms: (0..3).map(|i| term(weights[i], 4 + i as u32)).collect(),
        }),
    }
}

/// `x1 = 1` (edge {1,2}), `s_3 = 1`, everything else 0: feasible, objective
/// `w_3`.
const K3_INCUMBENT: [bool; 6] = [true, false, false, false, false, true];

#[test]
fn certifies_unit_k3_and_self_check_passes() {
    let instance = k3_instance([1, 1, 1]);
    let proof = certify_opt_lin_handshake_parity(&instance, &K3_INCUMBENT, 1)
        .expect("on-family unit instance must certify");
    // pol-only, `=`-split ids: 3 rows -> f 6, three derivation lines, no lift.
    assert!(proof.contains("f 6 ;"));
    assert_eq!(proof.matches("\npol ").count(), 3);
    assert!(proof.contains("conclusion BOUNDS 1 : 9 1 :"));
}

#[test]
fn certifies_weighted_k3_with_lift_line() {
    // w = (3, 4, 2): optimum = w_3 = 2 via `s_3 = 1`, floor = w_min = 2.
    let instance = k3_instance([3, 4, 2]);
    let proof = certify_opt_lin_handshake_parity(&instance, &K3_INCUMBENT, 2)
        .expect("weighted on-family instance must certify");
    // The lift line scales by w_min = 2 and adds (w_v - w_min) axioms.
    assert_eq!(proof.matches("\npol ").count(), 4);
    assert!(proof.contains("conclusion BOUNDS 2 : 10 2 :"));
}

#[test]
fn declines_even_handshake_total() {
    // Raise one RHS to 2: D = 4 is even, there is no parity argument, and the
    // certifier must decline at RECOVERY — not emit and hope.
    let mut instance = k3_instance([1, 1, 1]);
    instance.constraints[0].rhs = 2;
    // x1 = x2 = 1 satisfies row 1 (2), row 2 (1)... row 2 = s2+x1+x3 = 1 ✓,
    // row 3 = s3+x2+x3 = 1 ✓ with x3 = 0, s = 0: cost 0. Any claimed positive
    // optimum must be declined regardless of the incumbent offered.
    assert!(certify_opt_lin_handshake_parity(
        &instance,
        &[true, true, false, false, false, false],
        1
    )
    .is_none());
}

#[test]
fn declines_optimum_above_the_parity_floor() {
    // The parity floor is w_min = 1; an optimum of 3 (three slacks paid) is
    // NOT certified by this rung even when the incumbent really pays 3 —
    // the contract is optimality at the floor, nothing weaker or stranger.
    let instance = k3_instance([1, 1, 1]);
    // All slacks 1, all edges 0: every row reads 1 = 1; feasible, objective 3.
    let incumbent = [false, false, false, true, true, true];
    assert!(certify_opt_lin_handshake_parity(&instance, &incumbent, 3).is_none());
}

#[test]
fn declines_infeasible_incumbent() {
    let instance = k3_instance([1, 1, 1]);
    assert!(
        certify_opt_lin_handshake_parity(&instance, &[false; 6], 1).is_none(),
        "an incumbent violating every row must be declined"
    );
}

#[test]
fn declines_edge_variable_in_three_rows() {
    // Rewire edge x2 into row 3 as well (as an extra term): x2 now appears
    // three times; total accounting must decline.
    let mut instance = k3_instance([1, 1, 1]);
    instance.constraints[2].terms.push(term(1, 2));
    assert!(certify_opt_lin_handshake_parity(&instance, &K3_INCUMBENT, 1).is_none());
}

#[test]
fn declines_row_without_a_slack() {
    // Replace row 3's slack with a fresh edge variable: the row has no
    // objective variable and x7 appears once.
    let mut instance = k3_instance([1, 1, 1]);
    instance.constraints[2].terms[0] = term(1, 7);
    instance.num_vars = 7;
    assert!(certify_opt_lin_handshake_parity(&instance, &K3_INCUMBENT, 1).is_none());
}

#[test]
fn declines_ge_rows() {
    // Same shape but `>=` rows: the handshake equality is the argument; a
    // one-sided row has no `<=` half and no parity.
    let mut instance = k3_instance([1, 1, 1]);
    for constraint in &mut instance.constraints {
        constraint.rel = PbRel::Ge;
    }
    assert!(certify_opt_lin_handshake_parity(&instance, &K3_INCUMBENT, 1).is_none());
}

#[test]
fn declines_non_unit_row_coefficient() {
    let mut instance = k3_instance([1, 1, 1]);
    instance.constraints[0].terms[1].coeff = 2;
    assert!(certify_opt_lin_handshake_parity(&instance, &K3_INCUMBENT, 1).is_none());
}

#[test]
fn declines_negated_literal_in_row() {
    let mut instance = k3_instance([1, 1, 1]);
    instance.constraints[0].terms[1].lits[0].negated = true;
    assert!(certify_opt_lin_handshake_parity(&instance, &K3_INCUMBENT, 1).is_none());
}

#[test]
fn declines_when_objective_var_count_mismatches_rows() {
    // Add a fourth objective variable that is no row's slack: the O(1)
    // pre-gate (|objective| == #constraint) refuses before any scan.
    let mut instance = k3_instance([1, 1, 1]);
    instance
        .objective
        .as_mut()
        .expect("objective present")
        .terms
        .push(term(1, 7));
    instance.num_vars = 7;
    assert!(certify_opt_lin_handshake_parity(&instance, &K3_INCUMBENT, 1).is_none());
}

#[test]
fn emitted_bytes_replay_under_the_shared_interpreter() {
    // The entry point already self-checks; this pins the floor id arithmetic
    // (3 Eq rows -> ids 1..6 input, 7 = G, 8 = F, 9 = P) against drift.
    let instance = k3_instance([1, 1, 1]);
    let proof = certify_opt_lin_handshake_parity(&instance, &K3_INCUMBENT, 1)
        .expect("on-family instance must certify");
    assert!(super::self_check(&proof, &instance, &K3_INCUMBENT, 1, 9));
    assert!(!super::self_check(&proof, &instance, &K3_INCUMBENT, 1, 8));
}

/// A 5-row line graph family member with slack weights all 2: path
/// v1 - v2 - v3 - v4 - v5 with an extra edge closing (v1, v5) into a cycle,
/// every row `s_v + e_left + e_right = 1`, `D = 5` odd, optimum `2`.
#[test]
fn certifies_uniform_non_unit_weights() {
    // Edges x1..x5 around the cycle, slacks x6..x10.
    let edges_of = [[1u32, 5u32], [1, 2], [2, 3], [3, 4], [4, 5]];
    let constraints: Vec<PbConstraint> = (0..5)
        .map(|v| PbConstraint {
            terms: vec![
                term(1, 6 + v as u32),
                term(1, edges_of[v][0]),
                term(1, edges_of[v][1]),
            ],
            rel: PbRel::Eq,
            rhs: 1,
        })
        .collect();
    let instance = PbInstance {
        num_vars: 10,
        num_constraints: 5,
        constraints,
        objective: Some(PbObjective {
            terms: (0..5).map(|i| term(2, 6 + i as u32)).collect(),
        }),
    };
    // x1 = x3 = 1: rows 1, 2 (via x1), 3, 4 (via x3) hold with s = 0; row 5
    // (edges x4, x5) needs s_5 = 1. Objective 2 = w_min.
    let incumbent = [
        true, false, true, false, false, false, false, false, false, true,
    ];
    let proof = certify_opt_lin_handshake_parity(&instance, &incumbent, 2)
        .expect("uniform weight-2 instance must certify");
    // Uniform non-unit weights still need the lift line (scale by w_min).
    assert_eq!(proof.matches("\npol ").count(), 4);
    assert!(proof.contains("conclusion BOUNDS 2 : 14 2 :"));
}

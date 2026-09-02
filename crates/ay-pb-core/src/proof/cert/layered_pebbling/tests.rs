// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the layered group-division certifier.
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

fn ge(terms: Vec<PbTerm>, rhs: i128) -> PbConstraint {
    PbConstraint {
        terms,
        rel: PbRel::Ge,
        rhs,
    }
}

/// The three-group fan: groups `{1,2,3}`, `{4,5,6}`, `{7,8,9}`; two source
/// rows `2·Σ(G) >= 3` and one internal row `2·Σ(G3) - Σ(G1) - Σ(G2) >= 0`.
///
/// Floors: sources `ceil(3/2) = 2`, internal `ceil((2+2)/2) = 2`, total `6`.
/// The LP supports only `3/2` per group (uniform `x = 3/4` over the sources
/// and `3/4` on the internal group is feasible), so `ceil(LP*) = 5 < 6`: the
/// synthetic family reproduces the corpus family's division gap.
fn fan_instance() -> PbInstance {
    let constraints = vec![
        ge(vec![term(2, 1), term(2, 2), term(2, 3)], 3),
        ge(vec![term(2, 4), term(2, 5), term(2, 6)], 3),
        ge(
            vec![
                term(2, 7),
                term(2, 8),
                term(2, 9),
                term(-1, 1),
                term(-1, 2),
                term(-1, 3),
                term(-1, 4),
                term(-1, 5),
                term(-1, 6),
            ],
            0,
        ),
    ];
    PbInstance {
        num_vars: 9,
        num_constraints: 3,
        constraints,
        objective: Some(PbObjective {
            terms: (1..=9).map(|v| term(1, v)).collect(),
        }),
    }
}

/// Two variables true per group: every source row reads `4 >= 3`, the
/// internal row `4 - 4 >= 0`. Feasible, objective 6 = the DAG floor.
const FAN_INCUMBENT: [bool; 9] = [true, true, false, true, true, false, true, true, false];

#[test]
fn certifies_fan_and_self_check_passes() {
    let instance = fan_instance();
    let proof = certify_opt_lin_layered_pebbling(&instance, &FAN_INCUMBENT, 6)
        .expect("on-family instance must certify");
    // pol-only: one derivation per group plus the final sum; ids 4,5,6 then 7.
    assert!(proof.contains("f 3 ;"));
    assert_eq!(proof.matches("\npol ").count(), 4);
    assert!(proof.contains("pol 1 2 d ;"));
    assert!(proof.contains("pol 4 5 + 3 + 2 d ;"));
    assert!(proof.contains("pol 4 5 + 6 + ;"));
    assert!(proof.contains("conclusion BOUNDS 6 : 7 6 :"));
    assert!(!proof.contains("rup"), "the derivation must be pol-only");
}

#[test]
fn recovered_floor_matches_the_emitted_bound() {
    assert_eq!(recovered_floor(&fan_instance()), Some(6));
}

#[test]
fn recovered_floor_feeds_the_search_floor_bus() {
    let instance = fan_instance();
    let objective = instance.objective.clone().expect("objective");
    assert_eq!(
        crate::proof::recovered_structural_search_floor(&instance, &objective),
        Some(6),
        "the DAG floor must reach the pre-search bus"
    );
    // A caller optimizing any OTHER objective must get None, fail-closed.
    let other = PbObjective {
        terms: (1..=9).map(|v| term(2, v)).collect(),
    };
    assert_eq!(
        crate::proof::recovered_structural_search_floor(&instance, &other),
        None
    );
}

#[test]
fn declines_optimum_above_the_dag_floor() {
    // Pay one extra variable: feasible (rows only gain), objective 7. The
    // floor is 6, the contract is optimality at the floor, so this declines
    // rather than publishing a bound the derivation does not reach.
    let mut incumbent = FAN_INCUMBENT;
    incumbent[2] = true;
    assert!(certify_opt_lin_layered_pebbling(&fan_instance(), &incumbent, 7).is_none());
}

#[test]
fn declines_infeasible_incumbent() {
    assert!(
        certify_opt_lin_layered_pebbling(&fan_instance(), &[false; 9], 6).is_none(),
        "an incumbent violating the source rows must be declined"
    );
}

#[test]
fn declines_variable_in_two_groups() {
    // x1 with coefficient 2 in row 2 as well: not a partition.
    let mut instance = fan_instance();
    instance.constraints[1].terms.push(term(2, 1));
    assert!(certify_opt_lin_layered_pebbling(&instance, &FAN_INCUMBENT, 6).is_none());
    assert_eq!(recovered_floor(&instance), None);
}

#[test]
fn declines_partial_predecessor_overlap() {
    // Drop one variable of G2 from the internal row's negative side: the
    // union is no longer exact, the predecessor sum would not cancel, and the
    // emitted row would be WEAKER than the self-check expects. Decline at
    // recovery, not at replay.
    let mut instance = fan_instance();
    let internal = &mut instance.constraints[2];
    internal.terms.retain(|t| {
        t.lits[0].var != 6 || t.coeff != -1 // remove `-1 x6`
    });
    assert!(certify_opt_lin_layered_pebbling(&instance, &FAN_INCUMBENT, 6).is_none());
    assert_eq!(recovered_floor(&instance), None);
}

#[test]
fn declines_cyclic_group_references() {
    // Two groups, each subtracting the other: no topological order exists,
    // and the floor recurrence is unsound on a cycle. Must decline.
    let constraints = vec![
        ge(vec![term(2, 1), term(2, 2), term(-1, 3), term(-1, 4)], 1),
        ge(vec![term(2, 3), term(2, 4), term(-1, 1), term(-1, 2)], 1),
    ];
    let instance = PbInstance {
        num_vars: 4,
        num_constraints: 2,
        constraints,
        objective: Some(PbObjective {
            terms: (1..=4).map(|v| term(1, v)).collect(),
        }),
    };
    assert_eq!(recovered_floor(&instance), None);
    assert!(certify_opt_lin_layered_pebbling(&instance, &[true, false, true, false], 2).is_none());
}

#[test]
fn declines_self_referential_row() {
    // A row subtracting its OWN group variable: the recurrence would count
    // `x1` on both sides. Must decline.
    let instance = PbInstance {
        num_vars: 2,
        num_constraints: 1,
        constraints: vec![ge(vec![term(2, 1), term(2, 2), term(-1, 1)], 1)],
        objective: Some(PbObjective {
            terms: vec![term(1, 1), term(1, 2)],
        }),
    };
    // x1's owner is row 0 itself. (The `+2`/`-1` split parses; ownership does
    // not.)
    assert_eq!(recovered_floor(&instance), None);
}

#[test]
fn declines_duplicate_negative_literal() {
    // `-1 x4 -1 x4` instead of `-1 x4 -1 x5`: the occurrence count still
    // reaches |G2| = 3 (x4 twice + x6 once... it does not — but even where it
    // WOULD, the union is wrong and the predecessor sum cannot cancel). The
    // per-row duplicate check must decline.
    let mut instance = fan_instance();
    let internal = &mut instance.constraints[2];
    for t in internal.terms.iter_mut() {
        if t.coeff == -1 && t.lits[0].var == 5 {
            t.lits[0].var = 4;
        }
    }
    assert_eq!(recovered_floor(&instance), None);
    assert!(certify_opt_lin_layered_pebbling(&instance, &FAN_INCUMBENT, 6).is_none());
}

#[test]
fn declines_foreign_row_coefficients() {
    // A `+3` coefficient anywhere is off-family.
    let mut instance = fan_instance();
    instance.constraints[0].terms[0].coeff = 3;
    assert!(certify_opt_lin_layered_pebbling(&instance, &FAN_INCUMBENT, 6).is_none());
}

#[test]
fn declines_eq_rows() {
    let mut instance = fan_instance();
    instance.constraints[0].rel = PbRel::Eq;
    assert!(certify_opt_lin_layered_pebbling(&instance, &FAN_INCUMBENT, 6).is_none());
}

#[test]
fn declines_negated_literal_in_row() {
    let mut instance = fan_instance();
    instance.constraints[0].terms[0].lits[0].negated = true;
    assert!(certify_opt_lin_layered_pebbling(&instance, &FAN_INCUMBENT, 6).is_none());
}

#[test]
fn declines_non_unit_objective() {
    let mut instance = fan_instance();
    instance.objective.as_mut().expect("objective").terms[0].coeff = 2;
    assert!(certify_opt_lin_layered_pebbling(&instance, &FAN_INCUMBENT, 6).is_none());
    assert_eq!(recovered_floor(&instance), None);
}

#[test]
fn declines_objective_missing_a_variable() {
    // |objective| != #variable: the O(1) header gate refuses before any work.
    let mut instance = fan_instance();
    instance.objective.as_mut().expect("objective").terms.pop();
    assert!(certify_opt_lin_layered_pebbling(&instance, &FAN_INCUMBENT, 6).is_none());
}

#[test]
fn declines_pure_vertex_cover_rows() {
    // `odd_cycle_cover`'s family shares the header gate; the O(1) first-row
    // probe (leading coefficient 2) must separate the families before any
    // O(n) work. A `+1 x1 +1 x2 >= 1` first row declines here.
    let instance = PbInstance {
        num_vars: 2,
        num_constraints: 1,
        constraints: vec![ge(vec![term(1, 1), term(1, 2)], 1)],
        objective: Some(PbObjective {
            terms: vec![term(1, 1), term(1, 2)],
        }),
    };
    assert_eq!(recovered_floor(&instance), None);
}

#[test]
fn declines_overflowing_floor_arithmetic() {
    // An rhs near i128::MAX would wrap the recurrence; checked arithmetic
    // must decline rather than forge a floor.
    let mut instance = fan_instance();
    instance.constraints[0].rhs = i128::MAX;
    instance.constraints[2].rhs = i128::MAX;
    assert_eq!(recovered_floor(&instance), None);
}

// ---------------------------------------------------------------------------
// Constructed witness: the optimal incumbent the recovery can BUILD.
// ---------------------------------------------------------------------------

#[test]
fn constructed_witness_attains_the_floor_and_certifies() {
    let instance = fan_instance();
    let (witness, value) =
        constructed_optimum_witness(&instance).expect("on-family instance must construct");
    assert_eq!(value, 6, "the witness value must be the DAG floor");
    // First f(r) = 2 variables of each group, in row term order.
    assert_eq!(witness, FAN_INCUMBENT.to_vec());
    // The constructed point must be a full-fledged incumbent: feasible and
    // certifiable by the same entry point a search incumbent uses.
    assert!(incumbent_is_feasible(&instance, &witness));
    assert!(
        certify_opt_lin_layered_pebbling(&instance, &witness, value).is_some(),
        "the constructed witness must feed the certificate route"
    );
}

#[test]
fn constructed_witness_reaches_the_portfolio_wrapper() {
    let instance = fan_instance();
    let objective = instance.objective.clone().expect("objective");
    assert_eq!(
        crate::proof::layered_pebbling_constructed_optimum(&instance, &objective)
            .map(|(_, value)| value),
        Some(6)
    );
    // A caller optimizing any OTHER objective must get None, fail-closed.
    let other = PbObjective {
        terms: (1..=9).map(|v| term(2, v)).collect(),
    };
    assert_eq!(
        crate::proof::layered_pebbling_constructed_optimum(&instance, &other),
        None
    );
}

#[test]
fn constructed_witness_handles_the_deeper_dag() {
    // The 5-group DAG from `emitted_bytes_replay_for_a_deeper_dag`: floors
    // 2,2,2,2,3, total 11. The sink needs THREE of its group true, so the
    // construction is exercised beyond the uniform-2 case.
    let g = |base: u32| vec![term(2, base), term(2, base + 1), term(2, base + 2)];
    let sub = |base: u32| vec![term(-1, base), term(-1, base + 1), term(-1, base + 2)];
    let mut internal3 = g(7);
    internal3.extend(sub(1));
    internal3.extend(sub(4));
    let mut internal5 = g(13);
    internal5.extend(sub(7));
    internal5.extend(sub(10));
    let instance = PbInstance {
        num_vars: 15,
        num_constraints: 5,
        constraints: vec![
            ge(g(1), 3),
            ge(g(4), 3),
            ge(internal3, 0),
            ge(g(10), 3),
            ge(internal5, 1),
        ],
        objective: Some(PbObjective {
            terms: (1..=15).map(|v| term(1, v)).collect(),
        }),
    };
    let (witness, value) =
        constructed_optimum_witness(&instance).expect("the deeper DAG must construct");
    assert_eq!(value, 11);
    assert!(incumbent_is_feasible(&instance, &witness));
    assert!(certify_opt_lin_layered_pebbling(&instance, &witness, 11).is_some());
}

#[test]
fn constructed_witness_declines_a_floor_exceeding_the_group() {
    // `2·x1 >= 3` forces f = 2 in a group of size 1: by the floor's soundness
    // the instance is INFEASIBLE, and the constructor must decline rather
    // than fabricate a point (which could not verify anyway).
    let instance = PbInstance {
        num_vars: 1,
        num_constraints: 1,
        constraints: vec![ge(vec![term(2, 1)], 3)],
        objective: Some(PbObjective {
            terms: vec![term(1, 1)],
        }),
    };
    assert_eq!(constructed_optimum_witness(&instance), None);
}

#[test]
fn constructed_witness_declines_off_family() {
    // The vertex-cover first row that separates this family from
    // `odd_cycle_cover` must decline the constructor exactly as it declines
    // the floor.
    let instance = PbInstance {
        num_vars: 2,
        num_constraints: 1,
        constraints: vec![ge(vec![term(1, 1), term(1, 2)], 1)],
        objective: Some(PbObjective {
            terms: vec![term(1, 1), term(1, 2)],
        }),
    };
    assert_eq!(constructed_optimum_witness(&instance), None);
}

// ---------------------------------------------------------------------------
// Adversarial battery: the emitted BYTES, mutated, must fail the self-check.
// ---------------------------------------------------------------------------

/// Extracts the cited floor id from the emitted conclusion line.
fn floor_id_of(proof: &str) -> u64 {
    let line = proof
        .lines()
        .find(|l| l.starts_with("conclusion BOUNDS"))
        .expect("conclusion line");
    line.split_whitespace()
        .nth(4)
        .expect("hint id")
        .parse()
        .expect("numeric hint id")
}

#[test]
fn mutated_emissions_fail_the_shared_replay() {
    let instance = fan_instance();
    let proof = certify_opt_lin_layered_pebbling(&instance, &FAN_INCUMBENT, 6)
        .expect("on-family instance must certify");
    let floor_id = floor_id_of(&proof);
    assert!(
        self_check(&proof, &instance, &FAN_INCUMBENT, 6, floor_id),
        "the untouched emission must replay"
    );

    // Each mutation models one defect class the pinned checker also rejects
    // (measured on the prototype: all seven exit 1). The self-check must
    // refuse them WITHOUT the checker in the loop.
    let mutations: [(&str, &str, &str); 5] = [
        ("wrong divisor", "pol 1 2 d ;", "pol 1 3 d ;"),
        (
            "dropped group in final sum",
            "pol 4 5 + 6 + ;",
            "pol 4 6 + ;",
        ),
        (
            "wrong predecessor id",
            "pol 4 5 + 3 + 2 d ;",
            "pol 4 4 + 3 + 2 d ;",
        ),
        (
            "raw row cited for derived",
            "pol 4 5 + 6 + ;",
            "pol 1 5 + 6 + ;",
        ),
        ("no division at the source", "pol 1 2 d ;", "pol 1 ;"),
    ];
    for (label, from, to) in mutations {
        assert!(proof.contains(from), "{label}: template drifted");
        let mutated = proof.replacen(from, to, 1);
        assert!(
            !self_check(&mutated, &instance, &FAN_INCUMBENT, 6, floor_id),
            "{label}: the mutated bytes must fail the replay"
        );
    }

    // A claimed floor ABOVE the derivation must also fail.
    assert!(
        !self_check(&proof, &instance, &FAN_INCUMBENT, 7, floor_id),
        "optimum 7 against a degree-6 floor row must fail"
    );
}

#[test]
fn emitted_bytes_replay_for_a_deeper_dag() {
    // Three layers: two sources feed a middle group, the middle group and a
    // third source feed the sink. Exercises predecessor ordering and the
    // topological emission on a DAG that is not a single fan.
    //   G1 = {1,2,3}, G2 = {4,5,6}   sources, floor 2 each
    //   G3 = {7,8,9}                 2Σ - G1 - G2 >= 0, floor 2
    //   G4 = {10,11,12}              source, floor 2
    //   G5 = {13,14,15}              2Σ - G3 - G4 >= 1, floor ceil(5/2) = 3
    // Total floor = 11.
    let g = |base: u32| vec![term(2, base), term(2, base + 1), term(2, base + 2)];
    let sub = |base: u32| vec![term(-1, base), term(-1, base + 1), term(-1, base + 2)];
    let mut internal3 = g(7);
    internal3.extend(sub(1));
    internal3.extend(sub(4));
    let mut internal5 = g(13);
    internal5.extend(sub(7));
    internal5.extend(sub(10));
    let instance = PbInstance {
        num_vars: 15,
        num_constraints: 5,
        constraints: vec![
            ge(g(1), 3),
            ge(g(4), 3),
            ge(internal3, 0),
            ge(g(10), 3),
            ge(internal5, 1),
        ],
        objective: Some(PbObjective {
            terms: (1..=15).map(|v| term(1, v)).collect(),
        }),
    };
    assert_eq!(recovered_floor(&instance), Some(11));
    // Two true in every group but three in the sink: source rows 4 >= 3,
    // internal G3 4 - 4 >= 0, sink 6 - 4 >= 1. Objective 11.
    let mut incumbent = [false; 15];
    for base in [0usize, 3, 6, 9, 12] {
        incumbent[base] = true;
        incumbent[base + 1] = true;
    }
    incumbent[14] = true;
    let proof = certify_opt_lin_layered_pebbling(&instance, &incumbent, 11)
        .expect("the deeper DAG must certify");
    assert!(proof.contains("conclusion BOUNDS 11 :"));
}

//! Unit tests for the pseudo-Boolean propagator (`super::PbPropagator`).
//! Extracted verbatim from `propagation.rs` to keep the production module readable.

use super::*;

fn lit(var: u32) -> PbLit {
    PbLit {
        var,
        negated: false,
    }
}

fn not(var: u32) -> PbLit {
    PbLit { var, negated: true }
}

fn term(coeff: i128, lit: PbLit) -> PbTerm {
    PbTerm {
        coeff,
        lits: vec![lit],
    }
}

fn linear_term(coeff: i128, var: u32) -> PbTerm {
    term(coeff, lit(var))
}

fn negated_term(coeff: i128, var: u32) -> PbTerm {
    term(coeff, not(var))
}

fn ge_constraint(terms: Vec<PbTerm>, rhs: i128) -> PbConstraint {
    PbConstraint {
        terms,
        rel: PbRel::Ge,
        rhs,
    }
}

fn eval_pb_lit(lit: Lit, assignment: &[bool]) -> bool {
    let idx = usize::try_from(lit.unsigned_abs() - 1)
        .expect("1-based DIMACS variable index must fit in usize");
    let value = assignment[idx];
    if lit > 0 {
        value
    } else {
        !value
    }
}

fn eval_constraint(constraint: &PbConstraint, assignment: &[bool]) -> bool {
    let lhs: i128 = constraint
        .terms
        .iter()
        .filter(|term| {
            term.lits
                .iter()
                .all(|lit| eval_pb_lit(pb_lit_to_dimacs(*lit), assignment))
        })
        .map(|term| i128::from(term.coeff))
        .sum();

    match constraint.rel {
        PbRel::Ge => lhs >= i128::from(constraint.rhs),
        PbRel::Eq => lhs == i128::from(constraint.rhs),
    }
}

fn clause_is_valid(constraint: &PbConstraint, clause: &[Lit], num_vars: usize) -> bool {
    let limit = 1usize
        .checked_shl(u32::try_from(num_vars).expect("num_vars fits in u32"))
        .expect("test assignment space must fit in usize");

    (0..limit).all(|mask| {
        let assignment: Vec<bool> = (0..num_vars)
            .map(|bit| (mask & (1usize << bit)) != 0)
            .collect();
        let clause_false = clause.iter().all(|&lit| !eval_pb_lit(lit, &assignment));
        !clause_false || !eval_constraint(constraint, &assignment)
    })
}

fn assert_exact_coefficient_bounds(constraint: &PropConstraint) {
    let exact_watched_sum = constraint.terms[..constraint.watch_end]
        .iter()
        .map(|term| term.coeff)
        .fold(0i128, i128::saturating_add);
    let exact_max_watched = constraint.terms[..constraint.watch_end]
        .iter()
        .map(|term| term.coeff)
        .max()
        .unwrap_or(0);
    let exact_max_unwatched = constraint.terms[constraint.watch_end..]
        .iter()
        .map(|term| term.coeff)
        .max()
        .unwrap_or(0);

    assert_eq!(constraint.watched_sum, exact_watched_sum);
    assert_eq!(constraint.max_watched_coeff, exact_max_watched);
    assert_eq!(constraint.max_unwatched_coeff, exact_max_unwatched);
    assert!(
        constraint.watched_sum
            >= constraint
                .degree
                .saturating_add(constraint.max_unwatched_coeff),
        "watched-slack invariant must hold with exact coefficient bounds"
    );
}

#[test]
fn test_interruptible_constructor_stops_while_normalizing_exact_max_wide_row() {
    let constraint = ge_constraint(
        (1..=65_536).map(|var| linear_term(1, var)).collect(),
        65_536,
    );
    let calls = Cell::new(0usize);
    let mut stop_on_first_poll = || {
        calls.set(calls.get() + 1);
        true
    };
    let mut propagator = PbPropagator::new();

    assert_eq!(
        propagator.add_from_pb_constraint_interruptible(&constraint, &mut stop_on_first_poll),
        Err(())
    );
    assert_eq!(
        propagator.num_constraints(),
        0,
        "interruption during constructor normalization must not import the wide row"
    );
    assert_eq!(
        calls.get(),
        1,
        "wide-row constructor should poll before finishing normalization"
    );
}

#[test]
fn test_interruptible_constructor_stops_before_sparse_high_var_assignment_growth() {
    const HIGH_VAR: u32 = 1_048_576;
    let constraint = ge_constraint(
        vec![
            linear_term(4, 2),
            linear_term(3, HIGH_VAR),
            linear_term(2, 7),
        ],
        5,
    );
    let calls = Cell::new(0usize);
    let mut stop_at_dense_assignment_guard = || {
        let next = calls.get() + 1;
        calls.set(next);
        next >= 3
    };
    let mut propagator = PbPropagator::new();

    assert_eq!(
        propagator
            .add_from_pb_constraint_interruptible(&constraint, &mut stop_at_dense_assignment_guard),
        Err(())
    );
    assert_eq!(calls.get(), 3);
    assert_eq!(propagator.num_constraints(), 0);
    assert!(
        propagator.assignment.values.is_empty(),
        "constructor should stop before dense assignment growth for sparse high variable ids"
    );
    assert!(
        propagator.watches.is_empty(),
        "constructor should not grow watch lists after assignment-growth interruption"
    );
}

#[test]
fn test_interruptible_constructor_stops_before_sparse_high_var_watch_growth() {
    const HIGH_VAR: u32 = 1_048_576;
    let constraint = ge_constraint(
        vec![
            linear_term(4, 2),
            linear_term(3, HIGH_VAR),
            linear_term(2, 7),
        ],
        5,
    );
    let calls = Cell::new(0usize);
    let mut stop_at_watch_capacity_guard = || {
        let next = calls.get() + 1;
        calls.set(next);
        next >= 4
    };
    let mut propagator = PbPropagator::new();

    assert_eq!(
        propagator
            .add_from_pb_constraint_interruptible(&constraint, &mut stop_at_watch_capacity_guard),
        Err(())
    );
    assert_eq!(calls.get(), 4);
    assert_eq!(propagator.num_constraints(), 0);
    assert_eq!(
        propagator.assignment.values.len(),
        usize::try_from(HIGH_VAR).expect("test variable index fits in usize")
    );
    assert!(
        propagator.watches.is_empty(),
        "constructor should stop before dense watch-list growth for sparse high variable ids"
    );
}

#[test]
fn test_interruptible_constructor_sorts_like_standard_import_order() {
    let mut terms = vec![
        PropTerm { lit: 3, coeff: 2 },
        PropTerm { lit: -2, coeff: 4 },
        PropTerm { lit: 1, coeff: 4 },
        PropTerm { lit: -1, coeff: 4 },
        PropTerm { lit: 2, coeff: 1 },
    ];
    let mut never_stop = || false;

    sort_prop_terms_interruptible(&mut terms, &mut never_stop).expect("sort should not interrupt");

    assert_eq!(
        terms,
        vec![
            PropTerm { lit: -1, coeff: 4 },
            PropTerm { lit: 1, coeff: 4 },
            PropTerm { lit: -2, coeff: 4 },
            PropTerm { lit: 3, coeff: 2 },
            PropTerm { lit: 2, coeff: 1 },
        ]
    );
}

#[test]
fn test_normalized_shape_classification() {
    let mut prop = PbPropagator::new();
    let clause = prop
        .add_constraint(&[linear_term(1, 1), linear_term(1, 2)], PbRel::Ge, 1)
        .expect("clause should be added");
    let cardinality = prop
        .add_constraint(
            &[linear_term(1, 3), linear_term(1, 4), linear_term(1, 5)],
            PbRel::Ge,
            2,
        )
        .expect("cardinality should be added");
    let weighted = prop
        .add_constraint(&[linear_term(2, 6), linear_term(1, 7)], PbRel::Ge, 2)
        .expect("weighted constraint should be added");

    assert_eq!(prop.constraints[clause].shape, ConstraintShape::Clause);
    assert_eq!(
        prop.constraints[cardinality].shape,
        ConstraintShape::UnitCardinality
    );
    assert_eq!(prop.constraints[weighted].shape, ConstraintShape::Weighted);
}

#[test]
fn test_clause_shape_matches_weighted_equivalent_propagation() {
    let mut clause_prop = PbPropagator::new();
    let _ = clause_prop.add_constraint(&[linear_term(1, 1), linear_term(1, 2)], PbRel::Ge, 1);

    let mut weighted_prop = PbPropagator::new();
    let _ = weighted_prop.add_constraint(&[linear_term(2, 1), linear_term(2, 2)], PbRel::Ge, 2);

    assert_eq!(
        clause_prop.assign_literal(-1, 1),
        weighted_prop.assign_literal(-1, 1)
    );
}

#[test]
fn test_ternary_clause_fast_path_swaps_without_unwatched_scan() {
    let mut prop = PbPropagator::new();
    let cid = prop
        .add_constraint(
            &[linear_term(1, 1), linear_term(1, 2), linear_term(1, 3)],
            PbRel::Ge,
            1,
        )
        .expect("ternary clause should be added");

    assert_eq!(prop.constraints[cid].shape, ConstraintShape::TernaryClause);
    assert_eq!(prop.assign_literal(-1, 1), PropResult::Ok);

    let x1_watch = lit_index(1).expect("literal has watch index");
    let x3_watch = lit_index(3).expect("literal has watch index");
    assert!(!prop.watches[x1_watch].contains(&cid));
    assert!(prop.watches[x3_watch].contains(&cid));
    assert_eq!(prop.propagation_stats().unwatched_replacement_candidates, 0);
}

#[test]
fn test_ternary_clause_import_and_rebuild_skip_slack_recalculation() {
    let mut prop = PbPropagator::new();
    let cid = prop
        .add_constraint(
            &[linear_term(1, 1), linear_term(1, 2), linear_term(1, 3)],
            PbRel::Ge,
            1,
        )
        .expect("ternary clause should be added");

    assert_eq!(prop.constraints[cid].shape, ConstraintShape::TernaryClause);
    assert_eq!(prop.constraints[cid].watch_end, 2);
    assert_eq!(prop.propagation_stats().slack_recalculations, 0);

    assert_eq!(prop.assign_literal(-1, 1), PropResult::Ok);
    prop.unassign_literal(-1);

    assert_eq!(prop.constraints[cid].watch_end, 2);
    assert_eq!(prop.propagate(), PropResult::Ok);
    assert_eq!(prop.propagation_stats().slack_recalculations, 0);
}

#[test]
fn test_ternary_clause_swap_remove_rechecks_moved_watch() {
    let mut prop = PbPropagator::new();
    let first = prop
        .add_constraint(
            &[linear_term(1, 1), linear_term(1, 2), linear_term(1, 3)],
            PbRel::Ge,
            1,
        )
        .expect("first ternary clause should be added");
    let second = prop
        .add_constraint(
            &[linear_term(1, 1), linear_term(1, 4), linear_term(1, 5)],
            PbRel::Ge,
            1,
        )
        .expect("second ternary clause should be added");

    assert_eq!(prop.assign_literal(-1, 1), PropResult::Ok);

    let x1_watch = lit_index(1).expect("literal has watch index");
    let x3_watch = lit_index(3).expect("literal has watch index");
    let x5_watch = lit_index(5).expect("literal has watch index");
    assert!(!prop.watches[x1_watch].contains(&first));
    assert!(!prop.watches[x1_watch].contains(&second));
    assert!(prop.watches[x3_watch].contains(&first));
    assert!(prop.watches[x5_watch].contains(&second));
    assert_eq!(prop.propagation_stats().unwatched_replacement_candidates, 0);
}

#[test]
fn test_ternary_clause_fast_path_propagates_after_two_false() {
    let mut prop = PbPropagator::new();
    let cid = prop
        .add_constraint(
            &[linear_term(1, 1), linear_term(1, 2), linear_term(1, 3)],
            PbRel::Ge,
            1,
        )
        .expect("ternary clause should be added");

    assert_eq!(prop.assign_literal(-1, 1), PropResult::Ok);
    let result = prop.assign_literal(-2, 1);
    match result {
        PropResult::Propagated(lit, reason, result_cid) => {
            assert_eq!(lit, 3);
            assert_eq!(result_cid, cid);
            assert_eq!(reason, vec![3, 2, 1]);
            let constraint = prop
                .get_constraint_pb(cid)
                .expect("constraint should remain available");
            assert!(clause_is_valid(&constraint, &reason, 3));
        }
        other => panic!("expected ternary propagation, got {other:?}"),
    }
    assert_eq!(prop.propagation_stats().unwatched_replacement_candidates, 0);
}

#[test]
fn test_ternary_clause_fast_path_conflicts_all_false() {
    let mut prop = PbPropagator::new();
    let cid = prop
        .add_constraint(
            &[linear_term(1, 1), linear_term(1, 2), linear_term(1, 3)],
            PbRel::Ge,
            1,
        )
        .expect("ternary clause should be added");

    assert_eq!(prop.assign_literal(-1, 1), PropResult::Ok);
    assert!(matches!(
        prop.assign_literal(-2, 1),
        PropResult::Propagated(3, _, _)
    ));

    let result = prop.assign_literal(-3, 1);
    match result {
        PropResult::Conflict(reason, result_cid) => {
            assert_eq!(result_cid, cid);
            assert_eq!(reason, vec![3, 2, 1]);
            let constraint = prop
                .get_constraint_pb(cid)
                .expect("constraint should remain available");
            assert!(clause_is_valid(&constraint, &reason, 3));
        }
        other => panic!("expected ternary conflict, got {other:?}"),
    }
    assert_eq!(prop.propagation_stats().unwatched_replacement_candidates, 0);
}

#[test]
fn test_ternary_clause_interruptible_uses_same_fast_path() {
    let mut prop = PbPropagator::new();
    let cid = prop
        .add_constraint(
            &[linear_term(1, 1), linear_term(1, 2), linear_term(1, 3)],
            PbRel::Ge,
            1,
        )
        .expect("ternary clause should be added");

    assert_eq!(
        prop.assign_literal_interruptible(-1, 1, || false),
        PropResult::Ok
    );
    let result = prop.assign_literal_interruptible(-2, 1, || false);
    match result {
        PropResult::Propagated(lit, reason, result_cid) => {
            assert_eq!(lit, 3);
            assert_eq!(result_cid, cid);
            assert_eq!(reason, vec![3, 2, 1]);
        }
        other => panic!("expected ternary propagation, got {other:?}"),
    }
    assert_eq!(prop.propagation_stats().unwatched_replacement_candidates, 0);
}

#[test]
fn test_ternary_clause_fast_path_rejects_duplicate_literals() {
    let mut prop = PbPropagator::new();
    let cid = prop
        .add_constraint(
            &[linear_term(1, 1), linear_term(1, 1), linear_term(1, 2)],
            PbRel::Ge,
            1,
        )
        .expect("duplicate-literal clause should be added");

    assert_eq!(prop.constraints[cid].shape, ConstraintShape::Weighted);
}

#[test]
fn test_unit_cardinality_shape_matches_weighted_equivalent_conflict() {
    let mut cardinality_prop = PbPropagator::new();
    let _ = cardinality_prop.add_constraint(&[linear_term(1, 1), linear_term(1, 2)], PbRel::Ge, 2);

    let mut weighted_prop = PbPropagator::new();
    let _ = weighted_prop.add_constraint(&[linear_term(2, 1), linear_term(2, 2)], PbRel::Ge, 4);

    assert_eq!(
        cardinality_prop.assign_literal(-1, 1),
        weighted_prop.assign_literal(-1, 1)
    );
}

#[test]
fn test_unit_cardinality_shape_matches_weighted_equivalent_propagation() {
    let mut cardinality_prop = PbPropagator::new();
    let _ = cardinality_prop.add_constraint(
        &[linear_term(1, 1), linear_term(1, 2), linear_term(1, 3)],
        PbRel::Ge,
        2,
    );

    let mut weighted_prop = PbPropagator::new();
    let _ = weighted_prop.add_constraint(
        &[linear_term(2, 1), linear_term(2, 2), linear_term(2, 3)],
        PbRel::Ge,
        4,
    );

    assert_eq!(
        cardinality_prop.assign_literal(-1, 1),
        weighted_prop.assign_literal(-1, 1)
    );
}

#[test]
fn test_clause_shape_reason_matches_weighted_equivalent_after_watch_swap() {
    let mut clause_prop = PbPropagator::new();
    clause_prop.disable_blind_arming_for_test();
    let clause_cid = clause_prop
        .add_constraint(
            &[linear_term(1, 1), linear_term(1, 2), linear_term(1, 3)],
            PbRel::Ge,
            1,
        )
        .expect("clause should be added");

    let mut weighted_prop = PbPropagator::new();
    weighted_prop.disable_blind_arming_for_test();
    let _ = weighted_prop.add_constraint(
        &[linear_term(2, 1), linear_term(2, 2), linear_term(2, 3)],
        PbRel::Ge,
        2,
    );

    assert_eq!(
        clause_prop.assign_literal(-1, 1),
        weighted_prop.assign_literal(-1, 1)
    );

    let result = clause_prop.assign_literal(-2, 1);
    assert_eq!(result, weighted_prop.assign_literal(-2, 1));
    match result {
        PropResult::Propagated(lit, reason, _) => {
            assert_eq!(lit, 3);
            assert_eq!(reason, vec![3, 2, 1]);
            let constraint = clause_prop
                .get_constraint_pb(clause_cid)
                .expect("constraint should exist");
            assert!(clause_is_valid(&constraint, &reason, 3));
        }
        other => panic!("expected clause propagation, got {other:?}"),
    }
}

#[test]
fn test_unit_cardinality_shape_reason_matches_weighted_equivalent() {
    let mut cardinality_prop = PbPropagator::new();
    let cardinality_cid = cardinality_prop
        .add_constraint(
            &[
                linear_term(1, 1),
                linear_term(1, 2),
                linear_term(1, 3),
                linear_term(1, 4),
            ],
            PbRel::Ge,
            3,
        )
        .expect("cardinality should be added");

    let mut weighted_prop = PbPropagator::new();
    let _ = weighted_prop.add_constraint(
        &[
            linear_term(2, 1),
            linear_term(2, 2),
            linear_term(2, 3),
            linear_term(2, 4),
        ],
        PbRel::Ge,
        6,
    );

    let result = cardinality_prop.assign_literal(-1, 1);
    assert_eq!(result, weighted_prop.assign_literal(-1, 1));
    match result {
        PropResult::Propagated(lit, reason, _) => {
            assert_eq!(lit, 2);
            assert_eq!(reason, vec![2, 1]);
            let constraint = cardinality_prop
                .get_constraint_pb(cardinality_cid)
                .expect("constraint should exist");
            assert!(clause_is_valid(&constraint, &reason, 4));
        }
        other => panic!("expected cardinality propagation, got {other:?}"),
    }

    let result = cardinality_prop.assign_literal(-2, 1);
    assert_eq!(result, weighted_prop.assign_literal(-2, 1));
    match result {
        PropResult::Conflict(reason, _) => {
            assert_eq!(reason, vec![1, 2]);
            let constraint = cardinality_prop
                .get_constraint_pb(cardinality_cid)
                .expect("constraint should exist");
            assert!(clause_is_valid(&constraint, &reason, 4));
        }
        other => panic!("expected cardinality conflict, got {other:?}"),
    }
}

#[test]
fn test_non_unit_clause_equivalent_stays_on_weighted_reason_path() {
    let mut clause_prop = PbPropagator::new();
    clause_prop.disable_blind_arming_for_test();
    let _ = clause_prop.add_constraint(
        &[linear_term(1, 1), linear_term(1, 2), linear_term(1, 3)],
        PbRel::Ge,
        1,
    );

    let mut weighted_prop = PbPropagator::new();
    weighted_prop.disable_blind_arming_for_test();
    let weighted_cid = weighted_prop
        .add_constraint(
            &[linear_term(2, 1), linear_term(2, 2), linear_term(2, 3)],
            PbRel::Ge,
            2,
        )
        .expect("weighted constraint should be added");

    assert_eq!(
        weighted_prop.constraints[weighted_cid].shape,
        ConstraintShape::Weighted
    );
    assert_eq!(
        clause_prop.assign_literal(-1, 1),
        weighted_prop.assign_literal(-1, 1)
    );

    let result = weighted_prop.assign_literal(-2, 1);
    assert_eq!(result, clause_prop.assign_literal(-2, 1));
    match result {
        PropResult::Propagated(lit, reason, _) => {
            assert_eq!(lit, 3);
            assert_eq!(reason, vec![3, 2, 1]);
        }
        other => panic!("expected weighted propagation, got {other:?}"),
    }

    let stats = weighted_prop.propagation_stats();
    assert_eq!(stats.weighted_checks, 2);
    assert_eq!(stats.clause_checks, 0);
    assert_eq!(stats.unit_cardinality_checks, 0);
}

#[test]
fn test_non_unit_cardinality_equivalent_stays_on_weighted_reason_path() {
    let mut cardinality_prop = PbPropagator::new();
    let _ = cardinality_prop.add_constraint(
        &[
            linear_term(1, 1),
            linear_term(1, 2),
            linear_term(1, 3),
            linear_term(1, 4),
        ],
        PbRel::Ge,
        3,
    );

    let mut weighted_prop = PbPropagator::new();
    let weighted_cid = weighted_prop
        .add_constraint(
            &[
                linear_term(2, 1),
                linear_term(2, 2),
                linear_term(2, 3),
                linear_term(2, 4),
            ],
            PbRel::Ge,
            6,
        )
        .expect("weighted constraint should be added");

    assert_eq!(
        weighted_prop.constraints[weighted_cid].shape,
        ConstraintShape::Weighted
    );

    let result = weighted_prop.assign_literal(-1, 1);
    assert_eq!(result, cardinality_prop.assign_literal(-1, 1));
    match result {
        PropResult::Propagated(lit, reason, _) => {
            assert_eq!(lit, 2);
            assert_eq!(reason, vec![2, 1]);
        }
        other => panic!("expected weighted propagation, got {other:?}"),
    }

    let result = weighted_prop.assign_literal(-2, 1);
    assert_eq!(result, cardinality_prop.assign_literal(-2, 1));
    match result {
        PropResult::Conflict(reason, _) => {
            assert_eq!(reason, vec![1, 2]);
        }
        other => panic!("expected weighted conflict, got {other:?}"),
    }

    let stats = weighted_prop.propagation_stats();
    assert_eq!(stats.weighted_checks, 2);
    assert_eq!(stats.clause_checks, 0);
    assert_eq!(stats.unit_cardinality_checks, 0);
}

#[test]
fn test_normalized_scaled_cardinality_stays_on_weighted_reason_path() {
    let mut cardinality_prop = PbPropagator::new();
    let _ = cardinality_prop.add_constraint(
        &[negated_term(1, 1), linear_term(1, 2), linear_term(1, 3)],
        PbRel::Ge,
        2,
    );

    let mut weighted_prop = PbPropagator::new();
    let weighted_cid = weighted_prop
        .add_constraint(
            &[linear_term(-2, 1), linear_term(2, 2), linear_term(2, 3)],
            PbRel::Ge,
            2,
        )
        .expect("weighted constraint should be added");

    assert_eq!(
        weighted_prop.constraints[weighted_cid].shape,
        ConstraintShape::Weighted
    );

    let result = weighted_prop.assign_literal(1, 1);
    assert_eq!(result, cardinality_prop.assign_literal(1, 1));
    match result {
        PropResult::Propagated(lit, reason, _) => {
            assert_eq!(lit, 2);
            assert_eq!(reason, vec![2, -1]);
        }
        other => panic!("expected weighted propagation, got {other:?}"),
    }

    let stats = weighted_prop.propagation_stats();
    assert_eq!(stats.weighted_checks, 1);
    assert_eq!(stats.clause_checks, 0);
    assert_eq!(stats.unit_cardinality_checks, 0);
}

#[test]
fn test_weighted_sufficient_slack_shortcut_survives_backtrack_repair() {
    let mut prop = PbPropagator::new();
    let cid = prop
        .add_constraint(
            &[linear_term(3, 1), linear_term(2, 2), linear_term(1, 3)],
            PbRel::Ge,
            2,
        )
        .expect("weighted constraint should be added");

    assert_eq!(prop.constraints[cid].shape, ConstraintShape::Weighted);
    assert_eq!(prop.constraints[cid].max_watched_coeff, 3);
    assert!(prop.constraints[cid].slack >= prop.constraints[cid].max_watched_coeff);

    assert_eq!(prop.propagate(), PropResult::Ok);
    let stats = prop.propagation_stats();
    assert_eq!(stats.weighted_checks, 1);
    assert_eq!(stats.weighted_slack_shortcuts, 1);
    assert_eq!(stats.clause_checks, 0);
    assert_eq!(stats.unit_cardinality_checks, 0);

    assert_eq!(prop.assign_literal(-3, 1), PropResult::Ok);
    prop.unassign_literal(-3);
    assert_eq!(prop.propagate(), PropResult::Ok);

    let constraint = &prop.constraints[cid];
    assert_eq!(constraint.max_watched_coeff, 3);
    assert_eq!(constraint.max_unwatched_coeff, 1);
    assert!(constraint.slack >= constraint.max_watched_coeff);
    let stats = prop.propagation_stats();
    assert_eq!(stats.weighted_checks, 2);
    assert_eq!(stats.weighted_slack_shortcuts, 2);
    assert_eq!(stats.weighted_slack_shortcuts, stats.weighted_checks);
}

#[test]
fn test_perturbed_unwatched_order_uses_strongest_swap_for_weighted_slack() {
    let mut prop = PbPropagator::new();
    let cid = prop
        .add_constraint(
            &[
                linear_term(8, 1),
                linear_term(7, 4),
                linear_term(3, 2),
                linear_term(1, 3),
            ],
            PbRel::Ge,
            2,
        )
        .expect("weighted constraint should be added");

    prop.constraints[cid].terms = vec![
        PropTerm { lit: 1, coeff: 8 },
        PropTerm { lit: 2, coeff: 3 },
        PropTerm { lit: 3, coeff: 1 },
        PropTerm { lit: 4, coeff: 7 },
    ];
    prop.constraints[cid].watch_end = 2;
    prop.constraints[cid].watched_sum = 11;
    prop.constraints[cid].max_watched_coeff = 8;
    prop.constraints[cid].max_unwatched_coeff = 7;
    prop.recalculate_slack(cid);
    prop.rebuild_all_watches();

    assert_eq!(prop.assign_literal(-1, 1), PropResult::Ok);

    let constraint = &prop.constraints[cid];
    let watched_lits: Vec<Lit> = constraint.terms[..constraint.watch_end]
        .iter()
        .map(|term| term.lit)
        .collect();
    assert!(watched_lits.contains(&4));
    assert!(!watched_lits.contains(&3));
    assert!(
        constraint.watched_sum >= constraint.degree + constraint.max_unwatched_coeff,
        "strongest replacement keeps the watched-slack invariant after perturbed swaps"
    );

    assert_eq!(prop.propagate(), PropResult::Ok);
    let stats = prop.propagation_stats();
    assert_eq!(stats.unwatched_replacement_candidates, 2);
    assert_eq!(stats.unwatched_replacement_value_checks, 2);
    assert_eq!(stats.weighted_checks, 2);
    assert_eq!(stats.weighted_slack_shortcuts, 2);
}

#[test]
fn test_unwatched_replacement_stops_after_cached_max_candidate() {
    let mut prop = PbPropagator::new();
    let cid = prop
        .add_constraint(
            &[
                linear_term(10, 1),
                linear_term(9, 2),
                linear_term(8, 3),
                linear_term(7, 4),
                linear_term(6, 5),
                linear_term(5, 6),
            ],
            PbRel::Ge,
            2,
        )
        .expect("weighted constraint should be added");

    let constraint = &prop.constraints[cid];
    assert_eq!(constraint.watch_end, 2);
    assert!(constraint.terms.len() - constraint.watch_end > 1);
    assert_eq!(
        constraint.terms[constraint.watch_end].coeff,
        constraint.max_unwatched_coeff
    );

    assert_eq!(prop.assign_literal(-1, 1), PropResult::Ok);

    let constraint = &prop.constraints[cid];
    let watched_lits: Vec<Lit> = constraint.terms[..constraint.watch_end]
        .iter()
        .map(|term| term.lit)
        .collect();
    assert!(watched_lits.contains(&3));
    assert!(
        constraint.watched_sum >= constraint.degree + constraint.max_unwatched_coeff,
        "max-candidate swap must preserve the watched-slack invariant"
    );

    let stats = prop.propagation_stats();
    assert_eq!(stats.unwatched_replacement_candidates, 1);
    assert_eq!(stats.weighted_slack_shortcuts, stats.weighted_checks);
}

#[test]
fn test_weighted_swaps_use_replacement_scan_hint_after_false_unwatched_max() {
    const TERMS: u32 = 64;
    const SWAPS: u32 = 8;

    let mut prop = PbPropagator::new();
    let terms: Vec<PbTerm> = (1..=TERMS)
        .map(|var| linear_term(i128::from(TERMS + 1 - var), var))
        .collect();
    let cid = prop
        .add_constraint(&terms, PbRel::Ge, 2)
        .expect("weighted constraint should be added");

    // This test exercises the watched-swap replacement machinery; force the
    // constraint out of counting mode (its large coefficients would
    // otherwise auto-select counting, which has no swaps).
    prop.set_constraint_counting_for_test(cid, false);

    assert_eq!(prop.constraints[cid].shape, ConstraintShape::Weighted);
    assert_eq!(prop.constraints[cid].watch_end, 2);
    assert_exact_coefficient_bounds(&prop.constraints[cid]);

    for var in 1..=SWAPS {
        let falsified_lit = -i32::try_from(var).expect("test literal fits in i32");
        assert_eq!(prop.assign_literal(falsified_lit, 1), PropResult::Ok);
        assert_exact_coefficient_bounds(&prop.constraints[cid]);
    }

    let stats = prop.propagation_stats();
    let old_full_tail_candidates = 1 + u64::from(SWAPS - 1) * u64::from(TERMS - 2);
    let expected_candidates = u64::from(SWAPS);
    assert_eq!(
        stats.unwatched_replacement_candidates, expected_candidates,
        "replacement scan hints should skip false unwatched maxima from earlier swaps"
    );
    assert!(
        stats.unwatched_replacement_candidates < old_full_tail_candidates,
        "replacement search should avoid the former full-tail scan pattern"
    );
    assert_eq!(
        stats.unwatched_replacement_value_checks, expected_candidates,
        "each scanned higher false candidate plus the first safe non-false candidate is checked"
    );
    assert_eq!(stats.coefficient_bound_recomputations, 0);
    assert_eq!(stats.weighted_checks, u64::from(SWAPS));
    assert_eq!(stats.weighted_slack_shortcuts, u64::from(SWAPS));
}

#[test]
fn test_weighted_replacement_scan_hint_wraps_to_sufficient_prefix_candidate() {
    let mut prop = PbPropagator::new();
    let cid = prop
        .add_constraint(
            &[
                linear_term(10, 1),
                linear_term(9, 2),
                linear_term(8, 3),
                linear_term(1, 4),
            ],
            PbRel::Ge,
            2,
        )
        .expect("weighted constraint should be added");

    assert_eq!(prop.constraints[cid].shape, ConstraintShape::Weighted);
    assert_eq!(prop.constraints[cid].watch_end, 2);
    prop.constraints[cid].weighted_replacement_scan_hint = prop.constraints[cid].watch_end + 1;

    assert_eq!(prop.assign_literal(-1, 1), PropResult::Ok);

    let watched_lits: Vec<Lit> = prop.constraints[cid].terms[..prop.constraints[cid].watch_end]
        .iter()
        .map(|term| term.lit)
        .collect();
    assert!(watched_lits.contains(&3));
    assert_exact_coefficient_bounds(&prop.constraints[cid]);

    let stats = prop.propagation_stats();
    assert_eq!(
        stats.unwatched_replacement_candidates, 2,
        "scan must wrap after the hinted suffix fails to satisfy the invariant"
    );
    assert_eq!(stats.unwatched_replacement_value_checks, 2);
    assert_eq!(stats.weighted_checks, 1);
    assert_eq!(stats.weighted_slack_shortcuts, 1);
}

#[test]
fn test_weighted_rejects_below_threshold_replacement_preserves_bounds() {
    let mut prop = PbPropagator::new();
    prop.disable_blind_arming_for_test();
    let cid = prop
        .add_constraint(
            &[linear_term(15, 1), linear_term(10, 2), linear_term(8, 3)],
            PbRel::Ge,
            17,
        )
        .expect("weighted constraint should be added");

    assert_eq!(prop.constraints[cid].shape, ConstraintShape::Weighted);
    assert_eq!(prop.constraints[cid].watch_end, 2);
    assert_exact_coefficient_bounds(&prop.constraints[cid]);

    match prop.assign_literal(-2, 1) {
        PropResult::Propagated(lit, reason, result_cid) => {
            assert_eq!(lit, 1);
            assert_eq!(result_cid, cid);
            let constraint = prop
                .get_constraint_pb(cid)
                .expect("constraint should be available");
            assert!(clause_is_valid(&constraint, &reason, 3));
        }
        other => {
            panic!("expected exact weighted propagation after rejected swap, got {other:?}")
        }
    }

    let constraint = &prop.constraints[cid];
    assert_exact_coefficient_bounds(constraint);
    let watched_lits: Vec<Lit> = constraint.terms[..constraint.watch_end]
        .iter()
        .map(|term| term.lit)
        .collect();
    assert!(watched_lits.contains(&2));
    assert!(!watched_lits.contains(&3));
    assert!(
        constraint.watched_sum >= constraint.degree + constraint.max_unwatched_coeff,
        "rejecting a below-threshold replacement must preserve watched coefficient bounds"
    );

    let stats = prop.propagation_stats();
    assert_eq!(stats.unwatched_replacement_candidates, 1);
    assert_eq!(stats.unwatched_replacement_value_checks, 1);
    assert_eq!(stats.weighted_checks, 1);
    assert_eq!(stats.weighted_no_replacement_shortcuts, 0);
    assert_eq!(stats.weighted_exact_slack_scans, 1);
}

#[test]
fn test_weighted_swap_watch_end_two_does_not_emit_invalid_conflict() {
    let mut prop = PbPropagator::new();
    prop.disable_blind_arming_for_test();
    let cid = prop
        .add_constraint(
            &[
                linear_term(10, 1),
                linear_term(4, 2),
                linear_term(3, 3),
                linear_term(3, 4),
            ],
            PbRel::Ge,
            8,
        )
        .expect("weighted constraint should be added");

    assert_eq!(prop.constraints[cid].watch_end, 2);

    match prop.assign_literal(-1, 1) {
        PropResult::Conflict(reason, _) => {
            let constraint = prop
                .get_constraint_pb(cid)
                .expect("constraint should be available");
            assert!(
                clause_is_valid(&constraint, &reason, 4),
                "must not emit invalid conflict reason {reason:?}"
            );
        }
        PropResult::Propagated(_, reason, _) => {
            let constraint = prop
                .get_constraint_pb(cid)
                .expect("constraint should be available");
            assert!(clause_is_valid(&constraint, &reason, 4));
        }
        PropResult::Ok => {}
        PropResult::Interrupted => panic!("unexpected interruption"),
    }
}

#[test]
fn test_weighted_no_replacement_propagates_without_exact_slack_scan() {
    let mut prop = PbPropagator::new();
    prop.disable_blind_arming_for_test();
    let cid = prop
        .add_constraint(
            &[linear_term(5, 1), linear_term(4, 2), linear_term(1, 3)],
            PbRel::Ge,
            4,
        )
        .expect("weighted constraint should be added");

    assert_eq!(prop.constraints[cid].shape, ConstraintShape::Weighted);
    assert_eq!(prop.constraints[cid].watch_end, 2);
    assert_eq!(prop.assign_literal(-3, 1), PropResult::Ok);

    let result = prop.assign_literal(-1, 1);
    match result {
        PropResult::Propagated(lit, reason, result_cid) => {
            assert_eq!(lit, 2);
            assert_eq!(result_cid, cid);
            let constraint = prop
                .get_constraint_pb(cid)
                .expect("constraint should be available");
            assert!(clause_is_valid(&constraint, &reason, 3));
        }
        other => panic!("expected weighted no-replacement propagation, got {other:?}"),
    }

    let stats = prop.propagation_stats();
    assert_eq!(stats.unwatched_replacement_candidates, 1);
    assert_eq!(stats.weighted_checks, 1);
    assert_eq!(stats.weighted_no_replacement_shortcuts, 1);
    assert_eq!(stats.weighted_exact_slack_scans, 0);
    assert_eq!(stats.weighted_slack_shortcuts, 0);
    assert_eq!(stats.clause_checks, 0);
    assert_eq!(stats.unit_cardinality_checks, 0);
}

#[test]
fn test_weighted_no_replacement_counter_stays_zero_on_replacement_path() {
    let mut prop = PbPropagator::new();
    let cid = prop
        .add_constraint(
            &[
                linear_term(10, 1),
                linear_term(9, 2),
                linear_term(8, 3),
                linear_term(7, 4),
            ],
            PbRel::Ge,
            2,
        )
        .expect("weighted constraint should be added");

    assert_eq!(prop.constraints[cid].shape, ConstraintShape::Weighted);
    assert_eq!(prop.constraints[cid].watch_end, 2);
    assert_eq!(prop.assign_literal(-1, 1), PropResult::Ok);

    let stats = prop.propagation_stats();
    assert_eq!(stats.unwatched_replacement_candidates, 1);
    assert_eq!(stats.weighted_checks, 1);
    assert_eq!(stats.weighted_slack_shortcuts, 1);
    assert_eq!(stats.weighted_no_replacement_shortcuts, 0);
    assert_eq!(stats.weighted_exact_slack_scans, 0);
}

#[test]
fn test_event_driven_weighted_swap_updates_slack_without_recalculation() {
    let mut prop = PbPropagator::new();
    let cid = prop
        .add_constraint(
            &[
                linear_term(10, 1),
                linear_term(9, 2),
                linear_term(8, 3),
                linear_term(7, 4),
                linear_term(6, 5),
            ],
            PbRel::Ge,
            2,
        )
        .expect("weighted constraint should be added");

    assert_eq!(prop.constraints[cid].watch_end, 2);
    assert_eq!(prop.constraints[cid].slack, 17);
    assert_eq!(prop.propagation_stats().slack_recalculations, 1);

    assert_eq!(prop.assign_literal(-1, 1), PropResult::Ok);

    let constraint = &prop.constraints[cid];
    let watched_lits: Vec<Lit> = constraint.terms[..constraint.watch_end]
        .iter()
        .map(|term| term.lit)
        .collect();
    assert!(watched_lits.contains(&2));
    assert!(watched_lits.contains(&3));
    assert_eq!(constraint.slack, 15);
    assert!(
        constraint.watched_sum >= constraint.degree + constraint.max_unwatched_coeff,
        "incremental slack update must preserve the weighted shortcut invariant"
    );

    let stats = prop.propagation_stats();
    assert_eq!(stats.slack_recalculations, 1);
    assert_eq!(stats.coefficient_bound_recomputations, 0);
    assert_eq!(stats.unwatched_replacement_candidates, 1);
    assert_eq!(stats.weighted_checks, 1);
    assert_eq!(stats.weighted_slack_shortcuts, 1);
    assert_eq!(stats.clause_checks, 0);
    assert_eq!(stats.unit_cardinality_checks, 0);
}

#[test]
fn test_rebuild_uses_true_unwatched_max_after_skipped_swap_candidate() {
    let mut prop = PbPropagator::new();
    let cid = prop
        .add_constraint(
            &[
                linear_term(5, 1),
                linear_term(4, 2),
                linear_term(1, 3),
                linear_term(1, 4),
                linear_term(1, 5),
            ],
            PbRel::Ge,
            4,
        )
        .expect("weighted constraint should be added");

    assert_eq!(prop.constraints[cid].watch_end, 2);
    assert_eq!(prop.assign_literal(-3, 1), PropResult::Ok);

    let result = prop.assign_literal(-1, 1);
    match result {
        PropResult::Propagated(lit, reason, result_cid) => {
            assert_eq!(lit, 2);
            assert_eq!(result_cid, cid);
            let constraint = prop
                .get_constraint_pb(cid)
                .expect("constraint should exist");
            assert!(clause_is_valid(&constraint, &reason, 5));
        }
        other => panic!("expected propagation after swapping past false x3, got {other:?}"),
    }

    prop.unassign_literals(&[-1, -3]);

    let constraint = &prop.constraints[cid];
    assert!(
        constraint.watched_sum >= constraint.degree + constraint.max_unwatched_coeff,
        "rebuild must account for max unwatched coeff even after swaps perturb term order"
    );
    assert_eq!(prop.propagate(), PropResult::Ok);
}

#[test]
fn test_unit_cardinality_reason_omits_true_literals() {
    let mut prop = PbPropagator::new();
    let cid = prop
        .add_constraint(
            &[
                linear_term(1, 1),
                linear_term(1, 2),
                linear_term(1, 3),
                linear_term(1, 4),
                linear_term(1, 5),
            ],
            PbRel::Ge,
            3,
        )
        .expect("cardinality should be added");

    assert_eq!(prop.assign_literal(5, 1), PropResult::Ok);
    assert_eq!(prop.assign_literal(-1, 1), PropResult::Ok);
    let result = prop.assign_literal(-2, 1);

    match result {
        PropResult::Propagated(lit, reason, _) => {
            assert_eq!(lit, 3);
            assert_eq!(reason, vec![3, 2, 1]);
            assert!(!reason.contains(&-5));
            assert!(!reason.contains(&5));
            let constraint = prop
                .get_constraint_pb(cid)
                .expect("constraint should exist");
            assert!(clause_is_valid(&constraint, &reason, 5));
        }
        other => panic!("expected cardinality propagation, got {other:?}"),
    }
}

#[test]
fn test_unit_cardinality_sufficient_watched_slack_shortcuts_after_backtrack() {
    let mut prop = PbPropagator::new();
    let cid = prop
        .add_constraint(
            &[
                linear_term(1, 1),
                linear_term(1, 2),
                linear_term(1, 3),
                linear_term(1, 4),
                linear_term(1, 5),
            ],
            PbRel::Ge,
            3,
        )
        .expect("cardinality should be added");

    assert_eq!(
        prop.constraints[cid].shape,
        ConstraintShape::UnitCardinality
    );
    assert_eq!(prop.propagate(), PropResult::Ok);
    assert_eq!(prop.assign_literal(-1, 1), PropResult::Ok);
    prop.unassign_literal(-1);
    assert_eq!(prop.assign_literal(-2, 1), PropResult::Ok);

    let stats = prop.propagation_stats();
    assert_eq!(stats.unit_cardinality_checks, 1);
    assert_eq!(stats.unit_cardinality_slack_shortcuts, 1);
    assert_eq!(stats.unit_cardinality_watch_shortcuts, 2);
    assert_eq!(stats.unit_cardinality_full_scans, 0);
    assert_eq!(stats.weighted_checks, 0);
}

#[test]
fn test_unit_cardinality_event_swap_shortcuts_without_full_scan() {
    let mut prop = PbPropagator::new();
    let cid = prop
        .add_constraint(
            &[
                linear_term(1, 1),
                linear_term(1, 2),
                linear_term(1, 3),
                linear_term(1, 4),
                linear_term(1, 5),
            ],
            PbRel::Ge,
            3,
        )
        .expect("cardinality should be added");

    assert_eq!(
        prop.constraints[cid].shape,
        ConstraintShape::UnitCardinality
    );
    assert_eq!(prop.constraints[cid].watch_end, 4);

    assert_eq!(prop.assign_literal(-1, 1), PropResult::Ok);

    let watched_lits: Vec<Lit> = prop.constraints[cid].terms[..prop.constraints[cid].watch_end]
        .iter()
        .map(|term| term.lit)
        .collect();
    assert!(!watched_lits.contains(&1));
    assert!(watched_lits.contains(&5));
    assert!(!prop.watches[lit_index(1).expect("literal has watch index")].contains(&cid));
    assert!(prop.watches[lit_index(5).expect("literal has watch index")].contains(&cid));

    let stats = prop.propagation_stats();
    assert_eq!(stats.unit_cardinality_watch_shortcuts, 1);
    assert_eq!(stats.unit_cardinality_full_scans, 0);
    assert_eq!(stats.coefficient_bound_recomputations, 0);
    assert_eq!(stats.weighted_checks, 0);
}

#[test]
fn test_unit_cardinality_full_scan_stops_after_degree_exceeded() {
    let mut prop = PbPropagator::new();
    let cid = prop
        .add_constraint(
            &[
                linear_term(1, 1),
                linear_term(1, 2),
                linear_term(1, 3),
                linear_term(1, 4),
                linear_term(1, 5),
                linear_term(1, 6),
                linear_term(1, 7),
                linear_term(1, 8),
            ],
            PbRel::Ge,
            3,
        )
        .expect("cardinality should be added");

    assert_eq!(
        prop.constraints[cid].shape,
        ConstraintShape::UnitCardinality
    );
    assert_eq!(prop.constraints[cid].watch_end, 4);
    assert_eq!(
        prop.assignment.assign_literal(-1, 1),
        AssignOutcome::NewlyAssigned
    );
    prop.constraints[cid].slack = 0;

    assert_eq!(prop.propagate_constraint(cid), PropResult::Ok);

    let stats = prop.propagation_stats();
    assert_eq!(stats.unit_cardinality_full_scans, 1);
    assert_eq!(
        stats.unit_cardinality_scan_terms, 5,
        "scan should stop as soon as non-false count exceeds the degree"
    );
    assert_eq!(stats.weighted_checks, 0);
}

#[test]
fn test_native_helper_assignment_value_mirror_updates_assign_and_unassign() {
    let mut assignment = Assignment::default();

    assert_eq!(assignment.native_value(2), PB_NATIVE_VALUE_UNASSIGNED);
    assert_eq!(assignment.native_value(-2), PB_NATIVE_VALUE_UNASSIGNED);
    assert!(assignment.native_value_mirrors_assignment(2));
    assert!(assignment.native_value_mirrors_assignment(-2));

    assert_eq!(
        assignment.assign_literal(2, 1),
        AssignOutcome::NewlyAssigned
    );
    assert_eq!(assignment.native_value(2), PB_NATIVE_VALUE_TRUE);
    assert_eq!(assignment.native_value(-2), PB_NATIVE_VALUE_FALSE);
    assert!(assignment.native_value_mirrors_assignment(2));
    assert!(assignment.native_value_mirrors_assignment(-2));

    assert!(assignment.unassign_literal(2));
    assert_eq!(assignment.native_value(2), PB_NATIVE_VALUE_UNASSIGNED);
    assert_eq!(assignment.native_value(-2), PB_NATIVE_VALUE_UNASSIGNED);
    assert!(assignment.native_value_mirrors_assignment(2));
    assert!(assignment.native_value_mirrors_assignment(-2));
}

#[test]
fn test_unit_cardinality_native_lits_follow_watch_swaps() {
    let mut prop = PbPropagator::new();
    let cid = prop
        .add_constraint(
            &[
                linear_term(1, 1),
                linear_term(1, 2),
                linear_term(1, 3),
                linear_term(1, 4),
                linear_term(1, 5),
            ],
            PbRel::Ge,
            3,
        )
        .expect("cardinality should be added");

    {
        assert!(prop.constraints[cid].native_lits.is_empty());
    }
    assert_eq!(prop.assign_literal(-1, 1), PropResult::Ok);
    {
        assert!(prop.constraints[cid].native_lits.is_empty());
    }

    prop.unassign_literal(1);
    {
        assert!(prop.constraints[cid].native_lits.is_empty());
    }
}

#[test]
fn test_unit_cardinality_native_helper_counts_only_after_scalar_validation() {
    let mut prop = PbPropagator::new();
    let cid = prop
        .add_constraint(
            &[
                linear_term(1, 1),
                linear_term(1, 2),
                linear_term(1, 3),
                linear_term(1, 4),
                linear_term(1, 5),
            ],
            PbRel::Ge,
            3,
        )
        .expect("cardinality should be added");

    prop.set_native_code_helper_validation_enabled(true);
    assert_eq!(
        prop.assignment.assign_literal(-1, 1),
        AssignOutcome::NewlyAssigned
    );
    assert_eq!(
        prop.assignment.assign_literal(-2, 1),
        AssignOutcome::NewlyAssigned
    );
    prop.constraints[cid].slack = 0;

    match prop.propagate_constraint(cid) {
        PropResult::Propagated(lit, reason, result_cid) => {
            assert_eq!(lit, 3);
            assert_eq!(result_cid, cid);
            assert_eq!(reason, vec![3, 1, 2]);
        }
        other => panic!("expected validated native helper propagation, got {other:?}"),
    }

    let native_stats = prop.native_helper_stats();
    assert_eq!(prop.native_code_helper_applications(), u64::from(false));
    assert_eq!(native_stats.useful_native_applications(), u64::from(false));
    assert_eq!(native_stats.evaluation_attempts, 1);
    assert_eq!(native_stats.scalar_confirmation_checks, 1);
    assert_eq!(native_stats.scalar_shadow_applications, u64::from(true));
    assert_eq!(native_stats.native_apply_attempts, u64::from(false));
    assert_eq!(native_stats.native_apply_confirmations, u64::from(false));
    assert_eq!(native_stats.native_value_buffer_fills, 0);
    assert_eq!(native_stats.compile_attempts, u64::from(false));
    assert_eq!(native_stats.compile_successes, u64::from(false));
    assert_eq!(native_stats.compile_failures, 0);
}

#[test]
fn test_unit_cardinality_native_helper_mismatch_deopts_to_scalar_fallback() {
    let mut prop = PbPropagator::new();
    let cid = prop
        .add_constraint(
            &[
                linear_term(1, 1),
                linear_term(1, 2),
                linear_term(1, 3),
                linear_term(1, 4),
                linear_term(1, 5),
            ],
            PbRel::Ge,
            3,
        )
        .expect("cardinality should be added");

    prop.set_native_code_helper_validation_enabled(true);
    prop.force_next_native_code_helper_mismatch_for_test();
    assert_eq!(
        prop.assignment.assign_literal(-1, 1),
        AssignOutcome::NewlyAssigned
    );
    assert_eq!(
        prop.assignment.assign_literal(-2, 1),
        AssignOutcome::NewlyAssigned
    );
    prop.constraints[cid].slack = 0;

    match prop.propagate_constraint(cid) {
        PropResult::Propagated(lit, reason, result_cid) => {
            assert_eq!(lit, 3);
            assert_eq!(result_cid, cid);
            assert_eq!(reason, vec![3, 1, 2]);
        }
        other => panic!("expected scalar fallback propagation, got {other:?}"),
    }

    assert_eq!(prop.native_code_helper_applications(), 0);
    let native_stats = prop.native_helper_stats();
    assert_eq!(native_stats.evaluation_attempts, 1);
    assert_eq!(native_stats.scalar_confirmation_checks, 1);
    assert_eq!(native_stats.scalar_shadow_applications, 0);
    assert_eq!(native_stats.native_apply_attempts, u64::from(false));
    assert_eq!(native_stats.native_apply_confirmations, 0);
    assert_eq!(native_stats.native_value_buffer_fills, 0);
    assert_eq!(native_stats.deopts, 1);
    assert_eq!(native_stats.scalar_fallbacks, 1);

    assert_eq!(
        prop.propagate_constraint(cid),
        PropResult::Propagated(3, vec![3, 1, 2], cid)
    );
    assert_eq!(prop.native_code_helper_applications(), 0);
    assert_eq!(prop.native_helper_stats().scalar_fallbacks, 2);
}

#[test]
fn test_native_helper_stats_start_at_zero() {
    let prop = PbPropagator::new();

    assert_eq!(prop.native_code_helper_applications(), 0);
    assert_eq!(prop.native_helper_stats(), PbNativeHelperStats::default());
}

#[test]
fn test_weighted_constraint_records_native_helper_scalar_fallback() {
    let mut prop = PbPropagator::new();
    prop.disable_blind_arming_for_test();
    let cid = prop
        .add_constraint(
            &[linear_term(2, 1), linear_term(3, 2), linear_term(5, 3)],
            PbRel::Ge,
            4,
        )
        .expect("weighted constraint should be added");

    prop.set_native_code_helper_validation_enabled(true);
    assert_eq!(
        prop.assignment.assign_literal(-1, 1),
        AssignOutcome::NewlyAssigned
    );
    prop.constraints[cid].slack = 0;

    let _ = prop.propagate_constraint(cid);

    let native_stats = prop.native_helper_stats();
    assert_eq!(native_stats.scalar_fallbacks, 1);
    assert_eq!(native_stats.evaluation_attempts, 0);
    assert_eq!(native_stats.scalar_shadow_applications, 0);
    assert_eq!(native_stats.useful_native_applications(), 0);
}

#[test]
fn test_unit_cardinality_event_no_replacement_threshold_uses_reason_scan_only() {
    let mut prop = PbPropagator::new();
    let cid = prop
        .add_constraint(
            &[
                linear_term(1, 1),
                linear_term(1, 2),
                linear_term(1, 3),
                linear_term(1, 4),
                linear_term(1, 5),
            ],
            PbRel::Ge,
            3,
        )
        .expect("cardinality should be added");

    assert_eq!(prop.assign_literal(-5, 1), PropResult::Ok);
    match prop.assign_literal(-1, 1) {
        PropResult::Propagated(lit, reason, result_cid) => {
            assert_eq!(lit, 2);
            assert_eq!(result_cid, cid);
            assert_eq!(reason, vec![2, 1, 5]);
        }
        other => panic!("expected cardinality propagation, got {other:?}"),
    }

    let stats = prop.propagation_stats();
    assert_eq!(stats.unit_cardinality_watch_shortcuts, 1);
    assert_eq!(stats.unit_cardinality_full_scans, 0);
    assert_eq!(stats.weighted_checks, 0);
}

#[test]
fn test_unit_cardinality_event_shortcut_survives_backtrack_repair() {
    let mut prop = PbPropagator::new();
    let cid = prop
        .add_constraint(
            &[
                linear_term(1, 1),
                linear_term(1, 2),
                linear_term(1, 3),
                linear_term(1, 4),
                linear_term(1, 5),
                linear_term(1, 6),
            ],
            PbRel::Ge,
            3,
        )
        .expect("cardinality should be added");

    assert_eq!(prop.assign_literal(-1, 1), PropResult::Ok);
    let rebuilds_before = prop.rebuild_count();
    prop.unassign_literal(-1);
    assert_eq!(prop.rebuild_count(), rebuilds_before);
    assert_eq!(prop.propagate(), PropResult::Ok);
    assert_eq!(prop.rebuild_count(), rebuilds_before);

    assert_eq!(prop.assign_literal(-2, 1), PropResult::Ok);

    let watched_lits: Vec<Lit> = prop.constraints[cid].terms[..prop.constraints[cid].watch_end]
        .iter()
        .map(|term| term.lit)
        .collect();
    assert_eq!(watched_lits.len(), 4);
    assert!(watched_lits
        .iter()
        .all(|&lit| prop.value(lit) != LitValue::False));
    assert_eq!(prop.propagation_stats().unit_cardinality_full_scans, 0);
}

#[test]
fn test_clause_shape_shortcut_matches_weighted_equivalent_sat() {
    let mut clause_prop = PbPropagator::new();
    let _ = clause_prop.add_constraint(
        &[linear_term(1, 1), linear_term(1, 2), linear_term(1, 3)],
        PbRel::Ge,
        1,
    );

    let mut weighted_prop = PbPropagator::new();
    let _ = weighted_prop.add_constraint(
        &[linear_term(2, 1), linear_term(2, 2), linear_term(2, 3)],
        PbRel::Ge,
        2,
    );

    assert_eq!(clause_prop.assign_literal(2, 1), PropResult::Ok);
    assert_eq!(weighted_prop.assign_literal(2, 1), PropResult::Ok);
    assert_eq!(clause_prop.propagate(), weighted_prop.propagate());

    let clause_stats = clause_prop.propagation_stats();
    let weighted_stats = weighted_prop.propagation_stats();
    assert_eq!(clause_stats.clause_checks, 1);
    assert_eq!(clause_stats.clause_watch_shortcuts, 1);
    assert_eq!(weighted_stats.weighted_checks, 1);
}

#[test]
fn test_clause_shape_shortcut_matches_weighted_equivalent_non_unit() {
    let mut clause_prop = PbPropagator::new();
    let _ = clause_prop.add_constraint(
        &[linear_term(1, 1), linear_term(1, 2), linear_term(1, 3)],
        PbRel::Ge,
        1,
    );

    let mut weighted_prop = PbPropagator::new();
    let _ = weighted_prop.add_constraint(
        &[linear_term(2, 1), linear_term(2, 2), linear_term(2, 3)],
        PbRel::Ge,
        2,
    );

    assert_eq!(
        clause_prop.assign_literal(-1, 1),
        weighted_prop.assign_literal(-1, 1)
    );

    let clause_stats = clause_prop.propagation_stats();
    assert_eq!(clause_stats.clause_checks, 0);
    assert_eq!(clause_stats.clause_watch_shortcuts, 0);
}

#[test]
fn test_clause_event_kernel_swaps_watch_without_full_scan() {
    let mut prop = PbPropagator::new();
    let cid = prop
        .add_constraint(
            &[
                linear_term(1, 1),
                linear_term(1, 2),
                linear_term(1, 3),
                linear_term(1, 4),
            ],
            PbRel::Ge,
            1,
        )
        .expect("clause should be added");

    assert_eq!(prop.constraints[cid].shape, ConstraintShape::Clause);
    assert_eq!(prop.constraints[cid].watch_end, 2);

    assert_eq!(prop.assign_literal(-1, 1), PropResult::Ok);

    let watched_lits: Vec<Lit> = prop.constraints[cid].terms[..prop.constraints[cid].watch_end]
        .iter()
        .map(|term| term.lit)
        .collect();
    assert!(!watched_lits.contains(&1));
    assert!(watched_lits.contains(&2));
    assert!(watched_lits.contains(&3));
    assert!(!prop.watches[lit_index(1).expect("literal has watch index")].contains(&cid));
    assert!(prop.watches[lit_index(3).expect("literal has watch index")].contains(&cid));

    let stats = prop.propagation_stats();
    assert_eq!(stats.clause_checks, 0);
    assert_eq!(stats.weighted_checks, 0);
}

#[test]
fn test_clause_event_kernel_no_swap_derives_unit() {
    let mut prop = PbPropagator::new();
    let cid = prop
        .add_constraint(
            &[linear_term(1, 1), linear_term(1, 2), linear_term(1, 3)],
            PbRel::Ge,
            1,
        )
        .expect("clause should be added");

    assert_eq!(prop.assign_literal(-3, 1), PropResult::Ok);
    match prop.assign_literal(-1, 1) {
        PropResult::Propagated(lit, reason, result_cid) => {
            assert_eq!(lit, 2);
            assert_eq!(result_cid, cid);
            assert_eq!(reason, vec![2, 1, 3]);
        }
        other => panic!("expected clause unit propagation, got {other:?}"),
    }

    let stats = prop.propagation_stats();
    assert_eq!(stats.clause_checks, 1);
    assert_eq!(stats.weighted_checks, 0);
}

#[test]
fn test_clause_event_kernel_no_swap_derives_conflict() {
    let mut prop = PbPropagator::new();
    let cid = prop
        .add_constraint(&[linear_term(1, 1), linear_term(1, 2)], PbRel::Ge, 1)
        .expect("clause should be added");

    match prop.assign_literal(-1, 1) {
        PropResult::Propagated(lit, reason, result_cid) => {
            assert_eq!(lit, 2);
            assert_eq!(result_cid, cid);
            assert_eq!(reason, vec![2, 1]);
        }
        other => panic!("expected clause unit propagation, got {other:?}"),
    }

    match prop.assign_literal(-2, 2) {
        PropResult::Conflict(reason, result_cid) => {
            assert_eq!(result_cid, cid);
            assert_eq!(reason, vec![1, 2]);
        }
        other => panic!("expected clause conflict, got {other:?}"),
    }

    let stats = prop.propagation_stats();
    assert_eq!(stats.clause_checks, 2);
    assert_eq!(stats.weighted_checks, 0);
}

#[test]
fn test_clause_event_kernel_survives_backtrack_repair() {
    let mut prop = PbPropagator::new();
    let cid = prop
        .add_constraint(
            &[
                linear_term(1, 1),
                linear_term(1, 2),
                linear_term(1, 3),
                linear_term(1, 4),
            ],
            PbRel::Ge,
            1,
        )
        .expect("clause should be added");

    assert_eq!(prop.assign_literal(-1, 1), PropResult::Ok);
    prop.unassign_literal(-1);
    assert_eq!(prop.propagate(), PropResult::Ok);

    assert_eq!(prop.assign_literal(-3, 1), PropResult::Ok);
    let watched_lits: Vec<Lit> = prop.constraints[cid].terms[..prop.constraints[cid].watch_end]
        .iter()
        .map(|term| term.lit)
        .collect();
    assert_eq!(watched_lits.len(), 2);
    assert!(watched_lits
        .iter()
        .all(|&lit| prop.value(lit) != LitValue::False));
    assert_eq!(prop.propagation_stats().weighted_checks, 0);
}

#[test]
fn test_clause_shape_matches_weighted_equivalent_conflict_after_decisions() {
    let mut clause_prop = PbPropagator::new();
    let _ = clause_prop.add_constraint(&[linear_term(1, 1), linear_term(1, 2)], PbRel::Ge, 1);

    let mut weighted_prop = PbPropagator::new();
    let _ = weighted_prop.add_constraint(&[linear_term(2, 1), linear_term(2, 2)], PbRel::Ge, 2);

    assert_eq!(
        clause_prop.assign_literal(-1, 1),
        weighted_prop.assign_literal(-1, 1)
    );
    assert_eq!(
        clause_prop.assign_literal(-2, 2),
        weighted_prop.assign_literal(-2, 2)
    );
}

#[test]
fn test_clause_shape_matches_weighted_equivalent_after_backtrack() {
    let mut clause_prop = PbPropagator::new();
    let _ = clause_prop.add_constraint(
        &[linear_term(1, 1), linear_term(1, 2), linear_term(1, 3)],
        PbRel::Ge,
        1,
    );

    let mut weighted_prop = PbPropagator::new();
    let _ = weighted_prop.add_constraint(
        &[linear_term(2, 1), linear_term(2, 2), linear_term(2, 3)],
        PbRel::Ge,
        2,
    );

    assert_eq!(
        clause_prop.assign_literal(-1, 1),
        weighted_prop.assign_literal(-1, 1)
    );
    clause_prop.unassign_literal(-1);
    weighted_prop.unassign_literal(-1);
    assert_eq!(clause_prop.propagate(), weighted_prop.propagate());
    assert_eq!(
        clause_prop.assign_literal(-2, 1),
        weighted_prop.assign_literal(-2, 1)
    );
}

#[test]
fn test_unit_cardinality_shape_matches_weighted_equivalent_after_backtrack() {
    let mut cardinality_prop = PbPropagator::new();
    let _ = cardinality_prop.add_constraint(
        &[
            linear_term(1, 1),
            linear_term(1, 2),
            linear_term(1, 3),
            linear_term(1, 4),
        ],
        PbRel::Ge,
        3,
    );

    let mut weighted_prop = PbPropagator::new();
    let _ = weighted_prop.add_constraint(
        &[
            linear_term(2, 1),
            linear_term(2, 2),
            linear_term(2, 3),
            linear_term(2, 4),
        ],
        PbRel::Ge,
        6,
    );

    assert_eq!(
        cardinality_prop.assign_literal(-1, 1),
        weighted_prop.assign_literal(-1, 1)
    );
    cardinality_prop.unassign_literal(-1);
    weighted_prop.unassign_literal(-1);
    assert_eq!(cardinality_prop.propagate(), weighted_prop.propagate());
    assert_eq!(
        cardinality_prop.assign_literal(-3, 1),
        weighted_prop.assign_literal(-3, 1)
    );
}

#[test]
fn test_clause_shape_matches_weighted_equivalent_when_inactive() {
    let mut clause_prop = PbPropagator::new();
    let clause_cid = clause_prop
        .add_constraint(&[linear_term(1, 1), linear_term(1, 2)], PbRel::Ge, 1)
        .expect("clause should be added");

    let mut weighted_prop = PbPropagator::new();
    let weighted_cid = weighted_prop
        .add_constraint(&[linear_term(2, 1), linear_term(2, 2)], PbRel::Ge, 2)
        .expect("weighted constraint should be added");

    clause_prop.deactivate_constraint(clause_cid);
    weighted_prop.deactivate_constraint(weighted_cid);

    assert_eq!(
        clause_prop.assign_literal(-1, 1),
        weighted_prop.assign_literal(-1, 1)
    );
    assert_eq!(
        clause_prop.assign_literal(-2, 1),
        weighted_prop.assign_literal(-2, 1)
    );
    assert_eq!(clause_prop.propagate(), weighted_prop.propagate());

    assert_eq!(clause_prop.propagation_stats().clause_checks, 0);
    assert_eq!(weighted_prop.propagation_stats().weighted_checks, 0);
}

#[test]
fn test_inactive_shape_constraints_stay_skipped_after_backtrack() {
    let mut prop = PbPropagator::new();
    let clause_cid = prop
        .add_constraint(&[linear_term(1, 1), linear_term(1, 2)], PbRel::Ge, 1)
        .expect("clause should be added");
    let cardinality_cid = prop
        .add_constraint(
            &[linear_term(1, 3), linear_term(1, 4), linear_term(1, 5)],
            PbRel::Ge,
            2,
        )
        .expect("cardinality should be added");

    prop.deactivate_constraint(clause_cid);
    prop.deactivate_constraint(cardinality_cid);

    assert_eq!(prop.assign_literal(-1, 1), PropResult::Ok);
    assert_eq!(prop.assign_literal(-3, 1), PropResult::Ok);
    prop.unassign_literals(&[-1, -3]);

    assert_eq!(prop.propagate(), PropResult::Ok);
    let stats = prop.propagation_stats();
    assert_eq!(stats.clause_checks, 0);
    assert_eq!(stats.unit_cardinality_checks, 0);
}

#[test]
fn test_propagation_single_constraint() {
    // 3x1 + 2x2 + x3 >= 3: falsify x2 -> propagate x1
    let mut prop = PbPropagator::new();
    let constraint = PbConstraint {
        terms: vec![linear_term(3, 1), linear_term(2, 2), linear_term(1, 3)],
        rel: PbRel::Ge,
        rhs: 3,
    };

    let id = prop.add_from_pb_constraint(&constraint);
    assert_eq!(id, Some(0));

    let result = prop.assign_literal(-2, 1);
    match result {
        PropResult::Propagated(lit, reason, _cid) => {
            assert_eq!(lit, 1);
            assert_eq!(reason, vec![1, 2]);
        }
        other => panic!("expected x1 propagation, got {other:?}"),
    }
}

#[test]
fn test_conflict_detection() {
    let mut prop = PbPropagator::new();
    let constraint = PbConstraint {
        terms: vec![linear_term(1, 1), linear_term(1, 2)],
        rel: PbRel::Ge,
        rhs: 2,
    };

    let _ = prop.add_from_pb_constraint(&constraint);
    let result = prop.assign_literal(-1, 1);

    match result {
        PropResult::Conflict(reason, _cid) => {
            assert_eq!(reason, vec![1]);
            assert!(clause_is_valid(&constraint, &reason, 2));
        }
        other => panic!("expected immediate conflict, got {other:?}"),
    }
}

#[test]
fn test_no_propagation_sufficient_slack() {
    let mut prop = PbPropagator::new();
    let _ = prop.add_constraint(
        &[linear_term(1, 1), linear_term(1, 2), linear_term(1, 3)],
        PbRel::Ge,
        1,
    );

    assert_eq!(prop.assign_literal(-1, 1), PropResult::Ok);
    assert_eq!(prop.propagate(), PropResult::Ok);
}

#[test]
fn test_backtrack_restores_slack() {
    let mut prop = PbPropagator::new();
    let _ = prop.add_constraint(
        &[linear_term(5, 1), linear_term(4, 2), linear_term(4, 3)],
        PbRel::Ge,
        8,
    );

    let first = prop.assign_literal(-1, 1);
    match first {
        PropResult::Propagated(lit, _, _cid) => {
            // Either x2 or x3 may be propagated first depending on watched
            // region size. Both are valid since coeff(x2)=coeff(x3)=4 and
            // the constraint requires both when x1 is false.
            assert!(
                lit == 2 || lit == 3,
                "expected propagation of x2 or x3, got {lit}"
            );
        }
        other => panic!("expected propagation after falsifying x1, got {other:?}"),
    }

    prop.unassign_literal(-1);
    assert_eq!(prop.value(1), LitValue::Unassigned);
    assert_eq!(prop.propagate(), PropResult::Ok);
}

#[test]
fn test_noop_unassign_skips_backtrack_rebuild() {
    let mut prop = PbPropagator::new();
    let _ = prop.add_constraint(
        &[linear_term(1, 1), linear_term(1, 2), linear_term(1, 3)],
        PbRel::Ge,
        1,
    );

    prop.unassign_literal(-1);
    assert_eq!(prop.rebuild_count(), 0);

    assert_eq!(prop.assign_literal(-1, 1), PropResult::Ok);
    assert_eq!(prop.rebuild_count(), 0);

    prop.unassign_literal(-1);
    assert_eq!(prop.rebuild_count(), 0);

    prop.unassign_literal(-1);
    assert_eq!(prop.rebuild_count(), 0);
    assert_eq!(prop.propagate(), PropResult::Ok);
}

#[test]
fn test_unassign_literals_repairs_weighted_slack_without_rebuild() {
    let mut prop = PbPropagator::new();
    let cid = prop
        .add_constraint(&[linear_term(2, 1), linear_term(2, 2)], PbRel::Ge, 2)
        .expect("weighted constraint should be added");

    assert_eq!(prop.constraints[cid].shape, ConstraintShape::Weighted);
    assert_eq!(prop.constraints[cid].watch_end, 2);
    assert_eq!(prop.constraints[cid].slack, 2);

    assert_eq!(prop.assign_literal(2, 1), PropResult::Ok);
    assert_eq!(prop.assign_literal(-1, 1), PropResult::Ok);
    assert_eq!(prop.constraints[cid].slack, 0);

    let rebuilds_before = prop.rebuild_count();
    let slack_recalculations_before = prop.propagation_stats().slack_recalculations;
    prop.unassign_literal(-1);

    assert_eq!(prop.value(1), LitValue::Unassigned);
    assert_eq!(prop.rebuild_count(), rebuilds_before);
    assert_eq!(
        prop.propagation_stats().slack_recalculations,
        slack_recalculations_before
    );
    assert_eq!(prop.constraints[cid].slack, 2);
    assert_eq!(prop.propagate_constraint(cid), PropResult::Ok);
}

#[test]
fn test_unassign_literals_repairs_duplicate_watched_false_occurrences() {
    let mut prop = PbPropagator::new();
    let cid = prop
        .add_constraint(&[linear_term(1, 1), linear_term(1, 1)], PbRel::Ge, 1)
        .expect("duplicate weighted constraint should be added");

    assert_eq!(prop.constraints[cid].shape, ConstraintShape::Weighted);
    assert_eq!(prop.constraints[cid].watch_end, 2);
    assert_eq!(prop.constraints[cid].slack, 1);

    match prop.assign_literal(-1, 1) {
        PropResult::Conflict(_, result_cid) => assert_eq!(result_cid, cid),
        other => {
            panic!("expected duplicate watched false occurrences to conflict, got {other:?}")
        }
    }
    assert_eq!(prop.constraints[cid].slack, -1);

    let rebuilds_before = prop.rebuild_count();
    prop.unassign_literal(-1);

    assert_eq!(prop.rebuild_count(), rebuilds_before);
    assert_eq!(prop.constraints[cid].slack, 1);
    assert_eq!(prop.propagate_constraint(cid), PropResult::Ok);
}

#[test]
fn test_unassign_repair_sums_duplicate_coefficients_with_stamps() {
    let mut prop = PbPropagator::new();
    let cid = prop
        .add_constraint(&[linear_term(3, 1), linear_term(2, 1)], PbRel::Ge, 3)
        .expect("duplicate weighted constraint should be added");

    assert_eq!(prop.constraints[cid].shape, ConstraintShape::Weighted);
    assert_eq!(prop.constraints[cid].watch_end, 2);
    assert_eq!(prop.constraints[cid].slack, 2);

    match prop.assign_literal(-1, 1) {
        PropResult::Conflict(_, result_cid) => assert_eq!(result_cid, cid),
        other => panic!("expected duplicate watched literals to conflict, got {other:?}"),
    }
    assert_eq!(prop.constraints[cid].slack, -3);

    let rebuilds_before = prop.rebuild_count();
    prop.unassign_literal(-1);

    assert_eq!(prop.rebuild_count(), rebuilds_before);
    assert_eq!(prop.constraints[cid].slack, 2);
}

#[test]
fn test_unassign_repair_only_restores_processed_watch_events() {
    // Both constraints watch literal `1`. Falsifying it conflicts on the
    // FIRST (`conflict_cid`, the unit clause), which aborts the watch-list
    // scan. The SECOND constraint is a NON-counting weighted constraint, so
    // it is intentionally left unprocessed (its slack stays 2): non-counting
    // checks fall back to an exact rescan and tolerate a momentarily stale
    // cached slack, preserving the watched scheme's early-abort behavior.
    // (Counting constraints are instead decremented in a pre-pass before the
    // main loop; see `decrement_counting_watches`.)
    let mut prop = PbPropagator::new();
    let conflict_cid = prop
        .add_constraint(&[linear_term(1, 1)], PbRel::Ge, 1)
        .expect("unit constraint should be added");
    let unprocessed_cid = prop
        .add_constraint(&[linear_term(2, 1), linear_term(2, 2)], PbRel::Ge, 2)
        .expect("weighted constraint should be added");
    assert!(!prop.is_counting_for_test(unprocessed_cid));

    assert_eq!(prop.constraints[unprocessed_cid].slack, 2);

    match prop.assign_literal(-1, 1) {
        PropResult::Conflict(_, result_cid) => assert_eq!(result_cid, conflict_cid),
        other => panic!("expected first watch-bucket entry to conflict, got {other:?}"),
    }
    assert_eq!(prop.constraints[unprocessed_cid].slack, 2);

    let rebuilds_before = prop.rebuild_count();
    prop.unassign_literal(-1);

    assert_eq!(prop.rebuild_count(), rebuilds_before);
    assert_eq!(prop.constraints[unprocessed_cid].slack, 2);
}

#[test]
fn test_counting_watch_decremented_in_prepass_past_conflict() {
    // A unit clause that conflicts on assigning -1, plus a COUNTING
    // constraint that also watches literal 1. Even though the conflict
    // aborts the main scan, the counting constraint's slack must already
    // reflect the falsification (decremented in the pre-pass), and be
    // repaired on the subsequent unassign.
    let mut prop = PbPropagator::new();
    let conflict_cid = prop
        .add_constraint(&[linear_term(1, 1)], PbRel::Ge, 1)
        .expect("unit constraint should be added");
    // Enough terms with one large coeff -> counting (big-M); exceeds
    // COUNTING_MIN_TERMS so the constraint is auto-selected for counting.
    let mut terms = vec![linear_term(40, 1)];
    for v in 2..=60u32 {
        terms.push(linear_term(2, v));
    }
    let counting_cid = prop
        .add_constraint(&terms, PbRel::Ge, 30)
        .expect("weighted constraint should be added");
    assert!(prop.is_counting_for_test(counting_cid));

    let slack_before = prop.slack_for_test(counting_cid);
    assert_eq!(
        slack_before,
        prop.exact_weighted_slack_for_test(counting_cid)
    );

    match prop.assign_literal(-1, 1) {
        PropResult::Conflict(_, result_cid) => assert_eq!(result_cid, conflict_cid),
        other => panic!("expected unit clause to conflict, got {other:?}"),
    }
    // Counting slack reflects literal 1 being false (decremented by 40).
    assert_eq!(prop.slack_for_test(counting_cid), slack_before - 40);
    assert_eq!(
        prop.slack_for_test(counting_cid),
        prop.exact_weighted_slack_for_test(counting_cid)
    );

    prop.unassign_literal(-1);
    assert_eq!(prop.slack_for_test(counting_cid), slack_before);
    assert_eq!(
        prop.slack_for_test(counting_cid),
        prop.exact_weighted_slack_for_test(counting_cid)
    );
}

#[test]
fn counting_select_isolates_dominated_long_tail() {
    // The selection predicate accepts the one shape counting helps — a few
    // dominant big-M terms over a long tail of much smaller coefficients —
    // and rejects every large-coefficient family where the watched scheme is
    // already fast. Each row clears the term-count and big-M (top coeff >=
    // degree/4) gates, so the long-tail / dominance / bitvector gates are
    // what distinguish them.
    const N: u32 = 80;
    let add = |terms: &[PbTerm], rhs: i128| -> bool {
        let mut prop = PbPropagator::new();
        // Pin the SELECTION predicate: keep the P2d blind-row arming (which
        // may independently convert rows to counting) out of this test.
        prop.disable_blind_arming_for_test();
        match prop.add_constraint(terms, PbRel::Ge, rhs) {
            Some(cid) => prop.is_counting_for_test(cid),
            None => false,
        }
    };

    // (a) Dominant big-M row: one coeff 1000 over a long tail of units.
    // big_count = 1, strict dominance, not a bitvector -> counting.
    let mut dominant = vec![linear_term(1000, 1)];
    for v in 2..=N {
        dominant.push(linear_term(1, v));
    }
    assert!(
        add(&dominant, 1000),
        "a single dominant coefficient over a long tail should use counting"
    );

    // (b) A FEW big-M terms over a long tail of units, where the top still
    // dominates the second by >= 1.8x (1000 vs 400). Long tail (3*6 <= 80),
    // dominant -> counting.
    let mut multi = vec![
        linear_term(1000, 1),
        linear_term(400, 2),
        linear_term(300, 3),
    ];
    for v in 4..=N {
        multi.push(linear_term(1, v));
    }
    assert!(
        add(&multi, 1000),
        "a dominant top over a few big-M terms and a long tail should count"
    );

    // (c) Long-tail gate: MANY big coefficients (most terms big), even with a
    // strictly dominant top (1000 vs 300, > 1.8x). This is the knapsack /
    // even-colouring / rand6reg shape — no tail to rescan, so it must stay on
    // the watched scheme. Every coeff 300 is "big" (300*4 >= degree 1000), so
    // big_count == n and the long-tail gate (6*big_count > n) rejects it.
    let mut many_big = vec![linear_term(1000, 1)];
    for v in 2..=N {
        many_big.push(linear_term(300, v));
    }
    assert!(
        !add(&many_big, 1000),
        "many big coefficients (no long tail) should stay watched"
    );

    // (d) Dominance gate, equal top: knapsack with equal top coefficients
    // (mos = 1.0x < 1.8x) -> watched.
    let knapsack: Vec<_> = (1..=N).map(|v| linear_term(1000, v)).collect();
    assert!(
        !add(&knapsack, 1000),
        "equal top coefficients should stay on the watched scheme"
    );

    // (e) Dominance gate, near-equal top: a long-tail row whose top two
    // coefficients are within ~1.1x (1000 vs 900) — the near-equal-top shape
    // shared by knapsack and bitvector-equality rows. Below the 1.8x margin
    // -> watched, even though it has a long unit tail.
    let mut near_equal = vec![linear_term(1000, 1), linear_term(900, 2)];
    for v in 3..=N {
        near_equal.push(linear_term(1, v));
    }
    assert!(
        !add(&near_equal, 1000),
        "near-equal top coefficients should stay on the watched scheme"
    );
}

#[test]
fn test_propagation_updates_all_watching_constraints_then_repairs_on_unassign() {
    // Both constraints watch literal `1`. Falsifying it propagates from the
    // FIRST (`propagate_cid`); the watch-list scan MUST still continue and
    // decrement the SECOND (`unprocessed_cid`) so its cached slack stays
    // consistent with the assignment. Returning early on the propagation
    // would leave the second constraint's slack stale-high, which the
    // slack-shortcut would later mistake for "still satisfiable" — a
    // soundness bug (RoundingSat scans the whole watch list per literal).
    let mut prop = PbPropagator::new();
    let propagate_cid = prop
        .add_constraint(&[linear_term(2, 1), linear_term(3, 2)], PbRel::Ge, 3)
        .expect("propagating weighted constraint should be added");
    let unprocessed_cid = prop
        .add_constraint(&[linear_term(2, 1), linear_term(2, 3)], PbRel::Ge, 2)
        .expect("later weighted constraint should be added");

    assert_eq!(prop.constraints[unprocessed_cid].slack, 2);

    // The first propagation is surfaced to the caller, but the scan keeps
    // going so every watching constraint is updated.
    match prop.assign_literal(-1, 1) {
        PropResult::Propagated(lit, _, result_cid) => {
            assert_eq!(lit, 2);
            assert_eq!(result_cid, propagate_cid);
        }
        other => panic!("expected first watch-bucket entry to propagate, got {other:?}"),
    }
    // With `1` false, `unprocessed_cid` (2·x1 + 2·x3 >= 2) loses x1's
    // contribution: its watched slack is now 0 (was 2), correctly reflecting
    // that x3 is now forced.
    assert_eq!(prop.constraints[unprocessed_cid].slack, 0);

    // Unassigning `-1` restores x1's contribution to every constraint whose
    // slack was decremented for it, bringing the slack back to 2.
    let rebuilds_before = prop.rebuild_count();
    prop.unassign_literal(-1);

    assert_eq!(prop.rebuild_count(), rebuilds_before);
    assert_eq!(prop.constraints[unprocessed_cid].slack, 2);
}

#[test]
fn test_unassign_repair_uses_exact_literal_polarity() {
    let mut prop = PbPropagator::new();
    let cid = prop
        .add_constraint(&[linear_term(2, 1), negated_term(3, 1)], PbRel::Ge, 2)
        .expect("mixed-polarity weighted constraint should be added");

    assert_eq!(prop.constraints[cid].watch_end, 2);
    assert_eq!(prop.constraints[cid].slack, 3);

    assert_eq!(prop.assign_literal(1, 1), PropResult::Ok);
    assert_eq!(prop.constraints[cid].slack, 0);

    prop.unassign_literal(1);
    assert_eq!(prop.constraints[cid].slack, 3);
}

#[test]
fn test_event_buckets_keep_unmatched_literal_events() {
    // Two falsified literals record events in DIFFERENT buckets. Unassigning
    // only one literal must consume exactly that literal's bucket: its slack
    // contribution is restored, while the other literal's live event stays
    // outstanding for its own future backtrack.
    //
    // Flow detail: the first falsification leaves a false literal stuck in
    // the watched region, which arms full visibility and (for Weighted rows)
    // converts to counting mid-search — bumping the row's event epoch and
    // re-recording the aggregated event. The live entries below are therefore
    // at the post-conversion epoch; the leftover birth-epoch entry in lit 2's
    // bucket is stale and preserved-but-ignored.
    let mut prop = PbPropagator::new();
    let cid = prop
        .add_constraint(&[linear_term(2, 1), linear_term(2, 2)], PbRel::Ge, 2)
        .expect("weighted constraint should be added");

    match prop.assign_literal(-2, 1) {
        PropResult::Propagated(lit, _, result_cid) => {
            assert_eq!(lit, 1);
            assert_eq!(result_cid, cid);
        }
        other => panic!("expected unmatched-event fixture to propagate x1, got {other:?}"),
    }
    assert_eq!(prop.constraints[cid].slack, 0);
    assert!(prop.constraints[cid].counting);
    let live_epoch = prop.constraints[cid].event_epoch;
    let bucket_of = |prop: &PbPropagator, lit: Lit| -> Vec<(usize, u32)> {
        let idx = lit_index(lit).expect("literal has watch index");
        prop.falsified_watch_events
            .get(idx)
            .cloned()
            .unwrap_or_default()
    };
    assert!(bucket_of(&prop, 2).contains(&(cid, live_epoch)));

    match prop.assign_literal(-1, 1) {
        PropResult::Conflict(_, result_cid) => assert_eq!(result_cid, cid),
        other => panic!("expected matched-event fixture to conflict on x1, got {other:?}"),
    }
    assert_eq!(prop.constraints[cid].slack, -2);
    assert!(bucket_of(&prop, 1).contains(&(cid, live_epoch)));

    prop.unassign_literal(-1);

    assert_eq!(prop.constraints[cid].slack, 0);
    assert!(bucket_of(&prop, 2).contains(&(cid, live_epoch)));
    assert!(bucket_of(&prop, 1).is_empty());
}

#[test]
fn test_event_buckets_skip_stale_epoch_after_counting_conversion() {
    // A watched-mode falsification records an event at the row's birth epoch
    // 0. The stuck false watched literal then arms full visibility, which for
    // Weighted rows runs `convert_to_counting` mid-search: the event epoch
    // bumps to 1 and ONE aggregated event per false literal is re-recorded.
    // The stale epoch-0 entry left in the bucket must be SKIPPED on
    // consumption, otherwise the backtrack would restore the literal's
    // coefficient TWICE into the trusted-exact counting slack (a corrupted
    // slack is a spurious conflict/propagation).
    let mut prop = PbPropagator::new();
    let cid = prop
        .add_constraint(&[linear_term(2, 1), linear_term(2, 2)], PbRel::Ge, 2)
        .expect("weighted constraint should be added");
    assert_eq!(prop.constraints[cid].shape, ConstraintShape::Weighted);
    assert!(!prop.constraints[cid].counting);
    assert_eq!(prop.constraints[cid].event_epoch, 0);
    assert_eq!(prop.constraints[cid].slack, 2);

    match prop.assign_literal(-2, 1) {
        PropResult::Propagated(lit, _, result_cid) => {
            assert_eq!(lit, 1);
            assert_eq!(result_cid, cid);
        }
        other => panic!("expected stale-epoch fixture to propagate x1, got {other:?}"),
    }

    // The falsification recorded an epoch-0 watched-mode event, then the
    // arm-time counting conversion bumped the epoch and re-recorded: the
    // bucket now holds BOTH the stale epoch-0 and the live epoch-1 entry.
    assert!(prop.constraints[cid].counting);
    assert_eq!(prop.constraints[cid].event_epoch, 1);
    assert_eq!(prop.constraints[cid].slack, 0);
    let lit2_idx = lit_index(2).expect("literal has watch index");
    assert!(prop.falsified_watch_events[lit2_idx].contains(&(cid, 0)));
    assert!(prop.falsified_watch_events[lit2_idx].contains(&(cid, 1)));

    let rebuilds_before = prop.rebuild_count();
    prop.unassign_literal(-2);

    // Exactly ONE restore of x2's coefficient (+2): slack returns to the
    // all-unassigned exact value 2, not 4 (the stale-epoch double restore).
    assert_eq!(prop.rebuild_count(), rebuilds_before);
    assert_eq!(prop.constraints[cid].slack, 2);
    assert!(prop.falsified_watch_events[lit2_idx].is_empty());
}

#[test]
fn test_weighted_duplicate_watch_keeps_old_bucket_after_swap_and_reassign() {
    let mut prop = PbPropagator::new();
    let cid = prop
        .add_constraint(
            &[linear_term(3, 1), linear_term(3, 1), linear_term(2, 2)],
            PbRel::Ge,
            2,
        )
        .expect("weighted constraint should be added");
    let x_watch = lit_index(1).expect("literal has watch index");
    let y_watch = lit_index(2).expect("literal has watch index");

    assert_eq!(prop.constraints[cid].shape, ConstraintShape::Weighted);
    assert_eq!(prop.constraints[cid].watch_end, 2);
    assert!(prop.watches[x_watch].contains(&cid));
    assert!(!prop.watches[y_watch].contains(&cid));

    match prop.assign_literal(-1, 1) {
        PropResult::Propagated(lit, _, result_cid) => {
            assert_eq!(lit, 2);
            assert_eq!(result_cid, cid);
        }
        other => panic!("expected weighted duplicate swap to propagate, got {other:?}"),
    }
    assert!(prop.watches[x_watch].contains(&cid));
    assert!(prop.watches[y_watch].contains(&cid));

    let rebuilds_before = prop.rebuild_count();
    prop.unassign_literal(-1);
    assert_eq!(prop.rebuild_count(), rebuilds_before);

    match prop.assign_literal(-1, 1) {
        PropResult::Propagated(lit, _, result_cid) => {
            assert_eq!(lit, 2);
            assert_eq!(result_cid, cid);
        }
        other => panic!("expected retained duplicate watch to propagate again, got {other:?}"),
    }
}

#[test]
fn test_unit_cardinality_duplicate_watch_keeps_old_bucket_after_swap_and_reassign() {
    let mut prop = PbPropagator::new();
    let cid = prop
        .add_constraint(
            &[
                linear_term(1, 1),
                linear_term(1, 1),
                linear_term(1, 2),
                linear_term(1, 3),
            ],
            PbRel::Ge,
            2,
        )
        .expect("unit-cardinality constraint should be added");
    let x_watch = lit_index(1).expect("literal has watch index");
    let replacement_watch = lit_index(3).expect("literal has watch index");

    assert_eq!(
        prop.constraints[cid].shape,
        ConstraintShape::UnitCardinality
    );
    assert_eq!(prop.constraints[cid].watch_end, 3);
    assert!(prop.watches[x_watch].contains(&cid));
    assert!(!prop.watches[replacement_watch].contains(&cid));

    match prop.assign_literal(-1, 1) {
        PropResult::Propagated(_, _, result_cid) => assert_eq!(result_cid, cid),
        other => panic!("expected unit-cardinality duplicate swap to propagate, got {other:?}"),
    }
    assert!(prop.watches[x_watch].contains(&cid));
    assert!(prop.watches[replacement_watch].contains(&cid));

    let rebuilds_before = prop.rebuild_count();
    prop.unassign_literal(-1);
    assert_eq!(prop.rebuild_count(), rebuilds_before);

    match prop.assign_literal(-1, 1) {
        PropResult::Propagated(_, _, result_cid) => assert_eq!(result_cid, cid),
        other => {
            panic!("expected retained unit-cardinality watch to propagate again, got {other:?}")
        }
    }
}

#[test]
fn test_unassign_literals_keeps_full_rebuild_when_dirty() {
    let mut prop = PbPropagator::new();
    let cid = prop
        .add_constraint(&[linear_term(2, 1), linear_term(2, 2)], PbRel::Ge, 2)
        .expect("weighted constraint should be added");

    assert_eq!(prop.assign_literal(2, 1), PropResult::Ok);
    assert_eq!(prop.assign_literal(-1, 1), PropResult::Ok);
    prop.needs_rebuild = true;

    let rebuilds_before = prop.rebuild_count();
    prop.unassign_literal(-1);

    assert_eq!(prop.rebuild_count(), rebuilds_before + 1);
    assert!(!prop.needs_rebuild);
    assert_eq!(prop.constraints[cid].slack, 2);
    assert_eq!(prop.propagate_constraint(cid), PropResult::Ok);
}

#[test]
fn test_multiple_constraints() {
    let mut prop = PbPropagator::new();
    let _ = prop.add_constraint(&[linear_term(1, 1), linear_term(1, 2)], PbRel::Ge, 1);
    let _ = prop.add_constraint(&[negated_term(1, 2), linear_term(1, 3)], PbRel::Ge, 1);

    let first = prop.assign_literal(-1, 1);
    let propagated = match first {
        PropResult::Propagated(lit, reason, _cid) => {
            assert_eq!(lit, 2);
            assert_eq!(reason, vec![2, 1]);
            lit
        }
        other => panic!("expected x2 propagation, got {other:?}"),
    };

    let second = prop.assign_literal(propagated, 1);
    match second {
        PropResult::Propagated(lit, reason, _cid) => {
            assert_eq!(lit, 3);
            assert_eq!(reason, vec![3, -2]);
        }
        other => panic!("expected x3 propagation, got {other:?}"),
    }
}

#[test]
fn test_trivially_satisfied_skipped() {
    let mut prop = PbPropagator::new();
    let id = prop.add_constraint(&[linear_term(1, 1)], PbRel::Ge, 0);
    assert_eq!(id, None);
    assert_eq!(prop.num_constraints(), 0);
}

#[test]
fn test_reason_extraction_valid() {
    let mut prop = PbPropagator::new();
    let constraint = PbConstraint {
        terms: vec![linear_term(3, 1), linear_term(2, 2)],
        rel: PbRel::Ge,
        rhs: 3,
    };

    let _ = prop.add_from_pb_constraint(&constraint);
    let result = prop.assign_literal(-2, 1);

    match result {
        PropResult::Propagated(lit, reason, _cid) => {
            assert_eq!(lit, 1);
            assert_eq!(reason, vec![1, 2]);
            assert!(clause_is_valid(&constraint, &reason, 2));
        }
        other => panic!("expected propagation, got {other:?}"),
    }
}

#[test]
fn test_normalization_negative_coeffs() {
    let mut prop = PbPropagator::new();
    let _ = prop.add_constraint(&[linear_term(-1, 1), linear_term(2, 2)], PbRel::Ge, 1);

    let result = prop.assign_literal(1, 1);
    match result {
        PropResult::Propagated(lit, reason, _cid) => {
            assert_eq!(lit, 2);
            assert_eq!(reason, vec![2, -1]);
        }
        other => panic!("expected x2 propagation after normalization, got {other:?}"),
    }
}

#[test]
fn test_cardinality_constraint() {
    let mut prop = PbPropagator::new();
    let _ = prop.add_constraint(
        &[
            linear_term(1, 1),
            linear_term(1, 2),
            linear_term(1, 3),
            linear_term(1, 4),
        ],
        PbRel::Ge,
        3,
    );

    let mut propagated = Vec::new();
    let mut pending = prop.assign_literal(-1, 1);
    let mut level = 2;
    loop {
        match pending {
            PropResult::Propagated(lit, _, _cid) => {
                propagated.push(lit);
                pending = prop.assign_literal(lit, level);
                level += 1;
            }
            PropResult::Ok => {
                pending = prop.propagate();
                if pending == PropResult::Ok {
                    break;
                }
            }
            other => panic!("expected only propagation steps, got {other:?}"),
        }
    }

    assert_eq!(propagated, vec![2, 3, 4]);
}

#[test]
fn test_equality_constraint_both_directions() {
    let mut prop = PbPropagator::new();
    let id = prop.add_constraint(&[linear_term(1, 1), linear_term(1, 2)], PbRel::Eq, 1);

    assert_eq!(id, Some(0));
    assert_eq!(prop.num_constraints(), 2);

    let result = prop.assign_literal(1, 1);
    match result {
        PropResult::Propagated(lit, reason, _cid) => {
            assert_eq!(lit, -2);
            assert_eq!(reason, vec![-2, -1]);
        }
        other => panic!("expected ~x2 propagation from equality, got {other:?}"),
    }
}

// -----------------------------------------------------------------------
// New tests for watched-slack-specific behavior
// -----------------------------------------------------------------------

#[test]
fn test_watched_slack_threshold_maintained() {
    // 5x1 + 3x2 + 2x3 + 1x4 >= 6
    // After init, watched should include enough terms so that
    // watched_sum >= degree + max_unwatched_coeff
    let mut prop = PbPropagator::new();
    let _ = prop.add_constraint(
        &[
            linear_term(5, 1),
            linear_term(3, 2),
            linear_term(2, 3),
            linear_term(1, 4),
        ],
        PbRel::Ge,
        6,
    );

    // Verify the constraint was added.
    assert_eq!(prop.num_constraints(), 1);

    // The constraint has degree=6, terms sorted [5,3,2,1].
    // With watch_end=2: watched_sum=8, max_unwatched=2, threshold=6+2=8.
    // 8 >= 8: invariant holds with 2 watched.
    let c = &prop.constraints[0];
    assert!(
        c.watched_sum >= c.degree + c.max_unwatched_coeff,
        "watched_sum ({}) must be >= degree ({}) + max_unwatched ({}) = {}",
        c.watched_sum,
        c.degree,
        c.max_unwatched_coeff,
        c.degree + c.max_unwatched_coeff,
    );
}

#[test]
fn test_incremental_watch_swap() {
    // 4x1 + 3x2 + 2x3 + 1x4 >= 5
    // Watched: [x1(4), x2(3)], unwatched: [x3(2), x4(1)]
    // Falsify x1: should swap x3 in.
    let mut prop = PbPropagator::new();
    let _ = prop.add_constraint(
        &[
            linear_term(4, 1),
            linear_term(3, 2),
            linear_term(2, 3),
            linear_term(1, 4),
        ],
        PbRel::Ge,
        5,
    );

    let result = prop.assign_literal(-1, 1);
    // After swap: watched should contain x2(3) and x3(2), total=5.
    // slack = 5 - 5 = 0, no propagation (coeff 3 > 0 and coeff 2 > 0
    // are both > slack=0, so propagation should fire).
    // Actually: slack = watched_non_false_sum - degree.
    // Both x2 and x3 are non-false, so slack = 3 + 2 - 5 = 0.
    // coeff(x2)=3 > 0 => propagate x2.
    match result {
        PropResult::Propagated(lit, _, _) => {
            assert!(
                lit == 2 || lit == 3,
                "expected propagation of x2 or x3, got {lit}"
            );
        }
        PropResult::Ok => {
            // It's also valid if slack allows no immediate propagation
            // depending on exact threshold calculation.
        }
        PropResult::Interrupted => {
            panic!("non-interruptible propagation should not report interruption");
        }
        PropResult::Conflict(_, _) => {
            panic!("should not conflict when only one of four literals is false");
        }
    }
}

#[test]
fn test_falsified_watch_iteration_does_not_skip_shifted_entries() {
    let mut prop = PbPropagator::new();

    for offset in 0..64u32 {
        let x = 2 + offset * 2;
        let y = x + 1;
        let cid = prop.add_constraint(
            &[linear_term(1, 1), linear_term(1, x), linear_term(1, y)],
            PbRel::Ge,
            1,
        );
        assert_eq!(cid, Some(offset as usize));
    }

    let x1_watch = lit_index(1).expect("non-zero literal has watch index");
    assert_eq!(prop.watches[x1_watch].len(), 64);

    assert_eq!(prop.assign_literal(-1, 1), PropResult::Ok);

    assert!(
        prop.watches[x1_watch].is_empty(),
        "every x1 watch should be removed after being swapped out"
    );
    for offset in 0..64u32 {
        let y = i32::try_from(3 + offset * 2).expect("test literal fits in i32");
        let y_watch = lit_index(y).expect("non-zero literal has watch index");
        assert_eq!(prop.watches[y_watch], vec![offset as usize]);
    }
}

#[test]
fn test_general_watch_swap_remove_rechecks_moved_entries() {
    fn assert_watch_bucket_drained(
        build_terms: impl Fn(u32, u32, u32) -> Vec<PbTerm>,
        rhs: i128,
        expected_shape: ConstraintShape,
        replacement_offset: u32,
    ) {
        let mut prop = PbPropagator::new();

        for offset in 0..64u32 {
            let x = 2 + offset * 3;
            let y = x + 1;
            let z = x + 2;
            let cid = prop.add_constraint(&build_terms(x, y, z), PbRel::Ge, rhs);
            assert_eq!(cid, Some(offset as usize));
            assert_eq!(prop.constraints[offset as usize].shape, expected_shape);
        }

        let x1_watch = lit_index(1).expect("non-zero literal has watch index");
        assert_eq!(prop.watches[x1_watch].len(), 64);

        assert_eq!(prop.assign_literal(-1, 1), PropResult::Ok);

        assert!(
            prop.watches[x1_watch].is_empty(),
            "all x1 watches should be removed after unordered watch swaps"
        );
        for offset in 0..64u32 {
            let replacement =
                i32::try_from(2 + offset * 3 + replacement_offset).expect("literal fits i32");
            let replacement_watch =
                lit_index(replacement).expect("non-zero literal has watch index");
            assert_eq!(prop.watches[replacement_watch], vec![offset as usize]);
        }
    }

    assert_watch_bucket_drained(
        |x, y, z| {
            vec![
                linear_term(1, 1),
                linear_term(1, x),
                linear_term(1, y),
                linear_term(1, z),
            ]
        },
        1,
        ConstraintShape::Clause,
        1,
    );
    assert_watch_bucket_drained(
        |x, y, z| {
            vec![
                linear_term(1, 1),
                linear_term(1, x),
                linear_term(1, y),
                linear_term(1, z),
            ]
        },
        2,
        ConstraintShape::UnitCardinality,
        2,
    );
    assert_watch_bucket_drained(
        |x, y, z| {
            vec![
                linear_term(4, 1),
                linear_term(4, x),
                linear_term(3, y),
                linear_term(1, z),
            ]
        },
        3,
        ConstraintShape::Weighted,
        1,
    );
}

#[test]
fn test_watched_region_conflict_all_false() {
    // x1 + x2 >= 2: falsifying both must conflict
    let mut prop = PbPropagator::new();
    let _ = prop.add_constraint(&[linear_term(1, 1), linear_term(1, 2)], PbRel::Ge, 2);

    // First falsification should immediately conflict because x1+x2>=2
    // with x1 false means we need x2, but degree=2 requires BOTH.
    let r1 = prop.assign_literal(-1, 1);
    match r1 {
        PropResult::Conflict(reason, _) => {
            // x1 false makes it impossible: need x2=true for coeff 1,
            // but 1 < 2 = degree.
            assert!(reason.contains(&1), "conflict reason should include x1");
        }
        other => panic!("expected conflict on x1+x2>=2 with x1=false, got {other:?}"),
    }
}

#[test]
fn test_large_coefficient_propagation() {
    // 100x1 + 1x2 + 1x3 + 1x4 >= 100
    // Falsifying x1 should immediately conflict (remaining sum = 3 < 100).
    let mut prop = PbPropagator::new();
    let _ = prop.add_constraint(
        &[
            linear_term(100, 1),
            linear_term(1, 2),
            linear_term(1, 3),
            linear_term(1, 4),
        ],
        PbRel::Ge,
        100,
    );

    let result = prop.assign_literal(-1, 1);
    match result {
        PropResult::Conflict(_, _) => {
            // Expected: 1+1+1 = 3 < 100.
        }
        other => panic!("expected conflict, got {other:?}"),
    }
}

#[test]
fn test_deactivate_constraint() {
    let mut prop = PbPropagator::new();
    let cid = prop
        .add_constraint(&[linear_term(1, 1), linear_term(1, 2)], PbRel::Ge, 2)
        .expect("constraint should be added");

    // Deactivate: should not propagate/conflict on this constraint.
    prop.deactivate_constraint(cid);
    assert!(!prop.is_constraint_active(cid));

    let result = prop.assign_literal(-1, 1);
    assert_eq!(
        result,
        PropResult::Ok,
        "deactivated constraint should not trigger"
    );
}

#[test]
fn test_deactivate_constraint_removes_only_own_watch_buckets() {
    let mut prop = PbPropagator::new();
    let cid = prop
        .add_constraint(&[linear_term(1, 1), linear_term(1, 2)], PbRel::Ge, 2)
        .expect("constraint should be added");
    let high_cid = prop
        .add_constraint(&[linear_term(1, 10_000)], PbRel::Ge, 1)
        .expect("high-variable constraint should be added");

    assert!(
        prop.watches.len() >= 20_000,
        "sparse high variables should make a global watch-list sweep visible"
    );

    prop.deactivate_constraint(cid);

    let stats = prop.propagation_stats();
    assert_eq!(
        stats.deactivation_watch_lists_visited, 2,
        "deactivation should touch only the deactivated constraint's watched literal buckets"
    );

    let x1_watch = lit_index(1).expect("literal has watch index");
    let x2_watch = lit_index(2).expect("literal has watch index");
    let high_watch = lit_index(10_000).expect("literal has watch index");
    assert!(!prop.watches[x1_watch].contains(&cid));
    assert!(!prop.watches[x2_watch].contains(&cid));
    assert_eq!(prop.watches[high_watch], vec![high_cid]);
}

#[test]
fn test_lazy_deactivate_constraint_leaves_safe_stale_watches() {
    let mut prop = PbPropagator::new();
    let cid = prop
        .add_constraint(&[linear_term(1, 1), linear_term(1, 2)], PbRel::Ge, 2)
        .expect("constraint should be added");

    let x1_watch = lit_index(1).expect("literal has watch index");
    let x2_watch = lit_index(2).expect("literal has watch index");
    assert!(prop.watches[x1_watch].contains(&cid));
    assert!(prop.watches[x2_watch].contains(&cid));

    prop.deactivate_constraint_lazy(cid);

    assert!(!prop.is_constraint_active(cid));
    assert!(prop.watches[x1_watch].contains(&cid));
    assert!(prop.watches[x2_watch].contains(&cid));
    assert_eq!(
        prop.propagation_stats().deactivation_watch_lists_visited,
        0,
        "lazy deactivation must not sweep watch buckets"
    );
    assert_eq!(
        prop.assign_literal(-1, 1),
        PropResult::Ok,
        "inactive stale watch should not propagate or conflict"
    );
    assert!(
        !prop.watches[x1_watch].contains(&cid),
        "event propagation should prune the stale lazy-deactivated watch it visits"
    );
    assert!(
        prop.watches[x2_watch].contains(&cid),
        "unvisited stale watch can wait for rebuild or its own event"
    );

    prop.rebuild_all_watches();
    assert!(!prop.watches[x1_watch].contains(&cid));
    assert!(!prop.watches[x2_watch].contains(&cid));
}

#[test]
fn test_lazy_deactivate_constraint_is_skipped_by_interruptible_event_propagation() {
    let mut prop = PbPropagator::new();
    let cid = prop
        .add_constraint(&[linear_term(1, 1), linear_term(1, 2)], PbRel::Ge, 2)
        .expect("constraint should be added");

    prop.deactivate_constraint_lazy(cid);

    let mut polls = 0usize;
    let result = prop.assign_literal_interruptible(-1, 1, || {
        polls += 1;
        false
    });

    assert_eq!(
        result,
        PropResult::Ok,
        "inactive stale watch should not propagate or conflict"
    );
    assert_eq!(
        prop.value(2),
        LitValue::Unassigned,
        "inactive stale watch must not imply from a deactivated constraint"
    );
    let x1_watch = lit_index(1).expect("literal has watch index");
    assert!(
        !prop.watches[x1_watch].contains(&cid),
        "interruptible event propagation should prune the stale lazy-deactivated watch it visits"
    );
    assert!(polls > 0, "interruptible event path should poll");
}

#[test]
fn test_interruptible_rebuild_counting_conversion_keeps_single_watch_entries() {
    // D1 regression (release-mode wrong UNSAT): the interruptible rebuild
    // must add a row's watch entries BEFORE the blind-row arming/counting
    // conversion. `add_constraint_watches` uses unchecked inserts (safe only
    // on the row's freshly cleared lists); `convert_to_counting` adds one
    // deduplicated entry per literal. In the reversed order every literal
    // ends up holding the cid TWICE, the counting pre-pass double-decrements
    // the trusted exact slack, and a satisfiable row reports a spurious
    // conflict — at level 0 that is an unguarded wrong UNSAT.
    //
    // Scenario: `2a + 2b + c + d >= 2` is NOT blind at construction (watched
    // slack 2 == max watched coeff 2). Interrupt an assignment at the notify
    // entry poll so the assignment lands but notification is abandoned
    // (`needs_rebuild`). The re-entered drive runs the INTERRUPTIBLE rebuild:
    // repair swaps the falsified watch for a unit-coefficient literal, the
    // repaired region is blind (slack 1 < max watched coeff 2), and the row
    // converts to counting MID-REBUILD — the exact code path of the defect.
    let build = || {
        let mut prop = PbPropagator::new();
        let cid = prop
            .add_constraint(
                &[
                    linear_term(2, 1),
                    linear_term(2, 2),
                    linear_term(1, 3),
                    linear_term(1, 4),
                ],
                PbRel::Ge,
                2,
            )
            .expect("constraint should be added");
        assert!(
            !prop.is_counting_for_test(cid),
            "row must not be counting at construction for this repro"
        );
        (prop, cid)
    };

    let mut exercised = false;
    for stop_at in 1..12u32 {
        let (mut prop, cid) = build();
        let mut calls = 0u32;
        let result = prop.assign_literal_interruptible(-1, 1, || {
            calls += 1;
            calls >= stop_at
        });
        // Only the "assignment landed, notification abandoned" interleaving
        // reproduces the defect.
        if !matches!(result, PropResult::Interrupted) || prop.value(-1) != LitValue::True {
            continue;
        }
        exercised = true;

        // Re-enter with a fresh budget: the interruptible rebuild converts
        // the (now blind) row to counting mid-rebuild.
        assert_eq!(prop.propagate_interruptible(|| false), PropResult::Ok);
        assert!(
            prop.is_counting_for_test(cid),
            "repaired blind row should have converted to counting"
        );

        // Every literal must hold exactly ONE watch entry for the row.
        for var in 1..=4 {
            let idx = lit_index(var).expect("valid literal");
            let entries = prop.watches[idx].iter().filter(|&&c| c == cid).count();
            assert_eq!(
                entries, 1,
                "literal x{var} must hold exactly one watch entry, found {entries}"
            );
        }

        // With duplicate entries the counting pre-pass double-decrements and
        // this satisfiable assignment (c + d >= 2 still holds) reports a
        // spurious conflict; the correct outcome is the propagation of c/d.
        let result = prop.assign_literal(-2, 1);
        assert!(
            !matches!(result, PropResult::Conflict(_, _)),
            "spurious conflict on a satisfiable row: {result:?}"
        );
        assert_eq!(
            prop.slack_for_test(cid),
            prop.exact_weighted_slack_for_test(cid),
            "counting slack diverged from exact slack"
        );
    }
    assert!(
        exercised,
        "no interrupt point produced the assignment-landed/notify-abandoned interleaving"
    );
}

#[test]
fn test_multiple_backtrack_cycles() {
    // Test that multiple assign/unassign cycles work correctly.
    let mut prop = PbPropagator::new();
    let _ = prop.add_constraint(
        &[linear_term(2, 1), linear_term(2, 2), linear_term(1, 3)],
        PbRel::Ge,
        3,
    );

    // First cycle: falsify x3. With x3 false the constraint `2x1+2x2+x3 >= 3`
    // forces both x1 and x2 (exact slack 1 < coeff 2), and the row is armed
    // for full visibility at construction (watched slack 1 < max watched
    // coeff 2 — the P2d blindness rule), so the unwatched falsification of
    // x3 reports the first forced literal immediately. Historically this
    // returned `Ok` and relied on the caller's next full scan to find the
    // propagation.
    match prop.assign_literal(-3, 1) {
        PropResult::Propagated(lit, _, _) => {
            assert!(
                lit == 1 || lit == 2,
                "expected propagation of x1 or x2, got {lit}"
            );
        }
        other => panic!("expected propagation after falsifying x3, got {other:?}"),
    }
    prop.unassign_literal(-3);

    // Second cycle: falsify x1, should propagate x2 (since 2x2+x3>=3
    // requires x2=true) -- but x3 may also be propagated if it appears
    // first in the watched region after a swap.
    let r = prop.assign_literal(-1, 1);
    match r {
        PropResult::Propagated(lit, _, _) => {
            assert!(
                lit == 2 || lit == 3,
                "expected propagation of x2 or x3, got {lit}"
            );
        }
        other => panic!("expected propagation after falsifying x1, got {other:?}"),
    }
    prop.unassign_literal(-1);

    // Third cycle: everything should be back to normal.
    assert_eq!(prop.propagate(), PropResult::Ok);
}

#[test]
fn test_propagate_interruptible_stops_before_later_constraint_and_can_resume() {
    let mut prop = PbPropagator::new();
    for var in 1..=600 {
        let _ = prop.add_constraint(
            &[linear_term(1, var), linear_term(1, var + 600)],
            PbRel::Ge,
            1,
        );
    }

    let polls = Cell::new(0usize);
    let result = prop.propagate_interruptible(|| {
        let next = polls.get() + 1;
        polls.set(next);
        next >= 3
    });

    assert_eq!(result, PropResult::Interrupted);
    assert!(
        polls.get() >= 2,
        "interrupt should be observed during the scan"
    );
    assert_eq!(prop.propagate(), PropResult::Ok);
}

#[test]
fn test_assign_literal_interruptible_stops_before_later_impacted_constraint_and_can_resume() {
    let mut prop = PbPropagator::new();
    for offset in 0..600 {
        let x = 2 + offset * 2;
        let y = x + 1;
        let _ = prop.add_constraint(
            &[linear_term(1, 1), linear_term(1, x), linear_term(1, y)],
            PbRel::Ge,
            1,
        );
    }

    let polls = Cell::new(0usize);
    let result = prop.assign_literal_interruptible(-1, 1, || {
        let next = polls.get() + 1;
        polls.set(next);
        next >= 3
    });

    assert_eq!(result, PropResult::Interrupted);
    assert_eq!(prop.value(1), LitValue::False);
    assert!(
        polls.get() >= 2,
        "interrupt should be observed while processing watches"
    );
    assert_eq!(prop.propagate(), PropResult::Ok);
}

#[test]
fn test_unassign_literals_interruptible_repairs_without_rebuild() {
    let mut prop = PbPropagator::new();
    let cid = prop
        .add_constraint(&[linear_term(2, 1), linear_term(2, 2)], PbRel::Ge, 2)
        .expect("weighted constraint should be added");

    match prop.assign_literal(-1, 1) {
        PropResult::Propagated(lit, _, result_cid) => {
            assert_eq!(lit, 2);
            assert_eq!(result_cid, cid);
        }
        other => panic!("expected x2 propagation, got {other:?}"),
    }
    assert_eq!(prop.constraints[cid].slack, 0);

    let rebuilds_before = prop.rebuild_count();
    let interrupted = prop.unassign_literals_interruptible(&[-1], || false);

    assert!(!interrupted);
    assert_eq!(prop.rebuild_count(), rebuilds_before);
    assert!(!prop.needs_rebuild);
    assert_eq!(prop.value(1), LitValue::Unassigned);
    assert_eq!(prop.constraints[cid].slack, 2);
    assert_eq!(prop.propagate_constraint(cid), PropResult::Ok);
}

#[test]
fn test_unassign_literals_interruptible_stops_during_rebuild_and_can_resume() {
    let mut prop = PbPropagator::new();
    for offset in 0..600 {
        let x = 1 + offset * 2;
        let y = x + 1;
        let _ = prop.add_constraint(&[linear_term(1, x), linear_term(1, y)], PbRel::Ge, 1);
    }

    assert_eq!(prop.assign_literal(1, 1), PropResult::Ok);
    prop.needs_rebuild = true;

    let polls = Cell::new(0usize);
    let interrupted = prop.unassign_literals_interruptible(&[1], || {
        let next = polls.get() + 1;
        polls.set(next);
        next >= 3
    });

    assert!(interrupted, "interrupt should stop the rebuild pass");
    assert_eq!(prop.value(1), LitValue::Unassigned);
    assert!(
        polls.get() >= 2,
        "interrupt should be observed while rebuilding watched state"
    );
    assert_eq!(prop.propagate(), PropResult::Ok);
}

// -----------------------------------------------------------------------
// Counting-propagation equivalence / differential fuzz
// -----------------------------------------------------------------------

/// Deterministic splitmix64 PRNG for reproducible fuzzing without a dep.
struct Splitmix64(u64);

impl Splitmix64 {
    fn new(seed: u64) -> Self {
        Self(seed)
    }

    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    fn below(&mut self, bound: u64) -> u64 {
        self.next_u64() % bound.max(1)
    }
}

/// Generates a single random `>=` constraint over `num_vars` variables with
/// coefficients in `[1, max_coeff]`, optionally with one big-M coefficient to
/// exercise the big-M regime that defeats the watched-slack shortcut.
fn random_ge_constraint(
    rng: &mut Splitmix64,
    num_vars: u32,
    max_coeff: i128,
    big_m: bool,
) -> PbConstraint {
    let n = (rng.below(u64::from(num_vars - 1)) as u32 + 2).min(num_vars);
    // Pick `n` distinct variables.
    let mut vars: Vec<u32> = (1..=num_vars).collect();
    for i in (1..vars.len()).rev() {
        let j = rng.below((i + 1) as u64) as usize;
        vars.swap(i, j);
    }
    vars.truncate(n as usize);

    let mut terms = Vec::with_capacity(vars.len());
    let mut total: i128 = 0;
    for (idx, &var) in vars.iter().enumerate() {
        let coeff = if big_m && idx == 0 {
            // One dominating coefficient.
            max_coeff * (2 + rng.below(4) as i128)
        } else {
            1 + rng.below(max_coeff as u64) as i128
        };
        total = total.saturating_add(coeff);
        let negated = rng.below(2) == 1;
        terms.push(PbTerm {
            coeff,
            lits: vec![PbLit { var, negated }],
        });
    }
    // Degree somewhere in (0, total] so the constraint is non-trivial but
    // satisfiable by the all-true-ish assignment in at least some cases.
    let degree = 1 + rng.below(total.max(1) as u64) as i128;
    PbConstraint {
        terms,
        rel: PbRel::Ge,
        rhs: degree,
    }
}

/// Drives a propagator to fixpoint by repeatedly applying its own
/// propagations, returning the conflict status and the set of literals that
/// became forced-true (beyond the supplied decisions). Decision level is a
/// single shared level for simplicity; this exercises conflict/propagation
/// detection without the asserting-loop machinery.
fn drive_to_fixpoint(
    prop: &mut PbPropagator,
    level: u32,
) -> (bool, std::collections::BTreeSet<Lit>) {
    let mut forced = std::collections::BTreeSet::new();
    loop {
        match prop.propagate() {
            PropResult::Ok | PropResult::Interrupted => {
                return (false, forced);
            }
            PropResult::Conflict(..) => {
                return (true, forced);
            }
            PropResult::Propagated(lit, _reason, _cid) => {
                forced.insert(lit);
                match prop.assign_literal(lit, level) {
                    PropResult::Conflict(..) => return (true, forced),
                    _ => {}
                }
            }
        }
    }
}

/// Brute-force exact slack and forced/conflict status of a single `>=`
/// constraint under a partial assignment given as `value(var) -> Option<bool>`.
fn brute_force_single(
    constraint: &PbConstraint,
    values: &[Option<bool>],
) -> (i128, bool, std::collections::BTreeSet<Lit>) {
    // slack = sum(coeff over non-false terms) - degree
    let mut slack: i128 = -constraint.rhs;
    for term in &constraint.terms {
        let lit = pb_lit_to_dimacs(term.lits[0]);
        let var = lit.unsigned_abs() as usize - 1;
        let is_false = match values[var] {
            Some(v) => {
                let lit_val = if lit > 0 { v } else { !v };
                !lit_val
            }
            None => false,
        };
        if !is_false {
            slack = slack.saturating_add(term.coeff);
        }
    }
    let conflict = slack < 0;
    let mut forced = std::collections::BTreeSet::new();
    if !conflict {
        for term in &constraint.terms {
            let lit = pb_lit_to_dimacs(term.lits[0]);
            let var = lit.unsigned_abs() as usize - 1;
            if values[var].is_none() && term.coeff > slack {
                forced.insert(lit);
            }
        }
    }
    (slack, conflict, forced)
}

#[test]
fn counting_matches_watched_on_random_big_m_constraints() {
    // For each random constraint, run an identical sequence of decisions
    // through a counting propagator and a watched propagator and assert they
    // reach the same UNSAT status and the same forced-literal fixpoint set.
    // Also assert the counting propagator's incremental slack equals the
    // freshly-recomputed exact slack at every step, and that its per-step
    // decisions match a brute-force exact reference (soundness).
    let num_vars: u32 = 18;
    for seed in 0..4000u64 {
        let mut rng = Splitmix64::new(seed.wrapping_mul(0x100_0001).wrapping_add(7));
        let big_m = rng.below(2) == 1;
        let max_coeff = 1 + rng.below(50) as i128;
        let constraint = random_ge_constraint(&mut rng, num_vars, max_coeff, big_m);

        let mut counting = PbPropagator::new();
        counting.disable_blind_arming_for_test();
        let cid_c = counting.add_from_pb_constraint(&constraint);
        let mut watched = PbPropagator::new();
        // The watched twin must STAY on the pure watched scheme: the P2d
        // blind-row arming would otherwise convert it to counting mid-walk.
        watched.disable_blind_arming_for_test();
        let cid_w = watched.add_from_pb_constraint(&constraint);
        let (Some(cid_c), Some(cid_w)) = (cid_c, cid_w) else {
            continue; // trivially satisfied
        };
        counting.set_constraint_counting_for_test(cid_c, true);
        watched.set_constraint_counting_for_test(cid_w, false);
        // Only weighted constraints can be counting; skip pure cardinality
        // / clause shapes generated by chance (they share the unchanged
        // fast paths and are not the subject of this differential).
        if !counting.is_counting_for_test(cid_c) {
            continue;
        }
        assert!(!watched.is_counting_for_test(cid_w));

        // Track each variable's value for the brute-force reference.
        let mut values: Vec<Option<bool>> = vec![None; num_vars as usize];

        // Random decision sequence with occasional full backtracks.
        let num_steps = 30 + rng.below(40) as usize;
        let mut decisions: Vec<Lit> = Vec::new();
        for _ in 0..num_steps {
            if !decisions.is_empty() && rng.below(4) == 0 {
                // Backtrack: unassign all decisions and re-derived literals.
                let to_unassign: Vec<Lit> = (1..=num_vars as i32).collect();
                counting.unassign_literals(&to_unassign);
                watched.unassign_literals(&to_unassign);
                for v in &mut values {
                    *v = None;
                }
                decisions.clear();
                continue;
            }

            // Choose a random currently-unassigned variable and polarity.
            let unassigned: Vec<u32> = (1..=num_vars)
                .filter(|&v| values[v as usize - 1].is_none())
                .collect();
            if unassigned.is_empty() {
                continue;
            }
            let pick = unassigned[rng.below(unassigned.len() as u64) as usize];
            let polarity = rng.below(2) == 1;
            let lit: Lit = if polarity {
                pick as i32
            } else {
                -(pick as i32)
            };

            // Apply the decision to both propagators and the reference.
            let r_c = counting.assign_literal(lit, 1);
            let r_w = watched.assign_literal(lit, 1);
            values[pick as usize - 1] = Some(polarity);

            // Incremental slack must equal the exact recomputation.
            if counting.value(lit) != LitValue::Unassigned {
                assert_eq!(
                    counting.slack_for_test(cid_c),
                    counting.exact_weighted_slack_for_test(cid_c),
                    "seed {seed}: counting slack diverged from exact after assigning {lit}"
                );
            }

            // Brute-force reference for the single constraint.
            let (ref_slack, ref_conflict, ref_forced) = brute_force_single(&constraint, &values);

            // If the decision created a watched conflict, the counting path
            // must also report a conflict (or have already, before reaching
            // the just-assigned literal). We validate via fixpoint below, so
            // here we only sanity-check the immediate result variants are
            // sound: a reported conflict must be a real conflict.
            if let PropResult::Conflict(..) = r_c {
                assert!(
                        ref_conflict || ref_slack < 0 || would_conflict_after(&counting, cid_c),
                        "seed {seed}: counting reported a conflict that is not real (slack {ref_slack})"
                    );
            }
            let _ = (&r_w, &ref_forced);

            decisions.push(lit);

            // Drive both to fixpoint and compare UNSAT + forced sets.
            let (c_unsat, c_forced) = drive_to_fixpoint(&mut counting, 1);
            let (w_unsat, w_forced) = drive_to_fixpoint(&mut watched, 1);
            assert_eq!(
                c_unsat, w_unsat,
                "seed {seed}: counting/watched disagree on UNSAT after {lit}"
            );
            assert_eq!(
                c_forced, w_forced,
                "seed {seed}: counting/watched disagree on forced set after {lit}"
            );

            // Sync the brute-force reference with the literals the fixpoint
            // forced, then re-validate counting slack vs exact.
            for &f in &c_forced {
                let var = f.unsigned_abs() as usize - 1;
                if values[var].is_none() {
                    values[var] = Some(f > 0);
                }
            }
            assert_eq!(
                counting.slack_for_test(cid_c),
                counting.exact_weighted_slack_for_test(cid_c),
                "seed {seed}: counting slack diverged from exact at fixpoint"
            );

            if c_unsat {
                // Backtrack to continue fuzzing.
                let to_unassign: Vec<Lit> = (1..=num_vars as i32).collect();
                counting.unassign_literals(&to_unassign);
                watched.unassign_literals(&to_unassign);
                for v in &mut values {
                    *v = None;
                }
                decisions.clear();
            }
        }
    }
}

/// Helper: true if a fresh exact slack for `cid` is negative (real conflict).
fn would_conflict_after(prop: &PbPropagator, cid: usize) -> bool {
    prop.exact_weighted_slack_for_test(cid) < 0
}

#[test]
fn counting_propagation_is_sound_vs_brute_force_small() {
    // Exhaustively check that on small constraints, counting propagation
    // never reports a spurious conflict and never forces a literal that is
    // not actually entailed, across all partial assignments reachable by a
    // fixed decision order.
    let num_vars: u32 = 6;
    for seed in 0..2000u64 {
        let mut rng = Splitmix64::new(seed.wrapping_mul(0x9E3F).wrapping_add(101));
        let big_m = rng.below(2) == 1;
        let max_coeff = 1 + rng.below(8) as i128;
        let constraint = random_ge_constraint(&mut rng, num_vars, max_coeff, big_m);

        let mut prop = PbPropagator::new();
        let Some(cid) = prop.add_from_pb_constraint(&constraint) else {
            continue;
        };
        prop.set_constraint_counting_for_test(cid, true);
        if !prop.is_counting_for_test(cid) {
            continue;
        }

        let mut values: Vec<Option<bool>> = vec![None; num_vars as usize];
        let order: Vec<u32> = {
            let mut v: Vec<u32> = (1..=num_vars).collect();
            for i in (1..v.len()).rev() {
                let j = rng.below((i + 1) as u64) as usize;
                v.swap(i, j);
            }
            v
        };

        for &var in &order {
            let polarity = rng.below(2) == 1;
            let lit: Lit = if polarity { var as i32 } else { -(var as i32) };
            let result = prop.assign_literal(lit, 1);
            values[var as usize - 1] = Some(polarity);

            let (ref_slack, ref_conflict, ref_forced) = brute_force_single(&constraint, &values);

            // Slack must be exact.
            assert_eq!(
                prop.slack_for_test(cid),
                ref_slack,
                "seed {seed}: slack mismatch (got {}, exact {ref_slack})",
                prop.slack_for_test(cid)
            );

            match result {
                PropResult::Conflict(..) => {
                    assert!(
                        ref_conflict,
                        "seed {seed}: spurious conflict reported (slack {ref_slack})"
                    );
                }
                PropResult::Propagated(plit, reason, _) => {
                    assert!(
                        !ref_conflict,
                        "seed {seed}: propagated under a conflicting assignment"
                    );
                    assert!(
                        ref_forced.contains(&plit),
                        "seed {seed}: propagated {plit} that is not entailed"
                    );
                    // Reason literals must all be currently false (clause-style).
                    for &rl in reason.iter().skip(1) {
                        assert_eq!(
                            prop.value(rl),
                            LitValue::False,
                            "seed {seed}: reason literal {rl} is not false"
                        );
                    }
                }
                PropResult::Ok | PropResult::Interrupted => {
                    // No conflict reported: there must be no real conflict
                    // detectable from the just-assigned literal's touch.
                    // (Other forced literals may still exist; full propagate
                    // would surface them.)
                }
            }

            if ref_conflict {
                break;
            }
        }
    }
}

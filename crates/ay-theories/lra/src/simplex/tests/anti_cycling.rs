// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn least_index_phase_moves_leaving_basic_to_its_bound_without_clamping_entering() {
    let terms = TermStore::new();
    let mut solver = LraSolver::new(&terms);
    solver.vars = vec![
        basic_var(0, Some(bound_with_reason(10, 100, true, 1, 1)), None),
        nonbasic_var(None, Some(bound_with_reason(5, 101, true, 1, 1))),
        nonbasic_var(None, None),
    ];
    solver.rows = vec![TableauRow::new_rat(
        0,
        vec![(1, Rational::from(1i64)), (2, Rational::from(1i64))],
        Rational::from(0i64),
    )];
    solver.next_var = 3;
    solver.basic_var_to_row.insert(0, 0);
    solver.col_index = vec![
        Vec::new(),
        vec![ColEntry::new(0, 0)],
        vec![ColEntry::new(0, 1)],
    ];
    solver.bland_mode = true;
    assert_eq!(
        solver.find_pivot_candidate(0, BoundType::Lower),
        Some((1, 1)),
        "the smaller eligible nonbasic must enter"
    );

    let target =
        solver.compute_update_amount_with_coeff(0, 1, BoundType::Lower, &Rational::from(1i64));
    assert_eq!(target, InfRational::from_rational(int(10)));
    solver.update_nonbasic(1, target);
    solver.pivot(0, 1);
    solver.track_var_feasibility(1);

    assert_eq!(solver.vars[0].value, InfRational::from_rational(int(10)));
    assert_eq!(solver.vars[0].status, Some(VarStatus::NonBasic));
    assert_eq!(solver.vars[1].status, Some(VarStatus::Basic(0)));
    assert_eq!(solver.pop_greatest_error(), Some((0, BoundType::Upper)));
}

#[test]
fn new_check_rekeys_a_nonstale_least_index_heap_for_the_ordinary_phase() {
    let terms = TermStore::new();
    let mut solver = LraSolver::new(&terms);
    solver.vars = vec![
        basic_var(0, Some(bound_with_reason(1, 100, true, 1, 1)), None),
        VarInfo {
            status: Some(VarStatus::Basic(1)),
            ..basic_var(0, Some(bound_with_reason(2, 101, true, 1, 1)), None)
        },
        nonbasic_var(None, None),
        nonbasic_var(None, None),
        nonbasic_var(None, None),
    ];
    solver.rows = vec![
        TableauRow::new_rat(
            0,
            vec![(2, Rational::from(1i64)), (4, Rational::from(1i64))],
            Rational::from(0i64),
        ),
        TableauRow::new_rat(1, vec![(3, Rational::from(1i64))], Rational::from(0i64)),
    ];
    solver.next_var = 5;
    solver.basic_var_to_row.insert(0, 0);
    solver.basic_var_to_row.insert(1, 1);
    solver.col_index = vec![
        Vec::new(),
        Vec::new(),
        vec![ColEntry::new(0, 0)],
        vec![ColEntry::new(1, 0)],
        vec![ColEntry::new(0, 1)],
    ];
    solver.bland_mode = true;
    solver.rebuild_infeasible_heap();
    assert_eq!(solver.infeasible_heap.peek().map(|key| key.1), Some(0));
    assert!(!solver.heap_stale);

    // The zero-iteration budget preserves the heap for inspection. Resetting
    // least-index mode must rekey it even though membership was not stale.
    assert!(matches!(
        solver.dual_simplex_with_max_iters(0),
        TheoryResult::Unknown
    ));
    assert!(!solver.bland_mode);
    assert_eq!(solver.infeasible_heap.peek().map(|key| key.1), Some(1));
}

#[test]
fn long_tableau_enters_least_index_phase_and_selects_its_smallest_violated_basic() {
    // 1,000 independent width-one rows pivot first. The two remaining
    // violated basics are 1000 (width two, violation one) and 1001 (width
    // one, violation two). Both the ordinary shortest-row and greatest-error
    // heuristics would select 1001; the least-index phase must select 1000.
    const ROWS: usize = BLAND_THRESHOLD as usize + 2;
    let terms = TermStore::new();
    let mut solver = LraSolver::new(&terms);
    let extra_var = (2 * ROWS) as u32;
    solver.vars = (0..ROWS)
        .map(|row| VarInfo {
            value: InfRational::from_rational(int(0)),
            lower: Some(crate::Bound::new(
                int(if row < BLAND_THRESHOLD as usize {
                    3
                } else if row == ROWS - 1 {
                    2
                } else {
                    1
                })
                .into(),
                Vec::new(),
                Vec::new(),
                Vec::new(),
                false,
            )),
            upper: None,
            status: Some(VarStatus::Basic(row)),
        })
        .chain((0..=ROWS).map(|_| nonbasic_var(None, None)))
        .collect();
    solver.next_var = extra_var + 1;
    solver.col_index = vec![Vec::new(); solver.vars.len()];
    for row in 0..ROWS {
        let entering = (ROWS + row) as u32;
        let mut coeffs = vec![(entering, Rational::from(1i64))];
        solver.col_index[entering as usize].push(ColEntry::new(row, 0));
        if row == ROWS - 2 {
            coeffs.push((extra_var, Rational::from(1i64)));
            solver.col_index[extra_var as usize].push(ColEntry::new(row, 1));
        }
        solver.rows.push(TableauRow::new_rat(
            row as u32,
            coeffs,
            Rational::from(0i64),
        ));
        solver.basic_var_to_row.insert(row as u32, row);
    }

    // Stop immediately after the 1,001st real pivot so the chosen row remains
    // observable. The check budget, including its Unknown verdict, is retained.
    solver.stats.check_pivot_count = solver.check_pivot_budget() - (BLAND_THRESHOLD + 1);
    let result = solver.dual_simplex_with_max_iters(ROWS + 1);
    assert!(matches!(result, TheoryResult::Unknown));
    assert!(solver.bland_mode);
    assert_eq!(solver.pivots_before_bland, BLAND_THRESHOLD);
    assert_eq!(solver.stats.total_pivots, u64::from(BLAND_THRESHOLD + 1));
    assert_eq!(
        solver.vars[ROWS - 2].status,
        Some(VarStatus::NonBasic),
        "the least-index phase must repair basic 1000 before 1001"
    );
    assert_eq!(
        solver.vars[ROWS - 1].status,
        Some(VarStatus::Basic(ROWS - 1))
    );

    // The artificial check budget stopped after pivot, before heap re-tracking.
    // It must mark the heap stale; the next check rebuilds and finishes.
    solver.stats.check_pivot_count = 0;
    assert!(solver.heap_stale);
    assert!(matches!(
        solver.dual_simplex_with_max_iters(ROWS + 1),
        TheoryResult::Sat
    ));
}

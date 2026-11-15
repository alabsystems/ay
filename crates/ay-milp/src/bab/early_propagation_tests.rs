// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
//! Direct controls for the bounded admission around the shared row kernel.
use super::*;
use crate::model::Col;
use ay_test_support::env::lock_env;

fn loose_model(rows: usize) -> Model {
    let mut m = Model::new();
    let x = m.add_binary_col();
    m.add_col(-1.0, 1.0);
    m.add_col(-1.0, 1.0);
    for _ in 0..rows {
        m.add_row(f64::NEG_INFINITY, 2.0, &[(x, 1.0)]);
    }
    m
}
fn state(m: &Model) -> EarlyPropagation {
    EarlyPropagation::new(m, SearchMode::FULL, true, true, Activation::MarkedMargin)
}
fn bounds(m: &Model) -> (Vec<f64>, Vec<f64>) {
    (0..m.num_cols())
        .map(|i| m.col_bounds(Col(i as u32)))
        .unzip()
}
fn run(s: &mut EarlyPropagation, m: &Model, lo: &mut [f64], hi: &mut [f64]) -> Option<bool> {
    s.propagate(m, 1, &column_rows(m), &[0], lo, hi, None, 0, None)
}

#[test]
fn early_marked_activation_and_default_class_are_both_required() {
    let _guard = lock_env();
    let m = loose_model(1);
    assert!(state(&m).report.eligible);
    for (enabled, default, activation) in [
        (false, true, Activation::MarkedMargin),
        (true, false, Activation::MarkedMargin),
        (true, true, Activation::Legacy),
    ] {
        let mut s = EarlyPropagation::new(&m, SearchMode::FULL, enabled, default, activation);
        let (mut lo, mut hi) = bounds(&m);
        assert_eq!(run(&mut s, &m, &mut lo, &mut hi), None);
        assert!(!s.report.eligible);
        assert_eq!(s.report.attempts, 0);
    }
}

#[test]
fn early_nested_projected_cheap_and_dfs_modes_decline() {
    let _guard = lock_env();
    let m = loose_model(1);
    let mut modes = [SearchMode::FULL; 4];
    modes[0].depth = 1;
    modes[1].projected = true;
    modes[2].cheap = true;
    modes[3].dfs = true;
    for mode in modes {
        assert!(
            !EarlyPropagation::new(&m, mode, true, true, Activation::MarkedMargin)
                .report
                .eligible
        );
    }
}

#[test]
fn early_inexact_source_and_oversized_column_scratch_decline() {
    let _guard = lock_env();
    let mut m = loose_model(1);
    m.record_inexact_row_coeff(
        Row(0),
        0,
        num_rational::BigRational::new(1.into(), 3.into()),
    );
    assert!(!state(&m).report.eligible);
    let mut wide = Model::new();
    for _ in 0..=MAX_COLUMNS {
        wide.add_col(0.0, 1.0);
    }
    assert!(!state(&wide).report.eligible);
}

#[test]
fn early_deadline_memory_foreign_source_and_shape_preserve_box() {
    let _guard = lock_env();
    let m = loose_model(1);
    let foreign = m.clone();
    let (lo, hi) = bounds(&m);
    let mut s = state(&m);
    let (mut l, mut u) = (lo.clone(), hi.clone());
    assert_eq!(
        s.propagate(
            &m,
            4,
            &column_rows(&m),
            &[0],
            &mut l,
            &mut u,
            Some(Instant::now()),
            0,
            None
        ),
        None
    );
    assert_eq!((l.clone(), u.clone()), (lo.clone(), hi.clone()));
    assert_eq!(s.report.deadline_limits, 1);
    assert_eq!(
        s.propagate(
            &m,
            5,
            &column_rows(&m),
            &[0],
            &mut l,
            &mut u,
            None,
            1,
            Some(SCRATCH_BYTES)
        ),
        None
    );
    assert_eq!(s.report.memory_declines, 1);
    assert_eq!(
        s.propagate(
            &foreign,
            6,
            &column_rows(&foreign),
            &[0],
            &mut l,
            &mut u,
            None,
            0,
            None
        ),
        None
    );
    assert_eq!(
        s.propagate(&m, 7, &[], &[0], &mut l, &mut u, None, 0, None),
        None
    );
    assert_eq!((l, u), (lo, hi));
    assert_eq!(s.report.visits, 0);
}

#[test]
fn early_call_allowance_is_per_state_and_never_renews() {
    let _guard = lock_env();
    let m = loose_model(1);
    let (mut lo, mut hi) = bounds(&m);
    let mut s = state(&m);
    for _ in 0..MAX_CALLS {
        assert_eq!(run(&mut s, &m, &mut lo, &mut hi), Some(true));
    }
    assert_eq!(s.report.attempts, MAX_CALLS);
    assert_eq!(s.report.visits, MAX_CALLS);
    let snapshot = (s.report.attempts, s.report.visits);
    assert_eq!(run(&mut s, &m, &mut lo, &mut hi), None);
    assert_eq!((s.report.attempts, s.report.visits), snapshot);
    assert_eq!(run(&mut state(&m), &m, &mut lo, &mut hi), Some(true));
}

#[test]
fn early_row_visits_are_capped_and_terms_count_only_inspected_rows() {
    let _guard = lock_env();
    let m = loose_model(200);
    let (mut lo, mut hi) = bounds(&m);
    let mut s = state(&m);
    while run(&mut s, &m, &mut lo, &mut hi).is_some() {}
    assert_eq!(s.report.attempts, MAX_CALLS);
    assert_eq!(s.report.visits, MAX_VISITS);
    assert_eq!(s.report.terms, MAX_VISITS);
    assert_eq!(s.report.row_limits, MAX_CALLS);
    assert_eq!(s.report.visited_rows.len(), MAX_VISITS);
    assert!(s
        .report
        .visited_rows
        .iter()
        .all(|&r| (r as usize) < ROWS_PER_CALL));
}

#[test]
fn early_wide_rows_spend_visits_without_entering_arithmetic() {
    let _guard = lock_env();
    let mut m = Model::new();
    let cols: Vec<_> = (0..65).map(|_| m.add_col(0.0, 1.0)).collect();
    let terms: Vec<_> = cols.iter().map(|&c| (c, 1.0)).collect();
    m.add_row(f64::NEG_INFINITY, 0.0, &terms);
    let (mut lo, mut hi) = bounds(&m);
    let original = (lo.clone(), hi.clone());
    let mut s = state(&m);
    assert_eq!(run(&mut s, &m, &mut lo, &mut hi), Some(true));
    assert_eq!((lo, hi), original);
    assert_eq!(
        (s.report.visits, s.report.skipped_wide, s.report.terms),
        (1, 1, 0)
    );
}

#[test]
fn early_shared_kernel_matches_legacy_box_bits_on_complete_cascade() {
    let _guard = lock_env();
    let mut m = Model::new();
    let x = m.add_binary_col();
    let y = m.add_binary_col();
    let z = m.add_col(-2.0, 2.0);
    m.add_col(-1.0, 1.0);
    m.add_row(f64::NEG_INFINITY, 1.0, &[(x, 1.0), (y, 1.0)]);
    m.add_row(0.0, 0.0, &[(z, 1.0), (y, -1.0)]);
    let (mut lo, mut hi) = bounds(&m);
    lo[0] = 1.0;
    let (mut legacy_lo, mut legacy_hi) = (lo.clone(), hi.clone());
    let adjacency = column_rows(&m);
    let legacy = super::super::propagate_branch_rows_many(
        &m,
        &adjacency,
        &[0],
        &mut legacy_lo,
        &mut legacy_hi,
    );
    let mut s = state(&m);
    let early = s.propagate(&m, 2, &adjacency, &[0], &mut lo, &mut hi, None, 0, None);
    assert_eq!(early, Some(legacy));
    assert_eq!(
        lo.iter().map(|x| x.to_bits()).collect::<Vec<_>>(),
        legacy_lo.iter().map(|x| x.to_bits()).collect::<Vec<_>>()
    );
    assert_eq!(
        hi.iter().map(|x| x.to_bits()).collect::<Vec<_>>(),
        legacy_hi.iter().map(|x| x.to_bits()).collect::<Vec<_>>()
    );
    assert!(s.report.binary_fixings > 0 && s.report.tightenings > 0);
}

#[test]
fn early_strict_conflict_and_tie_keep_closed_feasible_witnesses() {
    let _guard = lock_env();
    for rhs in [0.5, 1.0] {
        let mut m = Model::new();
        let x = m.add_binary_col();
        let y = m.add_binary_col();
        m.add_col(-1.0, 1.0);
        m.add_col(-1.0, 1.0);
        m.add_row(f64::NEG_INFINITY, rhs, &[(x, 1.0), (y, 1.0)]);
        let (mut lo, mut hi) = bounds(&m);
        lo[0] = 1.0;
        let mut s = state(&m);
        let alive = run(&mut s, &m, &mut lo, &mut hi);
        if rhs == 0.5 {
            assert_eq!(alive, Some(false));
            assert!(s.report.conflicts > 0);
            assert_eq!(s.report.accepted_prunes, 1);
            assert_eq!(s.report.first_conflict_node, Some(1));
        } else {
            assert_eq!(alive, Some(true));
            assert!(lo[0] <= 1.0 && hi[0] >= 1.0 && lo[1] <= 0.0 && hi[1] >= 0.0);
            assert_eq!(s.report.conflicts, 0);
        }
    }
}

#[test]
fn early_structural_multiseed_and_degenerate_boxes_preserve_point() {
    let _guard = lock_env();
    let mut m = Model::new();
    let x = m.add_binary_col();
    let y = m.add_binary_col();
    let z = m.add_col(0.0, 0.0);
    m.add_col(-1.0, 1.0);
    m.add_row(1.0, 1.0, &[(x, 1.0), (y, 1.0), (z, 1.0)]);
    let (mut lo, mut hi) = bounds(&m);
    lo[0] = 1.0;
    hi[1] = 0.0;
    let mut s = state(&m);
    assert_eq!(
        s.propagate(
            &m,
            3,
            &column_rows(&m),
            &[0, 1, 0],
            &mut lo,
            &mut hi,
            None,
            0,
            None
        ),
        Some(true)
    );
    assert!(lo[0] <= 1.0 && hi[0] >= 1.0 && lo[1] <= 0.0 && hi[1] >= 0.0);
    assert_eq!((lo[2], hi[2]), (0.0, 0.0));
    assert_eq!(
        (s.report.first_node, s.report.last_node),
        (Some(3), Some(3))
    );
}

#[test]
fn early_value_row_and_queue_caps_never_mutate_legacy_globals() {
    let _guard = lock_env();
    let m = loose_model(10);
    let adjacency = column_rows(&m);
    let (mut lo, mut hi) = bounds(&m);
    let mut c = Control::Bounded {
        rows: 3,
        queue: 1,
        deadline: None,
        run: Report::default(),
    };
    assert!(super::super::propagate_branch_rows_many_t(
        &m,
        &adjacency,
        &[0],
        &mut lo,
        &mut hi,
        &mut NoDeps,
        &mut c
    ));
    let Control::Bounded {
        run, rows, queue, ..
    } = c
    else {
        unreachable!()
    };
    assert_eq!((rows, queue, run.visits, run.row_limits), (3, 1, 3, 1));
    assert_eq!(Control::Legacy.queue_capacity(2, 64), 2);
    assert_eq!(Control::Legacy.rows(192), 192);
    assert_eq!(Control::Legacy.queue(64), 64);

    let mut cascade = Model::new();
    let x = cascade.add_binary_col();
    let y = cascade.add_binary_col();
    cascade.add_row(f64::NEG_INFINITY, 1.0, &[(x, 1.0), (y, 1.0)]);
    let (mut lo, mut hi) = bounds(&cascade);
    lo[0] = 1.0;
    let mut c = Control::Bounded {
        rows: 64,
        queue: 1,
        deadline: None,
        run: Report::default(),
    };
    assert!(super::super::propagate_branch_rows_many_t(
        &cascade,
        &column_rows(&cascade),
        &[0],
        &mut lo,
        &mut hi,
        &mut NoDeps,
        &mut c
    ));
    let Control::Bounded { run, .. } = c else {
        unreachable!()
    };
    assert!(run.queue_limits > 0);
    assert_eq!(run.conflicts, 0);
    assert!(lo[0] <= 1.0 && hi[0] >= 1.0 && lo[1] <= 0.0 && hi[1] >= 0.0);
}

#[test]
fn early_per_row_clock_refuses_without_inspecting_or_pruning() {
    let _guard = lock_env();
    let m = loose_model(1);
    let adjacency = column_rows(&m);
    let (mut lo, mut hi) = bounds(&m);
    let original = (lo.clone(), hi.clone());
    let mut c = Control::Bounded {
        rows: 64,
        queue: 64,
        deadline: Some(Instant::now()),
        run: Report::default(),
    };
    assert!(super::super::propagate_branch_rows_many_t(
        &m,
        &adjacency,
        &[0],
        &mut lo,
        &mut hi,
        &mut NoDeps,
        &mut c
    ));
    let Control::Bounded { run, .. } = c else {
        unreachable!()
    };
    assert_eq!((run.visits, run.conflicts, run.deadline_limits), (0, 0, 1));
    assert_eq!((lo, hi), original);
}

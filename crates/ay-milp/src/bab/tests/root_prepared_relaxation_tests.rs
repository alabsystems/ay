// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Root prepared-relaxation authorization and end-to-end handoff tests.

use super::*;

#[test]
fn root_relaxation_reuse_requires_an_exact_complete_optimal_snapshot() {
    let mut model = Model::new();
    let x = model.add_binary_col();
    model.add_row(0.0, 1.0, &[(x, 1.0)]);
    let lp = FloatLp::from_model(&model, &[], Sense::Minimize).expect("lowered LP");
    let root = lp.solve_bounded(&lp.lower, &lp.upper, None, None);
    assert_eq!(root.status, SimplexStatus::Optimal);
    let prepared = prepare_root_relaxation(&lp, &root, &lp.lower, &lp.upper);
    assert!(prepared.is_some());

    lp.cut_slots_live.set(true);
    assert!(
        prepare_root_relaxation(&lp, &root, &lp.lower, &lp.upper).is_none(),
        "a row-rewritten LP must decline even when dimensions and bounds match"
    );
    let mut stale = 0;
    assert!(
        revalidate_prepared_relaxation(&lp, prepared, &mut stale).is_none(),
        "a Candidate prepared before a row rewrite must not be consumed"
    );
    assert_eq!(stale, 1, "the row-generation mismatch must be observable");
    lp.cut_slots_live.set(false);

    let mut narrowed = lp.lower.clone();
    narrowed[0] = 1.0;
    assert!(prepare_root_relaxation(&lp, &root, &narrowed, &lp.upper).is_none());

    for corrupt in ["status", "basis", "at", "values", "duals"] {
        let mut partial = root.clone();
        match corrupt {
            "status" => partial.status = SimplexStatus::Stopped,
            "basis" => {
                partial.basis.pop();
            }
            "at" => {
                partial.at.pop();
            }
            "values" => {
                partial.values.pop();
            }
            "duals" => {
                partial.duals.pop();
            }
            _ => unreachable!(),
        }
        assert!(
            prepare_root_relaxation(&lp, &partial, &lp.lower, &lp.upper).is_none(),
            "partial {corrupt} snapshot must decline"
        );
    }
}

/// End-to-end guard for the optimization: a real fractional MILP reaches
/// the root node under a deterministic one-node cap and consumes the
/// already-solved root Candidate through the direct prepared lane.  Merely
/// unit-testing `prepare_root_relaxation` would not catch wiring the result
/// back to `prepared: None` at the node construction site.
#[test]
fn first_tree_node_consumes_the_prepared_root_relaxation() {
    let _env_lock = lock_env();
    let (m, _) = market_split_with_floored_objective();
    let before = ROOT_PREPARED_CONSUMED.with(std::cell::Cell::get);
    let _ = solve_node_capped(&m, 1);
    let after = ROOT_PREPARED_CONSUMED.with(std::cell::Cell::get);
    assert_eq!(
        after,
        before + 1,
        "root node did not consume its root LP result"
    );
}

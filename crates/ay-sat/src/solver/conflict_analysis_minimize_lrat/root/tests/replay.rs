// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]
use super::*;

#[test]
fn actual_analyzed_root_hints_pass_independent_replay_and_omitting_the_root_fails() {
    let (mut s, conflict, _) = analysis_fixture(Roots::Input);
    let owner = test_owner(1_000_000, 1_000_000);
    assert!(s.attach_counted_admission(owner.clone()).is_ok());
    let result = run(&mut s, conflict).unwrap();
    assert_eq!(result.clause, [neg(2)]);
    let root_id = s.visible_unit_proof_id_for_lit(pos(0)).unwrap();
    assert!(result.chain.contains(&root_id));
    let base = s.cold.clause_trace.as_ref().unwrap();
    let next = base.entries().iter().map(|e| e.id).max().unwrap() + 1;
    for omit in [false, true] {
        let mut trace = base.clone();
        let hints: Vec<_> = result
            .chain
            .iter()
            .rev()
            .copied()
            .filter(|&id| id != 0 && (!omit || id != root_id))
            .collect();
        trace
            .prepare_counted_add(next, &result.clause, false, &hints, &owner)
            .unwrap()
            .commit();
        trace
            .prepare_counted_add(next + 1, &[pos(2)], true, &[], &owner)
            .unwrap()
            .commit();
        trace
            .prepare_counted_add(next + 2, &[], false, &[next, next + 1], &owner)
            .unwrap()
            .commit();
        assert_eq!(
            crate::test_util::strict_lrat_trace_replay(&trace, 5),
            !omit,
            "the exact recorded root hint must reach standalone strict replay"
        );
        // Conversion is a different contract: it can reconstruct the missing
        // root support and then independently validate the repaired DAG.
        let checked = crate::validate_clause_trace_resolution(
            &trace,
            5,
            &crate::ResolutionValidationLimits::unbounded(),
        );
        assert!(checked.is_ok(), "{checked:?}");
    }
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[path = "original_retirement/resources.rs"]
mod resources;

fn noisy_originals(width: u32) -> (Vec<(u64, Vec<Literal>)>, Vec<Literal>) {
    let mut satisfied = Vec::new();
    for variable in 0..width {
        satisfied.extend([pos(variable), pos(variable)]);
    }
    satisfied.push(pos(width));
    let originals = vec![(1, satisfied), (2, vec![pos(width - 1), pos(width + 1)])];
    let mut target: Vec<_> = (0..width).map(pos).collect();
    target.extend([neg(width), pos(width + 1)]);
    (originals, target)
}

fn oracle_chain(
    root: &mut RootPropagation,
    originals: &[(u64, Vec<Literal>)],
    target: &[Literal],
    meter: &mut ConversionMeter<'_>,
) -> Option<Vec<u64>> {
    assert!(matches!(
        seed_rooted_target(root, target, meter).unwrap(),
        RootSeedOutcome::Continue
    ));
    let conflict = oracle::legacy_sweep(root, originals, &[], &[], 0, meter).unwrap()?;
    finish_combined_rooted_chain(
        root,
        originals,
        &[],
        conflict,
        &mut Vec::new(),
        usize::MAX,
        meter,
    )
    .unwrap()
}

fn repair(
    root: &mut RootPropagation,
    originals: &[(u64, Vec<Literal>)],
    target: &[Literal],
    meter: &mut ConversionMeter<'_>,
) -> Result<Option<Vec<u64>>, ResolutionValidationError> {
    compact_rup_hint_candidates_rooted(root, originals, &[], target, &[], usize::MAX, 0, 0, meter)
}

fn assert_independent_replay(
    originals: Vec<(u64, Vec<Literal>)>,
    target: Vec<Literal>,
    hints: Vec<u64>,
) {
    let limits = ResolutionValidationLimits::unbounded();
    let mut stop = || false;
    let premises: Vec<_> = target.iter().map(|&literal| literal.negated()).collect();
    let dag = ResolutionDag {
        num_vars: 66,
        original_clauses: originals,
        derived: vec![
            RupStep {
                id: 3,
                clause: target,
                rup_hints: hints,
            },
            RupStep {
                id: 4,
                clause: vec![],
                rup_hints: vec![3],
            },
        ],
        empty_clause_id: 4,
    };
    assert!(dag
        .validate_with_limits_interruptible(&limits, &premises, 0, 0, &mut stop)
        .is_ok());
    let mut corrupted = dag.clone();
    corrupted.derived[0].rup_hints.clear();
    assert!(corrupted
        .validate_with_limits_interruptible(&limits, &premises, 0, 0, &mut stop)
        .is_err());
    assert!(dag.validate_with_limits(&limits).is_err());
}

#[test]
fn original_retirement_keeps_exact_chains_and_saves_repeated_satisfied_scans() {
    let (originals, target) = noisy_originals(64);
    let limits = ResolutionValidationLimits::unbounded();
    let mut stop = || false;
    let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    let mut legacy = root_for(&originals, 66);
    let expected = oracle_chain(&mut legacy, &originals, &target, &mut meter).unwrap();
    assert_eq!(expected, vec![2]);
    let old_work = meter.consumed_work();
    let mut root = root_for(&originals, 66);
    let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    assert!(matches!(
        seed_rooted_target(&mut root, &target, &mut meter).unwrap(),
        RootSeedOutcome::Continue
    ));
    let conflict = sweep_rooted_candidates(&mut root, &originals, &[], &[], 0, 0, &mut meter)
        .unwrap()
        .unwrap();
    assert!(
        !root.index_retired.is_clear(),
        "the original bitmap was used"
    );
    assert_eq!(root.assign, legacy.assign);
    assert_eq!(root.cand_reason, legacy.cand_reason);
    assert_eq!(root.cand_order, legacy.cand_order);
    assert_eq!(root.row_trail, legacy.row_trail);
    let actual = finish_combined_rooted_chain(
        &mut root,
        &originals,
        &[],
        conflict,
        &mut Vec::new(),
        2,
        &mut meter,
    )
    .unwrap()
    .unwrap();
    assert_eq!(actual, expected);
    assert!(
        meter.consumed_work() < old_work,
        "includes all retirement/reset debits"
    );
    rooted_repair_cleanup(&mut root);
    assert_clean(&root);
    assert_independent_replay(originals, target, actual);
}

#[test]
fn original_retirement_preserves_first_reasons_conflicts_and_opposing_row_reuse() {
    let originals = originals();
    let mut root = root_for(&originals, 5);
    let limits = ResolutionValidationLimits::unbounded();
    let mut stop = || false;
    let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    for (target, expected) in [
        (pos(0), vec![1, 2, 3]),
        (neg(0), vec![4, 5, 6]),
        (pos(0), vec![1, 2, 3]),
    ] {
        let mut legacy = root_for(&originals, 5);
        assert_eq!(
            oracle_chain(&mut legacy, &originals, &[target], &mut meter),
            Some(expected.clone())
        );
        assert!(matches!(
            seed_rooted_target(&mut root, &[target], &mut meter).unwrap(),
            RootSeedOutcome::Continue
        ));
        let conflict = sweep_rooted_candidates(&mut root, &originals, &[], &[], 0, 0, &mut meter)
            .unwrap()
            .unwrap();
        assert!(!root.index_retired.is_clear(), "unit originals retire too");
        assert_eq!(root.assign, legacy.assign);
        assert_eq!(root.cand_reason, legacy.cand_reason);
        assert_eq!(root.cand_order, legacy.cand_order);
        let actual = finish_combined_rooted_chain(
            &mut root,
            &originals,
            &[],
            conflict,
            &mut Vec::new(),
            6,
            &mut meter,
        )
        .unwrap();
        assert_eq!(actual, Some(expected));
        rooted_repair_cleanup(&mut root);
        assert_clean(&root);
    }
}

#[test]
fn original_retirement_layout_decline_and_missing_canonical_ids_keep_legacy_behavior() {
    let mut clauses: Vec<_> = (1..=65).map(|id| (id, vec![pos(0), pos(1)])).collect();
    clauses.push((66, vec![pos(0), neg(1)]));
    let limits = ResolutionValidationLimits::unbounded();
    let mut stop = || false;
    let mut meter = ConversionMeter::new(&limits, &mut stop).unwrap();
    let mut root = root_for(&clauses, 2); // Three bitmap words need seven cursor slots, but only five exist.
    let mut legacy = root_for(&clauses, 2);
    let expected = oracle_chain(&mut legacy, &clauses, &[pos(0)], &mut meter);
    assert_eq!(expected, Some(vec![1, 66]));
    assert_eq!(
        repair(&mut root, &clauses, &[pos(0)], &mut meter).unwrap(),
        expected
    );
    assert_clean(&root);
    // Private malformed-ID handling still skips the canonical-position miss;
    // the public namespace validator remains the source admission authority.
    clauses.truncate(2);
    clauses[1] = (999, vec![pos(0), neg(1)]);
    let mut root = root_for(&clauses, 2);
    let mut legacy = root_for(&clauses, 2);
    assert_eq!(
        oracle_chain(&mut legacy, &clauses, &[pos(0)], &mut meter),
        None
    );
    assert_eq!(
        repair(&mut root, &clauses, &[pos(0)], &mut meter).unwrap(),
        None
    );
    assert_clean(&root);
}

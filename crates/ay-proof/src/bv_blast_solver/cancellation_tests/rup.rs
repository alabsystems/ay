// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn chain(length: u32) -> (ResolutionDag, Vec<Clause>, Refutation) {
    let mut originals = vec![vec![Lit::pos(0)]];
    for variable in 1..length {
        originals.push(vec![Lit::neg(variable - 1), Lit::pos(variable)]);
    }
    originals.push(vec![Lit::neg(length - 1)]);
    let clauses: Vec<_> = originals
        .into_iter()
        .enumerate()
        .map(|(index, lits)| Clause {
            id: index as u32,
            lits,
            provenance: ClauseProvenance::Disequality,
        })
        .collect();
    let dag = ResolutionDag {
        num_vars: length as usize,
        original_clauses: clauses
            .iter()
            .map(|clause| {
                (
                    u64::from(clause.id) + 1,
                    clause.lits.iter().map(lit_to_sat).collect(),
                )
            })
            .collect(),
        derived: vec![RupStep {
            id: u64::from(length) + 2,
            clause: vec![],
            rup_hints: (1..=u64::from(length) + 1).collect(),
        }],
        empty_clause_id: u64::from(length) + 2,
    };
    let expected = Refutation {
        steps: (0..length)
            .map(|index| {
                let pivot = length - 1 - index;
                ResolutionStep {
                    id: length + 1 + index,
                    clause: if pivot == 0 {
                        vec![]
                    } else {
                        vec![Lit::neg(pivot - 1)]
                    },
                    rule: ResRule::Resolution,
                    premises: [length + index, pivot],
                    pivot,
                }
            })
            .collect(),
    };
    (dag, clauses, expected)
}

fn limits(length: usize) -> RupExpansionLimits {
    RupExpansionLimits {
        max_steps: length,
        // Frozen charge formulas for this unit-propagation chain:
        // 2N original slots + (N+1) hints + one conflict literal +
        // 4(N-1) intermediate slots + two last-pivot slots = 7N.
        // Literal/hint/pivot scans charge exactly 18N work units.
        max_literals: 7 * length,
        max_work: 18 * length,
        max_bytes: 1_024 * 1_024,
        deadline: Instant::now() + Duration::from_secs(60),
    }
}

#[test]
fn rup_keeps_frozen_resolution_order_and_exact_charge_thresholds() {
    for length in [1, 2, 4] {
        let (dag, clauses, expected) = chain(length);
        let caps = limits(length as usize);
        assert_eq!(
            expand_dag_to_resolution_with_cancellation(&dag, &clauses, Some(caps), &mut || true),
            Ok(expected)
        );
        let work = caps.max_work;
        assert_eq!(
            expand_dag_to_resolution_with_cancellation(
                &dag,
                &clauses,
                Some(RupExpansionLimits {
                    max_work: work - 1,
                    ..caps
                }),
                &mut || true
            ),
            Err(BvSolvedExportError::ResourceLimit {
                resource: "RUP expansion work",
                limit: work - 1,
                actual: work,
            })
        );
        let literals = caps.max_literals;
        assert_eq!(
            expand_dag_to_resolution_with_cancellation(
                &dag,
                &clauses,
                Some(RupExpansionLimits {
                    max_literals: literals - 1,
                    ..caps
                }),
                &mut || true
            ),
            Err(BvSolvedExportError::ResourceLimit {
                resource: "expanded literals",
                limit: literals - 1,
                actual: literals,
            })
        );
    }
}

#[test]
fn every_rup_expansion_poll_is_terminal_and_retry_keeps_the_source() {
    let (dag, clauses, expected) = chain(3);
    let source = format!("{dag:?}{clauses:?}");
    let caps = limits(3);
    let mut polls = 0;
    assert_eq!(
        expand_dag_to_resolution_with_cancellation(&dag, &clauses, Some(caps), &mut || {
            polls += 1;
            true
        }),
        Ok(expected.clone())
    );
    assert!(polls > 54); // work polls plus entry, resource and publication boundaries
    for stop in 1..=polls {
        let mut calls = 0;
        assert_eq!(
            expand_dag_to_resolution_with_cancellation(&dag, &clauses, Some(caps), &mut || {
                calls += 1;
                calls != stop
            }),
            Err(BvSolvedExportError::Cancelled)
        );
        assert_eq!(calls, stop);
    }
    assert_eq!(format!("{dag:?}{clauses:?}"), source);
    assert_eq!(
        expand_dag_to_resolution_with_cancellation(&dag, &clauses, Some(caps), &mut || true),
        Ok(expected)
    );
}

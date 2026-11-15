// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A valid LRAT step may state a weaker clause than its hint chain derives.

use super::*;
use crate::bv_blast_export::ClauseProvenance;
use ay_core::time::Instant;
use std::time::Duration;

/// Variables `a = 1`, `b = 2`, `c = 3` in DIMACS. Clause 5 states `stated`,
/// which contains `b`, but its chain (`¬a` is unit, then `(a b)` conflicts)
/// derives only `(b)`: a weakening LRAT accepts, with the same shape as
/// ay-sat's clause 15436 on `bvmul(a, b) == bvmul(b, a)`. Clause 6 then
/// refutes through clause 5.
fn weakened_refutation(stated: &[i32]) -> (ResolutionDag, Vec<Clause>) {
    fn dimacs(lits: &[i32]) -> Vec<Literal> {
        lits.iter().map(|&l| Literal::from_dimacs(l)).collect()
    }
    let originals = [vec![1, 2], vec![-1], vec![-2], vec![-3]];
    let dag = ResolutionDag {
        num_vars: 20,
        original_clauses: (1..)
            .zip(&originals)
            .map(|(id, lits)| (id, dimacs(lits)))
            .collect(),
        derived: vec![
            RupStep {
                id: 5,
                clause: dimacs(stated),
                rup_hints: vec![2, 1],
            },
            RupStep {
                id: 6,
                clause: Vec::new(),
                rup_hints: vec![4, 5, 3],
            },
        ],
        empty_clause_id: 6,
    };
    let clauses = (0..)
        .zip(&originals)
        .map(|(id, lits)| Clause {
            id,
            lits: lits
                .iter()
                .map(|&l| lit_from_sat(&Literal::from_dimacs(l)))
                .collect(),
            provenance: ClauseProvenance::Disequality,
        })
        .collect();
    (dag, clauses)
}

fn limits() -> RupExpansionLimits {
    RupExpansionLimits {
        max_steps: 16,
        max_literals: 1024,
        max_work: 4096,
        max_bytes: 1024 * 1024,
        deadline: Instant::now() + Duration::from_secs(10),
    }
}

/// Before `stronger_resolvent`, clause 5 was refused with
/// `RupExpansionFailed { id: 5 }` because its resolvent `(b)` is not set-equal
/// to the stated clause. The unbounded and the bounded expansion must both emit
/// exactly the two genuine resolutions, the second citing `(b)`. The 19-literal
/// statement drives the bounded comparisons onto their indexed path.
#[test]
fn a_weakened_lrat_clause_expands_through_its_stronger_resolvent() {
    for stated in [vec![2, 3], (2..=20).collect::<Vec<i32>>()] {
        let (dag, clauses) = weakened_refutation(&stated);
        for bounded in [None, Some(limits())] {
            let refutation = expand_dag_to_resolution(&dag, &clauses, bounded)
                .expect("a valid LRAT weakening must expand");
            let steps: Vec<_> = refutation
                .steps
                .iter()
                .map(|step| (step.clause.clone(), step.premises, step.pivot))
                .collect();
            assert_eq!(
                steps,
                vec![(vec![Lit::pos(1)], [0, 1], 0), (Vec::new(), [2, 4], 1)],
                "stated {stated:?}, bounded: {}",
                bounded.is_some()
            );
        }
    }
}

/// The relaxation admits a stronger resolvent, never a chain that fails to
/// conflict: a stated `(c)` gets no conflict from the same hints.
#[test]
fn a_chain_that_does_not_refute_its_stated_clause_is_still_refused() {
    let (dag, clauses) = weakened_refutation(&[3]);
    for bounded in [None, Some(limits())] {
        assert!(matches!(
            expand_dag_to_resolution(&dag, &clauses, bounded),
            Err(BvSolvedExportError::RupExpansionFailed { id: 5 })
        ));
    }
}

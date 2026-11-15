// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_sat::{Literal, Variable};

fn positive(index: u32) -> Literal {
    Literal::positive(Variable::new(index))
}

fn holds(clause: &[Literal], assignment: u32) -> bool {
    clause.iter().any(|literal| {
        let value = assignment & (1 << literal.variable().index()) != 0;
        value == literal.is_positive()
    })
}

#[test]
fn six_literal_tautology_never_becomes_a_blocking_remainder() {
    let x = positive(0);
    let original = vec![
        x,
        x.negated(),
        positive(1),
        positive(2),
        positive(3),
        positive(4),
    ];
    assert!((0..32).all(|assignment| holds(&original, assignment)));
    assert!(
        !holds(&original[2..], 0),
        "deleting the pair strengthens the clause"
    );

    for policy in [
        ConflictClausePolicy::PreserveLiterals,
        ConflictClausePolicy::Deduplicate,
    ] {
        let mut clause = original.clone();
        let reduction = minimize_conflict_clause(&mut clause, policy);
        let tautology = matches!(&reduction, ConflictClauseReduction::Tautology);
        let mut sat = ay_sat::Solver::new(5);
        sat.set_preprocess_enabled(false);
        if let ConflictClauseReduction::Clause { .. } = reduction {
            sat.add_clause(clause);
        }
        for index in 1..5 {
            sat.add_clause(vec![positive(index).negated()]);
        }
        assert!(
            sat.solve().into_inner().is_sat(),
            "the valid input may not exclude a=b=c=d=false"
        );
        assert!(
            tautology,
            "the caller must receive an explicit no-clause outcome"
        );
    }
}

#[test]
fn duplicated_polarities_still_classify_as_tautology() {
    let x = positive(0);
    let a = positive(1);
    for policy in [
        ConflictClausePolicy::PreserveLiterals,
        ConflictClausePolicy::Deduplicate,
    ] {
        let mut clause = vec![a, x, x, a, x.negated(), x.negated(), positive(2)];
        assert!(matches!(
            minimize_conflict_clause(&mut clause, policy),
            ConflictClauseReduction::Tautology
        ));
    }
}

#[test]
fn deduplication_preserves_the_clause_on_every_assignment() {
    let original = vec![
        positive(2),
        positive(0),
        positive(2),
        positive(1).negated(),
        positive(0),
    ];
    let mut clause = original.clone();
    assert!(matches!(
        minimize_conflict_clause(&mut clause, ConflictClausePolicy::Deduplicate),
        ConflictClauseReduction::Clause { removed: 2 }
    ));
    assert_eq!(
        clause,
        vec![positive(0), positive(1).negated(), positive(2)]
    );
    for assignment in 0..8 {
        assert_eq!(holds(&original, assignment), holds(&clause, assignment));
    }
}

#[test]
fn proof_policy_preserves_the_entire_signed_multiset() {
    let original = vec![
        positive(2).negated(),
        positive(0),
        positive(0),
        positive(1),
        positive(2).negated(),
    ];
    let expected = original.clone();
    let mut clause = original;
    assert!(matches!(
        minimize_conflict_clause(&mut clause, ConflictClausePolicy::PreserveLiterals),
        ConflictClauseReduction::Clause { removed: 0 }
    ));
    assert_eq!(
        clause, expected,
        "proof premise positions retain their original order and every signed occurrence"
    );
}

#[test]
fn real_assigned_and_new_unassigned_literals_all_survive_reduction() {
    let x = positive(0);
    let y = positive(1);
    let mut sat = ay_sat::Solver::new(2);
    sat.set_preprocess_enabled(false);
    sat.add_clause(vec![x]);
    sat.push();
    sat.add_clause(vec![y.negated()]);
    assert!(sat.solve().into_inner().is_sat());
    assert_eq!(sat.value(x.variable()), Some(true));
    assert_eq!(sat.value(y.variable()), Some(false));
    let fresh = Literal::positive(sat.new_var());
    assert_eq!(sat.value(fresh.variable()), None);

    let original = vec![y, fresh, x];
    for policy in [
        ConflictClausePolicy::PreserveLiterals,
        ConflictClausePolicy::Deduplicate,
    ] {
        let mut clause = original.clone();
        let mut expected = original.clone();
        if matches!(&policy, ConflictClausePolicy::Deduplicate) {
            expected.sort_unstable();
        }
        assert!(matches!(
            minimize_conflict_clause(&mut clause, policy),
            ConflictClauseReduction::Clause { removed: 0 }
        ));
        assert_eq!(
            clause, expected,
            "true, false and freshly mapped unassigned literals are data, not deletion permission"
        );
    }
    assert!(sat.pop());
    sat.add_clause(vec![y]);
    assert!(
        sat.solve().into_inner().is_sat(),
        "the prior scoped false assignment is not permanent"
    );
}

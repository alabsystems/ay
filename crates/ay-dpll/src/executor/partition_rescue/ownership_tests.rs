// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::Sort;

fn connector(name: &str, component: usize) -> Connector {
    Connector {
        name: name.to_string(),
        component,
    }
}

/// A proof whose empty clause rests on `own`, `lent`, `lent_low`, `stray`
/// and `true` (with `lent` assumed twice), beside an `assume` of `unused`
/// that no step depends on. With no proof installed there are no counts;
/// with this one, components 0, 1 and 2 as the returning component each see
/// two borrowed premises (lowest lenders 1, 0 and 0) and two unowned ones
/// (`stray` has no connector, `true` has no symbol).
#[test]
fn premises_are_counted_once_each_over_the_empty_clause_cone() {
    let mut executor = Executor::new();
    let terms = &mut executor.ctx.terms;
    let own = terms.mk_var("own", Sort::Bool);
    let lent = terms.mk_var("lent", Sort::Bool);
    let lent_low = terms.mk_var("lent_low", Sort::Bool);
    let stray = terms.mk_var("stray", Sort::Bool);
    let unused = terms.mk_var("unused", Sort::Bool);
    let constant = terms.true_term();
    let connectors = [
        connector("own", 0),
        connector("lent_low", 1),
        connector("lent", 2),
        connector("unused", 1),
    ];
    assert_eq!(executor.published_proof_lenders(0, &connectors), None);

    let mut proof = Proof::new();
    let _outside_the_cone = proof.add_assume(unused, None);
    let mut derived = proof.add_assume(own, None);
    for premise in [lent, lent_low, stray, constant] {
        let next = proof.add_assume(premise, None);
        derived = proof.add_resolution(vec![own], own, derived, next);
    }
    let lent_again = proof.add_assume(lent, None);
    let _empty_clause = proof.add_resolution(Vec::new(), own, derived, lent_again);
    executor.last_proof = Some(proof);

    assert_eq!(
        executor.published_proof_lenders(0, &connectors),
        Some(PremiseOwners {
            borrowed_rows: 2,
            lender: Some(1),
            unowned_premises: 2,
        })
    );
    for winner in [1, 2] {
        assert_eq!(
            executor.published_proof_lenders(winner, &connectors),
            Some(PremiseOwners {
                borrowed_rows: 2,
                lender: Some(0),
                unowned_premises: 2,
            }),
            "winner {winner}"
        );
    }
}

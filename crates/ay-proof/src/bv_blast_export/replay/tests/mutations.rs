// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

#[test]
fn malformed_graph_clause_and_resolution_errors_match_the_frozen_reader() {
    let proof = fixture(BvOp::Xor, 2);
    let mutations: &[fn(&mut BvBlastProof)] = &[
        |p| p.format_version += 1,
        |p| p.obligation.width = 0,
        |p| p.bit_lemmas[0].id = u32::MAX,
        |p| p.bit_lemmas[0].ins.clear(),
        |p| p.bit_lemmas[0].out = u32::MAX,
        |p| p.bit_lemmas[0].out = 0,
        |p| p.bit_lemmas[0].ins[0] = u32::MAX,
        |p| p.bit_lemmas[0].ins[0] = p.bit_lemmas[0].out,
        |p| p.bit_lemmas[1].out = p.bit_lemmas[0].out,
        |p| p.vars.roles.push(VarRole::Out { bit: 0 }),
        |p| p.clauses[0].id = u32::MAX,
        |p| p.clauses[0].lits.push(Lit::pos(u32::MAX)),
        |p| p.clauses[0].provenance = ClauseProvenance::BitLemmaCnf { lemma: u32::MAX },
        |p| p.clauses[0].lits.clear(),
        |p| p.refutation.steps.clear(),
        |p| p.refutation.steps[0].id = u32::MAX,
        |p| p.refutation.steps[0].premises[0] = u32::MAX,
        |p| p.refutation.steps[0].pivot = u32::MAX,
        |p| p.refutation.steps[0].clause.push(Lit::pos(u32::MAX)),
        |p| p.refutation.steps[0].clause.clear(),
        |p| {
            p.refutation.steps.pop();
        },
    ];
    for mutate in mutations {
        let mut malformed = proof.clone();
        mutate(&mut malformed);
        assert!(compare(&malformed, &limits(&malformed)).is_err());
    }
}

#[test]
fn complete_disequality_census_preserves_the_exact_count_error() {
    let mut proof = fixture(BvOp::Xor, 1);
    let disequality = proof
        .clauses
        .iter()
        .find(|c| matches!(c.provenance, ClauseProvenance::Disequality))
        .unwrap()
        .clone();
    proof
        .clauses
        .extend([disequality.clone(), disequality.clone(), disequality]);
    let limits = limits(&proof);
    let expected = Err(BvBlastValidateError::MalformedDisequality {
        reason: "expected exactly one disequality clause, found 4".to_owned(),
    });
    assert_eq!(compare(&proof, &limits), expected);
    let mut calls = 0;
    assert_eq!(
        proof.validate_with_limits_and_cancellation(&limits, &mut || {
            calls += 1;
            true
        }),
        expected
    );
    for refusal in 1..=calls {
        let mut ordinal = 0;
        assert_eq!(
            proof.validate_with_limits_and_cancellation(&limits, &mut || {
                ordinal += 1;
                ordinal != refusal
            }),
            Err(BvBlastValidateError::Cancelled)
        );
        assert_eq!(ordinal, refusal);
    }
}

#[test]
fn duplicate_gate_literals_keep_set_semantics_but_disequality_requires_unique_slots() {
    let mut proof = fixture(BvOp::Xor, 1);
    let literal = proof.clauses[0].lits[0];
    proof.clauses[0].lits.push(literal);
    assert_eq!(compare(&proof, &limits(&proof)), Ok(()));
    let disequality = proof
        .clauses
        .iter_mut()
        .find(|c| matches!(c.provenance, ClauseProvenance::Disequality))
        .unwrap();
    disequality.lits.push(disequality.lits[0]);
    assert!(matches!(
        compare(&proof, &limits(&proof)),
        Err(BvBlastValidateError::MalformedDisequality { .. })
    ));
}

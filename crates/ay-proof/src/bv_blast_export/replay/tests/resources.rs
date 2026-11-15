// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

fn charged_work(proof: &BvBlastProof) -> u64 {
    let mut work: usize = proof
        .bit_lemmas
        .iter()
        .map(|lemma| lemma.ins.len() + 1)
        .sum();
    work += proof.vars.len() + 2 * proof.obligation.width as usize;
    for clause in &proof.clauses {
        work += clause.lits.len() + 1;
        if let ClauseProvenance::BitLemmaCnf { lemma } = clause.provenance {
            let lemma = &proof.bit_lemmas[lemma as usize];
            work += tseitin_clauses(lemma.kind, lemma.out, &lemma.ins)
                .iter()
                .map(|candidate| candidate.len() + clause.lits.len())
                .sum::<usize>();
        }
    }
    let lookup = |id: u32| {
        if (id as usize) < proof.clauses.len() {
            proof.clauses[id as usize].lits.len()
        } else {
            proof.refutation.steps[id as usize - proof.clauses.len()]
                .clause
                .len()
        }
    };
    for step in &proof.refutation.steps {
        work += 4 * (lookup(step.premises[0]) + lookup(step.premises[1]) + step.clause.len()) + 1;
    }
    work as u64
}

#[test]
fn every_deterministic_work_boundary_matches_old_charges_exactly() {
    let proof = fixture(BvOp::Xor, 1);
    let total = charged_work(&proof);
    assert!(total > 0 && total < 2_000);
    let mut limits = limits(&proof);
    for allowance in 0..=total {
        limits.max_work = allowance;
        let result = compare(&proof, &limits);
        if allowance == total {
            assert_eq!(result, Ok(()));
        } else {
            assert!(
                matches!(result, Err(BvBlastValidateError::ResourceLimit { resource: "validation work", limit, .. }) if limit == allowance)
            );
        }
    }
}

#[test]
fn exact_certificate_count_limits_and_error_precedence_remain_unchanged() {
    let proof = fixture(BvOp::Xor, 1);
    let setters: &[fn(&mut BvBlastValidateLimits)] = &[
        |l| l.max_vars = 0,
        |l| l.max_bit_lemmas = 0,
        |l| l.max_clauses = 0,
        |l| l.max_resolution_steps = 0,
        |l| l.max_clause_literals = 0,
        |l| l.max_original_literals = 0,
        |l| l.max_derived_literals = 0,
    ];
    for set in setters {
        let mut limited = limits(&proof);
        set(&mut limited);
        assert!(matches!(
            compare(&proof, &limited),
            Err(BvBlastValidateError::ResourceLimit { .. })
        ));
    }
    let mut malformed = proof.clone();
    malformed.format_version += 1;
    let mut limited = limits(&malformed);
    limited.max_work = 0;
    assert!(matches!(
        compare(&malformed, &limited),
        Err(BvBlastValidateError::UnsupportedFormatVersion { .. })
    ));
    malformed = proof;
    malformed.bit_lemmas[0].id = u32::MAX;
    assert!(matches!(
        compare(&malformed, &limited),
        Err(BvBlastValidateError::ResourceLimit {
            resource: "validation work",
            ..
        })
    ));
}

#[test]
fn an_already_expired_deadline_retains_its_preflight_precedence() {
    let proof = fixture(BvOp::Xor, 1);
    let mut limits = limits(&proof);
    limits.deadline = Some(Instant::now());
    assert_eq!(
        compare(&proof, &limits),
        Err(BvBlastValidateError::DeadlineExceeded)
    );
    let mut calls = 0;
    assert_eq!(
        proof.validate_with_limits_and_cancellation(&limits, &mut || {
            calls += 1;
            true
        }),
        Err(BvBlastValidateError::DeadlineExceeded)
    );
    assert_eq!(calls, 0);
}

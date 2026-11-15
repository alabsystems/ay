// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn gate_work(proof: &BvBlastProof) -> u64 {
    let gates: usize = proof
        .bit_lemmas
        .iter()
        .map(|lemma| lemma.ins.len() + 1)
        .sum();
    let mut work = gates + proof.vars.len() + 2 * proof.obligation.width as usize;
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
    u64::try_from(work).expect("small independently counted gate fixture")
}

#[test]
fn cnf_usage_matches_existing_gate_charges_and_unit_api() {
    for op in [
        BvOp::Add,
        BvOp::Sub,
        BvOp::Xor,
        BvOp::And,
        BvOp::Or,
        BvOp::Shl,
        BvOp::Lshr,
        BvOp::Ashr,
    ] {
        for width in [1, 2, 4] {
            let proof = fixture(op, width);
            let expected = gate_work(&proof);
            let limits = limits(&proof);
            assert_eq!(oracle::validate(&proof, &limits), Ok(()));
            assert_eq!(
                proof.validate_cnf_with_limits_and_cancellation_work(&limits, &mut || true),
                Ok(expected)
            );
            assert_eq!(
                proof.validate_cnf_with_limits_and_cancellation(&limits, &mut || true),
                Ok(())
            );
        }
    }
}

#[test]
fn exact_cnf_work_boundary_and_zero_preserve_refusal() {
    let proof = fixture(BvOp::Sub, 4);
    let total = gate_work(&proof);
    assert!(total > 1);
    let mut limits = limits(&proof);
    for allowance in [0, total - 1, total] {
        limits.max_work = allowance;
        let result = proof.validate_cnf_with_limits_and_cancellation_work(&limits, &mut || true);
        assert_eq!(
            result.clone().map(|_| ()),
            proof.validate_cnf_with_limits_and_cancellation(&limits, &mut || true)
        );
        if allowance == total {
            assert_eq!(result, Ok(total));
        } else {
            assert!(matches!(result, Err(BvBlastValidateError::ResourceLimit {
                resource: "validation work", limit, actual,
            }) if limit == allowance && actual > allowance));
        }
    }
}

#[test]
fn cnf_usage_preserves_legacy_semantic_error_precedence() {
    let proof = fixture(BvOp::Xor, 2);
    let mutations: &[fn(&mut BvBlastProof)] = &[
        |p| p.format_version += 1,
        |p| p.obligation.width = 0,
        |p| p.bit_lemmas[0].id = u32::MAX,
        |p| p.bit_lemmas[0].ins.clear(),
        |p| p.bit_lemmas[0].out = u32::MAX,
        |p| p.clauses[0].id = u32::MAX,
        |p| p.clauses[0].lits.clear(),
    ];
    for mutate in mutations {
        let mut malformed = proof.clone();
        mutate(&mut malformed);
        let limits = limits(&malformed);
        let expected = oracle::validate(&malformed, &limits);
        assert!(expected.is_err());
        assert_eq!(
            malformed.validate_cnf_with_limits_and_cancellation(&limits, &mut || true),
            expected
        );
        assert_eq!(
            malformed
                .validate_cnf_with_limits_and_cancellation_work(&limits, &mut || true)
                .map(|_| ()),
            expected
        );
    }
}

#[test]
fn every_cnf_poll_including_final_refuses_without_work_report() {
    let proof = fixture(BvOp::Xor, 1);
    let before = proof.clone();
    let mut limits = limits(&proof);
    limits.max_work = gate_work(&proof);
    let mut calls = 0;
    assert_eq!(
        proof.validate_cnf_with_limits_and_cancellation_work(&limits, &mut || {
            calls += 1;
            true
        }),
        Ok(limits.max_work)
    );
    let mut legacy_calls = 0;
    assert_eq!(
        proof.validate_cnf_with_limits_and_cancellation(&limits, &mut || {
            legacy_calls += 1;
            true
        }),
        Ok(())
    );
    assert_eq!(calls, legacy_calls);
    assert!(calls > 1);
    for refusal in 1..=calls {
        let mut ordinal = 0;
        assert_eq!(
            proof.validate_cnf_with_limits_and_cancellation_work(&limits, &mut || {
                ordinal += 1;
                ordinal != refusal
            }),
            Err(BvBlastValidateError::Cancelled),
            "poll {refusal}/{calls}"
        );
        assert_eq!(ordinal, refusal, "transient refusal must not resume");
    }
    assert_eq!(proof, before);
}

#[test]
fn expired_cnf_deadline_returns_no_work_and_never_calls_the_callback() {
    let proof = fixture(BvOp::Xor, 1);
    let mut limits = limits(&proof);
    limits.deadline = Some(Instant::now());
    let mut calls = 0;
    assert_eq!(
        proof.validate_cnf_with_limits_and_cancellation_work(&limits, &mut || {
            calls += 1;
            true
        }),
        Err(BvBlastValidateError::DeadlineExceeded)
    );
    assert_eq!(calls, 0);
}

#[test]
#[cfg(target_pointer_width = "64")]
fn cnf_work_counter_overflow_refuses_instead_of_reporting_saturation() {
    let proof = fixture(BvOp::Xor, 1);
    let limits = limits(&proof);
    let mut calls = 0;
    let mut callback = || {
        calls += 1;
        true
    };
    let mut budget = ReplayBudget::new(&limits, &mut callback);
    assert_eq!(budget.add_work(usize::MAX), Ok(()));
    assert_eq!(budget.work(), u64::MAX);
    assert_eq!(budget.add_work(1), Err(BvBlastValidateError::WorkOverflow));
    assert_eq!(budget.work(), u64::MAX, "no wrapped or saturated new debit");
    assert_eq!(budget.poll(), Err(BvBlastValidateError::Cancelled));
    drop(budget);
    assert_eq!(calls, 1, "overflow cannot publish or restart the budget");
}

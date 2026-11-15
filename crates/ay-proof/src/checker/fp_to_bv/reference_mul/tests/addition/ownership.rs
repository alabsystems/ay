// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn exact_sum_success_and_negative_census_observe_final_original_owner() {
    for operation in [Arithmetic::Add, Arithmetic::Sub] {
        let f = SumFixture::new(3, 4, operation).certificate();
        for clause in [&[f.theorem][..], &[][..]] {
            let mut healthy = 0;
            recognizes_arithmetic(&f.fixture.terms, clause, operation, &mut |_, _| {
                healthy += 1;
                true
            })
            .expect("healthy original owner");
            let mut calls = 0;
            let stopped =
                recognizes_arithmetic(&f.fixture.terms, clause, operation, &mut |_, _| {
                    calls += 1;
                    calls < healthy
                });
            assert_eq!(stopped, Err(ReferenceError::Resource));
        }
    }
}

#[test]
fn sum_node_task_and_memo_storage_admit_before_all_owned_initialization() {
    for operation in [Arithmetic::Add, Arithmetic::Sub] {
        let f = SumFixture::new(3, 4, operation).certificate();
        for denied in 1..4 {
            let mut payloads = 0;
            let result = recognizes_arithmetic(
                &f.fixture.terms,
                &[f.theorem],
                operation,
                &mut |_, bytes| {
                    if bytes != 0 {
                        payloads += 1;
                    }
                    payloads < denied
                },
            );
            assert_eq!(result, Err(ReferenceError::Resource));
            assert_eq!(payloads, denied);
        }
    }
}

#[test]
fn sum_refusal_is_sticky_across_orientation_and_does_not_renew_work() {
    for operation in [Arithmetic::Add, Arithmetic::Sub] {
        let f = SumFixture::new(3, 4, operation).certificate();
        let mut calls = 0;
        let result =
            recognizes_arithmetic(&f.fixture.terms, &[f.theorem], operation, &mut |_, _| {
                calls += 1;
                calls != 7 // A later true callback must not erase this refusal.
            });
        assert_eq!(result, Err(ReferenceError::Resource));
        assert_eq!(calls, 7);
        let mut remaining = 20usize;
        let result =
            recognizes_arithmetic(&f.fixture.terms, &[f.theorem], operation, &mut |work, _| {
                let Some(next) = remaining.checked_sub(work) else {
                    return false;
                };
                remaining = next;
                true
            });
        assert_eq!(result, Err(ReferenceError::Resource));
    }
}

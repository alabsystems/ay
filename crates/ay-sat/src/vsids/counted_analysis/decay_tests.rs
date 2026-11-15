// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;
use crate::counted_storage::test_owner;

fn state(dormant: bool, rescale: bool) -> VSIDS {
    let mut s = VSIDS::new(33);
    if dormant {
        s.swap_chb_scores();
    }
    if rescale {
        s.increment = 2e100;
    }
    s
}

#[test]
fn counted_decay_matches_exact_evsids_dormant_scores_and_real_rescale_heap() {
    for dormant in [false, true] {
        for rescale in [false, true] {
            let mut actual = state(dormant, rescale);
            let mut expected = actual.clone();
            let stage = if dormant {
                ActivityStage::DormantEvsids
            } else {
                ActivityStage::Evsids
            };
            if dormant {
                expected.decay_evsids_dormant();
            } else {
                expected.decay();
            }
            actual
                .decay_counted(stage, &test_owner(1_000_000, 1_000_000))
                .unwrap();
            assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
            assert_eq!(actual.buffer_bytes(), expected.buffer_bytes());
            if rescale {
                assert!(actual.increment < 10.0);
            }
        }
    }
}

#[test]
fn every_short_decay_cut_refuses_before_mutation_or_after_the_completed_kernel() {
    for dormant in [false, true] {
        let stage = if dormant {
            ActivityStage::DormantEvsids
        } else {
            ActivityStage::Evsids
        };
        let mut base = state(dormant, true);
        let owner = test_owner(1_000_000, 1_000_000);
        base.decay_counted(stage, &owner).unwrap();
        let total = owner.usage().unwrap().work_admitted;
        for cut in 0..total {
            let mut actual = state(dormant, true);
            let before = format!("{actual:?}");
            let owner = test_owner(cut, 1_000_000);
            assert!(actual.decay_counted(stage, &owner).is_err());
            assert_eq!(format!("{actual:?}"), before);
            assert_eq!(owner.check(), Err(CountedAdmissionError::WorkExhausted));
        }
    }
}

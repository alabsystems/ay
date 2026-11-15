// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::counted_storage::{try_vec_with, Result};
use ay_core::original_query::CountedAdmission;

impl VSIDS {
    /// Preserve the normal heap, VMTF order and lazy CHB/bucket state.
    pub(crate) fn try_new_counted(num_vars: usize, owner: &CountedAdmission) -> Result<Self> {
        owner.admit(1, std::mem::size_of::<Self>())?;
        let bump_order = try_vec_with(owner, num_vars, |i| (num_vars - i) as u64)?;
        let heap = try_vec_with(owner, num_vars, |i| i as u32)?;
        let heap_pos = try_vec_with(owner, num_vars, |i| i as u32)?;
        let vmtf_prev = try_vec_with(owner, num_vars, |i| {
            if i + 1 < num_vars {
                (i + 1) as u32
            } else {
                INVALID_VAR
            }
        })?;
        let vmtf_next = try_vec_with(owner, num_vars, |i| {
            if i > 0 {
                (i - 1) as u32
            } else {
                INVALID_VAR
            }
        })?;
        let (vmtf_first, vmtf_last, vmtf_unassigned_bumped) = if num_vars == 0 {
            (INVALID_VAR, INVALID_VAR, 0)
        } else {
            (num_vars as u32 - 1, 0, bump_order[0])
        };
        Ok(Self {
            activities: try_vec_with(owner, num_vars, |_| 0.0)?,
            increment: 1.0,
            decay: default_vsids_decay(),
            random_seed: 0,
            bump_order,
            buried: try_vec_with(owner, num_vars, |_| false)?,
            bump_counter: num_vars as u64 + 1,
            heap,
            heap_pos,
            heap_repair_scratch: Vec::new(),
            heap_repair_order: Vec::new(),
            heap_repair_stamp: Vec::new(),
            heap_repair_epoch: 0,
            chb_scores: None,
            chb_last_conflict: None,
            chb_alpha: CHB_ALPHA_INIT,
            chb_conflicts: 0,
            chb_loaded: false,
            vmtf_prev,
            vmtf_next,
            vmtf_first,
            vmtf_last,
            vmtf_unassigned: vmtf_last,
            vmtf_unassigned_bumped,
            vmtf_deferred: false,
            queue_freeze: ay_core::sat_ab_switches().queue_freeze_kissat == Some(true),
            // This constructor initializes 32 empty Vecs and scalar metadata.
            bucket_queue: BucketQueue::new(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn all_initial_heap_queue_and_lazy_state_matches_normal_constructor() {
        for size in [0, 1, 7] {
            let owner = crate::counted_storage::test_owner(100_000, 100_000);
            let actual = VSIDS::try_new_counted(size, &owner).unwrap();
            let expected = VSIDS::new(size);
            assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
        }
    }
}

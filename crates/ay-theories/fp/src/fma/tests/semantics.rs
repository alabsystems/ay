// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use support::{case, with_owner};

#[test]
fn native_fma_single_round_keeps_exact_product_residual_lost_by_separate_multiply_add() {
    with_owner(|work| {
        for mode in RM_ORDER {
            // (1 + 2^-10)(1 - 2^-10) - 1 = -2^-20, exactly 16 minsubnormals.
            // Separately rounded multiplication instead gives 1 or its neighbor.
            case(
                mode,
                [(false, 15, 1), (false, 14, 1022), (true, 15, 0)],
                (true, 0, 16),
                work,
            );
        }
    });
}

#[test]
fn native_fma_exact_cancellation_and_opposite_signed_zeros_follow_each_mode() {
    with_owner(|work| {
        for mode in RM_ORDER {
            let negative = mode == RoundingMode::RTN;
            case(
                mode,
                [(false, 15, 0), (false, 16, 0), (true, 16, 0)],
                (negative, 0, 0),
                work,
            ); // +1 * +2 + -2
            case(
                mode,
                [(false, 0, 0), (false, 15, 0), (true, 0, 0)],
                (negative, 0, 0),
                work,
            ); // +0 * +1 + -0
        }
    });
}

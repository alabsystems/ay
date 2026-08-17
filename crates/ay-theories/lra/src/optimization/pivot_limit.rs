// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Ratio-test pivot limits for simplex optimization.

use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use crate::types::InfRational;
use crate::LraSolver;

impl LraSolver {
    /// The ratio test: how far `var` may move before some basic variable hits a
    /// bound, and which basic variable blocks first.
    ///
    /// `None` means no basic variable bounds the move at all — the caller reads
    /// that as "unbounded in this direction" once the entering variable has no
    /// bound of its own either.
    ///
    /// Ties go to the smallest basic-variable index. That tie-break is Bland's
    /// rule, and it is load-bearing: a degenerate vertex yields several blockers
    /// at ratio zero, and choosing among them arbitrarily lets the basis cycle
    /// forever.
    pub(super) fn find_pivot_limit(&self, var: u32, increase: bool) -> Option<(InfRational, u32)> {
        let mut best: Option<(InfRational, u32)> = None;
        let zero = InfRational::default();

        for row in &self.rows {
            let coeff = row.coeff_big(var);
            if coeff.is_zero() {
                continue;
            }

            let basic_info = &self.vars[row.basic_var as usize];
            let basic_val = &basic_info.value;

            // Moving `var` by Δ moves this basic by coeff·Δ; the limit is the
            // distance to the bound it moves toward (unbounded that way = no
            // limit from this row). Delta-rational: strict bounds are
            // `value ± ε` and the distance is scaled by 1/|coeff| through the
            // ε-part as well (#opt-epsilon).
            let inv_abs = BigRational::one() / coeff.abs();
            let delta = if increase == coeff.is_positive() {
                basic_info.upper.as_ref().map(|ub| {
                    (&ub.as_inf(crate::BoundType::Upper) - basic_val).mul_rational(&inv_abs)
                })
            } else {
                basic_info.lower.as_ref().map(|lb| {
                    (basic_val - &lb.as_inf(crate::BoundType::Lower)).mul_rational(&inv_abs)
                })
            };

            if let Some(d) = delta {
                if d >= zero {
                    let better = match &best {
                        None => true,
                        Some((m, blocker)) => d < *m || (d == *m && row.basic_var < *blocker),
                    };
                    if better {
                        best = Some((d, row.basic_var));
                    }
                }
            }
        }

        best
    }
}

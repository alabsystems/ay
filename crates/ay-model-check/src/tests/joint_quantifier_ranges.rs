// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

// Public evaluator regressions, textually included by finite_quantifiers.rs.
#[cfg(test)]
mod joint_quantifier_ranges {
    use super::*;

    include!("joint_quantifier_ranges/fixtures.rs");
    include!("joint_quantifier_ranges/matrices.rs");
    include!("joint_quantifier_ranges/scope.rs");
    include!("joint_quantifier_ranges/resources.rs");
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bool variable partitioning for TPA interpolation.
//!
//! When interpolation involves Bool variables appearing in both A and B
//! constraints, this module partitions them and enumerates assignments to
//! produce per-branch interpolants that are recombined.

use std::time::Duration;

use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

use crate::interpolant_validation::is_valid_interpolant_with_check_sat;
use crate::interpolation::{interpolating_sat_constraints, InterpolatingSatResult};
use crate::{ChcExpr, ChcSort, ChcVar};

use super::super::solver::{flatten_to_constraints, TpaSolver};

/// Maximum number of actual `interpolating_sat_constraints` calls within a
/// single full-Bool-partition invocation.
const MAX_INTERPOLATION_CALLS: usize = 256;

const INTERPOLANT_VALIDATION_TIMEOUT: Duration = Duration::from_secs(2);

#[derive(Debug)]
pub(super) struct BoolInterpolationPartition {
    pub(super) a_local: Vec<ChcVar>,
    pub(super) shared: Vec<ChcVar>,
    pub(super) b_local: Vec<ChcVar>,
}

#[derive(Debug)]
pub(super) struct NormalizedConstraints {
    pub(super) constraints: Vec<ChcExpr>,
    pub(super) unsat: bool,
}

fn collect_bool_vars(constraints: &[ChcExpr]) -> FxHashMap<String, ChcVar> {
    let mut vars = FxHashMap::default();
    for constraint in constraints {
        for var in constraint.vars() {
            if var.sort == ChcSort::Bool {
                vars.entry(var.name.clone()).or_insert(var);
            }
        }
    }
    vars
}

fn sort_vars_by_name(vars: impl IntoIterator<Item = ChcVar>) -> Vec<ChcVar> {
    let mut sorted: Vec<_> = vars.into_iter().collect();
    sorted.sort_by(|lhs, rhs| lhs.name.cmp(&rhs.name));
    sorted
}

pub(super) fn classify_bool_partition(
    a_constraints: &[ChcExpr],
    b_constraints: &[ChcExpr],
) -> BoolInterpolationPartition {
    let a_vars = collect_bool_vars(a_constraints);
    let b_vars = collect_bool_vars(b_constraints);

    let a_local = sort_vars_by_name(
        a_vars
            .iter()
            .filter(|(name, _)| !b_vars.contains_key(*name))
            .map(|(_, var)| var.clone()),
    );
    let shared = sort_vars_by_name(
        a_vars
            .iter()
            .filter(|(name, _)| b_vars.contains_key(*name))
            .map(|(_, var)| var.clone()),
    );
    let b_local = sort_vars_by_name(
        b_vars
            .iter()
            .filter(|(name, _)| !a_vars.contains_key(*name))
            .map(|(_, var)| var.clone()),
    );

    BoolInterpolationPartition {
        a_local,
        shared,
        b_local,
    }
}

fn bool_assignment_count(vars: &[ChcVar]) -> Option<usize> {
    1usize.checked_shl(vars.len() as u32)
}

pub(super) fn bool_partition_branch_count(partition: &BoolInterpolationPartition) -> Option<usize> {
    let shared = bool_assignment_count(&partition.shared)?;
    let a_local = bool_assignment_count(&partition.a_local)?;
    let b_local = bool_assignment_count(&partition.b_local)?;
    shared.checked_mul(a_local)?.checked_mul(b_local)
}

fn extend_bool_assignment(
    vars: &[ChcVar],
    assignment: usize,
    substitutions: &mut FxHashMap<String, ChcExpr>,
) {
    for (index, var) in vars.iter().enumerate() {
        let value = ((assignment >> index) & 1) == 1;
        substitutions.insert(var.name.clone(), ChcExpr::Bool(value));
    }
}

fn bool_assignment_guard(vars: &[ChcVar], assignment: usize) -> ChcExpr {
    ChcExpr::and_all(vars.iter().enumerate().map(|(index, var)| {
        let value = ((assignment >> index) & 1) == 1;
        if value {
            ChcExpr::var(var.clone())
        } else {
            ChcExpr::not(ChcExpr::var(var.clone()))
        }
    }))
}

pub(super) fn normalize_constraints_for_partition(
    constraints: &[ChcExpr],
    substitutions: &FxHashMap<String, ChcExpr>,
) -> NormalizedConstraints {
    let mut normalized = Vec::new();

    for constraint in constraints {
        let rewritten = constraint
            .substitute_name_map(substitutions)
            .simplify_constants()
            .eliminate_ite()
            .simplify_constants();

        for conjunct in flatten_to_constraints(&rewritten) {
            match conjunct {
                ChcExpr::Bool(true) => {}
                ChcExpr::Bool(false) => {
                    return NormalizedConstraints {
                        constraints: Vec::new(),
                        unsat: true,
                    };
                }
                other => normalized.push(other),
            }
        }
    }

    NormalizedConstraints {
        constraints: normalized,
        unsat: false,
    }
}

impl TpaSolver {
    pub(super) fn interpolate_with_full_bool_partitioning(
        &mut self,
        a_constraints: &[ChcExpr],
        b_constraints: &[ChcExpr],
        shared_vars: &FxHashSet<String>,
        partition: &BoolInterpolationPartition,
    ) -> Option<ChcExpr> {
        let shared_assignments = bool_assignment_count(&partition.shared)?;
        let a_local_assignments = bool_assignment_count(&partition.a_local)?;
        let b_local_assignments = bool_assignment_count(&partition.b_local)?;

        let shared_bool_names: FxHashSet<String> = partition
            .shared
            .iter()
            .map(|var| var.name.clone())
            .collect();
        let branch_shared_vars: FxHashSet<String> = shared_vars
            .iter()
            .filter(|name| !shared_bool_names.contains(*name))
            .cloned()
            .collect();

        let mut sigma_interpolants = Vec::with_capacity(shared_assignments);
        let mut interpolation_calls = 0usize;

        for shared_assignment in 0..shared_assignments {
            let mut shared_substitutions = FxHashMap::default();
            extend_bool_assignment(
                &partition.shared,
                shared_assignment,
                &mut shared_substitutions,
            );
            let sigma_guard = bool_assignment_guard(&partition.shared, shared_assignment);

            let normalized_a_cases: Vec<_> = (0..a_local_assignments)
                .map(|a_assignment| {
                    let mut substitutions = shared_substitutions.clone();
                    extend_bool_assignment(&partition.a_local, a_assignment, &mut substitutions);
                    normalize_constraints_for_partition(a_constraints, &substitutions)
                })
                .collect();
            let normalized_b_cases: Vec<_> = (0..b_local_assignments)
                .map(|b_assignment| {
                    let mut substitutions = shared_substitutions.clone();
                    extend_bool_assignment(&partition.b_local, b_assignment, &mut substitutions);
                    normalize_constraints_for_partition(b_constraints, &substitutions)
                })
                .collect();

            let mut alpha_interpolants = Vec::with_capacity(a_local_assignments);
            for normalized_a in &normalized_a_cases {
                if normalized_a.unsat {
                    alpha_interpolants.push(ChcExpr::Bool(false));
                    continue;
                }

                let mut beta_interpolants = Vec::with_capacity(b_local_assignments);
                for normalized_b in &normalized_b_cases {
                    if normalized_b.unsat {
                        beta_interpolants.push(ChcExpr::Bool(true));
                        continue;
                    }

                    interpolation_calls += 1;
                    if interpolation_calls > MAX_INTERPOLATION_CALLS {
                        return None;
                    }

                    match interpolating_sat_constraints(
                        &normalized_a.constraints,
                        &normalized_b.constraints,
                        &branch_shared_vars,
                    ) {
                        InterpolatingSatResult::Unsat(interpolant) => {
                            beta_interpolants.push(interpolant);
                        }
                        InterpolatingSatResult::Unknown => return None,
                    }
                }

                alpha_interpolants.push(ChcExpr::and_all(beta_interpolants).simplify_constants());
            }

            let sigma_interpolant = ChcExpr::or_all(alpha_interpolants).simplify_constants();
            sigma_interpolants
                .push(ChcExpr::implies(sigma_guard, sigma_interpolant).simplify_constants());
        }

        if self.config.verbose_level > 0 {
            safe_eprintln!(
                "TPA: full Bool partition used {interpolation_calls} interpolation calls"
            );
        }

        let combined = ChcExpr::and_all(sigma_interpolants).simplify_constants();
        if self.validate_recombined_interpolant(
            a_constraints,
            b_constraints,
            &combined,
            shared_vars,
        ) {
            Some(combined)
        } else {
            None
        }
    }

    pub(super) fn validate_recombined_interpolant(
        &mut self,
        a_constraints: &[ChcExpr],
        b_constraints: &[ChcExpr],
        interpolant: &ChcExpr,
        shared_vars: &FxHashSet<String>,
    ) -> bool {
        let a_conjunction = ChcExpr::and_all(a_constraints.to_vec());
        let b_conjunction = ChcExpr::and_all(b_constraints.to_vec());
        is_valid_interpolant_with_check_sat(
            &a_conjunction,
            &b_conjunction,
            interpolant,
            shared_vars,
            |query| {
                self.smt
                    .check_sat_with_timeout(query, INTERPOLANT_VALIDATION_TIMEOUT)
            },
        )
    }
}

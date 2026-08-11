// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! WBO (Weighted Boolean Optimization) to PBO translation.
//!
//! Converts a WBO instance with hard and soft constraints into an equivalent
//! PBO instance by introducing relaxation variables for soft constraints.
//!
//! For each soft constraint `[cost] C`:
//! - Add a relaxation variable `r_i`
//! - `>=` soft constraints become `sum(terms) + M * r_i >= rhs`
//! - `=` soft constraints become two relaxed `>=` directions that share `r_i`
//! - Objective term: `cost * r_i`
//!
//! The `soft: <top> ;` header is enforced as a hard budget row
//! `sum(cost_i * r_i) <= top - 1`: official WBO semantics admit only models
//! whose total falsified-soft cost is STRICTLY LESS than the top cost, so an
//! instance whose minimum cost reaches the top is UNSATISFIABLE. The row is
//! omitted when it cannot bind (total paid cost already below the top).

use crate::types::{PbConstraint, PbInstance, PbLit, PbObjective, PbRel, PbTerm, WboInstance};
use std::{collections::BTreeSet as HashSet, fmt, ops::Range};

/// Error returned when a WBO instance cannot be converted to PBO safely.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WboToPboError {
    ExplicitObjectiveUnsupported,
    NegativeSoftCost,
    VariableCountOverflow,
    RelaxedSoftCountOverflow,
    RelaxationCoefficientOverflow,
    SoftEqualityRhsOverflow,
    SoftEqualityCoefficientOverflow,
}

impl fmt::Display for WboToPboError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ExplicitObjectiveUnsupported => write!(
                f,
                "explicit objectives are unsupported; use soft constraints instead"
            ),
            Self::NegativeSoftCost => {
                write!(f, "negative WBO soft constraint costs are unsupported")
            }
            Self::VariableCountOverflow => write!(f, "relaxed WBO variable count exceeds u32::MAX"),
            Self::RelaxedSoftCountOverflow => {
                write!(f, "relaxed WBO soft constraint count exceeds u32::MAX")
            }
            Self::RelaxationCoefficientOverflow => {
                write!(
                    f,
                    "soft constraint relaxation coefficient exceeds i128::MAX"
                )
            }
            Self::SoftEqualityRhsOverflow => write!(
                f,
                "soft equality relaxation does not support rhs = i128::MIN"
            ),
            Self::SoftEqualityCoefficientOverflow => write!(
                f,
                "soft equality relaxation does not support i128::MIN coefficients"
            ),
        }
    }
}

impl std::error::Error for WboToPboError {}

/// Opt-in metadata scaffold for certified WBO-to-PBO projection.
///
/// Building this value does not enable WBO proof logging. It records the exact
/// variable, constraint, and objective correspondences created by the existing
/// WBO relaxation conversion so a future certified path can replay/prove those
/// projections explicitly.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CertifiedWboProjection {
    /// PBO instance produced by the existing WBO relaxation converter.
    pub pbo: PbInstance,
    /// Number of variables in the original WBO input.
    pub original_num_vars: u32,
    /// Number of variables after adding relaxation variables.
    pub projected_num_vars: u32,
    /// Mapping from original hard constraints to copied PBO constraints.
    pub hard_constraints: Vec<WboHardConstraintMapping>,
    /// Mapping for every original soft constraint, including skipped
    /// constraints.
    pub soft_constraints: Vec<WboSoftConstraintMapping>,
    /// Mapping from original paid soft constraints to relaxation variables.
    pub relaxation_vars: Vec<WboRelaxationVarMapping>,
    /// Mapping from PBO objective terms back to paid WBO soft constraints.
    pub objective_terms: Vec<WboObjectiveTermMapping>,
    /// Index of the top-cost budget row (`sum(cost_i * r_i) <= top - 1`, from
    /// the `soft: <top> ;` header) in the PBO constraint list, when one was
    /// appended.
    pub top_cost_budget_constraint: Option<usize>,
}

impl CertifiedWboProjection {
    /// Consume the projection and return the relaxed PBO instance.
    pub fn into_pbo(self) -> PbInstance {
        self.pbo
    }
}

/// Hard WBO constraints are copied unchanged into the front of the PBO
/// constraint list.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WboHardConstraintMapping {
    pub wbo_hard_index: usize,
    pub pbo_constraint_index: usize,
}

/// Mapping for a single original WBO soft constraint.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WboSoftConstraintMapping {
    pub wbo_soft_index: usize,
    pub cost: i128,
    /// Relaxation variable introduced for this soft constraint. `None` means
    /// the constraint is skipped by the existing converter.
    pub relaxation_var: Option<u32>,
    /// First PBO constraint generated for this soft constraint.
    pub pbo_constraint_start: Option<usize>,
    /// Number of generated PBO constraints: 0 for zero-cost, 1 for `>=`, 2 for
    /// `=`.
    pub pbo_constraint_len: usize,
    /// PBO objective term that charges this relaxation variable.
    pub objective_term_index: Option<usize>,
}

impl WboSoftConstraintMapping {
    pub fn is_relaxed(&self) -> bool {
        self.relaxation_var.is_some()
    }

    pub fn pbo_constraint_indices(&self) -> Option<Range<usize>> {
        self.pbo_constraint_start
            .map(|start| start..start + self.pbo_constraint_len)
    }
}

/// Mapping from a paid soft constraint to its relaxation variable.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WboRelaxationVarMapping {
    pub wbo_soft_index: usize,
    pub relaxation_var: u32,
    pub pbo_constraint_start: usize,
    pub pbo_constraint_len: usize,
    pub objective_term_index: usize,
}

impl WboRelaxationVarMapping {
    pub fn pbo_constraint_indices(&self) -> Range<usize> {
        self.pbo_constraint_start..self.pbo_constraint_start + self.pbo_constraint_len
    }
}

/// Mapping from a relaxed PBO objective term to the WBO soft constraint it
/// charges.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WboObjectiveTermMapping {
    pub objective_term_index: usize,
    pub wbo_soft_index: usize,
    pub relaxation_var: u32,
    pub cost: i128,
}

/// Which generated `>=` direction failed while trying to relax a soft
/// constraint.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WboRelaxedConstraintDirection {
    SoftGe,
    SoftEqLowerBound,
    SoftEqUpperBound,
}

impl fmt::Display for WboRelaxedConstraintDirection {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::SoftGe => write!(f, "soft >="),
            Self::SoftEqLowerBound => write!(f, "soft equality lower-bound direction"),
            Self::SoftEqUpperBound => write!(f, "soft equality upper-bound direction"),
        }
    }
}

/// Structured reason a certified WBO projection cannot be built.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WboProjectionUnsupported {
    pub reason: WboProjectionUnsupportedReason,
}

impl WboProjectionUnsupported {
    pub fn conversion_error(&self) -> WboToPboError {
        self.reason.conversion_error()
    }

    fn from_conversion_error(wbo: &WboInstance, source: WboToPboError) -> Self {
        Self {
            reason: refine_projection_unsupported_reason(wbo, source),
        }
    }
}

impl fmt::Display for WboProjectionUnsupported {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.reason.fmt(f)
    }
}

impl std::error::Error for WboProjectionUnsupported {}

/// Precise unsupported reason for the projection scaffold.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WboProjectionUnsupportedReason {
    ExplicitObjectiveUnsupported {
        objective_term_count: usize,
    },
    NegativeSoftCost {
        wbo_soft_index: usize,
        cost: i128,
    },
    VariableCountOverflow {
        original_num_vars: u32,
        relaxed_soft_constraints: usize,
    },
    RelaxedSoftCountOverflow {
        relaxed_soft_constraints: usize,
    },
    RelaxationCoefficientOverflow {
        wbo_soft_index: usize,
        direction: WboRelaxedConstraintDirection,
    },
    SoftEqualityRhsOverflow {
        wbo_soft_index: usize,
        rhs: i128,
    },
    SoftEqualityCoefficientOverflow {
        wbo_soft_index: usize,
        term_index: usize,
        coeff: i128,
    },
    ConversionRejected {
        source: WboToPboError,
    },
}

impl WboProjectionUnsupportedReason {
    pub fn conversion_error(&self) -> WboToPboError {
        match self {
            Self::ExplicitObjectiveUnsupported { .. } => {
                WboToPboError::ExplicitObjectiveUnsupported
            }
            Self::NegativeSoftCost { .. } => WboToPboError::NegativeSoftCost,
            Self::VariableCountOverflow { .. } => WboToPboError::VariableCountOverflow,
            Self::RelaxedSoftCountOverflow { .. } => WboToPboError::RelaxedSoftCountOverflow,
            Self::RelaxationCoefficientOverflow { .. } => {
                WboToPboError::RelaxationCoefficientOverflow
            }
            Self::SoftEqualityRhsOverflow { .. } => WboToPboError::SoftEqualityRhsOverflow,
            Self::SoftEqualityCoefficientOverflow { .. } => {
                WboToPboError::SoftEqualityCoefficientOverflow
            }
            Self::ConversionRejected { source } => *source,
        }
    }
}

impl fmt::Display for WboProjectionUnsupportedReason {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ExplicitObjectiveUnsupported {
                objective_term_count,
            } => write!(
                f,
                "explicit WBO objective is unsupported ({objective_term_count} objective terms)"
            ),
            Self::NegativeSoftCost {
                wbo_soft_index,
                cost,
            } => write!(
                f,
                "soft constraint {wbo_soft_index} has negative unsupported cost {cost}"
            ),
            Self::VariableCountOverflow {
                original_num_vars,
                relaxed_soft_constraints,
            } => write!(
                f,
                "relaxed WBO variable count overflows: original vars={original_num_vars}, relaxed soft constraints={relaxed_soft_constraints}"
            ),
            Self::RelaxedSoftCountOverflow {
                relaxed_soft_constraints,
            } => write!(
                f,
                "relaxed WBO soft constraint count exceeds u32::MAX: relaxed soft constraints={relaxed_soft_constraints}"
            ),
            Self::RelaxationCoefficientOverflow {
                wbo_soft_index,
                direction,
            } => write!(
                f,
                "soft constraint {wbo_soft_index} relaxation coefficient overflows in {direction}"
            ),
            Self::SoftEqualityRhsOverflow {
                wbo_soft_index,
                rhs,
            } => write!(
                f,
                "soft equality constraint {wbo_soft_index} cannot negate rhs {rhs}"
            ),
            Self::SoftEqualityCoefficientOverflow {
                wbo_soft_index,
                term_index,
                coeff,
            } => write!(
                f,
                "soft equality constraint {wbo_soft_index} cannot negate term {term_index} coefficient {coeff}"
            ),
            Self::ConversionRejected { source } => {
                write!(f, "WBO projection rejected by converter: {source}")
            }
        }
    }
}

/// Converts a WBO instance into an equivalent PBO instance.
///
/// Each soft constraint `[cost] C` becomes:
/// - One relaxed `>=` hard constraint when `C` is `>=`
/// - Two relaxed `>=` hard constraints with a shared relaxation variable when
///   `C` is `=`
/// - An objective term `cost * r_i`
///
/// Hard constraints are kept as-is.
pub fn wbo_to_pbo(wbo: &WboInstance) -> PbInstance {
    try_wbo_to_pbo(wbo).unwrap_or_else(|err| {
        panic!("invalid WBO instance cannot be converted to PBO: {err}");
    })
}

/// Fallible WBO-to-PBO conversion.
///
/// This preserves fail-closed behavior for malformed or too-large WBO
/// instances without panicking, so callers can return UNKNOWN instead of
/// aborting the process.
pub fn try_wbo_to_pbo(wbo: &WboInstance) -> Result<PbInstance, WboToPboError> {
    if wbo.objective.is_some() {
        return Err(WboToPboError::ExplicitObjectiveUnsupported);
    }
    if first_negative_soft_cost(wbo).is_some() {
        return Err(WboToPboError::NegativeSoftCost);
    }

    let hard_constraint_keys = build_hard_constraint_key_set(wbo);
    let relaxed_softs = relaxed_soft_constraint_plan(wbo, hard_constraint_keys.as_ref());
    let num_relaxed_soft_count = relaxed_softs.len();
    let num_relaxed_soft = u32::try_from(num_relaxed_soft_count)
        .map_err(|_| WboToPboError::RelaxedSoftCountOverflow)?;
    let num_vars = wbo
        .num_vars
        .checked_add(num_relaxed_soft)
        .ok_or(WboToPboError::VariableCountOverflow)?;
    let relaxed_constraint_count: usize = relaxed_softs
        .iter()
        .map(|entry| entry.pbo_constraint_len)
        .sum();

    let mut constraints = Vec::with_capacity(wbo.hard_constraints.len() + relaxed_constraint_count);
    let mut objective_terms = Vec::with_capacity(num_relaxed_soft as usize);

    // Keep hard constraints unchanged.
    constraints.extend_from_slice(&wbo.hard_constraints);

    // Relax each soft constraint.
    for (relaxed_idx, entry) in relaxed_softs.iter().enumerate() {
        let relax_var = wbo.num_vars + (relaxed_idx as u32) + 1; // 1-indexed

        constraints.extend(relax_soft_constraint(entry.constraint, relax_var)?);

        // Objective term: cost * r_i (minimize total cost of relaxation)
        objective_terms.push(PbTerm {
            coeff: entry.cost,
            lits: vec![PbLit {
                var: relax_var,
                negated: false,
            }],
        });
    }

    if let Some(budget) = top_cost_budget_constraint(wbo, &relaxed_softs) {
        constraints.push(budget);
    }

    Ok(PbInstance {
        num_vars,
        num_constraints: constraints.len() as u32,
        constraints,
        objective: Some(PbObjective {
            terms: objective_terms,
        }),
    })
}

#[derive(Debug, Clone, Copy)]
struct WboSoftRelaxationPlanEntry<'a> {
    cost: i128,
    constraint: &'a PbConstraint,
    pbo_constraint_len: usize,
}

/// The hard budget row enforcing the `soft: <top> ;` header, or `None` when no
/// row is needed.
///
/// A violated soft constraint forces its relaxation variable to 1 (with r_i =
/// 0 the relaxed row is the original constraint), so `sum(cost_i * r_i)` upper-
/// bounds the true falsified-soft cost of any solution; conversely, any WBO
/// model with cost < top extends to a solution of the budget row by setting
/// r_i = 1 exactly on its violated softs. Budgeting the relaxation sum to
/// `top - 1` therefore makes the converted PBO equisatisfiable with the
/// official strictly-less-than-top WBO semantics and preserves the optimum.
///
/// `top <= 0` admits no model at all (costs are validated non-negative, and a
/// model needs cost < top): encode plain falsity `0 >= 1`. Drivers additionally
/// short-circuit that case to UNSATISFIABLE before solving; this row is the
/// fail-closed backstop for any other caller.
///
/// Skipped softs need no budget term: zero-cost softs contribute nothing, and
/// softs identical to a hard constraint can never be falsified.
fn top_cost_budget_constraint(
    wbo: &WboInstance,
    relaxed_softs: &[WboSoftRelaxationPlanEntry<'_>],
) -> Option<PbConstraint> {
    let top = wbo.top_cost?;
    if top <= 0 {
        return Some(PbConstraint {
            terms: Vec::new(),
            rel: PbRel::Ge,
            rhs: 1,
        });
    }
    if !top_cost_budget_binds(relaxed_softs, top) {
        return None;
    }
    // Normalized `>=` form of sum(min(cost_i, top) * r_i) <= top - 1. Capping
    // each coefficient at `top` is equisatisfiable: a soft with cost >= top can
    // never be falsified by an admissible model (its cost alone reaches the
    // top), and min(cost, top) = top > top - 1 still forces its r_i to 0, while
    // coefficients below the top are unchanged. The cap keeps astronomically
    // large parsed costs out of constraint coefficients, where downstream
    // integer arithmetic (e.g. preprocessing's ceiling division) assumes
    // headroom. Costs are non-negative and top >= 1 here, so neither negation
    // can overflow.
    let terms = relaxed_softs
        .iter()
        .enumerate()
        .map(|(relaxed_idx, entry)| PbTerm {
            coeff: -entry.cost.min(top),
            lits: vec![PbLit {
                var: wbo.num_vars + (relaxed_idx as u32) + 1,
                negated: false,
            }],
        })
        .collect();
    Some(PbConstraint {
        terms,
        rel: PbRel::Ge,
        rhs: 1 - top,
    })
}

/// Whether the top-cost budget row can bind: `false` only when the sum of all
/// paid (top-capped) soft costs is already `<= top - 1`, in which case no
/// assignment can exceed the budget and the row is omitted (the conversion
/// stays byte-identical for instances with a vacuous top cost). Overflow of
/// the sum means the total exceeds any representable top, i.e. the row binds.
fn top_cost_budget_binds(relaxed_softs: &[WboSoftRelaxationPlanEntry<'_>], top: i128) -> bool {
    let mut total: i128 = 0;
    for entry in relaxed_softs {
        total = match total.checked_add(entry.cost.min(top)) {
            Some(t) => t,
            None => return true,
        };
    }
    total > top - 1
}

fn relaxed_soft_constraint_plan<'a>(
    wbo: &'a WboInstance,
    hard_constraint_keys: Option<&HashSet<ConstraintKey>>,
) -> Vec<WboSoftRelaxationPlanEntry<'a>> {
    wbo.soft_constraints
        .iter()
        .filter_map(|(cost, constraint)| {
            if should_relax_soft_constraint(*cost, constraint, hard_constraint_keys) {
                Some(WboSoftRelaxationPlanEntry {
                    cost: *cost,
                    constraint,
                    pbo_constraint_len: relaxed_soft_constraint_len(constraint),
                })
            } else {
                None
            }
        })
        .collect()
}

/// Build certified projection metadata for the existing WBO-to-PBO conversion.
///
/// This is intentionally not wired into the solver/proof path yet. Callers can
/// use it to inspect the exact projection that `try_wbo_to_pbo` already uses.
pub fn try_certified_wbo_projection(
    wbo: &WboInstance,
) -> Result<CertifiedWboProjection, WboProjectionUnsupported> {
    let pbo = try_wbo_to_pbo(wbo)
        .map_err(|err| WboProjectionUnsupported::from_conversion_error(wbo, err))?;
    Ok(build_certified_wbo_projection(wbo, pbo))
}

fn build_certified_wbo_projection(wbo: &WboInstance, pbo: PbInstance) -> CertifiedWboProjection {
    let hard_constraints = (0..wbo.hard_constraints.len())
        .map(|wbo_hard_index| WboHardConstraintMapping {
            wbo_hard_index,
            pbo_constraint_index: wbo_hard_index,
        })
        .collect();

    let mut soft_constraints = Vec::with_capacity(wbo.soft_constraints.len());
    let mut relaxation_vars = Vec::new();
    let mut objective_terms = Vec::new();
    let mut pbo_constraint_index = wbo.hard_constraints.len();
    let mut objective_term_index = 0usize;
    let hard_constraint_keys = build_hard_constraint_key_set(wbo);

    for (wbo_soft_index, (cost, constraint)) in wbo.soft_constraints.iter().enumerate() {
        if !should_relax_soft_constraint(*cost, constraint, hard_constraint_keys.as_ref()) {
            soft_constraints.push(WboSoftConstraintMapping {
                wbo_soft_index,
                cost: *cost,
                relaxation_var: None,
                pbo_constraint_start: None,
                pbo_constraint_len: 0,
                objective_term_index: None,
            });
            continue;
        }

        let relaxation_var = wbo.num_vars + relaxation_vars.len() as u32 + 1;
        let pbo_constraint_len = relaxed_soft_constraint_len(constraint);
        soft_constraints.push(WboSoftConstraintMapping {
            wbo_soft_index,
            cost: *cost,
            relaxation_var: Some(relaxation_var),
            pbo_constraint_start: Some(pbo_constraint_index),
            pbo_constraint_len,
            objective_term_index: Some(objective_term_index),
        });
        relaxation_vars.push(WboRelaxationVarMapping {
            wbo_soft_index,
            relaxation_var,
            pbo_constraint_start: pbo_constraint_index,
            pbo_constraint_len,
            objective_term_index,
        });
        objective_terms.push(WboObjectiveTermMapping {
            objective_term_index,
            wbo_soft_index,
            relaxation_var,
            cost: *cost,
        });

        pbo_constraint_index += pbo_constraint_len;
        objective_term_index += 1;
    }

    let top_cost_budget_constraint =
        (pbo_constraint_index < pbo.constraints.len()).then_some(pbo_constraint_index);
    debug_assert_eq!(
        pbo_constraint_index + usize::from(top_cost_budget_constraint.is_some()),
        pbo.constraints.len()
    );
    debug_assert_eq!(
        objective_term_index,
        pbo.objective.as_ref().map_or(0, |obj| obj.terms.len())
    );

    CertifiedWboProjection {
        original_num_vars: wbo.num_vars,
        projected_num_vars: pbo.num_vars,
        pbo,
        hard_constraints,
        soft_constraints,
        relaxation_vars,
        objective_terms,
        top_cost_budget_constraint,
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct ConstraintKey {
    terms: Vec<TermKey>,
    rel: PbRel,
    rhs: i128,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct TermKey {
    coeff: i128,
    lits: Vec<(u32, bool)>,
}

fn constraint_key_set(constraints: &[PbConstraint]) -> HashSet<ConstraintKey> {
    constraints.iter().map(constraint_key).collect()
}

fn build_hard_constraint_key_set(wbo: &WboInstance) -> Option<HashSet<ConstraintKey>> {
    if wbo.hard_constraints.is_empty() {
        None
    } else {
        Some(constraint_key_set(&wbo.hard_constraints))
    }
}

fn constraint_key(constraint: &PbConstraint) -> ConstraintKey {
    let mut terms: Vec<TermKey> = constraint.terms.iter().map(term_key).collect();
    terms.sort_unstable();
    ConstraintKey {
        terms,
        rel: constraint.rel,
        rhs: constraint.rhs,
    }
}

fn term_key(term: &PbTerm) -> TermKey {
    let mut lits: Vec<(u32, bool)> = term.lits.iter().map(|lit| (lit.var, lit.negated)).collect();
    lits.sort_unstable();
    TermKey {
        coeff: term.coeff,
        lits,
    }
}

fn should_relax_soft_constraint(
    cost: i128,
    constraint: &PbConstraint,
    hard_constraint_keys: Option<&HashSet<ConstraintKey>>,
) -> bool {
    if cost == 0 {
        return false;
    }

    if let Some(keys) = hard_constraint_keys {
        if keys.contains(&constraint_key(constraint)) {
            return false;
        }
    }

    true
}

fn relaxed_soft_constraint_len(constraint: &PbConstraint) -> usize {
    match constraint.rel {
        PbRel::Ge => 1,
        PbRel::Eq => 2,
    }
}

fn refine_projection_unsupported_reason(
    wbo: &WboInstance,
    source: WboToPboError,
) -> WboProjectionUnsupportedReason {
    match source {
        WboToPboError::ExplicitObjectiveUnsupported => {
            WboProjectionUnsupportedReason::ExplicitObjectiveUnsupported {
                objective_term_count: wbo
                    .objective
                    .as_ref()
                    .map_or(0, |objective| objective.terms.len()),
            }
        }
        WboToPboError::NegativeSoftCost => {
            if let Some((wbo_soft_index, cost)) = first_negative_soft_cost(wbo) {
                WboProjectionUnsupportedReason::NegativeSoftCost {
                    wbo_soft_index,
                    cost,
                }
            } else {
                WboProjectionUnsupportedReason::ConversionRejected { source }
            }
        }
        WboToPboError::VariableCountOverflow => {
            WboProjectionUnsupportedReason::VariableCountOverflow {
                original_num_vars: wbo.num_vars,
                relaxed_soft_constraints: relaxed_soft_constraint_count(wbo),
            }
        }
        WboToPboError::RelaxedSoftCountOverflow => {
            WboProjectionUnsupportedReason::RelaxedSoftCountOverflow {
                relaxed_soft_constraints: relaxed_soft_constraint_count(wbo),
            }
        }
        WboToPboError::RelaxationCoefficientOverflow => {
            if let Some((wbo_soft_index, direction)) = first_relaxation_coefficient_overflow(wbo) {
                WboProjectionUnsupportedReason::RelaxationCoefficientOverflow {
                    wbo_soft_index,
                    direction,
                }
            } else {
                WboProjectionUnsupportedReason::ConversionRejected { source }
            }
        }
        WboToPboError::SoftEqualityRhsOverflow => {
            if let Some((wbo_soft_index, rhs)) = first_soft_equality_rhs_overflow(wbo) {
                WboProjectionUnsupportedReason::SoftEqualityRhsOverflow {
                    wbo_soft_index,
                    rhs,
                }
            } else {
                WboProjectionUnsupportedReason::ConversionRejected { source }
            }
        }
        WboToPboError::SoftEqualityCoefficientOverflow => {
            if let Some((wbo_soft_index, term_index, coeff)) =
                first_soft_equality_coefficient_overflow(wbo)
            {
                WboProjectionUnsupportedReason::SoftEqualityCoefficientOverflow {
                    wbo_soft_index,
                    term_index,
                    coeff,
                }
            } else {
                WboProjectionUnsupportedReason::ConversionRejected { source }
            }
        }
    }
}

fn first_negative_soft_cost(wbo: &WboInstance) -> Option<(usize, i128)> {
    wbo.soft_constraints
        .iter()
        .enumerate()
        .find_map(|(wbo_soft_index, (cost, _))| (*cost < 0).then_some((wbo_soft_index, *cost)))
}

fn relaxed_soft_constraint_count(wbo: &WboInstance) -> usize {
    let hard_constraint_keys = build_hard_constraint_key_set(wbo);
    wbo.soft_constraints
        .iter()
        .filter(|(cost, constraint)| {
            should_relax_soft_constraint(*cost, constraint, hard_constraint_keys.as_ref())
        })
        .count()
}

fn first_relaxation_coefficient_overflow(
    wbo: &WboInstance,
) -> Option<(usize, WboRelaxedConstraintDirection)> {
    let hard_constraint_keys = build_hard_constraint_key_set(wbo);
    for (wbo_soft_index, (cost, constraint)) in wbo.soft_constraints.iter().enumerate() {
        if !should_relax_soft_constraint(*cost, constraint, hard_constraint_keys.as_ref()) {
            continue;
        }

        match constraint.rel {
            PbRel::Ge => {
                if matches!(
                    try_compute_relaxation_coefficient(&constraint.terms, constraint.rhs),
                    Err(WboToPboError::RelaxationCoefficientOverflow)
                ) {
                    return Some((wbo_soft_index, WboRelaxedConstraintDirection::SoftGe));
                }
            }
            PbRel::Eq => {
                if matches!(
                    try_compute_relaxation_coefficient(&constraint.terms, constraint.rhs),
                    Err(WboToPboError::RelaxationCoefficientOverflow)
                ) {
                    return Some((
                        wbo_soft_index,
                        WboRelaxedConstraintDirection::SoftEqLowerBound,
                    ));
                }

                let negated_rhs = match constraint.rhs.checked_neg() {
                    Some(rhs) => rhs,
                    None => continue,
                };
                let negated_terms = match negate_terms(&constraint.terms) {
                    Ok(terms) => terms,
                    Err(_) => continue,
                };
                if matches!(
                    try_compute_relaxation_coefficient(&negated_terms, negated_rhs),
                    Err(WboToPboError::RelaxationCoefficientOverflow)
                ) {
                    return Some((
                        wbo_soft_index,
                        WboRelaxedConstraintDirection::SoftEqUpperBound,
                    ));
                }
            }
        }
    }

    None
}

fn first_soft_equality_rhs_overflow(wbo: &WboInstance) -> Option<(usize, i128)> {
    let hard_constraint_keys = build_hard_constraint_key_set(wbo);
    wbo.soft_constraints
        .iter()
        .enumerate()
        .find_map(|(wbo_soft_index, (cost, constraint))| {
            if should_relax_soft_constraint(*cost, constraint, hard_constraint_keys.as_ref())
                && constraint.rel == PbRel::Eq
                && constraint.rhs == i128::MIN
            {
                Some((wbo_soft_index, constraint.rhs))
            } else {
                None
            }
        })
}

fn first_soft_equality_coefficient_overflow(wbo: &WboInstance) -> Option<(usize, usize, i128)> {
    let hard_constraint_keys = build_hard_constraint_key_set(wbo);
    for (wbo_soft_index, (cost, constraint)) in wbo.soft_constraints.iter().enumerate() {
        if !should_relax_soft_constraint(*cost, constraint, hard_constraint_keys.as_ref())
            || constraint.rel != PbRel::Eq
        {
            continue;
        }

        for (term_index, term) in constraint.terms.iter().enumerate() {
            if term.coeff == i128::MIN {
                return Some((wbo_soft_index, term_index, term.coeff));
            }
        }
    }

    None
}

fn relax_soft_constraint(
    constraint: &PbConstraint,
    relax_var: u32,
) -> Result<Vec<PbConstraint>, WboToPboError> {
    match constraint.rel {
        PbRel::Ge => Ok(vec![relax_ge_constraint(
            &constraint.terms,
            constraint.rhs,
            relax_var,
        )?]),
        PbRel::Eq => {
            let negated_rhs = constraint
                .rhs
                .checked_neg()
                .ok_or(WboToPboError::SoftEqualityRhsOverflow)?;
            let negated_terms = negate_terms(&constraint.terms)?;

            Ok(vec![
                relax_ge_constraint(&constraint.terms, constraint.rhs, relax_var)?,
                relax_ge_constraint(&negated_terms, negated_rhs, relax_var)?,
            ])
        }
    }
}

fn relax_ge_constraint(
    terms: &[PbTerm],
    rhs: i128,
    relax_var: u32,
) -> Result<PbConstraint, WboToPboError> {
    // M must be large enough that setting r_i = 1 can satisfy this >= direction
    // regardless of the original assignment.
    let big_m = try_compute_relaxation_coefficient(terms, rhs)?;

    let mut relaxed_terms = terms.to_vec();
    relaxed_terms.push(PbTerm {
        coeff: big_m,
        lits: vec![PbLit {
            var: relax_var,
            negated: false,
        }],
    });

    Ok(PbConstraint {
        terms: relaxed_terms,
        rel: PbRel::Ge,
        rhs,
    })
}

fn negate_terms(terms: &[PbTerm]) -> Result<Vec<PbTerm>, WboToPboError> {
    terms
        .iter()
        .map(|term| {
            Ok(PbTerm {
                coeff: term
                    .coeff
                    .checked_neg()
                    .ok_or(WboToPboError::SoftEqualityCoefficientOverflow)?,
                lits: term.lits.clone(),
            })
        })
        .collect()
}

/// Computes the relaxation coefficient M for a single `>=` direction.
///
/// For a constraint `sum(c_i * l_i) >= rhs`:
/// - When r_i = 1, we need the constraint to be trivially satisfiable
/// - The minimum possible value of `sum(c_i * l_i)` is the sum of all negative contributions
/// - M must be >= rhs - min_possible_lhs
fn try_compute_relaxation_coefficient(terms: &[PbTerm], rhs: i128) -> Result<i128, WboToPboError> {
    // Compute minimum possible LHS value (all terms at their worst).
    // For a term c * l: if c > 0, worst is l=0 contributing 0; if c < 0, worst is l=1 contributing c.
    // The accumulation and the deficit `rhs - min_lhs` can overflow i128 (e.g.
    // a negative coefficient near i128::MIN combined with a large rhs); detect
    // that and fail closed rather than wrapping to a bogus relaxation weight.
    let mut min_lhs: i128 = 0;
    for t in terms {
        if t.coeff < 0 {
            min_lhs = min_lhs
                .checked_add(t.coeff)
                .ok_or(WboToPboError::RelaxationCoefficientOverflow)?;
        }
    }

    let deficit = rhs
        .checked_sub(min_lhs)
        .ok_or(WboToPboError::RelaxationCoefficientOverflow)?;
    let m = deficit.max(1);

    i128::try_from(m).map_err(|_| WboToPboError::RelaxationCoefficientOverflow)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::PbRel;

    fn linear_term(coeff: i128, var: u32) -> PbTerm {
        PbTerm {
            coeff,
            lits: vec![PbLit {
                var,
                negated: false,
            }],
        }
    }

    #[test]
    fn test_wbo_to_pbo_hard_constraints_preserved() {
        let wbo = WboInstance {
            top_cost: Some(100),
            num_vars: 2,
            hard_constraints: vec![PbConstraint {
                terms: vec![linear_term(1, 1), linear_term(1, 2)],
                rel: PbRel::Ge,
                rhs: 1,
            }],
            soft_constraints: vec![],
            objective: None,
        };

        let pbo = wbo_to_pbo(&wbo);
        assert_eq!(pbo.num_vars, 2); // No relaxation vars added
        assert_eq!(pbo.constraints.len(), 1);
        assert_eq!(pbo.constraints[0].rhs, 1);
    }

    #[test]
    fn test_wbo_to_pbo_soft_constraint_relaxed() {
        let wbo = WboInstance {
            top_cost: Some(10),
            num_vars: 2,
            hard_constraints: vec![],
            soft_constraints: vec![(
                5,
                PbConstraint {
                    terms: vec![linear_term(1, 1), linear_term(1, 2)],
                    rel: PbRel::Ge,
                    rhs: 2,
                },
            )],
            objective: None,
        };

        let pbo = wbo_to_pbo(&wbo);
        assert_eq!(pbo.num_vars, 3); // 2 original + 1 relaxation
        assert_eq!(pbo.constraints.len(), 1);

        // The relaxed constraint should have an extra term with relax_var = 3
        let relaxed = &pbo.constraints[0];
        assert_eq!(relaxed.terms.len(), 3); // 2 original + 1 relaxation
        let relax_term = &relaxed.terms[2];
        assert_eq!(relax_term.lits[0].var, 3);
        assert!(!relax_term.lits[0].negated);

        // Objective should minimize 5 * r_1
        let obj = pbo.objective.as_ref().expect("should have objective");
        assert_eq!(obj.terms.len(), 1);
        assert_eq!(obj.terms[0].coeff, 5);
        assert_eq!(obj.terms[0].lits[0].var, 3);
    }

    #[test]
    fn test_wbo_to_pbo_soft_equality_relaxes_both_halves_with_shared_cost() {
        let wbo = WboInstance {
            top_cost: Some(10),
            num_vars: 2,
            hard_constraints: vec![],
            soft_constraints: vec![(
                5,
                PbConstraint {
                    terms: vec![linear_term(1, 1), linear_term(1, 2)],
                    rel: PbRel::Eq,
                    rhs: 1,
                },
            )],
            objective: None,
        };

        let pbo = wbo_to_pbo(&wbo);
        assert_eq!(pbo.num_vars, 3);
        assert_eq!(pbo.constraints.len(), 2);
        assert!(pbo
            .constraints
            .iter()
            .all(|constraint| constraint.rel == PbRel::Ge));

        for constraint in &pbo.constraints {
            let relax_term = constraint
                .terms
                .last()
                .expect("relaxed equality must include a relaxation variable");
            assert_eq!(relax_term.lits.len(), 1);
            assert_eq!(relax_term.lits[0].var, 3);
            assert_eq!(relax_term.coeff, 1);
        }

        let obj = pbo.objective.as_ref().expect("should have objective");
        assert_eq!(obj.terms.len(), 1);
        assert_eq!(obj.terms[0].coeff, 5);
        assert_eq!(obj.terms[0].lits[0].var, 3);
    }

    #[test]
    fn test_wbo_to_pbo_multiple_soft_constraints() {
        let wbo = WboInstance {
            top_cost: Some(100),
            num_vars: 3,
            hard_constraints: vec![PbConstraint {
                terms: vec![linear_term(1, 1)],
                rel: PbRel::Ge,
                rhs: 1,
            }],
            soft_constraints: vec![
                (
                    2,
                    PbConstraint {
                        terms: vec![linear_term(1, 2)],
                        rel: PbRel::Ge,
                        rhs: 1,
                    },
                ),
                (
                    3,
                    PbConstraint {
                        terms: vec![linear_term(1, 3)],
                        rel: PbRel::Ge,
                        rhs: 1,
                    },
                ),
            ],
            objective: None,
        };

        let pbo = wbo_to_pbo(&wbo);
        assert_eq!(pbo.num_vars, 5); // 3 original + 2 relaxation
        assert_eq!(pbo.constraints.len(), 3); // 1 hard + 2 relaxed soft

        let obj = pbo.objective.as_ref().expect("should have objective");
        assert_eq!(obj.terms.len(), 2);
        assert_eq!(obj.terms[0].coeff, 2); // cost of first soft
        assert_eq!(obj.terms[0].lits[0].var, 4); // r_1
        assert_eq!(obj.terms[1].coeff, 3); // cost of second soft
        assert_eq!(obj.terms[1].lits[0].var, 5); // r_2
    }

    #[test]
    fn test_wbo_to_pbo_skips_zero_cost_soft_constraints() {
        let wbo = WboInstance {
            top_cost: Some(100),
            num_vars: 2,
            hard_constraints: vec![PbConstraint {
                terms: vec![linear_term(1, 1)],
                rel: PbRel::Ge,
                rhs: 1,
            }],
            soft_constraints: vec![
                (
                    0,
                    PbConstraint {
                        terms: vec![linear_term(1, 1), linear_term(1, 2)],
                        rel: PbRel::Eq,
                        rhs: 1,
                    },
                ),
                (
                    4,
                    PbConstraint {
                        terms: vec![linear_term(1, 2)],
                        rel: PbRel::Ge,
                        rhs: 1,
                    },
                ),
            ],
            objective: None,
        };

        let pbo = wbo_to_pbo(&wbo);
        assert_eq!(pbo.num_vars, 3); // 2 original + one paid relaxation var
        assert_eq!(pbo.constraints.len(), 2); // hard + paid soft only

        let relaxed = &pbo.constraints[1];
        let relax_term = relaxed
            .terms
            .last()
            .expect("paid soft constraint should be relaxed");
        assert_eq!(relax_term.lits[0].var, 3);

        let obj = pbo.objective.as_ref().expect("should have objective");
        assert_eq!(obj.terms.len(), 1);
        assert_eq!(obj.terms[0].coeff, 4);
        assert_eq!(obj.terms[0].lits[0].var, 3);
    }

    #[test]
    fn test_wbo_to_pbo_skips_soft_constraint_already_enforced_as_hard() {
        let wbo = WboInstance {
            top_cost: Some(100),
            num_vars: 3,
            hard_constraints: vec![PbConstraint {
                terms: vec![linear_term(1, 1), linear_term(1, 2)],
                rel: PbRel::Ge,
                rhs: 1,
            }],
            soft_constraints: vec![
                (
                    5,
                    PbConstraint {
                        terms: vec![linear_term(1, 2), linear_term(1, 1)],
                        rel: PbRel::Ge,
                        rhs: 1,
                    },
                ),
                (
                    7,
                    PbConstraint {
                        terms: vec![linear_term(1, 3)],
                        rel: PbRel::Ge,
                        rhs: 1,
                    },
                ),
            ],
            objective: None,
        };

        let pbo = wbo_to_pbo(&wbo);
        assert_eq!(pbo.num_vars, 4);
        assert_eq!(pbo.constraints.len(), 2);

        let relaxed = &pbo.constraints[1];
        let relax_term = relaxed
            .terms
            .last()
            .expect("remaining paid soft constraint should be relaxed");
        assert_eq!(relax_term.lits[0].var, 4);

        let obj = pbo.objective.as_ref().expect("should have objective");
        assert_eq!(obj.terms.len(), 1);
        assert_eq!(obj.terms[0].coeff, 7);
        assert_eq!(obj.terms[0].lits[0].var, 4);
    }

    #[test]
    fn test_certified_wbo_projection_exposes_all_mappings() {
        let wbo = WboInstance {
            top_cost: Some(100),
            num_vars: 3,
            hard_constraints: vec![
                PbConstraint {
                    terms: vec![linear_term(1, 1)],
                    rel: PbRel::Ge,
                    rhs: 1,
                },
                PbConstraint {
                    terms: vec![linear_term(1, 2)],
                    rel: PbRel::Ge,
                    rhs: 0,
                },
            ],
            soft_constraints: vec![
                (
                    0,
                    PbConstraint {
                        terms: vec![linear_term(1, 1), linear_term(1, 2)],
                        rel: PbRel::Eq,
                        rhs: 1,
                    },
                ),
                (
                    4,
                    PbConstraint {
                        terms: vec![linear_term(1, 2)],
                        rel: PbRel::Ge,
                        rhs: 1,
                    },
                ),
                (
                    7,
                    PbConstraint {
                        terms: vec![linear_term(1, 2), linear_term(1, 3)],
                        rel: PbRel::Eq,
                        rhs: 1,
                    },
                ),
            ],
            objective: None,
        };

        let converted = try_wbo_to_pbo(&wbo).expect("conversion should succeed");
        let projection =
            try_certified_wbo_projection(&wbo).expect("projection metadata should build");

        assert_eq!(projection.pbo, converted);
        assert_eq!(projection.original_num_vars, 3);
        assert_eq!(projection.projected_num_vars, 5);
        assert_eq!(
            projection.hard_constraints,
            vec![
                WboHardConstraintMapping {
                    wbo_hard_index: 0,
                    pbo_constraint_index: 0,
                },
                WboHardConstraintMapping {
                    wbo_hard_index: 1,
                    pbo_constraint_index: 1,
                },
            ]
        );
        assert_eq!(
            projection.soft_constraints[0],
            WboSoftConstraintMapping {
                wbo_soft_index: 0,
                cost: 0,
                relaxation_var: None,
                pbo_constraint_start: None,
                pbo_constraint_len: 0,
                objective_term_index: None,
            }
        );
        assert!(!projection.soft_constraints[0].is_relaxed());
        assert_eq!(
            projection.soft_constraints[0].pbo_constraint_indices(),
            None
        );
        assert_eq!(
            projection.soft_constraints[1],
            WboSoftConstraintMapping {
                wbo_soft_index: 1,
                cost: 4,
                relaxation_var: Some(4),
                pbo_constraint_start: Some(2),
                pbo_constraint_len: 1,
                objective_term_index: Some(0),
            }
        );
        assert!(projection.soft_constraints[1].is_relaxed());
        assert_eq!(
            projection.soft_constraints[1].pbo_constraint_indices(),
            Some(2..3)
        );
        assert_eq!(
            projection.soft_constraints[2],
            WboSoftConstraintMapping {
                wbo_soft_index: 2,
                cost: 7,
                relaxation_var: Some(5),
                pbo_constraint_start: Some(3),
                pbo_constraint_len: 2,
                objective_term_index: Some(1),
            }
        );
        assert_eq!(
            projection.soft_constraints[2].pbo_constraint_indices(),
            Some(3..5)
        );
        assert_eq!(
            projection.relaxation_vars,
            vec![
                WboRelaxationVarMapping {
                    wbo_soft_index: 1,
                    relaxation_var: 4,
                    pbo_constraint_start: 2,
                    pbo_constraint_len: 1,
                    objective_term_index: 0,
                },
                WboRelaxationVarMapping {
                    wbo_soft_index: 2,
                    relaxation_var: 5,
                    pbo_constraint_start: 3,
                    pbo_constraint_len: 2,
                    objective_term_index: 1,
                },
            ]
        );
        assert_eq!(projection.relaxation_vars[1].pbo_constraint_indices(), 3..5);
        assert_eq!(
            projection.objective_terms,
            vec![
                WboObjectiveTermMapping {
                    objective_term_index: 0,
                    wbo_soft_index: 1,
                    relaxation_var: 4,
                    cost: 4,
                },
                WboObjectiveTermMapping {
                    objective_term_index: 1,
                    wbo_soft_index: 2,
                    relaxation_var: 5,
                    cost: 7,
                },
            ]
        );
    }

    #[test]
    fn test_certified_wbo_projection_marks_hard_duplicate_soft_rows_skipped() {
        let wbo = WboInstance {
            top_cost: Some(100),
            num_vars: 3,
            hard_constraints: vec![PbConstraint {
                terms: vec![linear_term(1, 1), linear_term(1, 2)],
                rel: PbRel::Ge,
                rhs: 1,
            }],
            soft_constraints: vec![
                (
                    5,
                    PbConstraint {
                        terms: vec![linear_term(1, 2), linear_term(1, 1)],
                        rel: PbRel::Ge,
                        rhs: 1,
                    },
                ),
                (
                    7,
                    PbConstraint {
                        terms: vec![linear_term(1, 3)],
                        rel: PbRel::Ge,
                        rhs: 1,
                    },
                ),
            ],
            objective: None,
        };

        let converted = try_wbo_to_pbo(&wbo).expect("conversion should succeed");
        let projection =
            try_certified_wbo_projection(&wbo).expect("projection metadata should build");

        assert_eq!(projection.pbo, converted);
        assert_eq!(projection.projected_num_vars, 4);
        assert_eq!(
            projection.soft_constraints[0],
            WboSoftConstraintMapping {
                wbo_soft_index: 0,
                cost: 5,
                relaxation_var: None,
                pbo_constraint_start: None,
                pbo_constraint_len: 0,
                objective_term_index: None,
            }
        );
        assert!(!projection.soft_constraints[0].is_relaxed());
        assert_eq!(
            projection.soft_constraints[1],
            WboSoftConstraintMapping {
                wbo_soft_index: 1,
                cost: 7,
                relaxation_var: Some(4),
                pbo_constraint_start: Some(1),
                pbo_constraint_len: 1,
                objective_term_index: Some(0),
            }
        );
        assert_eq!(
            projection.relaxation_vars,
            vec![WboRelaxationVarMapping {
                wbo_soft_index: 1,
                relaxation_var: 4,
                pbo_constraint_start: 1,
                pbo_constraint_len: 1,
                objective_term_index: 0,
            }]
        );
        assert_eq!(
            projection.objective_terms,
            vec![WboObjectiveTermMapping {
                objective_term_index: 0,
                wbo_soft_index: 1,
                relaxation_var: 4,
                cost: 7,
            }]
        );
    }

    #[test]
    fn test_certified_wbo_projection_variable_overflow_counts_only_relaxed_soft_rows() {
        let hard = PbConstraint {
            terms: vec![linear_term(1, 1)],
            rel: PbRel::Ge,
            rhs: 1,
        };
        let wbo = WboInstance {
            top_cost: Some(100),
            num_vars: u32::MAX,
            hard_constraints: vec![hard.clone()],
            soft_constraints: vec![
                (5, hard),
                (
                    7,
                    PbConstraint {
                        terms: vec![linear_term(1, 2)],
                        rel: PbRel::Ge,
                        rhs: 1,
                    },
                ),
            ],
            objective: None,
        };

        let err = try_certified_wbo_projection(&wbo).expect_err("variable count should overflow");
        assert_eq!(
            err.reason,
            WboProjectionUnsupportedReason::VariableCountOverflow {
                original_num_vars: u32::MAX,
                relaxed_soft_constraints: 1,
            }
        );
    }

    #[test]
    fn test_certified_wbo_projection_overflow_reason_ignores_hard_duplicate_soft_rows() {
        let hard = PbConstraint {
            terms: vec![linear_term(i128::MIN, 1)],
            rel: PbRel::Eq,
            rhs: 0,
        };
        let wbo = WboInstance {
            top_cost: Some(100),
            num_vars: 2,
            hard_constraints: vec![hard.clone()],
            soft_constraints: vec![
                (5, hard),
                (
                    7,
                    PbConstraint {
                        terms: vec![linear_term(i128::MIN, 2)],
                        rel: PbRel::Eq,
                        rhs: 0,
                    },
                ),
            ],
            objective: None,
        };

        let err = try_certified_wbo_projection(&wbo)
            .expect_err("relaxed soft equality coefficient should overflow");
        assert_eq!(
            err.reason,
            WboProjectionUnsupportedReason::SoftEqualityCoefficientOverflow {
                wbo_soft_index: 1,
                term_index: 0,
                coeff: i128::MIN,
            }
        );
    }

    #[test]
    fn test_wbo_to_pbo_binding_top_cost_appends_budget_row() {
        // Hard row forbids x1 and x2 together; both softs cost 2, so every
        // model falsifies at least one soft (minimum cost 2). top = 2 makes
        // the instance UNSATISFIABLE under the strictly-less-than rule; the
        // converted PBO must carry the budget row so the solver can prove it.
        let wbo = WboInstance {
            top_cost: Some(2),
            num_vars: 2,
            hard_constraints: vec![PbConstraint {
                terms: vec![linear_term(-1, 1), linear_term(-1, 2)],
                rel: PbRel::Ge,
                rhs: -1,
            }],
            soft_constraints: vec![
                (
                    2,
                    PbConstraint {
                        terms: vec![linear_term(1, 1)],
                        rel: PbRel::Ge,
                        rhs: 1,
                    },
                ),
                (
                    2,
                    PbConstraint {
                        terms: vec![linear_term(1, 2)],
                        rel: PbRel::Ge,
                        rhs: 1,
                    },
                ),
            ],
            objective: None,
        };

        let pbo = wbo_to_pbo(&wbo);
        assert_eq!(pbo.num_vars, 4); // 2 original + 2 relaxation
        assert_eq!(pbo.constraints.len(), 4); // hard + 2 relaxed + budget row

        // Budget row: -2 r3 -2 r4 >= 1 - 2, i.e. 2*r3 + 2*r4 <= 1.
        let budget = &pbo.constraints[3];
        assert_eq!(budget.rel, PbRel::Ge);
        assert_eq!(budget.rhs, -1);
        assert_eq!(budget.terms.len(), 2);
        assert_eq!(budget.terms[0].coeff, -2);
        assert_eq!(
            budget.terms[0].lits,
            vec![PbLit {
                var: 3,
                negated: false
            }]
        );
        assert_eq!(budget.terms[1].coeff, -2);
        assert_eq!(
            budget.terms[1].lits,
            vec![PbLit {
                var: 4,
                negated: false
            }]
        );

        let projection =
            try_certified_wbo_projection(&wbo).expect("projection metadata should build");
        assert_eq!(projection.top_cost_budget_constraint, Some(3));
    }

    #[test]
    fn test_wbo_to_pbo_vacuous_top_cost_appends_no_budget_row() {
        // Total paid cost 4 <= top - 1 = 4: the budget can never bind, so the
        // conversion is unchanged (byte-identical to the no-top conversion).
        let soft = PbConstraint {
            terms: vec![linear_term(1, 1)],
            rel: PbRel::Ge,
            rhs: 1,
        };
        let bounded = WboInstance {
            top_cost: Some(5),
            num_vars: 1,
            hard_constraints: vec![],
            soft_constraints: vec![(4, soft.clone())],
            objective: None,
        };
        let unbounded = WboInstance {
            top_cost: None,
            ..bounded.clone()
        };

        assert_eq!(wbo_to_pbo(&bounded), wbo_to_pbo(&unbounded));
        assert_eq!(wbo_to_pbo(&bounded).constraints.len(), 1);
    }

    #[test]
    fn test_wbo_to_pbo_omitted_top_cost_appends_no_budget_row() {
        let wbo = WboInstance {
            top_cost: None,
            num_vars: 1,
            hard_constraints: vec![],
            soft_constraints: vec![(
                4,
                PbConstraint {
                    terms: vec![linear_term(1, 1)],
                    rel: PbRel::Ge,
                    rhs: 1,
                },
            )],
            objective: None,
        };

        let pbo = wbo_to_pbo(&wbo);
        assert_eq!(pbo.constraints.len(), 1); // relaxed soft only, no budget
    }

    #[test]
    fn test_wbo_to_pbo_nonpositive_top_cost_appends_falsity_row() {
        // Costs are non-negative, so top <= 0 admits no model: the conversion
        // carries an unsatisfiable `0 >= 1` backstop row.
        let wbo = WboInstance {
            top_cost: Some(0),
            num_vars: 1,
            hard_constraints: vec![PbConstraint {
                terms: vec![linear_term(1, 1)],
                rel: PbRel::Ge,
                rhs: 1,
            }],
            soft_constraints: vec![],
            objective: None,
        };

        let pbo = wbo_to_pbo(&wbo);
        let falsity = pbo
            .constraints
            .last()
            .expect("falsity backstop row should be appended");
        assert!(falsity.terms.is_empty());
        assert_eq!(falsity.rel, PbRel::Ge);
        assert_eq!(falsity.rhs, 1);
    }

    #[test]
    fn test_wbo_to_pbo_budget_row_caps_coefficients_at_top() {
        // A soft with cost >= top can never be falsified by an admissible
        // model; min(cost, top) still forces its r_i to 0 while keeping huge
        // parsed costs out of constraint coefficients.
        let wbo = WboInstance {
            top_cost: Some(2),
            num_vars: 1,
            hard_constraints: vec![],
            soft_constraints: vec![(
                i128::MAX,
                PbConstraint {
                    terms: vec![linear_term(1, 1)],
                    rel: PbRel::Ge,
                    rhs: 1,
                },
            )],
            objective: None,
        };

        let pbo = wbo_to_pbo(&wbo);
        let budget = pbo
            .constraints
            .last()
            .expect("binding top must append a budget row");
        assert_eq!(budget.terms.len(), 1);
        assert_eq!(budget.terms[0].coeff, -2); // capped at top, not -i128::MAX
        assert_eq!(budget.rhs, -1);

        // The objective still charges the ORIGINAL cost.
        let obj = pbo.objective.as_ref().expect("should have objective");
        assert_eq!(obj.terms[0].coeff, i128::MAX);
    }

    #[test]
    fn test_wbo_to_pbo_budget_row_skips_zero_cost_and_hard_duplicate_softs() {
        // Zero-cost softs and softs identical to a hard row are not relaxed;
        // the budget row must charge only the paid, relaxed soft.
        let hard = PbConstraint {
            terms: vec![linear_term(1, 1)],
            rel: PbRel::Ge,
            rhs: 1,
        };
        let wbo = WboInstance {
            top_cost: Some(3),
            num_vars: 2,
            hard_constraints: vec![hard.clone()],
            soft_constraints: vec![
                (5, hard),
                (
                    0,
                    PbConstraint {
                        terms: vec![linear_term(1, 2)],
                        rel: PbRel::Ge,
                        rhs: 0,
                    },
                ),
                (
                    3,
                    PbConstraint {
                        terms: vec![linear_term(1, 2)],
                        rel: PbRel::Ge,
                        rhs: 1,
                    },
                ),
            ],
            objective: None,
        };

        let pbo = wbo_to_pbo(&wbo);
        // hard + one relaxed soft + budget row.
        assert_eq!(pbo.constraints.len(), 3);
        let budget = &pbo.constraints[2];
        assert_eq!(budget.terms.len(), 1);
        assert_eq!(budget.terms[0].coeff, -3);
        assert_eq!(
            budget.terms[0].lits,
            vec![PbLit {
                var: 3,
                negated: false
            }]
        );
        assert_eq!(budget.rhs, -2); // 1 - top = -2, i.e. 3*r3 <= 2 forces r3 = 0
    }

    #[test]
    fn test_certified_wbo_projection_is_metadata_only_not_proof_wiring() {
        let wbo = WboInstance {
            top_cost: Some(20),
            num_vars: 2,
            hard_constraints: vec![PbConstraint {
                terms: vec![linear_term(1, 1)],
                rel: PbRel::Ge,
                rhs: 1,
            }],
            soft_constraints: vec![(
                3,
                PbConstraint {
                    terms: vec![linear_term(1, 2)],
                    rel: PbRel::Ge,
                    rhs: 1,
                },
            )],
            objective: None,
        };

        let converted = try_wbo_to_pbo(&wbo).expect("conversion should succeed");
        let projection =
            try_certified_wbo_projection(&wbo).expect("projection metadata should build");

        // Exhaustive destructuring is intentional: this type currently carries
        // projection metadata only. It does not hold proof rows, a proof writer,
        // or any proof-mode enablement for WBO inputs.
        let CertifiedWboProjection {
            pbo,
            original_num_vars,
            projected_num_vars,
            hard_constraints,
            soft_constraints,
            relaxation_vars,
            objective_terms,
            top_cost_budget_constraint,
        } = projection;

        assert_eq!(pbo, converted);
        assert_eq!(original_num_vars, 2);
        assert_eq!(projected_num_vars, 3);
        // Total paid cost (3) is already below the top cost (20), so no budget
        // row is appended.
        assert_eq!(top_cost_budget_constraint, None);
        assert_eq!(
            hard_constraints,
            vec![WboHardConstraintMapping {
                wbo_hard_index: 0,
                pbo_constraint_index: 0,
            }]
        );
        assert_eq!(
            soft_constraints,
            vec![WboSoftConstraintMapping {
                wbo_soft_index: 0,
                cost: 3,
                relaxation_var: Some(3),
                pbo_constraint_start: Some(1),
                pbo_constraint_len: 1,
                objective_term_index: Some(0),
            }]
        );
        assert_eq!(
            relaxation_vars,
            vec![WboRelaxationVarMapping {
                wbo_soft_index: 0,
                relaxation_var: 3,
                pbo_constraint_start: 1,
                pbo_constraint_len: 1,
                objective_term_index: 0,
            }]
        );
        assert_eq!(
            objective_terms,
            vec![WboObjectiveTermMapping {
                objective_term_index: 0,
                wbo_soft_index: 0,
                relaxation_var: 3,
                cost: 3,
            }]
        );
    }

    #[test]
    fn test_certified_wbo_projection_counts_projected_pbo_rows_not_wbo_proof_rows() {
        let wbo = WboInstance {
            top_cost: Some(20),
            num_vars: 2,
            hard_constraints: vec![PbConstraint {
                terms: vec![linear_term(1, 1), linear_term(1, 2)],
                rel: PbRel::Eq,
                rhs: 1,
            }],
            soft_constraints: vec![(
                5,
                PbConstraint {
                    terms: vec![linear_term(1, 1)],
                    rel: PbRel::Eq,
                    rhs: 1,
                },
            )],
            objective: None,
        };

        let projection =
            try_certified_wbo_projection(&wbo).expect("projection metadata should build");

        // A future WBO proof path must prove the original WBO-to-PBO projection.
        // The current scaffold only exposes the already-projected PBO formula;
        // VeriPB row accounting therefore applies to projected PBO rows, not to
        // original WBO hard/soft rows.
        let original_wbo_rows = wbo.hard_constraints.len() + wbo.soft_constraints.len();
        let projected_veripb_rows = crate::proof::veripb_input_constraint_count(&projection.pbo)
            .expect("projected row count should fit");

        assert_eq!(original_wbo_rows, 2);
        assert_eq!(projection.pbo.constraints.len(), 3);
        assert_eq!(projected_veripb_rows, 4);
        assert_ne!(projected_veripb_rows, original_wbo_rows as u64);
        assert_eq!(projection.hard_constraints[0].pbo_constraint_index, 0);
        assert_eq!(
            projection.soft_constraints[0].pbo_constraint_indices(),
            Some(1..3)
        );
    }

    #[test]
    fn test_certified_wbo_projection_reports_explicit_objective_terms() {
        let wbo = WboInstance {
            top_cost: Some(100),
            num_vars: 1,
            hard_constraints: vec![],
            soft_constraints: vec![],
            objective: Some(PbObjective {
                terms: vec![linear_term(7, 1), linear_term(3, 1)],
            }),
        };

        let err =
            try_certified_wbo_projection(&wbo).expect_err("explicit objective should be rejected");
        assert_eq!(
            err.reason,
            WboProjectionUnsupportedReason::ExplicitObjectiveUnsupported {
                objective_term_count: 2,
            }
        );
        assert_eq!(
            err.conversion_error(),
            WboToPboError::ExplicitObjectiveUnsupported
        );
    }

    #[test]
    fn test_certified_wbo_projection_reports_negative_soft_cost_index() {
        let wbo = WboInstance {
            top_cost: Some(100),
            num_vars: 2,
            hard_constraints: vec![],
            soft_constraints: vec![
                (
                    0,
                    PbConstraint {
                        terms: vec![linear_term(1, 1)],
                        rel: PbRel::Ge,
                        rhs: 1,
                    },
                ),
                (
                    -5,
                    PbConstraint {
                        terms: vec![linear_term(1, 2)],
                        rel: PbRel::Ge,
                        rhs: 1,
                    },
                ),
            ],
            objective: None,
        };

        let err =
            try_certified_wbo_projection(&wbo).expect_err("negative soft cost should be rejected");
        assert_eq!(
            err.reason,
            WboProjectionUnsupportedReason::NegativeSoftCost {
                wbo_soft_index: 1,
                cost: -5,
            }
        );
        assert_eq!(err.conversion_error(), WboToPboError::NegativeSoftCost);
    }

    #[test]
    fn test_certified_wbo_projection_reports_relaxation_overflow_index() {
        let wbo = WboInstance {
            top_cost: Some(100),
            num_vars: 2,
            hard_constraints: vec![],
            soft_constraints: vec![
                (
                    3,
                    PbConstraint {
                        terms: vec![linear_term(1, 1)],
                        rel: PbRel::Ge,
                        rhs: 1,
                    },
                ),
                (
                    0,
                    PbConstraint {
                        terms: vec![linear_term(i128::MIN, 1)],
                        rel: PbRel::Ge,
                        rhs: i128::MAX,
                    },
                ),
                (
                    5,
                    PbConstraint {
                        terms: vec![linear_term(i128::MIN, 2)],
                        rel: PbRel::Ge,
                        rhs: i128::MAX,
                    },
                ),
            ],
            objective: None,
        };

        let err =
            try_certified_wbo_projection(&wbo).expect_err("relaxation coefficient should overflow");
        assert_eq!(
            err.reason,
            WboProjectionUnsupportedReason::RelaxationCoefficientOverflow {
                wbo_soft_index: 2,
                direction: WboRelaxedConstraintDirection::SoftGe,
            }
        );
        assert_eq!(
            err.conversion_error(),
            WboToPboError::RelaxationCoefficientOverflow
        );
    }

    #[test]
    fn test_certified_wbo_projection_reports_soft_equality_coefficient_index() {
        let wbo = WboInstance {
            top_cost: Some(100),
            num_vars: 2,
            hard_constraints: vec![],
            soft_constraints: vec![
                (
                    0,
                    PbConstraint {
                        terms: vec![linear_term(i128::MIN, 1)],
                        rel: PbRel::Eq,
                        rhs: 0,
                    },
                ),
                (
                    5,
                    PbConstraint {
                        terms: vec![linear_term(1, 1), linear_term(i128::MIN, 2)],
                        rel: PbRel::Eq,
                        rhs: 0,
                    },
                ),
            ],
            objective: None,
        };

        let err = try_certified_wbo_projection(&wbo)
            .expect_err("soft equality coefficient negation should fail");
        assert_eq!(
            err.reason,
            WboProjectionUnsupportedReason::SoftEqualityCoefficientOverflow {
                wbo_soft_index: 1,
                term_index: 1,
                coeff: i128::MIN,
            }
        );
        assert_eq!(
            err.conversion_error(),
            WboToPboError::SoftEqualityCoefficientOverflow
        );
    }

    #[test]
    #[should_panic(expected = "invalid WBO instance cannot be converted to PBO")]
    fn test_wbo_to_pbo_rejects_explicit_objective() {
        let wbo = WboInstance {
            top_cost: Some(100),
            num_vars: 1,
            hard_constraints: vec![],
            soft_constraints: vec![(
                5,
                PbConstraint {
                    terms: vec![linear_term(1, 1)],
                    rel: PbRel::Ge,
                    rhs: 1,
                },
            )],
            objective: Some(PbObjective {
                terms: vec![linear_term(7, 1)],
            }),
        };

        let _ = wbo_to_pbo(&wbo);
    }

    #[test]
    fn test_try_wbo_to_pbo_rejects_explicit_objective_without_panicking() {
        let wbo = WboInstance {
            top_cost: Some(100),
            num_vars: 1,
            hard_constraints: vec![],
            soft_constraints: vec![(
                5,
                PbConstraint {
                    terms: vec![linear_term(1, 1)],
                    rel: PbRel::Ge,
                    rhs: 1,
                },
            )],
            objective: Some(PbObjective {
                terms: vec![linear_term(7, 1)],
            }),
        };

        assert_eq!(
            try_wbo_to_pbo(&wbo),
            Err(WboToPboError::ExplicitObjectiveUnsupported)
        );
    }

    #[test]
    fn test_try_wbo_to_pbo_rejects_negative_soft_cost_without_panicking() {
        let wbo = WboInstance {
            top_cost: Some(100),
            num_vars: 1,
            hard_constraints: vec![],
            soft_constraints: vec![(
                -1,
                PbConstraint {
                    terms: vec![linear_term(1, 1)],
                    rel: PbRel::Ge,
                    rhs: 1,
                },
            )],
            objective: None,
        };

        assert_eq!(try_wbo_to_pbo(&wbo), Err(WboToPboError::NegativeSoftCost));
    }

    #[test]
    fn test_try_wbo_to_pbo_fails_closed_on_variable_count_overflow() {
        let wbo = WboInstance {
            top_cost: Some(100),
            num_vars: u32::MAX,
            hard_constraints: vec![],
            soft_constraints: vec![(
                5,
                PbConstraint {
                    terms: vec![linear_term(1, 1)],
                    rel: PbRel::Ge,
                    rhs: 1,
                },
            )],
            objective: None,
        };

        assert_eq!(
            try_wbo_to_pbo(&wbo),
            Err(WboToPboError::VariableCountOverflow)
        );
    }

    #[test]
    fn test_compute_relaxation_coefficient_positive_terms() {
        // +1 x1 +1 x2 >= 2: min LHS = 0, deficit = 2
        let constraint = PbConstraint {
            terms: vec![linear_term(1, 1), linear_term(1, 2)],
            rel: PbRel::Ge,
            rhs: 2,
        };
        assert_eq!(
            try_compute_relaxation_coefficient(&constraint.terms, constraint.rhs).unwrap(),
            2
        );
    }

    #[test]
    fn test_compute_relaxation_coefficient_negative_terms() {
        // +1 x1 -1 x2 >= 0: min LHS = -1, deficit = 0 - (-1) = 1
        let constraint = PbConstraint {
            terms: vec![linear_term(1, 1), linear_term(-1, 2)],
            rel: PbRel::Ge,
            rhs: 0,
        };
        assert_eq!(
            try_compute_relaxation_coefficient(&constraint.terms, constraint.rhs).unwrap(),
            1
        );
    }

    #[test]
    fn test_compute_relaxation_coefficient_for_equality_upper_bound_direction() {
        let negated_terms =
            negate_terms(&[linear_term(1, 1), linear_term(1, 2)]).expect("terms should negate");
        assert_eq!(
            try_compute_relaxation_coefficient(&negated_terms, -1).unwrap(),
            1
        );
    }

    #[test]
    fn test_compute_relaxation_coefficient_supports_i64_max_boundary() {
        assert_eq!(
            try_compute_relaxation_coefficient(&[], i128::MAX).unwrap(),
            i128::MAX
        );
    }

    #[test]
    fn test_try_wbo_to_pbo_fails_closed_on_relaxation_coefficient_overflow() {
        let wbo = WboInstance {
            top_cost: Some(100),
            num_vars: 1,
            hard_constraints: vec![],
            soft_constraints: vec![(
                5,
                PbConstraint {
                    terms: vec![linear_term(i128::MIN, 1)],
                    rel: PbRel::Ge,
                    rhs: i128::MAX,
                },
            )],
            objective: None,
        };

        assert_eq!(
            try_wbo_to_pbo(&wbo),
            Err(WboToPboError::RelaxationCoefficientOverflow)
        );
    }

    #[test]
    fn test_try_wbo_to_pbo_fails_closed_on_soft_equality_rhs_overflow() {
        let wbo = WboInstance {
            top_cost: Some(100),
            num_vars: 1,
            hard_constraints: vec![],
            soft_constraints: vec![(
                5,
                PbConstraint {
                    terms: vec![linear_term(1, 1)],
                    rel: PbRel::Eq,
                    rhs: i128::MIN,
                },
            )],
            objective: None,
        };

        assert_eq!(
            try_wbo_to_pbo(&wbo),
            Err(WboToPboError::SoftEqualityRhsOverflow)
        );
    }

    #[test]
    fn test_try_wbo_to_pbo_fails_closed_on_soft_equality_coefficient_overflow() {
        let wbo = WboInstance {
            top_cost: Some(100),
            num_vars: 1,
            hard_constraints: vec![],
            soft_constraints: vec![(
                5,
                PbConstraint {
                    terms: vec![linear_term(i128::MIN, 1)],
                    rel: PbRel::Eq,
                    rhs: 0,
                },
            )],
            objective: None,
        };

        assert_eq!(
            try_wbo_to_pbo(&wbo),
            Err(WboToPboError::SoftEqualityCoefficientOverflow)
        );
    }
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Author: Andrew Yates <andrewyates.name@gmail.com>
//! Core types for OPB/WBO pseudo-Boolean instances.

/// A pseudo-Boolean literal: a variable with optional negation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct PbLit {
    /// 1-indexed variable number.
    pub var: u32,
    /// Whether the literal is negated (`~x`).
    pub negated: bool,
}

/// A pseudo-Boolean term: a coefficient multiplied by one or more literals.
///
/// For linear constraints, `lits` has exactly one element.
/// For non-linear constraints (NLC track), `lits` has multiple elements
/// representing a product of literals.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PbTerm {
    /// Integer coefficient (up to i128 range).
    pub coeff: i128,
    /// Literals in this term. Linear: len == 1, non-linear: len > 1.
    pub lits: Vec<PbLit>,
}

/// Relational operator in a pseudo-Boolean constraint.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[non_exhaustive]
pub enum PbRel {
    /// Greater-than-or-equal (`>=`).
    Ge,
    /// Equality (`=`).
    Eq,
}

/// A single pseudo-Boolean constraint: `sum(terms) rel rhs`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PbConstraint {
    /// Terms on the left-hand side.
    pub terms: Vec<PbTerm>,
    /// Relational operator.
    pub rel: PbRel,
    /// Right-hand side integer constant.
    pub rhs: i128,
}

/// Objective function to minimize: `min: sum(terms)`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PbObjective {
    /// Terms in the objective function.
    pub terms: Vec<PbTerm>,
}

/// A parsed OPB instance (decision or optimization).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PbInstance {
    /// Number of variables declared in the header (0 if header absent).
    pub num_vars: u32,
    /// Number of constraints declared in the header (0 if header absent).
    pub num_constraints: u32,
    /// All constraints in the instance.
    pub constraints: Vec<PbConstraint>,
    /// Optional objective function (present for optimization instances).
    pub objective: Option<PbObjective>,
}

/// Classification of a PB instance by coefficient structure.
///
/// Guides solver strategy selection: cardinality-only instances can use simpler
/// encodings, while large-coefficient instances may benefit from different
/// cutting-planes strategies.
///
/// Reference: Exact (Devriendt et al., CP 2021) uses similar classification
/// to select propagation strategies.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum InstanceClass {
    /// All coefficients are 1 (pure cardinality constraints).
    Pure,
    /// All coefficients fit in i32 (small weighted PB).
    Small,
    /// Some coefficients require i128 (large weighted PB).
    Large,
    /// Mix of cardinality (all-1) and weighted constraints.
    Mixed,
}

/// Returns whether a PB constraint is a cardinality constraint (all coefficients
/// are 1 after normalization to positive form).
///
/// Cardinality constraints are a simpler special case of PB constraints where
/// each variable contributes equally. Many PB competition instances are pure
/// cardinality, and specialized propagation can be more efficient.
#[must_use]
pub fn is_cardinality(constraint: &PbConstraint) -> bool {
    if constraint.terms.is_empty() {
        return true;
    }
    constraint
        .terms
        .iter()
        .all(|t| t.coeff == 1 || t.coeff == -1)
}

/// Classifies a PB instance by its coefficient structure.
///
/// The classification examines all constraints (and the objective if present)
/// to determine the instance type:
/// - `Pure`: every constraint is cardinality (all coefficients are +/-1)
/// - `Small`: all coefficients fit in i32 range
/// - `Large`: at least one coefficient exceeds i32 range
/// - `Mixed`: some constraints are cardinality and some are not
#[must_use]
pub fn classify_instance(instance: &PbInstance) -> InstanceClass {
    if instance.constraints.is_empty() {
        return InstanceClass::Pure;
    }

    let mut has_cardinality = false;
    let mut has_weighted = false;
    let mut has_large = false;

    for constraint in &instance.constraints {
        if is_cardinality(constraint) {
            has_cardinality = true;
        } else {
            has_weighted = true;
            // Check if any coefficient exceeds i32 range.
            for term in &constraint.terms {
                if term.coeff.unsigned_abs() > i32::MAX as u128 {
                    has_large = true;
                }
            }
        }
    }

    // Also check objective coefficients.
    if let Some(ref obj) = instance.objective {
        for term in &obj.terms {
            if term.coeff.unsigned_abs() > 1 {
                has_weighted = true;
            }
            if term.coeff.unsigned_abs() > i32::MAX as u128 {
                has_large = true;
            }
        }
    }

    if has_large {
        InstanceClass::Large
    } else if has_cardinality && has_weighted {
        InstanceClass::Mixed
    } else if has_weighted {
        InstanceClass::Small
    } else {
        InstanceClass::Pure
    }
}

/// A parsed WBO (Weighted Boolean Optimization) instance.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WboInstance {
    /// Top cost from the `soft: [<cost>] ;` header.
    ///
    /// Official WBO semantics: an assignment is a model only if every hard
    /// constraint holds AND the total cost of falsified soft constraints is
    /// STRICTLY LESS than this value; an instance whose minimum cost reaches
    /// the top cost is UNSATISFIABLE. `None` means the integer was omitted
    /// (`soft: ;`), i.e. no cost bound.
    pub top_cost: Option<i128>,
    /// Number of variables (inferred from literals if no header).
    pub num_vars: u32,
    /// Hard constraints (must be satisfied).
    pub hard_constraints: Vec<PbConstraint>,
    /// Soft constraints with their violation costs.
    pub soft_constraints: Vec<(i128, PbConstraint)>,
    /// Optional objective function.
    pub objective: Option<PbObjective>,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lit(var: u32) -> PbLit {
        PbLit {
            var,
            negated: false,
        }
    }

    fn neg(var: u32) -> PbLit {
        PbLit { var, negated: true }
    }

    fn term(coeff: i128, l: PbLit) -> PbTerm {
        PbTerm {
            coeff,
            lits: vec![l],
        }
    }

    fn ge(terms: Vec<PbTerm>, rhs: i128) -> PbConstraint {
        PbConstraint {
            terms,
            rel: PbRel::Ge,
            rhs,
        }
    }

    // --- is_cardinality tests ---

    #[test]
    fn test_is_cardinality_all_ones() {
        let c = ge(vec![term(1, lit(1)), term(1, lit(2)), term(1, lit(3))], 2);
        assert!(is_cardinality(&c));
    }

    #[test]
    fn test_is_cardinality_with_negated_coefficients() {
        let c = ge(vec![term(-1, lit(1)), term(1, lit(2))], 1);
        assert!(is_cardinality(&c));
    }

    #[test]
    fn test_is_cardinality_weighted_false() {
        let c = ge(vec![term(3, lit(1)), term(2, lit(2))], 4);
        assert!(!is_cardinality(&c));
    }

    #[test]
    fn test_is_cardinality_empty() {
        let c = ge(vec![], 0);
        assert!(is_cardinality(&c));
    }

    #[test]
    fn test_is_cardinality_mixed_coefficients() {
        let c = ge(vec![term(1, lit(1)), term(2, lit(2))], 2);
        assert!(!is_cardinality(&c));
    }

    // --- classify_instance tests ---

    #[test]
    fn test_classify_pure_cardinality() {
        let instance = PbInstance {
            num_vars: 3,
            num_constraints: 2,
            constraints: vec![
                ge(vec![term(1, lit(1)), term(1, lit(2)), term(1, lit(3))], 2),
                ge(vec![term(1, neg(1)), term(1, neg(2))], 1),
            ],
            objective: None,
        };
        assert_eq!(classify_instance(&instance), InstanceClass::Pure);
    }

    #[test]
    fn test_classify_small_weighted() {
        let instance = PbInstance {
            num_vars: 2,
            num_constraints: 1,
            constraints: vec![ge(vec![term(3, lit(1)), term(2, lit(2))], 4)],
            objective: None,
        };
        assert_eq!(classify_instance(&instance), InstanceClass::Small);
    }

    #[test]
    fn test_classify_large_coefficients() {
        let instance = PbInstance {
            num_vars: 2,
            num_constraints: 1,
            constraints: vec![ge(
                vec![term(i128::from(i32::MAX) + 1, lit(1)), term(1, lit(2))],
                1,
            )],
            objective: None,
        };
        assert_eq!(classify_instance(&instance), InstanceClass::Large);
    }

    #[test]
    fn test_classify_mixed() {
        let instance = PbInstance {
            num_vars: 3,
            num_constraints: 2,
            constraints: vec![
                ge(vec![term(1, lit(1)), term(1, lit(2))], 1),
                ge(vec![term(3, lit(2)), term(2, lit(3))], 4),
            ],
            objective: None,
        };
        assert_eq!(classify_instance(&instance), InstanceClass::Mixed);
    }

    #[test]
    fn test_classify_empty_instance() {
        let instance = PbInstance {
            num_vars: 0,
            num_constraints: 0,
            constraints: vec![],
            objective: None,
        };
        assert_eq!(classify_instance(&instance), InstanceClass::Pure);
    }

    #[test]
    fn test_classify_weighted_objective_makes_mixed() {
        let instance = PbInstance {
            num_vars: 2,
            num_constraints: 1,
            constraints: vec![ge(vec![term(1, lit(1)), term(1, lit(2))], 1)],
            objective: Some(PbObjective {
                terms: vec![term(3, lit(1)), term(2, lit(2))],
            }),
        };
        // Constraints are cardinality, but objective has weighted terms -> Mixed.
        assert_eq!(classify_instance(&instance), InstanceClass::Mixed);
    }
}

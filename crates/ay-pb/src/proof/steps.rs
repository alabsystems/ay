// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Author: Andrew Yates <andrewyates.name@gmail.com>
//! VeriPB proof-step types.

use std::fmt;

use crate::types::PbLit;

/// A 1-indexed VeriPB constraint identifier.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ConstraintId(u64);

impl ConstraintId {
    /// Creates a new 1-indexed constraint identifier.
    pub const fn new(value: u64) -> Option<Self> {
        if value == 0 {
            None
        } else {
            Some(Self(value))
        }
    }

    /// Returns the raw numeric identifier.
    pub const fn get(self) -> u64 {
        self.0
    }

    pub(crate) const fn from_raw(value: u64) -> Self {
        debug_assert!(value > 0, "constraint IDs are 1-indexed");
        Self(value)
    }
}

impl fmt::Display for ConstraintId {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{}", self.0)
    }
}

impl From<ConstraintId> for u64 {
    fn from(value: ConstraintId) -> Self {
        value.0
    }
}

/// A single VeriPB v3 proof step.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProofStep {
    /// Adds two existing constraints: `p <id1> <id2> +`.
    Addition(ConstraintId, ConstraintId),
    /// Multiplies a constraint by a positive scalar: `p <id> <k> *`.
    Multiply(ConstraintId, i128),
    /// Divides a constraint by a positive divisor with ceiling: `p <id> <d> d`.
    Divide(ConstraintId, i128),
    /// Saturates a constraint: `p <id> s`.
    Saturate(ConstraintId),
    /// Emits a checked VeriPB polynomial expression: `pol <expression>`.
    ///
    /// The expression should omit the leading `pol` and include the trailing
    /// semicolon.
    Polynomial(String),
    /// Weakens away a VARIABLE: `p <id> x<var> w`. The stored literal's
    /// polarity is informational only — VeriPB's weaken operand must be the
    /// bare variable (a negated operand is a checker parse error), and the
    /// semantics are polarity-independent.
    Weaken(ConstraintId, PbLit),
    /// Reverse unit propagation with an inline OPB-style constraint.
    ///
    /// The constraint string should already be formatted for VeriPB, including
    /// the trailing semicolon.
    Rup(String),
    /// Redundance with an inline OPB-style constraint and witness.
    ///
    /// The constraint string should omit the trailing semicolon. The witness
    /// should already be formatted for VeriPB, including its trailing semicolon.
    Red(String, String),
    /// Deletes a previously introduced constraint: `del id <id> ;`.
    Delete(ConstraintId),
    // NOTE: there is deliberately no `obju` (objective update) step. VeriPB
    // classifies `obju` as a NON-DERIVATION rule: it adds no constraint to the
    // database and therefore consumes no constraint ID. A step variant here
    // would tempt the writer to allocate an ID for it, silently shifting every
    // later ID reference (the exact desync class behind "not implied by RUP"
    // checker rejects). Reintroduce only together with ID-neutral plumbing in
    // `VeriPbWriter::log_step`.
    /// Logs an incumbent solution and adds the objective-improving constraint.
    ///
    /// The assignment should contain VeriPB literals separated by spaces, without
    /// the trailing semicolon.
    SolutionImproving(String),
}

#[cfg(test)]
mod tests {
    use super::{ConstraintId, ProofStep};
    use crate::PbLit;

    fn lit(var: u32) -> PbLit {
        PbLit {
            var,
            negated: false,
        }
    }

    #[test]
    fn test_constraint_id_new_rejects_zero() {
        assert_eq!(ConstraintId::new(0), None);
        assert_eq!(
            ConstraintId::new(7).expect("non-zero IDs are valid").get(),
            7,
        );
    }

    #[test]
    fn test_constraint_id_display_and_conversion_use_raw_value() {
        let id = ConstraintId::new(12).expect("non-zero IDs are valid");

        assert_eq!(id.to_string(), "12");
        assert_eq!(u64::from(id), 12);
    }

    #[test]
    fn test_tuple_variants_preserve_referenced_ids() {
        let left = ConstraintId::new(2).expect("non-zero IDs are valid");
        let right = ConstraintId::new(9).expect("non-zero IDs are valid");

        match ProofStep::Addition(left, right) {
            ProofStep::Addition(actual_left, actual_right) => {
                assert_eq!(actual_left, left);
                assert_eq!(actual_right, right);
            }
            _ => panic!("expected addition step"),
        }

        match ProofStep::Delete(right) {
            ProofStep::Delete(actual_id) => assert_eq!(actual_id, right),
            _ => panic!("expected delete step"),
        }
    }

    #[test]
    fn test_string_and_literal_payloads_are_preserved() {
        match ProofStep::Red(String::from("+1 x1 >= 1"), String::from("x1 -> 1 ;")) {
            ProofStep::Red(constraint, witness) => {
                assert_eq!(constraint, "+1 x1 >= 1");
                assert_eq!(witness, "x1 -> 1 ;");
            }
            _ => panic!("expected redundance step"),
        }

        match ProofStep::Weaken(
            ConstraintId::new(4).expect("non-zero IDs are valid"),
            lit(9),
        ) {
            ProofStep::Weaken(actual_id, actual_lit) => {
                assert_eq!(
                    actual_id,
                    ConstraintId::new(4).expect("non-zero IDs are valid")
                );
                assert_eq!(actual_lit, lit(9));
            }
            _ => panic!("expected weakening step"),
        }
    }
}

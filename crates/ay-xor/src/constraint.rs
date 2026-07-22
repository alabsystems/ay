// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! XOR constraint representation.

use ay_sat::{Literal, Variable};

use crate::VarId;

/// XOR constraint: x1 XOR x2 XOR ... XOR xn = rhs
///
/// Represents a parity constraint over boolean variables. The constraint is
/// satisfied when the XOR of all variable values equals `rhs`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct XorConstraint {
    /// Variables in the XOR (sorted, no signs - XOR is symmetric).
    pub vars: Vec<VarId>,
    /// Right-hand side (true = odd parity, false = even parity).
    pub rhs: bool,
}

impl XorConstraint {
    /// Create a new XOR constraint.
    ///
    /// Variables are automatically sorted and deduplicated (a XOR a = 0).
    pub fn new(mut vars: Vec<VarId>, rhs: bool) -> Self {
        // Sort variables for canonical form
        vars.sort_unstable();

        // Remove duplicates (a XOR a = 0)
        let mut deduped = Vec::with_capacity(vars.len());
        let mut i = 0;
        while i < vars.len() {
            let v = vars[i];
            let mut count = 1;
            while i + count < vars.len() && vars[i + count] == v {
                count += 1;
            }
            // Only keep if odd count (even count XORs cancel out)
            if count % 2 == 1 {
                deduped.push(v);
            }
            // Pairs cancel out, no RHS adjustment needed
            i += count;
        }

        Self { vars: deduped, rhs }
    }

    /// Number of variables in this constraint.
    pub fn len(&self) -> usize {
        self.vars.len()
    }

    /// Check if this is an empty constraint.
    pub fn is_empty(&self) -> bool {
        self.vars.is_empty()
    }

    /// Check if this constraint is trivially satisfied (0 = 0).
    pub fn is_tautology(&self) -> bool {
        self.vars.is_empty() && !self.rhs
    }

    /// Check if this constraint is a conflict (0 = 1).
    pub fn is_conflict(&self) -> bool {
        self.vars.is_empty() && self.rhs
    }

    /// Check if this is a unit constraint (single variable).
    pub fn is_unit(&self) -> bool {
        self.vars.len() == 1
    }

    /// Get the unit literal if this is a unit constraint.
    ///
    /// Returns Some(literal) where the literal's polarity reflects the required
    /// value: positive if rhs=true (variable must be 1), negative if rhs=false
    /// (variable must be 0).
    pub fn unit_lit(&self) -> Option<Literal> {
        if self.vars.len() == 1 {
            let var = Variable::new(self.vars[0]);
            // x = rhs: positive literal if rhs=true, negative if rhs=false
            if self.rhs {
                Some(Literal::positive(var))
            } else {
                Some(Literal::negative(var))
            }
        } else {
            None
        }
    }
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! QBF formula representation
//!
//! Represents quantified boolean formulas in prenex normal form:
//! Q₁x₁...Qₙxₙ. φ(x₁,...,xₙ)
//!
//! Where each Qᵢ is either ∃ (existential) or ∀ (universal),
//! and φ is a propositional formula in CNF.

use std::collections::HashSet;

use ay_sat::Literal;

/// Maximum variable domain for the dense QBF solver state.
///
/// Parsed inputs reject larger formulas. Native construction remains
/// infallible for API compatibility, but avoids allocating dense metadata and
/// is rejected fail-closed by [`crate::QbfSolver`].
pub(crate) const MAX_QBF_VARS: usize = 1 << 20;

/// Quantifier type
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Quantifier {
    /// Existential quantifier (∃)
    Exists,
    /// Universal quantifier (∀)
    Forall,
}

impl std::fmt::Display for Quantifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Exists => write!(f, "∃"),
            Self::Forall => write!(f, "∀"),
        }
    }
}

/// A quantifier block (quantifier + variables)
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QuantifierBlock {
    /// The quantifier type
    pub quantifier: Quantifier,
    /// Variables in this block (1-indexed)
    pub variables: Vec<u32>,
}

impl QuantifierBlock {
    /// Create a new quantifier block
    pub fn new(quantifier: Quantifier, variables: Vec<u32>) -> Self {
        Self {
            quantifier,
            variables,
        }
    }

    /// Create an existential block
    pub fn exists(variables: Vec<u32>) -> Self {
        Self::new(Quantifier::Exists, variables)
    }

    /// Create a universal block
    pub fn forall(variables: Vec<u32>) -> Self {
        Self::new(Quantifier::Forall, variables)
    }
}

/// A QBF formula in prenex CNF form
///
/// The quantifier prefix is a sequence of quantifier blocks,
/// followed by a CNF matrix (list of clauses).
#[derive(Debug, Clone)]
pub struct QbfFormula {
    /// Number of variables
    pub num_vars: usize,
    /// Quantifier prefix (ordered from outermost to innermost)
    pub prefix: Vec<QuantifierBlock>,
    /// CNF matrix (clauses as lists of literals)
    pub clauses: Vec<Vec<Literal>>,
    /// Quantifier level for each variable (0-indexed by var-1)
    /// Level 0 is outermost, higher levels are more inner
    var_levels: Vec<u32>,
    /// Quantifier type for each variable (0-indexed by var-1)
    var_quantifiers: Vec<Quantifier>,
}

impl QbfFormula {
    /// Create a new QBF formula.
    ///
    /// Native callers may provide a malformed prefix even though parsed
    /// QDIMACS input is validated. Prefix canonicalization is deterministic:
    /// zero and out-of-range variables are dropped, and the first valid
    /// occurrence of a repeated variable wins. Empty blocks created by that
    /// filtering are removed. Variables absent from the resulting prefix are
    /// implicitly existential.
    pub fn new(
        num_vars: usize,
        prefix: Vec<QuantifierBlock>,
        mut clauses: Vec<Vec<Literal>>,
    ) -> Self {
        // Do not let an infallible native constructor turn an untrusted count
        // into a multi-gigabyte allocation. Oversized formulas retain their
        // public metadata for diagnostics; QbfSolver rejects them as Unknown
        // before indexing any dense state.
        let dense_num_vars = if num_vars <= MAX_QBF_VARS {
            num_vars
        } else {
            0
        };
        let mut var_levels = vec![0u32; dense_num_vars];
        let mut var_quantifiers = vec![Quantifier::Exists; dense_num_vars]; // Default to existential
        let mut seen = HashSet::with_capacity(num_vars.min(prefix.len()));
        let mut canonical_prefix = Vec::with_capacity(prefix.len());

        for block in prefix {
            let mut variables = Vec::with_capacity(block.variables.len());
            for var in block.variables {
                if var > 0 && (var as usize) <= num_vars && seen.insert(var) {
                    variables.push(var);
                }
            }
            if variables.is_empty() {
                continue;
            }

            let level = canonical_prefix.len() as u32;
            for &var in &variables {
                if let (Some(var_level), Some(var_quantifier)) = (
                    var_levels.get_mut(var as usize - 1),
                    var_quantifiers.get_mut(var as usize - 1),
                ) {
                    *var_level = level;
                    *var_quantifier = block.quantifier;
                }
            }
            canonical_prefix.push(QuantifierBlock::new(block.quantifier, variables));
        }

        // Canonicalize the CNF once instead of rediscovering tautologies and
        // duplicate literals at every QDPLL node. Tautological clauses impose
        // no constraint; retaining one can force a complete quantified search
        // before either polarity becomes visibly true.
        let mut seen_literals = HashSet::new();
        clauses.retain_mut(|clause| {
            seen_literals.clear();
            let mut tautological = false;
            clause.retain(|&literal| {
                if seen_literals.contains(&literal.negated()) {
                    tautological = true;
                }
                seen_literals.insert(literal)
            });
            !tautological
        });

        Self {
            num_vars,
            prefix: canonical_prefix,
            clauses,
            var_levels,
            var_quantifiers,
        }
    }

    /// Rebuild cached prefix metadata after public-field mutation.
    pub(crate) fn canonicalized(self) -> Self {
        Self::new(self.num_vars, self.prefix, self.clauses)
    }

    /// Get the quantifier level of a variable (1-indexed)
    pub fn var_level(&self, var: u32) -> u32 {
        var.checked_sub(1)
            .and_then(|index| self.var_levels.get(index as usize))
            .copied()
            .unwrap_or(0)
    }

    /// Get the quantifier type of a variable (1-indexed)
    pub fn var_quantifier(&self, var: u32) -> Quantifier {
        var.checked_sub(1)
            .and_then(|index| self.var_quantifiers.get(index as usize))
            .copied()
            .unwrap_or(Quantifier::Exists) // Unquantified variables are existential
    }

    /// Check if a variable is existential
    pub fn is_existential(&self, var: u32) -> bool {
        self.var_quantifier(var) == Quantifier::Exists
    }

    /// Check if a variable is universal
    pub fn is_universal(&self, var: u32) -> bool {
        self.var_quantifier(var) == Quantifier::Forall
    }

    /// Get the quantifier level of a literal
    pub fn lit_level(&self, lit: Literal) -> u32 {
        self.var_level(lit.variable().id())
    }

    /// Check if a literal is existential
    pub fn lit_is_existential(&self, lit: Literal) -> bool {
        self.is_existential(lit.variable().id())
    }

    /// Check if a literal is universal
    pub fn lit_is_universal(&self, lit: Literal) -> bool {
        self.is_universal(lit.variable().id())
    }

    /// Get the maximum quantifier level of any existential literal in a clause
    pub fn max_existential_level(&self, clause: &[Literal]) -> Option<u32> {
        clause
            .iter()
            .filter(|lit| self.lit_is_existential(**lit))
            .map(|lit| self.lit_level(*lit))
            .max()
    }

    /// Apply universal reduction to a clause
    ///
    /// Removes universal literals whose level is >= the maximum existential level.
    /// These literals cannot affect satisfiability because they can always be
    /// set to satisfy the clause after all existential decisions are made.
    pub fn universal_reduce(&self, clause: &[Literal]) -> Vec<Literal> {
        // Q-resolution never reduces a tautological clause: removing only the
        // universal side of a complementary pair would turn a tautology into
        // a real constraint. Preserve it verbatim.
        let mut seen = HashSet::with_capacity(clause.len());
        for &literal in clause {
            if seen.contains(&literal.negated()) {
                return clause.to_vec();
            }
            seen.insert(literal);
        }

        let max_exist_level = self.max_existential_level(clause);

        match max_exist_level {
            Some(max_level) => {
                clause
                    .iter()
                    .filter(|lit| {
                        // Keep existential literals and universal literals with level < max_exist
                        self.lit_is_existential(**lit) || self.lit_level(**lit) < max_level
                    })
                    .copied()
                    .collect()
            }
            None => {
                // A non-tautological clause containing only universal
                // literals can be falsified by the universal player. Universal
                // reduction therefore removes every literal and exposes the
                // empty-clause contradiction.
                Vec::new()
            }
        }
    }
}

#[cfg(test)]
#[path = "formula_tests.rs"]
mod tests;

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

use std::{collections::HashSet, fmt};

use ay_sat::Literal;

/// Maximum variable domain for the dense QBF solver state.
///
/// Parsed inputs reject larger formulas. Native construction remains
/// infallible for API compatibility, but uses canonical-prefix lookup instead
/// of dense metadata and is rejected fail-closed by [`crate::QbfSolver`].
pub(crate) const MAX_QBF_VARS: usize = 1 << 20;

/// Quantifier type
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Quantifier {
    /// Existential quantifier (∃)
    Exists,
    /// Universal quantifier (∀)
    Forall,
}

impl fmt::Display for Quantifier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
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
///
/// Its semantic components are exposed read-only so the canonical prefix and
/// its derived lookup metadata cannot diverge. Use [`Self::into_parts`] and
/// [`Self::new`] to construct a modified formula.
#[derive(Clone)]
pub struct QbfFormula {
    num_vars: usize,
    prefix: Vec<QuantifierBlock>,
    clauses: Vec<Vec<Literal>>,
    /// Dense quantifier levels, indexed by `var - 1`.
    ///
    /// Empty for an oversized native formula. Level zero is outermost.
    var_levels: Vec<u32>,
    /// Dense quantifiers, indexed by `var - 1` and empty when oversized.
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
    /// implicitly existential at the outermost level.
    ///
    /// Matrix normalization retains the first occurrence of each literal and
    /// removes tautological clauses. Empty clauses are preserved. Directly
    /// constructed matrices may still contain variables outside
    /// `1..=num_vars`; [`crate::QbfSolver`] rejects those formulas fail-closed.
    pub fn new(
        num_vars: usize,
        prefix: Vec<QuantifierBlock>,
        mut clauses: Vec<Vec<Literal>>,
    ) -> Self {
        // Do not let an infallible native constructor turn an untrusted count
        // into a multi-gigabyte allocation. Oversized formulas retain their
        // semantic prefix for read-only lookup and diagnostics; QbfSolver
        // rejects them as Unknown before indexing any dense state.
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

    /// Return the size of the 1-indexed variable domain.
    pub fn num_vars(&self) -> usize {
        self.num_vars
    }

    /// Return the canonical quantifier prefix, outermost block first.
    pub fn prefix(&self) -> &[QuantifierBlock] {
        &self.prefix
    }

    /// Return the normalized CNF matrix.
    pub fn clauses(&self) -> &[Vec<Literal>] {
        &self.clauses
    }

    /// Consume the formula and return its normalized semantic components.
    ///
    /// The returned vectors reuse the formula's allocations. Derived prefix
    /// metadata is deliberately omitted and will be rebuilt if the parts are
    /// passed to [`Self::new`] again.
    pub fn into_parts(self) -> (usize, Vec<QuantifierBlock>, Vec<Vec<Literal>>) {
        (self.num_vars, self.prefix, self.clauses)
    }

    /// Replace the matrix with its universally reduced equivalent.
    ///
    /// This mutation is intentionally restricted to the crate's experimental
    /// QCDCL path. Removing literals preserves matrix normalization and cannot
    /// invalidate prefix metadata.
    pub(crate) fn universally_reduce_matrix(&mut self) {
        let reduced = self
            .clauses
            .iter()
            .map(|clause| self.universal_reduce(clause))
            .collect();
        self.clauses = reduced;
    }

    /// Resolve a variable through dense metadata or the canonical prefix.
    fn variable_info(&self, var: u32) -> (u32, Quantifier) {
        let Some(index) = var
            .checked_sub(1)
            .map(|index| index as usize)
            .filter(|&index| index < self.num_vars)
        else {
            return (0, Quantifier::Exists);
        };

        if self.num_vars <= MAX_QBF_VARS {
            return (self.var_levels[index], self.var_quantifiers[index]);
        }

        self.prefix
            .iter()
            .enumerate()
            .find(|(_, block)| block.variables.contains(&var))
            .map_or((0, Quantifier::Exists), |(level, block)| {
                (level as u32, block.quantifier)
            })
    }

    /// Return the quantifier level of a 1-indexed variable.
    ///
    /// Variables absent from the prefix, as well as variables outside the
    /// formula's domain, are treated as outermost and return level zero.
    pub fn var_level(&self, var: u32) -> u32 {
        self.variable_info(var).0
    }

    /// Return the quantifier of a 1-indexed variable.
    ///
    /// Variables absent from the prefix, as well as variables outside the
    /// formula's domain, are treated as existential.
    pub fn var_quantifier(&self, var: u32) -> Quantifier {
        self.variable_info(var).1
    }

    /// Check whether a variable is existential.
    pub fn is_existential(&self, var: u32) -> bool {
        self.var_quantifier(var) == Quantifier::Exists
    }

    /// Check whether a variable is universal.
    pub fn is_universal(&self, var: u32) -> bool {
        self.var_quantifier(var) == Quantifier::Forall
    }

    /// Return the quantifier level of a literal.
    pub fn lit_level(&self, lit: Literal) -> u32 {
        self.var_level(lit.variable().id())
    }

    /// Check whether a literal is existential.
    pub fn lit_is_existential(&self, lit: Literal) -> bool {
        self.is_existential(lit.variable().id())
    }

    /// Check whether a literal is universal.
    pub fn lit_is_universal(&self, lit: Literal) -> bool {
        self.is_universal(lit.variable().id())
    }

    /// Return the maximum quantifier level of an existential clause literal.
    pub fn max_existential_level(&self, clause: &[Literal]) -> Option<u32> {
        clause
            .iter()
            .filter(|lit| self.lit_is_existential(**lit))
            .map(|lit| self.lit_level(*lit))
            .max()
    }

    /// Apply universal reduction to a clause
    ///
    /// Removes universal literals whose level is at least the maximum
    /// existential level. The universal player chooses those variables after
    /// the clause's preceding existential variables and can falsify their
    /// literals, so the existential player cannot rely on them.
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

impl fmt::Debug for QbfFormula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("QbfFormula")
            .field("num_vars", &self.num_vars)
            .field("prefix", &self.prefix)
            .field("clauses", &self.clauses)
            .finish_non_exhaustive()
    }
}

#[cfg(test)]
#[path = "formula_tests.rs"]
mod tests;

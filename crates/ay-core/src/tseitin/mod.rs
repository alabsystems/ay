// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tseitin transformation: convert Boolean formulas to CNF
//!
//! The Tseitin transformation converts an arbitrary Boolean formula into
//! Conjunctive Normal Form (CNF) by introducing fresh variables for subterms.
//! The resulting CNF is equisatisfiable with the original formula.
//!
//! # Example
//!
//! For a formula `(a ∧ b) ∨ c`:
//! 1. Introduce variable `t1` for `(a ∧ b)`
//! 2. Add clauses: `t1 → a`, `t1 → b`, `(a ∧ b) → t1`
//! 3. Introduce variable `t2` for `t1 ∨ c`
//! 4. Add clauses: `¬t1 → t2`, `¬c → t2`, `t2 → (t1 ∨ c)`
//! 5. Assert `t2`
//!
//! The output uses DIMACS-style signed integer literals where:
//! - Positive integer N means variable N is true
//! - Negative integer -N means variable N is false

mod encode;
mod transform;
mod types;

pub use types::*;

use crate::proof::AletheRule;
use crate::term::{TermId, TermStore};
use std::collections::BTreeMap;

/// Red zone size for `stacker::maybe_grow` in Tseitin encoding.
/// When remaining stack space falls below this, stacker allocates a new segment.
const TSEITIN_STACK_RED_ZONE: usize = if cfg!(debug_assertions) {
    128 * 1024
} else {
    32 * 1024
};

/// Stack segment size allocated by stacker for Tseitin recursion.
const TSEITIN_STACK_SIZE: usize = 2 * 1024 * 1024;

/// Tseitin transformation context
pub struct Tseitin<'a> {
    /// The term store
    terms: &'a TermStore,
    /// Mapping from term IDs to CNF variables
    term_to_var: BTreeMap<TermId, u32>,
    /// Mapping from CNF variables to term IDs
    var_to_term: BTreeMap<u32, TermId>,
    /// Generated clauses
    clauses: Vec<CnfClause>,
    /// Next variable index (1-indexed, DIMACS style)
    next_var: u32,
    /// Cache for polarity-aware encoding
    encoded: BTreeMap<(TermId, bool), CnfLit>,
    /// Index of clauses that have been extracted (for incremental use)
    clauses_extracted: usize,
    /// Proof annotations parallel to `clauses`. Present only when proof
    /// tracking is enabled (`:produce-proofs true`). Each entry corresponds
    /// to the clause at the same index.
    proof_annotations: Option<Vec<Option<ClausificationProof>>>,
}

impl<'a> Tseitin<'a> {
    /// Create a new Tseitin transformation context
    pub fn new(terms: &'a TermStore) -> Self {
        Tseitin {
            terms,
            term_to_var: BTreeMap::new(),
            var_to_term: BTreeMap::new(),
            clauses: Vec::new(),
            next_var: 1, // DIMACS variables are 1-indexed
            encoded: BTreeMap::new(),
            clauses_extracted: 0,
            proof_annotations: None,
        }
    }

    /// Create a new Tseitin context with proof tracking enabled.
    ///
    /// When enabled, each generated clause is annotated with its justifying
    /// Alethe tautology rule. Use [`TseitinResult::proof_annotations`] to
    /// retrieve annotations after transformation.
    pub fn new_with_proofs(terms: &'a TermStore) -> Self {
        Tseitin {
            terms,
            term_to_var: BTreeMap::new(),
            var_to_term: BTreeMap::new(),
            clauses: Vec::new(),
            next_var: 1,
            encoded: BTreeMap::new(),
            clauses_extracted: 0,
            proof_annotations: Some(Vec::new()),
        }
    }

    /// Create a Tseitin context from saved state
    ///
    /// This allows continuing from a previous transformation session,
    /// preserving term-to-variable mappings for incremental solving.
    pub fn from_state(terms: &'a TermStore, state: TseitinState) -> Self {
        Tseitin {
            terms,
            term_to_var: state.term_to_var,
            var_to_term: state.var_to_term,
            clauses: Vec::new(),
            next_var: state.next_var,
            encoded: state.encoded,
            clauses_extracted: 0,
            proof_annotations: None,
        }
    }

    /// Create a Tseitin context from saved state with proof tracking enabled.
    pub fn from_state_with_proofs(terms: &'a TermStore, state: TseitinState) -> Self {
        Tseitin {
            terms,
            term_to_var: state.term_to_var,
            var_to_term: state.var_to_term,
            clauses: Vec::new(),
            next_var: state.next_var,
            encoded: state.encoded,
            clauses_extracted: 0,
            proof_annotations: Some(Vec::new()),
        }
    }

    /// Save the current state for later restoration
    ///
    /// This extracts the term-to-variable mappings and variable counter
    /// so that a new Tseitin instance can be created later that continues
    /// from this point.
    pub fn save_state(&self) -> TseitinState {
        TseitinState {
            term_to_var: self.term_to_var.clone(),
            var_to_term: self.var_to_term.clone(),
            next_var: self.next_var,
            encoded: self.encoded.clone(),
        }
    }

    /// Take ownership of state (more efficient than clone)
    pub fn into_state(self) -> TseitinState {
        TseitinState {
            term_to_var: self.term_to_var,
            var_to_term: self.var_to_term,
            next_var: self.next_var,
            encoded: self.encoded,
        }
    }

    /// Allocate a fresh CNF variable
    fn fresh_var(&mut self) -> u32 {
        let var = self.next_var;
        self.next_var += 1;
        var
    }

    /// Get or create a CNF variable for a term
    fn get_var(&mut self, term_id: TermId) -> u32 {
        if let Some(&var) = self.term_to_var.get(&term_id) {
            return var;
        }
        let var = self.fresh_var();
        self.term_to_var.insert(term_id, var);
        self.var_to_term.insert(var, term_id);
        var
    }

    /// Get a literal for a term (positive or negative based on value)
    fn get_literal(&mut self, term_id: TermId, positive: bool) -> CnfLit {
        let var = self.get_var(term_id) as i32;
        if positive {
            var
        } else {
            -var
        }
    }

    /// Negate a literal
    fn negate(lit: CnfLit) -> CnfLit {
        -lit
    }

    /// Add a clause (no proof annotation).
    fn add_clause(&mut self, clause: CnfClause) {
        if !clause.is_empty() {
            if let Some(ref mut proofs) = self.proof_annotations {
                proofs.push(None);
            }
            self.clauses.push(clause);
        }
    }

    /// Add a clause with a proof annotation recording which Alethe tautology
    /// rule justifies it. The annotation is only recorded when proof tracking
    /// is enabled; otherwise this is equivalent to `add_clause`.
    fn add_clause_with_proof(&mut self, clause: CnfClause, rule: AletheRule, source: TermId) {
        if !clause.is_empty() {
            if let Some(ref mut proofs) = self.proof_annotations {
                proofs.push(Some(ClausificationProof {
                    rule,
                    source_term: source,
                }));
            }
            self.clauses.push(clause);
        }
    }

    /// Encode a term to CNF
    ///
    /// Returns a literal representing the term.
    /// The `positive` parameter indicates the polarity context:
    /// - true: the term appears positively (we need it to be true)
    /// - false: the term appears negatively (we need it to be false)
    ///
    /// Uses `stacker::maybe_grow` for stack safety on deeply nested terms (#4602).
    #[must_use = "Tseitin encoding returns a literal that must be used"]
    pub fn encode(&mut self, term_id: TermId, positive: bool) -> CnfLit {
        stacker::maybe_grow(TSEITIN_STACK_RED_ZONE, TSEITIN_STACK_SIZE, || {
            // Check cache
            if let Some(&lit) = self.encoded.get(&(term_id, positive)) {
                return lit;
            }

            let result = self.encode_inner(term_id, positive);

            // Cache the result
            self.encoded.insert((term_id, positive), result);

            result
        })
    }
}

#[cfg(test)]
mod tests;

#[cfg(kani)]
mod kani_proofs;

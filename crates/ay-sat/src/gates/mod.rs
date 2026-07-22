// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Gate Extraction for SAT solving
//!
//! Recognizes Boolean gate patterns in CNF clauses:
//! - AND gates: y ↔ (x1 ∧ x2 ∧ ... ∧ xn)
//! - XOR gates: y ↔ (x1 ⊕ x2 ⊕ ... ⊕ xk) for k up to 5
//! - ITE gates: y ↔ ITE(c, t, e)
//! - Equivalences: y ↔ x
//!
//! Gate extraction enables more efficient variable elimination by restricting
//! resolutions to only those between gate and non-gate clauses.
//!
//! Reference: Eén & Biere, "Effective Preprocessing in SAT through Variable
//! and Clause Elimination", SAT 2005.

mod and;
mod ite;
mod xor;

#[cfg(test)]
mod tests;

use crate::clause_arena::ClauseArena;
use crate::kitten::Kitten;
use crate::lit_marks::LitMarks;
use crate::literal::{Literal, Variable};

/// Bit parity of an unsigned integer. Returns true if popcount is odd.
/// CaDiCaL reference: `util.hpp:67-75`.
#[inline]
fn bit_parity(a: u32) -> bool {
    (a.count_ones() & 1) != 0
}

#[inline]
fn sorted_lit_pair(a: Literal, b: Literal) -> [Literal; 2] {
    let mut pair = [a, b];
    if pair[0].index() > pair[1].index() {
        pair.swap(0, 1);
    }
    debug_assert!(
        pair[0].index() <= pair[1].index(),
        "BUG: literal pair canonicalization must produce sorted order"
    );
    pair
}

/// Types of gates that can be recognized
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum GateType {
    /// AND gate: y = x1 ∧ x2 ∧ ... ∧ xn
    And,
    /// XOR gate: y = x1 ⊕ x2 ⊕ ... ⊕ xk (up to arity 5)
    Xor,
    /// If-then-else: y = ITE(c, t, e) = (c ∧ t) ∨ (¬c ∧ e)
    Ite,
    /// Equivalence: y ↔ x
    Equiv,
}

/// A recognized gate structure
#[derive(Debug, Clone)]
pub(crate) struct Gate {
    /// The output variable (pivot)
    pub output: Variable,
    /// Type of gate
    pub gate_type: GateType,
    /// Input literals for the gate
    pub inputs: Vec<Literal>,
    /// Indices of clauses that form the gate definition
    pub defining_clauses: Vec<usize>,
    /// True for XNOR gates (even count of negated inputs). See #6997, #7137.
    pub negated_output: bool,
}

/// BVE-only extraction outcomes.
///
/// Structural gates and semantic definition cores are both reduction
/// opportunities for BVE, but only the latter can directly force a unit.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum BveExtraction {
    /// Restrict resolution to the defining clauses of a functional dependency.
    RestrictResolution {
        defining_clauses: Vec<usize>,
        /// Resolve gate×gate pairs in addition to the usual cross pairs.
        /// CaDiCaL enables this for kitten-based semantic definitions via
        /// `definition_unit` / `resolve_gates` (elim.cpp:465,501).
        resolve_gate_pairs: bool,
    },
    /// One polarity alone is inconsistent after removing the pivot literal.
    FailedLiteral { unit: Literal },
}

/// Statistics for gate extraction
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct GateStats {
    /// Number of AND gates found
    pub and_gates: u64,
    /// Number of XOR gates found
    pub xor_gates: u64,
    /// Number of ITE gates found
    pub ite_gates: u64,
    /// Number of equivalences found
    pub equivalences: u64,
    /// Total gate extraction calls
    pub extraction_calls: u64,
}

impl GateStats {
    /// Total gates found
    pub fn total_gates(&self) -> u64 {
        self.and_gates + self.xor_gates + self.ite_gates + self.equivalences
    }
}

/// Gate extraction engine
pub(crate) struct GateExtractor {
    /// Marked literals to unmark later
    marked_lits: Vec<Literal>,
    /// Statistics
    stats: GateStats,
}

impl GateExtractor {
    /// Create a new gate extractor for n variables
    pub(crate) fn new(_num_vars: usize) -> Self {
        Self {
            marked_lits: Vec::new(),
            stats: GateStats::default(),
        }
    }

    /// Ensure internal buffers can handle `num_vars` variables.
    pub(crate) fn ensure_num_vars(&mut self, _num_vars: usize) {}

    /// Get statistics
    pub(crate) fn stats(&self) -> &GateStats {
        &self.stats
    }

    /// Mark a literal
    fn mark(&mut self, marks: &mut LitMarks, lit: Literal) {
        marks.mark(lit);
        self.marked_lits.push(lit);
    }

    /// Get mark for a variable
    fn get_mark(marks: &LitMarks, var: Variable) -> i8 {
        marks.get(var)
    }

    /// Unmark all marked literals
    fn unmark_all(&mut self, marks: &mut LitMarks) {
        for &lit in &self.marked_lits {
            marks.clear(lit);
        }
        self.marked_lits.clear();
    }

    /// No-ITE gate extraction with shared marks.
    ///
    /// `include_xor: false` skips the per-pivot XOR search — used by the
    /// congruence path, where the clause-driven group pass
    /// (`extract_xor_groups_clause_driven`) owns XOR extraction.
    pub(crate) fn find_gate_for_congruence_no_ite_with_marks(
        &mut self,
        pivot: Variable,
        clauses: &ClauseArena,
        pos_occs: &[usize],
        neg_occs: &[usize],
        include_xor: bool,
        marks: &mut LitMarks,
    ) -> Option<Gate> {
        self.find_gate_db_internal(
            pivot,
            clauses,
            pos_occs,
            neg_occs,
            &[],
            false,
            include_xor,
            &[],
            marks,
        )
    }

    /// Congruence gate extraction including ITE gates.
    ///
    /// `ternary_count` is the per-literal ternary-clause occurrence count
    /// (Kissat `largecount`), indexed by literal index. When non-empty it
    /// drives the ITE `twice` both-polarity pre-filter so candidate generation
    /// stays cheap on large formulas. An empty slice disables the filter.
    pub(crate) fn find_gate_for_congruence_with_marks(
        &mut self,
        pivot: Variable,
        clauses: &ClauseArena,
        pos_occs: &[usize],
        neg_occs: &[usize],
        include_xor: bool,
        ternary_count: &[u32],
        marks: &mut LitMarks,
    ) -> Option<Gate> {
        self.find_gate_db_internal(
            pivot,
            clauses,
            pos_occs,
            neg_occs,
            &[],
            true,
            include_xor,
            ternary_count,
            marks,
        )
    }

    /// Gate extraction with literal value awareness for effective binary detection.
    ///
    /// `vals` is indexed by literal index: 1 = true, -1 = false, 0 = unassigned.
    /// Falsified literals are skipped when scanning clauses, enabling detection of
    /// gates whose side-clauses are only "effectively binary" after prior propagation.
    /// This is critical for cascading gate discovery during progressive BVE (CaDiCaL).
    #[cfg(test)]
    pub(crate) fn find_gate_for_bve_with_vals(
        &mut self,
        pivot: Variable,
        clauses: &ClauseArena,
        pos_occs: &[usize],
        neg_occs: &[usize],
        vals: &[i8],
    ) -> Option<Gate> {
        let mut max_var = 0usize;
        for &ci in pos_occs.iter().chain(neg_occs.iter()) {
            if ci >= clauses.len() || clauses.is_empty_clause(ci) {
                continue;
            }
            for &lit in clauses.literals(ci) {
                max_var = max_var.max(lit.variable().index().saturating_add(1));
            }
        }
        let mut marks = LitMarks::new(max_var.max(1));
        self.find_gate_for_bve_with_vals_and_marks(
            pivot, clauses, pos_occs, neg_occs, vals, &mut marks,
        )
    }

    pub(crate) fn find_gate_for_bve_with_vals_and_marks(
        &mut self,
        pivot: Variable,
        clauses: &ClauseArena,
        pos_occs: &[usize],
        neg_occs: &[usize],
        vals: &[i8],
        marks: &mut LitMarks,
    ) -> Option<Gate> {
        self.find_gate_db_internal(
            pivot,
            clauses,
            pos_occs,
            neg_occs,
            vals,
            false,
            true,
            &[],
            marks,
        )
    }

    /// Schedule-only gate detection.
    ///
    /// Unlike the main BVE structural path, this includes ITE gates so the
    /// elimination scheduler can discount variables whose gate×gate pairs are
    /// known to collapse during restricted resolution.
    pub(crate) fn find_gate_for_schedule_with_vals_and_marks(
        &mut self,
        pivot: Variable,
        clauses: &ClauseArena,
        pos_occs: &[usize],
        neg_occs: &[usize],
        vals: &[i8],
        marks: &mut LitMarks,
    ) -> Option<Gate> {
        self.find_gate_db_internal(
            pivot,
            clauses,
            pos_occs,
            neg_occs,
            vals,
            true,
            true,
            &[],
            marks,
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn find_extraction_for_bve_with_marks(
        &mut self,
        kitten: &mut Kitten,
        pivot: Variable,
        clauses: &ClauseArena,
        pos_occs: &[usize],
        neg_occs: &[usize],
        vals: &[i8],
        marks: &mut LitMarks,
    ) -> Option<BveExtraction> {
        if let Some(gate) = self
            .find_gate_for_bve_with_vals_and_marks(pivot, clauses, pos_occs, neg_occs, vals, marks)
        {
            return Some(BveExtraction::RestrictResolution {
                defining_clauses: gate.defining_clauses,
                resolve_gate_pairs: false,
            });
        }
        self.find_definition_for_bve(kitten, pivot, clauses, pos_occs, neg_occs, vals)
    }

    #[allow(clippy::too_many_arguments)]
    fn find_gate_db_internal(
        &mut self,
        pivot: Variable,
        clauses: &ClauseArena,
        pos_occs: &[usize],
        neg_occs: &[usize],
        vals: &[i8],
        include_ite: bool,
        include_xor: bool,
        ternary_count: &[u32],
        marks: &mut LitMarks,
    ) -> Option<Gate> {
        self.stats.extraction_calls += 1;

        if let Some(gate) = self.find_equivalence_db(pivot, clauses, pos_occs, neg_occs, marks) {
            self.stats.equivalences += 1;
            return Some(gate);
        }

        if let Some(gate) =
            self.find_and_gate_db_vals(pivot, clauses, pos_occs, neg_occs, vals, marks)
        {
            self.stats.and_gates += 1;
            return Some(gate);
        }

        if include_xor {
            if let Some(gate) = self.find_xor_gate_db(pivot, clauses, pos_occs, neg_occs) {
                self.stats.xor_gates += 1;
                return Some(gate);
            }
        }

        if include_ite {
            if let Some(gate) =
                self.find_ite_gate_db(pivot, clauses, pos_occs, neg_occs, ternary_count)
            {
                self.stats.ite_gates += 1;
                return Some(gate);
            }
        }

        None
    }

    fn find_definition_for_bve(
        &mut self,
        kitten: &mut Kitten,
        pivot: Variable,
        clauses: &ClauseArena,
        pos_occs: &[usize],
        neg_occs: &[usize],
        vals: &[i8],
    ) -> Option<BveExtraction> {
        const DEFINITION_KITTEN_TICKS_BASE: u64 = 1_000;
        const DEFINITION_KITTEN_TICKS_PER_CLAUSE: u64 = 100;

        kitten.clear();
        let pivot_pos = Literal::positive(pivot);
        let pivot_neg = Literal::negative(pivot);

        let mut exported_clause_indices = Vec::with_capacity(pos_occs.len() + neg_occs.len());
        let mut exported_clause_sides = Vec::with_capacity(pos_occs.len() + neg_occs.len());

        for &(except, occs, side) in &[(pivot_pos, pos_occs, 1u8), (pivot_neg, neg_occs, 2u8)] {
            for &clause_idx in occs {
                if clause_idx >= clauses.len() || clauses.is_empty_clause(clause_idx) {
                    continue;
                }
                let clause_lits = clauses.literals(clause_idx);
                if clause_lits.iter().all(|&lit| lit == except) {
                    continue;
                }
                if clause_lits
                    .iter()
                    .any(|&lit| lit != except && vals.get(lit.index()).copied().unwrap_or(0) > 0)
                {
                    continue;
                }

                let export_id = exported_clause_indices.len() as u32;
                let ext_lits: Vec<u32> = clause_lits.iter().map(|lit| lit.raw()).collect();
                kitten.add_clause_with_id(export_id, &ext_lits, except.raw());
                exported_clause_indices.push(clause_idx);
                exported_clause_sides.push(side);
            }
        }

        if exported_clause_indices.is_empty() {
            return None;
        }

        kitten.seal_original();
        kitten.set_ticks_limit(
            DEFINITION_KITTEN_TICKS_BASE
                + DEFINITION_KITTEN_TICKS_PER_CLAUSE * exported_clause_indices.len() as u64,
        );
        if kitten.solve() != 20 {
            return None;
        }

        let core_ids = kitten.compute_clausal_core();
        if core_ids.is_empty() {
            return None;
        }

        let mut defining_clauses = Vec::with_capacity(core_ids.len());
        let mut side_mask = 0u8;
        for core_id in core_ids {
            let idx = core_id as usize;
            if idx >= exported_clause_indices.len() {
                continue;
            }
            defining_clauses.push(exported_clause_indices[idx]);
            side_mask |= exported_clause_sides[idx];
        }
        defining_clauses.sort_unstable();
        defining_clauses.dedup();

        match side_mask {
            1 => Some(BveExtraction::FailedLiteral { unit: pivot_pos }),
            2 => Some(BveExtraction::FailedLiteral { unit: pivot_neg }),
            // CaDiCaL definition extraction sets `definition_unit` when a
            // kitten core spans both polarities. That disables the same-gate
            // skip in elim.cpp:501, so gate×gate pairs are resolved in
            // addition to the normal gate×non-gate pairs.
            //
            // Structural gates keep `resolve_gate_pairs = false` because
            // their gate clauses resolve tautologically. Semantic definitions
            // can require those resolvents for soundness.
            3 => Some(BveExtraction::RestrictResolution {
                defining_clauses,
                resolve_gate_pairs: true,
            }),
            _ => None,
        }
    }

    fn find_equivalence_db(
        &mut self,
        pivot: Variable,
        clauses: &ClauseArena,
        pos_occs: &[usize],
        neg_occs: &[usize],
        marks: &mut LitMarks,
    ) -> Option<Gate> {
        let pivot_pos = Literal::positive(pivot);
        let pivot_neg = Literal::negative(pivot);

        for &clause_idx in pos_occs {
            if clause_idx >= clauses.len() || clauses.is_empty_clause(clause_idx) {
                continue;
            }
            let clause = clauses.literals(clause_idx);
            if let Some(other) = Self::get_binary_other(clause, pivot_pos) {
                self.mark(marks, other);
            }
        }

        let mut result = None;
        for &clause_idx in neg_occs {
            if clause_idx >= clauses.len() || clauses.is_empty_clause(clause_idx) {
                continue;
            }
            let clause = clauses.literals(clause_idx);
            if let Some(other) = Self::get_binary_other(clause, pivot_neg) {
                let neg_other = other.negated();
                if Self::get_mark(marks, neg_other.variable()) != 0 {
                    let mark = Self::get_mark(marks, neg_other.variable());
                    let expected = neg_other.sign_i8();
                    if mark == expected {
                        let mut pos_clause_idx = None;
                        for &ci in pos_occs {
                            if ci >= clauses.len() || clauses.is_empty_clause(ci) {
                                continue;
                            }
                            let c = clauses.literals(ci);
                            if let Some(o) = Self::get_binary_other(c, pivot_pos) {
                                if o == neg_other {
                                    pos_clause_idx = Some(ci);
                                    break;
                                }
                            }
                        }

                        if let Some(pci) = pos_clause_idx {
                            let gate = Gate {
                                output: pivot,
                                gate_type: GateType::Equiv,
                                inputs: vec![other],
                                defining_clauses: vec![pci, clause_idx],
                                negated_output: false,
                            };
                            debug_assert_eq!(
                                gate.inputs.len(),
                                1,
                                "BUG: Equiv gate must have exactly 1 input"
                            );
                            result = Some(gate);
                            break;
                        }
                    }
                }
            }
        }

        self.unmark_all(marks);
        result
    }

    /// Get the other literal in a syntactic binary clause, or `None` if not binary.
    fn get_binary_other(clause: &[Literal], exclude: Literal) -> Option<Literal> {
        match clause {
            [a, b] if *a == exclude => Some(*b),
            [a, b] if *b == exclude => Some(*a),
            _ => None,
        }
    }

    /// Get the "effective other" literal in a clause that is binary after filtering
    /// falsified literals. If `vals` is empty, falls back to syntactic check.
    fn get_effective_binary_other(
        clause: &[Literal],
        exclude: Literal,
        vals: &[i8],
    ) -> Option<Literal> {
        if vals.is_empty() {
            return Self::get_binary_other(clause, exclude);
        }
        let mut other = None;
        for &lit in clause {
            if lit == exclude {
                continue;
            }
            // Skip falsified literals
            if lit.index() < vals.len() && vals[lit.index()] < 0 {
                continue;
            }
            // If satisfied, clause is true — not useful
            if lit.index() < vals.len() && vals[lit.index()] > 0 {
                return None;
            }
            if other.is_some() {
                return None; // More than one remaining → not binary
            }
            other = Some(lit);
        }
        other
    }

    /// Get the other two literals in a ternary clause, or `None` if not ternary/missing.
    fn get_ternary_others(clause: &[Literal], exclude: Literal) -> Option<(Literal, Literal)> {
        match clause {
            [a, b, c] if *a == exclude => Some((*b, *c)),
            [a, b, c] if *b == exclude => Some((*a, *c)),
            [a, b, c] if *c == exclude => Some((*a, *b)),
            _ => None,
        }
    }
}

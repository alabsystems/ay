// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! AND gate detection for BVE and congruence.
//!
//! AND gate y = AND(x1, ..., xn) is encoded as:
//!   Binary side-clauses: (~y | x1), (~y | x2), ..., (~y | xn)
//!   Long clause: (y | ~x1 | ~x2 | ... | ~xn)

use super::{Gate, GateExtractor, GateType};
use crate::clause_arena::ClauseArena;
use crate::lit_marks::LitMarks;
use crate::literal::{Literal, Variable};

impl GateExtractor {
    /// AND gate detection with effective binary support (CaDiCaL approach).
    ///
    /// `vals` enables "effective binary" detection: clauses with falsified
    /// literals are treated as shorter. This is critical for cascading gate
    /// discovery during progressive BVE.
    pub(super) fn find_and_gate_db_vals(
        &mut self,
        pivot: Variable,
        clauses: &ClauseArena,
        pos_occs: &[usize],
        neg_occs: &[usize],
        vals: &[i8],
        marks: &mut LitMarks,
    ) -> Option<Gate> {
        // Try positive output: base clause contains +pivot, side binaries contain -pivot.
        if let Some(gate) =
            self.find_and_gate_oriented(pivot, clauses, pos_occs, neg_occs, vals, marks, false)
        {
            return Some(gate);
        }
        // Try negative output: base clause contains -pivot, side binaries contain +pivot.
        // CaDiCaL congruence.cpp:extract_and_gates_with_base_clause tries each literal
        // in the clause as LHS, including negative literals. Without this second try,
        // AY misses all AND gates where the output variable appears negatively in the
        // base clause (e.g., ¬a = AND(x1, x2) encoded as (¬a ∨ ¬x1 ∨ ¬x2) with
        // side clauses (a ∨ x1), (a ∨ x2)). (#7423)
        self.find_and_gate_oriented(pivot, clauses, neg_occs, pos_occs, vals, marks, true)
    }

    /// AND gate extraction for a single polarity orientation.
    ///
    /// `base_occs`: clauses containing the output literal (long base clauses).
    /// `side_occs`: clauses containing the negated output (binary side clauses).
    /// `negated_output`: true when the output literal is the negative polarity of `pivot`.
    #[allow(clippy::too_many_arguments)]
    fn find_and_gate_oriented(
        &mut self,
        pivot: Variable,
        clauses: &ClauseArena,
        base_occs: &[usize],
        side_occs: &[usize],
        vals: &[i8],
        marks: &mut LitMarks,
        negated_output: bool,
    ) -> Option<Gate> {
        let output_lit = if negated_output {
            Literal::negative(pivot)
        } else {
            Literal::positive(pivot)
        };
        let neg_output_lit = output_lit.negated();

        // Phase 1: Scan binary side-clauses (neg_output | xi).
        // With vals, clauses that are "effectively binary" (longer but with
        // falsified literals) are also recognized.
        let mut binary_clause_indices = Vec::new();
        for &clause_idx in side_occs {
            if clause_idx >= clauses.len() || clauses.is_empty_clause(clause_idx) {
                continue;
            }
            let clause = clauses.literals(clause_idx);
            if let Some(other) = Self::get_effective_binary_other(clause, neg_output_lit, vals) {
                self.mark(marks, other);
                binary_clause_indices.push(clause_idx);
            }
        }

        if binary_clause_indices.is_empty() {
            self.unmark_all(marks);
            return None;
        }

        // Phase 2: Scan long clauses (output | ~x1 | ~x2 | ... | ~xn).
        //
        // Soundness fix (#8477): skip root-false literals in the base clause
        // ONLY when a corresponding side clause exists (i.e., the negation of
        // the root-false literal is marked). CaDiCaL's `find_and_gate`
        // (gates.cpp:352-354) unconditionally skips root-false literals here,
        // but CaDiCaL also runs `elim_propagate` during `mark_binary_literals`
        // which keeps val() and occ lists synchronized. AY does not run
        // elim_propagate during BVE (#8356), so vals[] can contain
        // assignments that were NOT present when occ lists were built or when
        // side clauses were scanned.
        //
        // Without elim_propagate, a root-false literal in the base clause may
        // lack a corresponding side clause (because the side clause is longer
        // than binary at the time of Phase 1 scanning, or was not present).
        // Unconditionally skipping such a literal reduces the gate arity,
        // producing a gate where not all base-clause constraints are captured
        // by side clauses. This makes gate-restricted BVE skip non-gate x
        // non-gate resolvents that were needed for equisatisfiability.
        //
        // Fix: only skip a root-false literal if its negation is already
        // marked (meaning a side clause for that input exists). This is sound
        // even without elim_propagate: the skipped literal is root-false AND
        // has a side clause that constrains the output, so the gate definition
        // is complete.
        let mut result = None;
        for &clause_idx in base_occs {
            if clause_idx >= clauses.len() {
                continue;
            }
            if clauses.is_empty_clause(clause_idx) {
                continue;
            }
            let clause = clauses.literals(clause_idx);

            let mut all_match = true;
            let mut inputs = Vec::new();
            let mut arity = 0usize;
            let mut satisfied = false;

            for &lit in clause {
                if lit == output_lit {
                    continue;
                }
                // Skip falsified literals ONLY when a corresponding side clause
                // exists (negation is marked). This ensures the gate captures
                // all constraints from the base clause. (#8477)
                if lit.index() < vals.len() && vals[lit.index()] < 0 {
                    let neg_lit = lit.negated();
                    let mark = Self::get_mark(marks, neg_lit.variable());
                    let expected = neg_lit.sign_i8();
                    if mark == expected {
                        // Side clause exists for this input. Safe to skip the
                        // root-false literal — the gate captures this constraint.
                        continue;
                    }
                    // No side clause: this literal is root-false but its
                    // constraint is NOT in the gate. Do NOT skip — fall through
                    // to the normal mark check, which will fail (mark==0 !=
                    // expected), causing gate detection to fail for this base
                    // clause. This is the CaDiCaL-divergent path that prevents
                    // incomplete gates without elim_propagate.
                }
                // Satisfied clause is not a gate candidate
                if lit.index() < vals.len() && vals[lit.index()] > 0 {
                    satisfied = true;
                    break;
                }
                let neg_lit = lit.negated();
                let mark = Self::get_mark(marks, neg_lit.variable());
                let expected = neg_lit.sign_i8();

                if mark != expected {
                    all_match = false;
                    break;
                }
                inputs.push(neg_lit);
                arity += 1;
            }

            // CaDiCaL gates.cpp:384-416: arity must be > 0 and all long-clause
            // inputs must have matching side-clause marks.
            if !satisfied && all_match && arity > 0 {
                // Phase 3 (CaDiCaL gates.cpp:405-414): Promote marks for
                // literals that actually appear in this long clause. This
                // distinguishes the exact gate inputs from stray binary
                // side-clause marks that don't participate in this gate.
                for &input in &inputs {
                    marks.promote(input.variable());
                }

                // Phase 4 (CaDiCaL gates.cpp:417-433): Re-scan binary
                // side-clauses, only collecting those whose "other" literal
                // has a promoted mark (value == 2 or -2).
                let mut filtered_side_clauses = Vec::new();
                for &side_idx in &binary_clause_indices {
                    if side_idx >= clauses.len() || clauses.is_empty_clause(side_idx) {
                        continue;
                    }
                    let side_clause = clauses.literals(side_idx);
                    if let Some(other) =
                        Self::get_effective_binary_other(side_clause, neg_output_lit, vals)
                    {
                        let mark = Self::get_mark(marks, other.variable());
                        // Promoted mark: sign * 2. Check that the mark
                        // matches the literal's expected sign doubled.
                        let expected_promoted = other.sign_i8() * 2;
                        if mark == expected_promoted {
                            filtered_side_clauses.push(side_idx);
                        }
                    }
                }

                // CaDiCaL gates.cpp:434: count >= arity.
                // With promotion, filtered count should exactly match arity.
                if filtered_side_clauses.len() >= arity {
                    debug_assert!(
                        !inputs.is_empty(),
                        "BUG: AND gate extraction must produce at least one input literal"
                    );
                    let mut defining = vec![clause_idx];
                    defining.extend(filtered_side_clauses.iter().copied());

                    result = Some(Gate {
                        output: pivot,
                        gate_type: GateType::And,
                        inputs,
                        defining_clauses: defining,
                        negated_output,
                    });
                }
                // CaDiCaL gates.cpp:435: after promotion, marks are
                // corrupted (doubled). Break regardless of success or
                // failure — unmark_all below resets everything.
                break;
            }
        }

        self.unmark_all(marks);
        result
    }
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! ITE (if-then-else) gate detection.
//!
//! ITE gate y = ITE(c, t, e) = (c ∧ t) ∨ (¬c ∧ e) is encoded as 4 ternary clauses:
//!   (y ∨ c ∨ ¬e), (y ∨ ¬c ∨ ¬t), (¬y ∨ c ∨ e), (¬y ∨ ¬c ∨ t)

use super::{Gate, GateExtractor, GateType};
use crate::clause_arena::ClauseArena;
use crate::literal::{Literal, Variable};

impl GateExtractor {
    /// Number of ternary clauses a literal occurs in (Kissat `largecount`),
    /// or `0` if the filter is disabled (empty slice) / literal out of range.
    #[inline]
    fn ternary_occ(ternary_count: &[u32], lit: Literal) -> u32 {
        ternary_count.get(lit.index()).copied().unwrap_or(0)
    }

    /// Kissat's `twice` both-polarity test for a single base-clause literal:
    /// the literal AND its negation must each occur in ≥2 ternary clauses.
    #[inline]
    fn both_polarity_ternary(ternary_count: &[u32], lit: Literal) -> bool {
        Self::ternary_occ(ternary_count, lit) >= 2
            && Self::ternary_occ(ternary_count, lit.negated()) >= 2
    }

    pub(super) fn find_ite_gate_db(
        &self,
        pivot: Variable,
        clauses: &ClauseArena,
        pos_occs: &[usize],
        neg_occs: &[usize],
        ternary_count: &[u32],
    ) -> Option<Gate> {
        let pivot_pos = Literal::positive(pivot);
        let pivot_neg = Literal::negative(pivot);

        // Kissat `twice` both-polarity ternary pre-filter
        // (congruence.c init_ite_gate_extraction / extract_ite_gates_with_base_clause).
        // When `ternary_count` is empty the filter is disabled and we fall
        // back to the unfiltered O(pos² × neg) scan (used by BVE scheduling,
        // which has no global ternary census).
        let filter = !ternary_count.is_empty();

        // Output-variable gate: the pivot must head ≥2 positive ternaries and
        // appear negated in ≥2 ternaries (Kissat largecount[lhs] ≥ 2 and
        // largecount[¬lhs] ≥ 2). This O(1) test rejects most pivots before the
        // quadratic base-pair scan, which is the dominant cost on large
        // dense-ternary formulas.
        if filter && !Self::both_polarity_ternary(ternary_count, pivot_pos) {
            return None;
        }

        // Two positive ternaries define candidates for (cond, then, else):
        //   (pivot ∨ cond ∨ ¬else), (pivot ∨ ¬cond ∨ ¬then)
        for (i, &ci) in pos_occs.iter().enumerate() {
            if ci >= clauses.len() || clauses.is_empty_clause(ci) {
                continue;
            }
            let c1 = clauses.literals(ci);
            let Some((a1, b1)) = Self::get_ternary_others(c1, pivot_pos) else {
                continue;
            };

            // `twice` filter on the first base clause: at least 2 of its 3
            // literals must occur in BOTH polarities among ternary clauses, and
            // every literal's negation must occur at least once. The pivot is
            // already known both-polarity (checked above), so we require ≥1 of
            // {a1, b1} to also be both-polarity.
            if filter {
                if Self::ternary_occ(ternary_count, a1.negated()) == 0
                    || Self::ternary_occ(ternary_count, b1.negated()) == 0
                {
                    continue;
                }
                let twice = 1 // pivot_pos qualifies
                    + Self::both_polarity_ternary(ternary_count, a1) as u32
                    + Self::both_polarity_ternary(ternary_count, b1) as u32;
                if twice < 2 {
                    continue;
                }
            }

            for &cj in &pos_occs[i + 1..] {
                if cj >= clauses.len() || clauses.is_empty_clause(cj) {
                    continue;
                }
                let c2 = clauses.literals(cj);
                let Some((a2, b2)) = Self::get_ternary_others(c2, pivot_pos) else {
                    continue;
                };

                // (cond, then_neg, else_neg)
                let patterns = [
                    (a1, b2, b1, a1 == a2.negated()),
                    (a1, a2, b1, a1 == b2.negated()),
                    (b1, b2, a1, b1 == a2.negated()),
                    (b1, a2, a1, b1 == b2.negated()),
                ];

                for (cond, then_neg, else_neg, enabled) in patterns {
                    if !enabled {
                        continue;
                    }

                    // Per-literal `twice` filter (Kissat extract_ite_gates_with_base_clause):
                    // the condition must be both-polarity in ternary clauses,
                    // and the then/else branches must each occur in ≥1 ternary.
                    if filter
                        && (!Self::both_polarity_ternary(ternary_count, cond)
                            || Self::ternary_occ(ternary_count, then_neg.negated()) == 0
                            || Self::ternary_occ(ternary_count, else_neg.negated()) == 0)
                    {
                        continue;
                    }

                    let then_lit = then_neg.negated();
                    let else_lit = else_neg.negated();
                    let mut neg_idx_else = None;
                    let mut neg_idx_then = None;

                    for &nk in neg_occs {
                        if nk >= clauses.len() || clauses.is_empty_clause(nk) {
                            continue;
                        }
                        let cn = clauses.literals(nk);
                        let Some((x, y)) = Self::get_ternary_others(cn, pivot_neg) else {
                            continue;
                        };

                        if (x == cond && y == else_lit) || (x == else_lit && y == cond) {
                            neg_idx_else = Some(nk);
                        } else if (x == cond.negated() && y == then_lit)
                            || (x == then_lit && y == cond.negated())
                        {
                            neg_idx_then = Some(nk);
                        }
                    }

                    if let (Some(n1), Some(n2)) = (neg_idx_else, neg_idx_then) {
                        debug_assert!(
                            cond.variable() != pivot
                                && then_lit.variable() != pivot
                                && else_lit.variable() != pivot,
                            "BUG: ITE semantic inputs must not include output variable"
                        );
                        debug_assert!(
                            {
                                let mut ids = [ci, cj, n1, n2];
                                ids.sort_unstable();
                                ids.windows(2).all(|w| w[0] != w[1])
                            },
                            "BUG: ITE witness clauses must be distinct"
                        );
                        return Some(Gate {
                            output: pivot,
                            gate_type: GateType::Ite,
                            inputs: vec![cond, then_lit, else_lit],
                            defining_clauses: vec![ci, cj, n1, n2],
                            negated_output: false,
                        });
                    }
                }
            }
        }

        None
    }
}

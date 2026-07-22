// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Bridge between ay-sat's internal arena+trail state and the
//! `ay-approx-bcp` approximate-BCP pre-filter (issue #8789 Phase 2).
//!
//! # Phase 2 scope (this file)
//!
//! Phase 2 wires the filter into `ay-sat` as a **pure observer**, gated
//! on the `approx-bcp-filter` Cargo feature (off by default). The bridge:
//!
//! 1. Snapshots the current arena's active clauses into 64-bit
//!    [`ClauseSignature`]s.
//! 2. Snapshots the current trail into a 64-bit [`AssignmentMask`] by
//!    OR-ing `literal_bit(-lit)` for every `lit` on the trail (the
//!    "currently falsified" set).
//! 3. Invokes [`may_be_unit_or_falsified`] for every active clause and
//!    compares the verdict against the exact trail-based classification.
//! 4. Bumps [`SolverStats::approx_bcp_noop_matched`] /
//!    `approx_bcp_conflict_matched` / `approx_bcp_mismatch_detected`
//!    accordingly.
//!
//! The pre-filter never mutates solver state — it is a measurement hook
//! for Phase 3 BCP-skip wiring. A nonzero `approx_bcp_mismatch_detected`
//! counter would indicate a soundness bug in the filter itself and is
//! the metric the integration test watches.
//!
//! # Phase 3 plan (not in this commit)
//!
//! Phase 3 will thread the verdict into the watch-literal walker so that
//! `NoopLikely` clauses skip the arena fetch entirely. That step
//! requires the default-on flip and per-benchmark measurements.

#![cfg(feature = "approx-bcp-filter")]

use ay_approx_bcp::{may_be_unit_or_falsified, AssignmentMask, ClauseSignature};

use crate::clause_arena::HEADER_WORDS;
use crate::literal::Literal as SatLiteral;
use crate::solver::state::Solver;

/// Verdict produced by [`Solver::run_approx_bcp_prefilter`] after
/// comparing the filter's classification of every active clause against
/// the exact trail-based classification.
///
/// The verdict summarises the filter's overall correctness+precision
/// stance over the current solver snapshot. It is intentionally coarse:
/// Phase 2 cares about *detecting* a mismatch, not about localising it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ApproxBcpPrefilterVerdict {
    /// Filter classified every clause as `NoopLikely` **and** every one
    /// of those clauses was genuinely not unit / not falsified on the
    /// real trail. Roughly: "the filter agrees the formula has no BCP
    /// work to do." This is the Phase 3 fast-path signal — when the
    /// verdict is `NoopLikely`, no watchlist walk is needed.
    NoopLikely,
    /// At least one clause was flagged by the filter as "maybe unit or
    /// falsified" (popcount ≤ 1) and the exact trail check confirmed it
    /// is indeed unit or falsified. Falls through to the exact BCP pass.
    ConflictLikely,
    /// Filter disagreed with exact BCP in a soundness-violating way: the
    /// filter said `NoopLikely` for a clause that the exact check
    /// flagged as unit or falsified. This must never happen if
    /// `ay_approx_bcp::filter::may_be_unit_or_falsified` is correct.
    /// Phase 2 surfaces this via a counter so regressions show up in
    /// `--stats` output.
    MismatchDetected,
}

/// Exact classification of a clause under the current trail.
///
/// Used as the ground-truth label against which
/// [`may_be_unit_or_falsified`] is compared.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ExactClauseState {
    /// At least two literals are not falsified and at least one is not
    /// satisfied — BCP has nothing to do here.
    NoopOrSat,
    /// Exactly one literal is unassigned and all others are falsified,
    /// or all literals are falsified. BCP must visit this clause.
    UnitOrFalsified,
}

/// Classify a clause exactly using the current `Solver.vals` state.
///
/// Mirrors the watchlist invariant: a clause is unit/falsified iff at
/// most one of its literals is not currently falsified. Satisfied
/// clauses (≥1 true literal) are reported as `NoopOrSat` because BCP
/// skips them regardless of how many literals are free.
///
/// `NoopOrSat` covers three states for the purpose of the filter
/// comparison:
///   * ≥ 2 unassigned literals (classical "no-op" — BCP has no work),
///   * at least one literal satisfied (clause is SAT on the trail),
///   * any combination thereof.
///
/// Returning `NoopOrSat` for satisfied clauses is intentional: the
/// exact trail-based classification aligns with what BCP will do (skip
/// the clause). The filter's soundness claim covers only unit/falsified
/// clauses — satisfied clauses are always safe to skip regardless.
fn classify_clause_exact(solver: &Solver, literals: &[SatLiteral]) -> ExactClauseState {
    let mut unassigned_count = 0usize;
    for lit in literals {
        match solver.lit_value(*lit) {
            None => {
                unassigned_count += 1;
                if unassigned_count >= 2 {
                    // ≥ 2 free literals → clause cannot be unit or
                    // falsified. BCP has no work.
                    return ExactClauseState::NoopOrSat;
                }
            }
            Some(true) => {
                // Literal evaluates to true → clause is satisfied →
                // BCP skips regardless of how many literals remain.
                return ExactClauseState::NoopOrSat;
            }
            Some(false) => {
                // Literal is false — does not affect the free count.
            }
        }
    }
    // At most 1 unassigned literal, no literal is satisfied. Clause is
    // either unit (exactly 1 free) or falsified (0 free).
    ExactClauseState::UnitOrFalsified
}

/// Read the raw literal list of an arena clause at `offset`.
fn read_arena_clause_lits(solver: &Solver, offset: usize) -> Vec<SatLiteral> {
    let lit_len = solver.arena.len_of(offset);
    let words = solver.arena.words();
    let start = offset + HEADER_WORDS;
    (0..lit_len)
        .map(|i| SatLiteral::from_index(words[start + i] as usize))
        .collect()
}

/// Compute the [`AssignmentMask`] covering every currently-falsified
/// literal in the solver's trail.
///
/// For every `lit` on the trail, `-lit` (the negation) is false in the
/// model — so `literal_bit(-lit.to_dimacs())` is the bit to OR in.
fn trail_to_assignment_mask(solver: &Solver) -> AssignmentMask {
    let mut mask = AssignmentMask::empty();
    for lit in &solver.trail {
        // `lit` is true on the trail, so `-lit` is false. Pass the DIMACS
        // form of the *negation* to `insert_falsified_literal`.
        let falsified_dimacs = -lit.to_dimacs();
        mask.insert_falsified_literal(falsified_dimacs);
    }
    mask
}

impl Solver {
    /// Run the approximate-BCP filter over every active clause and
    /// compare the verdict against the exact trail-based classification.
    ///
    /// Updates the `approx_bcp_*` counters on [`SolverStats`] and returns
    /// a summary verdict suitable for Phase 3 dispatch logic.
    ///
    /// Zero side effects beyond counter updates — safe to call from any
    /// read-consistent solver state (level 0, after a decision, inside
    /// `check_during_propagate`, etc.). No allocation in steady state
    /// except the per-clause literal vector; Phase 3 will replace the
    /// allocation with a stack-based scan once the counter ratios
    /// justify it.
    #[must_use]
    pub fn run_approx_bcp_prefilter(&mut self) -> ApproxBcpPrefilterVerdict {
        let assignment = trail_to_assignment_mask(self);

        // `active_indices()` borrows `self.arena` immutably; collect the
        // offsets into a Vec so the subsequent per-clause scan can borrow
        // `self` mutably to update counters. The arena rarely contains
        // more clauses than fit in one vector allocation, so this is not
        // a measurable cost on the profiling workloads we care about.
        let offsets: Vec<usize> = self.arena.active_indices().collect();

        let mut verdict = ApproxBcpPrefilterVerdict::NoopLikely;

        for offset in offsets {
            let sat_lits = read_arena_clause_lits(self, offset);
            if sat_lits.is_empty() {
                continue;
            }
            // Build the clause signature from DIMACS-form literals so
            // the bit hash matches what `AssignmentMask` sees from the
            // trail conversion above.
            let dimacs_lits: Vec<i32> = sat_lits.iter().map(|l| l.to_dimacs()).collect();
            let sig = ClauseSignature::from_literals(&dimacs_lits);

            let filter_says_maybe_unit = may_be_unit_or_falsified(sig, assignment);
            let exact = classify_clause_exact(self, &sat_lits);

            match (filter_says_maybe_unit, exact) {
                (true, ExactClauseState::UnitOrFalsified) => {
                    self.stats.approx_bcp_conflict_matched += 1;
                    verdict = ApproxBcpPrefilterVerdict::ConflictLikely;
                }
                (true, ExactClauseState::NoopOrSat) => {
                    // Filter false-positive: it flagged the clause as
                    // "maybe unit" but the exact check shows ≥ 2 live
                    // literals. Fine for soundness (the exact pass
                    // catches this), just means the filter
                    // over-approximates. No counter: Phase 2 does not
                    // track false-positive rate (Phase 3 will).
                }
                (false, ExactClauseState::NoopOrSat) => {
                    // True negative: filter correctly rejected a
                    // non-unit/non-falsified clause. This is the column
                    // that justifies the Phase 3 BCP-skip.
                    self.stats.approx_bcp_noop_matched += 1;
                }
                (false, ExactClauseState::UnitOrFalsified) => {
                    // Filter soundness violation — must never happen.
                    self.stats.approx_bcp_mismatch_detected += 1;
                    verdict = ApproxBcpPrefilterVerdict::MismatchDetected;
                }
            }
        }

        verdict
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::literal::{Literal, Variable};
    use crate::solver::Solver;

    fn fresh_solver(n: u32) -> Solver {
        let mut s = Solver::new(0);
        for _ in 0..n {
            s.new_var();
        }
        s
    }

    #[test]
    fn empty_solver_verdict_is_noop() {
        let mut s = fresh_solver(3);
        // No clauses, no trail — filter has nothing to scan.
        let v = s.run_approx_bcp_prefilter();
        assert_eq!(v, ApproxBcpPrefilterVerdict::NoopLikely);
        assert_eq!(s.stats.approx_bcp_mismatch_detected, 0);
    }

    #[test]
    fn filter_never_reports_mismatch_on_simple_formula() {
        // Formula: (x0 ∨ x1), (¬x0 ∨ x2). Small enough that we can
        // reason about every state, big enough that the filter has
        // clauses to evaluate.
        let mut s = fresh_solver(3);
        let v0 = Variable::new(0);
        let v1 = Variable::new(1);
        let v2 = Variable::new(2);
        assert!(s.add_clause(vec![Literal::positive(v0), Literal::positive(v1)]));
        assert!(s.add_clause(vec![Literal::negative(v0), Literal::positive(v2)]));

        let _ = s.solve();

        let v = s.run_approx_bcp_prefilter();
        // Correctness: mismatch counter must stay at zero.
        assert_eq!(
            s.stats.approx_bcp_mismatch_detected, 0,
            "filter reported a soundness mismatch: {v:?}"
        );
    }

    #[test]
    fn counters_move_when_clauses_exist() {
        let mut s = fresh_solver(4);
        let v0 = Variable::new(0);
        let v1 = Variable::new(1);
        let v2 = Variable::new(2);
        let v3 = Variable::new(3);
        // A 3-literal clause gives popcount ≥ 2 on an empty trail, so
        // the filter should return NoopLikely for it.
        assert!(s.add_clause(vec![
            Literal::positive(v0),
            Literal::positive(v1),
            Literal::positive(v2),
        ]));
        assert!(s.add_clause(vec![
            Literal::negative(v0),
            Literal::negative(v1),
            Literal::positive(v3),
        ]));

        // Don't solve — keep the trail empty so the filter sees its
        // "∀ clauses: popcount = 3" fast path.
        let _ = s.run_approx_bcp_prefilter();
        assert_eq!(
            s.stats.approx_bcp_mismatch_detected, 0,
            "filter soundness violation on empty trail"
        );
        // At least one counter should have moved — either noop_matched
        // (large clauses filter out) or conflict_matched (if arena has
        // any binary learned clauses already). The exact distribution
        // depends on internal arena layout; we only assert totality.
        let total = s.stats.approx_bcp_noop_matched
            + s.stats.approx_bcp_conflict_matched
            + s.stats.approx_bcp_mismatch_detected;
        assert!(
            total > 0 || s.arena.active_indices().count() == 0,
            "filter did not classify any clauses despite non-empty arena"
        );
    }
}

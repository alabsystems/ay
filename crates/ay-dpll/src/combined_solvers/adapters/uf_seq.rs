// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::{TermId, TermStore, TheoryResult, TheorySolver};
use ay_euf::{EufModel, EufSolver};
use ay_seq::{SeqModel, SeqSolver};

use crate::combined_solvers::check_loops::{
    assert_fixpoint_convergence, debug_nelson_oppen, defer_non_local_result, forward_non_sat,
    propagate_equalities_to,
};

/// Combined EUF + Seq theory solver for QF_SEQ.
///
/// Wraps `EufSolver` and `SeqSolver` with Nelson-Oppen equality exchange.
/// EUF handles transitivity of equalities (e.g., `s = unit(5)` and `s = empty`
/// implies `unit(5) = empty`). SeqSolver handles sequence-specific reasoning
/// (unit injectivity, unit-empty conflict detection).
///
/// Without this combination, the standalone SeqSolver cannot detect conflicts
/// that require transitivity through shared variables. See #5951.
pub(crate) struct UfSeqSolver<'a> {
    /// EUF solver for equality and congruence reasoning.
    euf: EufSolver<'a>,
    /// Seq solver for sequence-specific axioms.
    seq: SeqSolver<'a>,
    /// Scope depth counter for push/pop symmetry checking (#4995).
    scope_depth: usize,
}

impl<'a> UfSeqSolver<'a> {
    /// Create a new combined EUF+Seq solver.
    pub(crate) fn new(terms: &'a TermStore) -> Self {
        Self {
            euf: EufSolver::new(terms),
            seq: SeqSolver::new(terms),
            scope_depth: 0,
        }
    }

    /// Extract both EUF and Seq models for model generation.
    pub(crate) fn extract_models(&mut self) -> (EufModel, SeqModel) {
        (self.euf.extract_model(), self.seq.extract_model())
    }

    /// Check EUF's equivalence classes for Seq-specific conflicts (#5951).
    ///
    /// EUF merges terms transitively (e.g., `s = unit(5)` and `s = empty` puts
    /// `unit(5)` and `empty` in the same class). This method detects:
    /// - **Unit-empty conflicts**: A unit term and empty term share an EUF class.
    /// - **Unit injectivity**: Two unit terms share an EUF class → their elements
    ///   must be equal (propagated as N-O equality).
    ///
    /// Returns `Err(Unsat)` on conflict, `Ok(count)` with new equalities propagated.
    #[allow(clippy::result_large_err)] // TheoryResult is inherently large; boxing adds overhead on the hot path
    fn check_seq_euf_classes(&mut self) -> Result<usize, TheoryResult> {
        let unit_terms: Vec<TermId> = self.seq.unit_terms().collect();
        let empty_terms: Vec<TermId> = self.seq.empty_terms().collect();
        let mut new_eq_count = 0usize;

        // Check if any unit term shares an EUF class with an empty term.
        for &unit_t in &unit_terms {
            for &empty_t in &empty_terms {
                if self.euf.are_equal(unit_t, empty_t) {
                    let reasons = self.euf.explain(unit_t, empty_t);
                    return Err(TheoryResult::Unsat(reasons));
                }
            }
        }

        // Check unit injectivity via EUF classes: if two unit terms share a
        // class, their elements must be equal.
        for i in 0..unit_terms.len() {
            let a = unit_terms[i];
            for &b in &unit_terms[i + 1..] {
                if self.euf.are_equal(a, b) {
                    if let (Some(elem_a), Some(elem_b)) =
                        (self.seq.unit_element(a), self.seq.unit_element(b))
                    {
                        if elem_a != elem_b && !self.euf.are_equal(elem_a, elem_b) {
                            let reasons = self.euf.explain(a, b);
                            self.seq.assert_shared_equality(elem_a, elem_b, &reasons);
                            self.euf.assert_shared_equality(elem_a, elem_b, &reasons);
                            new_eq_count += 1;
                        }
                    }
                }
            }
        }

        Ok(new_eq_count)
    }
}

impl TheorySolver for UfSeqSolver<'_> {
    fn register_atom(&mut self, atom: TermId) {
        self.euf.register_atom(atom);
        self.seq.register_atom(atom);
    }

    fn internalize_atom(&mut self, term: TermId) {
        self.euf.internalize_atom(term);
        self.seq.internalize_atom(term);
    }

    fn assert_literal(&mut self, literal: TermId, value: bool) {
        self.euf.assert_literal(literal, value);
        self.seq.assert_literal(literal, value);
    }

    fn check(&mut self) -> TheoryResult {
        let debug = debug_nelson_oppen() || crate::theory_debug_flags::debug_ufseq();
        const MAX_ITERATIONS: usize = 100;
        // #8319: AY_MAX_FIXPOINT_ROUNDS caps the N-O loop for debugging.
        let max_iters = crate::theory_debug_flags::max_fixpoint_rounds()
            .unwrap_or(MAX_ITERATIONS)
            .min(MAX_ITERATIONS);

        if debug {
            let unit_count = self.seq.unit_terms().count();
            let empty_count = self.seq.empty_terms().count();
            safe_eprintln!(
                "[UFSEQ] check() called: unit_terms={}, empty_terms={}",
                unit_count,
                empty_count
            );
        }

        for iteration in 0..max_iters {
            // Check Seq first for direct conflicts (unit = empty).
            let seq_result = self.seq.check();
            if debug {
                safe_eprintln!(
                    "[UFSEQ] iter {}: seq.check() => {:?}",
                    iteration,
                    match &seq_result {
                        TheoryResult::Sat => "Sat",
                        TheoryResult::Unsat(_) => "Unsat",
                        TheoryResult::Unknown => "Unknown",
                        _ => "Other",
                    }
                );
            }
            match &seq_result {
                TheoryResult::Unsat(reasons) => return TheoryResult::Unsat(reasons.clone()),
                TheoryResult::Unknown => return TheoryResult::Unknown,
                TheoryResult::Sat => {}
                _ => return seq_result,
            }

            // Propagate equalities from Seq to EUF (unit injectivity).
            let seq_eq_count = match propagate_equalities_to(
                &mut self.seq,
                &mut self.euf,
                debug,
                "UFSEQ-Seq",
                iteration,
            ) {
                Ok(n) => n,
                Err(conflict) => return conflict,
            };
            if debug {
                safe_eprintln!(
                    "[UFSEQ] iter {}: seq->euf eq_count={}",
                    iteration,
                    seq_eq_count
                );
            }

            // Check EUF (may find new equalities via congruence/transitivity).
            let euf_result = self.euf.check();
            if debug {
                safe_eprintln!(
                    "[UFSEQ] iter {}: euf.check() => {:?}",
                    iteration,
                    match &euf_result {
                        TheoryResult::Sat => "Sat",
                        TheoryResult::Unsat(_) => "Unsat",
                        TheoryResult::Unknown => "Unknown",
                        _ => "Other",
                    }
                );
            }
            if let Some(result) = forward_non_sat(euf_result) {
                return result;
            }

            // Check EUF's equivalence classes for Seq-specific conflicts.
            // This catches transitive unit-empty conflicts that neither theory
            // detects alone (e.g., s = unit(5) ∧ s = empty). (#5951)
            let class_eq_count = match self.check_seq_euf_classes() {
                Err(conflict) => {
                    if debug {
                        safe_eprintln!(
                            "[UFSEQ] iter {}: seq-euf class conflict detected",
                            iteration
                        );
                    }
                    return conflict;
                }
                Ok(n) => n,
            };

            // Propagate equalities from EUF to Seq.
            let euf_eq_count = match propagate_equalities_to(
                &mut self.euf,
                &mut self.seq,
                debug,
                "UFSEQ-EUF",
                iteration,
            ) {
                Ok(n) => n,
                Err(conflict) => return conflict,
            };

            let has_new_equalities = seq_eq_count > 0 || euf_eq_count > 0 || class_eq_count > 0;

            if !has_new_equalities {
                if debug && iteration > 0 {
                    safe_eprintln!(
                        "[N-O UFSEQ] Fixpoint reached after {} iterations",
                        iteration + 1
                    );
                }
                assert_fixpoint_convergence("UFSEQ", &mut [&mut self.seq, &mut self.euf]);
                return TheoryResult::Sat;
            }

            // Non-convergence is a solver bug — assert in all build modes.
            // Non-convergence within the fixpoint bound is a SOUND fallback, not
            // a crash: the loop ends and returns `TheoryResult::Unknown` below.
            // (Formerly a `did not converge` panic — an abort on a legitimate, if
            // pathological, instance; `unknown` is always sound. #8319: a capped
            // `--max-fixpoint-rounds` reaches the same fallback.)
        }
        TheoryResult::Unknown
    }

    /// BCP-time lightweight check: run each sub-theory's cheap check
    /// individually WITHOUT the Nelson-Oppen fixpoint loop (#8404).
    ///
    /// Same rationale as `UfSeqLiaSolver::check_during_propagate`. During BCP,
    /// only per-theory consistency checks are needed. The full N-O loop with
    /// cross-theory equality propagation is deferred to `check()`.
    fn check_during_propagate(&mut self) -> TheoryResult {
        // EUF: runs congruence closure check.
        let euf_result = defer_non_local_result(self.euf.check_during_propagate());
        if !matches!(euf_result, TheoryResult::Sat) {
            return euf_result;
        }

        // Seq: runs unit-empty conflict detection.
        let seq_result = defer_non_local_result(self.seq.check_during_propagate());
        if !matches!(seq_result, TheoryResult::Sat) {
            return seq_result;
        }

        TheoryResult::Sat
    }

    /// Since `check_during_propagate` skips the Nelson-Oppen fixpoint, the
    /// eager path must run one final full `check()` before accepting SAT.
    fn needs_final_check_after_sat(&self) -> bool {
        true
    }

    delegate_propagate!(euf, seq);

    delegate_scope_ops!("UfSeqSolver", euf, seq);
}

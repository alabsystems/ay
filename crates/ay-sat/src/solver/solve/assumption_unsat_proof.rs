// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Keep query-relative refutations out of the persistent base proof stream.

use super::super::*;
use super::finalize_unsat::UnsatProofFinalizationError;

/// A returned core is not itself authority to refute the persistent formula.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum AssumptionUnsatScope {
    BaseFormula,
    ConditionalQuery,
}

impl Solver {
    pub(super) fn assumption_unsat_scope(&self) -> AssumptionUnsatScope {
        // A root conflict may return an over-approximate, non-empty core.
        // Conversely, a temporary constraint can fail with an empty core.
        // Even an empty core at level zero is not authority: analysis may
        // already have backtracked or core extraction may have omitted an
        // assumption. Only the separately recorded semantic base refutation
        // licenses a terminal empty proof.
        if self.has_empty_clause {
            AssumptionUnsatScope::BaseFormula
        } else {
            AssumptionUnsatScope::ConditionalQuery
        }
    }

    /// Flush a base-proof prefix without closing it with an empty clause.
    ///
    /// Assumptions are decisions, not permanent proof axioms. Learned clauses
    /// retain their assumption complements, so they remain valid base steps.
    /// An empty clause would instead assert that the base formula is UNSAT.
    /// Neither DRAT nor LRAT provides query framing in this attached stream.
    /// Do not reconstruct a base refutation or publish its certificate here.
    pub(super) fn finalize_conditional_unsat_proof(
        &mut self,
    ) -> Result<(), UnsatProofFinalizationError> {
        // Preserve the existing SMT query marker. This is not an empty-clause
        // addition and must not raise has_empty_clause or allocate a proof ID.
        if let Some(trace) = self.live_clause_trace_mut() {
            trace.mark_empty();
        }

        // Keep I/O and chain failures fail-closed without requiring a terminal
        // empty. A replay exception for a base refutation is not authority for
        // this conditional prefix: LRAT authority failures remain terminal.
        if let Some(manager) = self.proof_manager.as_mut() {
            manager
                .flush()
                .map_err(|_| UnsatProofFinalizationError::ProofIo)?;
            if manager.has_lrat_authority_fail_closed() {
                return Err(UnsatProofFinalizationError::LratAuthorityFailClosed);
            }
            if manager.has_io_error() {
                return Err(UnsatProofFinalizationError::ProofIo);
            }
            let failures = manager.lrat_failures();
            if failures != 0 {
                return Err(UnsatProofFinalizationError::LratChainFailures(failures));
            }
        }
        if self.cold.backward_proof_failure.is_some() {
            return Err(UnsatProofFinalizationError::InvalidLratChain(
                "a prior backward reconstruction failed",
            ));
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn returning_to_root_without_base_refutation_stays_conditional() {
        let mut solver = Solver::new(2);
        solver.add_clause(vec![
            Literal::positive(Variable::new(0)),
            Literal::positive(Variable::new(1)),
        ]);
        solver.decide(Literal::negative(Variable::new(0)));
        solver.backtrack(0);
        assert_eq!(solver.decision_level, 0);
        assert!(!solver.has_empty_clause);
        assert_eq!(
            solver.assumption_unsat_scope(),
            AssumptionUnsatScope::ConditionalQuery,
        );
    }

    use std::io::{self, Write};
    use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
    use std::sync::Arc;

    enum FlushAction {
        Count,
        Raise(Arc<AtomicBool>),
    }

    struct ObservedFlush {
        action: FlushAction,
        calls: Arc<AtomicUsize>,
    }

    impl Write for ObservedFlush {
        fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
            Ok(bytes.len())
        }

        fn flush(&mut self) -> io::Result<()> {
            self.calls.fetch_add(1, Ordering::Relaxed);
            if let FlushAction::Raise(flag) = &self.action {
                flag.store(true, Ordering::Relaxed);
            }
            Ok(())
        }
    }

    #[test]
    fn native_stop_before_conditional_flush_refuses_without_writer_work() {
        for reason in [
            SatUnknownReason::DeadlineExceeded,
            SatUnknownReason::Interrupted,
        ] {
            let calls = Arc::new(AtomicUsize::new(0));
            let writer = ObservedFlush {
                action: FlushAction::Count,
                calls: calls.clone(),
            };
            let mut solver = Solver::with_proof_output(2, ProofOutput::drat_text(writer));
            solver.add_clause(vec![Literal::positive(Variable::new(0))]);
            if reason == SatUnknownReason::DeadlineExceeded {
                solver.set_solve_deadline(Some(ay_core::time::Instant::now()));
            } else {
                solver.set_interrupt(Arc::new(AtomicBool::new(true)));
            }
            assert!(solver.declare_unsat_assume(vec![]).is_unknown());
            assert_eq!(solver.last_unknown_reason(), Some(reason));
            assert_eq!(calls.load(Ordering::Relaxed), 0);
            assert!(!solver.has_empty_clause);
            assert!(!solver.cold.empty_clause_in_proof);
        }
    }

    #[test]
    fn native_interrupt_raised_by_conditional_flush_vetoes_terminal_unsat() {
        let flag = Arc::new(AtomicBool::new(false));
        let calls = Arc::new(AtomicUsize::new(0));
        let writer = ObservedFlush {
            action: FlushAction::Raise(flag.clone()),
            calls: calls.clone(),
        };
        let mut solver = Solver::with_proof_output(2, ProofOutput::drat_text(writer));
        solver.set_interrupt(flag.clone());
        solver.add_clause(vec![Literal::positive(Variable::new(0))]);
        assert!(solver.declare_unsat_assume(vec![]).is_unknown());
        assert_eq!(
            solver.last_unknown_reason(),
            Some(SatUnknownReason::Interrupted)
        );
        assert_eq!(calls.load(Ordering::Relaxed), 1);
        assert!(flag.load(Ordering::Relaxed));
        assert!(!solver.has_empty_clause);
        assert!(!solver.cold.empty_clause_in_proof);
        assert_eq!(solver.cold.empty_clause_lrat_id, None);
    }
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use std::cell::Cell;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use ay_core::Sort;
use ay_frontend::{parse, SourceContextStamp};

use crate::executor_types::{UnknownOrigin, UnknownReason};
use crate::incremental_state::{IncrementalBvState, IncrementalTheoryState};

use super::super::super::support::partition_fp_assertions;
use super::super::super::to_real::{collect_fp_to_real_sites, rewrite_fp_to_real_with_vars};
use super::*;

struct Fixture {
    executor: Executor,
    roots: Vec<TermId>,
    rewritten: Vec<TermId>,
    real: TermId,
    stamp: SourceContextStamp,
    theory_allocation: *const TermId,
}

impl Fixture {
    fn new() -> Self {
        let mut executor = Executor::new();
        executor
            .execute_all(
                &parse(
                    "(set-logic QF_FPLRA)
                     (declare-const x (_ FloatingPoint 5 11))
                     (assert (= (fp.to_real x) 3.5))
                     (push 1)",
                )
                .unwrap(),
            )
            .unwrap();
        let roots = executor.ctx.assertions.clone();
        let (_, mixed) = partition_fp_assertions(&executor.ctx.terms, &roots);
        let sites = collect_fp_to_real_sites(&executor.ctx.terms, &mixed);
        assert_eq!(sites.len(), 1);
        let real = executor.ctx.terms.mk_var("__mixed_test_real", Sort::Real);
        let replacements = HashMap::from_iter([(sites[0].arg, real)]);
        let rewritten = mixed
            .iter()
            .map(|&root| {
                rewrite_fp_to_real_with_vars(
                    &mut executor.ctx.terms,
                    root,
                    &replacements,
                    &mut HashMap::default(),
                )
            })
            .collect();
        // Explicit fault-injected stale publication guards, not a claimed
        // satisfying witness. Refusal must revoke them after restoration.
        let mut old_model = Model::empty();
        old_model.sat_model = vec![true, false, true];
        executor.last_model = Some(old_model);
        executor.last_result = Some(SolveResult::Sat);
        executor.last_model_validated = true;
        executor.last_assumption_core = Some(roots.clone());
        // Real retained SAT owners and a nonempty allocation canary prove that
        // the child's isolated state is not accidentally installed outside.
        let mut theory = IncrementalTheoryState::new();
        theory.scope_depth = 1;
        theory.persistent_sat = Some(ay_sat::Solver::new(7));
        theory.theory_atoms = roots.clone();
        let theory_allocation = theory.theory_atoms.as_ptr();
        executor.incr_theory_state = Some(theory);
        let mut bv = IncrementalBvState::new();
        bv.scope_depth = 1;
        bv.persistent_sat = Some(ay_sat::Solver::new(11));
        executor.incr_bv_state = Some(Box::new(bv));
        let stamp = executor.ctx.source_context_stamp();
        Self {
            executor,
            roots,
            rewritten,
            real,
            stamp,
            theory_allocation,
        }
    }

    fn restored(&self) {
        assert_eq!(self.executor.ctx.assertions, self.roots);
        assert_eq!(self.executor.ctx.logic(), Some("QF_FPLRA"));
        assert_eq!(self.executor.ctx.source_context_stamp(), self.stamp);
        assert_eq!(self.executor.ctx.scope_depth(), 1);
        let theory = self.executor.incr_theory_state.as_ref().unwrap();
        assert_eq!(theory.scope_depth, 1);
        assert_eq!(theory.theory_atoms, self.roots);
        assert_eq!(theory.theory_atoms.as_ptr(), self.theory_allocation);
        assert_eq!(theory.persistent_sat.as_ref().unwrap().total_num_vars(), 7);
        let bv = self.executor.incr_bv_state.as_ref().unwrap();
        assert_eq!(bv.scope_depth, 1);
        assert_eq!(bv.persistent_sat.as_ref().unwrap().total_num_vars(), 11);
    }

    fn revoked(&self, origin: UnknownOrigin) {
        self.restored();
        assert_eq!(self.executor.unknown_origin(), Some(origin));
        assert!(matches!(
            self.executor.last_result,
            Some(SolveResult::Unknown)
        ));
        assert!(self.executor.last_model.is_none());
        assert!(!self.executor.last_model_validated);
        assert!(self.executor.last_assumption_core.is_none());
        assert!(self.executor.last_proof.is_none());
        assert!(self.executor.last_sat_certificate.is_none());
        assert!(self.executor.last_unsat_certificate.is_none());
    }
}

#[test]
fn actual_proof_checkpoint_exhaustion_survives_mixed_state_restoration() {
    let mut fixture = Fixture::new();
    fixture.executor.proof_checkpoint_budget.set_remaining(0);
    let stop = FpStop::from_executor(&fixture.executor);
    let children = Cell::new(0);
    let result = fixture
        .executor
        .solve_rewritten_mixed_subproblem(&fixture.rewritten, &stop, &|phase| {
            if matches!(phase, FpRealPhase::MixedChild) {
                children.set(children.get() + 1);
            }
        })
        .unwrap();
    assert!(result.result.is_unknown());
    assert!(result.lra_model.is_none() && result.euf_model.is_none());
    assert_eq!(
        children.get(),
        0,
        "the actual proof preflight rejects the child"
    );
    fixture.revoked(UnknownOrigin::DeterministicResourceBudget);
    assert_eq!(fixture.executor.proof_checkpoint_budget.remaining(), 0);
    fixture.executor.begin_external_decision_query(false);
    assert!(fixture.executor.proof_checkpoint_budget.remaining() > 0);
    assert_eq!(
        stop.check(),
        Err(UnknownOrigin::DeterministicResourceBudget)
    );
    let fresh = FpStop::from_executor(&fixture.executor);
    let result = fixture
        .executor
        .solve_rewritten_mixed_subproblem(&fixture.rewritten, &fresh, &|_| {})
        .unwrap();
    assert!(result.result.is_sat());
    fixture.restored();
}

#[test]
fn successful_real_child_returns_its_model_but_restores_outer_owners() {
    let mut fixture = Fixture::new();
    let stop = FpStop::from_executor(&fixture.executor);
    let children = Cell::new(0);
    let result = fixture
        .executor
        .solve_rewritten_mixed_subproblem(&fixture.rewritten, &stop, &|phase| {
            if matches!(phase, FpRealPhase::MixedChild) {
                children.set(children.get() + 1);
            }
        })
        .unwrap();
    assert!(result.result.is_sat());
    assert_eq!(children.get(), 1);
    assert_eq!(
        result.lra_model.unwrap().values.get(&fixture.real),
        Some(&num_rational::BigRational::new(7.into(), 2.into()))
    );
    fixture.restored();
    assert_eq!(
        fixture.executor.last_model.as_ref().unwrap().sat_model,
        [true, false, true]
    );
    assert!(fixture.executor.last_model_validated);
    assert_eq!(stop.check(), Ok(()));
}

#[test]
fn ordinary_real_contradiction_does_not_poison_the_stop_owner() {
    let mut fixture = Fixture::new();
    let negated = fixture.executor.ctx.terms.mk_not(fixture.rewritten[0]);
    let contradictory = [fixture.rewritten[0], negated];
    let stop = FpStop::from_executor(&fixture.executor);
    let result = fixture
        .executor
        .solve_rewritten_mixed_subproblem(&contradictory, &stop, &|_| {})
        .unwrap();
    assert!(result.result.is_unsat());
    assert!(result.lra_model.is_none() && result.euf_model.is_none());
    fixture.restored();
    assert_eq!(stop.check(), Ok(()));
    assert!(matches!(
        fixture.executor.last_result,
        Some(SolveResult::Sat)
    ));
}

#[test]
fn mixed_child_interrupt_stays_terminal_after_restoration_resets_live_flag() {
    let mut fixture = Fixture::new();
    let flag = Arc::new(AtomicBool::new(false));
    fixture.executor.set_interrupt(Arc::clone(&flag));
    let stop = FpStop::from_executor(&fixture.executor);
    let result = fixture
        .executor
        .solve_rewritten_mixed_subproblem(&fixture.rewritten, &stop, &|phase| match phase {
            FpRealPhase::MixedChild => flag.store(true, Ordering::Relaxed),
            FpRealPhase::MixedRestored => flag.store(false, Ordering::Relaxed),
            _ => {}
        })
        .unwrap();
    assert!(result.result.is_unknown());
    assert!(!flag.load(Ordering::Relaxed));
    fixture.revoked(UnknownOrigin::InterruptFlag);
    assert_eq!(stop.check(), Err(UnknownOrigin::InterruptFlag));
}

#[test]
fn stop_after_successful_child_discards_its_returned_models() {
    let mut fixture = Fixture::new();
    let flag = Arc::new(AtomicBool::new(false));
    fixture.executor.set_interrupt(Arc::clone(&flag));
    let stop = FpStop::from_executor(&fixture.executor);
    let children = Cell::new(0);
    let result = fixture
        .executor
        .solve_rewritten_mixed_subproblem(&fixture.rewritten, &stop, &|phase| match phase {
            FpRealPhase::MixedChild => children.set(children.get() + 1),
            FpRealPhase::MixedRestored => flag.store(true, Ordering::Relaxed),
            _ => {}
        })
        .unwrap();
    assert_eq!(children.get(), 1);
    assert!(result.result.is_unknown());
    assert!(result.lra_model.is_none() && result.euf_model.is_none());
    fixture.revoked(UnknownOrigin::InterruptFlag);
}

#[test]
fn mixed_child_panic_restores_roots_logic_and_incremental_owners_before_unwind() {
    let mut fixture = Fixture::new();
    let stop = FpStop::from_executor(&fixture.executor);
    let caught = catch_unwind(AssertUnwindSafe(|| {
        let _ = fixture.executor.solve_rewritten_mixed_subproblem(
            &fixture.rewritten,
            &stop,
            &|phase| {
                if matches!(phase, FpRealPhase::MixedChild) {
                    panic!("test mixed observer unwind");
                }
            },
        );
    }));
    assert!(caught.is_err());
    fixture.restored();
    assert_eq!(
        fixture.executor.last_model.as_ref().unwrap().sat_model,
        [true, false, true]
    );
    assert!(fixture.executor.last_model_validated);
    assert_eq!(fixture.executor.last_unknown_reason, None::<UnknownReason>);
}

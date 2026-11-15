// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use std::cell::Cell;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use ay_core::Sort;
use ay_fp::FpBuildStage;
use ay_frontend::{parse, SourceContextStamp};

use super::super::support::partition_fp_assertions;
use super::super::to_real::{collect_fp_to_real_sites, extract_fp_to_real_targets};
use super::*;

mod lifecycle;

const EXACT: &str = "(set-logic QF_FPLRA)
    (declare-const x (_ FloatingPoint 5 11))
    (assert (not (fp.isNaN x)))
    (assert (not (fp.isInfinite x)))
    (assert (= (fp.to_real x) 3.5))";

struct Fixture {
    executor: Executor,
    roots: Vec<TermId>,
    stamp: SourceContextStamp,
    logic: Option<String>,
}

impl Fixture {
    fn new(script: &str) -> Self {
        let mut executor = Executor::new();
        executor.execute_all(&parse(script).unwrap()).unwrap();
        Self {
            roots: executor.ctx.assertions.clone(),
            stamp: executor.ctx.source_context_stamp(),
            logic: executor.ctx.logic().map(str::to_owned),
            executor,
        }
    }

    fn restored(&self) {
        assert_eq!(self.executor.ctx.assertions, self.roots);
        assert_eq!(self.executor.ctx.source_context_stamp(), self.stamp);
        assert_eq!(self.executor.ctx.logic(), self.logic.as_deref());
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

    fn public_sat(&mut self) {
        let output = self
            .executor
            .execute_all(&parse("(check-sat)").unwrap())
            .unwrap();
        assert_eq!(
            output,
            ["sat"],
            "origin={:?}, detail={:?}",
            self.executor.unknown_origin(),
            self.executor.unknown_detail()
        );
        assert!(self.executor.last_model.is_some());
        assert!(matches!(self.executor.last_result, Some(SolveResult::Sat)));
        self.restored();
    }

    fn targets(&self) -> HashMap<TermId, f64> {
        let (_, mixed) = partition_fp_assertions(&self.executor.ctx.terms, &self.roots);
        assert_eq!(
            collect_fp_to_real_sites(&self.executor.ctx.terms, &mixed).len(),
            1
        );
        let mut targets = HashMap::default();
        for root in mixed {
            extract_fp_to_real_targets(&self.executor.ctx.terms, root, &mut targets);
        }
        targets
    }
}

#[derive(Default)]
struct Counts {
    checkpoint: Cell<usize>,
    child: Cell<usize>,
    targeted: Cell<usize>,
    refinement: Cell<usize>,
    simple: Cell<usize>,
    publication: Cell<usize>,
}

impl Counts {
    fn observe(&self, phase: FpRealPhase) {
        let counter = match phase {
            FpRealPhase::MixedCheckpoint => &self.checkpoint,
            FpRealPhase::MixedChild => &self.child,
            FpRealPhase::TargetedSearch => &self.targeted,
            FpRealPhase::RefinementSearch => &self.refinement,
            FpRealPhase::SimpleSearch => &self.simple,
            FpRealPhase::Publication => &self.publication,
            _ => return,
        };
        counter.set(counter.get() + 1);
    }

    fn searches(&self) -> usize {
        self.targeted.get() + self.refinement.get() + self.simple.get()
    }
}

#[test]
fn absent_structural_target_proof_budget_stop_precedes_every_fp_search() {
    let mut fixture = Fixture::new(
        "(set-logic QF_FPLRA)
         (declare-const x (_ FloatingPoint 5 11))
         (assert (not (fp.isNaN x)))
         (assert (not (fp.isInfinite x)))
         (assert (> (fp.to_real x) 1.0))",
    );
    assert!(fixture.targets().is_empty());
    // Use the private lane only after setting the real checkpoint allowance:
    // a public check-sat correctly rearms it for a new external query.
    fixture.executor.proof_checkpoint_budget.set_remaining(0);
    let counts = Counts::default();
    let result = fixture
        .executor
        .solve_fp_to_real_observed(&|phase| counts.observe(phase))
        .unwrap();
    assert!(result.is_unknown());
    assert_eq!(counts.checkpoint.get(), 1);
    assert_eq!(counts.child.get(), 0);
    assert_eq!(counts.searches(), 0);
    assert_eq!(counts.publication.get(), 1);
    assert_eq!(fixture.executor.proof_checkpoint_budget.remaining(), 0);
    fixture.revoked(UnknownOrigin::DeterministicResourceBudget);
    fixture.public_sat();
    assert!(fixture.executor.proof_checkpoint_budget.remaining() > 0);
}

#[test]
fn exact_target_mixed_budget_stop_cannot_fall_through_to_refinement() {
    let mut fixture = Fixture::new(EXACT);
    let targets = fixture.targets();
    assert_eq!(targets.len(), 1);
    assert_eq!(targets.values().copied().next(), Some(3.5));
    fixture.executor.proof_checkpoint_budget.set_remaining(0);
    let counts = Counts::default();
    let result = fixture
        .executor
        .solve_fp_to_real_observed(&|phase| counts.observe(phase))
        .unwrap();
    assert!(result.is_unknown());
    assert_eq!(counts.targeted.get(), 1);
    assert_eq!(counts.checkpoint.get(), 1);
    assert_eq!(counts.child.get(), 0);
    assert_eq!(counts.refinement.get(), 0);
    assert_eq!(counts.simple.get(), 0);
    fixture.revoked(UnknownOrigin::DeterministicResourceBudget);
    fixture.public_sat();
}

#[test]
fn ordinary_nan_target_unsat_still_allows_refinement_sat() {
    let mut fixture = Fixture::new(
        "(set-logic QF_FPLRA)
         (declare-const x (_ FloatingPoint 5 11))
         (assert (fp.isNaN x))
         (assert (= (fp.to_real x) 5.0))",
    );
    assert_eq!(fixture.targets().values().copied().next(), Some(5.0));
    let counts = Counts::default();
    let result = fixture
        .executor
        .solve_fp_to_real_observed(&|phase| counts.observe(phase))
        .unwrap();
    // A finite 5.0 target contradicts isNaN. Its ordinary UNSAT must not stop
    // refinement: fp.to_real is unspecified on the subsequent NaN witness.
    assert!(result.is_sat());
    assert_eq!(counts.targeted.get(), 1);
    assert!(counts.refinement.get() > 0);
    assert!(counts.child.get() > 0);
    assert!(!fixture.executor.fp_recorded_resource_stop());
    fixture.restored();
    fixture.public_sat();
}

#[test]
fn no_site_branch_retains_simple_search_and_publication() {
    let mut fixture = Fixture::new(
        "(set-logic QF_FP)
         (declare-const x (_ FloatingPoint 5 11))
         (assert (fp.isZero x))",
    );
    let (_, mixed) = partition_fp_assertions(&fixture.executor.ctx.terms, &fixture.roots);
    assert!(collect_fp_to_real_sites(&fixture.executor.ctx.terms, &mixed).is_empty());
    let counts = Counts::default();
    // Directly exercise the helper's no-site branch; this does not claim that
    // ordinary public routing selects to_real for a pure-FP source problem.
    assert!(fixture
        .executor
        .solve_fp_to_real_observed(&|phase| counts.observe(phase))
        .unwrap()
        .is_sat());
    assert_eq!(counts.simple.get(), 1);
    assert_eq!(counts.targeted.get(), 0);
    assert_eq!(counts.refinement.get(), 0);
    assert_eq!(counts.child.get(), 0);
    assert_eq!(counts.publication.get(), 1);
    assert!(fixture.executor.last_model.is_some());
    fixture.restored();
}

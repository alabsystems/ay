// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::executor::theories::ChainSpend;

#[test]
fn full_lane_phase_stops_revoke_genuine_prior_sat_and_allow_fresh_queries() {
    for (target, boundary) in [
        (FpRealPhase::ClauseTransfer, 2),
        (FpRealPhase::SatLoad, 3),
        (FpRealPhase::TargetPreparation, 1),
        (FpRealPhase::TargetedSearch, 1),
        (FpRealPhase::SatPoll, 1),
        (FpRealPhase::SatReturned, 1),
        (FpRealPhase::Rewrite, 2),
        (FpRealPhase::ModelExtracted, 2),
        (FpRealPhase::MixedRestored, 1),
        (FpRealPhase::Publication, 1),
    ] {
        let mut fixture = Fixture::new(EXACT);
        fixture.public_sat(); // A real published SAT/model, not injected flags.
        let interrupt = Arc::new(AtomicBool::new(false));
        fixture.executor.set_interrupt(Arc::clone(&interrupt));
        let calls = Cell::new(0);
        let refinements = Cell::new(0);
        let result = fixture
            .executor
            .solve_fp_to_real_observed(&|phase| {
                if matches!(phase, FpRealPhase::RefinementSearch) {
                    refinements.set(refinements.get() + 1);
                }
                if std::mem::discriminant(&phase) == std::mem::discriminant(&target) {
                    calls.set(calls.get() + 1);
                    if calls.get() == boundary {
                        interrupt.store(true, Ordering::Relaxed);
                    }
                }
            })
            .unwrap();
        assert!(result.is_unknown(), "{target:?}");
        assert!(calls.get() >= boundary, "{target:?}");
        assert_eq!(refinements.get(), 0, "{target:?}");
        fixture.revoked(UnknownOrigin::InterruptFlag);
        interrupt.store(false, Ordering::Relaxed);
        assert!(fixture.executor.fp_recorded_resource_stop());
        fixture.public_sat();
    }
}

#[test]
fn actual_sat_callback_stop_survives_reset_at_sat_return() {
    let mut fixture = Fixture::new(EXACT);
    fixture.public_sat();
    let interrupt = Arc::new(AtomicBool::new(false));
    fixture.executor.set_interrupt(Arc::clone(&interrupt));
    let polls = Cell::new(0);
    let returned = Cell::new(0);
    let children = Cell::new(0);
    let result = fixture
        .executor
        .solve_fp_to_real_observed(&|phase| match phase {
            FpRealPhase::SatPoll => {
                polls.set(polls.get() + 1);
                interrupt.store(true, Ordering::Relaxed);
            }
            FpRealPhase::SatReturned => {
                returned.set(returned.get() + 1);
                interrupt.store(false, Ordering::Relaxed);
            }
            FpRealPhase::MixedChild => children.set(children.get() + 1),
            _ => {}
        })
        .unwrap();
    assert!(result.is_unknown());
    assert!(polls.get() > 0, "the actual SAT callback must be reached");
    assert_eq!(returned.get(), 1);
    assert_eq!(children.get(), 0);
    assert!(!interrupt.load(Ordering::Relaxed));
    fixture.revoked(UnknownOrigin::InterruptFlag);
    fixture.public_sat();
}

#[test]
fn forced_to_real_division_stops_inside_construction_before_any_search() {
    let mut fixture = Fixture::new(
        "(set-logic QF_FPLRA)
         (declare-const x (_ FloatingPoint 5 11))
         (declare-const y (_ FloatingPoint 5 11))
         (assert (= (fp.to_real (fp.div RNE x y)) 0.0))",
    );
    let (pure, mixed) = partition_fp_assertions(&fixture.executor.ctx.terms, &fixture.roots);
    assert!(
        pure.is_empty(),
        "the division exists only below the Real site"
    );
    assert_eq!(
        collect_fp_to_real_sites(&fixture.executor.ctx.terms, &mixed).len(),
        1
    );
    let interrupt = Arc::new(AtomicBool::new(false));
    fixture.executor.set_interrupt(Arc::clone(&interrupt));
    let rows = Cell::new(0);
    let clauses = Cell::new(0);
    let counts = Counts::default();
    let result = fixture
        .executor
        .solve_fp_to_real_observed(&|phase| {
            counts.observe(phase);
            if let FpRealPhase::Construction(progress) = phase {
                if progress.stage == FpBuildStage::DivideRow {
                    rows.set(rows.get() + 1);
                    if rows.get() == 4 {
                        clauses.set(progress.clauses);
                        interrupt.store(true, Ordering::Relaxed);
                    }
                }
            }
        })
        .unwrap();
    assert!(result.is_unknown());
    assert_eq!(rows.get(), 4);
    assert!(clauses.get() > 0);
    assert_eq!(counts.searches(), 0);
    assert_eq!(counts.checkpoint.get(), 0);
    fixture.revoked(UnknownOrigin::InterruptFlag);
    interrupt.store(false, Ordering::Relaxed);
    fixture.public_sat();
}

#[test]
fn full_lane_term_memory_entry_refusal_revokes_sat_and_fresh_query_recovers() {
    let mut fixture = Fixture::new(EXACT);
    fixture.public_sat();
    fixture.executor.set_term_memory_limit(Some(0));
    let counts = Counts::default();
    assert!(fixture
        .executor
        .solve_fp_to_real_observed(&|phase| counts.observe(phase))
        .unwrap()
        .is_unknown());
    assert_eq!(counts.searches(), 0);
    assert_eq!(counts.checkpoint.get(), 0);
    fixture.revoked(UnknownOrigin::MemoryBudget);
    fixture.executor.set_term_memory_limit(None);
    fixture.public_sat();
}

#[test]
fn typed_sat_resource_handoff_cannot_start_another_real_search() {
    let mut fixture = Fixture::new(EXACT);
    fixture.public_sat();
    let stop = FpStop::from_executor(&fixture.executor);
    // Explicitly exercise the production result/reason handoff, not purported
    // conflict exhaustion: easy instances can finish before a budgeted conflict.
    fixture.executor.capture_fp_sat_unknown(
        &SatResult::Unknown,
        Some(ay_sat::SatUnknownReason::ResourceBudget),
        &stop,
    );
    let counts = Counts::default();
    let before = ChainSpend {
        conflicts: 7,
        decisions: 11,
    };
    let mut spent = before;
    let result = fixture.executor.solve_fp_sat_controlled(
        &[],
        &[],
        0,
        &mut spent,
        &stop,
        &|phase| counts.observe(phase),
        FpRealPhase::RefinementSearch,
    );
    assert!(matches!(
        result,
        Err(UnknownOrigin::DeterministicResourceBudget)
    ));
    assert_eq!(spent, before);
    assert_eq!(counts.searches(), 0);
    assert!(fixture
        .executor
        .fp_stopped(stop.check().unwrap_err())
        .is_unknown());
    fixture.revoked(UnknownOrigin::DeterministicResourceBudget);
    fixture.public_sat();
}

#[test]
fn checkpoint_detects_live_term_growth_beyond_the_stop_owners_entry_snapshot() {
    let mut executor = Executor::new();
    let _ = executor.ctx.terms.mk_var("seed", Sort::Real);
    let cap = executor.ctx.terms.true_memory_bytes();
    executor.set_term_memory_limit(Some(cap));
    assert!(!executor.term_memory_exceeded());
    let stop = FpStop::from_executor(&executor);
    assert_eq!(stop.check(), Ok(()));
    // Exceed the existing census-refresh threshold, rather than claiming an
    // immediate per-allocation check below that threshold or an RSS ceiling.
    let _ = executor.ctx.terms.mk_var("g".repeat(64 * 1024), Sort::Real);
    assert!(executor.ctx.terms.true_memory_bytes() > cap);
    assert_eq!(
        stop.check(),
        Ok(()),
        "the owner captured only entry admission"
    );
    assert_eq!(
        executor.fp_real_checkpoint(&stop, &|_| {}, FpRealPhase::Rewrite),
        Err(UnknownOrigin::MemoryBudget)
    );
    executor.set_term_memory_limit(None);
    assert_eq!(stop.check(), Err(UnknownOrigin::MemoryBudget));
    let fresh = FpStop::from_executor(&executor);
    assert_eq!(
        executor.fp_real_checkpoint(&fresh, &|_| {}, FpRealPhase::Rewrite),
        Ok(())
    );
}

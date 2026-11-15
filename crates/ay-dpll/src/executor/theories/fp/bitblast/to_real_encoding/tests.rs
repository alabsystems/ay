// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use std::cell::Cell;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use ay_core::{Symbol, TermData};
use ay_fp::FpBuildStage;
use ay_frontend::parse;

use super::super::super::support::partition_fp_assertions;
use super::super::super::to_real::collect_fp_to_real_sites;
use super::*;

#[path = "tests/legacy.rs"]
mod legacy;

fn setup(script: &str) -> Executor {
    let mut executor = Executor::new();
    executor.execute_all(&parse(script).unwrap()).unwrap();
    executor
}

#[test]
fn forced_to_real_site_stops_inside_divider_and_fresh_encoding_matches_legacy() {
    let mut executor = setup(
        "(set-logic QF_FPLRA)
         (declare-const x (_ FloatingPoint 5 11))
         (declare-const y (_ FloatingPoint 5 11))
         (assert (> (fp.to_real (fp.div RNE x y)) 1.0))",
    );
    let roots = executor.ctx.assertions.clone();
    let stamp = executor.ctx.source_context_stamp();
    let (fp, mixed) = partition_fp_assertions(&executor.ctx.terms, &roots);
    assert!(fp.is_empty());
    assert_eq!(mixed.len(), 1);
    let sites = collect_fp_to_real_sites(&executor.ctx.terms, &mixed);
    assert_eq!(sites.len(), 1);
    assert!(matches!(executor.ctx.terms.get(sites[0].arg),
        TermData::App(sym, args) if sym.name() == "fp.div" && args.len() == 3));
    let interrupt = Arc::new(AtomicBool::new(false));
    executor.set_interrupt(Arc::clone(&interrupt));
    let stop = FpStop::from_executor(&executor);
    let rows = Cell::new(0);
    let ready = Cell::new(false);
    let result = executor.encode_fp_assertions_controlled(&fp, &sites, &stop, &|phase| {
        if let FpRealPhase::Construction(progress) = phase {
            if progress.stage == FpBuildStage::DivideRow {
                rows.set(rows.get() + 1);
                if rows.get() == 4 {
                    assert!(progress.clauses > 0);
                    interrupt.store(true, Ordering::Relaxed);
                }
            }
        }
        if matches!(phase, FpRealPhase::EncodingReady) {
            ready.set(true);
        }
    });
    assert!(matches!(
        result,
        Err(FpRealEncodingError::Stopped(UnknownOrigin::InterruptFlag))
    ));
    assert_eq!(rows.get(), 4);
    assert!(!ready.get());
    assert_eq!(executor.ctx.assertions, roots);
    assert_eq!(executor.ctx.source_context_stamp(), stamp);
    // The encoder owns no Executor publication fields and returns no partial
    // artifact. Its caller, tested separately, owns canonical Unknown publication.
    assert!(executor.last_model.is_none());
    interrupt.store(false, Ordering::Relaxed);
    assert!(matches!(
        executor.encode_fp_assertions_controlled(&fp, &sites, &stop, &|_| {
            panic!("the stopped owner must refuse before another observation")
        }),
        Err(FpRealEncodingError::Stopped(UnknownOrigin::InterruptFlag))
    ));
    let fresh = FpStop::from_executor(&executor);
    let actual = executor
        .encode_fp_assertions_controlled(&fp, &sites, &fresh, &|_| {})
        .unwrap();
    assert!(actual.term_to_fp.contains_key(&sites[0].arg));
    assert!(!actual.base_clauses.is_empty());
    let (expected, _, _) = legacy::encode(&executor, &fp, &sites);
    legacy::assert_same(&actual, &expected);
}

fn linked_fixture() -> Executor {
    setup(
        "(set-logic QF_FPLRA)
         (declare-const x (_ FloatingPoint 5 11))
         (declare-const y (_ FloatingPoint 5 11))
         (declare-const b Bool)
         (declare-const r Real)
         (declare-fun f ((_ FloatingPoint 5 11)) Bool)
         (assert b)
         (assert (fp.isZero (ite b x y)))
         (assert (f x))
         (assert (f y))
         (assert (> r 1.0))
         (assert (> (fp.to_real x) r))",
    )
}

#[test]
fn condition_links_precede_congruence_and_real_roots_keep_exact_legacy_encoding() {
    let executor = linked_fixture();
    let (fp, mixed) = partition_fp_assertions(&executor.ctx.terms, &executor.ctx.assertions);
    let sites = collect_fp_to_real_sites(&executor.ctx.terms, &mixed);
    assert_eq!(sites.len(), 1);
    assert!(congruence::scan_foreign(&executor.ctx.terms, &fp).unencodable);
    let (expected, conditions, congruences) = legacy::encode(&executor, &fp, &sites);
    assert!(conditions > 0 && congruences > 0);
    assert!(!expected.congruence_incomplete);
    let stop = FpStop::from_executor(&executor);
    let actual = executor
        .encode_fp_assertions_controlled(&fp, &sites, &stop, &|_| {})
        .unwrap();
    legacy::assert_same(&actual, &expected);
}

#[test]
fn transfer_and_final_admission_refuse_without_publishing_a_partial_encoding() {
    for target in [FpRealPhase::ClauseTransfer, FpRealPhase::EncodingReady] {
        let mut executor = linked_fixture();
        let (fp, mixed) = partition_fp_assertions(&executor.ctx.terms, &executor.ctx.assertions);
        let sites = collect_fp_to_real_sites(&executor.ctx.terms, &mixed);
        let interrupt = Arc::new(AtomicBool::new(false));
        executor.set_interrupt(Arc::clone(&interrupt));
        let stop = FpStop::from_executor(&executor);
        let visits = Cell::new(0);
        let limit = if matches!(target, FpRealPhase::ClauseTransfer) {
            3
        } else {
            1
        };
        let result = executor.encode_fp_assertions_controlled(&fp, &sites, &stop, &|phase| {
            if std::mem::discriminant(&phase) == std::mem::discriminant(&target) {
                visits.set(visits.get() + 1);
                if visits.get() == limit {
                    interrupt.store(true, Ordering::Relaxed);
                }
            }
        });
        assert!(matches!(
            result,
            Err(FpRealEncodingError::Stopped(UnknownOrigin::InterruptFlag))
        ));
        assert_eq!(visits.get(), limit);
        interrupt.store(false, Ordering::Relaxed);
        assert_eq!(stop.check(), Err(UnknownOrigin::InterruptFlag));
        let fresh = FpStop::from_executor(&executor);
        let actual = executor
            .encode_fp_assertions_controlled(&fp, &sites, &fresh, &|_| {})
            .unwrap();
        let (expected, _, _) = legacy::encode(&executor, &fp, &sites);
        legacy::assert_same(&actual, &expected);
    }
}

#[test]
fn unsupported_predicate_and_actual_condition_gap_are_not_resource_stops() {
    let mut executor = Executor::new();
    let terms = &mut executor.ctx.terms;
    let sort = Sort::FloatingPoint(5, 11);
    let x = terms.mk_var("x", sort.clone());
    let y = terms.mk_var("y", sort);
    let unknown = terms.mk_app(Symbol::named("fp.unknown"), [x], Sort::Bool);
    // Non-nullary opaque conditions, unlike a free Bool, are an actual gap
    // when not already represented by the outer Tseitin mapping.
    let opaque = terms.mk_app(Symbol::named("opaque"), [x], Sort::Bool);
    let selected = terms.mk_ite(opaque, x, y);
    let stop = FpStop::from_executor(&executor);
    let (old_unsupported, _, _) = legacy::encode(&executor, &[unknown], &[]);
    assert!(old_unsupported.base_clauses.is_empty());
    assert_eq!(old_unsupported.total_vars, 0);
    assert!(matches!(
        executor.encode_fp_assertions_controlled(&[unknown], &[], &stop, &|_| {}),
        Err(FpRealEncodingError::Unsupported)
    ));
    assert_eq!(stop.check(), Ok(()));
    let (old_gap, _, _) = legacy::encode(&executor, &[], &[FpToRealSite { arg: selected }]);
    assert!(old_gap.base_clauses.is_empty());
    assert_eq!(old_gap.total_vars, 0);
    assert!(old_gap.term_to_fp.contains_key(&selected));
    assert!(matches!(
        executor.encode_fp_assertions_controlled(
            &[],
            &[FpToRealSite { arg: selected }],
            &stop,
            &|_| {}
        ),
        Err(FpRealEncodingError::EncodingGap)
    ));
    assert_eq!(stop.check(), Ok(()));
    // An irrelevant non-FP site remains ignored, not recast as a cancellation
    // or a request to invent an FP decomposition.
    let empty = executor
        .encode_fp_assertions_controlled(&[], &[FpToRealSite { arg: opaque }], &stop, &|_| {})
        .unwrap();
    assert!(empty.term_to_fp.is_empty());
    let (old_empty, _, _) = legacy::encode(&executor, &[], &[FpToRealSite { arg: opaque }]);
    legacy::assert_same(&empty, &old_empty);
}

#[test]
fn zero_term_memory_and_preset_interrupt_refuse_before_tseitin_then_fresh_retry_works() {
    for memory in [false, true] {
        let mut executor = linked_fixture();
        let roots = executor.ctx.assertions.clone();
        let interrupt = Arc::new(AtomicBool::new(!memory));
        executor.set_interrupt(Arc::clone(&interrupt));
        if memory {
            executor.set_term_memory_limit(Some(0));
        }
        let stop = FpStop::from_executor(&executor);
        let origin = if memory {
            UnknownOrigin::MemoryBudget
        } else {
            UnknownOrigin::InterruptFlag
        };
        assert!(
            matches!(executor.encode_fp_assertions_controlled(&roots, &[], &stop, &|_| panic!("entry refused")),
            Err(FpRealEncodingError::Stopped(actual)) if actual == origin)
        );
        executor.set_term_memory_limit(None);
        interrupt.store(false, Ordering::Relaxed);
        assert_eq!(stop.check(), Err(origin));
        let fresh = FpStop::from_executor(&executor);
        assert!(executor
            .encode_fp_assertions_controlled(&roots, &[], &fresh, &|_| {})
            .is_ok());
    }
}

#[test]
fn long_clause_copy_polls_within_256_literals_and_never_appends_its_partial_row() {
    let mut executor = Executor::new();
    let interrupt = Arc::new(AtomicBool::new(false));
    executor.set_interrupt(Arc::clone(&interrupt));
    let stop = FpStop::from_executor(&executor);
    let copied = Cell::new(0);
    let mut destination = vec![CnfClause::unit(1)];
    let literals = (0..1024).map(|index| {
        copied.set(copied.get() + 1);
        if index == 257 {
            interrupt.store(true, Ordering::Relaxed);
        }
        1
    });
    assert_eq!(
        append_clause(&mut destination, literals, &stop, &|_| {}),
        Err(UnknownOrigin::InterruptFlag)
    );
    assert_eq!(copied.get(), 513); // The next periodic check is at index 512.
    assert_eq!(destination, [CnfClause::unit(1)]);
    interrupt.store(false, Ordering::Relaxed);
    assert_eq!(stop.check(), Err(UnknownOrigin::InterruptFlag));
    let fresh = FpStop::from_executor(&executor);
    append_clause(&mut destination, [1; 1024], &fresh, &|_| {}).unwrap();
    assert_eq!(destination[1].literals(), &[1; 1024]);
}

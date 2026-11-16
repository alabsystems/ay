// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::cell::Cell;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

#[test]
fn unsupported_arithmetic_guard_remains_an_encoding_gap() {
    let mut executor = setup(
        "(set-logic ALL) (declare-const i Int)
         (declare-const f (_ FloatingPoint 5 11))
         (declare-const g (_ FloatingPoint 5 11))
         (assert (fp.isZero (ite (< i 0) f g)))",
    );
    assert!(executor.solve_fp_stateless().unwrap().is_unknown());
    assert!(executor.last_model.is_none());
    assert!(!executor.last_model_validated);
}

#[test]
fn malformed_shadowed_and_indexed_predicates_are_not_seeded() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(4));
    let y = terms.mk_var("y", Sort::bitvec(8));
    let z = terms.mk_var("z", Sort::bitvec(4));
    let mismatch = terms.mk_app(Symbol::named("bvult"), [x, y], Sort::Bool);
    let short = terms.mk_app(Symbol::named("bvult"), [x], Sort::Bool);
    let indexed = terms.mk_app(Symbol::indexed("bvult", vec![1]), [x, x], Sort::Bool);
    let shadow = terms.mk_app(Symbol::named("bvule"), [x, z], Sort::Bool);
    terms.register_declared_function("bvule");
    let executor = Executor::new();
    let stop = FpStop::from_executor(&executor);
    let mut tseitin = Tseitin::new(&terms);
    seed(
        &terms,
        [mismatch, short, indexed, shadow],
        &mut tseitin,
        &stop,
        &|| {},
    )
    .unwrap();
    assert_eq!(tseitin.num_vars(), 0);
    assert_eq!(tseitin.take_new_clauses(), [] as [ay_core::CnfClause; 0]);
}

#[test]
fn bound_predicates_are_not_promoted_to_global_boolean_inputs() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("bound", Sort::bitvec(4));
    let y = terms.mk_var("y", Sort::bitvec(4));
    let guard = terms.mk_app(Symbol::named("bvult"), [x, y], Sort::Bool);
    let quantified = terms.mk_forall(vec![("bound".into(), Sort::bitvec(4))], guard);
    let executor = Executor::new();
    let stop = FpStop::from_executor(&executor);
    let mut tseitin = Tseitin::new(&terms);
    seed(&terms, [quantified], &mut tseitin, &stop, &|| {}).unwrap();
    assert!(tseitin.get_var_for_term(guard).is_none());
}

#[test]
fn graph_scan_stop_is_sticky_after_scratch_cleanup() {
    let mut executor = setup(&script(3, 4, "bvult"));
    let flag = Arc::new(AtomicBool::new(false));
    executor.set_interrupt(flag.clone());
    let roots = executor.ctx.assertions.clone();
    let stamp = executor.ctx.source_context_stamp();
    let stop = FpStop::from_executor(&executor);
    let mut tseitin = Tseitin::new(&executor.ctx.terms);
    let visits = Cell::new(0);
    let result = seed(
        &executor.ctx.terms,
        roots.iter().copied(),
        &mut tseitin,
        &stop,
        &|| {
            visits.set(visits.get() + 1);
            if visits.get() == 4 {
                flag.store(true, Ordering::Relaxed);
            }
        },
    );
    assert_eq!(result, Err(UnknownOrigin::InterruptFlag));
    assert_eq!(visits.get(), 4);
    drop(tseitin);
    flag.store(false, Ordering::Relaxed);
    let mut retry = Tseitin::new(&executor.ctx.terms);
    assert_eq!(
        seed(
            &executor.ctx.terms,
            roots.iter().copied(),
            &mut retry,
            &stop,
            &|| panic!("a refused owner must not resume")
        ),
        Err(UnknownOrigin::InterruptFlag)
    );
    drop(retry);
    assert_eq!(executor.ctx.assertions, roots);
    assert_eq!(executor.ctx.source_context_stamp(), stamp);
    assert!(executor.last_model.is_none());
    assert!(executor.last_proof.is_none());
}

#[test]
fn already_cancelled_public_fp_attempt_cannot_publish_a_model() {
    let mut executor = setup(&script(3, 4, "bvult"));
    let flag = Arc::new(AtomicBool::new(true));
    executor.set_interrupt(flag);
    let result = executor
        .execute_all(&parse("(check-sat)").unwrap())
        .unwrap();
    assert_eq!(result, ["unknown"]);
    assert!(executor.last_model.is_none());
    assert!(!executor.last_model_validated);
}

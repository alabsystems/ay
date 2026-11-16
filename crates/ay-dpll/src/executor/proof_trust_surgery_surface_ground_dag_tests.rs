// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn term(text: &str) -> Term {
    let commands = ay_frontend::parse(&format!("(assert {text})")).unwrap();
    let ay_frontend::Command::Assert(term) = &commands[0] else {
        panic!("assertion");
    };
    term.clone()
}

#[test]
fn sharing_is_exact_closed_source_syntax_not_canonical_equality() {
    let source = term("(and (= (select a (bvadd x #x00)) (select a x)) (= (select a (bvadd x #x00)) (select a x)))");
    let mut context = Context::new();
    for command in ay_frontend::parse(
        "(declare-const x (_ BitVec 8))
         (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))",
    )
    .unwrap()
    {
        context.process_command(&command).unwrap();
    }
    let plan = Plan::new(&source, &mut context, |_| false).unwrap();
    let Term::App(_, conjuncts) = &source else {
        panic!("and");
    };
    assert_eq!(
        plan.typed.node_index(&context, &conjuncts[0]),
        plan.typed.node_index(&context, &conjuncts[1])
    );
    let Term::App(_, sides) = &conjuncts[0] else {
        panic!("equality");
    };
    assert_ne!(
        plan.typed.node_index(&context, &sides[0]),
        plan.typed.node_index(&context, &sides[1])
    );
    assert_eq!(
        plan.canonical(&context, &sides[0])
            .expect("typed offset read"),
        plan.canonical(&context, &sides[1])
            .expect("typed plain read"),
        "x+0 and x fold canonically while the original read syntax stays distinct"
    );
}

#[test]
fn shared_source_keeps_existing_depth_token_and_macro_refusals() {
    let mut context = Context::new();
    for command in ay_frontend::parse("(define-fun alias () (_ BitVec 8) #x00)").unwrap() {
        context.process_command(&command).unwrap();
    }
    for source in [
        term("(= alias #x00)"),
        term("(forall ((x Bool)) x)"),
        Term::Symbol("x".repeat(4097)),
    ] {
        assert!(Plan::new(&source, &mut context, |_| false).is_none());
    }
    let mut source = Term::Symbol("x".into());
    for _ in 0..97 {
        source = Term::App("bvnot".into(), vec![source]);
    }
    assert!(Plan::new(&source, &mut context, |_| false).is_none());
}

#[test]
fn shared_source_does_not_raise_the_distinct_node_limit() {
    let leaves = (0..16_384)
        .map(|index| Term::Symbol(format!("p{index}")))
        .collect::<Vec<_>>();
    let children = leaves
        .chunks(128)
        .map(|chunk| Term::App("and".into(), chunk.to_vec()))
        .collect();
    let source = Term::App("and".into(), children);
    assert!(Plan::new(&source, &mut Context::new(), |_| false).is_none());
}

#[test]
fn shared_raw_rebuild_retains_source_and_declared_head_identity() {
    let mut executor = crate::executor::Executor::new();
    for command in ay_frontend::parse(
        "(declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
         (declare-const x (_ BitVec 8))
         (declare-fun rem ((_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))",
    )
    .unwrap()
    {
        executor.execute(&command).unwrap();
    }
    let source = term("(and (= (select (store a x (rem x x)) x) (rem x x)) (= (select (store a x (rem x x)) x) (rem x x)))");
    let canonical = executor.ctx.elaborate_surface_subterm(&source).unwrap();
    let ordinary_raw = executor.raw_intern_surface(&source).unwrap();
    let shared_raw = executor
        .raw_intern_shared_ground_memory_surface(&source)
        .unwrap();
    assert_eq!(shared_raw, ordinary_raw);
    assert_ne!(
        shared_raw, canonical,
        "canonical folding cannot replace the authored raw root"
    );
    let private = executor
        .ctx
        .symbol_info("rem")
        .unwrap()
        .internal_name
        .as_ref()
        .unwrap();
    let mut pending = vec![shared_raw];
    let mut found = false;
    while let Some(term) = pending.pop() {
        if let ay_core::TermData::App(head, _) = executor.ctx.terms.get(term) {
            assert_ne!(head.name(), "rem");
            found |= head.name() == private;
        }
        pending.extend(executor.ctx.terms.children(term));
    }
    assert!(found);
}

#[test]
fn shared_raw_rebuild_observes_existing_interrupt_and_term_memory_ceiling() {
    use std::sync::{atomic::AtomicBool, Arc};
    let mut executor = crate::executor::Executor::new();
    for command in
        ay_frontend::parse("(declare-const a (Array (_ BitVec 8) (_ BitVec 8)))").unwrap()
    {
        executor.execute(&command).unwrap();
    }
    let source = term("(= (select a #x00) #x00)");
    executor.set_interrupt(Arc::new(AtomicBool::new(true)));
    assert!(executor
        .raw_intern_shared_ground_memory_surface(&source)
        .is_none());
    executor.set_interrupt(Arc::new(AtomicBool::new(false)));
    executor.set_term_memory_limit(Some(0));
    assert!(executor
        .raw_intern_shared_ground_memory_surface(&source)
        .is_none());
}

#[test]
fn no_select_decline_leaves_live_arrays_unchanged_across_ordinary_solve_and_pop() {
    use crate::executor::Executor;
    let mut executor = Executor::new();
    executor
        .execute_all(
            &ay_frontend::parse(
                "(set-option :produce-proofs true)
                 (set-logic QF_AUFBV)
                 (declare-const A (Array (_ BitVec 8) (_ BitVec 8)))
                 (declare-const B (Array (_ BitVec 8) (_ BitVec 8)))
                 (declare-const k (_ BitVec 8))
                 (declare-const v (_ BitVec 8))
                 (assert (= (ite true A (store B k v)) A))",
            )
            .unwrap(),
        )
        .unwrap();
    let source = executor.ctx.assertions_parsed()[0].clone();
    let before = (
        executor.ctx.terms.len(),
        executor.ctx.terms.checker_visible_metadata_generation(),
        executor.ctx.terms.var_counter(),
    );
    let source_context = executor.ctx.source_context_stamp();
    assert!(executor
        .raw_intern_shared_ground_memory_surface(&source)
        .is_none());
    assert_eq!(
        before,
        (
            executor.ctx.terms.len(),
            executor.ctx.terms.checker_visible_metadata_generation(),
            executor.ctx.terms.var_counter(),
        ),
        "a no-select decline must not elaborate its untaken store in the live arena"
    );
    assert_eq!(source_context, executor.ctx.source_context_stamp());
    assert_eq!(
        executor.last_proof_raw_original_assertions,
        [] as [TermId; 0]
    );
    assert!(executor.last_proof().is_none());
    assert_eq!(
        executor
            .execute_all(&ay_frontend::parse("(check-sat)").unwrap())
            .unwrap(),
        ["sat"]
    );
    // The same store is now a genuine assertion in an owned scope, rather
    // than an untaken source branch admitted by a declined proof planner.
    assert_eq!(
        executor
            .execute_all(
                &ay_frontend::parse("(push 1)(assert (= A (store B k v)))(check-sat)",).unwrap(),
            )
            .unwrap(),
        ["sat"]
    );
    assert_eq!(
        executor
            .execute_all(
                &ay_frontend::parse("(assert (not (= A (store B k v))))(check-sat)").unwrap(),
            )
            .unwrap(),
        ["unsat"]
    );
    assert!(executor
        .check_proof_strict_with_datatypes(executor.last_proof().expect("actual scoped proof"))
        .unwrap()
        .is_complete());
    assert_eq!(
        executor
            .execute_all(&ay_frontend::parse("(pop 1)(check-sat)").unwrap())
            .unwrap(),
        ["sat"]
    );
    assert!(executor.last_proof().is_none());
    assert!(executor.last_unsat_certificate.is_none());
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Phase 0.5 of model completion (#uninterpreted-bitvec-class-values).

use ay_bv::BvModel;
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::Symbol;
use ay_core::{Sort, TermId};
use ay_euf::EufModel;
use num_bigint::BigInt;

use super::super::{EvalValue, Executor, Model};
use crate::executor_types::SolveResult;

const WIDTH: u32 = 8;

mod ownership;

fn bv(executor: &mut Executor, value: u8) -> TermId {
    executor.ctx.terms.mk_bitvec(BigInt::from(value), WIDTH)
}

/// A witness of a route with no BV model, whose EUF spelled `term` as
/// `spelled`.
fn euf_witness(spelled: &[(TermId, &str)]) -> Model {
    let mut model = Model::empty();
    model.euf_model = Some(EufModel {
        term_values: spelled
            .iter()
            .map(|&(term, value)| (term, value.to_string()))
            .collect(),
        ..EufModel::default()
    });
    model
}

/// Complete `model` over `assertions` and return the completed witness.
fn complete(executor: &mut Executor, assertions: Vec<TermId>, model: Model) -> Model {
    executor.ctx.assertions = assertions;
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(model);
    executor.complete_model_for_validation(&[]);
    executor.last_model.take().expect("completed model")
}

fn value_of(executor: &Executor, model: &Model, term: TermId) -> EvalValue {
    executor.evaluate_term(model, term)
}

fn bitvec(value: u8) -> EvalValue {
    EvalValue::BitVec {
        value: BigInt::from(value),
        width: WIDTH,
    }
}

/// The measured trigger: EUF put `b` apart from `#x00`, phase 1 used to give
/// it 0 anyway, and the lane's own validation refused the witness.
#[test]
fn a_committed_disequality_keeps_the_euf_class_value() {
    let mut executor = Executor::new();
    let b = executor.ctx.terms.mk_var("b", Sort::bitvec(WIDTH));
    let zero = bv(&mut executor, 0);
    let equal = executor.ctx.terms.mk_eq(b, zero);
    let apart = executor.ctx.terms.mk_not(equal);
    let model = complete(
        &mut executor,
        vec![apart],
        euf_witness(&[(b, "#x01"), (zero, "#x00")]),
    );
    assert_eq!(value_of(&executor, &model, b), bitvec(1));
    assert_eq!(value_of(&executor, &model, apart), EvalValue::Bool(true));
    assert_eq!(
        executor
            .last_statistics
            .get_int("model_completion.bv_class_values"),
        Some(1)
    );
}

/// A nested atom counts with the value the SAT model committed to it.
#[test]
fn a_nested_atom_is_checked_against_its_sat_value() {
    let mut executor = Executor::new();
    let b = executor.ctx.terms.mk_var("b", Sort::bitvec(WIDTH));
    let p = executor.ctx.terms.mk_var("p", Sort::Bool);
    let zero = bv(&mut executor, 0);
    let equal = executor.ctx.terms.mk_eq(b, zero);
    let apart = executor.ctx.terms.mk_not(equal);
    let root = executor.ctx.terms.mk_or(vec![p, apart]);
    let mut witness = euf_witness(&[(b, "#x01")]);
    witness.term_to_var = HashMap::from_iter([(equal, 0), (p, 1)]);
    witness.sat_model = vec![false, false];
    let model = complete(&mut executor, vec![root], witness);
    assert_eq!(value_of(&executor, &model, b), bitvec(1));
    assert_eq!(value_of(&executor, &model, root), EvalValue::Bool(true));
}

/// EUF knew `bvult` only as an uninterpreted predicate: a class value that
/// falsifies a committed `bvult` atom is withdrawn, and phase 1 defaults the
/// variable as before.
#[test]
fn a_class_value_an_atom_refutes_is_withdrawn() {
    let mut executor = Executor::new();
    let b = executor.ctx.terms.mk_var("b", Sort::bitvec(WIDTH));
    let five = bv(&mut executor, 5);
    let above = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bvult"), vec![five, b], Sort::Bool);
    let model = complete(&mut executor, vec![above], euf_witness(&[(b, "#x01")]));
    assert_eq!(value_of(&executor, &model, b), bitvec(0));
    assert_eq!(
        executor
            .last_statistics
            .get_int("model_completion.bv_class_values"),
        None
    );
}

/// An atom with no committed value cannot confirm an offer.
#[test]
fn an_atom_with_no_committed_value_confirms_nothing() {
    let mut executor = Executor::new();
    let b = executor.ctx.terms.mk_var("b", Sort::bitvec(WIDTH));
    let p = executor.ctx.terms.mk_var("p", Sort::Bool);
    let zero = bv(&mut executor, 0);
    let equal = executor.ctx.terms.mk_eq(b, zero);
    let apart = executor.ctx.terms.mk_not(equal);
    let root = executor.ctx.terms.mk_or(vec![p, apart]);
    let model = complete(&mut executor, vec![root], euf_witness(&[(b, "#x01")]));
    assert_eq!(value_of(&executor, &model, b), bitvec(0));
}

/// Withdrawal reaches a fixpoint: `c` shares an atom with the refuted `b`, so
/// its offer goes too, and the two default together.
#[test]
fn withdrawing_one_offer_withdraws_its_atom_partners() {
    let mut executor = Executor::new();
    let b = executor.ctx.terms.mk_var("b", Sort::bitvec(WIDTH));
    let c = executor.ctx.terms.mk_var("c", Sort::bitvec(WIDTH));
    let five = bv(&mut executor, 5);
    let above = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bvult"), vec![five, b], Sort::Bool);
    let same = executor.ctx.terms.mk_eq(b, c);
    let model = complete(
        &mut executor,
        vec![above, same],
        euf_witness(&[(b, "#x01"), (c, "#x01")]),
    );
    assert_eq!(value_of(&executor, &model, b), bitvec(0));
    assert_eq!(value_of(&executor, &model, c), bitvec(0));
}

/// A route with a BV model owns its bits: the EUF spelling is never read.
#[test]
fn a_witness_with_a_bv_model_is_untouched() {
    let mut executor = Executor::new();
    let b = executor.ctx.terms.mk_var("b", Sort::bitvec(WIDTH));
    let zero = bv(&mut executor, 0);
    let equal = executor.ctx.terms.mk_eq(b, zero);
    let apart = executor.ctx.terms.mk_not(equal);
    let mut witness = euf_witness(&[(b, "#x01")]);
    witness.bv_model = Some(BvModel {
        values: HashMap::default(),
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });
    let model = complete(&mut executor, vec![apart], witness);
    assert_eq!(value_of(&executor, &model, b), bitvec(0));
}

/// A substitution key is defined by its right-hand side, never offered.
#[test]
fn a_substitution_key_is_not_offered() {
    let mut executor = Executor::new();
    let b = executor.ctx.terms.mk_var("b", Sort::bitvec(WIDTH));
    let source = executor.ctx.terms.mk_var("source", Sort::bitvec(WIDTH));
    let defining = executor
        .ctx
        .terms
        .mk_app(Symbol::named("="), vec![b, source], Sort::Bool);
    executor.recorded_var_substitutions.insert(b, source);
    let model = complete(
        &mut executor,
        vec![defining],
        euf_witness(&[(b, "#x07"), (source, "#x03")]),
    );
    let key = value_of(&executor, &model, b);
    assert_ne!(key, bitvec(7), "the key's own EUF spelling was offered");
    assert_eq!(key, value_of(&executor, &model, source));
}

#[test]
fn independently_false_uf_interpretation_withdraws_every_offer() {
    for (published_else, kept) in [("#x00", 1), ("#x01", 0)] {
        let mut executor = Executor::new();
        let commands = ay_frontend::parse("(declare-fun f ((_ BitVec 8)) (_ BitVec 8))")
            .expect("function declaration");
        executor.execute_all(&commands).expect("declare f");
        let b = executor.ctx.terms.mk_var("b", Sort::bitvec(WIDTH));
        let zero = bv(&mut executor, 0);
        let equal = executor.ctx.terms.mk_eq(b, zero);
        let apart = executor.ctx.terms.mk_not(equal);
        let application =
            executor
                .ctx
                .terms
                .mk_app(Symbol::named("f"), vec![b], Sort::bitvec(WIDTH));
        let root = executor.ctx.terms.mk_eq(application, zero);
        executor.ctx.assertions = vec![apart, root];
        let mut model = euf_witness(&[(b, "#x01"), (application, "#x00")]);
        let euf = model.euf_model.as_mut().expect("euf witness");
        euf.func_app_const_terms.insert(application, zero);
        // The local evaluator matches exact table points before per-term pins.
        // Keep b's offered #x01 unlisted so it reads the application pin #x00.
        // The independent evaluator reads the PUBLISHED total interpretation:
        // its last row supplies the else value, even at an unlisted point.
        euf.function_tables.insert(
            "f".into(),
            vec![(vec!["#x02".into()], published_else.into())],
        );
        Executor::insert_completed_value(&executor.ctx.terms, &mut model, b, &bitvec(1));
        assert_eq!(value_of(&executor, &model, root), EvalValue::Bool(true));
        {
            let mut owner = super::CandidateOwner::capture(&executor).unwrap();
            let index = executor
                .bitvec_atom_index(&[apart, root], &mut owner)
                .unwrap();
            let offered = [b].into_iter().collect();
            assert_eq!(
                executor
                    .offers_an_atom_refuses(&model, &index, &offered, &mut owner)
                    .unwrap(),
                [] as [TermId; 0]
            );
        }
        assert_eq!(
            executor
                .independent_evaluator_refutes(&model, &[root])
                .unwrap(),
            kept == 0
        );
        model.completed_values.remove(&b);
        crate::executor::model::eval_memo_clear();
        assert_eq!(
            executor.complete_uninterpreted_bitvec_values(&mut model, &[], &Default::default()),
            Ok(kept)
        );
        assert_eq!(model.completed_values.contains_key(&b), kept == 1);
    }
}

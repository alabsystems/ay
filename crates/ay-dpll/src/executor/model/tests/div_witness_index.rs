// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use super::*;

#[test]
fn div_witness_index_is_exact_snapshot_keyed_and_bounded() {
    let mut exec = Executor::new();
    let dividend = exec.ctx.terms.mk_int(BigInt::from(7));
    let divisor = exec.ctx.terms.mk_int(BigInt::from(0));
    let literal = exec
        .ctx
        .terms
        .mk_var(format!("__ay_zerodiv_div_{}", dividend.index()), Sort::Int);
    let symbolic = exec.ctx.terms.mk_var(
        format!("__ay_symdiv_q_{}_{}", dividend.index(), divisor.index()),
        Sort::Int,
    );
    // A reserved-name lookalike at the wrong sort is never model evidence.
    let _wrong_sort = exec
        .ctx
        .terms
        .mk_var(format!("__ay_zerodiv_mod_{}", dividend.index()), Sort::Bool);

    let first = exec.div_witness_index_cache.index(&exec.ctx.terms);
    assert_eq!(exec.div_witness_index_cache.build_count(), 1);
    assert_eq!(
        first.candidates(DivWitnessFamily::LiteralDiv),
        &[DivWitnessCandidate {
            witness: literal,
            dividend,
            divisor: None,
        }]
    );
    assert_eq!(
        first.candidates(DivWitnessFamily::SymbolicQuotient),
        &[DivWitnessCandidate {
            witness: symbolic,
            dividend,
            divisor: Some(divisor),
        }]
    );
    assert!(first.candidates(DivWitnessFamily::LiteralMod).is_empty());

    let same_snapshot = exec.div_witness_index_cache.index(&exec.ctx.terms);
    assert!(Arc::ptr_eq(&first, &same_snapshot));
    assert_eq!(
        exec.div_witness_index_cache.build_count(),
        1,
        "an immutable snapshot is indexed at most once"
    );

    let checkpoint = exec.ctx.terms.rollback_checkpoint();
    let appended = exec
        .ctx
        .terms
        .mk_var(format!("__ay_zerodiv_mod_{}", dividend.index()), Sort::Int);
    let after_append = exec.div_witness_index_cache.index(&exec.ctx.terms);
    assert_eq!(exec.div_witness_index_cache.build_count(), 2);
    assert_eq!(
        after_append.candidates(DivWitnessFamily::LiteralMod),
        &[DivWitnessCandidate {
            witness: appended,
            dividend,
            divisor: None,
        }]
    );

    exec.ctx.terms.rollback_to(checkpoint);
    let after_rollback = exec.div_witness_index_cache.index(&exec.ctx.terms);
    assert_eq!(exec.div_witness_index_cache.build_count(), 3);
    assert!(after_rollback
        .candidates(DivWitnessFamily::LiteralMod)
        .is_empty());

    // Replacement can preserve both length and contents. The opaque physical
    // store identity must still retire the predecessor index.
    let replacement = exec.ctx.terms.clone();
    exec.ctx.terms = replacement;
    let after_replacement = exec.div_witness_index_cache.index(&exec.ctx.terms);
    assert_eq!(exec.div_witness_index_cache.build_count(), 4);
    assert!(!Arc::ptr_eq(&after_rollback, &after_replacement));
    assert_eq!(
        after_replacement.candidates(DivWitnessFamily::LiteralDiv),
        first.candidates(DivWitnessFamily::LiteralDiv)
    );
}

#[test]
fn cached_div_witness_lookup_remains_value_keyed_reentrant_and_model_fresh() {
    let mut exec = Executor::new();
    let seven = exec.ctx.terms.mk_int(BigInt::from(7));
    let zero = exec.ctx.terms.mk_int(BigInt::from(0));
    let inner_div = exec.ctx.terms.mk_intdiv(seven, zero);
    // Deliberately key the witness by a DIFFERENT term whose model value is
    // seven. Elimination can rewrite operands before naming the witness, so
    // lookup must remain value-keyed rather than switching to TermId equality.
    let rewritten_seven = exec.ctx.terms.mk_var("rewritten_seven", Sort::Int);
    let inner_witness = exec.ctx.terms.mk_var(
        format!("__ay_zerodiv_div_{}", rewritten_seven.index()),
        Sort::Int,
    );
    let outer_div = exec.ctx.terms.mk_intdiv(inner_div, zero);
    let outer_witness = exec
        .ctx
        .terms
        .mk_var(format!("__ay_zerodiv_div_{}", inner_div.index()), Sort::Int);

    let mut values = HashMap::default();
    values.insert(rewritten_seven, BigInt::from(7));
    values.insert(inner_witness, BigInt::from(3));
    values.insert(outer_witness, BigInt::from(5));
    let mut model = empty_model();
    model.lia_model = Some(LiaModel { values });

    let _outer_memo = EvalMemoSession::new();
    assert_eq!(
        exec.evaluate_term(&model, outer_div),
        EvalValue::Rational(BigRational::from_integer(BigInt::from(5)))
    );
    assert_eq!(
        exec.div_witness_index_cache.build_count(),
        1,
        "reentrant evaluation of the inner dividend reuses the structural index"
    );

    {
        let _nested_memo = EvalMemoSession::new();
        eval_memo_clear();
        assert_eq!(
            exec.evaluate_term(&model, outer_div),
            EvalValue::Rational(BigRational::from_integer(BigInt::from(5)))
        );
    }
    assert_eq!(
        exec.div_witness_index_cache.build_count(),
        1,
        "a nested memo session may force fresh value evaluation without rescanning structure"
    );

    // Evaluated values do not live in the structural cache. The ordinary memo
    // clear after a model mutation exposes the new choice without rescanning
    // the unchanged TermStore.
    model
        .lia_model
        .as_mut()
        .expect("fixture has an LIA model")
        .values
        .insert(outer_witness, BigInt::from(11));
    eval_memo_clear();
    assert_eq!(
        exec.evaluate_term(&model, outer_div),
        EvalValue::Rational(BigRational::from_integer(BigInt::from(11)))
    );
    assert_eq!(exec.div_witness_index_cache.build_count(), 1);
}

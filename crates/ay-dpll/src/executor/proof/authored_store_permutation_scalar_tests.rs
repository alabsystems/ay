// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_frontend::command::Term as FrontendTerm;
use ay_frontend::parse;

fn assert_no_trust(proof: &Proof) {
    assert!(proof.steps.iter().all(|step| match step {
        ProofStep::Step {
            rule: AletheRule::Trust,
            ..
        } => false,
        ProofStep::TheoryLemma { kind, .. } if kind.is_trust() => false,
        _ => true,
    }));
}

#[test]
fn scalar_aliased_select_witness_has_a_strict_native_proof() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun v1 () Int)
        (declare-fun v2 () Int)
        (declare-fun v3 () Int)
        (declare-fun lhs () (Array Int Int))
        (declare-fun rhs () (Array Int Int))
        (declare-fun k () Int)
        (declare-fun e1 () Int)
        (declare-fun e2 () Int)
        (assert (= lhs (store (store (store a 1 v1) 2 v2) 3 v3)))
        (assert (= rhs (store (store (store a 3 v3) 1 v1) 2 v2)))
        (assert (= e1 (select lhs k)))
        (assert (= e2 (select rhs k)))
        (assert (not (= e1 e2)))
        (check-sat)
        "#;
    let commands = parse(input).expect("fixture parses");
    let mut exec = Executor::new();
    assert_eq!(
        exec.execute_all(&commands).expect("fixture executes"),
        vec!["unsat"]
    );
    let proof = exec.last_proof.as_ref().expect("UNSAT retains its proof");
    exec.check_proof_strict_with_datatypes(proof)
        .expect("scalar alias transport is strict-checkable");
    assert!(
        proof
            .steps
            .iter()
            .filter(|step| matches!(
                step,
                ProofStep::TheoryLemma {
                    kind: TheoryLemmaKind::EufTransitive,
                    ..
                }
            ))
            .count()
            >= 2
    );
    assert!(proof.steps.iter().any(|step| matches!(
        step,
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::ArrayRowChain,
            ..
        }
    )));
    assert!(proof.steps.iter().all(|step| !matches!(
        step,
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::ArrayStorePermutation | TheoryLemmaKind::LiaGeneric,
            ..
        }
    )));
    assert_no_trust(proof);

    let strict_input = input.replacen(
        "(set-option :produce-proofs true)",
        "(set-option :produce-proofs true)\n        (set-option :check-proofs-strict true)",
        1,
    );
    let strict_commands = parse(&strict_input).expect("strict fixture parses");
    let mut strict_exec = Executor::new();
    assert_eq!(
        strict_exec
            .execute_all(&strict_commands)
            .expect("strict fixture executes"),
        vec!["unknown"]
    );
    assert_eq!(
        strict_exec.unknown_reason(),
        Some(crate::UnknownReason::ProofTrusted)
    );
}

#[test]
fn scalar_aliased_select_witness_with_support_difference_stays_sat() {
    let commands = parse(
        r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun v1 () Int)
        (declare-fun v2 () Int)
        (declare-fun lhs () (Array Int Int))
        (declare-fun rhs () (Array Int Int))
        (declare-fun k () Int)
        (declare-fun e1 () Int)
        (declare-fun e2 () Int)
        (assert (= lhs (store a 1 v1)))
        (assert (= rhs (store (store a 1 v1) 2 v2)))
        (assert (= e1 (select lhs k)))
        (assert (= e2 (select rhs k)))
        (assert (not (= e1 e2)))
        (check-sat)
        "#,
    )
    .expect("fixture parses");
    let mut exec = Executor::new();
    let output = exec.execute_all(&commands).expect("fixture executes");
    assert_ne!(
        output,
        vec!["unsat"],
        "the unequal store supports admit a real select difference; model validation may prove \
         SAT or fail closed as Unknown, but reconstruction must never claim UNSAT"
    );
}

struct RawScalarFixture {
    exec: Executor,
    index_disequality: TermId,
}

fn raw_store(
    exec: &mut Executor,
    array: TermId,
    index: TermId,
    value: TermId,
    sort: &Sort,
) -> TermId {
    exec.ctx
        .terms
        .mk_app(Symbol::named("store"), [array, index, value], sort.clone())
}

fn raw_symbolic_scalar_fixture() -> RawScalarFixture {
    let mut exec = Executor::new();
    let array_sort = Sort::array(Sort::Int, Sort::Int);
    let base = exec.ctx.terms.mk_var("raw_scalar_base", array_sort.clone());
    let lhs = exec.ctx.terms.mk_var("raw_scalar_lhs", array_sort.clone());
    let rhs = exec.ctx.terms.mk_var("raw_scalar_rhs", array_sort.clone());
    let i = exec.ctx.terms.mk_var("raw_scalar_i", Sort::Int);
    let j = exec.ctx.terms.mk_var("raw_scalar_j", Sort::Int);
    let vi = exec.ctx.terms.mk_var("raw_scalar_vi", Sort::Int);
    let vj = exec.ctx.terms.mk_var("raw_scalar_vj", Sort::Int);
    let k = exec.ctx.terms.mk_var("raw_scalar_k", Sort::Int);
    let e1 = exec.ctx.terms.mk_var("raw_scalar_e1", Sort::Int);
    let e2 = exec.ctx.terms.mk_var("raw_scalar_e2", Sort::Int);
    let left_inner = raw_store(&mut exec, base, i, vi, &array_sort);
    let left_chain = raw_store(&mut exec, left_inner, j, vj, &array_sort);
    let right_inner = raw_store(&mut exec, base, j, vj, &array_sort);
    let right_chain = raw_store(&mut exec, right_inner, i, vi, &array_sort);
    assert_ne!(left_chain, right_chain);
    let left_array = exec.ctx.terms.mk_eq(lhs, left_chain);
    let right_array = exec.ctx.terms.mk_eq(rhs, right_chain);
    let index_equality = exec
        .ctx
        .terms
        .mk_app(Symbol::named("="), [j, i], Sort::Bool);
    let index_disequality = exec.ctx.terms.mk_not_raw(index_equality);
    let left_select = exec.ctx.terms.mk_select(lhs, k);
    let right_select = exec.ctx.terms.mk_select(rhs, k);
    let left_scalar = exec.ctx.terms.mk_eq(e1, left_select);
    let right_scalar = exec.ctx.terms.mk_eq(e2, right_select);
    let scalar_equality = exec.ctx.terms.mk_eq(e1, e2);
    let conflict = exec.ctx.terms.mk_not_raw(scalar_equality);
    for root in [
        left_array,
        right_array,
        index_disequality,
        left_scalar,
        right_scalar,
        conflict,
    ] {
        exec.ctx
            .add_assertion_with_parsed(root, FrontendTerm::Symbol("raw_scalar".to_string()));
    }
    RawScalarFixture {
        exec,
        index_disequality,
    }
}

#[test]
fn raw_symbolic_scalar_aliases_use_store_permutation() {
    let RawScalarFixture {
        mut exec,
        index_disequality,
    } = raw_symbolic_scalar_fixture();
    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Trust, Vec::new(), Vec::new(), Vec::new());
    exec.replace_with_exact_authored_store_permutation_refutation(&mut proof);
    assert!(Executor::proof_derives_empty_clause(&proof));
    exec.check_proof_strict_with_datatypes(&proof)
        .expect("symbolic scalar composition is strict-checkable");
    assert!(proof
        .steps
        .iter()
        .any(|step| matches!(step, ProofStep::Assume(root) if *root == index_disequality)));
    for expected in [
        TheoryLemmaKind::ArrayStorePermutation,
        TheoryLemmaKind::ArrayRowChain,
    ] {
        assert!(proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::TheoryLemma { kind, .. } if *kind == expected
        )));
    }
    assert!(
        proof
            .steps
            .iter()
            .filter(|step| matches!(
                step,
                ProofStep::TheoryLemma {
                    kind: TheoryLemmaKind::EufTransitive,
                    ..
                }
            ))
            .count()
            >= 2
    );
    assert_no_trust(&proof);
}

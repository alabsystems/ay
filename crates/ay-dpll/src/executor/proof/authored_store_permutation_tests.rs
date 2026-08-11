// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::alias_index::AuthoredIndex;
use super::*;
use ay_frontend::command::Term as FrontendTerm;
use ay_frontend::parse;

#[test]
fn aliased_store_permutation_select_conflict_has_a_strict_native_proof() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-option :check-proofs-strict true)
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun e1 () Int)
        (declare-fun e2 () Int)
        (declare-fun k () Int)
        (declare-fun lhs () (Array Int Int))
        (declare-fun rhs () (Array Int Int))
        (declare-fun sk ((Array Int Int) (Array Int Int)) Int)
        (assert (= lhs (store (store a 1 e1) 2 e2)))
        (assert (= rhs (store (store a 2 e2) 1 e1)))
        (assert (= k (sk lhs rhs)))
        (assert (not (= (select lhs k) (select rhs k))))
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
        .expect("the reconstructed proof is strict-checkable");
    assert!(proof.steps.iter().all(|step| !matches!(
        step,
        ProofStep::TheoryLemma { kind, .. } if kind.is_trust()
    )));
    for expected in [
        TheoryLemmaKind::EufTransitive,
        TheoryLemmaKind::ArrayRowChain,
    ] {
        assert!(proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::TheoryLemma { kind, .. } if *kind == expected
        )));
    }
    assert!(proof.steps.iter().all(|step| !matches!(
        step,
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::ArrayStorePermutation | TheoryLemmaKind::LiaGeneric,
            ..
        }
    )));
}

#[test]
fn raw_ill_sorted_alias_binding_cannot_replace_a_proof() {
    let mut exec = Executor::new();
    let array_sort = Sort::array(Sort::Int, Sort::Int);
    let lhs = exec.ctx.terms.mk_var("raw_bad_lhs", array_sort.clone());
    let rhs = exec.ctx.terms.mk_var("raw_bad_rhs", array_sort.clone());
    let chain = exec.ctx.terms.mk_var("raw_bad_chain", array_sort);
    let wrong_chain = exec.ctx.terms.mk_var("raw_bad_int", Sort::Int);
    let index = exec.ctx.terms.mk_var("raw_bad_index", Sort::Int);

    // `mk_app` deliberately permits a raw malformed term. The left binding's
    // endpoints have different sorts, so it must not authorize alias transfer.
    let ill_sorted_binding =
        exec.ctx
            .terms
            .mk_app(Symbol::named("="), [lhs, wrong_chain], Sort::Bool);
    let right_binding = exec
        .ctx
        .terms
        .mk_app(Symbol::named("="), [rhs, chain], Sort::Bool);
    let left_select = exec.ctx.terms.mk_select(lhs, index);
    let right_select = exec.ctx.terms.mk_select(rhs, index);
    let select_equality =
        exec.ctx
            .terms
            .mk_app(Symbol::named("="), [left_select, right_select], Sort::Bool);
    let select_conflict = exec.ctx.terms.mk_not_raw(select_equality);
    for root in [ill_sorted_binding, right_binding, select_conflict] {
        exec.ctx
            .add_assertion_with_parsed(root, FrontendTerm::Symbol("raw_bad".to_string()));
    }

    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Trust, Vec::new(), Vec::new(), Vec::new());
    let before = format!("{:?}", proof.steps);
    exec.replace_with_exact_authored_store_permutation_refutation(&mut proof);
    assert_eq!(format!("{:?}", proof.steps), before);
}

#[test]
fn authored_alias_index_keeps_only_relevant_ordered_bindings() {
    let mut terms = TermStore::new();
    let array_sort = Sort::array(Sort::Int, Sort::Int);
    let alias = terms.mk_var("indexed_alias", array_sort.clone());
    let chain = terms.mk_var("indexed_chain", array_sort.clone());
    let relevant = terms.mk_app(Symbol::named("="), [alias, chain], Sort::Bool);
    let reflexive = terms.mk_app(Symbol::named("="), [alias, alias], Sort::Bool);
    let mut authored = vec![relevant, reflexive];
    for position in 0..256 {
        let left = terms.mk_var(format!("indexed_left_{position}"), array_sort.clone());
        let right = terms.mk_var(format!("indexed_right_{position}"), array_sort.clone());
        authored.push(terms.mk_app(Symbol::named("="), [left, right], Sort::Bool));
    }
    let capped_alias = terms.mk_var("indexed_capped_alias", array_sort.clone());
    for position in 0..65 {
        let chain = terms.mk_var(format!("indexed_capped_{position}"), array_sort.clone());
        authored.push(terms.mk_app(Symbol::named("="), [capped_alias, chain], Sort::Bool));
    }

    let index = AuthoredIndex::build(&terms, &authored).expect("fixture is within source cap");
    assert_eq!(
        index.array_bindings(alias),
        Some(&[(relevant, chain), (reflexive, alias), (reflexive, alias)][..])
    );
    assert!(index.array_bindings(capped_alias).is_none());
}

struct RawSymbolicFixture {
    exec: Executor,
    index_disequality: TermId,
    later_index_disequality: TermId,
}

fn raw_symbolic_fixture() -> RawSymbolicFixture {
    let mut exec = Executor::new();
    let array_sort = Sort::array(Sort::Int, Sort::Int);
    let base = exec
        .ctx
        .terms
        .mk_var("raw_symbolic_base", array_sort.clone());
    let lhs = exec
        .ctx
        .terms
        .mk_var("raw_symbolic_lhs", array_sort.clone());
    let rhs = exec
        .ctx
        .terms
        .mk_var("raw_symbolic_rhs", array_sort.clone());
    let i = exec.ctx.terms.mk_var("raw_symbolic_i", Sort::Int);
    let j = exec.ctx.terms.mk_var("raw_symbolic_j", Sort::Int);
    let vi = exec.ctx.terms.mk_var("raw_symbolic_vi", Sort::Int);
    let vj = exec.ctx.terms.mk_var("raw_symbolic_vj", Sort::Int);
    let read_index = exec.ctx.terms.mk_var("raw_symbolic_read", Sort::Int);

    let left_inner =
        exec.ctx
            .terms
            .mk_app(Symbol::named("store"), [base, i, vi], array_sort.clone());
    let left_chain = exec.ctx.terms.mk_app(
        Symbol::named("store"),
        [left_inner, j, vj],
        array_sort.clone(),
    );
    let right_inner =
        exec.ctx
            .terms
            .mk_app(Symbol::named("store"), [base, j, vj], array_sort.clone());
    let right_chain =
        exec.ctx
            .terms
            .mk_app(Symbol::named("store"), [right_inner, i, vi], array_sort);
    assert_ne!(left_chain, right_chain, "fixture must stay nonnormalized");

    let left_binding = exec
        .ctx
        .terms
        .mk_app(Symbol::named("="), [lhs, left_chain], Sort::Bool);
    let right_binding = exec
        .ctx
        .terms
        .mk_app(Symbol::named("="), [rhs, right_chain], Sort::Bool);
    let index_equality = exec
        .ctx
        .terms
        .mk_app(Symbol::named("="), [j, i], Sort::Bool);
    let index_disequality = exec.ctx.terms.mk_not_raw(index_equality);
    let later_index_equality = exec
        .ctx
        .terms
        .mk_app(Symbol::named("="), [i, j], Sort::Bool);
    let later_index_disequality = exec.ctx.terms.mk_not_raw(later_index_equality);
    let left_select = exec.ctx.terms.mk_select(lhs, read_index);
    let right_select = exec.ctx.terms.mk_select(rhs, read_index);
    let select_equality =
        exec.ctx
            .terms
            .mk_app(Symbol::named("="), [left_select, right_select], Sort::Bool);
    let select_conflict = exec.ctx.terms.mk_not_raw(select_equality);
    for root in [
        left_binding,
        right_binding,
        index_disequality,
        later_index_disequality,
        select_conflict,
    ] {
        exec.ctx
            .add_assertion_with_parsed(root, FrontendTerm::Symbol("raw_symbolic".to_string()));
    }
    RawSymbolicFixture {
        exec,
        index_disequality,
        later_index_disequality,
    }
}

#[test]
fn raw_symbolic_store_permutation_uses_authored_disequality() {
    let RawSymbolicFixture {
        mut exec,
        index_disequality,
        later_index_disequality,
    } = raw_symbolic_fixture();

    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Trust, Vec::new(), Vec::new(), Vec::new());
    exec.replace_with_exact_authored_store_permutation_refutation(&mut proof);

    assert!(Executor::proof_derives_empty_clause(&proof));
    exec.check_proof_strict_with_datatypes(&proof)
        .expect("authored symbolic disequality closes the strict proof");
    let disequality_assume = proof
        .steps
        .iter()
        .position(|step| matches!(step, ProofStep::Assume(root) if *root == index_disequality))
        .expect("exact authored disequality is assumed");
    let permutation = proof
        .steps
        .iter()
        .position(|step| {
            matches!(
                step,
                ProofStep::TheoryLemma {
                    kind: TheoryLemmaKind::ArrayStorePermutation,
                    ..
                }
            )
        })
        .expect("store-permutation lemma is emitted");
    assert!(disequality_assume < permutation);
    assert!(proof
        .steps
        .iter()
        .all(|step| !matches!(step, ProofStep::Assume(root) if *root == later_index_disequality)));
    for expected in [
        TheoryLemmaKind::ArrayStorePermutation,
        TheoryLemmaKind::EufTransitive,
        TheoryLemmaKind::ArrayRowChain,
    ] {
        assert!(proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::TheoryLemma { kind, .. } if *kind == expected
        )));
    }
    assert!(proof.steps.iter().all(|step| match step {
        ProofStep::Step {
            rule: AletheRule::Trust,
            ..
        } => false,
        ProofStep::TheoryLemma { kind, .. } if kind.is_trust() => false,
        _ => true,
    }));
}

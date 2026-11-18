// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! (#source-derived-unsat-replay) The finite-expansion UNSAT theorem's
//! source-derived pass: the shapes it must certify, and the nearby SAT shapes
//! it must never certify.

use super::*;

/// The nested-`Vec` obligation in miniature: the grouped premise is false at
/// `(2, 3)`, where the cell holds `9`. Both binder bounds are datatype FIELDS
/// pinned by the defining equality, never literals in the universal itself.
fn nested_premise(cell: u8, definition: &str) -> String {
    let value = |cell: u8| {
        format!(
            "(let ((cells ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x07))) \
               (mkOuter #x03 (store ((as const (Array (_ BitVec 8) Inner)) (mkInner #x00 cells)) \
                                    #x02 (mkInner #x04 (store cells #x03 (_ bv{cell} 8))))))"
        )
    };
    let definition = definition
        .replace("@VALUE@", &value(cell))
        .replace("@TRUE_VALUE@", &value(7));
    format!(
        "(set-logic ALL) \
         (declare-datatype Inner ((mkInner (fld_len (_ BitVec 8)) \
                                           (fld_data (Array (_ BitVec 8) (_ BitVec 8)))))) \
         (declare-datatype Outer ((mkOuter (fld_len (_ BitVec 8)) \
                                           (fld_data (Array (_ BitVec 8) Inner))))) \
         (declare-const outer Outer) \
         {definition} \
         (assert (forall ((r (_ BitVec 8)) (c (_ BitVec 8))) \
           (=> (and (bvult r (fld_len outer)) (bvult c (fld_len (select (fld_data outer) r)))) \
               (= (select (fld_data (select (fld_data outer) r)) c) #x07))))"
    )
}

const CONJUNCTIVE_DEFINITION: &str = "(assert (= outer @VALUE@))";

fn load(source: &str) -> Executor {
    let commands = ay_frontend::parse(source).expect("source-derived fixture must parse");
    let mut executor = Executor::new();
    executor
        .execute_all(&commands)
        .expect("source-derived fixture must elaborate");
    executor
}

fn bind_public_query(executor: &mut Executor) {
    executor.begin_public_solve(false);
    executor.bind_unsat_query_assumptions(&[]);
}

fn source_derived_evidence(source: &str) -> Option<CheckedExactFiniteExpansionUnsat> {
    let mut executor = load(source);
    bind_public_query(&mut executor);
    executor.try_authorize_current_query_source_derived_finite_expansion_unsat()
}

#[test]
fn a_field_bounded_false_instance_is_certified_only_by_the_source_derived_pass() {
    let source = nested_premise(9, CONJUNCTIVE_DEFINITION);

    let mut literal = load(&source);
    bind_public_query(&mut literal);
    assert!(
        literal
            .try_authorize_current_query_exact_finite_expansion_unsat()
            .is_none(),
        "the literal-bound replay cannot read a field bound; if it now can, \
         the source-derived pass is no longer needed for this shape"
    );

    let mut executor = load(&source);
    bind_public_query(&mut executor);
    let evidence = executor
        .try_authorize_current_query_source_derived_finite_expansion_unsat()
        .expect("the authored definition pins both bounds and the (2, 3) cell");
    let proposed = executor.emit_checked_exact_finite_expansion_unsat(evidence);
    assert!(proposed.is_unsat());
    assert!(executor
        .certify_unsat_for_publication(proposed, &[])
        .is_unsat());
    let certificate = executor
        .take_unsat_certificate()
        .expect("the source-derived token must cross publication once");
    assert!(matches!(
        certificate.0,
        UnsatCertificateKind::CheckedExactFiniteExpansion(_)
    ));
}

#[test]
fn a_true_premise_is_never_certified() {
    assert!(source_derived_evidence(&nested_premise(7, CONJUNCTIVE_DEFINITION)).is_none());
}

/// Only a definition in conjunctive position is a fact. Here the premise holds
/// for the second disjunct, so the problem is SAT.
#[test]
fn a_definition_under_a_disjunction_is_not_folded() {
    let source = nested_premise(9, "(assert (or (= outer @VALUE@) (= outer @TRUE_VALUE@)))");
    assert!(source_derived_evidence(&source).is_none());
}

/// A bound entailed only disjunctively is not a constant: with `n = 0` the
/// universal is vacuous, so the problem is SAT.
#[test]
fn a_bound_entailed_only_disjunctively_is_not_read() {
    let source = "(set-logic ALL) \
         (declare-const n (_ BitVec 64)) \
         (declare-const a (Array (_ BitVec 64) (_ BitVec 8))) \
         (assert (or (= n (_ bv3 64)) (= n (_ bv0 64)))) \
         (assert (= a (store ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x07) (_ bv2 64) #x09))) \
         (assert (forall ((r (_ BitVec 64))) (=> (bvult r n) (= (select a r) #x07))))";
    assert!(source_derived_evidence(source).is_none());
    let pinned = source.replace("(or (= n (_ bv3 64)) (= n (_ bv0 64)))", "(= n (_ bv3 64))");
    assert!(
        source_derived_evidence(&pinned).is_some(),
        "control: the same universal with a conjunctive pin is refuted"
    );
}

#[test]
fn explicit_proof_modes_decline() {
    let source = nested_premise(9, CONJUNCTIVE_DEFINITION);
    let mut proof = load(&source);
    proof.set_produce_proofs(true);
    bind_public_query(&mut proof);
    assert!(proof
        .try_authorize_current_query_source_derived_finite_expansion_unsat()
        .is_none());

    let mut self_check = load(&source);
    self_check.set_self_check(true);
    bind_public_query(&mut self_check);
    assert!(self_check
        .try_authorize_current_query_source_derived_finite_expansion_unsat()
        .is_none());
}

/// Load `head` (which must start with the universal), then register a constant
/// spelled like that universal's first binder and assert `tail`, with `@B@`
/// naming the constant.
///
/// The constant is minted in the term store and registered with
/// `Context::register_symbol`, as a native-API caller does, and is a
/// different identity from the binder; a `declare-const` of that spelling
/// takes a private identity instead. The fold then moves ground terms
/// mentioning the constant under the binder, where the expander, which
/// substitutes binders BY NAME, would read it as the binder.
fn load_with_binder_spelled_constant(head: &str, tail: &str) -> Executor {
    let mut executor = load(head);
    let TermData::Forall(vars, _, _) = executor.ctx.terms.get(executor.ctx.assertions[0]).clone()
    else {
        panic!("fixture starts with the universal");
    };
    let binder = vars[0].0.clone();
    let constant = executor
        .ctx
        .terms
        .mk_var(binder.clone(), ay_core::Sort::bitvec(8));
    executor
        .ctx
        .register_symbol(binder.clone(), constant, ay_core::Sort::bitvec(8));
    let later = ay_frontend::parse(&tail.replace("@B@", &binder)).expect("the tail must parse");
    executor
        .execute_all(&later)
        .expect("the tail must elaborate");
    let spelled_like_binder = executor
        .ctx
        .terms
        .term_ids()
        .filter(|&term| matches!(executor.ctx.terms.get(term), TermData::Var(name, _) if *name == binder))
        .count();
    assert_eq!(
        spelled_like_binder, 2,
        "fixture must hold two identities spelled `{binder}`"
    );
    bind_public_query(&mut executor);
    executor
}

/// Folding `a := (store K r' 9)` puts the foreign `r'` next to the binder `r`
/// it is spelled like; instantiating both as one value would read `9` at every
/// point and "refute" a SAT problem (`r' >= 3` satisfies it; z3: sat).
#[test]
fn a_fold_that_brings_a_binder_spelling_under_the_binder_is_refused() {
    let mut executor = load_with_binder_spelled_constant(
        "(set-logic ALL) \
         (declare-const a (Array (_ BitVec 8) (_ BitVec 8))) \
         (declare-const b (Array (_ BitVec 8) (_ BitVec 8))) \
         (assert (forall ((r (_ BitVec 8))) \
           (=> (bvult r (select b #x00)) (= (select a r) #x07))))",
        "(assert (= b ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x03))) \
         (assert (= a (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x07) @B@ #x09)))",
    );
    assert!(executor
        .try_authorize_current_query_source_derived_finite_expansion_unsat()
        .is_none());
}

/// The binder never occurs in the authored body, so after the fold the ONLY
/// `r`-spelled variable is the foreign `r'`: one identity per name, and a
/// one-identity-per-name audit passes. Read as the binder, `r'` would be `5` in
/// one instance, `(select a 5)` would read `9`, and a SAT problem (`r' /= 5`
/// satisfies it; z3: sat) would be "refuted".
#[test]
fn a_fold_that_brings_a_binder_spelling_under_a_vacuous_binder_is_refused() {
    let mut executor = load_with_binder_spelled_constant(
        "(set-logic ALL) \
         (declare-const a (Array (_ BitVec 8) (_ BitVec 8))) \
         (assert (forall ((r (_ BitVec 8))) (= (select a #x05) #x07)))",
        "(assert (= a (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x07) @B@ #x09)))",
    );
    assert!(executor
        .try_authorize_current_query_source_derived_finite_expansion_unsat()
        .is_none());
}

/// The same capture when the fold itself ERASES the binder: `(select b r)`
/// collapses to `5` once `b := (as const .. 5)` is folded in, leaving the
/// foreign `r'` from `a`'s definition as the only `r`-spelled variable
/// (z3: sat).
#[test]
fn a_fold_that_erases_the_binder_and_brings_its_spelling_is_refused() {
    let mut executor = load_with_binder_spelled_constant(
        "(set-logic ALL) \
         (declare-const a (Array (_ BitVec 8) (_ BitVec 8))) \
         (declare-const b (Array (_ BitVec 8) (_ BitVec 8))) \
         (assert (forall ((r (_ BitVec 8))) (= (select a (select b r)) #x07)))",
        "(assert (= b ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x05))) \
         (assert (= a (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x07) @B@ #x09)))",
    );
    assert!(executor
        .try_authorize_current_query_source_derived_finite_expansion_unsat()
        .is_none());
}

/// Control for the two refusals above: a fold may erase the binder, and one
/// that brings in no foreign spelling is still certified. With `a[5] = 9` the
/// universal reads `(select a 5) = 7` at every point (z3: unsat).
#[test]
fn a_fold_that_erases_the_binder_without_a_foreign_spelling_is_certified() {
    let mut executor = load(
        "(set-logic ALL) \
         (declare-const a (Array (_ BitVec 8) (_ BitVec 8))) \
         (declare-const b (Array (_ BitVec 8) (_ BitVec 8))) \
         (assert (forall ((r (_ BitVec 8))) (= (select a (select b r)) #x07))) \
         (assert (= b ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x05))) \
         (assert (= a (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x07) #x05 #x09)))",
    );
    bind_public_query(&mut executor);
    assert!(executor
        .try_authorize_current_query_source_derived_finite_expansion_unsat()
        .is_some());
}

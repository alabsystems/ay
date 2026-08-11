// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::{AletheRule, Proof, ProofId, ProofStep, Sort, Symbol, TermStore};
use ay_proof::export_alethe;

#[test]
fn exports_zero_arity_clause_constructor_in_args() {
    let mut terms = TermStore::new();
    let cl_term = terms.mk_app(Symbol::named("cl"), vec![], Sort::Bool);

    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Drup, vec![], vec![], vec![cl_term]);

    let output = export_alethe(&proof, &terms);
    assert_eq!(output, "(step t0 (cl) :rule drup :args ((cl)))\n");
}

#[test]
fn exports_anchor_steps_with_typed_arguments() {
    let mut proof = Proof::new();
    proof.steps.push(ProofStep::Anchor {
        end_step: ProofId(7),
        variables: vec![
            ("x".to_string(), Sort::Int),
            ("flag".to_string(), Sort::Bool),
        ],
    });

    let output = export_alethe(&proof, &TermStore::new());
    assert_eq!(output, "(anchor :step t7 :args ((x Int) (flag Bool)))\n");
}

#[test]
fn exports_quoted_binders_for_quantifier_and_let_terms() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x y", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);
    let equality = terms.mk_eq(x, z);
    let forall = terms.mk_forall(
        vec![("x y".to_string(), Sort::Int), ("z".to_string(), Sort::Int)],
        equality,
    );
    let let_term = terms.mk_let(vec![("tmp value".to_string(), x)], x);

    let mut proof = Proof::new();
    proof.add_assume(forall, None);
    proof.add_rule_step(AletheRule::AllSimplify, vec![], vec![], vec![let_term]);

    let output = export_alethe(&proof, &terms);
    // Declaration preamble is emitted for all Var nodes (including quantifier-bound ones).
    assert!(
        output.contains("(declare-fun |x y| () Int)"),
        "Missing declaration for |x y|: {output}"
    );
    assert!(
        output.contains("(declare-fun z () Int)"),
        "Missing declaration for z: {output}"
    );
    assert!(
        output.contains("(assume t0 (forall ((|x y| Int) (z Int)) (= |x y| z)))"),
        "Missing assume step: {output}"
    );
    // The rule prints as `hole`, NOT `all_simplify`. Verified against the
    // installed carcara 1.1.0:
    //   [ERROR] checking failed on step 't1' with rule 'all_simplify': unknown rule
    //   invalid
    // An unknown rule makes the whole document `invalid` — i.e. not a proof at
    // all. Demoting to `hole` costs nothing that was ever checked and moves the
    // document up the ladder to `holey` (an honest unproved step). This
    // assertion previously required the uncheckable spelling.
    //
    // What must NOT change is the term rendering: the quoted binder `|x y|` and
    // the quoted let-binding `|tmp value|` still have to survive into the args.
    assert!(
        output.contains("(step t1 (cl) :rule hole :args ((let ((|tmp value| |x y|)) |x y|)))"),
        "Missing step: {output}"
    );
}

#[test]
fn exports_indexed_symbols_and_constant_escaping() {
    let mut terms = TermStore::new();
    let bv = terms.mk_bitvec(0b1111_0000.into(), 8);
    let extract = terms.mk_app(
        Symbol::indexed("extract", vec![7, 4]),
        vec![bv],
        Sort::bitvec(4),
    );
    let escaped_str = terms.mk_string("a\"b".to_string());
    let neg_int = terms.mk_int((-5).into());

    let mut proof = Proof::new();
    proof.add_rule_step(
        AletheRule::Trust,
        vec![],
        vec![],
        vec![extract, escaped_str, neg_int],
    );

    let output = export_alethe(&proof, &terms);
    assert!(output.contains("((_ extract 7 4) #b11110000)"), "{output}");
    assert!(output.contains("\"a\"\"b\""), "{output}");
    assert!(output.contains("(- 5)"), "{output}");
}

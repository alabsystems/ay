// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the authored fold-identity refutation.

use super::*;

fn parse_assertion(text: &str) -> FrontendTerm {
    let commands = ay_frontend::parse(&format!("(assert {text})")).expect("parses");
    let [ay_frontend::Command::Assert(term)] = commands.as_slice() else {
        panic!("one assert");
    };
    term.clone()
}

/// A context with `f : Int -> Int` and `x y : Int` declared, and the fold
/// fixture asserted (so the executor holds a parsed root and a live `false`).
fn fixture_executor(assertion: &str) -> Executor {
    let script = format!(
        "(set-logic QF_UFLIA)\n(declare-fun f (Int) Int)\n(declare-fun x () Int)\n\
         (declare-fun y () Int)\n(assert {assertion})"
    );
    let commands = ay_frontend::parse(&script).expect("fixture must parse");
    let mut executor = Executor::new();
    executor
        .execute_all(&commands)
        .expect("fixture must elaborate");
    executor
}

#[test]
fn let_expansion_is_parallel_and_capture_safe() {
    let empty = std::collections::HashMap::new();
    // A plain chain expands innermost-first.
    let expanded = expand_surface_lets(
        &parse_assertion(
            "(let ((?a (f x)) (?b (f y))) (let ((?c (= ?a ?b))) (and ?c (distinct ?a ?b))))",
        ),
        &empty,
    )
    .expect("simple chain expands");
    assert_eq!(
        expanded,
        parse_assertion("(and (= (f x) (f y)) (distinct (f x) (f y)))")
    );
    // Parallel semantics: a value mentioning a name its own level binds
    // refers to the OUTER symbol, never to the sibling binding.
    let parallel = expand_surface_lets(
        &parse_assertion("(let ((?a x)) (let ((?a y) (?b (f ?a))) (= ?a ?b)))"),
        &empty,
    )
    .expect("parallel chain expands");
    assert_eq!(parallel, parse_assertion("(= y (f x))"));
    // A binder under a non-empty environment could capture: refused.
    assert!(expand_surface_lets(
        &parse_assertion("(let ((?a x)) (forall ((z Int)) (= ?a z)))"),
        &empty
    )
    .is_none());
    // A non-let root is returned unchanged.
    assert_eq!(
        expand_surface_lets(&parse_assertion("(and p q)"), &empty),
        Some(parse_assertion("(and p q)"))
    );
}

#[test]
fn the_shape_scan_sees_through_let_levels_and_refuses_the_rest() {
    assert!(parsed_root_holds_candidate_conjunct(&parse_assertion(
        "(let ((?a (f x))) (and (< x 1) (distinct ?a (* 2 ?a))))"
    )));
    assert!(parsed_root_holds_candidate_conjunct(&parse_assertion(
        "(and (< x 1) (not (= (+ x x) (* 2 x))))"
    )));
    // A negated conjunct under one `(not (not ..))` pair: the complement
    // shape, reachable by the shelled projection.
    assert!(parsed_root_holds_candidate_conjunct(&parse_assertion(
        "(not (not (and (not p) p)))"
    )));
    // A disequality NOT under the `and`-spine is not a conjunct.
    assert!(!parsed_root_holds_candidate_conjunct(&parse_assertion(
        "(or (< x 1) (distinct x y))"
    )));
    // An n-ary distinct and bare comparisons: nothing this pass derives.
    assert!(!parsed_root_holds_candidate_conjunct(&parse_assertion(
        "(and (distinct x y (f x)) (<= x y) (< y x))"
    )));
}

/// FALSIFY-ONCE for the arithmetic leaf. The pass's whole soundness argument
/// is that the `la_generic` pair is re-verified by the strict checker rather
/// than taken on the producer's word. Plant the byte-identical leaf
/// derivation over `(+ (f x) (f x))` and `(* 3 (f x))` — which are NOT one
/// term — and watch the strict checker refuse it. If this ever passes, the
/// pass is a false-proof machine.
#[test]
fn a_planted_identity_over_unequal_terms_is_refused_by_the_strict_checker() {
    let mut executor = fixture_executor("(< x 1)");
    let fx = executor
        .ctx
        .elaborate_surface_subterm(&parse_assertion("(f x)"))
        .expect("f x elaborates");
    let two = executor
        .ctx
        .elaborate_surface_subterm(&parse_assertion("2"))
        .expect("2 elaborates");
    let three = executor
        .ctx
        .elaborate_surface_subterm(&parse_assertion("3"))
        .expect("3 elaborates");
    let sum = executor
        .ctx
        .terms
        .mk_app(Symbol::named("+"), [fx, fx], Sort::Int);
    let twice = executor
        .ctx
        .terms
        .mk_app(Symbol::named("*"), [two, fx], Sort::Int);
    let thrice = executor
        .ctx
        .terms
        .mk_app(Symbol::named("*"), [three, fx], Sort::Int);

    // The producer itself declines: the two spellings do not normalize to
    // one term, so no derivation is built at all.
    let mut declined = Proof::new();
    let mut budget = MAX_DIFF_NODES;
    assert!(executor
        .derive_normalized_equality(
            &mut declined,
            sum,
            thrice,
            &parse_assertion("(+ (f x) (f x))"),
            &parse_assertion("(* 3 (f x))"),
            &mut budget,
        )
        .is_none());

    // The genuine identity IS derived, and the strict checker accepts it as
    // a complete derivation of `(cl (= (+ (f x) (f x)) (* 2 (f x))))`.
    let mut genuine = Proof::new();
    let mut budget = MAX_DIFF_NODES;
    let unit = executor
        .derive_normalized_equality(
            &mut genuine,
            sum,
            twice,
            &parse_assertion("(+ (f x) (f x))"),
            &parse_assertion("(* 2 (f x))"),
            &mut budget,
        )
        .expect("the genuine identity derives");
    let eq = raw_eq(&mut executor.ctx.terms, sum, twice);
    // Close the derivation against the planted disequality so the checker
    // judges a whole refutation, then plant the SAME skeleton over the
    // unequal pair and require refusal.
    let not_eq = executor.ctx.terms.mk_not_raw(eq);
    let assume = genuine.add_assume(not_eq, None);
    genuine.add_resolution(Vec::new(), eq, assume, unit);
    executor.record_rebuilt_authored_proof_premise(not_eq);
    assert!(
        executor
            .check_proof_strict_with_datatypes(&genuine)
            .is_ok_and(|quality| quality.is_complete()),
        "the genuine normalization identity must be strictly checkable"
    );

    let mut forged = Proof::new();
    let le_forward = executor
        .ctx
        .terms
        .mk_app(Symbol::named("<="), [sum, thrice], Sort::Bool);
    let le_reverse = executor
        .ctx
        .terms
        .mk_app(Symbol::named("<="), [thrice, sum], Sort::Bool);
    let forward = forged.add_theory_lemma_with_farkas_and_kind(
        "LIA",
        vec![le_forward],
        FarkasAnnotation::from_ints(&[1]),
        TheoryLemmaKind::LiaGeneric,
    );
    let reverse = forged.add_theory_lemma_with_farkas_and_kind(
        "LIA",
        vec![le_reverse],
        FarkasAnnotation::from_ints(&[1]),
        TheoryLemmaKind::LiaGeneric,
    );
    let forged_eq = raw_eq(&mut executor.ctx.terms, sum, thrice);
    let not_forward = executor.ctx.terms.mk_not_raw(le_forward);
    let not_reverse = executor.ctx.terms.mk_not_raw(le_reverse);
    let triangle = executor.ctx.terms.mk_app(
        Symbol::named("or"),
        [forged_eq, not_forward, not_reverse],
        Sort::Bool,
    );
    let disequality = forged.add_rule_step(
        AletheRule::LaDisequality,
        vec![triangle],
        Vec::new(),
        Vec::new(),
    );
    let clausified = forged.add_rule_step(
        AletheRule::Or,
        vec![forged_eq, not_forward, not_reverse],
        vec![disequality],
        Vec::new(),
    );
    let partial = forged.add_resolution(
        vec![forged_eq, not_reverse],
        le_forward,
        clausified,
        forward,
    );
    let unit = forged.add_resolution(vec![forged_eq], le_reverse, partial, reverse);
    let not_forged_eq = executor.ctx.terms.mk_not_raw(forged_eq);
    let assume = forged.add_assume(not_forged_eq, None);
    forged.add_resolution(Vec::new(), forged_eq, assume, unit);
    executor.record_rebuilt_authored_proof_premise(not_forged_eq);
    assert!(
        executor.check_proof_strict_with_datatypes(&forged).is_err(),
        "a la_generic unit over `(<= (+ (f x) (f x)) (* 3 (f x)))` is not a tautology and \
         the strict checker must refuse it"
    );
}

#[test]
fn the_propositional_scan_needs_a_refuting_constant_or_a_complement() {
    // A complement anywhere in the and/or/not skeleton, or `false` in
    // positive / `true` in negative position.
    for root in [
        "(or (and (<= x y) (and true (not (<= x y)))))",
        "(not (or (not (<= x y)) (and true (<= x y))))",
        "(or (< x 1) false)",
        "(and (< x 1) (not true))",
        "(let ((?l (<= x y))) (or (and ?l (not ?l))))",
    ] {
        assert!(
            parsed_root_holds_propositional_candidate(&parse_assertion(root)),
            "{root}"
        );
    }
    // No complement and no refuting constant: nothing to derive. `true` in
    // positive and `false` in negative position refute nothing.
    for root in [
        "(or (< x 1) (distinct x y))",
        "(and (<= x y) (and true (<= x y)))",
        "(or (< x 1) (not false))",
        "(= (f x) (f (f x)))",
    ] {
        assert!(
            !parsed_root_holds_propositional_candidate(&parse_assertion(root)),
            "{root}"
        );
    }
}

/// The raw, unfolded root of `text`, recorded as an authored premise so the
/// strict checker judges a whole refutation of it.
fn raw_premise(executor: &mut Executor, text: &str) -> TermId {
    let root = executor
        .raw_intern_surface(&parse_assertion(text))
        .expect("root re-interns raw");
    executor.record_rebuilt_authored_proof_premise(root);
    root
}

/// The propositional refuter on every nesting the elaborator folds through:
/// each candidate must be a COMPLETE strict refutation of the raw root.
#[test]
fn the_propositional_refutation_is_strictly_checked_at_every_nesting() {
    for root in [
        "(or (and (<= x y) (and true (not (<= x y)))))",
        "(or (and (<= x y) (and true (not (<= x y)))) false)",
        "(and (<= x y) (and true (and true (not (<= x y)))))",
        "(not (or (not (<= x y)) (and true (<= x y))))",
        "(and (<= x y) (or (and true (not (<= x y))) false))",
        "(not (and true (or (<= x y) (not (<= x y)))))",
        "(or (and true (<= x y) (not (<= x y))) (and (not (<= x y)) (and true (<= x y))))",
    ] {
        let mut executor = fixture_executor("(< x 1)");
        let raw = raw_premise(&mut executor, root);
        let mut candidate = Proof::new();
        let assume = candidate.add_assume(raw, None);
        propositional::refute_root(&mut executor.ctx.terms, &mut candidate, assume, raw)
            .unwrap_or_else(|| panic!("{root}: the refuter must close the root"));
        assert!(
            Executor::proof_derives_empty_clause(&candidate),
            "{root}: no empty clause"
        );
        assert!(
            executor
                .check_proof_strict_with_datatypes(&candidate)
                .is_ok_and(|quality| quality.is_complete()),
            "{root}: the strict checker must accept the refutation"
        );
    }
}

/// Construct the same-literal forgery used by the strict-checker negative.
fn planted_same_literal_refutation(executor: &mut Executor, root: TermId) -> Proof {
    let terms = &mut executor.ctx.terms;
    let TermData::App(_, disjuncts) = terms.get(root).clone() else {
        panic!("raw or");
    };
    let conjunction = disjuncts[0];
    let TermData::App(_, conjuncts) = terms.get(conjunction).clone() else {
        panic!("raw and");
    };
    let literal = conjuncts[0];
    let inner = conjuncts[1];
    let not_root = terms.mk_not_raw(root);
    let not_conjunction = terms.mk_not_raw(conjunction);
    let not_inner = terms.mk_not_raw(inner);
    let mut forged = Proof::new();
    let assume = forged.add_assume(root, None);
    let split = forged.add_rule_step(
        AletheRule::OrPos(0),
        vec![not_root, conjunction],
        Vec::new(),
        vec![root],
    );
    let unit = forged.add_resolution(vec![conjunction], root, split, assume);
    let first = forged.add_rule_step(
        AletheRule::AndPos(0),
        vec![not_conjunction, literal],
        Vec::new(),
        vec![conjunction],
    );
    let first = forged.add_resolution(vec![literal], conjunction, first, unit);
    let second = forged.add_rule_step(
        AletheRule::AndPos(1),
        vec![not_conjunction, inner],
        Vec::new(),
        vec![conjunction],
    );
    let second = forged.add_resolution(vec![inner], conjunction, second, unit);
    let projected = forged.add_rule_step(
        AletheRule::AndPos(1),
        vec![not_inner, literal],
        Vec::new(),
        vec![inner],
    );
    let again = forged.add_resolution(vec![literal], inner, projected, second);
    // The forgery: `l` and `l` resolved as if complementary.
    forged.add_resolution(Vec::new(), literal, again, first);
    forged
}

/// FALSIFY-ONCE for the propositional argument. The refuter declines a
/// SATISFIABLE root outright, and the planted refutations an unsound refuter
/// would build for it — a "complement" that is the same literal twice, an
/// `or_pos` that drops the satisfiable disjunct — are refused by the
/// unchanged strict checker. If either planted proof is ever accepted, the
/// self-check this pass feeds is a false-proof machine.
#[test]
fn a_planted_propositional_refutation_of_a_satisfiable_root_is_refused() {
    // `(or (and l (and true l)))`: satisfiable whenever `l` holds.
    let mut executor = fixture_executor("(< x 1)");
    let root = raw_premise(&mut executor, "(or (and (<= x y) (and true (<= x y))))");
    let mut declined = Proof::new();
    let assume = declined.add_assume(root, None);
    assert!(
        propositional::refute_root(&mut executor.ctx.terms, &mut declined, assume, root).is_none(),
        "the refuter must decline a satisfiable root"
    );

    let forged = planted_same_literal_refutation(&mut executor, root);
    assert!(
        executor.check_proof_strict_with_datatypes(&forged).is_err(),
        "resolving a literal against itself must be refused"
    );

    // `(or (and l (not l)) l)`: satisfiable through its second disjunct. An
    // `or_pos` that omits that disjunct is not a tautology.
    let mut executor = fixture_executor("(< x 1)");
    let root = raw_premise(&mut executor, "(or (and (<= x y) (not (<= x y))) (<= x y))");
    let mut declined = Proof::new();
    let assume = declined.add_assume(root, None);
    assert!(
        propositional::refute_root(&mut executor.ctx.terms, &mut declined, assume, root).is_none(),
        "the refuter must decline a root with a satisfiable disjunct"
    );
    let terms = &mut executor.ctx.terms;
    let TermData::App(_, disjuncts) = terms.get(root).clone() else {
        panic!("raw or");
    };
    let conjunction = disjuncts[0];
    let TermData::App(_, conjuncts) = terms.get(conjunction).clone() else {
        panic!("raw and");
    };
    let (positive, negative) = (conjuncts[0], conjuncts[1]);
    let not_root = terms.mk_not_raw(root);
    let not_conjunction = terms.mk_not_raw(conjunction);
    let mut forged = Proof::new();
    let assume = forged.add_assume(root, None);
    let split = forged.add_rule_step(
        AletheRule::OrPos(0),
        vec![not_root, conjunction],
        Vec::new(),
        vec![root],
    );
    let unit = forged.add_resolution(vec![conjunction], root, split, assume);
    let left = forged.add_rule_step(
        AletheRule::AndPos(0),
        vec![not_conjunction, positive],
        Vec::new(),
        vec![conjunction],
    );
    let left = forged.add_resolution(vec![positive], conjunction, left, unit);
    let right = forged.add_rule_step(
        AletheRule::AndPos(1),
        vec![not_conjunction, negative],
        Vec::new(),
        vec![conjunction],
    );
    let right = forged.add_resolution(vec![negative], conjunction, right, unit);
    forged.add_resolution(Vec::new(), positive, right, left);
    assert!(
        Executor::proof_derives_empty_clause(&forged),
        "the forgery must reach the empty clause, or this test proves nothing"
    );
    assert!(
        executor.check_proof_strict_with_datatypes(&forged).is_err(),
        "an or_pos that drops a disjunct must be refused"
    );
}

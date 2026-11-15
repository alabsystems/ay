// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The printed-surface rule gate, and the indexed-congruence bridge.
//!
//! Both defects these cover have the same shape and it is the shape that keeps
//! shipping: the rule name is read off the TERM DAG, the term text is read off
//! a SURFACE OVERRIDE, and nothing downstream compares the two. AY's own strict
//! checker validates the term, so every internal signal reads green while the
//! external checker refuses the step and throws the whole document away.
//!
//! Each test below is a MUTATION DIFFERENTIAL: the same proof is exported twice,
//! once with the override that moves the printed text out from under the rule
//! and once without. The un-mutated export must render the rule byte-identically
//! (a guard that fires on correct steps destroys evidence); the mutated export
//! must refuse (a guard that stays silent ships a false claim).

use crate::{try_export_alethe_with_problem_scope_and_overrides, AlethePrintError};
use ay_core::kani_compat::DetHashMap;
use ay_core::{AletheRule, Proof, Sort, Symbol, TermId, TermStore};

/// `(cl (not (ite c t e)) (not c) t)` — a genuine `ite_pos2`.
fn ite_pos2_proof(terms: &mut TermStore) -> (Proof, TermId) {
    let condition = terms.mk_var("c", Sort::Bool);
    let then_branch = terms.mk_var("t", Sort::Bool);
    let else_branch = terms.mk_var("e", Sort::Bool);
    let ite = terms.mk_ite(condition, then_branch, else_branch);
    let not_ite = terms.mk_not_raw(ite);
    let not_condition = terms.mk_not_raw(condition);
    let mut proof = Proof::new();
    proof.add_rule_step(
        AletheRule::ItePos2,
        vec![not_ite, not_condition, then_branch],
        Vec::new(),
        vec![ite],
    );
    (proof, ite)
}

#[test]
fn ite_pos2_over_an_unmutated_surface_still_renders_ite_pos2() {
    let mut terms = TermStore::new();
    let (proof, _ite) = ite_pos2_proof(&mut terms);

    let output = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &super::scope_covering_proof(&proof),
        None,
    )
    .expect("a spec-shaped ite_pos2 must still export");
    assert!(
        output.contains("(step t0 (cl (not (ite c t e)) (not c) t) :rule ite_pos2)"),
        "{output}"
    );
}

#[test]
fn ite_pos2_whose_printed_source_is_not_an_ite_is_refused() {
    let mut terms = TermStore::new();
    let (proof, ite) = ite_pos2_proof(&mut terms);
    // Exactly the corpus shape: AY lifts an authored `(= a (ite p u v))` into
    // an internal Boolean `ite` and registers the AUTHORED spelling as that
    // node's surface override so the quantifier instance keeps matching the
    // problem premise. `ite_pos2` is then correct over the term and refused
    // over the text ("is of the wrong form, expected '(not(ite ...))'").
    let mut overrides = DetHashMap::default();
    overrides.insert(ite, "(= a (ite c u v))".to_string());

    let error = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &super::scope_covering_proof(&proof),
        Some(&overrides),
    )
    .expect_err("an ite_pos2 whose printed source is an equality must not ship");
    match error {
        AlethePrintError::InvalidSurfaceStep { reason, .. } => {
            assert!(reason.contains("ite_pos2"), "{reason}");
            assert!(reason.contains("printed surface"), "{reason}");
        }
        other => panic!("expected InvalidSurfaceStep, got {other:?}"),
    }
}

#[test]
fn equiv_pos1_whose_printed_source_is_not_an_equality_is_refused() {
    // The gate is not a special case for `ite`: every premise-free
    // "tautologous rule" is valid purely as a function of its printed clause
    // and printed source, and the override channel can move that text out from
    // under any of them.
    let mut terms = TermStore::new();
    let left = terms.mk_var("p", Sort::Bool);
    let right = terms.mk_var("q", Sort::Bool);
    let equality = terms.mk_app(Symbol::named("="), [left, right], Sort::Bool);
    let not_equality = terms.mk_not_raw(equality);
    let not_right = terms.mk_not_raw(right);
    let mut proof = Proof::new();
    proof.add_rule_step(
        AletheRule::EquivPos1,
        vec![not_equality, left, not_right],
        Vec::new(),
        vec![equality],
    );

    let output = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &super::scope_covering_proof(&proof),
        None,
    )
    .expect("a spec-shaped equiv_pos1 must still export");
    assert!(output.contains(":rule equiv_pos1"), "{output}");

    let mut overrides = DetHashMap::default();
    overrides.insert(equality, "(and p q)".to_string());
    let error = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &super::scope_covering_proof(&proof),
        Some(&overrides),
    )
    .expect_err("an equiv_pos1 whose printed source is a conjunction must not ship");
    assert!(
        matches!(error, AlethePrintError::InvalidSurfaceStep { .. }),
        "{error:?}"
    );
}

/// `(cl (not (= x y)) (= ((_ extract 1 0) y) ((_ extract 1 0) x)))`.
///
/// The reversed conclusion is the corpus orientation (QF_AUFBV `ec_twin_mul`
/// step `t44`), which is why the bridge has to compose `symm`.
fn indexed_eq_congruent_proof(terms: &mut TermStore) -> Proof {
    let x = terms.mk_var("x", Sort::BitVec(ay_core::BitVecSort { width: 4 }));
    let y = terms.mk_var("y", Sort::BitVec(ay_core::BitVecSort { width: 4 }));
    let extract = Symbol::indexed("extract", vec![1, 0]);
    let extract_x = terms.mk_app(
        extract.clone(),
        [x],
        Sort::BitVec(ay_core::BitVecSort { width: 2 }),
    );
    let extract_y = terms.mk_app(extract, [y], Sort::BitVec(ay_core::BitVecSort { width: 2 }));
    let hypothesis = terms.mk_app(Symbol::named("="), [x, y], Sort::Bool);
    let not_hypothesis = terms.mk_not_raw(hypothesis);
    let conclusion = terms.mk_app(Symbol::named("="), [extract_y, extract_x], Sort::Bool);
    let mut proof = Proof::new();
    proof.add_rule_step(
        AletheRule::EqCongruent,
        vec![not_hypothesis, conclusion],
        Vec::new(),
        Vec::new(),
    );
    proof
}

#[test]
fn eq_congruent_over_an_indexed_head_is_rebuilt_as_a_cong_subproof() {
    // carcara 1.1.0's `eq_congruent` accepts only `Term::App` and `Term::Op`,
    // so `((_ extract 1 0) x)` is refused outright — MEASURED, and measured
    // alongside the same clause over an uninterpreted symbol, which is
    // `valid`. `cong` over the identical indexed term is also `valid`, so the
    // repair is a real derivation and not a relabel.
    let mut terms = TermStore::new();
    let proof = indexed_eq_congruent_proof(&mut terms);

    let output = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &super::scope_covering_proof(&proof),
        None,
    )
    .expect("the indexed congruence bridge must export");
    assert!(output.contains("(anchor :step t0)"), "{output}");
    assert!(output.contains("(assume t0.h0 (= x y))"), "{output}");
    assert!(
        output.contains(
            "(step t0.c (cl (= ((_ extract 1 0) x) ((_ extract 1 0) y))) :rule cong :premises (t0.h0))"
        ),
        "{output}"
    );
    assert!(
        output.contains(
            "(step t0.s (cl (= ((_ extract 1 0) y) ((_ extract 1 0) x))) :rule symm :premises (t0.c))"
        ),
        "{output}"
    );
    // The closing step keeps the original id and the byte-identical traced
    // clause, so no downstream premise reference moves.
    assert!(
        output.contains(
            "(step t0 (cl (not (= x y)) (= ((_ extract 1 0) y) ((_ extract 1 0) x))) :rule subproof :discharge (t0.h0))"
        ),
        "{output}"
    );
    assert!(!output.contains(":rule eq_congruent"), "{output}");
}

#[test]
fn eq_congruent_over_an_ordinary_head_is_left_byte_identical() {
    // The bridge exists for ONE printed shape. An ordinary application is not
    // refused by the external checker and must keep its existing rendering.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::BitVec(ay_core::BitVecSort { width: 4 }));
    let y = terms.mk_var("y", Sort::BitVec(ay_core::BitVecSort { width: 4 }));
    let g = Symbol::named("g");
    let g_x = terms.mk_app(
        g.clone(),
        [x],
        Sort::BitVec(ay_core::BitVecSort { width: 2 }),
    );
    let g_y = terms.mk_app(g, [y], Sort::BitVec(ay_core::BitVecSort { width: 2 }));
    let hypothesis = terms.mk_app(Symbol::named("="), [x, y], Sort::Bool);
    let not_hypothesis = terms.mk_not_raw(hypothesis);
    let conclusion = terms.mk_app(Symbol::named("="), [g_x, g_y], Sort::Bool);
    let mut proof = Proof::new();
    proof.add_rule_step(
        AletheRule::EqCongruent,
        vec![not_hypothesis, conclusion],
        Vec::new(),
        Vec::new(),
    );

    let output = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &super::scope_covering_proof(&proof),
        None,
    )
    .expect("an ordinary eq_congruent must still export");
    assert!(
        output.contains("(step t0 (cl (not (= x y)) (= (g x) (g y))) :rule eq_congruent)"),
        "{output}"
    );
    assert!(!output.contains(":rule subproof"), "{output}");
}

#[test]
fn indexed_eq_congruent_declines_when_the_argument_pairing_does_not_hold() {
    // MUTATION DIFFERENTIAL for the bridge itself: change the hypothesis so it
    // no longer equates the two applications' arguments, and the bridge must
    // stop applying rather than emit a `cong` whose premise proves something
    // else.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::BitVec(ay_core::BitVecSort { width: 4 }));
    let y = terms.mk_var("y", Sort::BitVec(ay_core::BitVecSort { width: 4 }));
    let z = terms.mk_var("z", Sort::BitVec(ay_core::BitVecSort { width: 4 }));
    let extract = Symbol::indexed("extract", vec![1, 0]);
    let extract_x = terms.mk_app(
        extract.clone(),
        [x],
        Sort::BitVec(ay_core::BitVecSort { width: 2 }),
    );
    let extract_y = terms.mk_app(extract, [y], Sort::BitVec(ay_core::BitVecSort { width: 2 }));
    // `(= x z)` says nothing about `y`.
    let hypothesis = terms.mk_app(Symbol::named("="), [x, z], Sort::Bool);
    let not_hypothesis = terms.mk_not_raw(hypothesis);
    let conclusion = terms.mk_app(Symbol::named("="), [extract_x, extract_y], Sort::Bool);
    let mut proof = Proof::new();
    proof.add_rule_step(
        AletheRule::EqCongruent,
        vec![not_hypothesis, conclusion],
        Vec::new(),
        Vec::new(),
    );

    let output = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &super::scope_covering_proof(&proof),
        None,
    )
    .expect("the declined bridge still exports the document");
    assert!(!output.contains(":rule cong"), "{output}");
    assert!(!output.contains(":rule subproof"), "{output}");
    // What the printer falls back to is the honest hole over the same text,
    // not the bare rule name: the unbridged `eq_congruent` this test once
    // pinned is a step the pinned checker refuses twice over (an indexed head
    // is not `Term::App`, and `(= x z)` justifies no argument pair), and
    // since 2026-09-20 every `eq_congruent` is judged over its printed
    // literals before it reaches the wire.
    assert!(!output.contains(":rule eq_congruent"), "{output}");
    assert!(
        output
            .contains("(cl (not (= x z)) (= ((_ extract 1 0) x) ((_ extract 1 0) y))) :rule hole)"),
        "{output}"
    );
}

/// The same `let`-rooted assertion assumed twice.
///
/// The first assume's bridge installs the eliminated body in
/// `let_bridge_renderings` so every downstream STEP prints the eliminated form.
/// That is right for steps and wrong for a second `assume` leaf: it would ship
/// the eliminated text, and carcara matches an `assume` against the ORIGINAL
/// problem premises through — never into — `Term::Let`, so the eliminated form
/// matches nothing and the whole document is `invalid`. MEASURED on QF_UF
/// QG-classification `gensys_icl483` / `_icl798` / `_icl448`.
#[test]
fn a_let_rooted_assertion_assumed_twice_bridges_both_leaves() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);
    let body = terms.mk_app(Symbol::named("and"), [p, q], Sort::Bool);
    let surface = "(let ((?v_0 p)) (and ?v_0 q))";
    let mut overrides = DetHashMap::default();
    overrides.insert(body, surface.to_string());

    // Both leaves must be CONSUMED: an assumption nothing uses is confined to
    // its own exact-spelling `assume` by a different path entirely, and the
    // bridge this test is about never runs.
    //
    // The consumer concludes `(cl (and p q))` rather than the empty clause.
    // That is not cosmetic: two copies of `(cl A)` do not resolve to `(cl)`,
    // and the printed-text judgement in `printed_resolution` refuses exactly
    // that step — as pinned carcara does. Keeping the bogus terminal here
    // would test the assume leaves through a document no checker accepts.
    let mut proof = Proof::new();
    let first = proof.add_assume(body, None);
    let second = proof.add_assume(body, None);
    proof.add_rule_step(
        AletheRule::ThResolution,
        vec![body],
        vec![first, second],
        Vec::new(),
    );

    let output = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &[body],
        Some(&overrides),
    )
    .expect("both leaves must export");
    assert!(
        output.contains(&format!("(assume t0.a {surface})")),
        "{output}"
    );
    assert!(
        output.contains(&format!("(assume t1.a {surface})")),
        "{output}"
    );
    // The eliminated body must never appear as a bare `assume`: that is exactly
    // the text carcara cannot match against the problem's `(let ...)` premise.
    assert!(!output.contains("(assume t1 (and p q))"), "{output}");
    assert!(!output.contains("(assume t0 (and p q))"), "{output}");
}

#[test]
fn assumes_without_a_let_surface_stay_plain() {
    // MUTATION DIFFERENTIAL for the leaf above: drop the authored `let`
    // spelling and both assumes must render as ordinary leaves, with no bridge
    // invented for them.
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);
    let body = terms.mk_app(Symbol::named("and"), [p, q], Sort::Bool);
    let mut proof = Proof::new();
    let first = proof.add_assume(body, None);
    let second = proof.add_assume(body, None);
    // Same terminal as the test above, and for the same reason.
    proof.add_rule_step(
        AletheRule::ThResolution,
        vec![body],
        vec![first, second],
        Vec::new(),
    );

    let output = try_export_alethe_with_problem_scope_and_overrides(&proof, &terms, &[body], None)
        .expect("both leaves must export");
    assert!(output.contains("(assume t0 (and p q))"), "{output}");
    assert!(output.contains("(assume t1 (and p q))"), "{output}");
    assert!(!output.contains(":rule let"), "{output}");
}

// ---------------------------------------------------------------------------
// The no-source-argument sub-population, and the order-atom orientation.
//
// Every test above passes `args = [source]`. The producers behind the
// 2026-09-07 false green do not: they emit a premise-free tautology with NO
// source-term argument, and the gate read its source exclusively from `args`,
// so it answered "nothing to say" and the default rendering shipped a step the
// external checker refuses. Silence read exactly like approval.
// ---------------------------------------------------------------------------

/// `(cl (not (= p q)) (not p) q)` — a genuine `equiv_pos2`, built the way the
/// producers in this defect's population build it: with **no source-term
/// argument**.
fn equiv_pos2_without_source_arg(terms: &mut TermStore) -> (Proof, TermId) {
    let left = terms.mk_var("p", Sort::Bool);
    let right = terms.mk_var("q", Sort::Bool);
    let equality = terms.mk_app(Symbol::named("="), [left, right], Sort::Bool);
    let not_equality = terms.mk_not_raw(equality);
    let not_left = terms.mk_not_raw(left);
    let mut proof = Proof::new();
    proof.add_rule_step(
        AletheRule::EquivPos2,
        vec![not_equality, not_left, right],
        Vec::new(),
        Vec::new(),
    );
    (proof, equality)
}

#[test]
fn equiv_pos2_with_no_source_argument_still_renders_equiv_pos2() {
    // The other half of every mutation differential: a guard that fires on a
    // correct step destroys evidence. Recovering the source from the clause
    // must leave a spec-shaped step byte-identical.
    let mut terms = TermStore::new();
    let (proof, _equality) = equiv_pos2_without_source_arg(&mut terms);

    let output = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &super::scope_covering_proof(&proof),
        None,
    )
    .expect("a spec-shaped equiv_pos2 must still export");
    assert!(
        output.contains("(step t0 (cl (not (= p q)) (not p) q) :rule equiv_pos2)"),
        "{output}"
    );
}

#[test]
fn equiv_pos2_with_no_source_argument_over_a_mutated_surface_is_refused() {
    // THE 2026-09-07 FALSE GREEN, in its general form. Before the source could
    // be recovered from the clause this exported a document AY called
    // hole-free, trust-free and self-checkable that carcara refused.
    let mut terms = TermStore::new();
    let (proof, equality) = equiv_pos2_without_source_arg(&mut terms);
    let mut overrides = DetHashMap::default();
    overrides.insert(equality, "(and p q)".to_string());

    let error = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &super::scope_covering_proof(&proof),
        Some(&overrides),
    )
    .expect_err(
        "an equiv_pos2 with no source arg whose printed source is a conjunction must not ship",
    );
    match error {
        AlethePrintError::InvalidSurfaceStep { reason, .. } => {
            assert!(reason.contains("equiv_pos2"), "{reason}");
            assert!(reason.contains("printed surface"), "{reason}");
        }
        other => panic!("expected InvalidSurfaceStep, got {other:?}"),
    }
}

#[test]
fn and_neg_with_no_source_argument_is_judged_on_the_printed_and_term() {
    // `and_neg` had the ONE hand-written exemption for a missing source
    // argument, found by walking the term DAG for an and-term. Recovering from
    // the PRINTED clause subsumes it, and judges the text that actually ships:
    // an and-term whose surface override is not an and-term no longer slips
    // through the internal lookup.
    let mut terms = TermStore::new();
    let left = terms.mk_var("p", Sort::Bool);
    let right = terms.mk_var("q", Sort::Bool);
    let conjunction = terms.mk_app(Symbol::named("and"), [left, right], Sort::Bool);
    let not_left = terms.mk_not_raw(left);
    let not_right = terms.mk_not_raw(right);
    let mut proof = Proof::new();
    proof.add_rule_step(
        AletheRule::AndNeg,
        vec![conjunction, not_left, not_right],
        Vec::new(),
        Vec::new(),
    );

    let output = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &super::scope_covering_proof(&proof),
        None,
    )
    .expect("a spec-shaped and_neg must still export");
    assert!(
        output.contains("(step t0 (cl (and p q) (not p) (not q)) :rule and_neg)"),
        "{output}"
    );

    let mut overrides = DetHashMap::default();
    overrides.insert(conjunction, "(or p q)".to_string());
    let error = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &super::scope_covering_proof(&proof),
        Some(&overrides),
    )
    .expect_err("an and_neg whose printed source is a disjunction must not ship");
    assert!(
        matches!(error, AlethePrintError::InvalidSurfaceStep { .. }),
        "{error:?}"
    );
}

/// `(>= a 10)` and `(<= 10 a)`: ONE atom, two spellings, two term ids.
fn order_atom_pair(terms: &mut TermStore) -> (TermId, TermId) {
    let a = terms.mk_var("a", Sort::Int);
    let ten = terms.mk_int(10.into());
    let ge = terms.mk_app(Symbol::named(">="), [a, ten], Sort::Bool);
    let le = terms.mk_app(Symbol::named("<="), [ten, a], Sort::Bool);
    (ge, le)
}

#[test]
fn equiv_pos2_over_an_order_atom_states_the_orientation_it_relies_on() {
    // The exact six-line reproducer, as a unit: the source equality holds the
    // canonical `(<= 10 a)` while the traced literal is the authored
    // `(>= a 10)`. `equiv_pos2` compares them TEXTUALLY, so the step is
    // refused even though AY derived it.
    //
    // The repair is neither a relabel nor a silent respelling: the step keeps
    // `equiv_pos2` over the operands `equiv_pos2` actually relates, and the
    // orientation it relies on is STATED as a linear-arithmetic tautology the
    // checker verifies for itself.
    let mut terms = TermStore::new();
    let (ge, le) = order_atom_pair(&mut terms);
    let p = terms.mk_var("p", Sort::Bool);
    let equality = terms.mk_app(Symbol::named("="), [p, le], Sort::Bool);
    let not_equality = terms.mk_not_raw(equality);
    let not_p = terms.mk_not_raw(p);
    let mut proof = Proof::new();
    proof.add_rule_step(
        AletheRule::EquivPos2,
        vec![not_equality, not_p, ge],
        Vec::new(),
        Vec::new(),
    );

    let output = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &super::scope_covering_proof(&proof),
        None,
    )
    .expect("an order-atom equiv_pos2 must export through the orientation bridge");
    assert!(
        output.contains("(step t0a (cl (not (= p (<= 10 a))) (not p) (<= 10 a)) :rule equiv_pos2)"),
        "{output}"
    );
    assert!(
        output.contains("(cl (not (<= 10 a)) (>= a 10)) :rule la_generic :args (1 1)"),
        "{output}"
    );
    assert!(
        output.contains("(step t0 (cl (not (= p (<= 10 a))) (not p) (>= a 10)) :rule resolution"),
        "{output}"
    );
    // And never the bare false claim that shipped before.
    assert!(
        !output.contains("(step t0 (cl (not (= p (<= 10 a))) (not p) (>= a 10)) :rule equiv_pos2)"),
        "{output}"
    );
}

#[test]
fn or_decomposition_over_an_order_atom_states_the_orientation_it_relies_on() {
    // The same defect on the other side of the premise line. `or` zips its
    // premise's printed disjuncts against the conclusion's literals, so a
    // canonicalized premise and an authored conclusion are refused
    // ("expected terms to be equal: '(<= 10 a)' and '(>= a 10)'").
    let mut terms = TermStore::new();
    let (ge, le) = order_atom_pair(&mut terms);
    let q = terms.mk_var("q", Sort::Bool);
    let disjunction = terms.mk_app(Symbol::named("or"), [le, q], Sort::Bool);
    let mut proof = Proof::new();
    let premise = proof.add_assume(disjunction, None);
    proof.add_rule_step(AletheRule::Or, vec![ge, q], vec![premise], Vec::new());

    let output = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &super::scope_covering_proof(&proof),
        None,
    )
    .expect("an order-atom or decomposition must export through the orientation bridge");
    assert!(
        output.contains("(step t1.o (cl (<= 10 a) q) :rule or :premises (t0))"),
        "{output}"
    );
    assert!(
        output.contains("(cl (not (<= 10 a)) (>= a 10)) :rule la_generic :args (1 1)"),
        "{output}"
    );
    assert!(
        output.contains("(step t1 (cl (>= a 10) q) :rule resolution"),
        "{output}"
    );
    assert!(
        !output.contains("(step t1 (cl (>= a 10) q) :rule or"),
        "{output}"
    );
}

#[test]
fn or_decomposition_whose_premise_already_agrees_is_left_alone() {
    // The anti-regression half: an `or` whose printed premise and conclusion
    // already agree must stay byte-identical. A bridge that fires when it is
    // not needed adds unchecked steps to every document in the corpus.
    let mut terms = TermStore::new();
    let (_ge, le) = order_atom_pair(&mut terms);
    let q = terms.mk_var("q", Sort::Bool);
    let disjunction = terms.mk_app(Symbol::named("or"), [le, q], Sort::Bool);
    let mut proof = Proof::new();
    let premise = proof.add_assume(disjunction, None);
    proof.add_rule_step(AletheRule::Or, vec![le, q], vec![premise], Vec::new());

    let output = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &super::scope_covering_proof(&proof),
        None,
    )
    .expect("an already-agreeing or decomposition must still export");
    assert!(
        output.contains("(step t1 (cl (<= 10 a) q) :rule or :premises (t0))"),
        "{output}"
    );
    assert!(!output.contains("la_generic"), "{output}");
}

/// `(cl (not (= a b)) (not (p a)) (p b))` — a genuine `eq_congruent_pred`,
/// in both the flat rule-step form and the `EufCongruentPred` theory-lemma
/// form the lazy-EUF lane states.
fn eq_congruent_pred_clause(terms: &mut TermStore) -> (Vec<TermId>, TermId, TermId) {
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let p_a = terms.mk_app(Symbol::named("p"), [a], Sort::Bool);
    let p_b = terms.mk_app(Symbol::named("p"), [b], Sort::Bool);
    let hypothesis = terms.mk_app(Symbol::named("="), [a, b], Sort::Bool);
    let not_hypothesis = terms.mk_not_raw(hypothesis);
    let not_p_a = terms.mk_not_raw(p_a);
    (vec![not_hypothesis, not_p_a, p_b], hypothesis, p_a)
}

fn eq_congruent_pred_proofs(terms: &mut TermStore) -> (Vec<Proof>, TermId, TermId) {
    let (clause, hypothesis, p_a) = eq_congruent_pred_clause(terms);
    let mut rule_step = Proof::new();
    rule_step.add_rule_step(
        AletheRule::EqCongruentPred,
        clause.clone(),
        Vec::new(),
        Vec::new(),
    );
    let mut theory_lemma = Proof::new();
    theory_lemma.add_theory_lemma_with_kind(
        "EUF",
        clause,
        ay_core::TheoryLemmaKind::EufCongruentPred,
    );
    (vec![rule_step, theory_lemma], hypothesis, p_a)
}

#[test]
fn eq_congruent_pred_over_an_unmutated_surface_still_renders_eq_congruent_pred() {
    let mut terms = TermStore::new();
    let (proofs, _, _) = eq_congruent_pred_proofs(&mut terms);
    for proof in &proofs {
        let output = try_export_alethe_with_problem_scope_and_overrides(
            proof,
            &terms,
            &super::scope_covering_proof(proof),
            None,
        )
        .expect("a spec-shaped eq_congruent_pred must still export");
        assert!(
            output
                .contains("(step t0 (cl (not (= a b)) (not (p a)) (p b)) :rule eq_congruent_pred)"),
            "{output}"
        );
    }
}

/// The 2026-09-11 rule audit named `eq_congruent_pred` as the one relation
/// rule with no printed-surface judgement. Measured 2026-09-20: it is judged
/// over the printed text like `eq_transitive` and `eq_congruent` are, and a
/// surface whose printed operands no longer instantiate the rule ships as the
/// honest hole — the same mechanism as the sixth false green, applied to the
/// predicate form, must never print a rule name carcara refuses.
#[test]
fn eq_congruent_pred_whose_printed_operands_do_not_pair_is_judged_over_the_text() {
    let mut terms = TermStore::new();
    let (proofs, hypothesis, p_a) = eq_congruent_pred_proofs(&mut terms);
    // The hypothesis re-spelled as the corpus's Boolean-as-Int encoding: the
    // literal shape is still `(not (= .. ..))`, and the equated operands are
    // no longer the predicate's arguments.
    let mut encoded = DetHashMap::default();
    encoded.insert(hypothesis, "(= (ite (not (= a b)) 1 0) 0)".to_string());
    // The negated application re-spelled over a different argument.
    let mut retargeted = DetHashMap::default();
    retargeted.insert(p_a, "(p c)".to_string());
    for (label, overrides) in [("encoded", encoded), ("retargeted", retargeted)] {
        for proof in &proofs {
            let output = try_export_alethe_with_problem_scope_and_overrides(
                proof,
                &terms,
                &super::scope_covering_proof(proof),
                Some(&overrides),
            )
            .expect("the declining export must still produce a document");
            assert!(
                !output.contains(":rule eq_congruent_pred"),
                "{label}: eq_congruent_pred shipped over operands that do not pair: {output}"
            );
            assert!(output.contains(":rule hole"), "{label}: {output}");
        }
    }
}

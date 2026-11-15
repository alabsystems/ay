// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The printed-surface judgement for `eq_congruent`.
//!
//! Every case here is stated against pinned carcara 1.1.0's own
//! `eq_congruent` (`carcara/src/checker/rules/congruence.rs`), because the
//! only thing this predicate is allowed to mean is "the pinned checker will
//! accept this exact text" — plus the one repair the internal validator's
//! omitted-identical-position shape needs, which was checked against the
//! checker on a hand-built document in both directions (padded `valid`,
//! unpadded `no premise to justify equality of arguments`).

use super::{printed_eq_congruent_holds, PrintedCongruence};

fn holds(literals: &[&str]) -> bool {
    matches!(
        printed_eq_congruent_holds(literals),
        Ok(PrintedCongruence::Exact)
    )
}

fn padded(literals: &[&str]) -> Option<Vec<(usize, String)>> {
    match printed_eq_congruent_holds(literals) {
        Ok(PrintedCongruence::Padded(paddings)) => Some(paddings),
        _ => None,
    }
}

#[test]
fn a_canonical_congruence_holds() {
    assert!(holds(&[
        "(not (= a b))",
        "(not (= c d))",
        "(= (f a c) (f b d))"
    ]));
    assert!(holds(&["(not (= a b))", "(= (f a) (f b))"]));
}

#[test]
fn hypotheses_may_be_flipped_but_not_reordered() {
    // carcara pairs hypothesis `i` with argument position `i` and accepts
    // either orientation of that one equality.
    assert!(holds(&[
        "(not (= b a))",
        "(not (= d c))",
        "(= (f a c) (f b d))"
    ]));
    assert!(printed_eq_congruent_holds(
        &["(not (= c d))", "(not (= a b))", "(= (f a c) (f b d))",]
    )
    .is_err());
}

#[test]
fn the_omitted_identical_position_is_a_padding_not_an_instance() {
    // The `iso_brn925` `t1892` shape: `(op e0 e0)` against `(op e0 (op e0
    // e0))`, one hypothesis for two positions. AY's validator admits it
    // (position 0 is the same term); carcara wants one hypothesis per
    // position and refuses `MissingPremise`. The padding names the position
    // and the argument text the reflexive hypothesis quotes.
    assert_eq!(
        padded(&[
            "(not (= (op e0 e0) e0))",
            "(= (op e0 e0) (op e0 (op e0 e0)))",
        ]),
        Some(vec![(0, "e0".to_string())])
    );
    // Padding at the last position, and two paddings around one hypothesis.
    assert_eq!(
        padded(&["(not (= a b))", "(= (f a x) (f b x))"]),
        Some(vec![(1, "x".to_string())])
    );
    assert_eq!(
        padded(&["(not (= a b))", "(= (g x a y) (g x b y))"]),
        Some(vec![(0, "x".to_string()), (2, "y".to_string())])
    );
    // A hypothesis that IS the reflexive equality is consumed, not padded.
    assert!(holds(&[
        "(not (= a b))",
        "(not (= x x))",
        "(= (f a x) (f b x))"
    ]));
}

#[test]
fn every_hypothesis_must_be_consumed_in_argument_order() {
    // `TooManyPremises`, a leftover hypothesis after every position is
    // justified, and a hypothesis skipped past an identical position.
    assert!(
        printed_eq_congruent_holds(&["(not (= a b))", "(not (= c d))", "(= (f a) (f b))",])
            .is_err()
    );
    assert!(printed_eq_congruent_holds(
        &["(not (= a b))", "(not (= p q))", "(= (f a x) (f b x))",]
    )
    .is_err());
    assert!(printed_eq_congruent_holds(
        &["(not (= x y))", "(not (= q q))", "(= (f a x) (f a y))",]
    )
    .is_err());
}

#[test]
fn a_differing_position_without_a_hypothesis_does_not_hold() {
    // The internal validator's own negative case, over the text.
    assert!(printed_eq_congruent_holds(&["(not (= a b))", "(= (g a c) (g b d))"]).is_err());
}

#[test]
fn the_re_spelled_hypothesis_of_the_sixth_false_green_does_not_hold() {
    assert!(printed_eq_congruent_holds(&[
        "(not (= (ite (not (= a b)) 1 0) 0))",
        "(= (f a) (f b))",
    ])
    .is_err());
}

#[test]
fn heads_arities_and_shapes_carcara_refuses_do_not_hold() {
    // Different heads, different arities, a bare-symbol side, an indexed
    // head (neither `Term::App` nor `Term::Op` to the checker), a
    // conclusion that is not an equality, a hypothesis that is not a negated
    // equality, an n-ary equality, and the two-literal floor.
    assert!(printed_eq_congruent_holds(&["(not (= a b))", "(= (f a) (g b))"]).is_err());
    assert!(printed_eq_congruent_holds(&["(not (= a b))", "(= (f a) (f b c))"]).is_err());
    assert!(printed_eq_congruent_holds(&["(not (= a b))", "(= a b)"]).is_err());
    assert!(printed_eq_congruent_holds(&[
        "(not (= a b))",
        "(= ((_ extract 1 0) a) ((_ extract 1 0) b))",
    ])
    .is_err());
    assert!(printed_eq_congruent_holds(&["(not (= a b))", "(distinct (f a) (f b))"]).is_err());
    assert!(printed_eq_congruent_holds(&["(= a b)", "(= (f a) (f b))"]).is_err());
    assert!(printed_eq_congruent_holds(&["(not (= a b c))", "(= (f a) (f b))"]).is_err());
    assert!(printed_eq_congruent_holds(&["(= (f a) (f b))"]).is_err());
    assert!(printed_eq_congruent_holds(&[]).is_err());
}

#[test]
fn builtin_operators_are_applications_too() {
    // carcara's `Term::Op` arm: `(+ a c)` and `(+ b d)` share the operator,
    // and so do two `select`s.
    assert!(holds(&[
        "(not (= a b))",
        "(not (= c d))",
        "(= (+ a c) (+ b d))"
    ]));
    assert!(!holds(&["(not (= i j))", "(= (select m i) (select m j))"]));
    assert_eq!(
        padded(&["(not (= i j))", "(= (select m i) (select m j))"]),
        Some(vec![(0, "m".to_string())])
    );
}

#[test]
fn operand_spelling_differences_carcara_parses_to_one_term_still_hold() {
    assert!(holds(&["(not (= x #xAA))", "(= (f x) (f (_ bv170 8)))"]));
    assert!(holds(&["(not (= (g  a) b))", "(= (f (g a)) (f b))"]));
}

#[test]
fn identical_operands_longer_than_the_spelling_walk_cap_still_hold() {
    // The array lanes' units quote nested store chains of 80 KiB per operand
    // (`swap_t1_pp_sf_ai_00009_002` at `-T:120`); the modulo-spelling walk
    // refuses anything over its 64 KiB cap, identical or not, and three real
    // units were declined to holes through it. Identical text is the
    // checker's own identity.
    let mut big = String::from("a");
    for _ in 0..12_000 {
        big = format!("(store {big} i e)");
    }
    assert!(big.len() > 64 * 1024);
    let hypothesis = format!("(not (= i (sk {big} {big})))");
    let conclusion = format!("(= (select {big} i) (select {big} (sk {big} {big})))");
    assert_eq!(
        padded(&[&hypothesis, &conclusion]),
        Some(vec![(0, big.clone())])
    );
}

/// The OR-packed congruence unit the lazy-EUF lane states — `(cl (or ¬e_1 ..
/// ¬e_k e))`, one literal — spells as an `eq_congruent` over the printed
/// disjuncts, one `or_neg` per disjunct, and a closing `resolution` that
/// ships the unit's exact text under the step's own id.
fn raw_eq(
    terms: &mut ay_core::TermStore,
    lhs: ay_core::TermId,
    rhs: ay_core::TermId,
) -> ay_core::TermId {
    // Raw applications throughout: `mk_eq` canonicalises operand order and
    // `mk_or` sorts and dedupes, while the orientation and the producer's
    // order (conclusion last) are exactly what carcara reads.
    terms.mk_app(ay_core::Symbol::named("="), [lhs, rhs], ay_core::Sort::Bool)
}

fn packed_unit(
    terms: &mut ay_core::TermStore,
    hypotheses: &[(ay_core::TermId, ay_core::TermId)],
    conclusion: (ay_core::TermId, ay_core::TermId),
) -> (ay_core::TermId, Vec<ay_core::TermId>) {
    let mut disjuncts: Vec<ay_core::TermId> = hypotheses
        .iter()
        .map(|&(lhs, rhs)| {
            let equality = raw_eq(terms, lhs, rhs);
            terms.mk_not_raw(equality)
        })
        .collect();
    let goal = raw_eq(terms, conclusion.0, conclusion.1);
    disjuncts.push(goal);
    let unit = terms.mk_app(
        ay_core::Symbol::named("or"),
        disjuncts.clone(),
        ay_core::Sort::Bool,
    );
    (unit, disjuncts)
}

fn lemma(clause: Vec<ay_core::TermId>) -> ay_core::ProofStep {
    ay_core::ProofStep::TheoryLemma {
        theory: "EUF".to_string(),
        clause,
        farkas: None,
        kind: ay_core::TheoryLemmaKind::EufCongruent,
        lia: None,
    }
}

fn uninterpreted(
    terms: &mut ay_core::TermStore,
    name: &str,
    args: Vec<ay_core::TermId>,
) -> ay_core::TermId {
    terms.mk_app(ay_core::Symbol::named(name), args, ay_core::Sort::Int)
}

#[test]
fn a_packed_congruence_unit_is_spelled_over_its_printed_disjuncts() {
    use ay_core::{ProofId, Sort, TermStore};

    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);
    let d = terms.mk_var("d", Sort::Int);
    let fac = uninterpreted(&mut terms, "f", vec![a, c]);
    let fbd = uninterpreted(&mut terms, "f", vec![b, d]);
    let (unit, _) = packed_unit(&mut terms, &[(a, b), (d, c)], (fac, fbd));
    let printer = crate::AlethePrinter::new(&terms);
    let text = printer
        .format_step(&lemma(vec![unit]), ProofId(7))
        .expect("the packed unit exports");
    let expected = "(step t7.ec (cl (not (= a b)) (not (= d c)) (= (f a c) (f b d))) :rule eq_congruent)\n\
        (step t7.o0 (cl (or (not (= a b)) (not (= d c)) (= (f a c) (f b d))) (not (not (= a b)))) :rule or_neg :args (0))\n\
        (step t7.o1 (cl (or (not (= a b)) (not (= d c)) (= (f a c) (f b d))) (not (not (= d c)))) :rule or_neg :args (1))\n\
        (step t7.o2 (cl (or (not (= a b)) (not (= d c)) (= (f a c) (f b d))) (not (= (f a c) (f b d)))) :rule or_neg :args (2))\n\
        (step t7 (cl (or (not (= a b)) (not (= d c)) (= (f a c) (f b d)))) :rule resolution :premises (t7.ec t7.o0 t7.o1 t7.o2))";
    assert_eq!(text, expected);
}

#[test]
fn the_omitted_identical_position_unit_is_padded_with_a_reflexive_axiom() {
    // `iso_brn925` `t1892` byte for byte: `(op e0 e0) = e0 |- (op e0 e0) =
    // (op e0 (op e0 e0))`, position 0 identical and unhypothesised. The
    // hand-built document with exactly this text is `valid` under pinned
    // carcara; without the padding and its axiom it is `invalid`.
    use ay_core::{ProofId, Sort, TermStore};

    let mut terms = TermStore::new();
    let e0 = terms.mk_var("e0", Sort::Int);
    let op_e0_e0 = uninterpreted(&mut terms, "op", vec![e0, e0]);
    let op_e0_op = uninterpreted(&mut terms, "op", vec![e0, op_e0_e0]);
    let (unit, _) = packed_unit(&mut terms, &[(op_e0_e0, e0)], (op_e0_e0, op_e0_op));
    let printer = crate::AlethePrinter::new(&terms);
    let text = printer
        .format_step(&lemma(vec![unit]), ProofId(1892))
        .expect("the packed unit exports");
    let unit_text = "(or (not (= (op e0 e0) e0)) (= (op e0 e0) (op e0 (op e0 e0))))";
    let expected = format!(
        "(step t1892.ec (cl (not (= e0 e0)) (not (= (op e0 e0) e0)) (= (op e0 e0) (op e0 (op e0 e0)))) :rule eq_congruent)\n\
         (step t1892.r0 (cl (= e0 e0)) :rule eq_reflexive)\n\
         (step t1892.o0 (cl {unit_text} (not (not (= (op e0 e0) e0)))) :rule or_neg :args (0))\n\
         (step t1892.o1 (cl {unit_text} (not (= (op e0 e0) (op e0 (op e0 e0))))) :rule or_neg :args (1))\n\
         (step t1892 (cl {unit_text}) :rule resolution :premises (t1892.ec t1892.r0 t1892.o0 t1892.o1))"
    );
    assert_eq!(text, expected);
}

#[test]
fn a_packed_unit_whose_printed_surface_breaks_the_congruence_stays_a_hole() {
    // The sixth false green's mechanism, applied to the packed unit: over the
    // term DAG this is `a = b |- f(a) = f(b)`; the surface re-spells the
    // hypothesis as the corpus's Boolean-as-Int encoding, and no hypothesis
    // pairs over the text. The hole ships the same text the spelling would
    // have quoted.
    use ay_core::kani_compat::DetHashMap;
    use ay_core::{ProofId, Sort, TermStore};

    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let fa = uninterpreted(&mut terms, "f", vec![a]);
    let fb = uninterpreted(&mut terms, "f", vec![b]);
    let (unit, disjuncts) = packed_unit(&mut terms, &[(a, b)], (fa, fb));
    let mut overrides = DetHashMap::default();
    overrides.insert(
        disjuncts[0],
        "(not (= (ite (not (= a b)) 1 0) 0))".to_string(),
    );
    overrides.insert(
        unit,
        "(or (not (= (ite (not (= a b)) 1 0) 0)) (= (f a) (f b)))".to_string(),
    );
    let printer = crate::AlethePrinter::new_with_overrides(&terms, Some(&overrides));
    let text = printer
        .format_step(&lemma(vec![unit]), ProofId(1))
        .expect("the declining step still exports");
    assert_eq!(
        text,
        "(step t1 (cl (or (not (= (ite (not (= a b)) 1 0) 0)) (= (f a) (f b)))) :rule hole)"
    );
}

#[test]
fn a_packed_unit_that_is_not_an_or_over_the_text_stays_a_hole() {
    use ay_core::kani_compat::DetHashMap;
    use ay_core::{ProofId, Sort, TermStore};

    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let fa = uninterpreted(&mut terms, "f", vec![a]);
    let fb = uninterpreted(&mut terms, "f", vec![b]);
    let (unit, _) = packed_unit(&mut terms, &[(a, b)], (fa, fb));
    let mut overrides = DetHashMap::default();
    overrides.insert(unit, "(=> (= a b) (= (f a) (f b)))".to_string());
    let printer = crate::AlethePrinter::new_with_overrides(&terms, Some(&overrides));
    let text = printer
        .format_step(&lemma(vec![unit]), ProofId(1))
        .expect("the declining step still exports");
    assert_eq!(
        text,
        "(step t1 (cl (=> (= a b) (= (f a) (f b)))) :rule hole)"
    );
}

#[test]
fn a_packed_unit_with_an_unjustified_position_stays_a_hole() {
    // A producer defect, not a surface one: position 1 differs (`c` against
    // `d`) and carries no hypothesis.
    use ay_core::{ProofId, Sort, TermStore};

    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);
    let d = terms.mk_var("d", Sort::Int);
    let gac = uninterpreted(&mut terms, "g", vec![a, c]);
    let gbd = uninterpreted(&mut terms, "g", vec![b, d]);
    let (unit, _) = packed_unit(&mut terms, &[(a, b)], (gac, gbd));
    let printer = crate::AlethePrinter::new(&terms);
    let text = printer
        .format_step(&lemma(vec![unit]), ProofId(2))
        .expect("the declining step still exports");
    assert_eq!(
        text,
        "(step t2 (cl (or (not (= a b)) (= (g a c) (g b d)))) :rule hole)"
    );
}

#[test]
fn a_flat_exact_congruence_renders_byte_identically_on_both_paths() {
    // The judgement must not move a correct step: a flat clause that is an
    // exact instance prints exactly the default rendering, as a theory lemma
    // and as an `AletheRule::EqCongruent` step.
    use ay_core::{AletheRule, ProofId, Sort, TermStore};

    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let fa = uninterpreted(&mut terms, "f", vec![a]);
    let fb = uninterpreted(&mut terms, "f", vec![b]);
    let eq_ab = raw_eq(&mut terms, b, a);
    let not_ab = terms.mk_not_raw(eq_ab);
    let goal = raw_eq(&mut terms, fa, fb);
    let clause = vec![not_ab, goal];
    let expected = "(step t4 (cl (not (= b a)) (= (f a) (f b))) :rule eq_congruent)";

    let printer = crate::AlethePrinter::new(&terms);
    let text = printer
        .format_step(&lemma(clause.clone()), ProofId(4))
        .expect("the flat lemma exports");
    assert_eq!(text, expected);

    let step = ay_core::ProofStep::Step {
        rule: AletheRule::EqCongruent,
        clause: clause.clone(),
        premises: Vec::new(),
        args: Vec::new(),
    };
    let printer = crate::AlethePrinter::new(&terms);
    let text = printer
        .format_step(&step, ProofId(4))
        .expect("the flat rule step exports");
    assert_eq!(text, expected);
}

#[test]
fn a_flat_omitted_identical_position_is_padded_and_resolved_back() {
    use ay_core::{ProofId, Sort, TermStore};

    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let x = terms.mk_var("x", Sort::Int);
    let fax = uninterpreted(&mut terms, "f", vec![a, x]);
    let fbx = uninterpreted(&mut terms, "f", vec![b, x]);
    let eq_ab = raw_eq(&mut terms, a, b);
    let not_ab = terms.mk_not_raw(eq_ab);
    let goal = raw_eq(&mut terms, fax, fbx);
    let printer = crate::AlethePrinter::new(&terms);
    let text = printer
        .format_step(&lemma(vec![not_ab, goal]), ProofId(5))
        .expect("the flat lemma exports");
    assert_eq!(
        text,
        "(step t5.ec (cl (not (= a b)) (not (= x x)) (= (f a x) (f b x))) :rule eq_congruent)\n\
         (step t5.r1 (cl (= x x)) :rule eq_reflexive)\n\
         (step t5 (cl (not (= a b)) (= (f a x) (f b x))) :rule resolution :premises (t5.ec t5.r1))"
    );
}

#[test]
fn a_generic_eq_congruent_rule_step_is_judged_over_its_printed_surface() {
    // The judgement sits on the generic rule-step path too, not only on the
    // theory-lemma path. Mutation differential: the un-mutated flat step
    // renders `eq_congruent` byte-identically; the OR-packed unit under the
    // same rule whose surface re-spells the hypothesis declines to `hole`
    // (the flat re-spelled clause is refused earlier, by the AC bridge's
    // fail-closed arm, exactly as before); and a flat clause with a
    // differing position no hypothesis justifies — a producer defect the
    // default rendering used to ship under the rule name — is the honest
    // hole.
    use ay_core::kani_compat::DetHashMap;
    use ay_core::{AletheRule, Proof, Sort, TermStore};

    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let fa = uninterpreted(&mut terms, "f", vec![a]);
    let fb = uninterpreted(&mut terms, "f", vec![b]);
    let eq_ab = terms.mk_eq(a, b);
    let not_ab = terms.mk_not(eq_ab);
    let goal = terms.mk_eq(fa, fb);
    let clause = vec![not_ab, goal];
    let mut proof = Proof::new();
    proof.add_rule_step(
        AletheRule::EqCongruent,
        clause.clone(),
        Vec::new(),
        Vec::new(),
    );
    let clean =
        crate::try_export_alethe_with_problem_scope_and_overrides(&proof, &terms, &clause, None)
            .expect("a spec-shaped eq_congruent rule step must still export");
    assert!(
        clean.contains(":rule eq_congruent)") && !clean.contains(":rule hole"),
        "{clean}"
    );

    let (unit, disjuncts) = packed_unit(&mut terms, &[(a, b)], (fa, fb));
    let mut packed = Proof::new();
    packed.add_rule_step(AletheRule::EqCongruent, vec![unit], Vec::new(), Vec::new());
    let spelled =
        crate::try_export_alethe_with_problem_scope_and_overrides(&packed, &terms, &[unit], None)
            .expect("the packed rule step exports");
    assert!(
        spelled.contains("(step t0.ec (cl (not (= a b)) (= (f a) (f b))) :rule eq_congruent)")
            && spelled.contains(":rule resolution :premises (t0.ec t0.o0 t0.o1))"),
        "{spelled}"
    );
    let mut overrides = DetHashMap::default();
    overrides.insert(
        disjuncts[0],
        "(not (= (ite (not (= a b)) 1 0) 0))".to_string(),
    );
    overrides.insert(
        unit,
        "(or (not (= (ite (not (= a b)) 1 0) 0)) (= (f a) (f b)))".to_string(),
    );
    let mutated = crate::try_export_alethe_with_problem_scope_and_overrides(
        &packed,
        &terms,
        &[unit],
        Some(&overrides),
    )
    .expect("the declining export must still produce a document");
    assert!(
        mutated.contains(
            "(step t0 (cl (or (not (= (ite (not (= a b)) 1 0) 0)) (= (f a) (f b)))) :rule hole)"
        ),
        "{mutated}"
    );
    assert!(!mutated.contains(":rule eq_congruent"), "{mutated}");

    let c = terms.mk_var("c", Sort::Int);
    let d = terms.mk_var("d", Sort::Int);
    let gac = uninterpreted(&mut terms, "g", vec![a, c]);
    let gbd = uninterpreted(&mut terms, "g", vec![b, d]);
    let unjustified = raw_eq(&mut terms, gac, gbd);
    let defect = vec![not_ab, unjustified];
    let mut defective = Proof::new();
    defective.add_rule_step(
        AletheRule::EqCongruent,
        defect.clone(),
        Vec::new(),
        Vec::new(),
    );
    let holed = crate::try_export_alethe_with_problem_scope_and_overrides(
        &defective, &terms, &defect, None,
    )
    .expect("the declining export must still produce a document");
    assert!(
        holed.contains("(step t0 (cl (not (= a b)) (= (g a c) (g b d))) :rule hole)"),
        "{holed}"
    );
    assert!(!holed.contains(":rule eq_congruent"), "{holed}");
}

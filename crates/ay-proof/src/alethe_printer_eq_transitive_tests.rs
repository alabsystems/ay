// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The printed-surface chain check for `eq_transitive`.
//!
//! Every case here is stated against pinned carcara 1.1.0's own
//! `eq_transitive` (`carcara/src/checker/rules/transitivity.rs`), because the
//! only thing this predicate is allowed to mean is "the pinned checker will
//! accept this exact text".

use super::printed_eq_transitive_chain_holds;

#[test]
fn a_canonical_chain_holds() {
    assert!(printed_eq_transitive_chain_holds(&[
        "(not (= a b))",
        "(not (= b c))",
        "(= a c)",
    ]));
}

#[test]
fn hypotheses_may_be_reordered_and_flipped() {
    // carcara's `find_chain` searches the remaining hypotheses at every hop
    // and orients each one itself, so neither source order nor the operand
    // order inside a hypothesis matters.
    assert!(printed_eq_transitive_chain_holds(&[
        "(not (= c b))",
        "(not (= a b))",
        "(= a c)",
    ]));
}

#[test]
fn an_unused_extra_hypothesis_still_holds() {
    // Extra `(not (= ..))` disjuncts only weaken the clause; carcara stops as
    // soon as the chain closes and never asks that every hypothesis be used.
    assert!(printed_eq_transitive_chain_holds(&[
        "(not (= a b))",
        "(not (= p q))",
        "(not (= b c))",
        "(= a c)",
    ]));
}

#[test]
fn a_reflexive_conclusion_holds_with_any_hypotheses() {
    // `find_chain` returns immediately when the conclusion's sides coincide.
    assert!(printed_eq_transitive_chain_holds(&[
        "(not (= a b))",
        "(not (= b c))",
        "(= a a)",
    ]));
}

#[test]
fn the_ite_encoded_slia_surface_does_not_hold() {
    // The 2026-09-12 false green, reduced. Over the term DAG this is the chain
    // at2 = at4, at2 = at3, at3 = at6 |- at4 = at6. Over the text the document
    // ships, each atom is its authored `(= (ite (not (= ..)) 1 0) 0)` encoding,
    // the shapes are all still right, and no chain connects the conclusion.
    assert!(!printed_eq_transitive_chain_holds(&[
        "(not (= (ite (not (= (str.at s 2) (str.at s 4))) 1 0) 0))",
        "(not (= (ite (not (= (str.at s 2) (str.at s 3))) 1 0) 0))",
        "(not (= (ite (not (= (str.at s 3) (str.at s 6))) 1 0) 0))",
        "(= (ite (not (= (str.at s 4) (str.at s 6))) 1 0) 0)",
    ]));
}

#[test]
fn the_same_clause_over_its_canonical_atoms_does_hold() {
    // The mutation differential for the case above: the internal clause AY
    // derived IS a chain, so the predicate is refusing the rendering, not the
    // derivation.
    assert!(printed_eq_transitive_chain_holds(&[
        "(not (= (str.at s 2) (str.at s 4)))",
        "(not (= (str.at s 2) (str.at s 3)))",
        "(not (= (str.at s 3) (str.at s 6)))",
        "(= (str.at s 4) (str.at s 6))",
    ]));
}

#[test]
fn a_conclusion_that_is_not_last_does_not_hold() {
    // carcara reads the conclusion off `conclusion.last()`; anywhere else and
    // the step is refused for `(= ..)` failing the `(not (= ..))` match.
    assert!(!printed_eq_transitive_chain_holds(&[
        "(= a c)",
        "(not (= a b))",
        "(not (= b c))",
    ]));
}

#[test]
fn a_two_literal_clause_does_not_hold() {
    // `assert_clause_len(conclusion, 3..)`.
    assert!(!printed_eq_transitive_chain_holds(&[
        "(not (= a b))",
        "(= a b)"
    ]));
}

#[test]
fn a_hypothesis_that_is_not_a_negated_equality_does_not_hold() {
    assert!(!printed_eq_transitive_chain_holds(&[
        "(not (= a b))",
        "(= (= b c) false)",
        "(= a c)",
    ]));
    assert!(!printed_eq_transitive_chain_holds(&[
        "(not (= a b))",
        "(distinct b c)",
        "(= a c)",
    ]));
}

#[test]
fn an_n_ary_equality_does_not_hold() {
    // carcara's `match_term_err!((= t u) = ..)` is binary.
    assert!(!printed_eq_transitive_chain_holds(&[
        "(not (= a b c))",
        "(not (= b c))",
        "(= a c)",
    ]));
    assert!(!printed_eq_transitive_chain_holds(&[
        "(not (= a b))",
        "(not (= b c))",
        "(= a b c)",
    ]));
}

#[test]
fn a_disconnected_chain_does_not_hold() {
    assert!(!printed_eq_transitive_chain_holds(&[
        "(not (= a b))",
        "(not (= c d))",
        "(= a d)",
    ]));
}

#[test]
fn operand_spelling_differences_carcara_parses_to_one_term_still_hold() {
    // Whitespace inside an application and alternate bit-vector literal
    // spellings are one term to carcara, so byte equality would refuse steps
    // the checker accepts — a guard that fires on correct steps destroys
    // evidence.
    assert!(printed_eq_transitive_chain_holds(&[
        "(not (= (select m  i) x))",
        "(not (= (select m i) y))",
        "(= x y)",
    ]));
    assert!(printed_eq_transitive_chain_holds(&[
        "(not (= x #xAA))",
        "(not (= (_ bv170 8) y))",
        "(= x y)",
    ]));
}

/// The guard must sit on the GENERIC rule-step path too, not only on the
/// theory-lemma path: `AletheRule::EqTransitive` steps are produced in a dozen
/// places (`proof_euf_lemma.rs`, `proof_original_rebuild.rs`, the authored
/// affine/array routes) and print through `format_generic_step`.
///
/// Mutation differential. The un-mutated export must render `eq_transitive`
/// byte-identically — a guard that fires on correct steps destroys evidence —
/// and the export whose surface re-spells each chain operand as the corpus's
/// `(= (ite (not (= .. ..)) 1 0) 0)` encoding must decline to `hole`.
#[test]
fn a_generic_eq_transitive_rule_step_is_judged_over_its_printed_surface() {
    use ay_core::kani_compat::DetHashMap;
    use ay_core::{AletheRule, Proof, Sort, TermStore};

    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);
    let eq_ab = terms.mk_eq(a, b);
    let eq_bc = terms.mk_eq(b, c);
    let eq_ac = terms.mk_eq(a, c);
    let not_ab = terms.mk_not(eq_ab);
    let not_bc = terms.mk_not(eq_bc);
    let clause = vec![not_ab, not_bc, eq_ac];
    let mut proof = Proof::new();
    proof.add_rule_step(
        AletheRule::EqTransitive,
        clause.clone(),
        Vec::new(),
        Vec::new(),
    );

    let clean =
        crate::try_export_alethe_with_problem_scope_and_overrides(&proof, &terms, &clause, None)
            .expect("a spec-shaped eq_transitive rule step must still export");
    assert!(
        clean.contains("(step t0 (cl (not (= a b)) (not (= b c)) (= a c)) :rule eq_transitive)"),
        "{clean}"
    );

    let mut overrides = DetHashMap::default();
    overrides.insert(eq_ab, "(= (ite (not (= a b)) 1 0) 0)".to_string());
    overrides.insert(eq_bc, "(= (ite (not (= b c)) 1 0) 0)".to_string());
    overrides.insert(eq_ac, "(= (ite (not (= a c)) 1 0) 0)".to_string());
    let mutated = crate::try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &clause,
        Some(&overrides),
    )
    .expect("the declining export must still produce a document");
    assert!(mutated.contains(":rule hole"), "{mutated}");
    assert!(!mutated.contains(":rule eq_transitive"), "{mutated}");
}

/// The OR-packed transitivity unit the lazy-EUF lane states — `(cl (or ¬e_1
/// .. ¬e_k e))`, one literal — spells as an `eq_transitive` over the printed
/// disjuncts, one `or_neg` per disjunct, and a closing `resolution` that
/// ships the unit's exact text under the step's own id, so its `or` consumer
/// reads the same conclusion it always did.
fn packed_unit(
    terms: &mut ay_core::TermStore,
    hypotheses: &[(ay_core::TermId, ay_core::TermId)],
    conclusion: (ay_core::TermId, ay_core::TermId),
) -> (ay_core::TermId, Vec<ay_core::TermId>) {
    // Raw applications throughout: `mk_eq` canonicalises operand order and
    // `mk_or` sorts and dedupes, while the orientation and the producer's
    // order (conclusion last) are exactly what carcara reads.
    let raw_eq = |terms: &mut ay_core::TermStore, lhs, rhs| {
        terms.mk_app(ay_core::Symbol::named("="), [lhs, rhs], ay_core::Sort::Bool)
    };
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

fn packed_step(unit: ay_core::TermId) -> ay_core::ProofStep {
    ay_core::ProofStep::TheoryLemma {
        theory: "EUF".to_string(),
        clause: vec![unit],
        farkas: None,
        kind: ay_core::TheoryLemmaKind::EufTransitive,
        lia: None,
    }
}

#[test]
fn a_packed_transitivity_unit_is_spelled_over_its_printed_disjuncts() {
    use ay_core::{ProofId, Sort, TermStore};

    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);
    let (unit, _) = packed_unit(&mut terms, &[(a, b), (b, c)], (a, c));
    let printer = crate::AlethePrinter::new(&terms);
    let text = printer
        .format_step(&packed_step(unit), ProofId(7))
        .expect("the packed unit exports");
    let expected = "(step t7.et (cl (not (= a b)) (not (= b c)) (= a c)) :rule eq_transitive)\n\
        (step t7.o0 (cl (or (not (= a b)) (not (= b c)) (= a c)) (not (not (= a b)))) :rule or_neg :args (0))\n\
        (step t7.o1 (cl (or (not (= a b)) (not (= b c)) (= a c)) (not (not (= b c)))) :rule or_neg :args (1))\n\
        (step t7.o2 (cl (or (not (= a b)) (not (= b c)) (= a c)) (not (= a c))) :rule or_neg :args (2))\n\
        (step t7 (cl (or (not (= a b)) (not (= b c)) (= a c))) :rule resolution :premises (t7.et t7.o0 t7.o1 t7.o2))";
    assert_eq!(text, expected);
}

#[test]
fn a_packed_unit_with_flipped_hypotheses_needs_no_symmetry_step() {
    // carcara's `find_chain` orients each hypothesis itself; 742 of the 974
    // ledger units (2026-09-20) carry at least one flipped equality.
    use ay_core::{ProofId, Sort, TermStore};

    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);
    let d = terms.mk_var("d", Sort::Int);
    let e = terms.mk_var("e", Sort::Int);
    // Hypotheses out of chain order and every one flipped: d = c, b = a,
    // c = b, e = d |- a = e.
    let (unit, _) = packed_unit(&mut terms, &[(d, c), (b, a), (c, b), (e, d)], (a, e));
    let printer = crate::AlethePrinter::new(&terms);
    let text = printer
        .format_step(&packed_step(unit), ProofId(3))
        .expect("the packed unit exports");
    assert!(
        text.starts_with(
            "(step t3.et (cl (not (= d c)) (not (= b a)) (not (= c b)) (not (= e d)) (= a e)) :rule eq_transitive)\n"
        ),
        "{text}"
    );
    assert!(text.contains(":rule or_neg :args (4))"), "{text}");
    assert!(
        text.ends_with(":rule resolution :premises (t3.et t3.o0 t3.o1 t3.o2 t3.o3 t3.o4))"),
        "{text}"
    );
    assert!(!text.contains(":rule hole"), "{text}");
    assert!(!text.contains("eq_symmetric"), "{text}");
}

#[test]
fn a_packed_unit_whose_printed_surface_breaks_the_chain_stays_a_hole() {
    // The sixth false green's mechanism, applied to the packed unit: over the
    // term DAG this is the chain a = b, b = c |- a = c; the surface re-spells
    // one hypothesis as the corpus's Boolean-as-Int encoding, and no chain
    // survives over the text. The hole ships the same text the spelling
    // would have quoted.
    use ay_core::kani_compat::DetHashMap;
    use ay_core::{ProofId, Sort, TermStore};

    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);
    let (unit, disjuncts) = packed_unit(&mut terms, &[(a, b), (b, c)], (a, c));
    let mut overrides = DetHashMap::default();
    overrides.insert(
        disjuncts[0],
        "(not (= (ite (not (= a b)) 1 0) 0))".to_string(),
    );
    overrides.insert(
        unit,
        "(or (not (= (ite (not (= a b)) 1 0) 0)) (not (= b c)) (= a c))".to_string(),
    );
    let printer = crate::AlethePrinter::new_with_overrides(&terms, Some(&overrides));
    let text = printer
        .format_step(&packed_step(unit), ProofId(1))
        .expect("the declining step still exports");
    assert_eq!(
        text,
        "(step t1 (cl (or (not (= (ite (not (= a b)) 1 0) 0)) (not (= b c)) (= a c))) :rule hole)"
    );
}

#[test]
fn a_packed_unit_that_is_not_an_or_over_the_text_stays_a_hole() {
    // The unit's own override re-spells the whole disjunction; nothing the
    // spelling would quote is on the wire, so it declines over that text.
    use ay_core::kani_compat::DetHashMap;
    use ay_core::{ProofId, Sort, TermStore};

    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);
    let (unit, _) = packed_unit(&mut terms, &[(a, b), (b, c)], (a, c));
    let mut overrides = DetHashMap::default();
    overrides.insert(unit, "(=> (and (= a b) (= b c)) (= a c))".to_string());
    let printer = crate::AlethePrinter::new_with_overrides(&terms, Some(&overrides));
    let text = printer
        .format_step(&packed_step(unit), ProofId(1))
        .expect("the declining step still exports");
    assert_eq!(
        text,
        "(step t1 (cl (=> (and (= a b) (= b c)) (= a c))) :rule hole)"
    );
}

#[test]
fn a_two_disjunct_packed_unit_stays_a_hole() {
    // `(or (not (= a b)) (= b a))` is a valid `EufTransitive` lemma internally
    // (a one-edge path), but carcara's `eq_transitive` floor is three
    // literals; the packed spelling declines rather than pad the chain.
    use ay_core::{ProofId, Sort, TermStore};

    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let (unit, _) = packed_unit(&mut terms, &[(a, b)], (b, a));
    let printer = crate::AlethePrinter::new(&terms);
    let text = printer
        .format_step(&packed_step(unit), ProofId(2))
        .expect("the declining step still exports");
    assert_eq!(text, "(step t2 (cl (or (not (= a b)) (= b a))) :rule hole)");
}

#[test]
fn a_packed_unit_with_a_disconnected_chain_stays_a_hole() {
    // A producer defect, not a surface one: the disjuncts have the right
    // shapes and no chain connects the conclusion.
    use ay_core::{ProofId, Sort, TermStore};

    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);
    let d = terms.mk_var("d", Sort::Int);
    let (unit, _) = packed_unit(&mut terms, &[(a, b), (c, d)], (a, d));
    let printer = crate::AlethePrinter::new(&terms);
    let text = printer
        .format_step(&packed_step(unit), ProofId(2))
        .expect("the declining step still exports");
    assert!(text.ends_with(":rule hole)"), "{text}");
    assert!(!text.contains("eq_transitive"), "{text}");
}

/// The packed unit `lo = #x04, hi = #x04 |- lo = hi`, exported as step `t5`
/// with the premise `lo = #x04` spelled `(= lo {spelling})`, as the authored
/// surface re-spells a closed bit-vector term AY folded.
fn packed_closed_bitvec_step(spelling: &str) -> String {
    use ay_core::kani_compat::DetHashMap;
    use ay_core::{ProofId, Sort, Symbol, TermStore};

    let mut terms = TermStore::new();
    let lo = terms.mk_var("lo", Sort::bitvec(8));
    let hi = terms.mk_var("hi", Sort::bitvec(8));
    let four = terms.mk_bitvec(num_bigint::BigInt::from(4u8), 8);
    let (unit, _) = packed_unit(&mut terms, &[(lo, four), (hi, four)], (lo, hi));
    let folded = terms.mk_app(Symbol::named("="), [lo, four], Sort::Bool);
    let mut overrides = DetHashMap::default();
    overrides.insert(folded, format!("(= lo {spelling})"));
    let printer = crate::AlethePrinter::new_with_overrides(&terms, Some(&overrides));
    printer
        .format_step(&packed_step(unit), ProofId(5))
        .expect("the packed unit exports")
}

#[test]
fn a_packed_unit_broken_only_by_a_closed_bitvec_spelling_is_bridged() {
    // The printed disjuncts meet at two spellings of one value, which carcara
    // refuses as a broken chain. `t5.et` is the flat path's closed-spelling
    // bridge (43a040081) for exactly the flat clause: `evaluate` proves the
    // missing link, a re-judged `eq_transitive` and a `resolution` close it.
    // The `or_neg` repack is the one every packed unit ships.
    let text = packed_closed_bitvec_step("(concat #x0 #x4)");
    let printed = "(or (not (= lo (concat #x0 #x4))) (not (= hi #b00000100)) (= lo hi))";
    let expected = format!(
        "(step t5.et.gb0 (cl (= (concat #x0 #x4) #b00000100)) :rule evaluate)\n\
         (step t5.et.gb.et (cl (not (= lo (concat #x0 #x4))) (not (= (concat #x0 #x4) #b00000100)) (not (= hi #b00000100)) (= lo hi)) :rule eq_transitive)\n\
         (step t5.et (cl (not (= lo (concat #x0 #x4))) (not (= hi #b00000100)) (= lo hi)) :rule resolution :premises (t5.et.gb.et t5.et.gb0))\n\
         (step t5.o0 (cl {printed} (not (not (= lo (concat #x0 #x4))))) :rule or_neg :args (0))\n\
         (step t5.o1 (cl {printed} (not (not (= hi #b00000100)))) :rule or_neg :args (1))\n\
         (step t5.o2 (cl {printed} (not (= lo hi))) :rule or_neg :args (2))\n\
         (step t5 (cl {printed}) :rule resolution :premises (t5.et t5.o0 t5.o1 t5.o2))"
    );
    assert_eq!(text, expected);
}

#[test]
fn a_packed_unit_broken_by_an_excluded_operator_stays_a_hole() {
    // The negative twin: pinned carcara 1.1.0 evaluates `bvsub` wrongly (this
    // one to #xfc, not #x04), so the bridge never evaluates it and the unit
    // ships as the honest hole over its exact text, with no partial
    // derivation.
    let text = packed_closed_bitvec_step("(bvsub #xff #xfb)");
    assert_eq!(
        text,
        "(step t5 (cl (or (not (= lo (bvsub #xff #xfb))) (not (= hi #b00000100)) (= lo hi))) :rule hole)"
    );
}

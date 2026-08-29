// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for checked surface and divisibility wire repairs.

use super::*;
use crate::try_export_alethe_with_problem_scope_and_overrides;
use ay_core::AletheRule;

fn scope_covering_proof(proof: &Proof) -> Vec<TermId> {
    let mut scope = Vec::new();
    for step in &proof.steps {
        match step {
            ProofStep::Assume(term) => scope.push(*term),
            ProofStep::Resolution { clause, pivot, .. } => {
                scope.extend(clause.iter().copied());
                scope.push(*pivot);
            }
            ProofStep::TheoryLemma { clause, .. } => scope.extend(clause.iter().copied()),
            ProofStep::Step { clause, args, .. } => {
                scope.extend(clause.iter().copied());
                scope.extend(args.iter().copied());
            }
            _ => {}
        }
    }
    scope
}

#[test]
fn test_cong_bridge_repairs_exact_multiplication_operand_swap() {
    use ay_core::kani_compat::DetHashMap;
    use ay_core::Symbol;

    let mut terms = TermStore::new();
    let c = terms.mk_var("c", Sort::Int);
    let s = terms.mk_var("s", Sort::Int);
    let sixteen = terms.mk_int(16.into());
    let seven = terms.mk_int(7.into());
    let mul = terms.mk_app(Symbol::named("*"), [c, sixteen], Sort::Int);
    let left = terms.mk_app(Symbol::named("+"), [mul, s], Sort::Int);
    let right = terms.mk_app(Symbol::named("+"), [mul, seven], Sort::Int);
    let premise_equality = terms.mk_app(Symbol::named("="), [s, seven], Sort::Bool);
    let conclusion = terms.mk_app(Symbol::named("="), [left, right], Sort::Bool);

    let mut proof = Proof::new();
    let premise = proof.add_assume(premise_equality, None);
    proof.add_rule_step(
        AletheRule::Cong,
        vec![conclusion],
        vec![premise],
        Vec::new(),
    );

    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(left, "(+ (* 16 c) s)".to_string());
    let output = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &scope_covering_proof(&proof),
        Some(&overrides),
    )
    .expect("an exact Int multiplication swap has a checked congruence bridge");
    assert!(
        output.contains("(step t1.ac0 (cl (= (* 16 c) (* c 16))) :rule aci_simp)"),
        "{output}"
    );
    assert!(
        output.contains(":rule cong :premises (t1.ac0 t0)"),
        "{output}"
    );
}

#[test]
fn test_cong_bridge_lifts_nested_multiplication_swap_positionally() {
    use ay_core::kani_compat::DetHashMap;
    use ay_core::Symbol;

    let mut terms = TermStore::new();
    let c = terms.mk_var("c", Sort::Int);
    let q = terms.mk_var("q", Sort::Int);
    let s = terms.mk_var("s", Sort::Int);
    let t = terms.mk_var("t", Sort::Int);
    let sixteen = terms.mk_int(16.into());
    let mul = terms.mk_app(Symbol::named("*"), [c, sixteen], Sort::Int);
    let nested = terms.mk_app(Symbol::named("+"), [mul, q], Sort::Int);
    let left = terms.mk_app(Symbol::named("f"), [nested, s], Sort::Int);
    let right = terms.mk_app(Symbol::named("f"), [nested, t], Sort::Int);
    let premise_equality = terms.mk_app(Symbol::named("="), [s, t], Sort::Bool);
    let conclusion = terms.mk_app(Symbol::named("="), [left, right], Sort::Bool);

    let mut proof = Proof::new();
    let premise = proof.add_assume(premise_equality, None);
    proof.add_rule_step(
        AletheRule::Cong,
        vec![conclusion],
        vec![premise],
        Vec::new(),
    );

    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(right, "(f (+ (* 16 c) q) t)".to_string());
    let output = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &scope_covering_proof(&proof),
        Some(&overrides),
    )
    .expect("a nested multiplication swap has a checked congruence chain");
    assert!(
        output.contains("(step t1.ac0.c0 (cl (= (* c 16) (* 16 c))) :rule aci_simp)"),
        "{output}"
    );
    assert!(
        output.contains(":rule cong :premises (t1.ac0.c0)")
            && output.contains(":rule cong :premises (t1.ac0 t0)"),
        "{output}"
    );
}

#[test]
fn test_cong_bridge_composes_surface_spelling_with_a_native_premise() {
    use ay_core::kani_compat::DetHashMap;
    use ay_core::Symbol;

    let mut terms = TermStore::new();
    let c = terms.mk_var("c", Sort::Int);
    let s = terms.mk_var("s", Sort::Int);
    let t = terms.mk_var("t", Sort::Int);
    let sixteen = terms.mk_int(16.into());
    let mul = terms.mk_app(Symbol::named("*"), [c, sixteen], Sort::Int);
    let left_nested = terms.mk_app(Symbol::named("+"), [mul, s], Sort::Int);
    let right_nested = terms.mk_app(Symbol::named("+"), [mul, t], Sort::Int);
    let left = terms.mk_app(Symbol::named("f"), [left_nested], Sort::Int);
    let right = terms.mk_app(Symbol::named("f"), [right_nested], Sort::Int);
    let premise_equality =
        terms.mk_app(Symbol::named("="), [left_nested, right_nested], Sort::Bool);
    let conclusion = terms.mk_app(Symbol::named("="), [left, right], Sort::Bool);

    let mut proof = Proof::new();
    let premise = proof.add_assume(premise_equality, None);
    proof.add_rule_step(
        AletheRule::Cong,
        vec![conclusion],
        vec![premise],
        Vec::new(),
    );

    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(left, "(f (+ (* 16 c) s))".to_string());
    overrides.insert(right, "(f (+ (* 16 c) t))".to_string());
    let output = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &scope_covering_proof(&proof),
        Some(&overrides),
    )
    .expect("surface spellings compose with the exact native premise");
    assert!(
        output.contains(":rule trans :premises (t1.ac0.l t0 t1.ac0.r)"),
        "{output}"
    );
    assert!(output.contains(":rule cong :premises (t1.ac0)"), "{output}");
}

#[test]
fn test_resolution_bridges_an_authored_symmetric_equality_pivot() {
    use ay_core::kani_compat::DetHashMap;
    use ay_core::Symbol;

    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let equality = terms.mk_app(Symbol::named("="), [b, a], Sort::Bool);
    let negated = terms.mk_not(equality);
    let mut proof = Proof::new();
    let positive = proof.add_assume(equality, None);
    let negative = proof.add_assume(negated, None);
    proof.add_resolution(Vec::new(), equality, positive, negative);

    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(negated, "(not (= a b))".to_string());
    let output = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &scope_covering_proof(&proof),
        Some(&overrides),
    )
    .expect("symmetric authored equality pivot has a checked bridge");
    assert!(
        output.contains("(step t2.s (cl (= a b)) :rule symm :premises (t0))")
            && output.contains("(step t2 (cl) :rule resolution :premises (t2.s t1))"),
        "{output}"
    );
}

#[test]
fn test_resolution_bridge_accepts_equal_bitvector_literal_spellings() {
    use ay_core::kani_compat::DetHashMap;
    use ay_core::Symbol;

    let mut terms = TermStore::new();
    let value = terms.mk_var("value", Sort::bitvec(8));
    let aa = terms.mk_bitvec(170u32.into(), 8);
    let equality = terms.mk_app(Symbol::named("="), [aa, value], Sort::Bool);
    let negated = terms.mk_not(equality);
    let mut proof = Proof::new();
    let positive = proof.add_assume(equality, None);
    let negative = proof.add_assume(negated, None);
    proof.add_resolution(Vec::new(), equality, positive, negative);

    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(negated, "(not (= value #xAA))".to_string());
    let output = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &scope_covering_proof(&proof),
        Some(&overrides),
    )
    .expect("equal bit-vector spellings preserve a symmetric resolution pivot");
    assert!(
        output.contains("(step t2.s (cl (= value #xAA)) :rule symm :premises (t0))")
            && output.contains("(step t2 (cl) :rule resolution :premises (t2.s t1))"),
        "{output}"
    );
}

fn symmetric_resolution_bridge_fixture(
    nonunit_positive: bool,
    nonempty_resolvent: bool,
) -> (
    TermStore,
    Proof,
    ay_core::kani_compat::DetHashMap<TermId, String>,
) {
    use ay_core::kani_compat::DetHashMap;
    use ay_core::Symbol;

    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let extra = terms.mk_var("extra", Sort::Bool);
    let equality = terms.mk_app(Symbol::named("="), [b, a], Sort::Bool);
    let negated = terms.mk_not(equality);
    let mut proof = Proof::new();
    let base = proof.add_assume(equality, None);
    let positive = if nonunit_positive {
        proof.add_rule_step(
            AletheRule::Weakening,
            vec![equality, extra],
            vec![base],
            Vec::new(),
        )
    } else {
        base
    };
    let negative = proof.add_assume(negated, None);
    let clause = nonempty_resolvent.then_some(extra).into_iter().collect();
    proof.add_resolution(clause, equality, positive, negative);
    let mut overrides = DetHashMap::default();
    overrides.insert(negated, "(not (= a b))".to_string());
    (terms, proof, overrides)
}

#[test]
fn test_resolution_bridge_declines_a_nonunit_premise() {
    let (terms, proof, overrides) = symmetric_resolution_bridge_fixture(true, false);
    let printer = AlethePrinter::new_with_overrides(&terms, Some(&overrides));
    printer
        .prepare_proof(&proof)
        .expect("prepare proof clauses");
    assert!(
        printer
            .symmetric_equality_resolution_bridge(ProofId(3), &[], ProofId(1), ProofId(2))
            .is_none(),
        "a nonunit premise must remain outside the symmetry bridge"
    );
}

#[test]
fn test_resolution_bridge_declines_a_nonempty_resolvent() {
    let (terms, proof, overrides) = symmetric_resolution_bridge_fixture(false, true);
    let printer = AlethePrinter::new_with_overrides(&terms, Some(&overrides));
    printer
        .prepare_proof(&proof)
        .expect("prepare proof clauses");
    assert!(
        printer
            .symmetric_equality_resolution_bridge(
                ProofId(2),
                match &proof.steps[2] {
                    ProofStep::Resolution { clause, .. } => clause,
                    _ => unreachable!("fixture final step is resolution"),
                },
                ProofId(0),
                ProofId(1),
            )
            .is_none(),
        "a nonempty resolvent must remain outside the symmetry bridge"
    );
}

fn bitvector_store_eq_congruent_fixture() -> (TermStore, Proof, TermId) {
    use ay_core::Symbol;

    let mut terms = TermStore::new();
    let array_sort = Sort::array(Sort::bitvec(32), Sort::bitvec(8));
    let mem = terms.mk_var("mem", array_sort.clone());
    let mem2 = terms.mk_var("mem2", array_sort.clone());
    let idx = terms.mk_var("idx", Sort::bitvec(32));
    let aa = terms.mk_bitvec(170u32.into(), 8);
    let store = terms.mk_app(Symbol::named("store"), [mem, idx, aa], array_sort);
    let left_select = terms.mk_app(Symbol::named("select"), [mem2, idx], Sort::bitvec(8));
    let right_select = terms.mk_app(Symbol::named("select"), [store, idx], Sort::bitvec(8));
    let store_equality = terms.mk_app(Symbol::named("="), [mem2, store], Sort::Bool);
    let index_reflexivity = terms.mk_app(Symbol::named("="), [idx, idx], Sort::Bool);
    let conclusion = terms.mk_app(Symbol::named("="), [left_select, right_select], Sort::Bool);
    let mut proof = Proof::new();
    proof.add_rule_step(
        AletheRule::EqCongruent,
        vec![
            terms.mk_not_raw(store_equality),
            terms.mk_not_raw(index_reflexivity),
            conclusion,
        ],
        Vec::new(),
        Vec::new(),
    );
    (terms, proof, store_equality)
}

#[test]
fn test_eq_congruent_accepts_equal_bitvector_literal_spellings() {
    use ay_core::kani_compat::DetHashMap;

    let (terms, proof, store_equality) = bitvector_store_eq_congruent_fixture();
    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(store_equality, "(= mem2 (store mem idx #xAA))".to_string());
    let output = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &scope_covering_proof(&proof),
        Some(&overrides),
    )
    .expect("equal bit-vector literal spellings preserve eq_congruent");
    assert!(
        output.contains("#xAA")
            && output.contains("#b10101010")
            && output.contains(":rule eq_congruent"),
        "{output}"
    );
}

#[test]
fn test_eq_congruent_rejects_a_changed_bitvector_literal() {
    use ay_core::kani_compat::DetHashMap;

    let (terms, proof, store_equality) = bitvector_store_eq_congruent_fixture();
    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(store_equality, "(= mem2 (store mem idx #xAB))".to_string());
    let error = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &scope_covering_proof(&proof),
        Some(&overrides),
    )
    .expect_err("a changed bit-vector value must fail closed");
    assert!(
        matches!(error, AlethePrintError::InvalidCongruenceStep { .. }),
        "{error}"
    );
}

fn assert_addition_permutation_declines(
    terms: &TermStore,
    proof: &Proof,
    left: TermId,
    surface: &str,
) {
    use ay_core::kani_compat::DetHashMap;

    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(left, surface.to_string());
    let error = try_export_alethe_with_problem_scope_and_overrides(
        proof,
        terms,
        &scope_covering_proof(proof),
        Some(&overrides),
    )
    .expect_err("addition permutation is outside the multiplication-only bridge");
    assert!(
        matches!(error, AlethePrintError::InvalidCongruenceStep { .. }),
        "{error}"
    );
}

#[test]
fn test_cong_bridge_rejects_binary_int_addition_permutation() {
    use ay_core::Symbol;

    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let s = terms.mk_var("s", Sort::Int);
    let t = terms.mk_var("t", Sort::Int);
    let sum = terms.mk_app(Symbol::named("+"), [a, b], Sort::Int);
    let left = terms.mk_app(Symbol::named("f"), [sum, s], Sort::Int);
    let right = terms.mk_app(Symbol::named("f"), [sum, t], Sort::Int);
    let premise_equality = terms.mk_app(Symbol::named("="), [s, t], Sort::Bool);
    let conclusion = terms.mk_app(Symbol::named("="), [left, right], Sort::Bool);
    let mut proof = Proof::new();
    let premise = proof.add_assume(premise_equality, None);
    proof.add_rule_step(
        AletheRule::Cong,
        vec![conclusion],
        vec![premise],
        Vec::new(),
    );

    assert_addition_permutation_declines(&terms, &proof, left, "(f (+ b a) s)");
}

#[test]
fn test_cong_bridge_rejects_binary_real_addition_permutation() {
    use ay_core::Symbol;

    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Real);
    let b = terms.mk_var("b", Sort::Real);
    let s = terms.mk_var("s", Sort::Real);
    let t = terms.mk_var("t", Sort::Real);
    let sum = terms.mk_app(Symbol::named("+"), [a, b], Sort::Real);
    let left = terms.mk_app(Symbol::named("f"), [sum, s], Sort::Real);
    let right = terms.mk_app(Symbol::named("f"), [sum, t], Sort::Real);
    let premise_equality = terms.mk_app(Symbol::named("="), [s, t], Sort::Bool);
    let conclusion = terms.mk_app(Symbol::named("="), [left, right], Sort::Bool);
    let mut proof = Proof::new();
    let premise = proof.add_assume(premise_equality, None);
    proof.add_rule_step(
        AletheRule::Cong,
        vec![conclusion],
        vec![premise],
        Vec::new(),
    );

    assert_addition_permutation_declines(&terms, &proof, left, "(f (+ b a) s)");
}

#[test]
fn test_cong_bridge_rejects_nary_addition_permutation() {
    use ay_core::Symbol;

    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);
    let s = terms.mk_var("s", Sort::Int);
    let t = terms.mk_var("t", Sort::Int);
    let sum = terms.mk_app(Symbol::named("+"), [a, b, c], Sort::Int);
    let left = terms.mk_app(Symbol::named("f"), [sum, s], Sort::Int);
    let right = terms.mk_app(Symbol::named("f"), [sum, t], Sort::Int);
    let premise_equality = terms.mk_app(Symbol::named("="), [s, t], Sort::Bool);
    let conclusion = terms.mk_app(Symbol::named("="), [left, right], Sort::Bool);
    let mut proof = Proof::new();
    let premise = proof.add_assume(premise_equality, None);
    proof.add_rule_step(
        AletheRule::Cong,
        vec![conclusion],
        vec![premise],
        Vec::new(),
    );

    assert_addition_permutation_declines(&terms, &proof, left, "(f (+ c b a) s)");
}

#[test]
fn test_cong_bridge_rejects_a_non_commutative_surface_mutation() {
    use ay_core::kani_compat::DetHashMap;
    use ay_core::Symbol;

    let mut terms = TermStore::new();
    let c = terms.mk_var("c", Sort::Int);
    let s = terms.mk_var("s", Sort::Int);
    let sixteen = terms.mk_int(16.into());
    let seven = terms.mk_int(7.into());
    let mul = terms.mk_app(Symbol::named("*"), [c, sixteen], Sort::Int);
    let left = terms.mk_app(Symbol::named("+"), [mul, s], Sort::Int);
    let right = terms.mk_app(Symbol::named("+"), [mul, seven], Sort::Int);
    let premise_equality = terms.mk_app(Symbol::named("="), [s, seven], Sort::Bool);
    let conclusion = terms.mk_app(Symbol::named("="), [left, right], Sort::Bool);

    let mut proof = Proof::new();
    let premise = proof.add_assume(premise_equality, None);
    proof.add_rule_step(
        AletheRule::Cong,
        vec![conclusion],
        vec![premise],
        Vec::new(),
    );

    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(left, "(+ (* 15 c) s)".to_string());
    let error = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &scope_covering_proof(&proof),
        Some(&overrides),
    )
    .expect_err("a changed multiplier is not a commutativity bridge");
    assert!(
        matches!(error, AlethePrintError::InvalidCongruenceStep { .. }),
        "{error}"
    );
}

#[test]
fn test_divisibility_lowers_to_checked_integer_lattice_steps() {
    use ay_core::{LiaAnnotation, Symbol, TheoryLemmaKind};

    let mut terms = TermStore::new();
    let y = terms.mk_var("y", Sort::Int);
    let two = terms.mk_int(2.into());
    let seven = terms.mk_int(7.into());
    let two_y = terms.mk_app(Symbol::named("*"), [two, y], Sort::Int);
    let equality = terms.mk_app(Symbol::named("="), [two_y, seven], Sort::Bool);
    let disequality = terms.mk_not_raw(equality);

    let mut proof = Proof::new();
    proof.add_theory_lemma_with_lia(
        "lia",
        vec![disequality],
        None,
        TheoryLemmaKind::LiaGeneric,
        LiaAnnotation::Divisibility,
    );
    let output = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &scope_covering_proof(&proof),
        None,
    )
    .expect("the exact divisibility witness has a checked wire derivation");
    assert!(output.contains("(step t0.split"), "{output}");
    assert!(output.contains(":rule la_generic :args (1 1)"), "{output}");
    assert!(
        output.contains("(step t0 (cl (not (= (* 2 y) 7))) :rule resolution"),
        "{output}"
    );
    assert!(!output.contains(":rule hole"), "{output}");
    assert!(!output.contains(":rule lia_generic"), "{output}");
}

/// The bridge's cross-check proves the two literals are COMPLEMENTARY; it does
/// not prove they are printed in different ORDERS. A self-equality satisfies it
/// with all four operands spelled identically, and the emitted `symm` then
/// concludes a clause byte-identical to its own premise: a step that reorients
/// nothing, injected into every self-equality refutation.
/// `distinct_eq_resolution_bridge` already requires its `swapped` flag before
/// emitting `symm`; an aligned pivot here must likewise fall through to the
/// ordinary resolution rendering.
#[test]
fn aligned_self_equality_pivot_resolves_without_a_no_op_symm() {
    use ay_core::Symbol;

    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let equality = terms.mk_app(Symbol::named("="), [x, x], Sort::Bool);
    let negated = terms.mk_not_raw(equality);
    let mut proof = Proof::new();
    let positive = proof.add_assume(equality, None);
    let negative = proof.add_assume(negated, None);
    proof.add_resolution(Vec::new(), equality, positive, negative);

    let output = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &scope_covering_proof(&proof),
        None,
    )
    .expect("an aligned self-equality pivot has an ordinary resolution rendering");
    assert!(
        !output.contains(":rule symm"),
        "a `symm` whose conclusion equals its premise reorients nothing:\n{output}"
    );
    assert!(
        output.contains("(step t2 (cl) :rule resolution :premises (t0 t1))"),
        "the aligned pivot must resolve directly against its two premises:\n{output}"
    );
}

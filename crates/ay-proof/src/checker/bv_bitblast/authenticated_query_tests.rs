// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ay_core::{Sort, Symbol, TermStore};
use num_bigint::BigInt;

use super::{
    authenticate_bool_bv_unsat_query, BoolBvUnsatAuthenticationError,
    MAX_PROOF_PRODUCING_INTERNAL_BV_WIDTH,
};

fn signed_add_safety_query(
    terms: &mut TermStore,
    lhs_value: u32,
    rhs_value: u32,
) -> Vec<ay_core::TermId> {
    const WIDTH: u32 = 4;
    let lhs = terms.mk_var("auth_bv_lhs", Sort::bitvec(WIDTH));
    let rhs = terms.mk_var("auth_bv_rhs", Sort::bitvec(WIDTH));
    let lhs_literal = terms.mk_bitvec(BigInt::from(lhs_value), WIDTH);
    let rhs_literal = terms.mk_bitvec(BigInt::from(rhs_value), WIDTH);
    let lhs_eq = terms.mk_app(Symbol::named("="), [lhs, lhs_literal], Sort::Bool);
    let rhs_eq = terms.mk_app(Symbol::named("="), [rhs, rhs_literal], Sort::Bool);

    let zero = terms.mk_bitvec(BigInt::from(0_u8), WIDTH);
    let sum = terms.mk_app(Symbol::named("bvadd"), [lhs, rhs], Sort::bitvec(WIDTH));
    let lhs_positive = terms.mk_app(Symbol::named("bvsgt"), [lhs, zero], Sort::Bool);
    let rhs_positive = terms.mk_app(Symbol::named("bvsgt"), [rhs, zero], Sort::Bool);
    let both_positive = terms.mk_and(vec![lhs_positive, rhs_positive]);
    let sum_positive = terms.mk_app(Symbol::named("bvsgt"), [sum, zero], Sort::Bool);
    let no_positive_overflow = terms.mk_implies(both_positive, sum_positive);
    vec![lhs_eq, rhs_eq, no_positive_overflow]
}

fn wide_signed_keep_max_query(
    terms: &mut TermStore,
    negate_difference_positive: bool,
) -> Vec<ay_core::TermId> {
    const WIDTH: u32 = 128;
    let lo = terms.mk_var("auth_wide_lo", Sort::bitvec(WIDTH));
    let hi = terms.mk_var("auth_wide_hi", Sort::bitvec(WIDTH));
    let zero = terms.mk_bitvec(BigInt::from(0_u8), WIDTH);
    let one = terms.mk_bitvec(BigInt::from(1_u8), WIDTH);
    let difference = terms.mk_app(Symbol::named("bvsub"), [hi, lo], Sort::bitvec(WIDTH));
    let difference_positive = terms.mk_app(Symbol::named("bvslt"), [zero, difference], Sort::Bool);
    let first = if negate_difference_positive {
        terms.mk_not_raw(difference_positive)
    } else {
        difference_positive
    };
    vec![
        first,
        terms.mk_app(Symbol::named("bvslt"), [lo, hi], Sort::Bool),
        terms.mk_app(Symbol::named("bvsle"), [one, lo], Sort::Bool),
    ]
}

#[test]
fn source_bound_query_authenticates_signed_overflow_and_retires_on_change() {
    let mut terms = TermStore::new();
    // 7 + 1 wraps to -8 in signed four-bit arithmetic.
    let roots = signed_add_safety_query(&mut terms, 7, 1);
    let evidence = authenticate_bool_bv_unsat_query(&terms, &roots, None)
        .expect("the source-level signed-overflow contradiction must be proved");
    assert!(evidence.is_current_for(&terms, &roots));

    let mut reordered = roots.clone();
    reordered.swap(0, 1);
    assert!(!evidence.is_current_for(&terms, &reordered));

    let _late_term = terms.mk_var("auth_bv_late", Sort::Bool);
    assert!(!evidence.term_snapshot_is_current(&terms));
    assert!(!evidence.is_current_for(&terms, &roots));
}

#[test]
fn source_bound_query_refuses_satisfiable_signed_addition() {
    let mut terms = TermStore::new();
    let roots = signed_add_safety_query(&mut terms, 1, 1);
    let error = authenticate_bool_bv_unsat_query(&terms, &roots, None)
        .expect_err("a safe concrete addition is satisfiable");
    assert!(matches!(error, BoolBvUnsatAuthenticationError::Satisfiable));
}

#[test]
fn source_bound_query_authenticates_wide_signed_keep_max_refutation() {
    let mut terms = TermStore::new();
    let roots = wide_signed_keep_max_query(&mut terms, true);

    let evidence = authenticate_bool_bv_unsat_query(&terms, &roots, None)
        .expect("the wide signed keep-max contradiction must have a checked refutation");
    assert!(evidence.is_current_for(&terms, &roots));
}

#[test]
fn source_bound_query_refuses_satisfiable_wide_signed_keep_max_twin() {
    let mut terms = TermStore::new();
    let roots = wide_signed_keep_max_query(&mut terms, false);
    let error = authenticate_bool_bv_unsat_query(&terms, &roots, None)
        .expect_err("the positive-difference twin has satisfying assignments");
    assert!(matches!(error, BoolBvUnsatAuthenticationError::Satisfiable));
}

#[test]
fn source_bound_query_declines_width_above_internal_ceiling() {
    const WIDTH: u32 = MAX_PROOF_PRODUCING_INTERNAL_BV_WIDTH + 1;
    let mut terms = TermStore::new();
    let value = terms.mk_var("auth_too_wide", Sort::bitvec(WIDTH));
    let reflexive = terms.mk_app(Symbol::named("="), [value, value], Sort::Bool);
    let contradiction = terms.mk_not_raw(reflexive);
    let error = authenticate_bool_bv_unsat_query(&terms, &[contradiction], None)
        .expect_err("widths above the internal source-checker ceiling must decline");
    assert!(error.is_unsupported_fragment());
}

#[test]
fn source_bound_query_refuses_unsupported_theory_roots() {
    let mut terms = TermStore::new();
    let integer = terms.mk_var("auth_integer", Sort::Int);
    let zero = terms.mk_int(0.into());
    let root = terms.mk_app(Symbol::named("="), [integer, zero], Sort::Bool);
    let error = authenticate_bool_bv_unsat_query(&terms, &[root], None)
        .expect_err("integer equality is outside the Bool/BV proof fragment");
    assert!(error.is_unsupported_fragment());
}

/// The qpf fixpoint instance shape (#bitblast-original-clause-authority):
/// `fa0(c)=1 ∧ fa1(c)=fa0(c)+1 ∧ (3=fa0(c) ∨ 3=fa1(c))` over one pinned
/// argument tuple. With each application one shared 8-bit free leaf the
/// conjunction is UNSAT, and the UF-leaf entry point must authenticate it.
fn fixpoint_instance_query(terms: &mut TermStore) -> Vec<ay_core::TermId> {
    const WIDTH: u32 = 8;
    let bv = Sort::bitvec(WIDTH);
    let one = terms.mk_bitvec(BigInt::from(1_u8), WIDTH);
    let two = terms.mk_bitvec(BigInt::from(2_u8), WIDTH);
    let three = terms.mk_bitvec(BigInt::from(3_u8), WIDTH);
    let fa0 = terms.mk_app(Symbol::named("fa0"), [three, two, one], bv.clone());
    let fa1 = terms.mk_app(Symbol::named("fa1"), [three, two, one], bv.clone());
    let fa0_is_one = terms.mk_app(Symbol::named("="), [fa0, one], Sort::Bool);
    let fa0_succ = terms.mk_app(Symbol::named("bvadd"), [fa0, one], bv);
    let fa1_is_succ = terms.mk_app(Symbol::named("="), [fa1, fa0_succ], Sort::Bool);
    let fix0 = terms.mk_app(Symbol::named("="), [three, fa0], Sort::Bool);
    let fix1 = terms.mk_app(Symbol::named("="), [three, fa1], Sort::Bool);
    let fixpoint = terms.mk_or(vec![fix0, fix1]);
    vec![fa0_is_one, fa1_is_succ, fixpoint]
}

#[test]
fn uf_leaf_query_authenticates_fixpoint_instance_and_retires_on_change() {
    let mut terms = TermStore::new();
    let roots = fixpoint_instance_query(&mut terms);
    let evidence = super::authenticate_uf_leaf_bool_bv_unsat_query(&terms, &roots, None)
        .expect("the congruence-free fixpoint instance must be refuted over free leaves");
    assert!(evidence.is_current_for(&terms, &roots));
    assert!(evidence.used_uninterpreted_leaves());

    let _late_term = terms.mk_var("auth_uf_late", Sort::Bool);
    assert!(!evidence.term_snapshot_is_current(&terms));
    assert!(!evidence.is_current_for(&terms, &roots));
}

/// Identical applications share ONE leaf, so `f(c) != f(c)` refutes.
#[test]
fn uf_leaf_query_shares_leaf_between_identical_applications() {
    let mut terms = TermStore::new();
    let constant = terms.mk_bitvec(BigInt::from(5_u8), 8);
    let lhs = terms.mk_app(Symbol::named("free_f"), [constant], Sort::bitvec(8));
    let rhs = terms.mk_app(Symbol::named("free_f"), [constant], Sort::bitvec(8));
    let equal = terms.mk_app(Symbol::named("="), [lhs, rhs], Sort::Bool);
    let root = terms.mk_not_raw(equal);
    let evidence = super::authenticate_uf_leaf_bool_bv_unsat_query(&terms, &[root], None)
        .expect("one canonical application must lower to one leaf");
    assert!(evidence.used_uninterpreted_leaves());
}

/// Distinct applications never alias: `f(a) != f(b)` has a free-leaf
/// model, and the entry point must DECLINE — never claim `Satisfiable`,
/// which downstream consumers treat as contradictory evidence.
#[test]
fn uf_leaf_query_declines_satisfiable_abstraction_without_sat_claim() {
    let mut terms = TermStore::new();
    let a = terms.mk_bitvec(BigInt::from(1_u8), 8);
    let b = terms.mk_bitvec(BigInt::from(2_u8), 8);
    let fa = terms.mk_app(Symbol::named("free_f"), [a], Sort::bitvec(8));
    let fb = terms.mk_app(Symbol::named("free_f"), [b], Sort::bitvec(8));
    let equal = terms.mk_app(Symbol::named("="), [fa, fb], Sort::Bool);
    let root = terms.mk_not_raw(equal);
    let error = super::authenticate_uf_leaf_bool_bv_unsat_query(&terms, &[root], None)
        .expect_err("congruence-free leaves cannot refute distinct applications");
    assert!(
        error.is_unsupported_fragment(),
        "a satisfiable UF-leaf abstraction must decline, got: {error}"
    );
    assert!(
        !matches!(error, BoolBvUnsatAuthenticationError::Satisfiable),
        "a satisfiable abstraction is not evidence the exact query is satisfiable"
    );
}

/// A Bool-sorted uninterpreted predicate is a one-bit leaf: `p(c) ∧ ¬p(c)`
/// refutes.
#[test]
fn uf_leaf_query_authenticates_bool_predicate_contradiction() {
    let mut terms = TermStore::new();
    let constant = terms.mk_bitvec(BigInt::from(3_u8), 4);
    let positive = terms.mk_app(Symbol::named("free_p"), [constant], Sort::Bool);
    let negative = terms.mk_not_raw(positive);
    let evidence =
        super::authenticate_uf_leaf_bool_bv_unsat_query(&terms, &[positive, negative], None)
            .expect("a Boolean application must lower to a one-bit leaf");
    assert!(evidence.used_uninterpreted_leaves());
}

/// A pure Bool/BV query that never needed a leaf keeps the exact
/// `Satisfiable` verdict: the two entry points coincide on the exact
/// fragment.
#[test]
fn uf_leaf_query_preserves_exact_satisfiable_verdict_without_leaves() {
    let mut terms = TermStore::new();
    let roots = signed_add_safety_query(&mut terms, 1, 1);
    let error = super::authenticate_uf_leaf_bool_bv_unsat_query(&terms, &roots, None)
        .expect_err("a safe concrete addition is satisfiable");
    assert!(matches!(error, BoolBvUnsatAuthenticationError::Satisfiable));
}

/// Reserved-but-uninterpreted BV theory operators must keep declining as
/// unsupported instead of silently weakening into free leaves — and the
/// decline reason must show the reserved spelling was NOT abstracted.
#[test]
fn uf_leaf_query_never_abstracts_reserved_bv_operators() {
    let mut terms = TermStore::new();
    let lhs = terms.mk_var("auth_udiv_lhs", Sort::bitvec(8));
    let rhs = terms.mk_var("auth_udiv_rhs", Sort::bitvec(8));
    let quotient = terms.mk_app(Symbol::named("bvudiv"), [lhs, rhs], Sort::bitvec(8));
    let equal = terms.mk_app(Symbol::named("="), [quotient, quotient], Sort::Bool);
    let root = terms.mk_not_raw(equal);
    let error = super::authenticate_uf_leaf_bool_bv_unsat_query(&terms, &[root], None)
        .expect_err("`bvudiv` is reserved theory vocabulary, not a free function");
    assert!(error.is_unsupported_fragment());
    assert!(
        error.to_string().contains("bvudiv"),
        "the reserved operator must be the decline reason, got: {error}"
    );
}

/// Guard-removal proof for the opt-in flag: the DEFAULT entry point must
/// still reject uninterpreted applications outright. Deleting the
/// `uninterpreted_leaves` guard in the lowerer makes this fail.
#[test]
fn default_entry_point_still_rejects_uninterpreted_applications() {
    let mut terms = TermStore::new();
    let roots = fixpoint_instance_query(&mut terms);
    let error = authenticate_bool_bv_unsat_query(&terms, &roots, None)
        .expect_err("the exact entry point must not abstract applications");
    assert!(error.is_unsupported_fragment());
}

// ---------------------------------------------------------------------------
// Bool-ATOM abstraction over non-finitely-sorted operands
// (`authenticate_atom_leaf_bool_bv_unsat_query`).
// ---------------------------------------------------------------------------

/// `(= i 0)` over `Int` next to a self-contained BitVec contradiction. The
/// integer atom becomes ONE free Boolean leaf, the BitVec half still refutes,
/// and the query is authenticated. This is the shape the mixed BV+Int
/// obligations reach, and it is `Err(UnsupportedFragment)` on both older entry
/// points.
#[test]
fn atom_leaf_query_authenticates_int_atom_beside_bv_contradiction() {
    let mut terms = TermStore::new();
    let integer = terms.mk_var("atom_leaf_int", Sort::Int);
    let zero = terms.mk_int(0.into());
    let int_atom = terms.mk_app(Symbol::named("="), [integer, zero], Sort::Bool);
    let value = terms.mk_var("atom_leaf_bv", Sort::bitvec(4));
    let reflexive = terms.mk_app(Symbol::named("="), [value, value], Sort::Bool);
    let bv_contradiction = terms.mk_not_raw(reflexive);

    let roots = vec![int_atom, bv_contradiction];
    let evidence = super::authenticate_atom_leaf_bool_bv_unsat_query(&terms, &roots, None)
        .expect("the BitVec half refutes while the integer atom is a free Boolean leaf");
    assert!(evidence.is_current_for(&terms, &roots));
    assert!(evidence.used_uninterpreted_leaves());

    let mut reordered = roots.clone();
    reordered.swap(0, 1);
    assert!(!evidence.is_current_for(&terms, &reordered));

    let _late_term = terms.mk_var("atom_leaf_late", Sort::Bool);
    assert!(!evidence.term_snapshot_is_current(&terms));
    assert!(!evidence.is_current_for(&terms, &roots));
}

/// THE CARDINAL NARROWNESS PIN. `n` pairwise-distinct integers are satisfiable
/// over the integers for every `n` (take `0, 1, …, n-1`), so this query must
/// DECLINE. Modelling each `Int` term as a width-`w` bit-vector leaf instead
/// would refute it by pigeonhole for `n > 2^w` — and the counterexample is
/// parametric in `w`, so NO finite width is sound. This test fails the moment
/// anyone mints a non-Boolean leaf for a non-finitely-sorted term.
#[test]
fn atom_leaf_query_never_refutes_pairwise_distinct_integers() {
    for count in 2..=5_usize {
        let mut terms = TermStore::new();
        let integers: Vec<_> = (0..count)
            .map(|index| terms.mk_var(format!("atom_leaf_distinct_{index}"), Sort::Int))
            .collect();
        let mut roots = Vec::new();
        for (lhs_index, &lhs) in integers.iter().enumerate() {
            for &rhs in &integers[lhs_index + 1..] {
                let equal = terms.mk_app(Symbol::named("="), [lhs, rhs], Sort::Bool);
                roots.push(terms.mk_not_raw(equal));
            }
        }

        let error = super::authenticate_atom_leaf_bool_bv_unsat_query(&terms, &roots, None)
            .expect_err("pairwise-distinct integers are satisfiable over Z");
        assert!(
            error.is_unsupported_fragment(),
            "pairwise-distinct integers must DECLINE at n={count}, got: {error}"
        );
        assert!(
            !matches!(error, BoolBvUnsatAuthenticationError::Satisfiable),
            "a satisfiable atom abstraction is not evidence about the exact query"
        );
    }
}

/// FAIL-CLOSED PIN: a satisfiable abstraction that minted at least one leaf
/// must DECLINE, never report `Satisfiable`. Congruence — including
/// REFLEXIVITY — is deliberately forgotten, so `¬(= i i)` over `Int` has a
/// free-leaf model even though the exact query is unsatisfiable. Declining is
/// the correct, strictly-weaker answer; claiming `Satisfiable` would be a veto
/// on a theorem.
#[test]
fn atom_leaf_query_declines_satisfiable_int_abstraction_without_sat_claim() {
    let mut terms = TermStore::new();
    let integer = terms.mk_var("atom_leaf_reflexive", Sort::Int);
    let reflexive = terms.mk_app(Symbol::named("="), [integer, integer], Sort::Bool);
    let root = terms.mk_not_raw(reflexive);
    let error = super::authenticate_atom_leaf_bool_bv_unsat_query(&terms, &[root], None)
        .expect_err("the congruence-free atom abstraction cannot refute reflexivity");
    assert!(
        error.is_unsupported_fragment(),
        "a satisfiable atom abstraction must decline, got: {error}"
    );
    assert!(
        !matches!(error, BoolBvUnsatAuthenticationError::Satisfiable),
        "a satisfiable abstraction is not evidence the exact query is satisfiable"
    );
}

/// The trigger is the operand SORT FAMILY, never "lowering the operand
/// failed". `bvudiv` is reserved BitVec vocabulary with BitVec-sorted
/// operands, so it must keep declining with the operator named even under the
/// atom abstraction. Rewriting the trigger as "any lowering error" flips this.
#[test]
fn atom_leaf_query_never_abstracts_reserved_bv_operators() {
    let mut terms = TermStore::new();
    let lhs = terms.mk_var("atom_udiv_lhs", Sort::bitvec(8));
    let rhs = terms.mk_var("atom_udiv_rhs", Sort::bitvec(8));
    let quotient = terms.mk_app(Symbol::named("bvudiv"), [lhs, rhs], Sort::bitvec(8));
    let equal = terms.mk_app(Symbol::named("="), [quotient, quotient], Sort::Bool);
    let root = terms.mk_not_raw(equal);
    let error = super::authenticate_atom_leaf_bool_bv_unsat_query(&terms, &[root], None)
        .expect_err("`bvudiv` is reserved theory vocabulary, not a free function");
    assert!(error.is_unsupported_fragment());
    assert!(
        error.to_string().contains("bvudiv"),
        "the reserved operator must be the decline reason, got: {error}"
    );
}

/// The internal BitVec width ceiling must NOT become route-aroundable by
/// wrapping the too-wide term in `=`. A `BitVec` above the ceiling is a BOUND
/// failure inside an interpreted sort family, not a non-finite sort, so the
/// atom abstraction must not absorb it.
#[test]
fn atom_leaf_query_still_declines_width_above_internal_ceiling() {
    const WIDTH: u32 = MAX_PROOF_PRODUCING_INTERNAL_BV_WIDTH + 1;
    let mut terms = TermStore::new();
    let value = terms.mk_var("atom_too_wide", Sort::bitvec(WIDTH));
    let reflexive = terms.mk_app(Symbol::named("="), [value, value], Sort::Bool);
    let contradiction = terms.mk_not_raw(reflexive);
    let error = super::authenticate_atom_leaf_bool_bv_unsat_query(&terms, &[contradiction], None)
        .expect_err("widths above the internal source-checker ceiling must decline");
    assert!(error.is_unsupported_fragment());
    assert!(
        !error.to_string().contains("unsupported source sort"),
        "the decline must stay the width-range diagnosis, got: {error}"
    );
}

/// A pure Bool/BV query that never needed a leaf keeps the exact
/// `Satisfiable` verdict on the atom entry point too.
#[test]
fn atom_leaf_query_preserves_exact_satisfiable_verdict_without_leaves() {
    let mut terms = TermStore::new();
    let roots = signed_add_safety_query(&mut terms, 1, 1);
    let error = super::authenticate_atom_leaf_bool_bv_unsat_query(&terms, &roots, None)
        .expect_err("a safe concrete addition is satisfiable");
    assert!(matches!(error, BoolBvUnsatAuthenticationError::Satisfiable));
}

/// GUARD-REMOVAL PROOF, both directions. The pre-existing entry points must
/// still REJECT the exact query the new one now authenticates: the exact lane
/// because it abstracts nothing, and the UF-leaf lane because reserved `=`
/// over `Int` still descends into its operands there. The second assertion is
/// what keeps the `CheckedQpfInstanceRefutation` lane's accept set
/// bit-identical — deleting the `non_finite_atom_leaves` flag and reusing the
/// shared lowerer would widen an existing lane, and this test fails.
#[test]
fn older_entry_points_still_reject_the_atom_abstracted_query() {
    let mut terms = TermStore::new();
    let integer = terms.mk_var("atom_guard_int", Sort::Int);
    let zero = terms.mk_int(0.into());
    let int_atom = terms.mk_app(Symbol::named("="), [integer, zero], Sort::Bool);
    let value = terms.mk_var("atom_guard_bv", Sort::bitvec(4));
    let reflexive = terms.mk_app(Symbol::named("="), [value, value], Sort::Bool);
    let roots = vec![int_atom, terms.mk_not_raw(reflexive)];

    let exact = authenticate_bool_bv_unsat_query(&terms, &roots, None)
        .expect_err("the exact entry point must not abstract an integer atom");
    assert!(exact.is_unsupported_fragment());
    assert!(
        exact.to_string().contains("unsupported source sort Int"),
        "the exact lane must still name the Int sort, got: {exact}"
    );

    let uf_leaf = super::authenticate_uf_leaf_bool_bv_unsat_query(&terms, &roots, None)
        .expect_err("the UF-leaf entry point must keep its pre-existing accept set");
    assert!(uf_leaf.is_unsupported_fragment());
    assert!(
        uf_leaf.to_string().contains("unsupported source sort Int"),
        "the UF-leaf lane must still name the Int sort, got: {uf_leaf}"
    );
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The printed-against-internal pairing, and the `eq_congruent` AC bridge that
//! reads an operand's SORT off the internal argument list while naming that
//! operand off the printed one.
//!
//! MUTATION DIFFERENTIAL, in the shape `alethe_printer_printed_rule_gate_tests
//! .rs` established: the same clause is exported with a whole-application
//! override that PERMUTES the printed operands and with one that only
//! re-spells an operand in place. The permuting export must be judged over the
//! operand it actually names; the re-spelling export must render exactly as it
//! always did.

use crate::{try_export_alethe_with_problem_scope_and_overrides, AlethePrintError};
use ay_core::kani_compat::DetHashMap;
use ay_core::{AletheRule, Proof, Sort, Symbol, TermId, TermStore};

struct EqCongruentFixture {
    terms: TermStore,
    proof: Proof,
    scope: Vec<TermId>,
    left: TermId,
    right: TermId,
}

/// `(cl (not (= m m)) (not (= u v)) (= (f ..) (f ..)))` — the `eq_congruent`
/// clause the AC bridge repairs. The multiplication's hypothesis is REFLEXIVE:
/// both applications hold the same node, and only the printed spellings
/// differ, which is the shape the bridge exists for.
///
/// `mul_position` is the multiplication's INTERNAL position inside `f`; the
/// clause always lists the reflexive hypothesis first, because the bridge
/// pairs hypothesis `k` with PRINTED argument `k`. `mul_sort` is the
/// multiplication node's sort — the production shape is `Sort::Int`, and a
/// bridge that reads the sort off the wrong internal argument cannot tell that
/// apart from anything else the application holds.
fn eq_congruent_fixture(mul_position: usize, mul_sort: Sort) -> EqCongruentFixture {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let u = terms.mk_var("u", Sort::Int);
    let v = terms.mk_var("v", Sort::Int);
    let mul = terms.mk_app(Symbol::named("*"), [a, b], mul_sort);

    let (left_args, right_args) = if mul_position == 0 {
        ([mul, u], [mul, v])
    } else {
        ([u, mul], [v, mul])
    };
    let left = terms.mk_app(Symbol::named("f"), left_args, Sort::Int);
    let right = terms.mk_app(Symbol::named("f"), right_args, Sort::Int);
    let reflexive = terms.mk_app(Symbol::named("="), [mul, mul], Sort::Bool);
    let ordinary = terms.mk_app(Symbol::named("="), [u, v], Sort::Bool);
    let not_reflexive = terms.mk_not_raw(reflexive);
    let not_ordinary = terms.mk_not_raw(ordinary);
    let conclusion = terms.mk_app(Symbol::named("="), [left, right], Sort::Bool);

    let clause = vec![not_reflexive, not_ordinary, conclusion];
    let mut proof = Proof::new();
    proof.add_rule_step(
        AletheRule::EqCongruent,
        clause.clone(),
        Vec::new(),
        Vec::new(),
    );
    EqCongruentFixture {
        terms,
        proof,
        scope: clause,
        left,
        right,
    }
}

fn export(
    fixture: &EqCongruentFixture,
    overrides: &DetHashMap<TermId, String>,
) -> Result<String, AlethePrintError> {
    try_export_alethe_with_problem_scope_and_overrides(
        &fixture.proof,
        &fixture.terms,
        &fixture.scope,
        Some(overrides),
    )
}

/// CONTROL, and the production shape: an authored multiplication keeps source
/// operand order in one application while canonical interning uses the
/// commuted order everywhere else. The override RE-SPELLS one operand in
/// place and does not move it, so nothing realigns and the bridge renders
/// byte-identically to what it always did.
#[test]
fn an_in_place_respelling_still_renders_the_ac_bridge() {
    let fixture = eq_congruent_fixture(0, Sort::Int);
    let mut overrides = DetHashMap::default();
    overrides.insert(fixture.right, "(f (* b a) v)".to_string());
    let output = export(&fixture, &overrides).expect("an exact Int multiplication swap bridges");
    assert!(
        output.contains("(step t0.ac (cl (= (* a b) (* b a))) :rule aci_simp)"),
        "{output}"
    );
    assert!(output.contains(":rule eq_congruent"), "{output}");
}

/// THE DEFECT. The override PERMUTES the printed operands, so printed position
/// 0 names the multiplication while INTERNAL position 0 holds the ordinary
/// argument. The Int/Real gate this bridge is documented to be "restricted to"
/// read `left_internal_args[index]` at the PRINTED index — the ordinary
/// argument, which is `Int` — so the gate passed and an `aci_simp` shipped for
/// a multiplication whose sort it never looked at.
///
/// Here that multiplication is `Bool`-sorted, which the restriction must
/// refuse. The refusal is loud (`InvalidCongruenceStep`), never a silently
/// different step.
#[test]
fn a_permuted_printed_operand_is_gated_on_the_argument_it_names() {
    let fixture = eq_congruent_fixture(1, Sort::Bool);
    let mut overrides = DetHashMap::default();
    // Printed: the multiplication first, the ordinary argument second.
    // Internal: the ordinary argument first, the multiplication second.
    overrides.insert(fixture.left, "(f (* a b) u)".to_string());
    overrides.insert(fixture.right, "(f (* b a) v)".to_string());
    let error = export(&fixture, &overrides)
        .expect_err("the AC bridge is restricted to Int/Real multiplication");
    let reason = format!("{error}");
    assert!(
        reason.contains("restricted to Int/Real multiplication"),
        "the gate must be read off the operand the step names: {reason}"
    );
}

/// The realignment is a PAIRING fix, not a new refusal: the same permutation
/// over a numeric multiplication must still bridge, so nothing the lane could
/// do before is lost.
#[test]
fn a_permuted_printed_operand_still_bridges_when_it_is_numeric() {
    let fixture = eq_congruent_fixture(1, Sort::Int);
    let mut overrides = DetHashMap::default();
    overrides.insert(fixture.left, "(f (* a b) u)".to_string());
    overrides.insert(fixture.right, "(f (* b a) v)".to_string());
    let output = export(&fixture, &overrides).expect("a numeric permuted operand still bridges");
    assert!(
        output.contains("(step t0.ac (cl (= (* a b) (* b a))) :rule aci_simp)"),
        "{output}"
    );
}

/// THE THIRD SITE, and the reason it is NOT realigned: in
/// `authored_assume::equivalence::build_authored_surface_equivalence` the
/// printed list is the AUTHOR's spelling, the internal list is the canonical
/// term's children, and the step built over them is a `cong` — whose premise
/// `k` must equate argument `k` of the left application with argument `k` of
/// the right. There the by-position pairing IS the claim the emitted step
/// discharges, not an assumption about order, and each position is proved by
/// recursion rather than asserted. Pairing a permuted reading there would emit
/// an INVALID `cong`, so the realignment above is deliberately not applied to
/// it.
///
/// MEASURED, not argued: an authored spelling that commutes the operands of an
/// order-normalized equality declines the whole bridge. Nothing is emitted for
/// a position the recursion cannot prove.
#[test]
fn an_authored_spelling_that_commutes_an_equality_declines_rather_than_pairing_across() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let a = terms.mk_var("a", Sort::Int);
    let four = terms.mk_int(4.into());
    let one = terms.mk_int(1.into());
    let product = terms.mk_app(Symbol::named("*"), [a, four], Sort::Int);
    let affine = terms.mk_app(Symbol::named("+"), [product, one], Sort::Int);
    let canonical = terms.mk_app(Symbol::named("="), [x, affine], Sort::Bool);
    let negated = terms.mk_not_raw(canonical);
    let mut proof = Proof::new();
    let positive = proof.add_assume(canonical, None);
    let negative = proof.add_assume(negated, None);
    proof.add_resolution(Vec::new(), canonical, positive, negative);

    // The CONTROL spelling `(= x (+ (* 4 a) 1))` bridges (pinned by
    // `alethe_printer_authored_assume_tests::
    // test_authored_nested_multiplication_assume_uses_aci_and_congruence`).
    // This one commutes the equality's own operands as well.
    let mut overrides = DetHashMap::default();
    overrides.insert(canonical, "(= (+ (* 4 a) 1) x)".to_string());
    let exported = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &[canonical, negated],
        Some(&overrides),
    );
    match exported {
        Err(_) => {}
        Ok(output) => {
            assert!(
                !output.contains("(cl (= (+ (* 4 a) 1) x))"),
                "a cong pairing the printed operands across positions would be invalid: {output}"
            );
            assert!(
                !output.contains("(cl (= (+ (* 4 a) 1) (+ (* a 4) 1)))"),
                "no position of the commuted spelling may be discharged as if it \
                 were the stored one: {output}"
            );
        }
    }
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn fixture() -> (TermStore, TermId, TermId, TermId) {
    let mut terms = TermStore::new();
    let x = terms.mk_var("sko_x", Sort::Int);
    let body = terms.mk_app(Symbol::named("sko_p"), [x], Sort::Bool);
    let quant = terms.mk_forall(vec![("sko_x".to_string(), Sort::Int)], body);
    let witness = terms.mk_var("sk!sko_x_test", Sort::Int);
    terms.mark_skolem_symbol("sk!sko_x_test");
    let instance = terms.mk_app(Symbol::named("sko_p"), [witness], Sort::Bool);
    let equality = terms.mk_eq(quant, instance);
    (terms, equality, witness, quant)
}

#[test]
fn exact_registered_single_substitution_is_valid() {
    let (terms, equality, witness, _) = fixture();
    validate_sko_forall(&terms, ProofId(0), &[equality], 0, &[witness])
        .expect("exact registered Skolem substitution must validate");
}

#[test]
fn unregistered_witness_is_rejected() {
    let (mut terms, _, _, quant) = fixture();
    let forged = terms.mk_var("ordinary_constant", Sort::Int);
    let instance = terms.mk_app(Symbol::named("sko_p"), [forged], Sort::Bool);
    let equality = terms.mk_eq(quant, instance);
    assert!(validate_sko_forall(&terms, ProofId(0), &[equality], 0, &[forged]).is_err());
}

#[test]
fn skolem_shaped_but_unregistered_witness_is_rejected() {
    let (mut terms, _, _, quant) = fixture();
    let forged = terms.mk_var("sk!looks_authentic_but_is_user_owned", Sort::Int);
    let instance = terms.mk_app(Symbol::named("sko_p"), [forged], Sort::Bool);
    let equality = terms.mk_eq(quant, instance);
    assert!(validate_sko_forall(&terms, ProofId(0), &[equality], 0, &[forged]).is_err());
}

#[test]
fn wrong_instantiated_body_is_rejected() {
    let (mut terms, _, witness, quant) = fixture();
    let wrong = terms.mk_app(Symbol::named("different_predicate"), [witness], Sort::Bool);
    let equality = terms.mk_eq(quant, wrong);
    assert!(validate_sko_forall(&terms, ProofId(0), &[equality], 0, &[witness]).is_err());
}

#[test]
fn premises_and_extra_args_are_rejected() {
    let (terms, equality, witness, _) = fixture();
    assert!(validate_sko_forall(&terms, ProofId(0), &[equality], 1, &[witness]).is_err());
    assert!(validate_sko_forall(&terms, ProofId(0), &[equality], 0, &[witness, witness]).is_err());
}

#[test]
fn one_witness_cannot_certify_two_incompatible_foralls() {
    let (mut terms, equality1, witness, _) = fixture();
    let y = terms.mk_var("sko_y", Sort::Int);
    let body2 = terms.mk_app(Symbol::named("sko_q"), [y], Sort::Bool);
    let quant2 = terms.mk_forall(vec![("sko_y".to_string(), Sort::Int)], body2);
    let instance2 = terms.mk_app(Symbol::named("sko_q"), [witness], Sort::Bool);
    let equality2 = terms.mk_app(Symbol::named("="), [quant2, instance2], Sort::Bool);

    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Skolem, vec![equality1], vec![], vec![witness]);
    proof.add_rule_step(AletheRule::Skolem, vec![equality2], vec![], vec![witness]);
    let err = validate_sko_forall_uniqueness(&proof, &terms)
        .expect_err("one witness must not acquire two choice definitions");
    assert!(matches!(err, ProofCheckError::InvalidBooleanRule { .. }));
}

// -----------------------------------------------------------------------
// `sko_ex` arm (#quant-unit-authority): the positive-`exists` flat form
// `(= (exists x. B) B[sk])` is admitted ONLY with the live registry as
// authority AND only when the registry's recorded `SkolemChoice` (binder,
// sort, unnegated body) matches this exact quantifier. These tests pin
// the arm's guards; each was proven load-bearing by removing the guard
// and watching the test fail (see P3A_DERIVATION_AUTHORITY_REVIEW.md).

/// `exists x. P(x)` with a properly minted witness. `register_choice`
/// controls whether the witness gets a registry definition, and
/// `choice_body_of` lets a test register the choice against a DIFFERENT
/// quantifier's body (the borrowed-witness forgery).
fn sko_ex_fixture(
    register_choice: bool,
    borrow_from_other_body: bool,
) -> (TermStore, TermId, TermId, TermId) {
    let mut terms = TermStore::new();
    let x = terms.mk_var("se_x", Sort::Int);
    let body = terms.mk_app(Symbol::named("se_p"), [x], Sort::Bool);
    let quantified = terms.mk_exists(vec![("se_x".to_string(), Sort::Int)], body);
    let witness = terms.mk_var("sk!se_x", Sort::Int);
    terms.mark_skolem_symbol("sk!se_x");
    if register_choice {
        let registered_body = if borrow_from_other_body {
            terms.mk_app(Symbol::named("se_q"), [x], Sort::Bool)
        } else {
            body
        };
        terms.register_skolem_choice(
            witness,
            ay_core::SkolemChoice {
                binder: "se_x".to_string(),
                sort: Sort::Int,
                body: registered_body,
            },
        );
    }
    let instance = terms.mk_app(Symbol::named("se_p"), [witness], Sort::Bool);
    let equality = terms.mk_app(Symbol::named("="), [quantified, instance], Sort::Bool);
    (terms, equality, witness, instance)
}

#[test]
fn sko_ex_accepts_registered_exact_substitution() {
    let (terms, equality, witness, _) = sko_ex_fixture(true, false);
    validate_sko_forall(&terms, ProofId(0), &[equality], 0, &[witness])
        .expect("a registered choice with the exact substitution must validate");
}

#[test]
fn sko_ex_rejects_unregistered_witness() {
    // The witness IS a marked Skolem symbol, but no choice definition was
    // ever registered: nothing states that `sk` denotes `(choice x. P x)`,
    // so the equality is an unlicensed assumption.
    let (terms, equality, witness, _) = sko_ex_fixture(false, false);
    let error = validate_sko_forall(&terms, ProofId(0), &[equality], 0, &[witness])
        .expect_err("an unregistered sko_ex witness must be rejected");
    assert!(
        error
            .to_string()
            .contains("no registered choice definition"),
        "unexpected rejection: {error}"
    );
}

#[test]
fn sko_ex_rejects_witness_borrowed_from_another_quantifier() {
    // The witness has a registered choice — for a DIFFERENT body. Using
    // it here would let one quantifier's witness realize another's.
    let (terms, equality, witness, _) = sko_ex_fixture(true, true);
    let error = validate_sko_forall(&terms, ProofId(0), &[equality], 0, &[witness])
        .expect_err("a borrowed sko_ex witness must be rejected");
    assert!(
        error
            .to_string()
            .contains("registered choice does not match"),
        "unexpected rejection: {error}"
    );
}

#[test]
fn sko_ex_rejects_non_substitution_right_side() {
    // Choice properly registered, but the equality's right side is NOT
    // `B[x := sk]` — it names a different predicate entirely.
    let (mut terms, _, witness, _) = sko_ex_fixture(true, false);
    let x = terms.mk_var("se_x", Sort::Int);
    let body = terms.mk_app(Symbol::named("se_p"), [x], Sort::Bool);
    let quantified = terms.mk_exists(vec![("se_x".to_string(), Sort::Int)], body);
    let wrong_instance = terms.mk_app(Symbol::named("se_q"), [witness], Sort::Bool);
    let equality = terms.mk_app(Symbol::named("="), [quantified, wrong_instance], Sort::Bool);
    let error = validate_sko_forall(&terms, ProofId(0), &[equality], 0, &[witness])
        .expect_err("a non-substitution right side must be rejected");
    assert!(
        error
            .to_string()
            .contains("not the exact registered-witness substitution"),
        "unexpected rejection: {error}"
    );
}

// -----------------------------------------------------------------------
// FRESHNESS mutation proofs (the load-bearing soundness precondition of
// skolemization). `exists x. B ⊢ B[sk]` (and the dual `¬∀x. B ⊢ (¬B)[sk]`)
// is sound ONLY when `sk` is genuinely fresh — it must not occur in the
// quantified source. `validate_fresh_substitution`'s `term_contains` guard
// enforces exactly that; if it did not, a non-fresh witness could "prove"
// false things. These two tests VIOLATE the precondition (the registered
// witness already occurs in the source) and confirm the strict checker
// REJECTS — one per arm of the shared guard.

#[test]
fn sko_forall_rejects_non_fresh_witness_occurring_in_the_source() {
    // Source `forall x. sko_p(x, sk)` already mentions the registered
    // Skolem witness `sk`, so `sk` is NOT fresh for this quantifier. The
    // substituted instance `sko_p(sk, sk)` is even the exact structural
    // substitution — yet freshness fails first and must dominate.
    let mut terms = TermStore::new();
    let x = terms.mk_var("sko_x", Sort::Int);
    let witness = terms.mk_var("sk!sko_x_nonfresh", Sort::Int);
    terms.mark_skolem_symbol("sk!sko_x_nonfresh");
    let body = terms.mk_app(Symbol::named("sko_p"), [x, witness], Sort::Bool);
    let quant = terms.mk_forall(vec![("sko_x".to_string(), Sort::Int)], body);
    let instance = terms.mk_app(Symbol::named("sko_p"), [witness, witness], Sort::Bool);
    let equality = terms.mk_eq(quant, instance);
    let error = validate_sko_forall(&terms, ProofId(0), &[equality], 0, &[witness])
        .expect_err("a witness occurring in the source forall must be rejected as non-fresh");
    assert!(
        error
            .to_string()
            .contains("fresh witness occurs in the quantified source"),
        "unexpected rejection: {error}"
    );
}

#[test]
fn sko_ex_rejects_non_fresh_witness_occurring_in_the_source() {
    // The existential arm of the same guard. The registered witness `sk`
    // occurs in the source `exists x. se_p(x, sk)`, and its choice is
    // registered CONSISTENTLY with that (non-fresh) body so the authority
    // check passes and freshness is the deciding rejection. A non-fresh
    // existential witness is exactly the unsound case the task warns about.
    let mut terms = TermStore::new();
    let x = terms.mk_var("se_x", Sort::Int);
    let witness = terms.mk_var("sk!se_x_nonfresh", Sort::Int);
    terms.mark_skolem_symbol("sk!se_x_nonfresh");
    let body = terms.mk_app(Symbol::named("se_p"), [x, witness], Sort::Bool);
    let quantified = terms.mk_exists(vec![("se_x".to_string(), Sort::Int)], body);
    terms.register_skolem_choice(
        witness,
        ay_core::SkolemChoice {
            binder: "se_x".to_string(),
            sort: Sort::Int,
            body,
        },
    );
    let instance = terms.mk_app(Symbol::named("se_p"), [witness, witness], Sort::Bool);
    let equality = terms.mk_app(Symbol::named("="), [quantified, instance], Sort::Bool);
    let error = validate_sko_forall(&terms, ProofId(0), &[equality], 0, &[witness])
        .expect_err("a witness occurring in the source existential must be rejected as non-fresh");
    assert!(
        error
            .to_string()
            .contains("fresh witness occurs in the quantified source"),
        "unexpected rejection: {error}"
    );
}

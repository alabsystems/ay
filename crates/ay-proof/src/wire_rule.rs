// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Complete-step selection of externally meaningful theory-lemma rules.

use ay_core::kani_compat::DetHashMap;
use ay_core::{
    FarkasAnnotation, LiaAnnotation, ProofId, Symbol, TermData, TermId, TermStore, TheoryLemmaKind,
    TheoryLit, UNPROVED_STEP_RULE,
};

use crate::alethe_printer::ClauseSurfaceAgreement;

/// Whether one native `Divisibility` lemma has the exact checked external
/// lowering implemented by the Alethe printer.
///
/// This is consumed by both the printer and the publication wire-gap screen.
/// Requiring an identity surface is deliberate: the lattice witness was
/// derived from the internal term DAG, so a spelling channel that changes the
/// clause must be bridged or purged before this certificate can publish.
#[must_use]
pub fn lia_divisibility_lowering_supported(
    terms: &TermStore,
    clause: &[TermId],
    lia: Option<&LiaAnnotation>,
    term_overrides: Option<&DetHashMap<TermId, String>>,
) -> bool {
    matches!(lia, Some(LiaAnnotation::Divisibility))
        && crate::alethe_printer::clause_surface_agreement(terms, clause, term_overrides)
            == ClauseSurfaceAgreement::Identical
        && ay_core::proof_validation::lia_divisibility_equality_witness(terms, clause).is_some()
}

/// Select the externally meaningful wire rule for one complete theory lemma.
///
/// The pinned Alethe checker recognizes `lia_generic` but treats it as an
/// unchecked placeholder. A [`TheoryLemmaKind::LiaGeneric`] step therefore
/// stays an honest [`UNPROVED_STEP_RULE`] unless either its clause is accepted
/// by the independent ground `evaluate` validator, or its actual Farkas
/// annotation proves the clause in the checker's linear fragment and can be
/// promoted to checked `la_generic`.
///
/// Surface overrides are a hard barrier for both promotions whenever they
/// CHANGE WHAT THIS CLAUSE SAYS. The validators reason about the internal term
/// DAG, while an override changes the text the external checker reads; a
/// promotion is honest exactly when those two agree, which
/// [`crate::alethe_printer::clause_surface_agreement`] decides by re-rendering
/// the clause without the channel.
///
/// Screening the whole document instead — refusing whenever the channel is
/// installed at all — threw away checkable evidence for every clause the
/// overrides never touched, which is how a composed authored root degraded an
/// independently checked ground `evaluate` step to `hole`.
///
/// [`ClauseSurfaceAgreement::OrderReversed`] is the residual case that byte
/// comparison over-refused. `TermStore::mk_gt`/`mk_ge` canonicalize an
/// authored `(> t u)` into `(< u t)`, and the surface channel then re-spells
/// that atom back to the problem's own `(> t u)` — the SAME atom, printed
/// converse-first. There is nothing to reconcile semantically, so the Farkas
/// promotion stands; the `evaluate` lowering is nevertheless withheld, because
/// `format_lia_ground_evaluate` self-guards on byte-identical clause text and
/// would silently fall back to a `hole` the gate had already granted. Keeping
/// that arm on `Identical` is what keeps the two consumers exact.
///
/// Both the Alethe printer and the publication wire-gap gate consume THIS
/// function with the same override state, so the narrowed test cannot drift
/// between them; neither may reconstruct the decision from
/// [`TheoryLemmaKind::alethe_wire_rule`] alone.
#[must_use]
pub fn promoted_wire_rule<'a>(
    terms: &TermStore,
    kind: &'a TheoryLemmaKind,
    clause: &[TermId],
    farkas: Option<&FarkasAnnotation>,
    term_overrides: Option<&DetHashMap<TermId, String>>,
) -> &'a str {
    if !matches!(kind, TheoryLemmaKind::LiaGeneric) {
        return kind.alethe_wire_rule();
    }
    let agreement = crate::alethe_printer::clause_surface_agreement(terms, clause, term_overrides);
    if agreement == ClauseSurfaceAgreement::Divergent {
        return UNPROVED_STEP_RULE;
    }
    if agreement == ClauseSurfaceAgreement::Identical
        && lia_ground_evaluate_is_supported(terms, clause)
    {
        return "evaluate";
    }
    let Some(farkas) = farkas else {
        return UNPROVED_STEP_RULE;
    };
    let conflict: Vec<TheoryLit> = clause
        .iter()
        .map(|&literal| match terms.get(literal) {
            TermData::Not(inner) => TheoryLit::new(*inner, true),
            _ => TheoryLit::new(literal, false),
        })
        .collect();
    if ay_core::proof_validation::verify_farkas_conflict_lits_linear(terms, &conflict, farkas)
        .is_ok()
    {
        "la_generic"
    } else {
        UNPROVED_STEP_RULE
    }
}

fn lia_ground_evaluate_is_supported(terms: &TermStore, clause: &[TermId]) -> bool {
    if crate::checker::validate_ground_evaluate_for_printer(terms, ProofId(0), clause, 0, &[])
        .is_ok()
    {
        return true;
    }
    let [literal] = clause else {
        return false;
    };
    let TermData::Not(equality) = terms.get(*literal) else {
        return false;
    };
    matches!(
        terms.get(*equality),
        TermData::App(Symbol::Named(operator), operands)
            if operator == "=" && operands.len() == 2
    ) && crate::checker::recognize_ground_evaluate(terms, *literal)
}

#[cfg(test)]
mod tests {
    use ay_core::{FarkasAnnotation, Sort, Symbol};
    use num_bigint::BigInt;

    use super::*;

    fn comparison(terms: &mut TermStore, left: i64, right: i64) -> TermId {
        let left = terms.mk_int(BigInt::from(left));
        let right = terms.mk_int(BigInt::from(right));
        terms.mk_app(Symbol::named("<"), [left, right], Sort::Bool)
    }

    #[test]
    fn lia_wire_promotes_only_real_checked_evidence() {
        let mut terms = TermStore::new();
        let two = terms.mk_int(BigInt::from(2));
        let three = terms.mk_int(BigInt::from(3));
        let five = terms.mk_int(BigInt::from(5));
        let sum = terms.mk_app(Symbol::named("+"), [two, three], Sort::Int);
        let tautology = terms.mk_app(Symbol::named("="), [sum, five], Sort::Bool);
        let falsehood = comparison(&mut terms, 1, 0);
        let one = FarkasAnnotation::from_ints(&[1]);

        assert_eq!(
            promoted_wire_rule(
                &terms,
                &TheoryLemmaKind::LiaGeneric,
                &[tautology],
                Some(&one),
                None,
            ),
            "evaluate",
            "a ground truth uses the independently checked evaluate lowering"
        );
        assert_eq!(
            promoted_wire_rule(
                &terms,
                &TheoryLemmaKind::LiaGeneric,
                &[falsehood],
                Some(&one),
                None,
            ),
            UNPROVED_STEP_RULE,
            "a certificate for a satisfiable conflict proves nothing"
        );
    }

    #[test]
    fn symbolic_farkas_promotion_and_override_barrier_are_atomic() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("wire_x", Sort::Int);
        let zero = terms.mk_int(BigInt::from(0));
        let lower = terms.mk_app(Symbol::named("<="), [zero, x], Sort::Bool);
        let upper = terms.mk_app(Symbol::named("<"), [x, zero], Sort::Bool);
        let clause = [terms.mk_not_raw(lower), terms.mk_not_raw(upper)];
        let coefficients = FarkasAnnotation::from_ints(&[1, 1]);

        assert_eq!(
            promoted_wire_rule(
                &terms,
                &TheoryLemmaKind::LiaGeneric,
                &clause,
                Some(&coefficients),
                None,
            ),
            "la_generic"
        );

        let mut overrides = DetHashMap::default();
        overrides.insert(x, "(+ wire_x 1)".to_string());
        assert_eq!(
            promoted_wire_rule(
                &terms,
                &TheoryLemmaKind::LiaGeneric,
                &clause,
                Some(&coefficients),
                Some(&overrides),
            ),
            UNPROVED_STEP_RULE,
            "a surface channel blocks the term-only promotion"
        );
    }

    /// The AUTHORED spelling of a canonicalized order atom is the same atom.
    ///
    /// `mk_gt` interns `(> t u)` as `(< u t)`, and the surface channel then
    /// re-spells that exact atom back to the problem's own `(> t u)`. Byte
    /// comparison called that a changed clause and withheld a certificate AY
    /// had already checked; same-atom comparison does not. Every NEAR miss
    /// below still withholds it.
    #[test]
    fn authored_order_reversal_is_the_same_atom_and_keeps_the_certificate() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("wire_rev_x", Sort::Int);
        let zero = terms.mk_int(BigInt::from(0));
        let lower = terms.mk_app(Symbol::named("<="), [zero, x], Sort::Bool);
        let upper = terms.mk_app(Symbol::named("<"), [x, zero], Sort::Bool);
        let clause = [terms.mk_not_raw(lower), terms.mk_not_raw(upper)];
        let coefficients = FarkasAnnotation::from_ints(&[1, 1]);

        // `(<= 0 wire_rev_x)` is exactly how `(>= wire_rev_x 0)` is interned.
        let mut reversed = DetHashMap::default();
        reversed.insert(lower, "(>= wire_rev_x 0)".to_string());
        assert_eq!(
            promoted_wire_rule(
                &terms,
                &TheoryLemmaKind::LiaGeneric,
                &clause,
                Some(&coefficients),
                Some(&reversed),
            ),
            "la_generic",
            "the authored converse spelling denotes the validated atom"
        );

        // Same operator, swapped arguments: a DIFFERENT atom.
        let mut swapped = DetHashMap::default();
        swapped.insert(lower, "(<= wire_rev_x 0)".to_string());
        assert_eq!(
            promoted_wire_rule(
                &terms,
                &TheoryLemmaKind::LiaGeneric,
                &clause,
                Some(&coefficients),
                Some(&swapped),
            ),
            UNPROVED_STEP_RULE,
            "an argument swap without the converse operator is another atom"
        );

        // Converse operator but the wrong STRICTNESS: `(<= 0 x)` reverses to
        // `(>= x 0)`, never to `(> x 0)`.
        let mut strictened = DetHashMap::default();
        strictened.insert(lower, "(> wire_rev_x 0)".to_string());
        assert_eq!(
            promoted_wire_rule(
                &terms,
                &TheoryLemmaKind::LiaGeneric,
                &clause,
                Some(&coefficients),
                Some(&strictened),
            ),
            UNPROVED_STEP_RULE,
            "the converse spelling may not change strictness"
        );

        // Converse operator, converse order, but a RE-SPELLED operand.
        let mut respelled = DetHashMap::default();
        respelled.insert(lower, "(>= (+ wire_rev_x 1) 0)".to_string());
        assert_eq!(
            promoted_wire_rule(
                &terms,
                &TheoryLemmaKind::LiaGeneric,
                &clause,
                Some(&coefficients),
                Some(&respelled),
            ),
            UNPROVED_STEP_RULE,
            "argument reversal may not smuggle a re-spelled operand"
        );
    }

    /// The classifier both consumers share, pinned outcome by outcome.
    ///
    /// `promoted_wire_rule` reads three distinct answers off this one call —
    /// `Divergent` withholds everything, `Identical` additionally unlocks the
    /// ground `evaluate` lowering (whose printer self-guards on byte-identical
    /// clause text), `OrderReversed` unlocks only the certificate arm — so the
    /// classifier is pinned directly rather than inferred from a wire name.
    #[test]
    fn clause_surface_agreement_separates_identity_reversal_and_divergence() {
        use crate::alethe_printer::{clause_surface_agreement, ClauseSurfaceAgreement};

        let mut terms = TermStore::new();
        let x = terms.mk_var("wire_agree_x", Sort::Int);
        let zero = terms.mk_int(BigInt::from(0));
        let lower = terms.mk_app(Symbol::named("<="), [zero, x], Sort::Bool);
        let clause = [terms.mk_not_raw(lower)];

        assert_eq!(
            clause_surface_agreement(&terms, &clause, None),
            ClauseSurfaceAgreement::Identical,
            "no channel is no change"
        );

        let mut identity = DetHashMap::default();
        identity.insert(lower, "(<= 0 wire_agree_x)".to_string());
        assert_eq!(
            clause_surface_agreement(&terms, &clause, Some(&identity)),
            ClauseSurfaceAgreement::Identical,
            "an identity spelling is no change"
        );

        let mut reversed = DetHashMap::default();
        reversed.insert(lower, "(>= wire_agree_x 0)".to_string());
        assert_eq!(
            clause_surface_agreement(&terms, &clause, Some(&reversed)),
            ClauseSurfaceAgreement::OrderReversed,
            "the authored converse spelling is the same atom"
        );

        let mut divergent = DetHashMap::default();
        divergent.insert(lower, "(>= wire_agree_x 1)".to_string());
        assert_eq!(
            clause_surface_agreement(&terms, &clause, Some(&divergent)),
            ClauseSurfaceAgreement::Divergent,
            "a changed operand is a changed clause"
        );
    }
}

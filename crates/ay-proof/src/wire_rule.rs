// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Complete-step selection of externally meaningful theory-lemma rules.

use ay_core::kani_compat::DetHashMap;
use ay_core::{
    FarkasAnnotation, ProofId, Symbol, TermData, TermId, TermStore, TheoryLemmaKind, TheoryLit,
    UNPROVED_STEP_RULE,
};

/// Select the externally meaningful wire rule for one complete theory lemma.
///
/// The pinned Alethe checker recognizes `lia_generic` but treats it as an
/// unchecked placeholder. A [`TheoryLemmaKind::LiaGeneric`] step therefore
/// stays an honest [`UNPROVED_STEP_RULE`] unless either its clause is accepted
/// by the independent ground `evaluate` validator, or its actual Farkas
/// annotation proves the clause in the checker's linear fragment and can be
/// promoted to checked `la_generic`.
///
/// Surface overrides are a hard barrier for both promotions. The validators
/// reason about the internal term DAG, while an override changes the text the
/// external checker reads. Refusing promotion whenever that channel is
/// installed keeps the decision independent of presentation. Both the Alethe
/// printer and the publication wire-gap gate consume this function with the
/// same override state; neither may reconstruct the decision from
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
    if term_overrides.is_some() {
        return UNPROVED_STEP_RULE;
    }
    if lia_ground_evaluate_is_supported(terms, clause) {
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
}

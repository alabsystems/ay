// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact external-eligibility gates for Farkas-classified theory conflicts.

use ay_core::{FarkasAnnotation, Sort, Symbol, TermData, TermStore, TheoryLit};

use super::{is_pure_la_term, strip_not};

/// Whether every conflict literal is an "opaque-atom" linear-arithmetic
/// literal — a binary `<`/`<=`/`>`/`>=` comparison over Int/Real-sorted terms
/// (uninterpreted subterms are treated as opaque variables, exactly as the
/// semantic Farkas verifier and Alethe `la_generic` checkers do), or an
/// equality over Int/Real-sorted terms that is asserted TRUE (its blocking
/// literal is the negation, which `la_generic` consumes as an equality; an
/// equality asserted false would need a disequality case split downstream
/// checkers do not perform, so it is rejected) — AND the given certificate
/// passes the full semantic Farkas check in LINEAR-ONLY mode (no #4666
/// congruence merging, which external `la_generic` checkers cannot replay).
pub(super) fn opaque_arith_farkas_valid(
    terms: &TermStore,
    conflict: &[TheoryLit],
    farkas: &FarkasAnnotation,
) -> bool {
    opaque_arith_farkas_valid_memo(&mut LinearFarkasVerdict::new(), terms, conflict, farkas)
}

/// One-shot memo for the LINEAR Farkas verification of a FIXED
/// `(terms, conflict, farkas)` triple.
///
/// `classify_arith_conflict_kind` reaches that verification through three
/// different eligibility gates, and every one of them calls it with the same
/// three arguments — so a conflict that fails the first gate pays for the same
/// exponential orientation search up to three times. The gates genuinely
/// differ (which conflicts they will even consider), the verification does not,
/// so caching its result across one classification is behaviour-identical.
pub(super) struct LinearFarkasVerdict(Option<bool>);

impl LinearFarkasVerdict {
    pub(super) fn new() -> Self {
        Self(None)
    }

    pub(super) fn verified_linear(
        &mut self,
        terms: &TermStore,
        conflict: &[TheoryLit],
        farkas: &FarkasAnnotation,
    ) -> bool {
        *self.0.get_or_insert_with(|| {
            ay_core::proof_validation::verify_farkas_conflict_lits_linear(terms, conflict, farkas)
                .is_ok()
        })
    }
}

/// [`opaque_arith_farkas_valid`] sharing one [`LinearFarkasVerdict`] across the
/// several gates a single classification consults.
pub(super) fn opaque_arith_farkas_valid_memo(
    verdict: &mut LinearFarkasVerdict,
    terms: &TermStore,
    conflict: &[TheoryLit],
    farkas: &FarkasAnnotation,
) -> bool {
    if conflict.is_empty() {
        return false;
    }
    let eligible = conflict.iter().all(|lit| {
        let atom = strip_not(terms, lit.term);
        // `strip_not` flips into conflict polarity: a `Not` wrapper on the
        // conflict literal inverts the asserted value.
        let value = if matches!(terms.get(lit.term), TermData::Not(_)) {
            !lit.value
        } else {
            lit.value
        };
        match terms.get(atom) {
            TermData::App(Symbol::Named(name), args) if args.len() == 2 => {
                let arith_sorts = matches!(terms.sort(args[0]), Sort::Int | Sort::Real)
                    && matches!(terms.sort(args[1]), Sort::Int | Sort::Real);
                match name.as_str() {
                    "<" | "<=" | ">" | ">=" => arith_sorts,
                    "=" => arith_sorts && value,
                    _ => false,
                }
            }
            _ => false,
        }
    });
    if !eligible {
        return false;
    }
    // LINEAR-only verification: no congruence-closure merging of opaque
    // terms, matching exactly what external `la_generic` checkers can check.
    verdict.verified_linear(terms, conflict, farkas)
}

/// Whether an equality-bearing conflict is an exact, externally replayable
/// linear Farkas certificate.
///
/// The ordinary pure-arithmetic classifier deliberately excludes equality
/// atoms, while the integer fallback renders as Carcara-unsupported
/// `lia_generic`. Alethe `la_generic` does accept an ASSERTED equality as an
/// orientation-selectable row, provided every operand is genuinely linear and
/// the exact positional certificate eliminates all variables. Keep this narrower than
/// [`opaque_arith_farkas_valid`]: in particular, a repeated nonlinear product
/// must not gain `la_generic` authority merely because the internal verifier
/// can conservatively regard that product as one opaque atom.
pub(super) fn linear_equality_arith_farkas_valid_memo(
    verdict: &mut LinearFarkasVerdict,
    terms: &TermStore,
    conflict: &[TheoryLit],
    farkas: &FarkasAnnotation,
) -> bool {
    let mut has_asserted_equality = false;
    let eligible = !conflict.is_empty()
        && conflict.iter().all(|lit| {
            let atom = strip_not(terms, lit.term);
            let value = if matches!(terms.get(lit.term), TermData::Not(_)) {
                !lit.value
            } else {
                lit.value
            };
            let TermData::App(Symbol::Named(name), args) = terms.get(atom) else {
                return false;
            };
            if args.len() != 2
                || !is_pure_la_term(terms, args[0])
                || !is_pure_la_term(terms, args[1])
            {
                return false;
            }
            match name.as_str() {
                "<" | "<=" | ">" | ">=" => true,
                "=" if value => {
                    has_asserted_equality = true;
                    true
                }
                _ => false,
            }
        });
    eligible
        && has_asserted_equality
        && opaque_arith_farkas_valid_memo(verdict, terms, conflict, farkas)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::{Proof, TheoryLemmaKind};
    use num_bigint::BigInt;

    use crate::theory_inference::classify_arith_conflict_kind;

    #[test]
    fn integer_equality_farkas_classifies_and_exports_as_la_generic() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let zero = terms.mk_int(BigInt::from(0));
        let one = terms.mk_int(BigInt::from(1));
        let x_eq_zero = terms.mk_eq(x, zero);
        let x_ge_one = terms.mk_ge(x, one);
        let conflict = [
            TheoryLit::new(x_eq_zero, true),
            TheoryLit::new(x_ge_one, true),
        ];
        let farkas = FarkasAnnotation::from_ints(&[1, 1]);

        let kind = classify_arith_conflict_kind(&terms, &conflict, Some(&farkas));
        assert_eq!(kind, TheoryLemmaKind::LraFarkas);
        let not_x_eq_zero = terms.mk_not_raw(x_eq_zero);
        let not_x_ge_one = terms.mk_not_raw(x_ge_one);
        let mut proof = Proof::new();
        let eq_assume = proof.add_assume(x_eq_zero, None);
        let bound_assume = proof.add_assume(x_ge_one, None);
        let lemma = proof.add_theory_lemma_with_farkas_and_kind(
            "lra",
            vec![not_x_eq_zero, not_x_ge_one],
            farkas,
            kind,
        );
        let bound_blocker = proof.add_resolution(vec![not_x_ge_one], x_eq_zero, eq_assume, lemma);
        proof.add_resolution(Vec::new(), x_ge_one, bound_assume, bound_blocker);
        ay_proof::check_proof_strict(&proof, &terms)
            .expect("native strict checker must replay the equality certificate");
        let rendered = ay_proof::export_alethe(&proof, &terms);
        assert!(rendered.contains(":rule la_generic"), "{rendered}");
        assert!(!rendered.contains(":rule lia_generic"), "{rendered}");
    }

    #[test]
    fn integer_equality_farkas_rejects_bad_evidence_and_disequality() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let zero = terms.mk_int(BigInt::from(0));
        let one = terms.mk_int(BigInt::from(1));
        let x_eq_zero = terms.mk_eq(x, zero);
        let x_ge_one = terms.mk_ge(x, one);
        let bad = FarkasAnnotation::from_ints(&[2, 1]);
        let bad_conflict = [
            TheoryLit::new(x_eq_zero, true),
            TheoryLit::new(x_ge_one, true),
        ];
        assert_ne!(
            classify_arith_conflict_kind(&terms, &bad_conflict, Some(&bad)),
            TheoryLemmaKind::LraFarkas
        );

        let disequality = [TheoryLit::new(x_eq_zero, false)];
        let unit = FarkasAnnotation::from_ints(&[1]);
        assert_ne!(
            classify_arith_conflict_kind(&terms, &disequality, Some(&unit)),
            TheoryLemmaKind::LraFarkas
        );
    }

    #[test]
    fn nonlinear_integer_equality_stays_out_of_la_generic() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let zero = terms.mk_int(BigInt::from(0));
        let square = terms.mk_mul(vec![x, x]);
        let square_eq_zero = terms.mk_eq(square, zero);
        let square_gt_zero = terms.mk_gt(square, zero);
        let conflict = [
            TheoryLit::new(square_eq_zero, true),
            TheoryLit::new(square_gt_zero, true),
        ];
        let farkas = FarkasAnnotation::from_ints(&[1, 1]);

        assert_eq!(
            classify_arith_conflict_kind(&terms, &conflict, Some(&farkas)),
            TheoryLemmaKind::LiaGeneric
        );
    }
}

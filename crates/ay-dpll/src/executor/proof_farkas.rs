// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Farkas coefficient synthesis and reconstruction for theory lemma proofs.
//!
//! Extracted from `proof.rs` as part of #6763.

use ay_core::term::TermData;
use ay_core::{Proof, ProofStep, Symbol, TheoryLemmaKind};
use ay_core::{TermId, TermStore};
use ay_frontend::command::Term as FrontendTerm;

use super::proof_resolution::congruence::substitute_in_term;
use super::proof_surface_syntax::strip_frontend_annotations;

/// Synthesize Farkas coefficients for integer equality contradiction clauses.
///
/// Handles clauses of the form `(not (= t c1)) (not (= t c2))` where `t`
/// is an integer-sorted term and `c1 != c2` are distinct integer constants.
///
/// Each equality `(= t c)` in the blocking clause (as `Not(= t c)`) becomes
/// a conflict literal `(= t c) = true`. The Farkas validator decomposes this
/// equality into two alternative constraints: `t - c <= 0` and `c - t <= 0`.
/// With uniform coefficients `[1, 1]`, the search finds the alternative
/// combination that yields a positive constant:
///   e.g., `(t - c1) + (c2 - t) = c2 - c1 > 0` when `c1 != c2`.
pub(crate) fn synthesize_equality_farkas(
    terms: &TermStore,
    clause: &[TermId],
) -> Option<ay_core::FarkasAnnotation> {
    use ay_core::{FarkasAnnotation, Sort};

    if clause.len() != 2 {
        return None;
    }

    // Extract the equality atoms from negated literals.
    let decode_negated_eq = |term: TermId| -> Option<(TermId, TermId)> {
        let inner = match terms.get(term) {
            TermData::Not(inner) => *inner,
            _ => return None,
        };
        match terms.get(inner) {
            TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
                Some((args[0], args[1]))
            }
            _ => None,
        }
    };

    let (lhs1, rhs1) = decode_negated_eq(clause[0])?;
    let (lhs2, rhs2) = decode_negated_eq(clause[1])?;

    // Both must be Int-sorted.
    if !matches!(terms.sort(lhs1), Sort::Int) {
        return None;
    }

    // Must share one operand and differ on the other (constant).
    let extract_int_const = |term: TermId| -> Option<i64> {
        match terms.get(term) {
            TermData::Const(ay_core::Constant::Int(n)) => n.try_into().ok(),
            _ => None,
        }
    };

    // Check for pattern: (= t c1), (= t c2) -- shared LHS
    if lhs1 == lhs2 {
        let c1 = extract_int_const(rhs1)?;
        let c2 = extract_int_const(rhs2)?;
        if c1 == c2 {
            return None;
        }
        // Use uniform positive coefficients [1, 1]. The Farkas validator's
        // search over equality alternatives will find the contradicting
        // combination automatically.
        let coeffs = vec![
            num_rational::Rational64::from(1),
            num_rational::Rational64::from(1),
        ];
        return Some(FarkasAnnotation::new(coeffs));
    }

    // Check for pattern: (= c1 t), (= c2 t) -- shared RHS
    if rhs1 == rhs2 {
        let c1 = extract_int_const(lhs1)?;
        let c2 = extract_int_const(lhs2)?;
        if c1 == c2 {
            return None;
        }
        let coeffs = vec![
            num_rational::Rational64::from(1),
            num_rational::Rational64::from(1),
        ];
        return Some(FarkasAnnotation::new(coeffs));
    }

    None
}

/// Synthesize Farkas coefficients for mixed equality + arithmetic clauses.
///
/// Handles clauses containing exactly one equality literal `(not (= a b))`
/// plus arithmetic literals. Uses the equality to substitute `a → b` (or
/// vice versa) in the remaining literals, then runs Farkas reconstruction
/// on the substituted pure-arithmetic clause. The equality coefficient is
/// computed to cancel the substitution effect.
///
/// Example: `(cl (not (= sel x)) (not (< 0 x)) (not (<= sel 0)))`
/// → substitute `sel → x`: `(cl (not (< 0 x)) (not (<= x 0)))`
/// → Farkas {1, 1} → equality coefficient -1 → result {-1, 1, 1}.
pub(crate) fn synthesize_mixed_equality_arithmetic_farkas(
    terms: &mut TermStore,
    clause: &[TermId],
) -> Option<ay_core::FarkasAnnotation> {
    use ay_core::FarkasAnnotation;

    // Find equality literals in the clause.
    let mut eq_positions = Vec::new();
    for (i, &lit) in clause.iter().enumerate() {
        let inner = match terms.get(lit) {
            TermData::Not(inner) => *inner,
            _ => continue,
        };
        if matches!(terms.get(inner), TermData::App(Symbol::Named(n), args) if n == "=" && args.len() == 2)
        {
            eq_positions.push(i);
        }
    }

    // Handle exactly one equality for now.
    if eq_positions.len() != 1 || clause.len() < 3 {
        return None;
    }
    let eq_pos = eq_positions[0];
    let eq_inner = match terms.get(clause[eq_pos]) {
        TermData::Not(inner) => *inner,
        _ => return None,
    };
    let (lhs, rhs) = match terms.get(eq_inner) {
        TermData::App(Symbol::Named(n), args) if n == "=" && args.len() == 2 => (args[0], args[1]),
        _ => return None,
    };

    // Try both substitution directions: lhs→rhs and rhs→lhs.
    for &(from, to) in &[(lhs, rhs), (rhs, lhs)] {
        // Build substituted clause (without the equality literal).
        let mut sub_clause = Vec::with_capacity(clause.len() - 1);
        let mut any_changed = false;
        for (i, &lit) in clause.iter().enumerate() {
            if i == eq_pos {
                continue;
            }
            let subst = substitute_in_term(terms, lit, from, to);
            any_changed |= subst != lit;
            sub_clause.push(subst);
        }
        if !any_changed {
            continue;
        }

        // Try Farkas reconstruction on the substituted pure-arithmetic clause.
        let mut sub_farkas = None;
        let mut sub_kind = TheoryLemmaKind::LiaGeneric;
        if !try_lra_farkas_reconstruction(terms, &sub_clause, &mut sub_farkas, &mut sub_kind) {
            continue;
        }

        let sub_coeffs = sub_farkas.as_ref()?.coefficients.clone();
        if sub_coeffs.len() != sub_clause.len() {
            continue;
        }

        // Compute equality coefficient. The substitution replaced `from`
        // with `to` in the arithmetic constraints. The equality needs to
        // undo this: `to → from` direction, i.e., `to - from ≤ 0`,
        // which is the NEGATIVE direction for `(= from to)`.
        // Coefficient = -1 (negative direction: `to - from ≤ 0`).
        let eq_coeff = num_rational::Rational64::from(-1);

        // Assemble full coefficient vector.
        let mut coeffs = Vec::with_capacity(clause.len());
        let mut sub_idx = 0;
        for i in 0..clause.len() {
            if i == eq_pos {
                coeffs.push(eq_coeff);
            } else {
                coeffs.push(sub_coeffs[sub_idx]);
                sub_idx += 1;
            }
        }
        return Some(FarkasAnnotation::new(coeffs));
    }

    None
}

/// Reconstruct missing Farkas coefficients for arithmetic theory lemmas (#6757).
///
/// The post-rewrite promotion pass (`promote_generic_theory_lemma_kinds_after_rewrite`)
/// only handles trust-kind lemmas. Lemmas that are already `LiaGeneric` or
/// `LraFarkas` (from the theory solver) but lack Farkas coefficients are not
/// promoted — they need a separate reconstruction pass.
///
/// For each qualifying lemma: tries LRA solver first, then equality synthesis.
pub(crate) fn reconstruct_missing_farkas_coefficients(
    terms: &mut TermStore,
    proof: &mut Proof,
    assertions: &[TermId],
    hidden_equality_assertions: &[TermId],
) {
    // Collect equality assertions for clause unsimplification (#6757).
    // Combined-theory conflicts may record the linking equality as
    // `Not(true)` when the assertion was simplified at the SAT level.
    // The original assertion TermIds in ctx.assertions have the
    // un-simplified equality.
    let true_id = terms.true_term();
    let equality_assertions: Vec<TermId> = assertions
        .iter()
        .copied()
        .filter(|&term| {
            matches!(
                terms.get(term),
                TermData::App(Symbol::Named(n), args) if n == "=" && args.len() == 2
            )
        })
        .collect();
    let mut equality_assertions = equality_assertions;
    for &term in hidden_equality_assertions {
        if !equality_assertions.contains(&term) {
            equality_assertions.push(term);
        }
    }
    // (#6759) Also scan proof Assume steps for equality terms. In the
    // with_deferred_postprocessing path, provenance-aware assertions may
    // include equalities not present in ctx.assertions (which holds
    // simplified forms).
    for step in proof.steps.iter() {
        if let ProofStep::Assume(term) = step {
            if !equality_assertions.contains(term)
                && matches!(
                    terms.get(*term),
                    TermData::App(Symbol::Named(n), args) if n == "=" && args.len() == 2
                )
            {
                equality_assertions.push(*term);
            }
        }
    }

    for step in &mut proof.steps {
        let ProofStep::TheoryLemma {
            kind,
            clause,
            farkas,
            ..
        } = step
        else {
            continue;
        };
        if farkas.is_some() {
            continue;
        }
        // Skip non-arithmetic theory lemma kinds that can never produce
        // Farkas coefficients (BV bit-blasting, pure EUF congruence).
        if matches!(
            kind,
            TheoryLemmaKind::BvBitBlast
                | TheoryLemmaKind::BvBitBlastGate { .. }
                | TheoryLemmaKind::ArraySelectStore { .. }
                | TheoryLemmaKind::ArrayStorePermutation
                | TheoryLemmaKind::ArrayRowChain
                | TheoryLemmaKind::ArrayExtensionality
                | TheoryLemmaKind::FpToBv { .. }
                | TheoryLemmaKind::StringLengthAxiom
                | TheoryLemmaKind::StringContentAxiom
                | TheoryLemmaKind::StringNormalForm
                | TheoryLemmaKind::StringGroundEval
                | TheoryLemmaKind::RegexIntersectEmpty
                | TheoryLemmaKind::EufTransitive
                | TheoryLemmaKind::EufReflexive
                | TheoryLemmaKind::EufCongruent
                | TheoryLemmaKind::EufCongruentPred
        ) {
            continue;
        }

        if try_lra_farkas_reconstruction(terms, clause, farkas, kind) {
            continue;
        }

        // (#6757) If the clause contains `Not(true)` from a simplified
        // linking equality, try replacing it with each equality assumption
        // and re-attempting Farkas reconstruction.
        let simplified_positions: Vec<usize> = clause
            .iter()
            .enumerate()
            .filter_map(|(i, &lit)| match terms.get(lit) {
                TermData::Not(inner) if *inner == true_id => Some(i),
                _ => None,
            })
            .collect();
        if !simplified_positions.is_empty() {
            let original_clause = clause.clone();
            for &eq_term in &equality_assertions {
                // Create Not(eq_term) in the term store (#6757). The
                // negation may not exist yet because the clause was built
                // with Not(true) when EUF simplified the equality.
                let neg_eq = terms.mk_not_raw(eq_term);
                let mut candidate_clause = original_clause.clone();
                for &pos in &simplified_positions {
                    candidate_clause[pos] = neg_eq;
                }
                if try_lra_farkas_reconstruction(terms, &candidate_clause, farkas, kind) {
                    break;
                }
                // (#6759) If pure Farkas failed, try mixed equality+arithmetic
                // synthesis on the unsimplified candidate clause.
                if let Some(synth) =
                    synthesize_mixed_equality_arithmetic_farkas(terms, &candidate_clause)
                {
                    *farkas = Some(synth);
                    if kind.is_trust() || matches!(kind, TheoryLemmaKind::Generic) {
                        *kind = TheoryLemmaKind::LiaGeneric;
                    }
                    break;
                }
            }
            if farkas.is_some() {
                continue;
            }
        }

        // Fallback: equality synthesis for (= t c1) vs (= t c2) patterns.
        if let Some(synth) = synthesize_equality_farkas(terms, clause) {
            *farkas = Some(synth);
            if kind.is_trust() {
                *kind = TheoryLemmaKind::LiaGeneric;
            }
            continue;
        }

        // Fallback: mixed equality + arithmetic synthesis (#6759).
        // For clauses with one equality and arithmetic literals, substitute
        // equal terms to get a pure arithmetic clause, then run Farkas.
        if let Some(synth) = synthesize_mixed_equality_arithmetic_farkas(terms, clause) {
            *farkas = Some(synth);
            if kind.is_trust() {
                *kind = TheoryLemmaKind::LiaGeneric;
            }
        }
    }
}

/// Check if a frontend term is an equality application.
pub(crate) fn frontend_term_is_equality(term: &FrontendTerm) -> bool {
    matches!(
        strip_frontend_annotations(term),
        FrontendTerm::App(name, args) if name == "=" && args.len() == 2
    )
}

/// Try to reconstruct Farkas coefficients for a single theory lemma clause
/// using the LRA solver. Returns true if successful.
pub(crate) fn try_lra_farkas_reconstruction(
    terms: &TermStore,
    clause: &[TermId],
    farkas: &mut Option<ay_core::FarkasAnnotation>,
    kind: &mut TheoryLemmaKind,
) -> bool {
    let mut lra = ay_lra::LraSolver::new(terms);
    lra.set_combined_theory_mode(true);
    for &lit in clause.iter() {
        let atom = match terms.get(lit) {
            TermData::Not(inner) => *inner,
            _ => lit,
        };
        ay_core::TheorySolver::register_atom(&mut lra, atom);
    }
    for &lit in clause.iter() {
        let (atom, value) = match terms.get(lit) {
            TermData::Not(inner) => (*inner, true),
            _ => (lit, false),
        };
        ay_core::TheorySolver::assert_literal(&mut lra, atom, value);
    }
    let ay_core::TheoryResult::UnsatWithFarkas(conflict) = ay_core::TheorySolver::check(&mut lra)
    else {
        return false;
    };
    let Some(source_farkas) = conflict.farkas.as_ref() else {
        return false;
    };
    if source_farkas.coefficients.len() != conflict.literals.len() {
        return false;
    }

    // LraSolver returns coefficients in `conflict.literals` order, which is
    // free to differ from registration/assertion order. Recover the exact
    // blocking-clause identity of each row, then rebind by TermId. Attaching
    // this vector directly to `clause` is unsound after a solver permutation.
    let zero = num_rational::Rational64::from(0);
    let mut source_clause = Vec::with_capacity(conflict.literals.len());
    let mut source_coefficients = Vec::with_capacity(conflict.literals.len());
    for (&literal, coefficient) in conflict
        .literals
        .iter()
        .zip(source_farkas.coefficients.iter())
    {
        let blocker = clause.iter().copied().find(|&candidate| {
            if literal.value {
                matches!(terms.get(candidate), TermData::Not(inner) if *inner == literal.term)
            } else {
                candidate == literal.term
            }
        });
        match blocker {
            Some(blocker) => {
                source_clause.push(blocker);
                source_coefficients.push(*coefficient);
            }
            None if *coefficient == zero => {}
            None => return false,
        }
    }
    let source_farkas = ay_core::FarkasAnnotation::new(source_coefficients);
    let Some(rebound) = source_farkas.rebind_by_literal(&source_clause, clause) else {
        return false;
    };
    if !rebound.is_valid() {
        return false;
    }

    // Re-check the rebound certificate against the exact target clause before
    // it can become proof authority. This is independent of the producing LRA
    // solver and catches every remaining polarity/order mismatch fail-closed.
    let target_conflict: Vec<ay_core::TheoryLit> = clause
        .iter()
        .map(|&literal| match terms.get(literal) {
            TermData::Not(inner) => ay_core::TheoryLit::new(*inner, true),
            _ => ay_core::TheoryLit::new(literal, false),
        })
        .collect();
    if ay_core::proof_validation::verify_farkas_conflict_lits_full(
        terms,
        &target_conflict,
        &rebound,
    )
    .is_err()
    {
        return false;
    }

    let inferred_kind =
        crate::theory_inference::infer_theory_lemma_kind_from_clause_terms_and_farkas(
            terms,
            clause,
            Some(&rebound),
        );
    *farkas = Some(rebound);
    *kind = if inferred_kind.is_trust() {
        TheoryLemmaKind::LraFarkas
    } else {
        inferred_kind
    };
    true
}

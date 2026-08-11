// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Combined real-theory lemma decomposition for Alethe proof generation.
//!
//! Decomposes Generic/trust combined real-theory lemmas into an EUF
//! congruence lemma plus an arithmetic bridge lemma with Farkas
//! coefficients (#6756 Packet 2). Extracted from `theory_inference.rs`
//! for code health (#5970).

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{
    FarkasAnnotation, Sort, TermData, TermId, TermStore, TheoryConflict, TheoryLemmaKind, TheoryLit,
};

use super::decode_eq;

/// Decompose a Generic/trust combined real-theory lemma into an EUF congruence
/// lemma plus an arithmetic bridge lemma with Farkas coefficients (#6756 Packet 2).
///
/// Returns `(euf_kind, euf_clause, bridge_clause, bridge_farkas)` if the lemma
/// can be decomposed, or `None` if it doesn't match the combined pattern.
///
/// Called from `proof.rs::decompose_combined_real_conflict_lemmas`.
pub(crate) fn decompose_generic_combined_real_lemma(
    terms: &mut TermStore,
    clause: &[TermId],
) -> Option<(TheoryLemmaKind, Vec<TermId>, Vec<TermId>, FarkasAnnotation)> {
    // All literals must be negated equalities with non-Int operands.
    let mut eq_atoms: Vec<(TermId, TermId, TermId, TermId)> = Vec::new();
    for &lit in clause {
        let eq = match terms.get(lit) {
            TermData::Not(inner) => *inner,
            _ => return None,
        };
        let (lhs, rhs) = decode_eq(terms, eq)?;
        if matches!(terms.sort(lhs), Sort::Int) || matches!(terms.sort(rhs), Sort::Int) {
            return None;
        }
        eq_atoms.push((lit, eq, lhs, rhs));
    }
    if eq_atoms.len() < 3 {
        return None;
    }

    let mut eq_by_pair: HashMap<(TermId, TermId), (TermId, TermId)> = HashMap::default();
    for &(not_eq, eq, lhs, rhs) in &eq_atoms {
        let pair = if lhs.0 <= rhs.0 {
            (lhs, rhs)
        } else {
            (rhs, lhs)
        };
        eq_by_pair.insert(pair, (eq, not_eq));
    }

    // Try all pairs of operands from different equalities to find a congruence.
    for i in 0..eq_atoms.len() {
        for j in (i + 1)..eq_atoms.len() {
            for &(candidate_lhs, candidate_rhs) in &[
                (eq_atoms[i].2, eq_atoms[j].2),
                (eq_atoms[i].2, eq_atoms[j].3),
                (eq_atoms[i].3, eq_atoms[j].2),
                (eq_atoms[i].3, eq_atoms[j].3),
            ] {
                if let Some(result) = try_congruence_decomposition(
                    terms,
                    clause,
                    &eq_by_pair,
                    candidate_lhs,
                    candidate_rhs,
                ) {
                    return Some(result);
                }
            }
        }
    }
    None
}

fn try_congruence_decomposition(
    terms: &mut TermStore,
    clause: &[TermId],
    eq_by_pair: &HashMap<(TermId, TermId), (TermId, TermId)>,
    candidate_lhs: TermId,
    candidate_rhs: TermId,
) -> Option<(TheoryLemmaKind, Vec<TermId>, Vec<TermId>, FarkasAnnotation)> {
    if candidate_lhs == candidate_rhs {
        return None;
    }
    let (lhs_sym, lhs_args) = match terms.get(candidate_lhs) {
        TermData::App(sym, args) if !args.is_empty() => (sym.clone(), args.clone()),
        _ => return None,
    };
    let (rhs_sym, rhs_args) = match terms.get(candidate_rhs) {
        TermData::App(sym, args) if !args.is_empty() => (sym.clone(), args.clone()),
        _ => return None,
    };
    if lhs_sym != rhs_sym || lhs_args.len() != rhs_args.len() {
        return None;
    }

    let mut arg_eq_not_lits = Vec::with_capacity(lhs_args.len());
    let mut used_eq_atoms = Vec::new();
    for (a, b) in lhs_args.iter().copied().zip(rhs_args.iter().copied()) {
        if a == b {
            continue;
        }
        let pair = if a.0 <= b.0 { (a, b) } else { (b, a) };
        let &(eq, not_eq) = eq_by_pair.get(&pair)?;
        arg_eq_not_lits.push(not_eq);
        used_eq_atoms.push(eq);
    }
    if arg_eq_not_lits.is_empty() {
        return None;
    }

    // Synthesize the conclusion equality and its negation.
    let conclusion_eq = terms.mk_eq_coerce(candidate_lhs, candidate_rhs);
    let conclusion_neg = terms.mk_not(conclusion_eq);

    // EUF lemma: negated premise equalities + positive conclusion.
    let mut euf_clause = arg_eq_not_lits;
    euf_clause.push(conclusion_eq);

    // Bridge clause: original literals NOT used by EUF + negated conclusion.
    let used_set: HashSet<TermId> = used_eq_atoms.iter().copied().collect();
    let mut bridge_clause = Vec::new();
    for &lit in clause {
        let eq = match terms.get(lit) {
            TermData::Not(inner) => *inner,
            _ => continue,
        };
        if !used_set.contains(&eq) {
            bridge_clause.push(lit);
        }
    }
    bridge_clause.push(conclusion_neg);

    // Validate bridge via temporary LRA replay.
    let farkas = replay_bridge_clause_with_farkas(terms, &bridge_clause)?;
    Some((
        TheoryLemmaKind::EufCongruent,
        euf_clause,
        bridge_clause,
        farkas,
    ))
}

/// Replay a clause through a temporary LRA solver to obtain Farkas coefficients.
fn replay_bridge_clause_with_farkas(
    terms: &TermStore,
    clause: &[TermId],
) -> Option<FarkasAnnotation> {
    let mut lra = ay_lra::LraSolver::new(terms);
    lra.set_combined_theory_mode(true);
    for &lit in clause {
        let atom = match terms.get(lit) {
            TermData::Not(inner) => *inner,
            _ => lit,
        };
        ay_core::TheorySolver::register_atom(&mut lra, atom);
    }
    for &lit in clause {
        let (atom, value) = match terms.get(lit) {
            TermData::Not(inner) => (*inner, true),
            _ => (lit, false),
        };
        ay_core::TheorySolver::assert_literal(&mut lra, atom, value);
    }
    let ay_core::TheoryResult::UnsatWithFarkas(conflict) = ay_core::TheorySolver::check(&mut lra)
    else {
        return None;
    };
    rebind_replayed_farkas(terms, clause, &conflict)
}

/// Rebind an LRA replay certificate from the solver's conflict order to the
/// bridge clause's order, then validate it against that exact clause.
///
/// `LraSolver` may return a conflict subset in an order different from the
/// assertion order. Farkas coefficients are positional, so a length check alone
/// cannot establish that they still describe `target_clause`.
fn rebind_replayed_farkas(
    terms: &TermStore,
    target_clause: &[TermId],
    conflict: &TheoryConflict,
) -> Option<FarkasAnnotation> {
    let source_farkas = conflict.farkas.as_ref()?;
    if source_farkas.coefficients.len() != conflict.literals.len() {
        return None;
    }

    let zero = num_rational::Rational64::from(0);
    let mut source_clause = Vec::with_capacity(conflict.literals.len());
    let mut source_coefficients = Vec::with_capacity(conflict.literals.len());
    for (&literal, coefficient) in conflict
        .literals
        .iter()
        .zip(source_farkas.coefficients.iter())
    {
        let blocker = target_clause.iter().copied().find(|&candidate| {
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
            None => return None,
        }
    }

    let source_farkas = FarkasAnnotation::new(source_coefficients);
    let rebound = source_farkas.rebind_by_literal(&source_clause, target_clause)?;
    let target_conflict: Vec<TheoryLit> = target_clause
        .iter()
        .map(|&literal| match terms.get(literal) {
            TermData::Not(inner) => TheoryLit::new(*inner, true),
            _ => TheoryLit::new(literal, false),
        })
        .collect();
    ay_core::proof_validation::verify_farkas_conflict_lits_full(terms, &target_conflict, &rebound)
        .ok()?;
    Some(rebound)
}

#[cfg(test)]
mod tests {
    use num_bigint::BigInt;
    use num_rational::BigRational;

    use super::*;

    #[test]
    fn replayed_farkas_is_rebound_from_permuted_nonuniform_conflict() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Real);
        let zero = terms.mk_rational(BigRational::from_integer(BigInt::from(0)));
        let one = terms.mk_rational(BigRational::from_integer(BigInt::from(1)));
        let three = terms.mk_rational(BigRational::from_integer(BigInt::from(3)));
        let three_x = terms.mk_mul(vec![three, x]);
        let three_x_le_zero = terms.mk_le(three_x, zero);
        let x_ge_one = terms.mk_ge(x, one);
        let not_three_x_le_zero = terms.mk_not(three_x_le_zero);
        let not_x_ge_one = terms.mk_not(x_ge_one);

        let target_clause = vec![not_three_x_le_zero, not_x_ge_one];
        let target_conflict = vec![
            TheoryLit::new(three_x_le_zero, true),
            TheoryLit::new(x_ge_one, true),
        ];
        let source_farkas = FarkasAnnotation::from_ints(&[3, 1]);
        assert!(ay_core::proof_validation::verify_farkas_conflict_lits_full(
            &terms,
            &target_conflict,
            &source_farkas,
        )
        .is_err());

        let solver_conflict = TheoryConflict::with_farkas(
            vec![
                TheoryLit::new(x_ge_one, true),
                TheoryLit::new(three_x_le_zero, true),
            ],
            source_farkas,
        );
        let rebound = rebind_replayed_farkas(&terms, &target_clause, &solver_conflict)
            .expect("permuted replay certificate should rebind by literal identity");

        assert_eq!(rebound, FarkasAnnotation::from_ints(&[1, 3]));
        ay_core::proof_validation::verify_farkas_conflict_lits_full(
            &terms,
            &target_conflict,
            &rebound,
        )
        .expect("rebound certificate must validate against the exact bridge clause");
    }
}

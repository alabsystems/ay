// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::SatProofManager;
use ay_core::{AletheRule, Proof, ProofId, ProofStep, Sort, Symbol, TermId, TermStore, Tseitin};
use ay_proof::{authenticate_premise_clauses_strict_with_context, ProofCheckError};

fn canonical(
    terms: &mut TermStore,
    rule: &AletheRule,
    source: TermId,
    clause: &[TermId],
) -> Option<Vec<TermId>> {
    SatProofManager::canonicalize_tautology_clause(terms, rule, source, clause)
}

fn strict_replay(
    terms: &TermStore,
    rule: &AletheRule,
    equality: TermId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    let mut proof = Proof::default();
    proof.steps.push(ProofStep::Step {
        rule: rule.clone(),
        clause: clause.to_vec(),
        premises: Vec::new(),
        args: vec![equality],
    });
    // Authenticate the original tautology with no assumed problem inputs.
    // A repeated literal remains legal; no synthetic refutation is required.
    let authenticated =
        authenticate_premise_clauses_strict_with_context(&proof, terms, None, None, &[])?;
    assert_eq!(authenticated.clause(ProofId(0)), Some(clause));
    Ok(())
}

fn replay_permutations(
    terms: &mut TermStore,
    rule: &AletheRule,
    equality: TermId,
    traced: &[TermId],
) -> usize {
    for rotation in 0..3 {
        for reverse in [false, true] {
            let mut permutation = traced.to_vec();
            permutation.rotate_left(rotation);
            if reverse {
                permutation.reverse();
            }
            let rebuilt = canonical(terms, rule, equality, &permutation)
                .expect("an authentic encoder annotation must reconstruct");
            strict_replay(terms, rule, equality, &rebuilt)
                .expect("the independent checker must accept the exact named rule");
        }
    }
    let wrong = match rule {
        AletheRule::EquivNeg1 => Some(AletheRule::EquivNeg2),
        AletheRule::EquivNeg2 => Some(AletheRule::EquivNeg1),
        _ => None,
    };
    if let Some(wrong) = wrong {
        assert!(
            canonical(terms, &wrong, equality, traced).is_none(),
            "a swapped rule label is not authority for the traced clause"
        );
        assert!(
            strict_replay(terms, &wrong, equality, traced).is_err(),
            "the independent checker must also reject the swapped rule"
        );
    }
    // Remove every occurrence: an identical operand can repeat a literal.
    let missing = traced[0];
    let shortened: Vec<_> = traced.iter().copied().filter(|&t| t != missing).collect();
    assert!(
        canonical(terms, rule, equality, &shortened).is_none(),
        "removing a distinct literal must invalidate the annotation"
    );
    6
}

// The source of the expected rule/clauses is the actual CNF encoder. The
// independent strict checker must replay each reconstructed clause.
#[test]
fn encoder_equivalence_annotations_survive_permutation_and_strict_replay() {
    let mut checked = 0;
    for shape in 0..6 {
        let mut terms = TermStore::new();
        let p = terms.mk_var("p", Sort::Bool);
        let q = terms.mk_var("q", Sort::Bool);
        let r = terms.mk_var("r", Sort::Bool);
        let a = if shape == 1 || shape == 3 {
            terms.mk_not_raw(p)
        } else {
            p
        };
        let b = match shape {
            2 | 3 => terms.mk_not_raw(q),
            4 => terms.mk_and(vec![q, r]),
            5 => p,
            _ => q,
        };
        let equality = terms.mk_app(Symbol::named("="), vec![a, b], Sort::Bool);
        let encoded = Tseitin::new_with_proofs(&terms).transform(equality);
        let annotations = encoded
            .proof_annotations
            .as_ref()
            .expect("annotations retained");
        let mut rules = Vec::new();
        for (clause, annotation) in encoded.clauses.iter().zip(annotations) {
            let Some(annotation) = annotation else {
                continue;
            };
            if annotation.source_term != equality {
                continue;
            }
            rules.push(annotation.rule.clone());
            let traced: Vec<TermId> = clause
                .literals()
                .iter()
                .map(|&literal| {
                    let term = encoded.var_to_term[&literal.unsigned_abs()];
                    if literal < 0 {
                        terms.mk_not_raw(term)
                    } else {
                        term
                    }
                })
                .collect();
            assert_eq!(traced.len(), 3);
            checked += replay_permutations(&mut terms, &annotation.rule, equality, &traced);
        }
        assert_eq!(rules.len(), 4);
        for rule in [
            AletheRule::EquivPos1,
            AletheRule::EquivPos2,
            AletheRule::EquivNeg1,
            AletheRule::EquivNeg2,
        ] {
            assert!(rules.contains(&rule));
        }
    }
    assert_eq!(checked, 144);
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#[cfg(kani)]
use ay_core::kani_compat::DetHashSet as HashSet;
#[cfg(not(kani))]
// #8529: Use deterministic hash sets in all builds.
use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::TermData;
use ay_core::{AletheRule, Proof, ProofId, ProofStep, Symbol, TermId, TermStore, TheoryLemmaKind};

use super::empty_clause::collect_assumptions_and_theory_lemmas;

/// Red zone size for `stacker::maybe_grow` in congruence substitution recursion (#8414).
const CONG_SUBST_STACK_RED_ZONE: usize = 32 * 1024;

/// Stack segment size allocated by stacker for congruence substitution recursion.
const CONG_SUBST_STACK_SIZE: usize = 1024 * 1024;

/// Per-literal bridge instruction for congruence-based empty-clause derivation.
///
/// Used by [`try_derive_empty_via_congruence_bridging`] to record
/// how each theory-lemma literal resolves against the proof assumptions.
pub(crate) enum CongruenceBridge {
    /// Literal resolves directly against assumption at `assumptions[idx]`.
    Direct(usize),
    /// Literal requires an `eq_congruent_pred` step bridging `from → to`
    /// via the equality assumption at `eq_pid`, then resolves with `assumptions[assume_idx]`.
    ViaCongruence {
        assume_idx: usize,
        eq_pid: ProofId,
        from: TermId,
        to: TermId,
    },
}

/// Bridge VarSubst-induced term mismatches via EUF congruence steps.
pub(crate) fn try_derive_empty_via_congruence_bridging(
    terms: &mut TermStore,
    proof: &mut Proof,
) -> bool {
    let (assumptions, theory_lemmas) = collect_assumptions_and_theory_lemmas(proof);
    if assumptions.is_empty() || theory_lemmas.is_empty() {
        return false;
    }

    let equality_assumptions: Vec<(ProofId, TermId, TermId)> = assumptions
        .iter()
        .filter_map(|&(pid, term)| {
            if let TermData::App(Symbol::Named(name), args) = terms.get(term) {
                if name == "=" && args.len() == 2 {
                    return Some((pid, args[0], args[1]));
                }
            }
            None
        })
        .collect();

    if equality_assumptions.is_empty() {
        return false;
    }

    for (lemma_id, lemma_clause) in &theory_lemmas {
        if let Some(derivation) = try_bridge_lemma_with_congruence(
            terms,
            lemma_clause,
            &assumptions,
            &equality_assumptions,
        ) {
            apply_congruence_bridged_derivation(
                terms,
                proof,
                *lemma_id,
                lemma_clause,
                &assumptions,
                &derivation,
            );
            return true;
        }
    }

    false
}

fn try_bridge_lemma_with_congruence(
    terms: &mut TermStore,
    lemma_clause: &[TermId],
    assumptions: &[(ProofId, TermId)],
    equality_assumptions: &[(ProofId, TermId, TermId)],
) -> Option<Vec<CongruenceBridge>> {
    let mut bridges = Vec::with_capacity(lemma_clause.len());
    let mut used_assumptions: HashSet<usize> = HashSet::default();

    for &lit in lemma_clause {
        if let Some(idx) = find_direct_resolution_assumption(terms, lit, assumptions) {
            if used_assumptions.insert(idx) {
                bridges.push(CongruenceBridge::Direct(idx));
                continue;
            }
        }

        let mut bridged = false;
        for &(eq_pid, lhs, rhs) in equality_assumptions {
            for &(from, to) in &[(lhs, rhs), (rhs, lhs)] {
                let substituted = substitute_in_term(terms, lit, from, to);
                if substituted == lit {
                    continue;
                }
                if let Some(idx) =
                    find_direct_resolution_assumption(terms, substituted, assumptions)
                {
                    if used_assumptions.insert(idx) {
                        bridges.push(CongruenceBridge::ViaCongruence {
                            assume_idx: idx,
                            eq_pid,
                            from,
                            to,
                        });
                        bridged = true;
                        break;
                    }
                }
            }
            if bridged {
                break;
            }
        }
        if !bridged {
            return None;
        }
    }

    Some(bridges)
}

/// Find the assumption index that resolves directly with a lemma literal.
pub(crate) fn find_direct_resolution_assumption(
    terms: &TermStore,
    lit: TermId,
    assumptions: &[(ProofId, TermId)],
) -> Option<usize> {
    let target = if let TermData::Not(inner) = terms.get(lit) {
        *inner
    } else {
        return assumptions
            .iter()
            .position(|&(_, a)| matches!(terms.get(a), TermData::Not(inner) if *inner == lit));
    };
    assumptions.iter().position(|&(_, a)| a == target)
}

/// Substitute one term for another within a composite term.
/// Uses `stacker::maybe_grow` for stack safety on deeply nested terms (#8414).
pub(crate) fn substitute_in_term(
    terms: &mut TermStore,
    term: TermId,
    from: TermId,
    to: TermId,
) -> TermId {
    stacker::maybe_grow(CONG_SUBST_STACK_RED_ZONE, CONG_SUBST_STACK_SIZE, || {
        if term == from {
            return to;
        }
        match terms.get(term).clone() {
            TermData::Not(inner) => {
                let new_inner = substitute_in_term(terms, inner, from, to);
                if new_inner == inner {
                    term
                } else {
                    terms.mk_not(new_inner)
                }
            }
            TermData::App(sym, args) => {
                let mut changed = false;
                let new_args: Vec<TermId> = args
                    .into_iter()
                    .map(|a| {
                        let na = substitute_in_term(terms, a, from, to);
                        changed |= na != a;
                        na
                    })
                    .collect();
                if !changed {
                    term
                } else {
                    terms.mk_app(sym, new_args, terms.sort(term).clone())
                }
            }
            _ => term,
        }
    }) // stacker::maybe_grow
}

/// Build the proof steps for a congruence-bridged derivation.
fn apply_congruence_bridged_derivation(
    terms: &mut TermStore,
    proof: &mut Proof,
    lemma_id: ProofId,
    lemma_clause: &[TermId],
    assumptions: &[(ProofId, TermId)],
    bridges: &[CongruenceBridge],
) {
    let mut current_id = lemma_id;
    let mut current_clause = lemma_clause.to_vec();

    for (lit_idx, bridge) in bridges.iter().enumerate() {
        let lemma_lit = lemma_clause[lit_idx];

        match bridge {
            CongruenceBridge::Direct(assume_idx) => {
                let (assume_id, _) = assumptions[*assume_idx];
                current_clause.retain(|&t| t != lemma_lit);
                current_id = proof.add_step(ProofStep::Step {
                    rule: AletheRule::ThResolution,
                    clause: current_clause.clone(),
                    premises: vec![current_id, assume_id],
                    args: vec![],
                });
            }
            CongruenceBridge::ViaCongruence {
                assume_idx,
                eq_pid,
                from,
                to,
            } => {
                let (assume_id, assume_term) = assumptions[*assume_idx];
                let eq_term = terms.mk_eq(*from, *to);
                let neg_eq = terms.mk_not(eq_term);
                let neg_assume = if let TermData::Not(inner) = terms.get(assume_term) {
                    *inner
                } else {
                    terms.mk_not_raw(assume_term)
                };

                let cong_id = proof.add_step(ProofStep::TheoryLemma {
                    theory: "eq_congruent_pred".to_string(),
                    clause: vec![neg_eq, neg_assume, lemma_lit],
                    farkas: None,
                    kind: TheoryLemmaKind::EufCongruentPred,
                    lia: None,
                });

                let after_eq_id = proof.add_step(ProofStep::Step {
                    rule: AletheRule::ThResolution,
                    clause: vec![neg_assume, lemma_lit],
                    premises: vec![cong_id, *eq_pid],
                    args: vec![],
                });

                let unit_id = proof.add_step(ProofStep::Step {
                    rule: AletheRule::ThResolution,
                    clause: vec![lemma_lit],
                    premises: vec![after_eq_id, assume_id],
                    args: vec![],
                });

                current_clause.retain(|&t| t != lemma_lit);
                current_id = proof.add_step(ProofStep::Step {
                    rule: AletheRule::ThResolution,
                    clause: current_clause.clone(),
                    premises: vec![current_id, unit_id],
                    args: vec![],
                });
            }
        }
    }

    debug_assert!(
        current_clause.is_empty(),
        "congruence-bridged derivation did not derive empty clause"
    );
}

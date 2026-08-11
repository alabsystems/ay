// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! EUF theory inference for Alethe proof generation.
//!
//! Infers congruence, congruent-predicate, and transitivity lemma kinds
//! from theory conflict literals. Extracted from `theory_inference.rs`
//! for code health (#5970).

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{Sort, TermData, TermId, TermStore, TheoryLemmaKind, TheoryLit};

use super::decode_eq;

/// Try to infer an EUF lemma kind (congruent, congruent-pred, or transitive)
/// from a theory conflict. Returns the kind and the reordered clause.
pub(super) fn infer_euf_lemma(
    terms: &TermStore,
    negations: &HashMap<TermId, TermId>,
    conflict: &[TheoryLit],
) -> Option<(TheoryLemmaKind, Vec<TermId>)> {
    infer_euf_congruent_pred(terms, negations, conflict)
        .or_else(|| infer_euf_congruent(terms, negations, conflict))
        .or_else(|| infer_euf_transitive(terms, negations, conflict))
}

fn infer_euf_congruent_pred(
    terms: &TermStore,
    negations: &HashMap<TermId, TermId>,
    conflict: &[TheoryLit],
) -> Option<(TheoryLemmaKind, Vec<TermId>)> {
    let mut pred_lits = Vec::new();
    let mut premise_eqs = Vec::new();
    for &lit in conflict {
        if decode_eq(terms, lit.term).is_some() {
            // Premises for congruence predicates must be asserted true.
            if !lit.value {
                return None;
            }
            premise_eqs.push(lit.term);
        } else if terms.sort(lit.term) == &Sort::Bool {
            pred_lits.push(lit);
        } else {
            return None;
        }
    }

    if pred_lits.len() != 2 || pred_lits[0].value == pred_lits[1].value {
        return None;
    }

    let (p_term, p_args) = match terms.get(pred_lits[0].term) {
        TermData::App(sym, args) => (sym, args.as_slice()),
        _ => return None,
    };
    let (q_term, q_args) = match terms.get(pred_lits[1].term) {
        TermData::App(sym, args) => (sym, args.as_slice()),
        _ => return None,
    };

    if p_term != q_term || p_args.len() != q_args.len() || p_args.is_empty() {
        return None;
    }

    let mut eq_by_pair: HashMap<(TermId, TermId), TermId> = HashMap::default();
    for &eq_term in &premise_eqs {
        let (a, b) = decode_eq(terms, eq_term)?;
        let pair = if a.0 <= b.0 { (a, b) } else { (b, a) };
        eq_by_pair.insert(pair, eq_term);
    }

    if eq_by_pair.len() != p_args.len() {
        return None;
    }

    let mut clause = Vec::with_capacity(p_args.len() + 2);
    for (a, b) in p_args.iter().copied().zip(q_args.iter().copied()) {
        let pair = if a.0 <= b.0 { (a, b) } else { (b, a) };
        let eq_term = *eq_by_pair.get(&pair)?;
        clause.push(*negations.get(&eq_term)?);
    }

    let (true_pred, false_pred) = if pred_lits[0].value {
        (pred_lits[0].term, pred_lits[1].term)
    } else {
        (pred_lits[1].term, pred_lits[0].term)
    };
    clause.push(*negations.get(&true_pred)?);
    clause.push(false_pred);

    Some((TheoryLemmaKind::EufCongruentPred, clause))
}

fn infer_euf_congruent(
    terms: &TermStore,
    negations: &HashMap<TermId, TermId>,
    conflict: &[TheoryLit],
) -> Option<(TheoryLemmaKind, Vec<TermId>)> {
    let mut conclusion_eq = None;
    let mut premise_eqs = Vec::new();
    for &lit in conflict {
        let _ = decode_eq(terms, lit.term)?;
        if lit.value {
            premise_eqs.push(lit.term);
        } else if conclusion_eq.replace(lit.term).is_some() {
            // Multiple false equalities: ambiguous.
            return None;
        }
    }

    let conclusion_eq = conclusion_eq?;
    let (lhs, rhs) = decode_eq(terms, conclusion_eq)?;

    let (lhs_sym, lhs_args) = match terms.get(lhs) {
        TermData::App(sym, args) => (sym, args.as_slice()),
        _ => return None,
    };
    let (rhs_sym, rhs_args) = match terms.get(rhs) {
        TermData::App(sym, args) => (sym, args.as_slice()),
        _ => return None,
    };
    if lhs_sym != rhs_sym || lhs_args.len() != rhs_args.len() || lhs_args.is_empty() {
        return None;
    }

    let mut eq_by_pair: HashMap<(TermId, TermId), TermId> = HashMap::default();
    for &eq_term in &premise_eqs {
        let (a, b) = decode_eq(terms, eq_term)?;
        let pair = if a.0 <= b.0 { (a, b) } else { (b, a) };
        eq_by_pair.insert(pair, eq_term);
    }
    if eq_by_pair.len() != lhs_args.len() {
        return None;
    }

    let mut clause = Vec::with_capacity(lhs_args.len() + 1);
    for (a, b) in lhs_args.iter().copied().zip(rhs_args.iter().copied()) {
        let pair = if a.0 <= b.0 { (a, b) } else { (b, a) };
        let eq_term = *eq_by_pair.get(&pair)?;
        clause.push(*negations.get(&eq_term)?);
    }
    clause.push(conclusion_eq);

    Some((TheoryLemmaKind::EufCongruent, clause))
}

fn infer_euf_transitive(
    terms: &TermStore,
    negations: &HashMap<TermId, TermId>,
    conflict: &[TheoryLit],
) -> Option<(TheoryLemmaKind, Vec<TermId>)> {
    let mut conclusion_eq = None;
    let mut premise_eqs = Vec::new();
    for &lit in conflict {
        let _ = decode_eq(terms, lit.term)?;
        if lit.value {
            premise_eqs.push(lit.term);
        } else if conclusion_eq.replace(lit.term).is_some() {
            // Multiple false equalities: ambiguous.
            return None;
        }
    }

    let conclusion_eq = conclusion_eq?;
    let (lhs, rhs) = decode_eq(terms, conclusion_eq)?;

    // Reflexive conclusion: the refuted disequality relates a term to ITSELF,
    // so there is no chain to walk and nothing for transitivity to say. The
    // BFS below would terminate at once, leave `chain_eqs` empty and build a
    // ONE-literal `eq_transitive` clause — a shape the strict checker rejects
    // outright, turning a correct refutation into an uncertifiable one and,
    // under mandatory certification, into `unknown`. `eq_reflexive` states
    // exactly this conflict and its clause is legitimately a unit.
    if lhs == rhs {
        return Some((TheoryLemmaKind::EufReflexive, vec![conclusion_eq]));
    }

    // Build adjacency: term -> neighbors with the equality term that connects them.
    let mut adj: HashMap<TermId, Vec<(TermId, TermId)>> = HashMap::default();
    for &eq_term in &premise_eqs {
        let (a, b) = decode_eq(terms, eq_term)?;
        adj.entry(a).or_default().push((b, eq_term));
        adj.entry(b).or_default().push((a, eq_term));
    }
    // Sort adjacency lists by TermId for deterministic BFS traversal order.
    for neighbors in adj.values_mut() {
        neighbors.sort_unstable_by_key(|&(next, _)| next);
    }

    // BFS from lhs to rhs, recording parent edge.
    let mut queue = std::collections::VecDeque::new();
    let mut parent: HashMap<TermId, (TermId, TermId)> = HashMap::default();
    queue.push_back(lhs);
    parent.insert(lhs, (lhs, TermId(u32::MAX)));

    while let Some(curr) = queue.pop_front() {
        if curr == rhs {
            break;
        }
        if let Some(neighbors) = adj.get(&curr) {
            for &(next, edge_eq) in neighbors {
                if !parent.contains_key(&next) {
                    parent.insert(next, (curr, edge_eq));
                    queue.push_back(next);
                }
            }
        }
    }

    if !parent.contains_key(&rhs) {
        return None;
    }

    // Reconstruct the chain of premise equalities from lhs to rhs.
    let mut chain_eqs = Vec::new();
    let mut curr = rhs;
    while curr != lhs {
        let (prev, edge_eq) = parent.get(&curr).copied()?;
        chain_eqs.push(edge_eq);
        curr = prev;
    }
    chain_eqs.reverse();

    let mut clause = Vec::with_capacity(chain_eqs.len() + 1);
    for eq_term in chain_eqs {
        clause.push(*negations.get(&eq_term)?);
    }
    clause.push(conclusion_eq);

    Some((TheoryLemmaKind::EufTransitive, clause))
}

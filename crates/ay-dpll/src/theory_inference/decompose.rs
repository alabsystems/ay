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
    FarkasAnnotation, Sort, Symbol, TermData, TermId, TermStore, TheoryConflict, TheoryLemmaKind,
    TheoryLit,
};

use super::decode_eq;

/// Maximum Generic lemmas inspected by this pass in one proof.
const MAX_DECOMPOSITION_ATTEMPTS_PER_PROOF: usize = 128;
/// Maximum literals inspected in one candidate clause.
const MAX_DECOMPOSITION_CLAUSE_LITERALS: usize = 64;
/// Maximum candidate operand pairs inspected for one Generic lemma.
const MAX_CANDIDATE_PROBES_PER_CLAUSE: usize = 4096;
/// Maximum arguments inspected in either candidate application.
const MAX_CANDIDATE_APPLICATION_ARITY: usize = 64;
/// Maximum bytes compared in either candidate application's symbol name.
const MAX_CANDIDATE_SYMBOL_NAME_BYTES: usize = 256;
/// Maximum indexed-symbol parameters compared per candidate application.
const MAX_CANDIDATE_SYMBOL_INDICES: usize = 64;
/// Maximum fresh LRA solvers constructed for one Generic lemma.
const MAX_LRA_REPLAYS_PER_CLAUSE: usize = 32;
/// Maximum fresh LRA solvers constructed by the pass in one proof.
const MAX_LRA_REPLAYS_PER_PROOF: usize = 64;

/// Shared resource envelope for one proof's combined-conflict pass.
///
/// Exhaustion declines decomposition, leaving the original Generic lemma for
/// strict checking. It can therefore cost proof completeness, never soundness.
pub(crate) struct CombinedDecompositionBudget {
    remaining_attempts: usize,
    remaining_replays: usize,
    candidate_probes_per_clause: usize,
    replays_per_clause: usize,
}

struct ClauseDecompositionBudget {
    remaining_candidate_probes: usize,
    remaining_replays: usize,
}

impl CombinedDecompositionBudget {
    pub(crate) const fn new() -> Self {
        Self {
            remaining_attempts: MAX_DECOMPOSITION_ATTEMPTS_PER_PROOF,
            remaining_replays: MAX_LRA_REPLAYS_PER_PROOF,
            candidate_probes_per_clause: MAX_CANDIDATE_PROBES_PER_CLAUSE,
            replays_per_clause: MAX_LRA_REPLAYS_PER_CLAUSE,
        }
    }

    fn begin_clause(&mut self) -> Option<ClauseDecompositionBudget> {
        if self.remaining_replays == 0 {
            return None;
        }
        self.remaining_attempts = self.remaining_attempts.checked_sub(1)?;
        Some(ClauseDecompositionBudget {
            remaining_candidate_probes: self.candidate_probes_per_clause,
            remaining_replays: self.replays_per_clause,
        })
    }

    fn charge_replay(&mut self, clause: &mut ClauseDecompositionBudget) -> Option<()> {
        let clause_remaining = clause.remaining_replays.checked_sub(1)?;
        let proof_remaining = self.remaining_replays.checked_sub(1)?;
        clause.remaining_replays = clause_remaining;
        self.remaining_replays = proof_remaining;
        Some(())
    }
}

impl ClauseDecompositionBudget {
    fn charge_candidate_probe(&mut self) -> Option<()> {
        self.remaining_candidate_probes = self.remaining_candidate_probes.checked_sub(1)?;
        Some(())
    }
}

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
    budget: &mut CombinedDecompositionBudget,
) -> Option<(TheoryLemmaKind, Vec<TermId>, Vec<TermId>, FarkasAnnotation)> {
    let mut clause_budget = budget.begin_clause()?;
    if clause.len() > MAX_DECOMPOSITION_CLAUSE_LITERALS {
        return None;
    }
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
                clause_budget.charge_candidate_probe()?;
                if let Some(result) = try_congruence_decomposition(
                    terms,
                    clause,
                    &eq_by_pair,
                    candidate_lhs,
                    candidate_rhs,
                    budget,
                    &mut clause_budget,
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
    budget: &mut CombinedDecompositionBudget,
    clause_budget: &mut ClauseDecompositionBudget,
) -> Option<(TheoryLemmaKind, Vec<TermId>, Vec<TermId>, FarkasAnnotation)> {
    if candidate_lhs == candidate_rhs {
        return None;
    }
    let (lhs_sym, lhs_args) = bounded_candidate_application(terms, candidate_lhs)?;
    let (rhs_sym, rhs_args) = bounded_candidate_application(terms, candidate_rhs)?;
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

    // Reserve both replay envelopes before synthesizing terms or constructing
    // the temporary solver. A declined reservation leaves the proof untouched.
    budget.charge_replay(clause_budget)?;

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

fn bounded_candidate_application(terms: &TermStore, term: TermId) -> Option<(&Symbol, &[TermId])> {
    let TermData::App(symbol, arguments) = terms.get(term) else {
        return None;
    };
    if arguments.is_empty()
        || arguments.len() > MAX_CANDIDATE_APPLICATION_ARITY
        || symbol.name().len() > MAX_CANDIDATE_SYMBOL_NAME_BYTES
        || matches!(symbol, Symbol::Indexed(_, indices) if indices.len() > MAX_CANDIDATE_SYMBOL_INDICES)
    {
        return None;
    }
    Some((symbol, arguments))
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
#[path = "decompose/tests.rs"]
mod tests;

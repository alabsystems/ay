// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Resolution and RUP verification engine.
//!
//! Implements propositional resolution checking and reverse-unit-propagation
//! (RUP) for DRUP proof steps in Alethe proofs.

#[path = "resolution_exact.rs"]
mod exact;
#[path = "resolution_parity.rs"]
mod parity;

// #8529/#8857: Use deterministic hash collections for reproducible proof output.
use ay_core::kani_compat::{
    det_hash_set_with_capacity, DetHashMap as HashMap, DetHashSet as HashSet,
};
use ay_core::{AletheRule, Constant, ProofId, TermData, TermId, TermStore};

use super::ProofCheckError;
use parity::{chain_resolve_candidates, clause_as_set, resolves_to};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct SignedLiteral {
    pub(crate) atom: TermId,
    pub(crate) positive: bool,
}

impl SignedLiteral {
    pub(crate) fn negated(self) -> Self {
        Self {
            atom: self.atom,
            positive: !self.positive,
        }
    }
}

fn decode_literal(terms: &TermStore, literal: TermId) -> SignedLiteral {
    let mut atom = literal;
    let mut positive = true;
    while let TermData::Not(inner) = terms.get(atom) {
        atom = *inner;
        positive = !positive;
    }
    SignedLiteral { atom, positive }
}

pub(crate) fn is_valid_binary_resolution(
    terms: &TermStore,
    clause1: &[TermId],
    clause2: &[TermId],
    conclusion: &[TermId],
    pivot: Option<TermId>,
) -> bool {
    let clause1_set = clause_as_set(terms, clause1);
    let clause2_set = clause_as_set(terms, clause2);
    let conclusion_set = clause_as_set(terms, conclusion);

    if let Some(pivot_term) = pivot {
        let pivot_lit = decode_literal(terms, pivot_term);
        return resolves_to(&clause1_set, &clause2_set, pivot_lit, &conclusion_set)
            || resolves_to(
                &clause1_set,
                &clause2_set,
                pivot_lit.negated(),
                &conclusion_set,
            );
    }

    clause1_set
        .iter()
        .any(|pivot| resolves_to(&clause1_set, &clause2_set, *pivot, &conclusion_set))
        || clause2_set
            .iter()
            .any(|pivot| resolves_to(&clause2_set, &clause1_set, *pivot, &conclusion_set))
}

pub(crate) fn is_valid_rup_step(
    terms: &TermStore,
    clause: &[TermId],
    prior_clauses: &[Option<Vec<TermId>>],
) -> bool {
    let mut assignments: HashMap<TermId, bool> = HashMap::default();

    // RUP checks unsat(F ∧ ¬clause): assign each literal in clause to false.
    for &literal in clause {
        let negated = decode_literal(terms, literal).negated();
        if !assign_literal(&mut assignments, negated) {
            return true;
        }
    }

    // Upper bound on BCP iterations: each pass assigns at least one new atom
    // when `changed` is set. The total distinct atoms across all clauses plus
    // the negated target clause is the hard ceiling.
    let max_iterations: usize = {
        let atom_count = prior_clauses
            .iter()
            .filter_map(Option::as_deref)
            .flat_map(|c| c.iter().map(|&lit| decode_literal(terms, lit).atom))
            .chain(clause.iter().map(|&lit| decode_literal(terms, lit).atom))
            .collect::<HashSet<_>>()
            .len();
        atom_count + 1
    };
    let mut iterations: usize = 0;

    loop {
        iterations += 1;
        debug_assert!(
            iterations <= max_iterations,
            "BUG: RUP propagation exceeded atom count bound ({iterations} > {max_iterations})"
        );
        if iterations > max_iterations {
            return false;
        }
        let mut changed = false;

        for clause in prior_clauses.iter().filter_map(Option::as_deref) {
            let mut unit_literal: Option<SignedLiteral> = None;
            let mut clause_satisfied = false;
            let mut multiple_unassigned = false;

            for &literal in clause {
                let signed = decode_literal(terms, literal);
                match assignments.get(&signed.atom) {
                    Some(value) if *value == signed.positive => {
                        clause_satisfied = true;
                        break;
                    }
                    Some(_) => {}
                    None => {
                        if unit_literal.is_some() {
                            multiple_unassigned = true;
                        } else {
                            unit_literal = Some(signed);
                        }
                    }
                }
            }

            if clause_satisfied {
                continue;
            }

            match (unit_literal, multiple_unassigned) {
                (None, _) => return true,
                (Some(_), true) => continue,
                (Some(unit), false) => {
                    if !assign_literal(&mut assignments, unit) {
                        return true;
                    }
                    changed = true;
                }
            }
        }

        if !changed {
            return false;
        }
    }
}

fn assign_literal(assignments: &mut HashMap<TermId, bool>, literal: SignedLiteral) -> bool {
    match assignments.get(&literal.atom) {
        Some(existing) => *existing == literal.positive,
        None => {
            assignments.insert(literal.atom, literal.positive);
            true
        }
    }
}

/// `resolution` / `th_resolution` of any arity. A non-empty Alethe `:args`
/// list selects the pivot-directed form; otherwise binary resolution infers a
/// pivot and larger arities use the bounded chain search.
pub(crate) fn validate_resolution_rule(
    terms: &TermStore,
    step_id: ProofId,
    rule: &AletheRule,
    clause: &[TermId],
    premise_clauses: &[&[TermId]],
    args: &[TermId],
) -> Result<(), ProofCheckError> {
    if !args.is_empty() {
        return validate_pivot_directed_resolution_rule(
            terms,
            step_id,
            rule,
            clause,
            premise_clauses,
            args,
        );
    }

    if premise_clauses.len() != 2 {
        return validate_chain_resolution_rule(terms, step_id, rule, clause, premise_clauses);
    }

    if !is_valid_binary_resolution(terms, premise_clauses[0], premise_clauses[1], clause, None) {
        return Err(ProofCheckError::InvalidResolution {
            step: step_id,
            rule: rule.name().to_string(),
        });
    }

    Ok(())
}

/// Alethe's argument-directed resolution form. Each link contributes exactly
/// `(pivot, polarity)`: `true` means the pivot occurs in the accumulator and
/// its negation occurs in the next premise; `false` means the reverse.
fn validate_pivot_directed_resolution_rule(
    terms: &TermStore,
    step_id: ProofId,
    rule: &AletheRule,
    clause: &[TermId],
    premise_clauses: &[&[TermId]],
    args: &[TermId],
) -> Result<(), ProofCheckError> {
    let invalid = || ProofCheckError::InvalidResolution {
        step: step_id,
        rule: rule.name().to_string(),
    };
    if premise_clauses.len() < 2
        || args.len() != premise_clauses.len().saturating_sub(1).saturating_mul(2)
    {
        return Err(invalid());
    }

    let mut accumulator =
        exact::clause_as_unique_set(terms, premise_clauses[0]).ok_or_else(&invalid)?;
    for (next, annotation) in premise_clauses[1..].iter().zip(args.chunks_exact(2)) {
        let polarity = match terms.get(annotation[1]) {
            TermData::Const(Constant::Bool(value)) => *value,
            _ => return Err(invalid()),
        };
        let pivot = exact::decode_literal(terms, annotation[0]);
        let negated_pivot = pivot.with_outer_not().ok_or_else(&invalid)?;
        let (current_pivot, next_pivot) = if polarity {
            (pivot, negated_pivot)
        } else {
            (negated_pivot, pivot)
        };
        let next = exact::clause_as_unique_set(terms, next).ok_or_else(&invalid)?;
        accumulator = exact::resolve_clause(&accumulator, &next, current_pivot, next_pivot)
            .ok_or_else(&invalid)?;
    }

    let conclusion = exact::clause_as_unique_set(terms, clause).ok_or_else(&invalid)?;
    if accumulator == conclusion {
        Ok(())
    } else {
        Err(invalid())
    }
}

/// N-ary (chain) `resolution` / `th_resolution`.
///
/// #dt-premise-binding — WHY this exists. Alethe's `resolution` and
/// `th_resolution` are N-ARY: one step may list any number of premises,
/// resolved left-to-right. AY's checker used to reject every arity but 2,
/// which forced emitters to spell a chain out as one BINARY step per premise —
/// and each such step must print its whole remaining clause, so the document
/// grows TRIANGULARLY.
///
/// Measured on `QF_DT/20210312-Bouvier/vlsat3_b14.smt2` (2,986 premises): the
/// binary chain rendered a **105.6 MB** `.alethe` (5,973 lines, 105.5 MB of
/// which was resolution-step text; line lengths decayed 75,252 → 61,678 →
/// 36,896 → … → 83 chars). That blows the default 64 MiB emission work budget,
/// so the shipped artefact was **no proof at all**. The identical refutation as
/// ONE n-ary step is 193,103 bytes — 547x smaller — and carcara 1.1.0 checks it
/// in 0.01 s. Teaching the checker the n-ary form is what lets the emitter use it:
/// `executor/proof.rs` re-derives the empty clause from scratch whenever this
/// checker rejects a proof, which would otherwise re-materialise the triangle.
///
/// SEMANTICS — deliberately STRICTER than carcara. The accumulator starts at
/// the first premise; every later premise must contribute exactly one
/// complementary literal pair, and the accumulator loses the pivot. One
/// deliberate deviation from carcara 1.1.0 is fail-closed:
///
///  * carcara silently ABSORBS premises once the accumulator is empty
///    (verified: `(cl (not P1)) , P1 , P2 ⊢ (cl)` checks there, though the true
///    resolvent is `{P2}`). Here a premise that does not resolve is an error.
///
/// Literals are normalized only by leading-`not` parity. This matches
/// Carcara's argument-free RUP fallback. A De Morgan equivalent such as
/// `(and a b)` versus `(or (not a) (not b))` remains a distinct atom and is not
/// a resolution pivot.
pub(crate) fn validate_chain_resolution_rule(
    terms: &TermStore,
    step_id: ProofId,
    rule: &AletheRule,
    clause: &[TermId],
    premise_clauses: &[&[TermId]],
) -> Result<(), ProofCheckError> {
    // Fewer than two premises is not a chain, it is a malformed step. Keep the
    // original arity error so the fail-closed posture (and its message) stands.
    if premise_clauses.len() < 2 {
        return Err(ProofCheckError::UnsupportedResolutionArity {
            step: step_id,
            rule: rule.name().to_string(),
            premise_count: premise_clauses.len(),
        });
    }

    let invalid = || ProofCheckError::InvalidResolution {
        step: step_id,
        rule: rule.name().to_string(),
    };

    // The finite-enum certificate is a complete positive equality graph
    // followed by one negative unit for every edge. Validate that common
    // unit-tail shape as a deterministic set subtraction. Besides avoiding the
    // generic ambiguity search, this avoids rebuilding the shrinking
    // accumulator once per edge (quadratic work on large direct cliques).
    // Any all-unit-tail chain is decided here; malformed instances do not fall
    // through to a more permissive interpretation.
    if premise_clauses[1..]
        .iter()
        .all(|premise| premise.len() == 1)
    {
        let mut accumulator = det_hash_set_with_capacity(premise_clauses[0].len());
        for &literal in premise_clauses[0] {
            accumulator.insert(decode_literal(terms, literal));
        }
        for premise in &premise_clauses[1..] {
            let unit = decode_literal(terms, premise[0]);
            if !accumulator.remove(&unit.negated()) {
                return Err(invalid());
            }
        }
        let mut target = det_hash_set_with_capacity(clause.len());
        for &literal in clause {
            target.insert(decode_literal(terms, literal));
        }
        if accumulator == target {
            return Ok(());
        }
        return Err(invalid());
    }

    let target = clause_as_set(terms, clause);

    // BOUNDED SEARCH over the ambiguous links, not a unique-pair demand.
    //
    // A link with two complementary pairs has two legitimate resolvents, and
    // this used to reject rather than pick one. Nothing needs picking: the fold
    // is CHECKED against the clause the step declares, so a branch is accepted
    // only when it arrives there.
    //
    // Sound for the same reason binary resolution is — a resolvent is implied by
    // its premises under ANY pivot choice, so a chain that ends at the declared
    // clause witnesses that the declared clause follows. The pivot is a search
    // detail; the entailment does not depend on it. Existence is still required
    // (a link that resolves on nothing is still an error), so this only relaxes
    // UNIQUENESS.
    //
    // This is the argument-FREE fallback. AY's n-ary `th_resolution` emitter
    // currently omits pivots, so ambiguous links must be searched rather than
    // guessed; annotated proofs take the directed path above instead.
    //
    // Cost of the old behaviour, measured: `pushscope_repro` computes a correct
    // `unsat`, certification rejects `step t110 has invalid th_resolution
    // derivation`, and the verdict publishes as `unknown` — a caught-and-
    // discarded refutation.
    //
    // The budget keeps the unambiguous case linear (one candidate per link, so
    // the stack never grows) while bounding the branching blow-up. Exhausting it
    // REJECTS, so the fail-closed posture is preserved.
    let mut budget: usize = premise_clauses
        .len()
        .saturating_mul(CHAIN_BRANCH_BUDGET_PER_LINK)
        .saturating_add(CHAIN_BRANCH_BUDGET_BASE);

    let mut stack: Vec<(usize, Vec<SignedLiteral>)> =
        vec![(1, clause_as_set(terms, premise_clauses[0]))];
    while let Some((idx, acc)) = stack.pop() {
        if idx == premise_clauses.len() {
            if acc == target {
                return Ok(());
            }
            continue;
        }
        if budget == 0 {
            break;
        }
        budget -= 1;
        let next = clause_as_set(terms, premise_clauses[idx]);
        for resolvent in chain_resolve_candidates(&acc, &next, CHAIN_MAX_PAIRS_PER_LINK) {
            stack.push((idx + 1, resolvent));
        }
    }
    Err(invalid())
}

/// Per-link branching allowance, and a flat base so short chains can still
/// explore. Both are pure budget: exceeding them rejects.
const CHAIN_BRANCH_BUDGET_PER_LINK: usize = 4;
const CHAIN_BRANCH_BUDGET_BASE: usize = 256;
/// Most complementary pairs considered at one link. Beyond this the link is too
/// ambiguous to search and the step is rejected.
const CHAIN_MAX_PAIRS_PER_LINK: usize = 8;

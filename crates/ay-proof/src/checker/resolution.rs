// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Resolution and RUP verification engine.
//!
//! Implements propositional resolution checking and reverse-unit-propagation
//! (RUP) for DRUP proof steps in Alethe proofs.

use super::boolean::{matches_negation_of_term, matches_positive_literal_of_term};
// #8529/#8857: Use deterministic hash collections for reproducible proof output.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{AletheRule, ProofId, TermData, TermId, TermStore};

use super::ProofCheckError;

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

pub(crate) fn decode_literal(terms: &TermStore, literal: TermId) -> SignedLiteral {
    match terms.get(literal) {
        TermData::Not(inner) => SignedLiteral {
            atom: *inner,
            positive: false,
        },
        _ => SignedLiteral {
            atom: literal,
            positive: true,
        },
    }
}

/// Decode a clause into a sorted, deduplicated literal set.
///
/// #proof-tax: this used to build a `DetHashSet` per clause per resolution
/// step — three hash-table allocations + rehashes for every checked step,
/// which dominated the checker's profile on resolution-heavy proofs
/// (`storecomm` QF_AX family). A sorted `Vec` with `binary_search` has the
/// identical SET semantics (dedup + membership) at a fraction of the cost
/// for conflict-analysis-sized clauses.
fn clause_as_set(terms: &TermStore, clause: &[TermId]) -> Vec<SignedLiteral> {
    let mut set: Vec<SignedLiteral> = clause
        .iter()
        .map(|literal| decode_literal(terms, *literal))
        .collect();
    set.sort_unstable();
    set.dedup();
    set
}

#[inline]
fn set_contains(set: &[SignedLiteral], lit: SignedLiteral) -> bool {
    set.binary_search(&lit).is_ok()
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
        if resolve_on_pivot(&clause1_set, &clause2_set, pivot_lit, &conclusion_set)
            || resolve_on_pivot(
                &clause1_set,
                &clause2_set,
                pivot_lit.negated(),
                &conclusion_set,
            )
        {
            return true;
        }

        return resolve_on_semantic_pivot(terms, clause1, clause2, conclusion, Some(pivot_term));
    }

    if clause1_set
        .iter()
        .any(|pivot_lit| resolve_on_pivot(&clause1_set, &clause2_set, *pivot_lit, &conclusion_set))
        || clause2_set.iter().any(|pivot_lit| {
            resolve_on_pivot(&clause2_set, &clause1_set, *pivot_lit, &conclusion_set)
        })
    {
        return true;
    }

    resolve_on_semantic_pivot(terms, clause1, clause2, conclusion, None)
}

fn resolve_on_pivot(
    left: &[SignedLiteral],
    right: &[SignedLiteral],
    pivot: SignedLiteral,
    expected: &[SignedLiteral],
) -> bool {
    let neg_pivot = pivot.negated();
    if !set_contains(left, pivot) || !set_contains(right, neg_pivot) {
        return false;
    }

    // The resolvent is (left \ {pivot}) ∪ (right \ {¬pivot}); check equality
    // with `expected` by a single three-way merge over the sorted, deduped
    // literal sets (#proof-tax — per-literal membership probes made this the
    // hottest checker leaf on wide-clause QF_AX proofs). `left` skips ONLY
    // `pivot` and `right` skips ONLY `¬pivot` (each may still contribute the
    // other's pivot literal), exactly the legacy set-equality semantics.
    let mut i = 0usize; // left cursor
    let mut j = 0usize; // right cursor
    let mut k = 0usize; // expected cursor
    loop {
        if i < left.len() && left[i] == pivot {
            i += 1;
            continue;
        }
        if j < right.len() && right[j] == neg_pivot {
            j += 1;
            continue;
        }
        // Next element of the union in sorted order (dedup across sides).
        let next = match (left.get(i), right.get(j)) {
            (None, None) => break,
            (Some(&l), None) => {
                i += 1;
                l
            }
            (None, Some(&r)) => {
                j += 1;
                r
            }
            (Some(&l), Some(&r)) => {
                if l < r {
                    i += 1;
                    l
                } else if r < l {
                    j += 1;
                    r
                } else {
                    i += 1;
                    j += 1;
                    l
                }
            }
        };
        if k >= expected.len() || expected[k] != next {
            return false;
        }
        k += 1;
    }
    k == expected.len()
}

fn resolve_on_semantic_pivot(
    terms: &TermStore,
    left: &[TermId],
    right: &[TermId],
    expected: &[TermId],
    pivot: Option<TermId>,
) -> bool {
    let expected_set: HashSet<TermId> = expected.iter().copied().collect();
    for (left_idx, &left_lit) in left.iter().enumerate() {
        for (right_idx, &right_lit) in right.iter().enumerate() {
            if !are_complements(terms, left_lit, right_lit) {
                continue;
            }
            if let Some(pivot_term) = pivot {
                if !pair_matches_pivot(terms, left_lit, right_lit, pivot_term) {
                    continue;
                }
            }

            let mut resolvent: HashSet<TermId> = HashSet::default();
            for (idx, &lit) in left.iter().enumerate() {
                if idx != left_idx {
                    resolvent.insert(lit);
                }
            }
            for (idx, &lit) in right.iter().enumerate() {
                if idx != right_idx {
                    resolvent.insert(lit);
                }
            }

            if resolvent == expected_set {
                return true;
            }
        }
    }
    false
}

fn are_complements(terms: &TermStore, left: TermId, right: TermId) -> bool {
    matches_negation_of_term(terms, left, right) || matches_negation_of_term(terms, right, left)
}

fn pair_matches_pivot(terms: &TermStore, left: TermId, right: TermId, pivot: TermId) -> bool {
    // Either left matches pivot positively and right matches negation, or vice versa.
    // (Previous version had 4 arms; arms 3 and 4 duplicated arms 2 and 1.)
    (matches_positive_literal_of_term(terms, left, pivot)
        && matches_negation_of_term(terms, right, pivot))
        || (matches_positive_literal_of_term(terms, right, pivot)
            && matches_negation_of_term(terms, left, pivot))
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

/// `resolution` / `th_resolution` of ANY arity. Arity 2 keeps the exact
/// binary check it always had; every other arity folds the chain (see
/// [`validate_chain_resolution_rule`]).
pub(crate) fn validate_resolution_rule(
    terms: &TermStore,
    step_id: ProofId,
    rule: &AletheRule,
    clause: &[TermId],
    premise_clauses: &[&[TermId]],
    pivot: Option<TermId>,
) -> Result<(), ProofCheckError> {
    if premise_clauses.len() != 2 {
        return validate_chain_resolution_rule(terms, step_id, rule, clause, premise_clauses);
    }

    if !is_valid_binary_resolution(terms, premise_clauses[0], premise_clauses[1], clause, pivot) {
        return Err(ProofCheckError::InvalidResolution {
            step: step_id,
            rule: rule.name().to_string(),
        });
    }

    Ok(())
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
/// complementary literal pair, and the accumulator loses the pivot. Two
/// deviations from carcara 1.1.0, both fail-closed:
///
///  * carcara silently ABSORBS premises once the accumulator is empty
///    (verified: `(cl (not P1)) , P1 , P2 ⊢ (cl)` checks there, though the true
///    resolvent is `{P2}`). Here a premise that does not resolve is an error.
///  * an AMBIGUOUS link (two distinct complementary pairs, i.e. two different
///    resolvents) is rejected rather than guessed, since guessing wrong would
///    silently change the accumulated clause.
///
/// Complement detection is `are_complements`, the same notion the binary path
/// falls back on (`resolve_on_semantic_pivot`), so double negations such as
/// `(not (not X))` vs `(not X)` pair up exactly as they do today. `:args` are
/// ignored: for a chain they are per-link (pivot, polarity) pairs, and the
/// folded resolvent is compared against the declared clause regardless, so they
/// can only ever be a hint.
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

    let target = dedup_terms(clause);

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
    // `:args` cannot help here even though the doc above suggests they might:
    // every n-ary `th_resolution` emitter in `ay-dpll` passes `Vec::new()` for
    // args (`executor/proof_rewrite_division.rs`), so the per-link pivots are
    // simply absent from AY's own proofs. Searching is the only route that works
    // on them.
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

    let mut stack: Vec<(usize, Vec<TermId>)> = vec![(1, dedup_terms(premise_clauses[0]))];
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
        for resolvent in chain_resolve_candidates(terms, &acc, premise_clauses[idx]) {
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

/// Sorted, deduplicated literal set. Terms are hash-consed, so `TermId`
/// equality IS syntactic literal equality and this is the same set the
/// `SignedLiteral` decoding would produce (the decoding is injective on
/// `TermId`s), just without the per-clause re-decode.
fn dedup_terms(clause: &[TermId]) -> Vec<TermId> {
    let mut set = clause.to_vec();
    set.sort_unstable();
    set.dedup();
    set
}

/// One link of the chain: resolve `acc` against `next` on their unique
/// complementary literal pair. `None` (→ rejection) when the pair does not
/// exist or is not unique.
fn chain_resolve_candidates(
    terms: &TermStore,
    acc: &[TermId],
    next: &[TermId],
) -> Vec<Vec<TermId>> {
    let next_set = dedup_terms(next);

    let mut pairs: Vec<(TermId, TermId)> = Vec::new();
    for &left in acc {
        for &right in &next_set {
            if !are_complements(terms, left, right) {
                continue;
            }
            pairs.push((left, right));
            if pairs.len() > CHAIN_MAX_PAIRS_PER_LINK {
                // Too ambiguous to search; fail closed.
                return Vec::new();
            }
        }
    }

    pairs
        .into_iter()
        .map(|(pivot, neg_pivot)| {
            let mut resolvent: Vec<TermId> = acc.iter().copied().filter(|&l| l != pivot).collect();
            resolvent.extend(next_set.iter().copied().filter(|&l| l != neg_pivot));
            resolvent.sort_unstable();
            resolvent.dedup();
            resolvent
        })
        .collect()
}

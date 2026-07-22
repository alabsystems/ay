// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! McMillan/Pudlak recursive proof traversal for Craig interpolation.
//!
//! Given a resolution proof of A ∧ B → ⊥, this module traverses the proof
//! bottom-up to compute a Craig interpolant I such that:
//! - A ⊨ I
//! - I ∧ B is UNSAT
//! - I mentions only variables shared between A and B
//!
//! # Algorithms
//!
//! Three labeled interpolation systems (D'Silva et al., VMCAI 2010) are
//! supported. Each system fixes the label of shared-atom literal occurrences
//! (A-only atoms are always `a`, B-only atoms always `b`), and the leaf and
//! pivot rules both follow that labeling:
//!
//! | system    | shared label | A-leaf (unit, shared) | B-leaf (unit, shared) | shared pivot          |
//! |-----------|--------------|-----------------------|-----------------------|-----------------------|
//! | McMillan  | b            | the literal           | true                  | I₁ ∧ I₂               |
//! | Pudlak    | ab           | false                 | true                  | (I₁ ∨ p) ∧ (I₂ ∨ ¬p)  |
//! | McMillan' | a            | false                 | ¬literal              | I₁ ∨ I₂               |
//!
//! (#rank-4 increment 1 fixed the McMillan/McMillan' shared-pivot rules,
//! which previously used the OR/AND pairing of the *other* system while
//! keeping McMillan-style leaves — an inconsistent labeling that produced
//! non-interpolants on shared-pivot resolutions.)
//!
//! # References
//!
//! - McMillan, "Interpolation and SAT-based Model Checking", CAV 2003.
//! - Pudlák, "Lower bounds for resolution and cutting plane proofs", JSL 1997.
//! - D'Silva, Kroening, Purandare, Weissenbacher, "Interpolant Strength",
//!   VMCAI 2010 (labeled interpolation systems).
//! - OpenSMT `src/proof/InterpolationContext.cc` (MIT, Martin Blicha).

use std::sync::Arc;

use super::*;

/// Algorithm for combining partial interpolants at shared-variable pivots.
///
/// All three algorithms agree on A-local and B-local pivots:
/// - A-local pivot: I = I₁ ∨ I₂
/// - B-local pivot: I = I₁ ∧ I₂
///
/// They differ only on shared (AB) pivots.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum TraversalAlgorithm {
    /// McMillan (2003): labels shared occurrences `b` — A-leaves contribute
    /// their shared literals, shared pivots combine with AND.
    /// Produces strong interpolants (close to A).
    McMillan,
    /// McMillan' (dual): labels shared occurrences `a` — B-leaves contribute
    /// their negated shared literals, shared pivots combine with OR.
    /// Produces weak interpolants (close to B).
    McMillanPrime,
    /// Pudlak (1997): labels shared occurrences `ab` — leaves are
    /// false (A) / true (B), shared pivots combine as
    /// I = (I₁ ∨ p) ∧ (I₂ ∨ ¬p).
    Pudlak,
}

/// Traverse a resolution proof bottom-up to compute a Craig interpolant.
///
/// The proof steps must be in topological order (each step's premises appear
/// before the step itself). This is guaranteed by `Proof::add_step()`.
///
/// At leaf nodes:
/// - **Assume** (input assertions): system-dependent leaf rule (see
///   `interpolate_assume` and the module docs table).
/// - **TheoryLemma**: delegates to `combine_a_constraints()` which extracts an
///   interpolant from Farkas coefficients annotating the theory conflict.
///   (This is the McMillan-style A-projection theory leaf; wiring per-system
///   theory leaves is deferred to the Farkas increment.)
///
/// At inner nodes:
/// - **Resolution**: combines sub-interpolants based on pivot coloring.
///
/// Returns `None` if the proof is empty or if any required theory lemma
/// interpolation fails.
/// REQUIRES: `proof` is non-empty (checked: returns None)
/// REQUIRES: `a_atoms` and `b_atoms` are disjoint or overlapping sets of atom TermIds
/// ENSURES: returned interpolant (if Some) mentions only variables in `shared_vars`
pub(crate) fn traverse_proof(
    proof: &Proof,
    terms: &TermStore,
    a_lits: &FxHashSet<SignedLit>,
    a_atoms: &FxHashSet<TermId>,
    b_atoms: &FxHashSet<TermId>,
    atom_to_expr: &FxHashMap<TermId, ChcExpr>,
    shared_vars: &FxHashSet<String>,
    algorithm: TraversalAlgorithm,
) -> Option<ChcExpr> {
    if proof.is_empty() {
        return None;
    }

    // Mark all proof nodes with A/B dependency.
    // Previously discarded as `_marks` in extract_interpolant_from_proof;
    // now used to classify pivots and assumptions.
    let marks = mark_proof_nodes(proof, terms, a_atoms, b_atoms);
    debug_assert_eq!(
        marks.len(),
        proof.len(),
        "BUG: mark_proof_nodes returned {} marks for {} proof steps",
        marks.len(),
        proof.len()
    );

    // Partial interpolants indexed by step position (same as ProofId).
    let mut partial: Vec<Option<ChcExpr>> = vec![None; proof.len()];

    for (idx, step) in proof.steps.iter().enumerate() {
        let interp = match step {
            ProofStep::Assume(lit) => interpolate_assume(
                *lit,
                terms,
                a_lits,
                atom_to_expr,
                shared_vars,
                marks[idx],
                algorithm,
            ),
            ProofStep::TheoryLemma { .. } => {
                // Delegate to existing Farkas-based leaf interpolation.
                combine_a_constraints(
                    proof,
                    terms,
                    ProofId(idx as u32),
                    a_lits,
                    atom_to_expr,
                    shared_vars,
                )
            }
            ProofStep::Resolution {
                pivot,
                clause1,
                clause2,
                ..
            } => {
                let i1 = partial.get(clause1.0 as usize).and_then(Clone::clone);
                let i2 = partial.get(clause2.0 as usize).and_then(Clone::clone);
                interpolate_resolution(
                    *pivot,
                    terms,
                    i1,
                    i2,
                    a_atoms,
                    b_atoms,
                    atom_to_expr,
                    algorithm,
                )
            }
            ProofStep::Step { premises, .. } => {
                // Generic Alethe step: combine premise interpolants conjunctively.
                combine_premise_interpolants(&partial, premises)
            }
            ProofStep::Anchor { end_step, .. } => {
                partial.get(end_step.0 as usize).and_then(Clone::clone)
            }
            // Unknown ProofStep variant; no interpolant (#6091).
            _ => None,
        };
        // Apply lightweight constant folding at each step to prevent exponential
        // tree growth during traversal. Full simplification runs at the end.
        partial[idx] = interp.map(simplify_partial);
    }

    debug_assert_eq!(
        partial.len(),
        proof.len(),
        "BUG: partial interpolant vec length {} != proof length {}",
        partial.len(),
        proof.len()
    );

    // The last step's interpolant is the final result.
    // ENSURES: if returned, the interpolant only mentions shared variables
    let result = partial
        .last()
        .and_then(Clone::clone)
        .map(|i| i.simplify_constants());

    if cfg!(debug_assertions) {
        if let Some(ref interp) = result {
            debug_assert!(
                vars_all_shared(interp, shared_vars),
                "BUG: traverse_proof produced interpolant with non-shared vars: {interp}",
            );
        }
    }

    result
}

/// Compute partial interpolant for an Assume (input assertion) leaf.
///
/// Labeled-interpolation-system leaf rules (see module docs):
///   I(A-clause) = disjunction of b-labeled literals
///   I(B-clause) = conjunction of negated a-labeled literals
///
/// For a unit assumption the label of the single literal occurrence decides:
/// - A-only atom (always labeled `a`): I = `false` in all three systems.
/// - B-only atom (always labeled `b`): I = `true` in all three systems.
/// - Shared atom: clause membership (does A assert this literal?) plus the
///   system's shared label decide:
///   - McMillan (shared → b): A-clause → the literal, B-clause → `true`
///   - Pudlak (shared → ab): A-clause → `false`, B-clause → `true`
///   - McMillan' (shared → a): A-clause → `false`, B-clause → ¬literal
pub(super) fn interpolate_assume(
    lit: TermId,
    terms: &TermStore,
    a_lits: &FxHashSet<SignedLit>,
    atom_to_expr: &FxHashMap<TermId, ChcExpr>,
    shared_vars: &FxHashSet<String>,
    mark: DependencyMark,
    algorithm: TraversalAlgorithm,
) -> Option<ChcExpr> {
    let atom = atom_of_literal(terms, lit);
    let is_negated = matches!(terms.get(lit), TermData::Not(_));

    match mark {
        DependencyMark::A => {
            // A-clause whose literal has an A-only atom: labeled `a` in every
            // system, so the b-restriction is empty: I = false.
            Some(ChcExpr::Bool(false))
        }
        DependencyMark::B => {
            // B-clause whose literal has a B-only atom: labeled `b` in every
            // system, so the a-restriction is empty: I = true.
            Some(ChcExpr::Bool(true))
        }
        DependencyMark::AB => {
            // `a_lits` records the A-side literal assignments as
            // (atom, asserted_value); asserting `lit` means the atom is
            // assigned `!is_negated`.
            let asserted_in_a = a_lits.contains(&(atom, !is_negated));
            match (algorithm, asserted_in_a) {
                (TraversalAlgorithm::McMillan, true) => {
                    // A-clause, shared literal is b-labeled: I = the literal.
                    // No sound constant fallback exists here (the invariant
                    // needs A ⊨ I for a unit A-leaf), so fail honestly when
                    // the literal cannot be expressed over shared variables.
                    match lit_as_chc_expr(atom, is_negated, atom_to_expr) {
                        Some(e) if vars_all_shared(&e, shared_vars) => Some(e),
                        _ => None,
                    }
                }
                (TraversalAlgorithm::McMillanPrime, false) => {
                    // B-clause, shared literal is a-labeled: I = ¬literal.
                    // Dually, the invariant needs B ∧ I ⊨ ⊥, so fail honestly
                    // when the literal cannot be expressed.
                    match lit_as_chc_expr(atom, is_negated, atom_to_expr) {
                        Some(e) if vars_all_shared(&e, shared_vars) => Some(ChcExpr::not(e)),
                        _ => None,
                    }
                }
                // Pudlak A/B leaves, McMillan B-leaf: constants.
                (TraversalAlgorithm::Pudlak | TraversalAlgorithm::McMillanPrime, true) => {
                    Some(ChcExpr::Bool(false))
                }
                (TraversalAlgorithm::Pudlak | TraversalAlgorithm::McMillan, false) => {
                    Some(ChcExpr::Bool(true))
                }
            }
        }
        DependencyMark::None => {
            // Unknown origin — shouldn't occur in a well-formed proof.
            // Conservative: treat as B (return true, don't constrain).
            iuc_trace!(
                "traverse_proof: Assume with unknown atom origin (atom={:?})",
                atom
            );
            Some(ChcExpr::Bool(true))
        }
    }
}

/// Convert an atom + polarity to a `ChcExpr`.
fn lit_as_chc_expr(
    atom: TermId,
    is_negated: bool,
    atom_to_expr: &FxHashMap<TermId, ChcExpr>,
) -> Option<ChcExpr> {
    atom_to_expr.get(&atom).map(|expr| {
        if is_negated {
            ChcExpr::not(expr.clone())
        } else {
            expr.clone()
        }
    })
}

/// Compute partial interpolant at a Resolution node.
///
/// The pivot determines how sub-interpolants I₁ and I₂ are combined:
/// - A-local pivot: I₁ ∨ I₂ (the resolution eliminates an A-local fact)
/// - B-local pivot: I₁ ∧ I₂ (the resolution eliminates a B-local fact)
/// - Shared pivot: depends on the algorithm variant
///
/// REQUIRES: `i1` and `i2` are partial interpolants from the two premises
/// REQUIRES: `pivot` is a valid term in `terms`
/// ENSURES: result (if Some) is a Boolean combination of sub-interpolants and pivot expressions
pub(super) fn interpolate_resolution(
    pivot: TermId,
    terms: &TermStore,
    i1: Option<ChcExpr>,
    i2: Option<ChcExpr>,
    a_atoms: &FxHashSet<TermId>,
    b_atoms: &FxHashSet<TermId>,
    atom_to_expr: &FxHashMap<TermId, ChcExpr>,
    algorithm: TraversalAlgorithm,
) -> Option<ChcExpr> {
    let i1 = i1?;
    let i2 = i2?;

    let pivot_atom = atom_of_literal(terms, pivot);
    let pivot_in_a = a_atoms.contains(&pivot_atom);
    let pivot_in_b = b_atoms.contains(&pivot_atom);

    match (pivot_in_a, pivot_in_b) {
        (true, false) => {
            // A-local pivot: I = I₁ ∨ I₂
            Some(ChcExpr::or(i1, i2))
        }
        (false, true) => {
            // B-local pivot: I = I₁ ∧ I₂
            Some(ChcExpr::and(i1, i2))
        }
        (true, true) => {
            // Shared (AB) pivot: the rule must match the system's shared
            // label (#rank-4 increment 1; see module docs):
            //   McMillan  (shared → b)  → I₁ ∧ I₂
            //   McMillan' (shared → a)  → I₁ ∨ I₂
            //   Pudlak    (shared → ab) → (I₁ ∨ p) ∧ (I₂ ∨ ¬p)
            match algorithm {
                TraversalAlgorithm::McMillan => Some(ChcExpr::and(i1, i2)),
                TraversalAlgorithm::McMillanPrime => Some(ChcExpr::or(i1, i2)),
                TraversalAlgorithm::Pudlak => {
                    // I = (I₁ ∨ p) ∧ (I₂ ∨ ¬p)
                    let pivot_negated = matches!(terms.get(pivot), TermData::Not(_));
                    if let Some(p_expr) = atom_to_expr.get(&pivot_atom) {
                        let p = if pivot_negated {
                            ChcExpr::not(p_expr.clone())
                        } else {
                            p_expr.clone()
                        };
                        let not_p = ChcExpr::not(p.clone());
                        let left = ChcExpr::or(i1, p);
                        let right = ChcExpr::or(i2, not_p);
                        Some(ChcExpr::and(left, right))
                    } else {
                        // Can't express the pivot as a ChcExpr. An ab-labeled
                        // pivot has no sound constant combination, so fail
                        // honestly instead of silently mixing systems.
                        iuc_trace!(
                            "traverse_proof: Pudlak shared pivot not expressible (atom {:?} not in atom_to_expr)",
                            pivot_atom
                        );
                        None
                    }
                }
            }
        }
        (false, false) => {
            // Unknown pivot origin — treat as A-local (conservative).
            iuc_trace!(
                "traverse_proof: Resolution pivot with unknown atom origin ({:?})",
                pivot_atom
            );
            Some(ChcExpr::or(i1, i2))
        }
    }
}

/// Combine premise interpolants conjunctively for generic Alethe proof steps.
fn combine_premise_interpolants(
    partial: &[Option<ChcExpr>],
    premises: &[ProofId],
) -> Option<ChcExpr> {
    let sub_interps: Vec<ChcExpr> = premises
        .iter()
        .filter_map(|p| partial.get(p.0 as usize).and_then(Clone::clone))
        .collect();
    if sub_interps.is_empty() {
        Some(ChcExpr::Bool(true))
    } else {
        Some(ChcExpr::and_all(sub_interps))
    }
}

/// Lightweight constant folding for partial interpolants during traversal.
///
/// Applies absorbing-element and identity-element simplification for AND/OR/NOT
/// without recursing into subexpressions. This prevents exponential tree growth
/// when many resolution steps chain together.
///
/// Full simplification (`simplify_constants()`) runs on the final result.
pub(super) fn simplify_partial(expr: ChcExpr) -> ChcExpr {
    match &expr {
        ChcExpr::Op(ChcOp::Or, args) => {
            // true ∨ X = true (absorbing element)
            if args.iter().any(|a| matches!(**a, ChcExpr::Bool(true))) {
                return ChcExpr::Bool(true);
            }
            // Remove false from OR (identity element)
            let filtered: Vec<Arc<ChcExpr>> = args
                .iter()
                .filter(|a| !matches!(***a, ChcExpr::Bool(false)))
                .cloned()
                .collect();
            match filtered.len() {
                0 => ChcExpr::Bool(false),
                1 => (*filtered[0]).clone(),
                _ if filtered.len() == args.len() => expr,
                _ => ChcExpr::Op(ChcOp::Or, filtered),
            }
        }
        ChcExpr::Op(ChcOp::And, args) => {
            // false ∧ X = false (absorbing element)
            if args.iter().any(|a| matches!(**a, ChcExpr::Bool(false))) {
                return ChcExpr::Bool(false);
            }
            // Remove true from AND (identity element)
            let filtered: Vec<Arc<ChcExpr>> = args
                .iter()
                .filter(|a| !matches!(***a, ChcExpr::Bool(true)))
                .cloned()
                .collect();
            match filtered.len() {
                0 => ChcExpr::Bool(true),
                1 => (*filtered[0]).clone(),
                _ if filtered.len() == args.len() => expr,
                _ => ChcExpr::Op(ChcOp::And, filtered),
            }
        }
        ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => match &*args[0] {
            ChcExpr::Bool(true) => ChcExpr::Bool(false),
            ChcExpr::Bool(false) => ChcExpr::Bool(true),
            _ => expr,
        },
        _ => expr,
    }
}

#[cfg(test)]
#[path = "proof_traversal_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "proof_traversal_tree_tests.rs"]
mod tree_tests;

#[cfg(test)]
#[path = "proof_traversal_craig_tests.rs"]
mod craig_tests;

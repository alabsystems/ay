// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Standard Farkas extraction and Craig interpolation.

use super::*;

enum StandardFarkasCandidate {
    Interpolant(ChcExpr),
    NeedsDecomposition,
    Reject,
}

/// REQUIRES: `constraints.len() == weights.len()`
/// REQUIRES: all weights are non-negative
fn try_standard_farkas_candidate(
    constraints: &[LinearConstraint],
    weights: &[Rational64],
    shared_vars: &FxHashSet<String>,
) -> StandardFarkasCandidate {
    debug_assert_eq!(
        constraints.len(),
        weights.len(),
        "BUG: try_standard_farkas_candidate called with mismatched lengths ({} vs {})",
        constraints.len(),
        weights.len()
    );
    debug_assert!(
        weights.iter().all(|w| !w.is_negative()),
        "BUG: try_standard_farkas_candidate called with negative weight"
    );
    let Some((combined_coeffs, combined_bound, combined_strict)) =
        weighted_sum_linear_constraints(constraints, weights)
    else {
        return StandardFarkasCandidate::Reject;
    };

    if combined_coeffs.is_empty() {
        return StandardFarkasCandidate::Reject;
    }

    let has_non_shared = combined_coeffs.keys().any(|v| !shared_vars.contains(v));
    if has_non_shared {
        return StandardFarkasCandidate::NeedsDecomposition;
    }

    let Some(expr) = build_linear_inequality(&combined_coeffs, combined_bound, combined_strict)
    else {
        return StandardFarkasCandidate::Reject;
    };

    if matches!(expr, ChcExpr::Bool(true | false)) {
        StandardFarkasCandidate::Reject
    } else {
        StandardFarkasCandidate::Interpolant(expr)
    }
}

/// REQUIRES: `lemma` is a valid ProofId indexing a TheoryLemma step in `proof`
/// REQUIRES: Farkas coefficients have same length as theory lemma clause
/// ENSURES: returned expression (if Some) mentions only variables in `shared_vars`
pub(super) fn combine_a_constraints(
    proof: &Proof,
    terms: &TermStore,
    lemma: ProofId,
    a_lits: &FxHashSet<SignedLit>,
    atom_to_expr: &FxHashMap<TermId, ChcExpr>,
    shared_vars: &FxHashSet<String>,
) -> Option<ChcExpr> {
    debug_assert!(
        (lemma.0 as usize) < proof.len(),
        "BUG: combine_a_constraints lemma index {} out of bounds (proof len {})",
        lemma.0,
        proof.len()
    );
    let ProofStep::TheoryLemma { clause, farkas, .. } = proof.get_step(lemma)? else {
        return None;
    };
    let FarkasAnnotation { coefficients } = farkas.as_ref()?;
    if coefficients.len() != clause.len() {
        return None;
    }

    struct Contrib {
        linear: LinearConstraint,
        weight: Rational64,
        flippable: bool,
    }

    // Collect A-side constraints that appear in the Farkas certificate.
    //
    // Equalities are represented as two bounds (<= and >=) internally; the conflict often
    // includes the same equality term multiple times. To avoid losing direction information
    // (parse_linear_constraint picks one direction for `=`), we treat each equality literal as
    // *flippable* and try both directions (`a <= b` vs `a >= b`) when combining.
    let mut fixed: Vec<Contrib> = Vec::new();
    let mut flippable: Vec<Contrib> = Vec::new();

    for (&lit_term, &coef_raw) in clause.iter().zip(coefficients.iter()) {
        let weight = rational64_abs(coef_raw);
        if weight == Rational64::from_integer(0) {
            continue;
        }

        let atom = atom_of_literal(terms, lit_term);
        let assignment_value = matches!(terms.get(lit_term), TermData::Not(_));
        if !a_lits.contains(&(atom, assignment_value)) {
            continue;
        }

        let Some(atom_expr) = atom_to_expr.get(&atom).cloned() else {
            continue;
        };
        let assignment_expr = if assignment_value {
            atom_expr
        } else {
            ChcExpr::not(atom_expr)
        };

        let Some(lin) = parse_linear_constraint(&assignment_expr) else {
            continue;
        };

        let contrib = Contrib {
            linear: strengthen_strict_lia_constraint(lin),
            weight,
            flippable: is_equality_constraint(&assignment_expr),
        };
        if contrib.flippable {
            flippable.push(contrib);
        } else {
            fixed.push(contrib);
        }
    }

    if fixed.is_empty() && flippable.is_empty() {
        iuc_trace!("combine_a_constraints: no A-side literals in Farkas conflict");
        return None;
    }

    let fixed_constraints: Vec<LinearConstraint> = fixed.iter().map(|c| c.linear.clone()).collect();
    let fixed_weights: Vec<Rational64> = fixed.iter().map(|c| c.weight).collect();

    let run_candidate =
        |constraints: &[LinearConstraint], weights: &[Rational64]| -> Option<ChcExpr> {
            assert_eq!(
                constraints.len(),
                weights.len(),
                "constraint/weight length mismatch in combine_a_constraints"
            );
            match try_standard_farkas_candidate(constraints, weights, shared_vars) {
                StandardFarkasCandidate::Interpolant(expr) => Some(expr),
                StandardFarkasCandidate::NeedsDecomposition => {
                    decomposed_farkas_interpolant(constraints, weights, shared_vars)
                }
                StandardFarkasCandidate::Reject => None,
            }
        };

    // If there are no equalities, use the standard weighted combination and
    // fall back to decomposed Farkas when A-local vars remain.
    if flippable.is_empty() {
        if let Some(expr) = run_candidate(&fixed_constraints, &fixed_weights) {
            return Some(expr);
        }
        if let Some((coeffs, _, _)) =
            weighted_sum_linear_constraints(&fixed_constraints, &fixed_weights)
        {
            let non_shared: Vec<&String> = coeffs
                .keys()
                .filter(|v| !shared_vars.contains(*v))
                .collect();
            if !non_shared.is_empty() {
                iuc_trace!(
                    "combine_a_constraints: rejected - non-shared vars {:?} in candidate (shared={:?})",
                    non_shared,
                    shared_vars.iter().collect::<Vec<_>>()
                );
            }
        }
        return None;
    }

    // Equalities may need direction selection (<= vs >=) to eliminate non-shared vars.
    //
    // Try both directions per equality occurrence (bounded search); if the conflict contains a
    // large number of equalities, fall back to a cheap alternating-direction heuristic.
    //
    // #2956 Finding 2: Pre-compute both orientations of each flippable constraint
    // outside the loop, and reuse a single buffer instead of cloning fixed_constraints
    // on every iteration. This reduces per-iteration cost from O(F + N*HashMap_clone)
    // to O(N) index copies.
    const MAX_FLIPPABLES: usize = 12;

    // Pre-compute both orientations to avoid cloning inside the loop.
    let flippable_orientations: Vec<[LinearConstraint; 2]> = flippable
        .iter()
        .map(|c| [c.linear.clone(), flip_linear_constraint(&c.linear)])
        .collect();

    if flippable.len() <= MAX_FLIPPABLES {
        let total = 1usize << flippable.len();
        // Allocate buffer once with full capacity; fixed portion stays, tail is overwritten.
        let fixed_len = fixed_constraints.len();
        let mut constraints = Vec::with_capacity(fixed_len + flippable.len());
        constraints.extend_from_slice(&fixed_constraints);
        let mut weights = Vec::with_capacity(fixed_len + flippable.len());
        weights.extend_from_slice(&fixed_weights);
        // Pad with placeholders for the flippable slots.
        for c in &flippable {
            constraints.push(c.linear.clone());
            weights.push(c.weight);
        }

        for mask in 0..total {
            // Overwrite the flippable tail in-place — no allocation.
            for (idx, _) in flippable.iter().enumerate() {
                let orientation = (mask >> idx) & 1;
                constraints[fixed_len + idx].clone_from(&flippable_orientations[idx][orientation]);
            }
            if let Some(expr) = run_candidate(&constraints, &weights) {
                return Some(expr);
            }
        }
    } else {
        let mut constraints = fixed_constraints.clone();
        let mut weights = fixed_weights.clone();
        for (idx, c) in flippable.iter().enumerate() {
            constraints.push(flippable_orientations[idx][idx % 2].clone());
            weights.push(c.weight);
        }
        if let Some(expr) = run_candidate(&constraints, &weights) {
            return Some(expr);
        }
    }

    // Last resort: ignore equalities entirely.
    let result = run_candidate(&fixed_constraints, &fixed_weights);
    if result.is_none() {
        let non_shared: Vec<String> = if let Some((coeffs, _, _)) =
            weighted_sum_linear_constraints(&fixed_constraints, &fixed_weights)
        {
            coeffs
                .keys()
                .filter(|v| !shared_vars.contains(*v))
                .cloned()
                .collect()
        } else {
            Vec::new()
        };

        iuc_trace!(
            "combine_a_constraints: all {} equality combinations failed, non-shared={:?}",
            if flippable.len() <= MAX_FLIPPABLES {
                1usize << flippable.len()
            } else {
                1
            },
            non_shared
        );
    }
    result
}

/// REQUIRES: `proof` is non-empty for meaningful interpolation
/// ENSURES: returned interpolant (if Some) mentions only variables in `shared_vars`
pub(crate) fn extract_interpolant_from_proof(
    proof: &Proof,
    terms: &TermStore,
    a_lits: &FxHashSet<SignedLit>,
    a_atoms: &FxHashSet<TermId>,
    b_atoms: &FxHashSet<TermId>,
    atom_to_expr: &FxHashMap<TermId, ChcExpr>,
    shared_vars: &FxHashSet<String>,
) -> Option<ChcExpr> {
    // Primary path: McMillan/Pudlak proof traversal.
    // Uses mark_proof_nodes() to classify assumptions and pivots,
    // delegates to combine_a_constraints() for theory lemma leaves.
    // Try McMillan (strong), then McMillan' (weak), then Pudlak (symmetric).
    for algorithm in [
        TraversalAlgorithm::McMillan,
        TraversalAlgorithm::McMillanPrime,
        TraversalAlgorithm::Pudlak,
    ] {
        if let Some(i) = traverse_proof(
            proof,
            terms,
            a_lits,
            a_atoms,
            b_atoms,
            atom_to_expr,
            shared_vars,
            algorithm,
        ) {
            return Some(i);
        }
    }

    // Fallback: iterate over Farkas lemmas individually (legacy path).
    // This handles cases where the traversal fails (e.g., missing atom_to_expr
    // entries for pivot atoms in multi-step proofs).
    let lemmas = collect_farkas_lemmas(proof);
    for lemma in lemmas {
        if let Some(i) =
            combine_a_constraints(proof, terms, lemma, a_lits, atom_to_expr, shared_vars)
        {
            return Some(i);
        }
    }
    None
}

/// Classification of a literal in a Farkas conflict based on variable presence.
///
/// This is a legacy fallback used only when a `FarkasConflict` does not carry
/// per-literal partition origin information (#982). In that mode, we approximate
/// “B-pure” as “mentions only shared variables”.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum LiteralClass {
    APure,
    BPure,
    Mixed,
}

/// Classify a literal based on whether its variables are shared.
///
/// In the absence of origin information, “B-pure” is approximated as “all variables
/// are shared” so that any linear combination also mentions only shared variables.
pub(super) fn classify_literal(expr: &ChcExpr, shared_vars: &FxHashSet<String>) -> LiteralClass {
    let vars = expr.vars();
    if vars.is_empty() {
        // Constants are considered B-pure (shared)
        return LiteralClass::BPure;
    }

    let all_shared = vars.iter().all(|v| shared_vars.contains(&v.name));
    let any_shared = vars.iter().any(|v| shared_vars.contains(&v.name));

    match (all_shared, any_shared) {
        (true, _) => LiteralClass::BPure,      // All vars are shared
        (false, false) => LiteralClass::APure, // No vars are shared
        (false, true) => LiteralClass::Mixed,  // Some but not all shared
    }
}

pub(super) fn vars_all_shared(expr: &ChcExpr, shared_vars: &FxHashSet<String>) -> bool {
    let vars = expr.vars();
    vars.is_empty() || vars.iter().all(|v| shared_vars.contains(&v.name))
}

/// Verify Craig interpolation properties: A ⊨ I and I ∧ B is UNSAT.
///
/// Checks all three Craig conditions:
/// 1. A ⊨ I (A implies the interpolant)
/// 2. I ∧ B is UNSAT (the interpolant contradicts B)
/// 3. I mentions only variables shared between A and B
///
/// REQUIRES: `candidate` is a well-formed ChcExpr
/// ENSURES: returns true only if all three Craig conditions hold
pub(super) fn verify_craig_properties(
    candidate: &ChcExpr,
    a_conj: &ChcExpr,
    b_conj: &ChcExpr,
    shared_vars: &FxHashSet<String>,
    smt: &mut SmtContext,
    label: &str,
) -> bool {
    // Check 0 (Craig condition 3): I uses only shared variables
    if !vars_all_shared(candidate, shared_vars) {
        iuc_trace!(
            "{}: Craig check FAILED - I mentions non-shared variables",
            label
        );
        return false;
    }
    // Check 1: I ∧ B must be UNSAT
    let combined = ChcExpr::and(candidate.clone(), b_conj.clone());
    smt.reset();
    match smt.check_sat(&combined) {
        SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {}
        _ => {
            iuc_trace!("{}: Craig check FAILED - I ∧ B is SAT", label);
            return false;
        }
    }
    // Check 2: A ⊨ I (i.e., A ∧ ¬I is UNSAT)
    smt.reset();
    let implies = ChcExpr::and(a_conj.clone(), ChcExpr::not(candidate.clone()));
    match smt.check_sat(&implies) {
        SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
            iuc_trace!("{}: Craig check PASSED", label);
            true
        }
        other => {
            iuc_trace!(
                "{}: Craig check FAILED - A does not imply I (result={:?}, |A|={}, I={})",
                label,
                match other {
                    SmtResult::Sat(_) => "SAT",
                    SmtResult::Unknown => "Unknown",
                    _ => "Other",
                },
                format!("{a_conj}").len(),
                candidate,
            );
            false
        }
    }
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SMT Farkas history-based interpolation.
//!
//! Computes interpolants from Farkas conflict streams collected during
//! DPLL(T) solving. This is the main entry point for PDR/Spacer-style
//! lemma learning when the background contains Boolean structure.

use super::*;

/// Build A-side and B-side theory atom sets from constraint expressions (#6484 dedup).
///
/// `b_indexed` carries `(original_index, expr)` pairs so that the B-side namespace
/// (`"a{idx}"`) uses the correct index regardless of whether the caller passes the
/// full B set or an IUC-shrunk subset.
///
/// Returns `None` if the conversion budget is exceeded.
fn build_partition_atom_sets(
    smt: &mut SmtContext,
    a_constraints: &[ChcExpr],
    b_indexed: &[(usize, &ChcExpr)],
) -> Option<(FxHashSet<TermId>, FxHashSet<TermId>)> {
    smt.reset_conversion_budget();

    let mut a_atoms: FxHashSet<TermId> = FxHashSet::default();
    let mut a_roots: Vec<TermId> = Vec::with_capacity(a_constraints.len());
    for (idx, a) in a_constraints.iter().enumerate() {
        let namespace = format!("bg{idx}");
        let normalized = SmtContext::preprocess_incremental_assumption(a, &namespace);
        a_roots.push(smt.convert_expr(&normalized));
        if smt.conversion_budget_exceeded() {
            return None;
        }
    }
    collect_theory_atoms(&smt.terms, a_roots, &mut a_atoms);

    let mut b_atoms: FxHashSet<TermId> = FxHashSet::default();
    let mut b_roots: Vec<TermId> = Vec::with_capacity(b_indexed.len());
    for &(idx, b) in b_indexed {
        let namespace = format!("a{idx}");
        let normalized = SmtContext::preprocess_incremental_assumption(b, &namespace);
        b_roots.push(smt.convert_expr(&normalized));
        if smt.conversion_budget_exceeded() {
            return None;
        }
    }
    collect_theory_atoms(&smt.terms, b_roots, &mut b_atoms);

    Some((a_atoms, b_atoms))
}

/// Try all interpolation strategies on a single Farkas conflict (#6484 dedup).
///
/// Returns `Some(interpolant)` if any strategy succeeds, `None` otherwise.
/// The `label_prefix` is prepended to strategy names in Craig-property verification
/// diagnostics (e.g. `""` for the history path, `"precomputed-"` for precomputed).
fn try_farkas_conflict_strategies(
    smt: &mut SmtContext,
    conflict: &FarkasConflict,
    a_atoms_in_a: &FxHashSet<TermId>,
    a_conj: &ChcExpr,
    b_conj: &ChcExpr,
    b_atoms: &FxHashSet<TermId>,
    shared_vars: &FxHashSet<String>,
    check_smt: &mut SmtContext,
    label_prefix: &str,
) -> Option<ChcExpr> {
    if conflict.conflict_terms.len() != conflict.polarities.len() {
        return None;
    }
    if conflict.farkas.coefficients.len() != conflict.conflict_terms.len() {
        return None;
    }

    let mut a_lits: FxHashSet<SignedLit> = FxHashSet::default();
    let mut atom_to_expr: FxHashMap<TermId, ChcExpr> = FxHashMap::default();

    let mut clause: Vec<TermId> = Vec::with_capacity(conflict.conflict_terms.len());
    for (idx, (&atom, &value)) in conflict
        .conflict_terms
        .iter()
        .zip(conflict.polarities.iter())
        .enumerate()
    {
        let clause_lit = if value { smt.terms.mk_not(atom) } else { atom };
        clause.push(clause_lit);

        let in_a_atoms = a_atoms_in_a.contains(&atom);
        let iuc_a_origin = idx < conflict.origins.len()
            && matches!(conflict.origins[idx], Partition::A | Partition::AB);
        if in_a_atoms || iuc_a_origin {
            a_lits.insert((atom, value));
        }

        if let Some(expr) = smt.term_to_chc_expr(atom) {
            atom_to_expr.entry(atom).or_insert(expr);
        }
    }

    if a_lits.is_empty() {
        return None;
    }

    let a_atoms: FxHashSet<TermId> = a_lits.iter().map(|(t, _)| *t).collect();

    // Strategy 1: B-pure combination
    if let Some(candidate) = try_b_pure_combination(
        &conflict.conflict_terms,
        &conflict.origins,
        &conflict.polarities,
        &conflict.farkas.coefficients,
        &atom_to_expr,
        shared_vars,
        a_atoms_in_a,
    ) {
        if verify_craig_properties(
            &candidate,
            a_conj,
            b_conj,
            shared_vars,
            check_smt,
            &format!("{label_prefix}B-pure"),
        ) {
            return Some(candidate);
        }
    }

    // Strategy 1.1: Split-literals partitioning (#6484)
    // Partition B-pure constraints into variable-disjoint groups,
    // compute separate Farkas combinations per group, then conjoin.
    if let Some(candidate) = try_split_literals_combination(
        &conflict.conflict_terms,
        &conflict.origins,
        &conflict.polarities,
        &conflict.farkas.coefficients,
        &atom_to_expr,
        shared_vars,
        a_atoms_in_a,
    ) {
        if verify_craig_properties(
            &candidate,
            a_conj,
            b_conj,
            shared_vars,
            check_smt,
            &format!("{label_prefix}split-lit"),
        ) {
            return Some(candidate);
        }
    }

    // Strategy 1.25: Relaxed B-origin combination
    if let Some(candidate) = try_relaxed_b_origin_combination(
        &conflict.conflict_terms,
        &conflict.origins,
        &conflict.polarities,
        &conflict.farkas.coefficients,
        &atom_to_expr,
        shared_vars,
    ) {
        if verify_craig_properties(
            &candidate,
            a_conj,
            b_conj,
            shared_vars,
            check_smt,
            &format!("{label_prefix}relaxed-B"),
        ) {
            return Some(candidate);
        }
    }

    // Strategy 1.5: Per-clause interpolation
    if let Some(candidate) = try_per_clause_interpolation(
        &conflict.conflict_terms,
        &conflict.origins,
        &conflict.polarities,
        &atom_to_expr,
        shared_vars,
    ) {
        if verify_craig_properties(
            &candidate,
            a_conj,
            b_conj,
            shared_vars,
            check_smt,
            &format!("{label_prefix}per-clause"),
        ) {
            return Some(candidate);
        }
    }

    // Strategy 1.75: A-side Farkas projection
    if let Some(candidate) = try_a_side_farkas_projection(
        &conflict.conflict_terms,
        &conflict.origins,
        &conflict.polarities,
        &conflict.farkas.coefficients,
        &atom_to_expr,
        shared_vars,
        a_atoms_in_a,
    ) {
        if verify_craig_properties(
            &candidate,
            a_conj,
            b_conj,
            shared_vars,
            check_smt,
            &format!("{label_prefix}A-side-farkas-proj"),
        ) {
            return Some(candidate);
        }
    }

    // Strategy 2: A-side proof extraction
    let mut proof = Proof::new();
    proof.add_step(ProofStep::TheoryLemma {
        theory: "LIA".to_string(),
        clause,
        farkas: Some(conflict.farkas.clone()),
        kind: TheoryLemmaKind::LiaGeneric,
        lia: None,
    });
    if let Some(candidate) = extract_interpolant_from_proof(
        &proof,
        &smt.terms,
        &a_lits,
        &a_atoms,
        b_atoms,
        &atom_to_expr,
        shared_vars,
    ) {
        if verify_craig_properties(
            &candidate,
            a_conj,
            b_conj,
            shared_vars,
            check_smt,
            &format!("{label_prefix}A-side"),
        ) {
            return Some(candidate);
        }
    }

    // Strategy 3: MBP projection
    if let Some(projected) = try_mbp_projection(a_conj, shared_vars, check_smt) {
        if verify_craig_properties(
            &projected,
            a_conj,
            b_conj,
            shared_vars,
            check_smt,
            &format!("{label_prefix}MBP-projected"),
        ) {
            return Some(projected);
        }
    }

    None
}

/// Log per-literal origin breakdown for partition debugging (#2450).
///
/// This is the IUC trace logging that was originally inline in
/// `compute_interpolant_from_smt_farkas_history`. Extracted during the
/// #6484 dedup to keep it out of `try_farkas_conflict_strategies` (which
/// is shared with the precomputed path that has no IUC context).
fn trace_conflict_origins(conflict: &FarkasConflict, smt: &mut SmtContext) {
    let mut origin_counts = [0usize; 4]; // A, B, AB, Split
    for origin in &conflict.origins {
        match origin {
            Partition::A => origin_counts[0] += 1,
            Partition::B => origin_counts[1] += 1,
            Partition::AB => origin_counts[2] += 1,
            Partition::Split => origin_counts[3] += 1,
        }
    }
    iuc_trace!(
        "conflict origins: A={}, B={}, AB={}, Split={}",
        origin_counts[0],
        origin_counts[1],
        origin_counts[2],
        origin_counts[3]
    );
    for (idx, ((&atom, &polarity), &origin)) in conflict
        .conflict_terms
        .iter()
        .zip(conflict.polarities.iter())
        .zip(conflict.origins.iter())
        .enumerate()
    {
        let coeff = conflict
            .farkas
            .coefficients
            .get(idx)
            .copied()
            .unwrap_or(Rational64::from_integer(0));
        let expr_str = smt
            .term_to_chc_expr(atom)
            .map_or_else(|| format!("term#{}", atom.0), |e| format!("{e}"));
        iuc_trace!(
            "  lit[{}]: {:?} pol={} coeff={} expr={}",
            idx,
            origin,
            polarity,
            coeff,
            expr_str
        );
    }
}

/// Compute an interpolant from the SMT layer's Farkas conflict stream (IUC-style fallback).
///
/// This is intended for PDR/Spacer-style lemma learning when the background contains
/// Boolean structure (e.g., disjunctions) that `compute_interpolant_from_lia_farkas`
/// cannot directly handle.
///
/// Strategy:
/// - Run `check_sat_with_assumption_conjuncts(A, B)` to get an UNSAT core over B.
/// - Collect arithmetic conflicts annotated with Farkas coefficients encountered during DPLL(T).
/// - For each conflict, model it as a 1-step theory lemma proof and extract an A-side
///   interpolant using `extract_interpolant_from_proof`.
/// - Soundness check: verify `I ∧ core_B` is UNSAT before returning.
pub(crate) fn compute_interpolant_candidate_from_smt_farkas_history(
    smt: &mut SmtContext,
    a_constraints: &[ChcExpr],
    b_constraints: &[ChcExpr],
    shared_vars: &FxHashSet<String>,
    verbose: bool,
) -> Option<InterpolantCandidate> {
    if b_constraints.is_empty() {
        iuc_trace!("compute_interpolant_from_smt_farkas_history: b_constraints empty");
        return None;
    }

    // Log A/B constraint variable names to diagnose naming mismatch
    if iuc_trace_enabled() {
        let a_vars: FxHashSet<String> = a_constraints
            .iter()
            .flat_map(ChcExpr::vars)
            .map(|v| v.name)
            .collect();
        let b_vars: FxHashSet<String> = b_constraints
            .iter()
            .flat_map(ChcExpr::vars)
            .map(|v| v.name)
            .collect();
        iuc_trace!(
            "compute_interpolant_from_smt_farkas_history: A vars={:?}, B vars={:?}",
            a_vars.iter().collect::<Vec<_>>(),
            b_vars.iter().collect::<Vec<_>>()
        );
    }

    // Use IucSolver for accurate A/B partition tracking via proxy literals.
    // This prevents split atoms from polluting the B-partition classification.
    let mut iuc = IucSolver::with_context(std::mem::take(smt));
    let (shrunk_b, farkas_conflicts, iuc_diagnostic, smt_diagnostic): (
        Vec<ChcExpr>,
        Vec<FarkasConflict>,
        (usize, usize, bool),
        Option<UnsatCoreDiagnostics>,
    ) = match iuc.check_sat_with_partitions(a_constraints, b_constraints) {
        IucResult::Unsat {
            core,
            farkas_conflicts,
            diagnostics,
        } => {
            let iuc_core_count = core.len();
            // Extract B-partition expressions from the core
            let b_core: Vec<ChcExpr> = core
                .iter()
                .filter(|(_, p)| *p == Partition::B)
                .map(|(e, _)| e.clone())
                .collect();
            let iuc_b_core_count = b_core.len();
            let used_full_b_fallback = b_core.is_empty();

            let shrunk = if b_core.is_empty() {
                b_constraints.to_vec()
            } else {
                b_core
            };

            let shrink_happened = !shrunk.is_empty() && shrunk.len() < b_constraints.len();
            if verbose && shrink_happened {
                safe_eprintln!(
                    "PDR: IUC fallback shrunk B from {} to {} conjuncts",
                    b_constraints.len(),
                    shrunk.len()
                );
            }

            iuc_trace!(
                "compute_interpolant_from_smt_farkas_history: IUC B-core = {:?}",
                shrunk.iter().map(ToString::to_string).collect::<Vec<_>>()
            );
            (
                shrunk,
                farkas_conflicts,
                (iuc_core_count, iuc_b_core_count, used_full_b_fallback),
                diagnostics,
            )
        }
        IucResult::Sat(model) => {
            iuc_trace!(
                "compute_interpolant_from_smt_farkas_history: IUC returned Sat with {} model bindings",
                model.len()
            );
            // Restore SMT context before returning
            *smt = std::mem::take(iuc.smt_mut());
            return None;
        }
        IucResult::Unknown => {
            // Restore SMT context before returning
            *smt = std::mem::take(iuc.smt_mut());
            return None;
        }
    };
    // Restore SMT context after successful query
    *smt = std::mem::take(iuc.smt_mut());

    iuc_trace!(
        "compute_interpolant_from_smt_farkas_history: {} Farkas conflicts, {} A constraints, {} B constraints, shared_vars={:?}",
        farkas_conflicts.len(),
        a_constraints.len(),
        shrunk_b.len(),
        shared_vars.iter().collect::<Vec<_>>()
    );

    // When we have the UNSAT core (shrunk_b) but no Farkas conflicts, prefer
    // core-derived interpolants first:
    // 1) direct IUC over B-core, 2) A-side equalities, 3) synthetic decomposition.
    //
    // The synthetic decomposed path is useful as a last resort, but it can produce
    // overly specific interpolants from all A-constraints. Prioritizing core-derived
    // candidates keeps interpolation aligned with the UNSAT explanation.
    if farkas_conflicts.is_empty() {
        let (iuc_core_count, iuc_b_core_count, used_full_b_fallback) = iuc_diagnostic;
        trace_zero_farkas_diagnostic(
            a_constraints.len(),
            shrunk_b.len(),
            iuc_core_count,
            iuc_b_core_count,
            used_full_b_fallback,
            smt_diagnostic,
        );
        return try_zero_farkas_interpolant_candidate(
            smt,
            a_constraints,
            &shrunk_b,
            shared_vars,
            false,
        );
    }

    let a_conj = and_slice(a_constraints);
    let b_conj = and_slice(&shrunk_b);

    // Build A/B atom sets. The B-side uses `select_shrunk_b_occurrences` to map
    // indices from the original `b_constraints` to the IUC-shrunk B-core.
    let b_indexed = select_shrunk_b_occurrences(b_constraints, &shrunk_b);
    let (a_atoms_in_a, b_atoms) = build_partition_atom_sets(smt, a_constraints, &b_indexed)?;

    let mut check_smt = SmtContext::new();
    for conflict in farkas_conflicts {
        // #2450: IUC trace logging before delegating to shared strategy cascade
        if iuc_trace_enabled() {
            trace_conflict_origins(&conflict, smt);
        }

        if let Some(interpolant) = try_farkas_conflict_strategies(
            smt,
            &conflict,
            &a_atoms_in_a,
            &a_conj,
            &b_conj,
            &b_atoms,
            shared_vars,
            &mut check_smt,
            "",
        ) {
            return Some(InterpolantCandidate::new(
                interpolant,
                InterpolantKind::LiaFarkas,
                true,
            ));
        }
    }

    iuc_trace!(
        "compute_interpolant_from_smt_farkas_history: exhausted all conflicts, no valid interpolant; trying zero-Farkas fallback chain"
    );

    // When all Farkas conflicts fail to produce a valid interpolant, fall through
    // to the same fallback chain used for zero-Farkas queries. The IUC shrunk B-core
    // is still valid, and FM elimination / LIA Farkas / synthetic decomposition may
    // succeed where per-conflict extraction failed.
    try_zero_farkas_interpolant_candidate(smt, a_constraints, &shrunk_b, shared_vars, true)
}

pub(crate) fn compute_interpolant_from_smt_farkas_history(
    smt: &mut SmtContext,
    a_constraints: &[ChcExpr],
    b_constraints: &[ChcExpr],
    shared_vars: &FxHashSet<String>,
    verbose: bool,
) -> Option<ChcExpr> {
    compute_interpolant_candidate_from_smt_farkas_history(
        smt,
        a_constraints,
        b_constraints,
        shared_vars,
        verbose,
    )
    .map(|candidate| candidate.expr)
}

/// Extract an interpolant from precomputed Farkas conflicts without re-querying SMT (#6484).
///
/// This is the extraction half of `compute_interpolant_from_smt_farkas_history`,
/// factored out so that PDR blocking can reuse it when clause-local Farkas
/// certificates were preserved from the original blocking query.
///
/// `a_constraints` is the A-side (transition) and `b_constraints` is the B-side
/// (bad state). `farkas_conflicts` are the clause-local certificates to process.
pub(crate) fn extract_interpolant_from_precomputed_farkas(
    smt: &mut SmtContext,
    a_constraints: &[ChcExpr],
    b_constraints: &[ChcExpr],
    farkas_conflicts: Vec<FarkasConflict>,
    shared_vars: &FxHashSet<String>,
) -> Option<ChcExpr> {
    if farkas_conflicts.is_empty() {
        return None;
    }

    let a_conj = and_slice(a_constraints);
    let b_conj = and_slice(b_constraints);

    // Build A/B atom sets. The B-side uses plain enumeration (no IUC shrinking).
    let b_indexed: Vec<(usize, &ChcExpr)> = b_constraints.iter().enumerate().collect();
    let (a_atoms_in_a, b_atoms) = build_partition_atom_sets(smt, a_constraints, &b_indexed)?;

    let mut check_smt = SmtContext::new();
    for conflict in farkas_conflicts {
        if let Some(interpolant) = try_farkas_conflict_strategies(
            smt,
            &conflict,
            &a_atoms_in_a,
            &a_conj,
            &b_conj,
            &b_atoms,
            shared_vars,
            &mut check_smt,
            "precomputed-",
        ) {
            return Some(interpolant);
        }
    }

    None
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Zero-Farkas fallback interpolation pipeline.
//!
//! When no Farkas conflicts are available from the DPLL(T) history, these
//! strategies attempt to derive interpolants from the UNSAT core alone:
//! direct IUC, A-side equalities, Fourier-Motzkin elimination, B-side FM
//! projection, LIA Farkas, and synthetic decomposition.

use super::*;

pub(super) fn select_shrunk_b_occurrences<'a>(
    b_constraints: &'a [ChcExpr],
    shrunk_b: &[ChcExpr],
) -> Vec<(usize, &'a ChcExpr)> {
    let mut remaining: FxHashMap<ChcExpr, usize> = FxHashMap::default();
    for expr in shrunk_b {
        *remaining.entry(expr.clone()).or_insert(0) += 1;
    }

    let mut selected: Vec<(usize, &'a ChcExpr)> = Vec::with_capacity(shrunk_b.len());
    for (idx, expr) in b_constraints.iter().enumerate() {
        if let Some(count) = remaining.get_mut(expr) {
            if *count == 0 {
                continue;
            }
            selected.push((idx, expr));
            *count -= 1;
        }
    }
    selected
}

pub(super) fn try_zero_farkas_interpolant_candidate(
    smt: &mut SmtContext,
    a_constraints: &[ChcExpr],
    b_constraints: &[ChcExpr],
    shared_vars: &FxHashSet<String>,
    has_farkas_conflicts: bool,
) -> Option<InterpolantCandidate> {
    bump_zero_farkas(&ZERO_FARKAS_ATTEMPTS);
    // Reusable SmtContext for Craig property validation within this function.
    // Avoids allocating a fresh context per validation call (multiple strategies).
    let mut check_smt = SmtContext::new();
    iuc_trace!(
        "compute_interpolant_from_smt_farkas_history: no Farkas conflicts, trying direct IUC on {} B-core conjuncts",
        b_constraints.len()
    );

    // #5877: For BV-native CHC, keep the full IUC B-core instead of dropping
    // non-shared-by-syntax literals up front. The bad-state core is already a
    // shrunk set of predicate constraints, and Z3 Spacer keeps these raw BV
    // guards/clause literals before later inductive minimization. The Craig
    // property check below remains the soundness gate.
    let use_full_b_core_for_direct_iuc = a_constraints
        .iter()
        .chain(b_constraints.iter())
        .any(|expr| expr.scan_features().has_bv);

    let shared_b: Vec<&ChcExpr> = if use_full_b_core_for_direct_iuc {
        b_constraints.iter().collect()
    } else {
        b_constraints
            .iter()
            .filter(|expr| vars_all_shared(expr, shared_vars))
            .collect()
    };

    if shared_b.is_empty() {
        iuc_trace!(
            "compute_interpolant_from_smt_farkas_history: no shared-var B-core conjuncts (B-core = {:?}); trying fallback paths",
            b_constraints.iter().map(ToString::to_string).collect::<Vec<_>>()
        );
    } else {
        iuc_trace!(
            "compute_interpolant_from_smt_farkas_history: shared B-core = {:?}",
            shared_b.iter().map(ToString::to_string).collect::<Vec<_>>()
        );

        // Build interpolant: NOT(AND(shared_b)) = OR(NOT(b_i))
        let negated: Vec<ChcExpr> = shared_b
            .iter()
            .map(|&expr| {
                let neg = ChcExpr::not(expr.clone())
                    .normalize_negations()
                    .normalize_strict_int_comparisons()
                    .simplify_constants();
                iuc_trace!(
                    "compute_interpolant_from_smt_farkas_history: NOT({}) = {}",
                    expr,
                    neg
                );
                neg
            })
            .filter(|e| !matches!(e, ChcExpr::Bool(true)))
            .collect();

        if negated.is_empty() {
            iuc_trace!(
                "compute_interpolant_from_smt_farkas_history: all negated B-core conjuncts simplified to true; trying fallback paths"
            );
        } else {
            let core_exact =
                shared_b.len() == b_constraints.len() && negated.len() == shared_b.len();
            let candidate = ChcExpr::or_all(negated);
            let candidate_is_shared = vars_all_shared(&candidate, shared_vars);
            iuc_trace!(
                "compute_interpolant_from_smt_farkas_history: direct IUC candidate = {}",
                candidate
            );

            // Fast path: when the filtered shared B-core is exactly the UNSAT core,
            // candidate = ¬(∧B_core) is Craig-valid by construction:
            //   1) A ∧ B_core is UNSAT  =>  A => ¬B_core
            //   2) (¬B_core) ∧ B is UNSAT because B includes B_core
            // Skip extra SMT checks in release builds only when the candidate
            // already satisfies Craig locality syntactically. Full-BV exact
            // cores can keep B-local variables that must fall through to the
            // validated/fallback paths instead of panicking in debug.
            if core_exact && candidate_is_shared {
                let debug_valid = if cfg!(debug_assertions) {
                    let a_conj = and_slice(a_constraints);
                    let b_conj = and_slice(b_constraints);
                    verify_craig_properties(
                        &candidate,
                        &a_conj,
                        &b_conj,
                        shared_vars,
                        &mut check_smt,
                        "compute_interpolant_from_smt_farkas_history[core-exact]",
                    )
                } else {
                    true
                };
                if debug_valid {
                    iuc_trace!(
                        "compute_interpolant_from_smt_farkas_history: direct IUC core-exact fast path SUCCESS"
                    );
                    bump_zero_farkas(&ZERO_FARKAS_DIRECT_IUC_SUCCESSES);
                    bump_zero_farkas(&ZERO_FARKAS_DIRECT_IUC_CORE_EXACT_SUCCESSES);
                    trace_zero_farkas_stats("direct-iuc-core-exact-success");
                    return Some(InterpolantCandidate::new(
                        candidate,
                        InterpolantKind::DirectIucCoreExact,
                        has_farkas_conflicts,
                    ));
                }
                iuc_trace!(
                    "compute_interpolant_from_smt_farkas_history: direct IUC core-exact debug revalidation failed; trying fallback paths"
                );
            } else if core_exact {
                iuc_trace!(
                    "compute_interpolant_from_smt_farkas_history: direct IUC core-exact candidate mentions non-shared vars; trying fallback paths"
                );
            }

            let a_conj = and_slice(a_constraints);
            let b_conj = and_slice(b_constraints);
            if verify_craig_properties(
                &candidate,
                &a_conj,
                &b_conj,
                shared_vars,
                &mut check_smt,
                "compute_interpolant_from_smt_farkas_history",
            ) {
                iuc_trace!("compute_interpolant_from_smt_farkas_history: direct IUC SUCCESS");
                bump_zero_farkas(&ZERO_FARKAS_DIRECT_IUC_SUCCESSES);
                trace_zero_farkas_stats("direct-iuc-success");
                return Some(InterpolantCandidate::new(
                    candidate,
                    InterpolantKind::DirectIucValidated,
                    has_farkas_conflicts,
                ));
            }
            iuc_trace!(
                "compute_interpolant_from_smt_farkas_history: direct IUC FAILED; trying fallback paths"
            );
        }
    }

    // Fix #966: if direct IUC is unavailable or fails, try A-side equalities.
    if let Some(a_eq_interpolant) =
        try_a_side_equality_interpolant(a_constraints, b_constraints, shared_vars, &mut check_smt)
    {
        iuc_trace!(
            "compute_interpolant_from_smt_farkas_history: A-side equality interpolant SUCCESS: {}",
            a_eq_interpolant
        );
        bump_zero_farkas(&ZERO_FARKAS_A_SIDE_EQUALITY_SUCCESSES);
        trace_zero_farkas_stats("a-side-equality-success");
        return Some(InterpolantCandidate::new(
            a_eq_interpolant,
            InterpolantKind::ASideEquality,
            has_farkas_conflicts,
        ));
    }

    // Fourier-Motzkin elimination: project A-constraints onto shared variables
    // by eliminating local variables. Any resulting bound on shared variables
    // that contradicts B is a valid interpolant.
    {
        let a_flat = flatten_constraints(a_constraints);
        let a_vars: FxHashSet<String> = a_flat
            .iter()
            .flat_map(ChcExpr::vars)
            .map(|v| v.name)
            .collect();
        let vars_to_eliminate: FxHashSet<String> = a_vars
            .iter()
            .filter(|v| !shared_vars.contains(*v))
            .cloned()
            .collect();
        if !vars_to_eliminate.is_empty() {
            let vars_to_eliminate_names: FxHashSet<&str> =
                vars_to_eliminate.iter().map(String::as_str).collect();
            iuc_trace!(
                "try_zero_farkas_fm_elimination: {} A-constraints, eliminating {} local vars: {:?}",
                a_flat.len(),
                vars_to_eliminate.len(),
                vars_to_eliminate
            );
            if let Some(fm_candidate) =
                try_fourier_motzkin_elimination(&a_flat, &vars_to_eliminate_names)
            {
                let a_conj = and_slice(a_constraints);
                let b_conj = and_slice(b_constraints);
                if verify_craig_properties(
                    &fm_candidate,
                    &a_conj,
                    &b_conj,
                    shared_vars,
                    &mut check_smt,
                    "try_zero_farkas_fm_elimination",
                ) {
                    iuc_trace!(
                        "compute_interpolant_from_smt_farkas_history: FM elimination SUCCESS: {}",
                        fm_candidate
                    );
                    bump_zero_farkas(&ZERO_FARKAS_FM_ELIMINATION_SUCCESSES);
                    trace_zero_farkas_stats("fm-elimination-success");
                    return Some(InterpolantCandidate::new(
                        fm_candidate,
                        InterpolantKind::FourierMotzkin,
                        has_farkas_conflicts,
                    ));
                }
                iuc_trace!(
                    "compute_interpolant_from_smt_farkas_history: FM elimination candidate {} failed Craig check",
                    fm_candidate
                );
            } else {
                iuc_trace!(
                    "try_zero_farkas_fm_elimination: FM returned None (elimination incomplete or no linear constraints)"
                );
            }
        }
    }

    // Dual FM projection: derive a shared-only summary J from B and return I = ¬J.
    // This helps when B-core has no shared-only conjuncts (so direct IUC is unavailable),
    // but B still implies a shared bound after eliminating B-local variables.
    if let Some(b_side_projection_interpolant) = try_b_side_fm_projection_interpolant(
        a_constraints,
        b_constraints,
        shared_vars,
        &mut check_smt,
    ) {
        iuc_trace!(
            "compute_interpolant_from_smt_farkas_history: B-side FM projection SUCCESS: {}",
            b_side_projection_interpolant
        );
        bump_zero_farkas(&ZERO_FARKAS_B_SIDE_FM_PROJECTION_SUCCESSES);
        trace_zero_farkas_stats("b-side-fm-projection-success");
        return Some(InterpolantCandidate::new(
            b_side_projection_interpolant,
            InterpolantKind::BSideFourierMotzkin,
            has_farkas_conflicts,
        ));
    }

    // Try a proof-derived LIA fallback before synthetic decomposition.
    // This remains certificate-faithful (real Farkas coefficients) and can
    // recover useful interpolants even when assumption-core history is empty.
    bump_zero_farkas(&ZERO_FARKAS_LIA_FARKAS_ATTEMPTS);
    if let Some(lia_interpolant) =
        compute_interpolant_from_lia_farkas(smt, a_constraints, b_constraints, shared_vars)
    {
        iuc_trace!(
            "compute_interpolant_from_smt_farkas_history: LIA Farkas fallback SUCCESS: {}",
            lia_interpolant
        );
        bump_zero_farkas(&ZERO_FARKAS_LIA_FARKAS_SUCCESSES);
        trace_zero_farkas_stats("lia-farkas-success");
        return Some(InterpolantCandidate::new(
            lia_interpolant,
            InterpolantKind::LiaFarkas,
            has_farkas_conflicts,
        ));
    }

    // Heuristic fallback (not certificate-faithful): synthetic decomposed Farkas
    // with uniform weights. This runs only after core-derived paths fail.
    if let Some(synth_interpolant) =
        try_synthetic_decomposed_farkas(a_constraints, b_constraints, shared_vars, &mut check_smt)
    {
        iuc_trace!(
            "compute_interpolant_from_smt_farkas_history: synthetic decomposed Farkas SUCCESS: {}",
            synth_interpolant
        );
        bump_zero_farkas(&ZERO_FARKAS_SYNTHETIC_SUCCESSES);
        trace_zero_farkas_stats("synthetic-success");
        return Some(InterpolantCandidate::new(
            synth_interpolant,
            InterpolantKind::Synthetic,
            has_farkas_conflicts,
        ));
    }

    bump_zero_farkas(&ZERO_FARKAS_FAILURES);
    trace_zero_farkas_stats("all-fallbacks-failed");
    None
}

#[cfg(test)]
pub(super) fn try_zero_farkas_interpolant(
    smt: &mut SmtContext,
    a_constraints: &[ChcExpr],
    b_constraints: &[ChcExpr],
    shared_vars: &FxHashSet<String>,
) -> Option<ChcExpr> {
    try_zero_farkas_interpolant_candidate(smt, a_constraints, b_constraints, shared_vars, false)
        .map(|candidate| candidate.expr)
}

fn try_b_side_fm_projection_interpolant(
    a_constraints: &[ChcExpr],
    b_constraints: &[ChcExpr],
    shared_vars: &FxHashSet<String>,
    check_smt: &mut SmtContext,
) -> Option<ChcExpr> {
    let b_flat = flatten_constraints(b_constraints);
    let b_vars: FxHashSet<String> = b_flat
        .iter()
        .flat_map(ChcExpr::vars)
        .map(|v| v.name)
        .collect();
    let vars_to_eliminate: FxHashSet<String> = b_vars
        .iter()
        .filter(|v| !shared_vars.contains(*v))
        .cloned()
        .collect();

    if vars_to_eliminate.is_empty() {
        return None;
    }
    let vars_to_eliminate_names: FxHashSet<&str> =
        vars_to_eliminate.iter().map(String::as_str).collect();

    iuc_trace!(
        "try_b_side_fm_projection_interpolant: {} B-constraints, eliminating {} local vars: {:?}",
        b_flat.len(),
        vars_to_eliminate.len(),
        vars_to_eliminate
    );

    let projected_b = try_fourier_motzkin_elimination(&b_flat, &vars_to_eliminate_names)?;
    if matches!(projected_b, ChcExpr::Bool(true)) {
        iuc_trace!("try_b_side_fm_projection_interpolant: projected B simplified to true");
        return None;
    }

    let candidate = ChcExpr::not(projected_b)
        .normalize_negations()
        .normalize_strict_int_comparisons()
        .simplify_constants();
    iuc_trace!(
        "try_b_side_fm_projection_interpolant: candidate = {}",
        candidate
    );

    let a_conj = and_slice(a_constraints);
    let b_conj = and_slice(b_constraints);
    if verify_craig_properties(
        &candidate,
        &a_conj,
        &b_conj,
        shared_vars,
        check_smt,
        "try_b_side_fm_projection_interpolant",
    ) {
        Some(candidate)
    } else {
        None
    }
}

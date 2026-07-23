// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared helper macros for eager and eager-persistent split-loop arms.
//!
//! Extracted from per-arm files (#6680 Packet 5). These macros own the
//! duplicated split-dispatch and UNSAT proof code that is identical
//! between the eager and eager-persistent execution modes.

/// Dispatches a pending split result (NeedSplit, NeedDisequalitySplit,
/// NeedExpressionSplit) into SAT solver clause additions.
///
/// Must be invoked inside a `'split_loop`-labeled block within a `for` loop.
/// Uses `continue` when a split clause is successfully added, and
/// `break $loop_label` when the split cannot proceed (oscillation, encoding
/// failure, or unrecognized theory result).
///
/// The `fallthrough` block handles the `_` match arm (other TheoryResult
/// variants). In the SAT path this breaks with Unknown; in the Unknown path
/// it is typically empty.
macro_rules! pipeline_incremental_split_eager_dispatch_split {
    ($loop_label:lifetime, $self:ident, $solver:ident,
     tag: $tag:expr, suffix: $suffix:expr,
     $local_term_to_var:ident, $local_var_to_term:ident, $local_next_var:ident, $negations:ident,
     $islp_added_split_clauses:ident, $islp_last_split_values:ident,
     split_result: $split_result:expr,
     drained_diseq_extras: $drained_extras:expr,
     fallthrough: { $($fallthrough:tt)* }
    ) => {
        use ay_core::TheoryResult;
        // Buffer any disequality split extras drained from the theory *before*
        // it was unset. We evaluate the caller's expression before matching so
        // the vec is ready to encode in-line once the primary NeedDisequalitySplit
        // arm fires (#8762).
        let _islp_pending_diseq_extras: Vec<ay_core::DisequalitySplitRequest> = $drained_extras;
        match $split_result {
            TheoryResult::NeedSplit(split) => {
                debug_assert!(
                    !split.value.is_integer(),
                    concat!("BUG: ", $tag, $suffix, " NeedSplit value {} is integral"),
                    split.value
                );

                let oscillation_detected = $crate::executor::theories::solve_harness::check_split_oscillation(
                    &mut $islp_last_split_values, split.variable, &split.value,
                );

                if oscillation_detected {
                    // Unbounded drift detected (#1836): the split variable's value
                    // has moved monotonically in one direction for
                    // UNBOUNDED_THRESHOLD branch-and-bound rounds, i.e. the LP
                    // relaxation keeps walking along an unbounded feasible ray
                    // without landing on an integer point.
                    //
                    // SOUNDNESS FIX: previously this forced the OPPOSITE branch via
                    // a HARD unit clause (`v <= floor` / `v >= ceil`) to "explore
                    // the bounded region". That is UNSOUND when the variable is
                    // genuinely unbounded and an integer witness lies in the pruned
                    // direction: the unit clause permanently removes the witness, so
                    // the residual search reports a spurious propositional UNSAT
                    // which the QF_LIA `accept_unsat_after_splits` opt-in then
                    // accepts as a genuine theory UNSAT — a false proof (e.g.
                    // `51*x + 53*y = 1`, witness x=26, y=-25, was decided `unsat`).
                    //
                    // Branch-and-bound can only soundly close to UNSAT by exhausting
                    // a finite box; under unbounded drift no such box exists, so the
                    // only sound verdict is `Unknown` (matches
                    // `check_split_oscillation`'s documented contract).
                    $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                    $self.last_result = Some(SolveResult::Unknown);
                    break $loop_label Ok(SolveResult::Unknown);
                }

                let (le_atom, ge_atom, _prefer_ceil) =
                    $crate::executor::theories::solve_harness::create_int_split_atoms(
                        &mut $self.ctx.terms, &split,
                    );

                let (le_var, ge_var, _) = $crate::executor::theories::split_incremental::encode_and_add_split_clause(
                    &$self.ctx.terms, $solver,
                    &mut $local_term_to_var, &mut $local_var_to_term,
                    &mut $local_next_var, &mut $negations,
                    le_atom, ge_atom, None,
                    &mut $islp_added_split_clauses,
                );

                if _prefer_ceil == Some(true) {
                    $solver.set_var_phase(ge_var, true);
                    $solver.set_var_phase(le_var, false);
                } else {
                    $solver.set_var_phase(le_var, true);
                    $solver.set_var_phase(ge_var, false);
                }
                continue;
            }
            TheoryResult::NeedDisequalitySplit(split) => {
                use $crate::executor::theories::solve_harness::DisequalitySplitAtoms;
                match $crate::executor::theories::solve_harness::create_disequality_split_atoms(
                    &mut $self.ctx.terms, &split,
                ) {
                    DisequalitySplitAtoms::Skip => { continue; }
                    DisequalitySplitAtoms::IntFractional { le, ge } => {
                        let (le_var, ge_var, _) = $crate::executor::theories::split_incremental::encode_and_add_split_clause(
                            &$self.ctx.terms, $solver,
                            &mut $local_term_to_var, &mut $local_var_to_term,
                            &mut $local_next_var, &mut $negations, le, ge, None,
                            &mut $islp_added_split_clauses,
                        );
                        $crate::executor::theories::split_incremental::bias_split_clause_vars(
                            $solver, le_var, ge_var,
                        );
                    }
                    DisequalitySplitAtoms::IntExact { le, ge, disequality_term, is_distinct } => {
                        let guard = disequality_term.map(|dt| (dt, is_distinct));
                        let (le_var, ge_var, _) = $crate::executor::theories::split_incremental::encode_and_add_split_clause(
                            &$self.ctx.terms, $solver,
                            &mut $local_term_to_var, &mut $local_var_to_term,
                            &mut $local_next_var, &mut $negations, le, ge, guard,
                            &mut $islp_added_split_clauses,
                        );
                        $crate::executor::theories::split_incremental::bias_split_clause_vars(
                            $solver, le_var, ge_var,
                        );
                    }
                    DisequalitySplitAtoms::Real { lt, gt, disequality_term, is_distinct } => {
                        let guard = disequality_term.map(|dt| (dt, is_distinct));
                        let (lt_var, gt_var, _) = $crate::executor::theories::split_incremental::encode_and_add_split_clause(
                            &$self.ctx.terms, $solver,
                            &mut $local_term_to_var, &mut $local_var_to_term,
                            &mut $local_next_var, &mut $negations, lt, gt, guard,
                            &mut $islp_added_split_clauses,
                        );
                        $crate::executor::theories::split_incremental::bias_split_clause_vars(
                            $solver, lt_var, gt_var,
                        );
                    }
                }
                // Encode any additional disequality splits that were batched by the
                // theory but not returned via NeedDisequalitySplit (#8762). This
                // amortizes N disequalities over 1 SAT-resolve round instead of N.
                $crate::executor::theories::split_incremental::encode_pending_diseq_split_extras(
                    _islp_pending_diseq_extras,
                    &mut $self.ctx.terms, $solver,
                    &mut $local_term_to_var, &mut $local_var_to_term,
                    &mut $local_next_var, &mut $negations,
                    &mut $islp_added_split_clauses,
                );
                continue;
            }
            TheoryResult::NeedExpressionSplit(split) => {
                let Some((lt_atom, gt_atom, is_distinct)) =
                    $crate::executor::theories::create_expression_split_atoms(
                        &mut $self.ctx.terms,
                        &mut $self.array_ext_witness_cache,
                        split.disequality_term,
                    )
                else {
                    $self.last_unknown_reason = Some(UnknownReason::ExpressionSplit);
                    $self.last_result = Some(SolveResult::Unknown);
                    break $loop_label Ok(SolveResult::Unknown);
                };

                let guard = Some((split.disequality_term, is_distinct));
                let (lt_var, gt_var, _) = $crate::executor::theories::split_incremental::encode_and_add_split_clause(
                    &$self.ctx.terms, $solver,
                    &mut $local_term_to_var, &mut $local_var_to_term,
                    &mut $local_next_var, &mut $negations,
                    lt_atom, gt_atom, guard,
                    &mut $islp_added_split_clauses,
                );
                $crate::executor::theories::split_incremental::bias_split_clause_vars(
                    $solver, lt_var, gt_var,
                );
                // #array-index-split: ROW-congruence contrapositive companion
                // lemma for same-array select/select disequalities (see the
                // lazy arm / array_select_index_diseq_lemma_atom for why the
                // value split alone cannot converge).
                if let Some(idx_eq) =
                    $crate::executor::theories::array_select_index_diseq_lemma_atom(
                        &mut $self.ctx.terms,
                        split.disequality_term,
                    )
                {
                    let _ = $crate::executor::theories::split_incremental::encode_and_add_negated_atom_lemma(
                        &$self.ctx.terms, $solver,
                        &mut $local_term_to_var, &mut $local_var_to_term,
                        &mut $local_next_var, &mut $negations,
                        idx_eq, (split.disequality_term, is_distinct),
                        &mut $islp_added_split_clauses,
                    );
                }
                continue;
            }
            // #8707 / #8762 / #8765: Batched expression splits. Encode each
            // split exactly as the singleton variant does, deduping by
            // `disequality_term` so the N-O fixpoint cannot re-add clauses.
            TheoryResult::NeedExpressionSplits(splits) => {
                let mut _sld_seen: ay_core::kani_compat::DetHashSet<ay_core::TermId> =
                    ay_core::kani_compat::det_hash_set_new();
                for split in splits {
                    if !_sld_seen.insert(split.disequality_term) {
                        continue;
                    }
                    let Some((lt_atom, gt_atom, is_distinct)) =
                        $crate::executor::theories::create_expression_split_atoms(
                            &mut $self.ctx.terms,
                            &mut $self.array_ext_witness_cache,
                            split.disequality_term,
                        )
                    else {
                        $self.last_unknown_reason = Some(UnknownReason::ExpressionSplit);
                        $self.last_result = Some(SolveResult::Unknown);
                        break $loop_label Ok(SolveResult::Unknown);
                    };

                    let guard = Some((split.disequality_term, is_distinct));
                    let (lt_var, gt_var, _) = $crate::executor::theories::split_incremental::encode_and_add_split_clause(
                        &$self.ctx.terms, $solver,
                        &mut $local_term_to_var, &mut $local_var_to_term,
                        &mut $local_next_var, &mut $negations,
                        lt_atom, gt_atom, guard,
                        &mut $islp_added_split_clauses,
                    );
                    $crate::executor::theories::split_incremental::bias_split_clause_vars(
                        $solver, lt_var, gt_var,
                    );
                    // #array-index-split: ROW-congruence contrapositive companion
                    // lemma for same-array select/select disequalities (see the
                    // lazy arm / array_select_index_diseq_lemma_atom for why the
                    // value split alone cannot converge).
                    if let Some(idx_eq) =
                        $crate::executor::theories::array_select_index_diseq_lemma_atom(
                            &mut $self.ctx.terms,
                            split.disequality_term,
                        )
                    {
                        let _ = $crate::executor::theories::split_incremental::encode_and_add_negated_atom_lemma(
                            &$self.ctx.terms, $solver,
                            &mut $local_term_to_var, &mut $local_var_to_term,
                            &mut $local_next_var, &mut $negations,
                            idx_eq, (split.disequality_term, is_distinct),
                            &mut $islp_added_split_clauses,
                        );
                    }
                }
                continue;
            }
            _ => {
                $($fallthrough)*
            }
        }
    };
}

/// Build the UNSAT proof for an incremental-split eager exit and break the loop.
///
/// Thin shim over [`crate::pipeline_fns::capture_split_unsat_proof`]: the capture
/// half (clone trace, resize/clone local ledgers) was de-macro'd into that
/// function (#6725); this macro survives only to assign the captured data to the
/// private `$self.last_*` fields, run the whole-`&mut self` `build_unsat_proof()`,
/// and `break $loop_label Ok(unsat())` out of the caller's split loop.
macro_rules! pipeline_incremental_split_eager_build_unsat_proof {
    ($loop_label:lifetime, $self:ident, $solver:ident, $state:ident,
     $local_var_to_term:ident, $islp_negations:ident, $proof_enabled:ident,
     $local_clausification_proofs:ident, $local_theory_proofs:ident
    ) => {
        $self.last_model = None;
        if let Some(__islp_cap) = $crate::pipeline_fns::capture_split_unsat_proof(
            $solver,
            $proof_enabled,
            &$local_var_to_term,
            &mut $local_clausification_proofs,
            &mut $local_theory_proofs,
            $islp_negations.as_map(),
        ) {
            $self.last_clause_trace = __islp_cap.clause_trace;
            $self.last_clausification_proofs = Some(__islp_cap.clausification_proofs);
            $self.last_original_clause_theory_proofs = Some(__islp_cap.theory_proofs);
            $self.last_var_to_term = Some(__islp_cap.var_to_term);
            $self.last_negations = Some(__islp_cap.negations);
            $self.build_unsat_proof();
        }
        $self.last_result = Some(SolveResult::unsat());
        break $loop_label Ok(SolveResult::unsat());
    };
}

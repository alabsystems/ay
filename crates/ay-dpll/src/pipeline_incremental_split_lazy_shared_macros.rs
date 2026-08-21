// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared helper macros for lazy and assumption split-loop arms.
//!
//! Extracted from per-arm files (#6680 Packet 2). This macro owns the
//! duplicated theory-result dispatch code that is identical between the
//! lazy and assumption execution modes.

/// Dispatches a theory result (Sat, Unsat, UnsatWithFarkas, NeedSplit,
/// NeedDisequalitySplit, NeedExpressionSplit, NeedLemmas, NeedModelEquality,
/// NeedModelEqualities) inside the lazy/assumption split loop.
///
/// Must be invoked inside a `'split_loop`-labeled block within a `for` loop.
/// The Sat handler and remaining arms (NeedStringLemma, Unknown, catchall)
/// are provided by the caller as token blocks.
///
/// The `$theory` variable is consumed (dropped) by non-Sat arms that need
/// to create split atoms or encode lemmas. The Sat handler block receives
/// `$theory` still alive.
macro_rules! pipeline_incremental_split_lazy_dispatch_theory_result {
    ($loop_label:lifetime, $self:ident, $solver:ident, $state:ident,
     tag: $tag:expr,
     $theory:ident,
     theory_result: $theory_result:expr,
     export_theory: |$export_theory:ident| $export_expr:expr,
     $ltv:ident, $lvt:ident, $lnv:ident,
     $asc:ident, $lsv:ident, $met:ident,
     $lc:ident, $shc:ident, $ds:ident, $tl:ident, $tls:ident,
     $neg:ident, $pe:ident, $lcp:ident, $ltp:ident,
     sat_handler: { $($sat_handler:tt)* },
     remaining_arms: { $($remaining_arms:tt)* }
    ) => {
        match $theory_result {
            ay_core::TheoryResult::Sat => {
                $($sat_handler)*
            }
            ay_core::TheoryResult::Unsat(mut conflict_terms) => {
                // #4666: exact-duplicate literals are a logical identity in a
                // conflict (X ∨ X ≡ X in the learned clause) but structurally
                // fail verification. Dedupe before verifying so well-formed
                // conflicts are learned instead of re-derived.
                $crate::verification::dedup_conflict_literals(&mut conflict_terms);
                $crate::verification::log_conflict_debug_with_terms(
                    &conflict_terms,
                    concat!("incremental ", $tag, " UNSAT"),
                    &$self.ctx.terms,
                );
                if let Err(e) = $crate::verification::verify_theory_conflict(&conflict_terms) {
                    // Structural failure is diagnostic only: the fail-closed
                    // semantic gate below is the authoritative check.
                    tracing::warn!(
                        error = %e,
                        conflict_len = conflict_terms.len(),
                        concat!("BUG(#4666): ", $tag, " conflict structural verification failed; deferring to fail-closed semantic gate")
                    );
                }
                // Semantic conflict verification must stay domain-aware here.
                // Mixed UFLIA/AUFLIA conflicts can legitimately include EUF
                // atoms; re-checking them with a standalone LiaSolver alone
                // turns real combined-theory UNSAT results into false Unknown.
                //
                // Fail-closed: a conflict that cannot be semantically verified
                // must NOT be learned as a global clause. The former #8595
                // "using conflict anyway" arm laundered unverifiable theory
                // conflicts (e.g. LIA conflicts whose parse silently depended
                // on the current Boolean assignment) into learned clauses,
                // producing wrong UNSAT verdicts on satisfiable array/LIA
                // formulas. Verifiable-domain skips inside
                // `verify_conflict_semantic` return Ok, so only genuine
                // verification failures reach this bail.
                if let Err(e) = $crate::verification::verify_conflict_semantic_memoized(
                    &mut $self.conflict_semantic_verify_memo,
                    &conflict_terms,
                    &$self.ctx.terms,
                    &$self.active_support_axioms,
                ) {
                    let _ = $solver.pop();
                    tracing::error!(
                        error = %e,
                        conflict_len = conflict_terms.len(),
                        conflict = ?conflict_terms,
                        concat!("BUG(#6853): ", $tag, " conflict semantic verification failed; returning Unknown instead of learning unverified clause")
                    );
                    $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                    $self.last_result = Some(SolveResult::Unknown);
                    break $loop_label Ok(SolveResult::Unknown);
                }
                // Record structured theory proof (#6725) — mirrors no-split
                // incremental path (pipeline_incremental_macros.rs:248).
                // This shared dispatcher has no pipeline-level registry cache,
                // so the registry data stays scoped to the proof-recording call
                // and remains absent for non-DT problems.
                let _sld_theory_proof = if $pe {
                    dt_conflict_proof!(
                        $self,
                        $neg,
                        &conflict_terms,
                        $crate::theory_inference::dt_funnel_registry_data(&$self.ctx)
                    )
                } else {
                    None
                };
                pipeline_map_incremental_split_conflict_clause!(
                    $self,
                    label: $loop_label,
                    state: $state,
                    solver: $solver,
                    theory: $theory,
                    export_theory: |$export_theory| $export_expr,
                    learned_cuts: $lc,
                    seen_hnf_cuts: $shc,
                    dioph_state: $ds,
                    local_term_to_var: $ltv,
                    conflict_terms: conflict_terms,
                    proof_enabled: $pe,
                    negations: $neg,
                    local_var_to_term: $lvt,
                    local_clausification_proofs: $lcp,
                    local_theory_proofs: $ltp,
                    theory_proof: _sld_theory_proof
                );
            }
            ay_core::TheoryResult::UnsatWithFarkas(mut conflict) => {
                // #4666: dedupe with Farkas coefficient merge-by-sum
                // (λ₁·c + λ₂·c = (λ₁+λ₂)·c) — logical identity, keeps the
                // certificate aligned and verifiable.
                $crate::verification::dedup_conflict_with_farkas(&mut conflict);
                $crate::verification::log_conflict_debug_with_terms(
                    &conflict.literals,
                    concat!("incremental ", $tag, " UnsatWithFarkas"),
                    &$self.ctx.terms,
                );
                let mut _sld_farkas_proof_valid = conflict.farkas.is_some();
                if let Err(e) = $crate::verification::verify_theory_conflict_with_farkas(&conflict) {
                    if e.is_missing_annotation() {
                        _sld_farkas_proof_valid = false;
                        tracing::debug!(
                            conflict_len = conflict.literals.len(),
                            concat!($tag, " Farkas annotation missing; conflict clause is sound, skipping proof cert")
                        );
                    } else {
                        // Certificate downgrade: the Farkas certificate is
                        // unusable, so drop it. The conflict itself is then
                        // re-verified by the fail-closed semantic backstop
                        // below — it is only learned if that verification
                        // succeeds (no more fail-open "use anyway" path).
                        _sld_farkas_proof_valid = false;
                        tracing::warn!(
                            error = %e,
                            conflict_len = conflict.literals.len(),
                            concat!("BUG(#4666): ", $tag, " Farkas verification failed; dropping certificate, deferring to semantic backstop")
                        );
                    }
                }
                // Semantic Farkas verification in ALL builds (adversarial-review
                // followup on #rank-4 increment 2 — this arm previously had NO
                // semantic check at all): a verified certificate semantically
                // proves the conflict.
                let mut _sld_farkas_semantically_verified = false;
                if _sld_farkas_proof_valid {
                    match $crate::verification::verify_theory_conflict_with_farkas_full(
                        &conflict,
                        &$self.ctx.terms,
                    ) {
                        Ok(()) => _sld_farkas_semantically_verified = true,
                        Err(e) => {
                            // Certificate downgrade: semantically invalid
                            // certificate. Drop it and defer to the
                            // fail-closed semantic backstop below, which only
                            // learns the conflict if it verifies.
                            _sld_farkas_proof_valid = false;
                            tracing::warn!(
                                error = %e,
                                conflict_len = conflict.literals.len(),
                                concat!("BUG(#4666): ", $tag, " Farkas semantic verification failed; dropping certificate, deferring to semantic backstop")
                            );
                        }
                    }
                }
                // Release backstop: when the UNSAT verdict is NOT covered by a
                // semantically verified certificate, run the same domain-aware
                // semantic re-check the Unsat arm runs.
                //
                // Fail-closed: if that re-check also fails, the conflict has
                // no verification at all — do not learn it (see the Unsat arm
                // above; the former #8595 "using conflict anyway" arm was a
                // fail-open workaround that laundered unverifiable conflicts
                // into learned clauses).
                if !_sld_farkas_semantically_verified {
                    if let Err(e) = $crate::verification::verify_conflict_semantic_memoized(
                        &mut $self.conflict_semantic_verify_memo,
                        &conflict.literals,
                        &$self.ctx.terms,
                        &$self.active_support_axioms,
                    ) {
                        let _ = $solver.pop();
                        tracing::error!(
                            error = %e,
                            conflict_len = conflict.literals.len(),
                            conflict = ?conflict.literals,
                            concat!("BUG(#6853): ", $tag, " Farkas conflict semantic verification failed; returning Unknown instead of learning unverified clause")
                        );
                        $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                        $self.last_result = Some(SolveResult::Unknown);
                        break $loop_label Ok(SolveResult::Unknown);
                    }
                }
                // Record structured theory proof with Farkas coefficients (#6725)
                // — mirrors no-split incremental path (pipeline_incremental_macros.rs:321-327).
                let _sld_theory_proof = if $pe {
                    if _sld_farkas_proof_valid {
                        dt_farkas_proof!(
                            $self,
                            $neg,
                            &conflict,
                            $crate::theory_inference::dt_funnel_registry_data(&$self.ctx)
                        )
                    } else {
                        dt_conflict_proof!(
                            $self,
                            $neg,
                            &conflict.literals,
                            $crate::theory_inference::dt_funnel_registry_data(&$self.ctx)
                        )
                    }
                } else {
                    None
                };
                pipeline_map_incremental_split_conflict_clause!(
                    $self,
                    label: $loop_label,
                    state: $state,
                    solver: $solver,
                    theory: $theory,
                    export_theory: |$export_theory| $export_expr,
                    learned_cuts: $lc,
                    seen_hnf_cuts: $shc,
                    dioph_state: $ds,
                    local_term_to_var: $ltv,
                    conflict_terms: conflict.literals,
                    proof_enabled: $pe,
                    negations: $neg,
                    local_var_to_term: $lvt,
                    local_clausification_proofs: $lcp,
                    local_theory_proofs: $ltp,
                    theory_proof: _sld_theory_proof
                );
            }
            ay_core::TheoryResult::NeedSplit(split) => {
                let oscillation_detected = $crate::executor::theories::solve_harness::check_split_oscillation(
                    &mut $lsv, split.variable, &split.value,
                );

                if oscillation_detected {
                    // Unbounded drift detected (#1836): the split variable's
                    // value has moved monotonically in one direction for
                    // UNBOUNDED_THRESHOLD branch-and-bound rounds, i.e. the LP
                    // relaxation keeps walking along an unbounded feasible ray
                    // without landing on an integer point.
                    //
                    // SOUNDNESS FIX: previously (#6729) this forced the OPPOSITE
                    // branch by adding a HARD unit clause (`v <= floor`), aiming
                    // to "explore the bounded region of the feasible polyhedron".
                    // That is UNSOUND when the variable is genuinely unbounded and
                    // an integer witness lies in the pruned direction: the unit
                    // clause permanently removes the witness, so the residual
                    // search reports a spurious propositional UNSAT which the
                    // QF_LIA `accept_unsat_after_splits` opt-in then accepts as a
                    // genuine theory UNSAT — a false proof. Concretely
                    // `51*x + 53*y = 1` (witness x=26, y=-25) was decided `unsat`.
                    //
                    // Branch-and-bound can only soundly close to UNSAT by
                    // *exhausting* a finite box; on an unbounded drift no such box
                    // exists, so the only sound verdict is `Unknown`. Phase biasing
                    // toward the bounded region (the legitimate part of #6729's
                    // intent) cannot help here: the near-origin region was already
                    // explored without a witness, which is precisely why the drift
                    // triggered. Bail to Unknown (matches `check_split_oscillation`'s
                    // documented contract).
                    pipeline_export_theory_state!(
                        $theory, $export_theory, $export_expr,
                        $lc, $shc, $ds
                    );
                    drop($theory);
                    $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                    $self.last_result = Some(SolveResult::Unknown);
                    break $loop_label Ok(SolveResult::Unknown);
                }

                pipeline_export_theory_state!(
                    $theory, $export_theory, $export_expr,
                    $lc, $shc, $ds
                );
                drop($theory);

                let (le_atom, ge_atom, _prefer_ceil) =
                    $crate::executor::theories::solve_harness::create_int_split_atoms(
                        &mut $self.ctx.terms, &split,
                    );

                let (le_var, ge_var, _) = $crate::executor::theories::split_incremental::encode_and_add_split_clause(
                    &mut $self.ctx.terms, $solver,
                    &mut $ltv, &mut $lvt,
                    &mut $lnv, &mut $neg,
                    le_atom, ge_atom, None,
                    &mut $asc,
                );

                if _prefer_ceil == Some(true) {
                    $solver.set_var_phase(ge_var, true);
                    $solver.set_var_phase(le_var, false);
                } else {
                    $solver.set_var_phase(le_var, true);
                    $solver.set_var_phase(ge_var, false);
                }
            }
            ay_core::TheoryResult::NeedDisequalitySplit(split) => {
                pipeline_export_theory_state!(
                    $theory, $export_theory, $export_expr,
                    $lc, $shc, $ds
                );
                drop($theory);

                use $crate::executor::theories::solve_harness::DisequalitySplitAtoms;
                match $crate::executor::theories::solve_harness::create_disequality_split_atoms(
                    &mut $self.ctx.terms, &split,
                ) {
                    DisequalitySplitAtoms::Skip => { continue; }
                    DisequalitySplitAtoms::IntFractional { le, ge } => {
                        let (le_var, ge_var, _) = $crate::executor::theories::split_incremental::encode_and_add_split_clause(
                            &mut $self.ctx.terms, $solver,
                            &mut $ltv, &mut $lvt,
                            &mut $lnv, &mut $neg, le, ge, None,
                            &mut $asc,
                        );
                        $crate::executor::theories::split_incremental::bias_split_clause_vars(
                            $solver, le_var, ge_var,
                        );
                    }
                    DisequalitySplitAtoms::IntExact { le, ge, disequality_term, is_distinct } => {
                        let guard = disequality_term.map(|dt| (dt, is_distinct));
                        let (le_var, ge_var, _) = $crate::executor::theories::split_incremental::encode_and_add_split_clause(
                            &mut $self.ctx.terms, $solver,
                            &mut $ltv, &mut $lvt,
                            &mut $lnv, &mut $neg, le, ge, guard,
                            &mut $asc,
                        );
                        $crate::executor::theories::split_incremental::bias_split_clause_vars(
                            $solver, le_var, ge_var,
                        );
                    }
                    DisequalitySplitAtoms::Real { lt, gt, disequality_term, is_distinct } => {
                        let guard = disequality_term.map(|dt| (dt, is_distinct));
                        let (lt_var, gt_var, _) = $crate::executor::theories::split_incremental::encode_and_add_split_clause(
                            &mut $self.ctx.terms, $solver,
                            &mut $ltv, &mut $lvt,
                            &mut $lnv, &mut $neg, lt, gt, guard,
                            &mut $asc,
                        );
                        $crate::executor::theories::split_incremental::bias_split_clause_vars(
                            $solver, lt_var, gt_var,
                        );
                    }
                }
            }
            ay_core::TheoryResult::NeedExpressionSplit(split) => {
                // #stale-expr-split (same design as the #1771 stale
                // model-equality fallback above): if a previous encode round
                // for this disequality term added NOTHING new (split clause,
                // mutex clause, and index lemma all deduplicated), a repeat
                // request is provably unproductive — the SAT solver already
                // searched with every clause this split can contribute.
                // Re-encoding and looping livelocks: an EUF-derived shared
                // disequality whose violated variable pair is disjoint from
                // the split atoms re-requests the identical split every round
                // (observed on false_unsat_array_ite_store_index: 1276
                // identical requests for one term until the 60s budget).
                // Fall through to the Sat handler instead; the fail-closed
                // model-validation gates still decide the final verdict.
                if $met.is_stale_expr_split(split.disequality_term) {
                    tracing::debug!(
                        diseq_term = ?split.disequality_term,
                        "#stale-expr-split: repeat request with nothing new to encode, treating as Sat"
                    );
                    pipeline_export_theory_state!(
                        $theory, $export_theory, $export_expr,
                        $lc, $shc, $ds
                    );
                    $($sat_handler)*
                } else {
                pipeline_export_theory_state!(
                    $theory, $export_theory, $export_expr,
                    $lc, $shc, $ds
                );
                drop($theory);

                let Some((lt_atom, gt_atom, is_distinct)) =
                    $crate::executor::theories::create_expression_split_atoms(
                        &mut $self.ctx.terms,
                        &mut $self.array_ext_witness_cache,
                        split.disequality_term,
                    )
                else {
                    let _ = $solver.pop();
                    $self.last_unknown_reason = Some(UnknownReason::ExpressionSplit);
                    $self.last_result = Some(SolveResult::Unknown);
                    break $loop_label Ok(SolveResult::Unknown);
                };

                let guard = Some((split.disequality_term, is_distinct));
                let (lt_var, gt_var, _sld_xs_split_added) = $crate::executor::theories::split_incremental::encode_and_add_split_clause(
                    &mut $self.ctx.terms, $solver,
                    &mut $ltv, &mut $lvt,
                    &mut $lnv, &mut $neg,
                    lt_atom, gt_atom, guard,
                    &mut $asc,
                );
                $crate::executor::theories::split_incremental::bias_split_clause_vars(
                    $solver, lt_var, gt_var,
                );
                // #array-index-split: same-array select/select disequalities
                // additionally get the ROW-congruence contrapositive
                // `⟨guard⟩ ∨ ¬(= i j)` — the value split alone is LIA-opaque
                // and cannot stop ROW congruence from re-merging the selects
                // (see array_select_index_diseq_lemma_atom).
                let mut _sld_xs_lemma_added = false;
                if let Some(idx_eq) =
                    $crate::executor::theories::array_select_index_diseq_lemma_atom(
                        &mut $self.ctx.terms,
                        split.disequality_term,
                    )
                {
                    _sld_xs_lemma_added = $crate::executor::theories::split_incremental::encode_and_add_negated_atom_lemma(
                        &mut $self.ctx.terms, $solver,
                        &mut $ltv, &mut $lvt,
                        &mut $lnv, &mut $neg,
                        idx_eq, (split.disequality_term, is_distinct),
                        &mut $asc,
                    );
                }
                // #stale-expr-split: nothing was added this round, so the
                // next identical request can add nothing either.
                if !_sld_xs_split_added && !_sld_xs_lemma_added {
                    $met.mark_stale_expr_split(split.disequality_term);
                }
                }
            }
            // #8707 / #8765: Batched expression splits (e.g. LRA buffered the
            // whole pairwise violation set of a `distinct` constraint). Encode
            // each split exactly as the singleton variant does — deduping by
            // `disequality_term` so repeated requests from the N-O fixpoint
            // only add clauses once.
            ay_core::TheoryResult::NeedExpressionSplits(splits) => {
                // #stale-expr-split: same fallback as the singleton arm — when
                // EVERY split in the batch was previously encoded with nothing
                // new added, the whole batch is unproductive; treat as Sat and
                // let the fail-closed model-validation gates decide.
                if splits
                    .iter()
                    .all(|s| $met.is_stale_expr_split(s.disequality_term))
                {
                    tracing::debug!(
                        stale_count = splits.len(),
                        "#stale-expr-split: all batched expression splits stale, treating as Sat"
                    );
                    pipeline_export_theory_state!(
                        $theory, $export_theory, $export_expr,
                        $lc, $shc, $ds
                    );
                    $($sat_handler)*
                } else {
                pipeline_export_theory_state!(
                    $theory, $export_theory, $export_expr,
                    $lc, $shc, $ds
                );
                drop($theory);

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
                        let _ = $solver.pop();
                        $self.last_unknown_reason = Some(UnknownReason::ExpressionSplit);
                        $self.last_result = Some(SolveResult::Unknown);
                        break $loop_label Ok(SolveResult::Unknown);
                    };

                    let guard = Some((split.disequality_term, is_distinct));
                    let (lt_var, gt_var, _sld_xs_split_added) = $crate::executor::theories::split_incremental::encode_and_add_split_clause(
                        &mut $self.ctx.terms, $solver,
                        &mut $ltv, &mut $lvt,
                        &mut $lnv, &mut $neg,
                        lt_atom, gt_atom, guard,
                        &mut $asc,
                    );
                    $crate::executor::theories::split_incremental::bias_split_clause_vars(
                        $solver, lt_var, gt_var,
                    );
                    // #array-index-split: same-array select/select disequalities
                    // additionally get the ROW-congruence contrapositive
                    // `⟨guard⟩ ∨ ¬(= i j)` — the value split alone is LIA-opaque
                    // and cannot stop ROW congruence from re-merging the selects
                    // (see array_select_index_diseq_lemma_atom).
                    let mut _sld_xs_lemma_added = false;
                    if let Some(idx_eq) =
                        $crate::executor::theories::array_select_index_diseq_lemma_atom(
                            &mut $self.ctx.terms,
                            split.disequality_term,
                        )
                    {
                        _sld_xs_lemma_added = $crate::executor::theories::split_incremental::encode_and_add_negated_atom_lemma(
                            &mut $self.ctx.terms, $solver,
                            &mut $ltv, &mut $lvt,
                            &mut $lnv, &mut $neg,
                            idx_eq, (split.disequality_term, is_distinct),
                            &mut $asc,
                        );
                    }
                    // #stale-expr-split: nothing was added for this split, so
                    // the next identical request can add nothing either.
                    if !_sld_xs_split_added && !_sld_xs_lemma_added {
                        $met.mark_stale_expr_split(split.disequality_term);
                    }
                }
                }
            }
            ay_core::TheoryResult::NeedLemmas(lemmas) => {
                pipeline_export_theory_state!(
                    $theory, $export_theory, $export_expr,
                    $lc, $shc, $ds
                );
                drop($theory);

                let _sld_requested_lemmas = lemmas.len();
                let (_sld_new_lemmas, _sld_duplicate_lemmas) =
                    $crate::executor::theories::split_incremental::take_new_theory_lemmas(
                        lemmas,
                        &mut $tls,
                    );
                let mut _sld_original_ids = Vec::with_capacity(_sld_new_lemmas.len());
                for lemma in &_sld_new_lemmas {
                    _sld_original_ids.push($crate::executor::theories::split_incremental::apply_theory_lemma_incremental(
                        &$self.ctx.terms,
                        $solver,
                        &mut $ltv,
                        &mut $lvt,
                        &mut $lnv,
                        &mut $neg,
                        &lemma.clause,
                    ));
                }
                if $pe {
                    $neg.sync_pending(&mut $self.ctx.terms);
                }
                // #trust->0 C3: DT registries, once per batch (proofs-on only).
                let _c3_dt = if $pe {
                    $crate::theory_inference::dt_funnel_registry_data(&$self.ctx)
                } else {
                    None
                };
                for (lemma, _sld_original_id) in
                    _sld_new_lemmas.iter().zip(_sld_original_ids)
                {
                    if $pe {
                        let terms: Vec<ay_core::TermId> = lemma
                            .clause
                            .iter()
                            .map(|lit| {
                                if lit.value {
                                    lit.term
                                } else {
                                    *$neg
                                        .as_map()
                                        .get(&lit.term)
                                        .expect("theory-lemma negation cache should be synced")
                                }
                            })
                            .collect();
                        // #trust->0 C3: funnel classifies + records; adopt its
                        // validator-ordered clause.
                        let (kind, terms) =
                            $crate::theory_inference::record_funnel_classified_lemma(
                                &mut $self.proof_tracker,
                                &$self.ctx.terms,
                                terms,
                                _c3_dt.as_ref(),
                            );
                        if let Some(_sld_original_id) = _sld_original_id {
                            $crate::pipeline_fns::place_original_clause_authority_at_id(
                                &$solver,
                                _sld_original_id,
                                None,
                                Some(ay_core::TheoryLemmaProof {
                                    clause: terms,
                                    kind,
                                    farkas: None,
                                    lia: None,
                                }),
                                &mut $lcp,
                                &mut $ltp,
                            );
                        }
                    }
                    $tl.push(lemma.clone());
                }
                continue;
            }
            ay_core::TheoryResult::NeedModelEquality(eq) => {
                // #1771: If the equality atom is already encoded AND triangle
                // axioms have been added, the SAT/theory loop has done all the
                // coupling it can — treat as Sat.
                //
                // #8748: BUT if the equality atom is encoded (e.g., as part of
                // an asserted `(not (= a b))`) without triangle axioms, the
                // SAT solver's Bool decision on the eq is disconnected from the
                // LRA model.  Forcing "Sat" here can return a model where the
                // LRA has `lhs == rhs` in contradiction to the SAT solver's
                // false assignment on `(= lhs rhs)`, yielding a disequality
                // violation that later trips model validation and downgrades
                // the check to `unknown (incomplete)`. We MUST encode triangle
                // axioms first so the arith/Bool layers agree.
                let _sld_me_eq_atom = $self.ctx.terms.find_eq(eq.lhs, eq.rhs);
                let _sld_me_encoded = _sld_me_eq_atom
                    .is_some_and(|ea| $ltv.contains_key(&ea));
                let _sld_me_triangle_added = _sld_me_eq_atom
                    .is_some_and(|ea| $met.triangle_atoms_mut().contains(&ea));
                let _sld_me_stale = _sld_me_encoded && _sld_me_triangle_added;
                if _sld_me_stale {
                    tracing::debug!(
                        "#1771: stale NeedModelEquality suppressed, treating as Sat"
                    );
                    pipeline_export_theory_state!(
                        $theory, $export_theory, $export_expr,
                        $lc, $shc, $ds
                    );
                    $($sat_handler)*
                } else {
                    pipeline_export_theory_state!(
                        $theory, $export_theory, $export_expr,
                        $lc, $shc, $ds
                    );
                    drop($theory);

                    // #6851: Centralized round budget via ModelEqualityTracker.
                    if $met.increment_round() {
                        let _ = $solver.pop();
                        $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                        $self.last_result = Some(SolveResult::Unknown);
                        break $loop_label Ok(SolveResult::Unknown);
                    }

                    // #8748: Route through the tracked variant so triangle
                    // axioms are added exactly once per eq atom and the next
                    // iteration's stale check correctly detects full coupling.
                    pipeline_encode_model_equality!(
                        $self, $solver, $ltv, $lvt, $lnv, $neg, eq,
                        added_model_eqs: $met.triangle_atoms_mut()
                    );
                }
            }
            ay_core::TheoryResult::NeedModelEqualities(eqs) => {
                // #1771 / #8748: Same logic as single-NeedModelEquality above.
                // All equalities must be encoded AND have their triangle axioms
                // added before treating the batch as stale.
                let _sld_me_all_stale = eqs.iter().all(|eq| {
                    match $self.ctx.terms.find_eq(eq.lhs, eq.rhs) {
                        Some(ea) => {
                            $ltv.contains_key(&ea)
                                && $met.triangle_atoms_mut().contains(&ea)
                        }
                        None => false,
                    }
                });
                if _sld_me_all_stale {
                    tracing::debug!(
                        stale_count = eqs.len(),
                        "#1771: all NeedModelEqualities stale, treating as Sat"
                    );
                    pipeline_export_theory_state!(
                        $theory, $export_theory, $export_expr,
                        $lc, $shc, $ds
                    );
                    $($sat_handler)*
                } else {
                    pipeline_export_theory_state!(
                        $theory, $export_theory, $export_expr,
                        $lc, $shc, $ds
                    );
                    drop($theory);

                    // #6851: Centralized round budget via ModelEqualityTracker.
                    if $met.increment_round() {
                        let _ = $solver.pop();
                        $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                        $self.last_result = Some(SolveResult::Unknown);
                        break $loop_label Ok(SolveResult::Unknown);
                    }

                    // #8748: Encode triangle axioms for any eq atom whose
                    // triangle clauses are not yet present, even if the eq
                    // atom itself was already encoded by some prior step
                    // (e.g., as part of an asserted `(not (= a b))`).
                    for eq in eqs {
                        let _needs_encode = match $self.ctx.terms
                            .find_eq(eq.lhs, eq.rhs)
                        {
                            Some(ea) => {
                                !$ltv.contains_key(&ea)
                                    || !$met.triangle_atoms_mut().contains(&ea)
                            }
                            None => true,
                        };
                        if _needs_encode {
                            pipeline_encode_model_equality!(
                                $self, $solver, $ltv, $lvt, $lnv, $neg, eq,
                                added_model_eqs: $met.triangle_atoms_mut()
                            );
                        }
                    }
                }
            }
            $($remaining_arms)*
        }
    };
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! LIRA and AUFLIRA combined theory solving (mixed Int + Real arithmetic).
//!
//! Non-LIRA theory combinations (UF+LRA, UF+NRA, AUFLIA, AUFLRA, BV+LIA)
//! are in the parent module.

use crate::combined_solvers::{AufLiraSolver, LiraSolver};
use crate::executor::theories::solve_harness::{ProofProblemAssertionProvenance, TheoryModels};
use crate::executor_types::{Result, SolveResult};
use ay_core::term::TermData;
use ay_core::{Sort, TermId};

use super::super::super::Executor;
use super::super::MAX_SPLITS_MIXED;

impl Executor {
    /// Solve using combined LIA + LRA theory with assumptions (QF_LIRA).
    ///
    /// This is the assumption-based version of [`Self::solve_lira`], enabling
    /// split-aware `check-sat-assuming` for mixed Int/Real problems.
    ///
    /// Fixes #1835: `check-sat-assuming` must handle `NeedSplit`/`NeedDisequalitySplit`
    /// for LIRA-family logics instead of returning `unknown`.
    pub(in crate::executor) fn solve_lira_with_assumptions(
        &mut self,
        assertions: &[TermId],
        assumptions: &[TermId],
    ) -> Result<SolveResult> {
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }
        // Preprocess assertions and assumptions through the full LIA normalization
        // family: variable substitution, SOM, ITE lifting, mod/div elimination (#6737).
        let artifacts = self.preprocess_mixed_arith_assumptions(assertions, assumptions);
        let var_subst = artifacts.var_subst;
        let final_assumptions = artifacts.assumptions;
        let proof_provenance = ProofProblemAssertionProvenance::from_sources(
            assertions.to_vec(),
            &artifacts.assertions,
            artifacts.assertion_sources,
        );

        // Preserve original assertions for fill-only equality recovery on SAT.
        let original_assertions: Vec<TermId> = assertions.to_vec();

        let solve_interrupt = self.solve_interrupt.clone();
        let solve_deadline = self.solve_deadline.clone();
        self.with_deferred_postprocessing(artifacts.assertions, proof_provenance, |this| {
            this.configure_sat_search_tuning(100.0, 1.1, 0.01);
            solve_incremental_assume_split_loop_pipeline!(this,
                tag: "LIRA-ASSUME",
                persistent_sat_field: persistent_sat,
                assumptions: &final_assumptions,
                create_theory: LiraSolver::new(&this.ctx.terms),
                extract_models: |theory| {
                    let (mut lia, lra) = theory.extract_models();
                    // Recover substituted Int values and fill-only equalities (#6737)
                    if let Some(model) = lia.as_mut() {
                        super::super::lia::recover_substituted_lia_values(
                            &this.ctx.terms, &var_subst, model,
                        );
                        super::super::lia::recover_lia_equalities_from_assertions(
                            &this.ctx.terms, &original_assertions, model,
                        );
                    }
                    TheoryModels {
                        lra: Some(lra),
                        lia,
                        ..TheoryModels::default()
                    }
                },
                max_splits: MAX_SPLITS_MIXED,
                pre_theory_import: |theory, lc, hc, ds| {
                    theory.import_learned_state(std::mem::take(lc), std::mem::take(hc));
                    theory.import_dioph_state(std::mem::take(ds));
                },
                post_theory_export: |theory| {
                    let (lc, hc) = theory.take_learned_state();
                    let ds = theory.take_dioph_state();
                    (lc, hc, ds)
                },
                pre_iter_check: |_s| {
                    solve_interrupt
                        .as_ref()
                        .is_some_and(|flag| flag.load(std::sync::atomic::Ordering::Relaxed))
                        || solve_deadline.expired()
                }
            )
        })
    }

    /// Solve using combined Arrays + EUF + LIA + LRA theory with assumptions (QF_AUFLIRA).
    ///
    /// Fixes #1835: `check-sat-assuming` must handle integer/disequality splits for AUFLIRA.
    pub(in crate::executor) fn solve_auflira_with_assumptions(
        &mut self,
        assertions: &[TermId],
        assumptions: &[TermId],
    ) -> Result<SolveResult> {
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }
        // Preprocess assertions and assumptions through the full LIA normalization
        // family: variable substitution, SOM, ITE lifting, mod/div elimination (#6737).
        let artifacts = self.preprocess_mixed_arith_assumptions(assertions, assumptions);
        let var_subst = artifacts.var_subst;
        let final_assumptions = artifacts.assumptions;

        // Preserve original assertions for fill-only equality recovery on SAT.
        let original_assertions: Vec<TermId> = assertions.to_vec();

        let assumption_terms: Vec<TermId> = final_assumptions.iter().map(|(t, _)| *t).collect();
        let mut final_assertions = artifacts.assertions;

        // Eager array axioms for AUFLIRA-ASSUME (#4304, #5086, #6282).
        // Keeps eager ROW because LRA index arithmetic disequalities
        // cannot be derived by the lazy ArraySolver alone.
        // Include assumption terms in the reachable set (#6736).
        {
            let axiom_start = self.ctx.assertions.len();
            self.run_array_axiom_full_fixpoint_at_with_roots(axiom_start, &assumption_terms);
            final_assertions.extend(self.ctx.assertions.drain(axiom_start..));
        }
        let proof_provenance = ProofProblemAssertionProvenance::from_sources(
            assertions.to_vec(),
            &final_assertions,
            artifacts.assertion_sources,
        );

        // Use isolated incremental state with the new incremental assumption
        // split-loop macro (#6689 Packet 4). LIA learned state is now preserved
        // across split iterations — an improvement over the legacy path.
        let solve_interrupt = self.solve_interrupt.clone();
        let solve_deadline = self.solve_deadline.clone();
        self.with_deferred_postprocessing(final_assertions, proof_provenance, |this| {
            this.configure_sat_search_tuning(100.0, 1.1, 0.01);
            solve_incremental_assume_split_loop_pipeline!(this,
                tag: "AUFLIRA-ASSUME",
                persistent_sat_field: persistent_sat,
                assumptions: &final_assumptions,
                create_theory: AufLiraSolver::new(&this.ctx.terms),
                extract_models: |theory| {
                    let (euf, arr, mut lia, lra) = theory.extract_all_models();
                    // Recover substituted Int values and fill-only equalities (#6737)
                    if let Some(model) = lia.as_mut() {
                        super::super::lia::recover_substituted_lia_values(
                            &this.ctx.terms, &var_subst, model,
                        );
                        super::super::lia::recover_lia_equalities_from_assertions(
                            &this.ctx.terms, &original_assertions, model,
                        );
                    }
                    TheoryModels {
                        euf: Some(euf),
                        array: Some(arr),
                        lra: Some(lra),
                        lia,
                        ..TheoryModels::default()
                    }
                },
                max_splits: MAX_SPLITS_MIXED,
                pre_theory_import: |theory, lc, hc, ds| {
                    theory.import_learned_state(std::mem::take(lc), std::mem::take(hc));
                    theory.import_dioph_state(std::mem::take(ds));
                },
                post_theory_export: |theory| {
                    let (lc, hc) = theory.take_learned_state();
                    let ds = theory.take_dioph_state();
                    (lc, hc, ds)
                },
                pre_iter_check: |_s| {
                    solve_interrupt
                        .as_ref()
                        .is_some_and(|flag| flag.load(std::sync::atomic::Ordering::Relaxed))
                        || solve_deadline.expired()
                }
            )
        })
    }

    /// Solve using combined LIA + LRA theory (QF_LIRA)
    ///
    /// This handles both integer branch-and-bound splits (NeedSplit) and
    /// disequality splits (NeedDisequalitySplit) for mixed Int+Real problems.
    pub(in crate::executor) fn solve_lira(&mut self) -> Result<SolveResult> {
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }
        // Fail-safe pre-pass for provably-disjoint mixed Int/Real problems
        // (#mixed-int-real; repros/mixed-int-real-combination/). Either returns a
        // model-validated verdict or defers to the unchanged solve below.
        if let Some(result) = self.try_disjoint_int_real_split()? {
            return Ok(result);
        }
        // ROUTE 1 (status quo): mod/div-only preprocessing, exactly the
        // historical plain-LIRA route. Runs FIRST so every input the route
        // already decides keeps its verdict and cost bit-for-bit — the
        // LiraSolver natively decides e.g. `r_i = to_real(n_i)` bridge
        // networks that variable substitution would smear into unsupported
        // multi-`to_real` sum atoms (measured: a 3-var to_real chain is SAT
        // in ~0.01s here and unknown after substitution).
        let (preprocessed_assertions, proof_provenance) =
            self.preprocess_mod_div_assertions_with_proof_provenance(&self.ctx.assertions.clone());

        let solve_interrupt = self.solve_interrupt.clone();
        let solve_deadline = self.solve_deadline.clone();
        let result =
            self.with_deferred_postprocessing(preprocessed_assertions, proof_provenance, |this| {
                this.configure_sat_search_tuning(100.0, 1.1, 0.01);
                solve_incremental_split_loop_pipeline!(this,
                    tag: "LIRA",
                    persistent_sat_field: persistent_sat,
                    create_theory: LiraSolver::new(&this.ctx.terms),
                    extract_models: |theory| {
                        let (lia, lra) = theory.extract_models();
                        TheoryModels {
                            lra: Some(lra),
                            lia,
                            ..TheoryModels::default()
                        }
                    },
                    max_splits: MAX_SPLITS_MIXED,
                    pre_theory_import: |theory, lc, hc, ds| {
                        theory.import_learned_state(std::mem::take(lc), std::mem::take(hc));
                        theory.import_dioph_state(std::mem::take(ds));
                    },
                    post_theory_export: |theory| {
                        let (lc, hc) = theory.take_learned_state();
                        let ds = theory.take_dioph_state();
                        (lc, hc, ds)
                    },
                    // #5462: LIRA stays on lazy path. Cross-sort NeedSplit requires
                    // the N-O fixpoint to run inside the SAT solve (extension check),
                    // but the eager arm's theory recreation loses cross-sort state
                    // between iterations. The extension fix (returning Sat for
                    // NeedSplit) helps but doesn't fully resolve multi-split SAT
                    // problems that depend on cross-sort bound propagation.
                    pre_iter_check: |_s| {
                        solve_interrupt
                            .as_ref()
                            .is_some_and(|flag| flag.load(std::sync::atomic::Ordering::Relaxed))
                            || solve_deadline.expired()
                    }
                )
            })?;
        if !matches!(result, SolveResult::Unknown) {
            return Ok(result);
        }
        // Route 1 could not decide. Do not retry once the deadline/interrupt
        // has fired — the retry would only burn the caller's remaining budget.
        if self.should_abort_theory_loop()
            || self.solve_deadline.expired()
            || self
                .solve_interrupt
                .as_ref()
                .is_some_and(|flag| flag.load(std::sync::atomic::Ordering::Relaxed))
        {
            return Ok(result);
        }
        self.solve_lira_full_preprocess_retry()
    }

    /// ROUTE 2 (fail-closed retry) for [`Self::solve_lira`]: the FULL LIA
    /// normalization family (variable substitution, SOM, ITE lifting, mod/div
    /// elimination) — the same pipeline the assumptions route runs via
    /// `preprocess_mixed_arith_assumptions` and QF_LIA runs directly.
    /// Variable substitution folds definitional bridges like `r = to_real(n)`
    /// into their use sites, where the to_real-integrality constructor
    /// rewrites decide the Int core (g4: `0 < to_real(n) < 1` → `1 ≤ n ∧
    /// n ≤ 0`, formerly unknown on plain check-sat while check-sat-assuming
    /// decided it). Runs ONLY after the status-quo route returned unknown, so
    /// it can only add decisions, never change or slow an existing one; each
    /// route runs under its own isolated incremental state
    /// (`with_deferred_postprocessing` → `with_isolated_incremental_state`),
    /// and every SAT is revalidated at the outer boundary against the
    /// original assertions.
    fn solve_lira_full_preprocess_retry(&mut self) -> Result<SolveResult> {
        let original_assertions: Vec<TermId> = self.ctx.assertions.clone();
        let artifacts = self.preprocess_lia_artifacts();
        let introduced_unconstrained_div_mod = artifacts.introduced_unconstrained_div_mod;
        let var_subst = artifacts.var_subst;
        let proof_provenance = ProofProblemAssertionProvenance::from_sources(
            original_assertions.clone(),
            &artifacts.assertions,
            artifacts.assertion_sources,
        );

        let solve_interrupt = self.solve_interrupt.clone();
        let solve_deadline = self.solve_deadline.clone();
        let result =
            self.with_deferred_postprocessing(artifacts.assertions, proof_provenance, |this| {
                this.configure_sat_search_tuning(100.0, 1.1, 0.01);
                solve_incremental_split_loop_pipeline!(this,
                    tag: "LIRA-FULLPP",
                    persistent_sat_field: persistent_sat,
                    create_theory: LiraSolver::new(&this.ctx.terms),
                    extract_models: |theory| {
                        let (mut lia, lra) = theory.extract_models();
                        // Recover substituted Int values and fill-only equalities
                        // (#6737), mirroring the assumptions route: without this,
                        // SAT models lose the substituted variables and outer
                        // revalidation degrades SAT to unknown (fail-closed, but
                        // needlessly incomplete).
                        if let Some(model) = lia.as_mut() {
                            super::super::lia::recover_substituted_lia_values(
                                &this.ctx.terms, &var_subst, model,
                            );
                            super::super::lia::recover_lia_equalities_from_assertions(
                                &this.ctx.terms, &original_assertions, model,
                            );
                        }
                        TheoryModels {
                            lra: Some(lra),
                            lia,
                            ..TheoryModels::default()
                        }
                    },
                    max_splits: MAX_SPLITS_MIXED,
                    pre_theory_import: |theory, lc, hc, ds| {
                        theory.import_learned_state(std::mem::take(lc), std::mem::take(hc));
                        theory.import_dioph_state(std::mem::take(ds));
                    },
                    post_theory_export: |theory| {
                        let (lc, hc) = theory.take_learned_state();
                        let ds = theory.take_dioph_state();
                        (lc, hc, ds)
                    },
                    // #5462: lazy path — see the status-quo route above.
                    pre_iter_check: |_s| {
                        solve_interrupt
                            .as_ref()
                            .is_some_and(|flag| flag.load(std::sync::atomic::Ordering::Relaxed))
                            || solve_deadline.expired()
                    }
                )
            });
        // #div0: mod/div elimination of a (possibly) zero divisor introduces an
        // UNCONSTRAINED fresh variable the outer model evaluator cannot replay;
        // thread the artifact flag into the validation bypass exactly like
        // QF_LIA (`solve_lia_incremental`) does — satisfiability follows
        // soundly from the rewritten constraints, and the bypass stays gated
        // by the strict definitive-false oracle.
        if matches!(result, Ok(SolveResult::Sat)) && introduced_unconstrained_div_mod {
            self.sat_validated_by_mod_div_or_branch = true;
        }
        result
    }

    /// Record whether `term` references any Int-sorted variable (`has_int`),
    /// any Real-sorted variable (`has_real`), and/or any Bool-sorted VARIABLE
    /// (`has_bool`). Constants are ignored (only variables decide disjointness);
    /// quantifier bodies are not reached (the caller gates out quantifiers). A
    /// free Bool variable disqualifies the split — the two sub-solves have
    /// independent SAT encodings, so their `sat_model`s cannot be unioned; only
    /// pure-arithmetic formulas (atoms + connectives, no Bool var) are eligible,
    /// where `evaluate_term` reads atoms straight from the LIA/LRA sub-models.
    fn term_arith_var_sorts(
        &self,
        term: TermId,
        has_int: &mut bool,
        has_real: &mut bool,
        has_bool: &mut bool,
    ) {
        match self.ctx.terms.get(term) {
            TermData::Var(_, _) => match self.ctx.terms.sort(term) {
                Sort::Int => *has_int = true,
                Sort::Real => *has_real = true,
                Sort::Bool => *has_bool = true,
                _ => *has_bool = true, // any other var sort also disqualifies
            },
            TermData::App(_, args) => {
                for &a in args {
                    self.term_arith_var_sorts(a, has_int, has_real, has_bool);
                }
            }
            TermData::Not(inner) => self.term_arith_var_sorts(*inner, has_int, has_real, has_bool),
            TermData::Ite(c, t, e) => {
                self.term_arith_var_sorts(*c, has_int, has_real, has_bool);
                self.term_arith_var_sorts(*t, has_int, has_real, has_bool);
                self.term_arith_var_sorts(*e, has_int, has_real, has_bool);
            }
            TermData::Let(bindings, body) => {
                for (_, val) in bindings {
                    self.term_arith_var_sorts(*val, has_int, has_real, has_bool);
                }
                self.term_arith_var_sorts(*body, has_int, has_real, has_bool);
            }
            _ => {}
        }
    }

    /// Fail-safe pre-pass: solve a provably-disjoint pure-Int / pure-Real problem
    /// with the two complete pure solvers and combine (#mixed-int-real; see
    /// `repros/mixed-int-real-combination/`). Closes the exact P0 trigger — an
    /// Int-var atom and a Real-var atom sharing no variable — that today returns
    /// `unknown` because the Nelson-Oppen combination of the Int and Real linear
    /// solvers is not implemented.
    ///
    /// Trigger (all required): non-incremental (`incr_theory_state.is_none()`,
    /// which also guards re-entrancy since the sub-solves create that state);
    /// quantifier-free, pure linear Int+Real, no other theory, no
    /// `to_real`/`to_int`/`is_int` bridge; at the FLATTENED-conjunct level no
    /// conjunct mixes an Int and a Real variable (exactly how a bridge would
    /// co-locate the two sorts), with ≥1 Int-var conjunct and ≥1 Real-var
    /// conjunct.
    ///
    /// Soundness is airtight by construction and independent of the disjointness
    /// analysis being perfect: UNSAT is returned only when a SUBSET (one
    /// partition) is unsat; SAT is returned only when the union model satisfies
    /// the FULL original formula (`model_satisfies_assertions`); every other
    /// outcome returns `None` and falls through to the unchanged solve below.
    fn try_disjoint_int_real_split(&mut self) -> Result<Option<SolveResult>> {
        // Gate: non-incremental only (doubles as the re-entrancy guard — the
        // sub-solves populate incr_theory_state, so a nested call bails here).
        if self.incr_theory_state.is_some() {
            return Ok(None);
        }
        // Cheap whole-formula pre-filter: QF, pure linear Int+Real, no bridge,
        // no other theory. `has_is_int_real` covers the `is_int` bridge; the
        // per-conjunct mix check below covers `to_real`/`to_int`.
        let feats = crate::features::StaticFeatures::collect(&self.ctx.terms, &self.ctx.assertions);
        if feats.has_quantifiers
            || feats.has_is_int_real
            || feats.has_bv
            || feats.has_bv_int_conversion
            || feats.has_arrays
            || feats.has_strings
            || feats.has_seq
            || feats.has_seq_ops
            || feats.has_set_ops
            || feats.has_multiset_ops
            || feats.has_map_ops
            || feats.has_regex
            || feats.has_fpa
            || feats.has_uf
            || !feats.has_int_var
            || !feats.has_real
        {
            return Ok(None);
        }

        // Per-conjunct sort profiling on the flattened top-level conjunction (the
        // P0 example is a single `(assert (and (> x 5) (> p 5.0)))`).
        let flat = self.flatten_assertion_conjunctions();
        let mut int_side: Vec<TermId> = Vec::new();
        let mut real_side: Vec<TermId> = Vec::new();
        let mut saw_int_var = false;
        let mut saw_real_var = false;
        for &c in &flat {
            let (mut hi, mut hr, mut hb) = (false, false, false);
            self.term_arith_var_sorts(c, &mut hi, &mut hr, &mut hb);
            if hb || (hi && hr) {
                // A free Bool (or other-sort) variable, or a conjunct mixing Int
                // and Real vars (incl. any to_real/to_int bridge) — either
                // disqualifies the pure-arithmetic disjoint split. Defer.
                return Ok(None);
            }
            if hr {
                real_side.push(c);
                saw_real_var = true;
            } else {
                // Int-var conjunct, or a pure-Bool conjunct (no arith var) — the
                // full-formula revalidation is the backstop either way.
                int_side.push(c);
                if hi {
                    saw_int_var = true;
                }
            }
        }
        if !(saw_int_var && saw_real_var) {
            return Ok(None);
        }

        // Snapshot state (mirror `try_sat_via_mod_free_or_branch`) so every exit
        // restores the executor to entry. incr_theory_state was None at entry
        // and is reset to None on exit regardless of the sub-solves.
        let saved_assertions = self.ctx.assertions.clone();
        let saved_model = self.last_model.clone();
        let saved_model_validated = self.last_model_validated;
        let saved_unknown_reason = self.last_unknown_reason;
        let saved_result = self.last_result.clone();
        let saved_skip_model_eval = self.skip_model_eval;
        let saved_branch_validation = self.sat_validated_by_mod_div_or_branch;

        // Sub-solve the pure-Int partition with the complete Int solver.
        self.ctx.assertions = int_side;
        self.last_model = None;
        self.last_result = None;
        self.last_model_validated = false;
        self.skip_model_eval = false;
        self.sat_validated_by_mod_div_or_branch = false;
        let res_int = self.solve_lia();
        let model_int = self.last_model.take();
        self.incr_theory_state = None;

        // Sub-solve the pure-Real partition with the complete Real solver.
        self.ctx.assertions = real_side;
        self.last_model = None;
        self.last_result = None;
        self.last_model_validated = false;
        self.skip_model_eval = false;
        self.sat_validated_by_mod_div_or_branch = false;
        let res_real = self.solve_lra();
        let model_real = self.last_model.take();
        self.incr_theory_state = None;

        let int_unsat = matches!(&res_int, Ok(r) if r.is_unsat());
        let real_unsat = matches!(&res_real, Ok(r) if r.is_unsat());
        let int_sat = matches!(&res_int, Ok(r) if r.is_sat());
        let real_sat = matches!(&res_real, Ok(r) if r.is_sat());

        // UNSAT via subset — always sound (each partition is a subset of the
        // whole, so if either is unsat the conjunction is unsat).
        if int_unsat || real_unsat {
            self.ctx.assertions = saved_assertions;
            self.last_model = saved_model;
            self.last_model_validated = saved_model_validated;
            self.last_unknown_reason = saved_unknown_reason;
            self.last_result = saved_result;
            self.skip_model_eval = saved_skip_model_eval;
            self.sat_validated_by_mod_div_or_branch = saved_branch_validation;
            self.incr_theory_state = None;
            return Ok(Some(SolveResult::unsat()));
        }

        // SAT via union model, GATED by full-formula revalidation.
        if int_sat && real_sat {
            if let (Some(mut combined), Some(mr)) = (model_int, model_real) {
                // Pure-arithmetic disjoint components: graft the Real solve's
                // Real assignments onto the Int solve's model. `evaluate_term`
                // reads Int atoms from `lia_model` (already on `combined`) and
                // Real atoms from `lra_model` (grafted here); no Bool var exists
                // (gated above), so the divergent `sat_model`s are never
                // consulted. `completed_values` carries unconstrained-constant
                // assignments from each side. Any field this misses can only
                // make the revalidation below FAIL (→ fall through), never a
                // wrong `sat`.
                combined.lra_model = mr.lra_model;
                combined.completed_values.extend(mr.completed_values);
                combined.bool_overrides.extend(mr.bool_overrides);
                self.ctx.assertions = saved_assertions.clone();
                self.last_model = Some(combined);
                self.last_result = Some(SolveResult::Sat);
                self.last_model_validated = true;
                self.last_unknown_reason = None;
                self.skip_model_eval = saved_skip_model_eval;
                self.sat_validated_by_mod_div_or_branch = false;
                self.incr_theory_state = None;
                if self.model_satisfies_assertions() {
                    return Ok(Some(SolveResult::Sat));
                }
                // The union did not satisfy the full formula — fall through.
            }
        }

        // Fall through: restore entry state exactly; the unchanged solve runs.
        self.ctx.assertions = saved_assertions;
        self.last_model = saved_model;
        self.last_model_validated = saved_model_validated;
        self.last_unknown_reason = saved_unknown_reason;
        self.last_result = saved_result;
        self.skip_model_eval = saved_skip_model_eval;
        self.sat_validated_by_mod_div_or_branch = saved_branch_validation;
        self.incr_theory_state = None;
        Ok(None)
    }

    /// Solve using combined Arrays + EUF + LIA + LRA theory (QF_AUFLIRA)
    ///
    /// This handles both integer branch-and-bound splits (NeedSplit) and
    /// disequality splits (NeedDisequalitySplit) for mixed Int+Real problems.
    pub(in crate::executor) fn solve_auflira(&mut self) -> Result<SolveResult> {
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }
        let (mut preprocessed_assertions, mut proof_provenance) =
            self.preprocess_mod_div_assertions_with_proof_provenance(&self.ctx.assertions.clone());

        // NOTE: expand_select_store is NOT applied here — solve_auflira does not
        // have ITE lifting. See solve_auf_lia for the full pipeline (#6282).

        // Eager array axioms for soundness (#4304, #5086, #6282)
        {
            let axiom_start = self.ctx.assertions.len();
            self.run_array_axiom_full_fixpoint_at(axiom_start);
            preprocessed_assertions.extend(self.ctx.assertions.drain(axiom_start..));
        }
        proof_provenance = ProofProblemAssertionProvenance::from_sources(
            proof_provenance.original_problem_assertions,
            &preprocessed_assertions,
            proof_provenance.assertion_sources,
        );

        let solve_interrupt = self.solve_interrupt.clone();
        let solve_deadline = self.solve_deadline.clone();
        self.with_deferred_postprocessing(preprocessed_assertions, proof_provenance, |this| {
            this.configure_sat_search_tuning(100.0, 1.1, 0.01);
            solve_incremental_split_loop_pipeline!(this,
                tag: "AUFLIRA",
                persistent_sat_field: persistent_sat,
                create_theory: AufLiraSolver::new(&this.ctx.terms),
                extract_models: |theory| {
                    let (euf, arr, lia, lra) = theory.extract_all_models();
                    TheoryModels {
                        euf: Some(euf),
                        array: Some(arr),
                        lra: Some(lra),
                        lia,
                        ..TheoryModels::default()
                    }
                },
                max_splits: MAX_SPLITS_MIXED,
                pre_theory_import: |theory, lc, hc, ds| {
                    theory.import_learned_state(std::mem::take(lc), std::mem::take(hc));
                    theory.import_dioph_state(std::mem::take(ds));
                },
                post_theory_export: |theory| {
                    let (lc, hc) = theory.take_learned_state();
                    let ds = theory.take_dioph_state();
                    (lc, hc, ds)
                },
                pre_iter_check: |_s| {
                    solve_interrupt
                        .as_ref()
                        .is_some_and(|flag| flag.load(std::sync::atomic::Ordering::Relaxed))
                        || solve_deadline.expired()
                }
            )
        })
    }
}

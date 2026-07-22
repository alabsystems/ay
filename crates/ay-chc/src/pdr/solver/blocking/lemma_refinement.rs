// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl PdrSolver {
    /// Post-interpolation lemma refinement pipeline.
    ///
    /// Applies 7 sequential transformations to a raw interpolation result:
    /// 1. Bool denormalization (Int→Bool sort recovery)
    /// 2. Trivial interpolant rejection (true/false → heuristic fallback)
    /// 3. Sign-bit strengthening (Bool-only interpolant + non-Bool vars)
    /// 4. Point-blocking strengthening
    /// 5. Literal weakening / BV flag-guard weakening
    /// 6. BV bit decomposition
    /// 7. BV native simplification
    ///
    /// Returns the refined blocking formula ready for inductiveness verification.
    pub(in crate::pdr::solver) fn refine_blocking_lemma(
        &mut self,
        generalized: ChcExpr,
        pob: &ProofObligation,
        has_bool_normalization: bool,
        all_bool_vars: &FxHashSet<String>,
        interpolant_kind: Option<InterpolantKind>,
    ) -> ChcExpr {
        // #5877: Denormalize integer-encoded boolean vars back to Bool sort.
        // If we normalized Bool constraints to Int for interpolation, convert
        // the interpolant back so downstream lemma processing sees Bool vars.
        let generalized = if has_bool_normalization {
            denormalize_int_to_bool(&generalized, all_bool_vars)
        } else {
            generalized
        };

        // #5805/#6002: Reject trivial interpolation results before generalization.
        //
        // Four degenerate blocking formulas can arise from interpolation:
        //   Bool(false)       — blocks nothing (useless lemma, wastes generalization)
        //   Not(Bool(true))   — structurally "not true" = false, same as above
        //   Bool(true)        — blocks everything (unsound: negated lemma is "false",
        //                       which falsifies the frame → spurious Safe)
        //   Not(Bool(false))  — structurally "not false" = true, same as above
        //
        // All four are rejected early and fall back to heuristic generalization.
        let generalized = if matches!(&generalized, ChcExpr::Bool(false))
            || matches!(&generalized, ChcExpr::Bool(true))
            || matches!(&generalized, ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 && matches!(args[0].as_ref(), ChcExpr::Bool(true)))
            || matches!(&generalized, ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 && matches!(args[0].as_ref(), ChcExpr::Bool(false)))
        {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: #5805/#6002 Rejecting trivial interpolant ({}) — falling back to heuristic generalization",
                    generalized
                );
            }
            self.generalize_blocking_formula(&pob.state, pob.predicate, pob.level)
        } else {
            generalized
        };

        // #7756: After denormalization, verify the generalized formula still covers
        // the original state. Bool denormalization can invert polarity when the
        // interpolant's Bool component agrees with (rather than contradicts) the
        // bad state. Example: interpolant has (>= a0 1) meaning "a0=true", bad
        // state also has a0=true. NOT(interpolant) produces (not a0) = "a0=false"
        // which does NOT cover the bad state. When this happens, the interpolation
        // result is valid globally but the negated Bool fragment alone is wrong.
        // Fall back to heuristic generalization which starts from the state itself.
        let generalized = {
            let state_values = self.extract_point_values_from_state(&pob.state);
            if !state_values.is_empty() {
                let state_consistent = self.point_values_satisfy_cube(&pob.state, &state_values);
                if state_consistent && !self.point_values_satisfy_cube(&generalized, &state_values)
                {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: #7756 Interpolation result does not cover original state after denormalization, \
                             falling back to heuristic generalization. state={}, generalized={}",
                            pob.state,
                            generalized
                        );
                    }
                    self.generalize_blocking_formula(&pob.state, pob.predicate, pob.level)
                } else {
                    generalized
                }
            } else {
                generalized
            }
        };

        // #5877: Strengthen Boolean-only interpolants for mixed-sort predicates.
        // When a predicate has non-Bool arguments (BV/Int) but the interpolant
        // references only Bool-sorted variables, the interpolation lost all
        // non-Bool constraints. Such lemmas are inductive at each level but
        // never self-inductive (transitions can produce states satisfying the
        // Bool constraint with arbitrary non-Bool values), causing infinite
        // level growth without convergence.
        //
        // Fix: augment the Bool interpolant with sign-bit / bound constraints
        // for non-Bool predicate args using model values from Step 1. For Int
        // variables, add `(>= x 0)` or `(< x 0)` based on the model sign.
        // For BV variables, add `(= (extract msb msb x) #b0)` or `#b1`.
        // Then check self-inductiveness: if the strengthened lemma is
        // self-inductive, it can be pushed and PDR converges.
        let generalized = {
            let interp_vars = generalized.vars();
            let has_non_bool_var = interp_vars.iter().any(|v| !matches!(v.sort, ChcSort::Bool));
            let pred_has_non_bool = self.canonical_vars(pob.predicate).map_or(false, |vars| {
                vars.iter().any(|v| !matches!(v.sort, ChcSort::Bool))
            });
            if !has_non_bool_var && pred_has_non_bool && !interp_vars.is_empty() {
                if let Some(ref model) = pob.smt_model {
                    if let Some(canon_vars) = self.canonical_vars(pob.predicate) {
                        let constrained_names: FxHashSet<String> =
                            interp_vars.iter().map(|v| v.name.clone()).collect();
                        // Build sign-bit constraints for each unconstrained non-Bool var.
                        let mut sign_constraints: Vec<ChcExpr> = Vec::new();
                        for cv in canon_vars {
                            if constrained_names.contains(&cv.name) {
                                continue;
                            }
                            match (&cv.sort, model.get(&cv.name)) {
                                (ChcSort::Int, Some(SmtValue::Int(n))) => {
                                    // Int var: add sign constraint (>= x 0) or (< x 0)
                                    if *n >= 0 {
                                        sign_constraints.push(ChcExpr::ge(
                                            ChcExpr::var(cv.clone()),
                                            ChcExpr::int(0),
                                        ));
                                    } else {
                                        sign_constraints.push(ChcExpr::lt(
                                            ChcExpr::var(cv.clone()),
                                            ChcExpr::int(0),
                                        ));
                                    }
                                }
                                (ChcSort::BitVec(w), Some(SmtValue::BitVec(v, _))) => {
                                    // BV var: add sign-bit constraint based on MSB
                                    let msb = if *w > 0 { *w - 1 } else { 0 };
                                    let sign_bit = (*v >> msb) & 1;
                                    let bv_var = ChcExpr::var(cv.clone());
                                    let extract = ChcExpr::Op(
                                        ChcOp::BvExtract(msb, msb),
                                        vec![Arc::new(bv_var)],
                                    );
                                    let bit_val = ChcExpr::BitVec(sign_bit, 1);
                                    sign_constraints.push(ChcExpr::eq(extract, bit_val));
                                }
                                _ => {}
                            }
                        }
                        if !sign_constraints.is_empty() {
                            // Try each sign constraint individually with the interpolant.
                            // Keep those that maintain self-inductiveness.
                            let mut strengthened = generalized;
                            for sc in &sign_constraints {
                                let candidate = ChcExpr::and(strengthened.clone(), sc.clone());
                                if self.is_inductive_blocking(&candidate, pob.predicate, pob.level)
                                {
                                    if self.is_self_inductive_blocking(&candidate, pob.predicate) {
                                        if self.config.verbose {
                                            safe_eprintln!(
                                                "PDR: #5877 Strengthened with self-inductive sign constraint: {} + {}",
                                                strengthened, sc
                                            );
                                        }
                                        strengthened = candidate;
                                    } else {
                                        if self.config.verbose {
                                            safe_eprintln!(
                                                "PDR: #5877 Sign constraint {} is inductive but not self-inductive, keeping",
                                                sc
                                            );
                                        }
                                        // Still add it — it may help with convergence
                                        // even if not immediately self-inductive
                                        strengthened = candidate;
                                    }
                                }
                            }
                            strengthened
                        } else {
                            generalized
                        }
                    } else {
                        generalized
                    }
                } else {
                    generalized
                }
            } else {
                generalized
            }
        };

        // Fix #967: Strengthen weak point-blocking from interpolation to avoid enumeration.
        // When interpolation produces (= var k), try strengthening to (= var init_val).
        // Fix #1236: Pass pob.state to verify strengthened formula still blocks the POB.
        // inc-12: spacer-mode (interpolant-as-lemma) skips this SMT-checked
        // enumeration — the cascade's result is admitted raw, golem-style.
        let generalized = if self.config.interpolant_first_blocking {
            generalized
        } else {
            self.try_strengthen_point_blocking(&generalized, pob.predicate, pob.level, &pob.state)
        };

        // #5877 Packet 2: preserve direct-IUC BV clauses on first admission.
        // Spacer stores the raw clause first and only generalizes later. For
        // native-BV zero-Farkas interpolation, both direct-IUC variants are
        // Craig-valid raw cores; running the BV weakening stack immediately can
        // erase the compact guard clauses needed for nested4-style convergence.
        let skip_bv_weakening = !self.problem_is_pure_lia
            && matches!(
                interpolant_kind,
                Some(InterpolantKind::DirectIucCoreExact | InterpolantKind::DirectIucValidated)
            );

        if skip_bv_weakening && self.config.verbose {
            safe_eprintln!(
                "PDR: #5877 Packet 2: skipping BV weakening for direct-IUC interpolant: {}",
                generalized
            );
        }

        // Fix #816: Apply LiteralWeakeningGeneralizer to convert point equalities to inequalities.
        //
        // After #967 strengthening, lemmas may contain equalities like (= var 0) that could
        // be weakened to (var <= 0) or (var >= 0). This converts point lemmas to range lemmas,
        // which block more states and prevent exponential point enumeration.
        //
        // Design: the development design notes
        let generalized = if skip_bv_weakening {
            let before = generalized.clone();
            let mut adapter = PdrGeneralizerAdapter::new(self, pob.predicate);
            let after = BvFlagGuardGeneralizer::new().generalize(
                &generalized,
                pob.level as u32,
                &mut adapter,
            );
            if self.config.verbose && before != after {
                safe_eprintln!(
                    "PDR: #5877 BV flag-guard weakening on direct-IUC: {} -> {}",
                    before,
                    after
                );
            }
            after
        } else if self.config.interpolant_first_blocking {
            // inc-12: spacer-mode skips the #816 literal-weakening ladder —
            // measured at up to 26 SMT-checked rejections per pob on the
            // attribution instances. The lemma is admitted as the cascade
            // produced it; the inductiveness guard downstream is unchanged.
            generalized
        } else {
            let before = generalized.clone();
            let mut adapter = PdrGeneralizerAdapter::new(self, pob.predicate);
            let after = LiteralWeakeningGeneralizer::new().generalize(
                &generalized,
                pob.level as u32,
                &mut adapter,
            );
            if self.config.verbose && before != after {
                safe_eprintln!("PDR: #816 LiteralWeakening: {} -> {}", before, after);
            }
            after
        };

        // #5877: Apply BvBitDecompositionGeneralizer to post-interpolation lemmas.
        // Interpolation can produce BV equality conjuncts `(= var #xNNNN)` that are
        // maximally specific. Decompose into per-bit constraints and try dropping bits.
        let generalized = if !self.problem_is_pure_lia && !skip_bv_weakening {
            let before = generalized.clone();
            let mut adapter = PdrGeneralizerAdapter::new(self, pob.predicate);
            let after = BvBitDecompositionGeneralizer::new().generalize(
                &generalized,
                pob.level as u32,
                &mut adapter,
            );
            if self.config.verbose && before != after {
                safe_eprintln!(
                    "PDR: #5877 BvBitDecompose post-interp: {} -> {}",
                    before,
                    after
                );
            }
            after
        } else {
            generalized
        };

        // #5877 Packet 3 fallback remains deferred. Only run the BV-native
        // simplifier on non-exact-core paths; exact-core direct-IUC lemmas get a
        // raw-clause first admission and can be simplified later if propagation
        // shows the raw form is insufficient.
        let generalized = if !self.problem_is_pure_lia && !skip_bv_weakening {
            self.try_simplify_bv_native_lemma(&generalized, pob.predicate, pob.level)
                .unwrap_or(generalized)
        } else {
            generalized
        };

        // #7756: Final coverage check. If any refinement step caused the
        // generalized formula to lose coverage of the original state, fall back
        // to the original state as the blocking formula. This is a safety net
        // that catches polarity inversions from interpolation + denormalization,
        // sign-bit strengthening on wrong-polarity Bool fragments, or any other
        // refinement step that inadvertently narrows the blocking set.
        let generalized = {
            let state_values = self.extract_point_values_from_state(&pob.state);
            if !state_values.is_empty() {
                // #5805: Only check coverage if the state itself is consistent
                // under point evaluation. States with clause-local boolean
                // variables can be self-contradictory (e.g., I=true, H=false
                // but (or (not I) (and I H)) in conjuncts). In that case, any
                // generalization is valid — the state is vacuously unreachable.
                let state_consistent = self.point_values_satisfy_cube(&pob.state, &state_values);
                if state_consistent && !self.point_values_satisfy_cube(&generalized, &state_values)
                {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: #7756 Final coverage check failed — refined formula does not cover \
                             original state, falling back to heuristic generalization. state={}, generalized={}",
                            pob.state,
                            generalized
                        );
                    }
                    self.generalize_blocking_formula(&pob.state, pob.predicate, pob.level)
                } else {
                    generalized
                }
            } else {
                generalized
            }
        };

        generalized
    }
}

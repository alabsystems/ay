// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! String extf reduction pass: EQC constant conflict detection and unification.
//!
//! Evaluates value-returning extf applications (str.at, str.substr, str.replace)
//! and checks for conflicts with EQC constants. Also simplifies singleton
//! concats and finds constant terms for reduced values.
//!
//! Extracted from extf_pass.rs as part of #5970 code-health splits.

use super::*;

impl CoreSolver {
    /// Evaluate value-returning extf applications and check for EQC constant conflicts.
    ///
    /// For each EQC that has a known string constant, check if any member is a
    /// reducible function application (str.at, str.substr, str.replace) whose
    /// evaluated result differs from the EQC constant. This detects conflicts like:
    ///   str.at("hello", 0) = "e"  → evaluated "h" ≠ EQC constant "e" → conflict.
    ///
    /// Reference: CVC5 ExtfSolver::checkExtfReductions
    pub(super) fn check_extf_reductions(
        &mut self,
        terms: &TermStore,
        state: &SolverState,
        infer: &mut InferenceManager,
    ) -> bool {
        let reps = state.eqc_representatives();

        // Pass 1: For EQCs with a known constant, check that any reducible member
        // evaluates to the same constant (conflict detection).
        for &rep in &reps {
            let eqc = match state.get_eqc(&rep) {
                Some(eqc) => eqc,
                None => continue,
            };

            let eqc_const = match &eqc.constant {
                Some(c) => c.clone(),
                None => continue,
            };

            for &member in &eqc.members {
                if self.reduced_terms.contains(&member) {
                    // Soundness (#6715): Even for reduced terms, verify value
                    // consistency when the EQC has a constant. Structural
                    // decomposition lemmas constrain lengths/concatenation but
                    // do NOT propagate string content values through skolems.
                    if let Some(ref reduced) = Self::try_reduce_string_term(terms, state, member) {
                        if *reduced != eqc_const {
                            if *DEBUG_STRING_CORE {
                                eprintln!(
                                    "[STRING_CORE] check_extf_reductions conflict (reduced term): rep={:?} member={:?} data={:?} reduced={:?} eqc_const={:?}",
                                    rep, member, terms.get(member), reduced, eqc_const
                                );
                            }
                            let mut explanation = state.explain_or_all(member, rep);
                            if let Some(const_id) = state.find_constant_term_id_for_rep(terms, &rep)
                            {
                                explanation.extend(state.explain(const_id, rep));
                            }
                            Self::add_arg_resolution_explanations(
                                terms,
                                state,
                                member,
                                &mut explanation,
                            );
                            infer.add_conflict(InferenceKind::PredicateConflict, explanation);
                            return true;
                        }
                    }
                    continue;
                }
                // Evaluate BEFORE requesting a reduction lemma (extf wave 2):
                // a ground-resolvable application needs no decomposition, and
                // recursive reductions (str.replace_all) would otherwise keep
                // unrolling ground-evaluable chains until the step budget.
                let evaluated = Self::try_reduce_string_term(terms, state, member);
                if evaluated.is_none() && self.request_dynamic_extf_lemma(terms, state, member) {
                    continue;
                }
                if let Some(ref reduced) = evaluated {
                    if *reduced == eqc_const {
                        continue;
                    }
                    if *DEBUG_STRING_CORE {
                        eprintln!(
                            "[STRING_CORE] check_extf_reductions conflict: rep={:?} member={:?} data={:?} reduced={:?} eqc_const={:?}",
                            rep,
                            member,
                            terms.get(member),
                            reduced,
                            eqc_const
                        );
                    }
                    // Evaluated value differs from EQC constant → conflict.
                    // Explanation: why member is in this EQC + why the EQC
                    // has its constant + arg resolution for the reduction.
                    let mut explanation = state.explain_or_all(member, rep);
                    if let Some(const_id) = state.find_constant_term_id_for_rep(terms, &rep) {
                        explanation.extend(state.explain(const_id, rep));
                    }
                    Self::add_arg_resolution_explanations(terms, state, member, &mut explanation);
                    infer.add_conflict(InferenceKind::PredicateConflict, explanation);
                    return true;
                }

                if Self::is_reducible_string_app(terms, member)
                    && !self.reduced_terms.contains(&member)
                    && !self.request_dynamic_extf_lemma(terms, state, member)
                {
                    if *DEBUG_STRING_CORE {
                        eprintln!(
                            "[STRING_CORE] extf_reductions pass1 latches incomplete: {:?} = {:?}",
                            member,
                            terms.get(member)
                        );
                    }
                    self.incomplete = true;
                }
            }
        }

        // Pass 2: For EQCs WITHOUT a constant, check if any reducible member
        // can be evaluated. If so, find the constant term for the reduced value
        // and assert an internal equality. This handles cases like
        // str.replace(y, y, "") reducing to "" before normal form computation.
        for &rep in &reps {
            let eqc = match state.get_eqc(&rep) {
                Some(eqc) => eqc,
                None => continue,
            };
            if eqc.constant.is_some() {
                continue; // Already handled in pass 1.
            }

            for &member in &eqc.members {
                if !Self::is_reducible_string_app(terms, member) {
                    continue;
                }
                // Terms with DPLL-level reduction lemmas have their
                // semantics captured by word equations + arithmetic, so
                // they never latch `incomplete` or re-request a lemma —
                // but a ground-resolvable one is still EVALUATED and
                // merged below (extf wave 2): the partial regex-replace
                // reductions rely on this merge to pin the application's
                // value once its haystack resolves.
                let is_reduced = self.reduced_terms.contains(&member);
                // Evaluate BEFORE requesting a reduction lemma (extf wave 2):
                // a ground-resolvable application resolves via the internal
                // equality merge below, and recursive reductions
                // (str.replace_all) would otherwise keep unrolling
                // ground-evaluable chains until the step budget.
                let Some(reduced) = Self::try_reduce_string_term(terms, state, member) else {
                    if !is_reduced && !self.request_dynamic_extf_lemma(terms, state, member) {
                        if *DEBUG_STRING_CORE {
                            eprintln!(
                                "[STRING_CORE] extf_reductions pass2-noeval latches incomplete: {:?} = {:?}",
                                member,
                                terms.get(member)
                            );
                        }
                        self.incomplete = true;
                    }
                    continue;
                };
                // Find a registered constant term with this value.
                let const_term = Self::find_constant_term_for_value(terms, state, &reduced);
                if let Some(const_id) = const_term {
                    if state.find(member) != state.find(const_id) {
                        // Explanation: why each argument of member resolved
                        // to its current representative.
                        let mut explanation = Vec::new();
                        Self::add_arg_resolution_explanations(
                            terms,
                            state,
                            member,
                            &mut explanation,
                        );
                        // Ground extf evaluations (e.g., str.at("hello", 0) → "h")
                        // produce empty explanations because all arguments are
                        // constants that don't need EQC resolution. The
                        // merge_internal_equalities guard (#4057) skips merges
                        // with empty explanations. For ground evaluations, find
                        // an assertion that involves the extf's EQC as
                        // explanation — the assertion is the reason the extf
                        // term is relevant to the current SAT assignment.
                        if explanation.is_empty() {
                            let member_rep = state.find(member);
                            for &lit in state.assertions() {
                                let (atom, polarity) = Self::atom_and_polarity(terms, lit);
                                if !polarity {
                                    continue;
                                }
                                if let TermData::App(sym, args) = terms.get(atom) {
                                    if sym.name() == "=" && args.len() == 2 {
                                        let a_rep = state.find(args[0]);
                                        let b_rep = state.find(args[1]);
                                        if a_rep == member_rep || b_rep == member_rep {
                                            explanation.push(lit);
                                            break;
                                        }
                                    }
                                }
                            }
                        }
                        infer.add_internal_equality(
                            InferenceKind::Unify,
                            member,
                            const_id,
                            explanation,
                        );
                    }
                } else {
                    // Term reduces to a value but no matching constant exists
                    // in the state. Cannot merge; stay incomplete to avoid
                    // false SAT. Already-reduced terms are not re-requested
                    // (that would stall the lemma loop on duplicates) but
                    // still latch incomplete here — their value is known yet
                    // unconnected, so claiming SAT would be unsound.
                    if is_reduced || !self.request_dynamic_extf_lemma(terms, state, member) {
                        if *DEBUG_STRING_CORE {
                            eprintln!(
                                "[STRING_CORE] extf_reductions pass2-noconst latches incomplete: {:?} = {:?}",
                                member,
                                terms.get(member)
                            );
                        }
                        self.incomplete = true;
                    }
                }
            }
        }

        if self.check_extf_string_equalities(terms, state, infer) {
            return true;
        }
        infer.has_conflict()
    }

    /// Simplify concat terms that reduce to a single non-empty child.
    ///
    /// After I_CYCLE and self-concat reasoning infer extras="", a concat like
    /// `str.++(x, y)` where `y=""` effectively equals `x`. This step infers
    /// that equality explicitly, breaking mutual NF dependency cycles (#3850).
    pub(super) fn simplify_singleton_concats(
        &self,
        terms: &TermStore,
        state: &SolverState,
        infer: &mut InferenceManager,
    ) -> bool {
        for rep in state.eqc_representatives() {
            let Some(eqc) = state.get_eqc(&rep) else {
                continue;
            };
            for &concat_term in &eqc.concat_terms {
                let Some(children) = state.get_concat_children(terms, concat_term) else {
                    continue;
                };

                let mut sole_child = None;
                let mut multi = false;
                for &child in children {
                    if !state.is_empty_string(terms, child) {
                        if sole_child.is_some() {
                            multi = true;
                            break;
                        }
                        sole_child = Some(child);
                    }
                }

                if multi {
                    continue;
                }

                let target = match sole_child {
                    Some(c) => c,
                    None => match state.empty_string_id() {
                        Some(eid) => eid,
                        None => continue,
                    },
                };

                if state.find(concat_term) != state.find(target) {
                    // Explain: concat_term = target because every sibling is
                    // empty. Collect explain(sibling, "") for each empty child.
                    let mut explanation = Vec::new();
                    if let Some(eid) = state.empty_string_id() {
                        for &child in children {
                            if Some(child) != sole_child {
                                explanation.extend(state.explain(child, eid));
                            }
                        }
                    }
                    if *DEBUG_STRING_CORE {
                        eprintln!(
                            "[STRING_CORE] simplify_singleton_concats: {:?} = {:?} (sole_child={:?}, explanation_len={})",
                            concat_term, target, sole_child, explanation.len()
                        );
                    }
                    infer.add_internal_equality(
                        InferenceKind::EndpointEq,
                        concat_term,
                        target,
                        explanation,
                    );
                }
            }
            if infer.has_conflict() {
                return true;
            }
        }
        infer.has_conflict()
    }

    /// Find a registered constant term with the given string value.
    ///
    /// Searches all EQCs for one whose constant matches `value`, then
    /// returns the actual constant TermId from that EQC.
    pub(super) fn find_constant_term_for_value(
        terms: &TermStore,
        state: &SolverState,
        value: &str,
    ) -> Option<TermId> {
        // Fast path for empty string.
        if value.is_empty() {
            return state.empty_string_id();
        }
        // Slow path: scan EQCs for a matching constant.
        for rep in state.eqc_representatives() {
            if let Some(eqc) = state.get_eqc(&rep) {
                if eqc.constant.as_deref() == Some(value) {
                    return state.find_constant_term_id_for_rep(terms, &rep);
                }
            }
        }
        None
    }
}

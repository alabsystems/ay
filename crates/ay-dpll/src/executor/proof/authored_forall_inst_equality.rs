// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl Executor {
    /// Ground terms that may be proposed as `forall_inst` arguments: every
    /// subterm of the authored roots reachable WITHOUT entering a binder.
    ///
    /// Never descending into a `forall`/`exists`/`let` body is what makes the
    /// harvest safe to hand to the strict validator: no variable bound by the
    /// quantifier being instantiated can appear in the result, so no proposal
    /// can capture. This decides NOTHING — `validate_forall_inst` re-checks
    /// groundness (`argument_is_ground_for`) and the exact substitution on
    /// whatever this returns, so an over-eager harvest costs a declined
    /// candidate and never buys an accepted one.
    fn collect_ground_instantiation_values(
        terms: &TermStore,
        authored: &[TermId],
        work_limit: usize,
    ) -> Vec<TermId> {
        let mut seen = ay_core::kani_compat::DetHashSet::default();
        let mut values = Vec::new();
        let mut work = 0usize;
        // Reversed so the iterative stack visits the authored roots in order;
        // the whole harvest must be deterministic across runs.
        let mut stack: Vec<TermId> = authored.iter().rev().copied().collect();
        while let Some(term) = stack.pop() {
            if work >= work_limit {
                break;
            }
            work += 1;
            if !seen.insert(term) {
                continue;
            }
            match terms.get(term) {
                // A binder's body is off limits: its bound variables are not
                // ground and must never reach a proposal.
                TermData::Forall(..) | TermData::Exists(..) | TermData::Let(..) => continue,
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(condition, then_branch, else_branch) => {
                    values.push(term);
                    stack.extend([*condition, *then_branch, *else_branch]);
                }
                TermData::App(_, args) => {
                    values.push(term);
                    stack.extend(args.iter().rev().copied());
                }
                TermData::Const(..) | TermData::Var(..) => values.push(term),
                _ => {}
            }
        }
        values
    }

    /// Derive the unit clause `(cl instance)` inside `candidate` from the exact
    /// authored `forall` root, and return the step proving it.
    ///
    /// Four steps, all strict-checkable and none of them trusted: the authored
    /// `assume`, a premiseless `forall_inst` carrying the positional arguments,
    /// Boolean `or` clausification, and one resolution against the assume.
    /// `validate_forall_inst` re-derives the whole substitution from the clause
    /// and the arguments, so this producer asserts nothing.
    fn derive_authored_forall_instance_unit(
        &mut self,
        candidate: &mut Proof,
        forall_root: TermId,
        values: &[TermId],
        instance: TermId,
    ) -> ProofId {
        let not_forall = self.ctx.terms.mk_not_raw(forall_root);
        let implication =
            self.ctx
                .terms
                .mk_app(Symbol::named("or"), [not_forall, instance], Sort::Bool);
        let forall_assume = candidate.add_assume(forall_root, None);
        let instantiated = candidate.add_rule_step(
            AletheRule::ForallInst,
            vec![implication],
            Vec::new(),
            values.to_vec(),
        );
        let clausified = candidate.add_rule_step(
            AletheRule::Or,
            vec![not_forall, instance],
            vec![instantiated],
            Vec::new(),
        );
        candidate.add_resolution(vec![instance], forall_root, clausified, forall_assume)
    }

    /// The exact authored root that refutes `(= first second)`, in whichever
    /// orientation the author wrote it.
    ///
    /// Binary `(distinct u v)` is interned as `(not (= u v))`
    /// (`TermStore::mk_distinct`), so an authored `distinct` is found here
    /// without any special case. Returns the root together with the exact
    /// equality TermId the final resolution must pivot on.
    fn authored_disequality_for(
        &mut self,
        disequalities: &[(TermId, TermId)],
        first: TermId,
        second: TermId,
    ) -> Option<(TermId, TermId)> {
        for (left, right) in [(first, second), (second, first)] {
            let equality = self
                .ctx
                .terms
                .mk_app(Symbol::named("="), [left, right], Sort::Bool);
            if let Some(&(root, _)) = disequalities
                .iter()
                .find(|&&(_, refuted)| refuted == equality)
            {
                return Some((root, equality));
            }
        }
        None
    }

    /// Rebuild an EUF refutation whose equality chain needs one or two GROUND
    /// INSTANCES of an authored `forall` (#trust-count→0, the quantified
    /// left-inverse family).
    ///
    /// ROOT CAUSE. [`Self::replace_with_exact_authored_forall_inst_refutation`]
    /// closes only the shape where an authored `(not I)` root is the EXACT
    /// complement of the instantiated body, so the whole refutation is
    /// `forall_inst` plus one resolution. The deductive-checks box/unbox family is one
    /// step past that: the instance is an EQUALITY that has to be composed with
    /// the other authored roots before anything contradicts. On
    /// `false_control_left_inverse_image_disagreement_unsat_2774`
    ///
    /// ```text
    /// (assert (forall ((x (_ BitVec 32))) (= (Unbox_i32 (Box_i32 x)) x)))
    /// (assert (distinct c d))
    /// (assert (= (Unbox_i32 (Box_i32 c)) d))
    /// ```
    ///
    /// AY computes `unsat` every time — z3 5.0.0 agrees — and published
    /// `unknown`:
    ///
    /// ```text
    /// computed UNSAT rejected by mandatory strict certification: strict UNSAT
    /// proof validation failed: step t4 uses unverified trust rule
    /// ```
    ///
    /// THE FIX IS A DERIVATION, NOT A RELAXATION. Both arms below emit only
    /// steps the strict checker re-derives on its own:
    ///
    /// * ARM 1 — SHARED ENDPOINT. The instance `(= (Unbox (Box c)) c)` and the
    ///   authored `(= (Unbox (Box c)) d)` share an endpoint, so `eq_transitive`
    ///   yields `(= c d)`, which the authored `distinct` refutes directly.
    /// * ARM 2 — CONGRUENCE BRIDGE. Two instances `(= (Unbox (Box a)) a)` and
    ///   `(= (Unbox (Box b)) b)` are joined by a CONGRUENCE unit built from the
    ///   authored `(= (Box a) (Box b))` — the same
    ///   [`Self::derive_authored_congruence_unit`] the ground lane uses — and
    ///   the three-edge chain yields `(= a b)`, refuted by the authored
    ///   `distinct`. This is
    ///   `false_control_left_inverse_ground_non_injectivity_unsat_2774`.
    ///
    /// Nothing about either arm is decided producer-side.
    /// `validate_forall_inst` re-derives the exact simultaneous substitution
    /// and the groundness of every argument; `validate_euf_transitive` BFSes
    /// the premise equality graph for a genuine path between the conclusion's
    /// two endpoints (a chain that does not connect is rejected there);
    /// `validate_euf_congruent` re-checks one premise per argument position.
    /// The refuting disequality is not synthesized at all — it must be an EXACT
    /// authored root, so the pass cannot invent the fact that closes it.
    ///
    /// FAIL-CLOSED at every step, following
    /// [`Self::replace_with_exact_authored_store_permutation_refutation`]: it
    /// runs ONLY on a proof the strict checker already rejects; every `assume`
    /// is drawn from the exact authored scope; instantiation arguments are
    /// harvested only from OUTSIDE binders so nothing can capture; and the
    /// candidate replaces the proof only after
    /// `validate_reachable_assumes_in_problem_scope`,
    /// `proof_derives_empty_clause` and the PLAIN
    /// `check_proof_strict_with_datatypes` all accept it
    /// ([`Self::commit_if_strictly_checked`]). A misjudged candidate therefore
    /// costs completeness — the verdict stays `unknown` — and can never cost
    /// soundness.
    pub(super) fn replace_with_exact_authored_forall_inst_equality_refutation(
        &mut self,
        proof: &mut Proof,
    ) {
        /// Ground values tried per authored `forall`. Each survivor costs one
        /// substitution; declining past the bound leaves the verdict exactly as
        /// it is today.
        const MAX_GROUND_VALUES_PER_FORALL: usize = 24;
        /// Ground instances built across ALL authored `forall` roots. ARM 2
        /// pairs instances, so this also bounds its scan quadratically.
        const MAX_INSTANCES: usize = 96;
        /// Total strict replays this pass may spend on one refutation. The
        /// replay is the expensive step and this pass runs on every proof the
        /// strict checker rejects.
        const MAX_COMMIT_ATTEMPTS: usize = 48;
        /// Subterm-walk bound while harvesting instantiation values.
        const MAX_HARVEST_WORK: usize = 20_000;

        if self.check_proof_strict_with_datatypes(proof).is_ok() {
            return;
        }
        let authored = self.exact_concrete_authored_scope();

        // Authored positive equalities, kept with their exact root term so the
        // rebuilt proof assumes the authored syntax rather than a re-normalized
        // copy of it.
        let authored_equalities: Vec<(TermId, TermId, TermId)> = authored
            .iter()
            .filter_map(|&root| {
                decode_eq_local(&self.ctx.terms, root).map(|(lhs, rhs)| (root, lhs, rhs))
            })
            .collect();
        // Authored disequality roots, paired with the equality each refutes.
        let authored_disequalities: Vec<(TermId, TermId)> = authored
            .iter()
            .filter_map(|&root| match self.ctx.terms.get(root) {
                TermData::Not(inner) => {
                    let inner = *inner;
                    decode_eq_local(&self.ctx.terms, inner).map(|_| (root, inner))
                }
                _ => None,
            })
            .collect();
        // Both arms end at an authored disequality; with none there is nothing
        // for a derived equality chain to contradict.
        if authored_disequalities.is_empty() {
            return;
        }

        // Authored single-binder `forall` roots whose body is a QUANTIFIER-FREE
        // equality. A nested binder is skipped rather than approximated: the
        // strict `forall_inst` validator fails closed on one, so proposing it
        // could only produce a candidate it rejects.
        let foralls: Vec<(TermId, String, Sort, TermId)> = authored
            .iter()
            .filter_map(|&root| {
                let TermData::Forall(bindings, body, _) = self.ctx.terms.get(root) else {
                    return None;
                };
                let body = *body;
                let [(name, sort)] = bindings.as_slice() else {
                    return None;
                };
                let (name, sort) = (name.clone(), sort.clone());
                if crate::ematching::contains_quantifier(&self.ctx.terms, body) {
                    return None;
                }
                let _equality = decode_eq_local(&self.ctx.terms, body)?;
                Some((root, name, sort, body))
            })
            .collect();
        if foralls.is_empty() {
            return;
        }

        let ground_values =
            Self::collect_ground_instantiation_values(&self.ctx.terms, &authored, MAX_HARVEST_WORK);

        // Candidate ground instances: (forall root, argument, instance
        // equality, its two sides). The substitution is recomputed with the
        // certificate-producing `subst_vars_exact_qf` — the exact counterpart
        // of the checker's `forall_inst` matcher — so a shape it cannot express
        // declines here instead of being handed to the validator.
        let mut instances: Vec<(TermId, TermId, TermId, TermId, TermId)> = Vec::new();
        'harvest: for (forall_root, name, sort, body) in &foralls {
            let mut used = 0usize;
            for &value in &ground_values {
                // Substitution INTERNS terms, so the total is capped as well as
                // the per-`forall` share: a problem carrying many quantified
                // equalities must not grow the term store by thousands of dead
                // instances on a proof this pass will decline anyway.
                if instances.len() >= MAX_INSTANCES {
                    break 'harvest;
                }
                if used >= MAX_GROUND_VALUES_PER_FORALL {
                    break;
                }
                if self.ctx.terms.sort(value) != sort {
                    continue;
                }
                used += 1;
                let mut substitution = ay_core::kani_compat::DetHashMap::default();
                let _ = substitution.insert(name.clone(), value);
                let Some(instance) = crate::ematching::subst_vars_exact_qf(
                    &mut self.ctx.terms,
                    *body,
                    &substitution,
                ) else {
                    continue;
                };
                let Some((lhs, rhs)) = decode_eq_local(&self.ctx.terms, instance) else {
                    continue;
                };
                instances.push((*forall_root, value, instance, lhs, rhs));
            }
        }
        if instances.is_empty() {
            return;
        }

        let mut attempts = 0usize;

        // ARM 1 — one instance plus one authored equality sharing an endpoint.
        for &(forall_root, value, instance, instance_lhs, instance_rhs) in &instances {
            for &(equality_root, equality_lhs, equality_rhs) in &authored_equalities {
                let endpoint_pairs = [
                    (instance_lhs == equality_lhs, instance_rhs, equality_rhs),
                    (instance_lhs == equality_rhs, instance_rhs, equality_lhs),
                    (instance_rhs == equality_lhs, instance_lhs, equality_rhs),
                    (instance_rhs == equality_rhs, instance_lhs, equality_lhs),
                ];
                for (shares_endpoint, first, second) in endpoint_pairs {
                    if !shares_endpoint
                        || first == second
                        || self.ctx.terms.sort(first) != self.ctx.terms.sort(second)
                    {
                        continue;
                    }
                    let Some((disequality_root, endpoint_equality)) =
                        self.authored_disequality_for(&authored_disequalities, first, second)
                    else {
                        continue;
                    };
                    attempts += 1;
                    if attempts > MAX_COMMIT_ATTEMPTS {
                        return;
                    }

                    let mut candidate = Proof::new();
                    let instance_unit = self.derive_authored_forall_instance_unit(
                        &mut candidate,
                        forall_root,
                        &[value],
                        instance,
                    );
                    let equality_assume = candidate.add_assume(equality_root, None);
                    let not_instance = self.ctx.terms.mk_not_raw(instance);
                    let not_equality = self.ctx.terms.mk_not_raw(equality_root);
                    // (cl (not I) (not E) (= first second)) — the conclusion is
                    // last, as `validate_euf_transitive` requires.
                    let chain = candidate.add_rule_step(
                        AletheRule::EqTransitive,
                        vec![not_instance, not_equality, endpoint_equality],
                        Vec::new(),
                        Vec::new(),
                    );
                    let residual = candidate.add_resolution(
                        vec![not_equality, endpoint_equality],
                        instance,
                        chain,
                        instance_unit,
                    );
                    let endpoint_unit = candidate.add_resolution(
                        vec![endpoint_equality],
                        equality_root,
                        residual,
                        equality_assume,
                    );
                    let disequality_assume = candidate.add_assume(disequality_root, None);
                    candidate.add_resolution(
                        Vec::new(),
                        endpoint_equality,
                        endpoint_unit,
                        disequality_assume,
                    );

                    if self.commit_if_strictly_checked(proof, candidate, &authored) {
                        return;
                    }
                }
            }
        }

        // ARM 2 — two instances bridged by an authored congruence.
        for (left_index, &(left_forall, left_value, left_instance, left_lhs, left_rhs)) in
            instances.iter().enumerate()
        {
            for &(right_forall, right_value, right_instance, right_lhs, right_rhs) in
                instances.iter().skip(left_index + 1)
            {
                // Each instance offers two readings of which side is the
                // congruent application; the schema decides nothing here, the
                // checker's validators do.
                for (left_app, left_endpoint) in [(left_lhs, left_rhs), (left_rhs, left_lhs)] {
                    for (right_app, right_endpoint) in
                        [(right_lhs, right_rhs), (right_rhs, right_lhs)]
                    {
                        if !Self::is_distinct_same_symbol_application(
                            &self.ctx.terms,
                            left_app,
                            right_app,
                        ) || left_endpoint == right_endpoint
                            || self.ctx.terms.sort(left_endpoint)
                                != self.ctx.terms.sort(right_endpoint)
                        {
                            continue;
                        }
                        let Some((disequality_root, endpoint_equality)) = self
                            .authored_disequality_for(
                                &authored_disequalities,
                                left_endpoint,
                                right_endpoint,
                            )
                        else {
                            continue;
                        };
                        attempts += 1;
                        if attempts > MAX_COMMIT_ATTEMPTS {
                            return;
                        }

                        let mut candidate = Proof::new();
                        let Some((congruence_unit, congruence_equality)) = self
                            .derive_authored_congruence_unit(
                                &mut candidate,
                                left_app,
                                right_app,
                                &authored_equalities,
                            )
                        else {
                            continue;
                        };
                        let left_unit = self.derive_authored_forall_instance_unit(
                            &mut candidate,
                            left_forall,
                            &[left_value],
                            left_instance,
                        );
                        let right_unit = self.derive_authored_forall_instance_unit(
                            &mut candidate,
                            right_forall,
                            &[right_value],
                            right_instance,
                        );
                        // (cl (not I_l) (not (= app_l app_r)) (not I_r) (= e_l e_r))
                        let chain_clause = vec![
                            self.ctx.terms.mk_not_raw(left_instance),
                            self.ctx.terms.mk_not_raw(congruence_equality),
                            self.ctx.terms.mk_not_raw(right_instance),
                            endpoint_equality,
                        ];
                        let mut chain = candidate.add_rule_step(
                            AletheRule::EqTransitive,
                            chain_clause.clone(),
                            Vec::new(),
                            Vec::new(),
                        );
                        let mut remaining = chain_clause;
                        let mut discharged = true;
                        for (equality, support) in [
                            (left_instance, left_unit),
                            (congruence_equality, congruence_unit),
                            (right_instance, right_unit),
                        ] {
                            let negated = self.ctx.terms.mk_not_raw(equality);
                            let Some(position) =
                                remaining.iter().position(|&literal| literal == negated)
                            else {
                                discharged = false;
                                break;
                            };
                            let _ = remaining.remove(position);
                            chain = candidate.add_resolution(
                                remaining.clone(),
                                equality,
                                chain,
                                support,
                            );
                        }
                        if !discharged || remaining != vec![endpoint_equality] {
                            continue;
                        }
                        let disequality_assume = candidate.add_assume(disequality_root, None);
                        candidate.add_resolution(
                            Vec::new(),
                            endpoint_equality,
                            chain,
                            disequality_assume,
                        );

                        if self.commit_if_strictly_checked(proof, candidate, &authored) {
                            return;
                        }
                    }
                }
            }
        }
    }
}

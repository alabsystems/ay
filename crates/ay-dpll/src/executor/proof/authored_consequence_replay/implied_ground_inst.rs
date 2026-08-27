// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Ground-instantiation artifact-firewall translation for authored universals
//! that sit under an implication (#implied-forall-ground-inst).
//!
//! THE GAP THIS CLOSES, MEASURED. On the verification-consumer ext_eq push/pop refutation
//! (#7956) the engine reaches the correct semantic `Unsat` and then discards
//! it. The consequence-replay lane — the one producer that BUILDS an artifact
//! rather than consulting for one — runs, assembles 21 recorded `forall_inst`
//! instances and a 30-formula consequence set, hands it to the bounded
//! same-context probe, and the probe answers `Ok(Unknown)`. That reads like a
//! budget problem and is not one. Solved standalone, that exact 30-formula set
//! is **`sat` in 400 ms**: it is missing the single instance that carries the
//! refutation, namely the ext_eq pointwise universal at `i := 0`. Add that one
//! instance and the same set is **`unsat` in ~400 ms standalone** — well
//! inside the unchanged 2000 ms allowance. CAUTION, measured after the fact:
//! standalone timing does NOT transfer to the same-context probe by itself.
//! Two further defects had to fall before the probe matched it: the probe's
//! unscoped whole-store array-axiom scans (see
//! `Executor::shared_store_derived_query`) and the fused Generic conflict the
//! strict checker refused until the certified-EUF planner learned the
//! ROW-under-equality bridge (`CcReason::Row` in `proof_euf_lemma`).
//!
//! WHY THAT INSTANCE IS MISSING. The authored root is
//!
//! ```smt2
//! (assert (=> ext_eq_0
//!   (forall ((i Int)) (=> (and (>= i 0) (< i (seq_len vec)))
//!                         (= (seq_index_logic vec i) (seq_index_logic cat i))))))
//! ```
//!
//! with `(assert ext_eq_0)` also present. Every provenance path that can mint a
//! `forall_inst` record descends the authored roots through `and` ONLY —
//! `collect_unconditional_foralls`, `positive_and_spine_forall_conjuncts`, and
//! `authored_and_conjunct_closure` all stop at `=>`. So this universal is
//! reachable for SOLVING (`collect_entailed_foralls_with_units` does apply the
//! `#unit-conjunctive` rule, which is why the engine refutes at all) and
//! unreachable for PROVING. It is handled by CEGQI, whose counterexample lemma
//! is the negation of the universal and therefore not a consequence anything
//! may conjoin.
//!
//! THE FIX IS A DERIVATION, NOT A RELAXATION. `A` and `A => F` entail `F`, and
//! a universal entails every ground instance of its body, so for ground `t⃗`
//! drawn from the problem's own term set `F[t⃗]` is a sound consequence of two
//! authored roots. The stitcher's new [`ConsequencePlan::ImpliedConsequent`]
//! arm emits exactly:
//!
//! ```text
//! (assume h0 (or F (not A)))                  ; the authored implication root
//! (assume h1 A)                               ; the authored antecedent
//! (step d0 (cl (not h0-term) (not A) F) :rule implies_pos)
//! (step d1 (cl (not A) F)   :rule resolution :premises (d0 h0))
//! (step d2 (cl F)           :rule resolution :premises (d1 h1))
//! (step i0 (cl (or (not F) I)) :rule forall_inst :args (t⃗))
//! (step i1 (cl (not F) I)   :rule or          :premises (i0))
//! (step i2 (cl I)           :rule resolution :premises (i1 d2))
//! ```
//!
//! `implies_pos` and `forall_inst` are both in [`ay_core::CHECKABLE_ALETHE_RULES`]
//! with strict validators; no `trust` and no `hole` is introduced.
//!
//! NOTHING IS TAKEN ON THE PRODUCER'S WORD. The witness tuple is a pure hint:
//! `validate_implies_pos` re-derives the implication's own two literals,
//! `validate_forall_inst` re-derives binder/argument arity and sorts, argument
//! groundness, and the exact simultaneous substitution, and the probe's ground
//! steps are replayed by the outer strict checker over the authored scope. A
//! wrong witness or a still-satisfiable consequence set can only cost a
//! declined candidate.
//!
//! UNSAT-ONLY. Consulted at exactly one place — the artifact firewall's
//! downgrade — so its only reachable transition is `unknown -> unsat`, and it
//! installs `last_proof` only through the shared consequence-replay
//! installation boundary, which re-gates over the exact authored scope. Kill
//! switch: the parent `--no-consequence-replay` (and
//! `--no-quant-unit-authority`), both checked here and again inside the
//! stitcher.

use super::super::authored_negated_exists_ground_inst::bounded_tuples;
use super::types::{AndConjunctClosure, ConsequencePlan, ImpliedForall};
use super::*;

/// Authored-scope size beyond which this lane declines.
const MAX_AUTHORED_ROOTS: usize = 64;
/// Implication roots with a universal consequent considered per public query.
const MAX_IMPLIED_ROOTS: usize = 4;
/// Ground instances added to the probe's consequence set, across all roots.
const MAX_GROUND_INSTANCES: usize = 12;
/// Binder count beyond which the tuple enumeration declines outright.
const MAX_BINDERS: usize = 2;
/// Probe attempts this lane may consume per public check-sat.
const MAX_LANE_ATTEMPTS: u8 = 1;

/// Decline attribution. Deliberately `tracing`, not a `--debug-cert`
/// `eprintln!`: the per-check-sat leg attribution this lane feeds is printed
/// once, at the firewall itself.
fn note(message: impl FnOnce() -> String) {
    tracing::debug!(target: "ay::cert::implied_forall_inst", "{}", message());
}

impl Executor {
    /// Artifact-firewall translation: turn the semantic refutation of a query
    /// whose decisive universal sits under an authored implication into an
    /// authored-scope strict certificate and install it as `last_proof`.
    ///
    /// Returns `true` only when a complete, scope-authorized, strict-checkable
    /// certificate was installed; on `false` the caller keeps the fail-closed
    /// firewall path and every byte of proof state is left as found.
    ///
    /// SOUNDNESS: the installed proof is re-checked from scratch by the
    /// mandatory certification mint before any verdict is published, so a
    /// mis-built certificate can only cost the firewall's `unknown`.
    pub(in crate::executor) fn try_translate_implied_forall_ground_instantiation_unsat(
        &mut self,
    ) -> bool {
        if !crate::quant_unit_authority::consequence_replay_enabled()
            || !crate::quant_unit_authority::quant_unit_authority_enabled()
        {
            return false;
        }
        let attempts = self.implied_forall_ground_inst_attempts.get();
        if attempts >= MAX_LANE_ATTEMPTS {
            note(|| "decline: lane attempt budget exhausted".into());
            return false;
        }
        let authored = self.exact_concrete_authored_scope();
        if authored.is_empty() || authored.len() > MAX_AUTHORED_ROOTS {
            return false;
        }
        let Some((implied, records)) = self.plan_implied_forall_ground_instances(&authored) else {
            return false;
        };
        self.implied_forall_ground_inst_attempts.set(attempts + 1);
        let installed =
            self.try_translate_authored_consequence_replay_unsat_with_implied(&records, &implied);
        note(|| {
            format!(
                "translate: implied={} instances={} installed={installed}",
                implied.len(),
                records.len()
            )
        });
        installed
    }

    /// Build the implied-forall / instance plan, or `None` when nothing is
    /// proposable. Every returned record is a HINT; the stitcher and the strict
    /// checker re-derive all of it.
    fn plan_implied_forall_ground_instances(
        &mut self,
        authored: &[TermId],
    ) -> Option<(
        Vec<ImpliedForall>,
        Vec<crate::ematching::ForallInstantiationProvenance>,
    )> {
        let roots = self.exact_authored_implied_forall_roots(authored);
        if roots.is_empty() {
            note(|| "decline: no authored implication with a universal consequent".into());
            return None;
        }
        let bound_names = self.authored_binder_names(authored);

        let mut implied: Vec<ImpliedForall> = Vec::new();
        let mut records: Vec<crate::ematching::ForallInstantiationProvenance> = Vec::new();
        for (implication, antecedent, forall) in roots.into_iter().take(MAX_IMPLIED_ROOTS) {
            let TermData::Forall(bindings, body, _) = self.ctx.terms.get(forall).clone() else {
                continue;
            };
            if bindings.is_empty()
                || bindings.len() > MAX_BINDERS
                || crate::ematching::contains_quantifier(&self.ctx.terms, body)
            {
                continue;
            }
            let slots = Self::binder_argument_slots(&self.ctx.terms, body, &bindings);
            let mut per_binder: Vec<Vec<TermId>> = Vec::with_capacity(bindings.len());
            for (name, sort) in &bindings {
                // Trigger discipline, MEASURED: the generic subterm scan
                // proposes every Int-sorted authored subterm, and on #7956
                // that is 8 witnesses — 7 junk instances whose nested
                // select/offset terms push the same-context probe past its
                // unchanged 2000 ms grant (2003 ms, `Ok(Unknown)`). Witnesses
                // drawn from ground ARGUMENT positions of the very symbols
                // the body applies to the binder (here `seq_index_logic _ 0`,
                // giving exactly `0`) leave the probe the 31-formula load
                // measured to close in 317 ms. The generic scan remains only
                // as a fallback when no slot witness exists.
                let mut candidates =
                    self.slot_ground_witnesses(authored, &slots, name, sort, &bound_names);
                if candidates.is_empty() {
                    candidates = self.ground_witnesses_for_sort(authored, sort, &bound_names);
                    Self::order_witnesses_smallest_first(&self.ctx.terms, &mut candidates);
                }
                if candidates.is_empty() {
                    break;
                }
                per_binder.push(candidates);
            }
            if per_binder.len() != bindings.len() {
                note(|| "decline: a binder sort has no ground witness in scope".into());
                continue;
            }

            let mut minted = 0usize;
            for tuple in bounded_tuples(&per_binder, MAX_GROUND_INSTANCES - records.len()) {
                let mut substitution: ay_core::kani_compat::DetHashMap<String, TermId> =
                    ay_core::kani_compat::DetHashMap::default();
                for ((name, _), &value) in bindings.iter().zip(&tuple) {
                    substitution.insert(name.clone(), value);
                }
                let Some(instance) =
                    crate::ematching::subst_vars_exact_qf(&mut self.ctx.terms, body, &substitution)
                else {
                    continue;
                };
                if crate::ematching::contains_quantifier(&self.ctx.terms, instance) {
                    continue;
                }
                note(|| {
                    format!(
                        "mint: instance {}",
                        ay_proof::render_term_canonical(&self.ctx.terms, instance)
                    )
                });
                records.push(crate::ematching::ForallInstantiationProvenance {
                    quantifier: forall,
                    binding: tuple,
                    instance,
                });
                minted += 1;
                if records.len() >= MAX_GROUND_INSTANCES {
                    break;
                }
            }
            if minted > 0 {
                implied.push(ImpliedForall {
                    implication,
                    antecedent,
                    forall,
                });
            }
            if records.len() >= MAX_GROUND_INSTANCES {
                break;
            }
        }
        if records.is_empty() {
            note(|| "decline: no ground instance proposable".into());
            return None;
        }
        Some((implied, records))
    }

    /// Authored roots of shape `(=> A F)` — or the desugared two-literal
    /// `(or F (not A))` the frontend actually stores — whose consequent `F` is
    /// a `Forall` and whose antecedent `A` is ITSELF an exact authored root.
    ///
    /// Requiring `A` to be an authored root (rather than merely entailed) is
    /// the narrow, checkable version of the `#unit-conjunctive` rule: it is
    /// what makes `(cl A)` an `assume` the strict scope validator accepts. The
    /// stitcher re-checks membership in the authored `and`-conjunct closure
    /// before emitting anything.
    fn exact_authored_implied_forall_roots(
        &self,
        authored: &[TermId],
    ) -> Vec<(TermId, TermId, TermId)> {
        let authored_set: ay_core::kani_compat::DetHashSet<TermId> =
            authored.iter().copied().collect();
        let mut out = Vec::new();
        for &root in authored {
            let Some((antecedent, consequent)) =
                Self::decode_implication_local(&self.ctx.terms, root)
            else {
                continue;
            };
            if !authored_set.contains(&antecedent)
                || !matches!(self.ctx.terms.get(consequent), TermData::Forall(..))
            {
                continue;
            }
            out.push((root, antecedent, consequent));
        }
        out
    }

    /// Argument slots `(symbol, position)` at which the universal's body
    /// applies a function directly to one of its binders. These are the
    /// body's own trigger shapes: any ground term the authored scope puts in
    /// such a slot is a witness the refutation could actually need.
    fn binder_argument_slots(
        terms: &TermStore,
        body: TermId,
        bindings: &[(String, Sort)],
    ) -> ay_core::kani_compat::DetHashSet<(Symbol, usize, String)> {
        const MAX_SCAN_WORK: usize = 20_000;
        let binder_names: ay_core::kani_compat::DetHashSet<&str> =
            bindings.iter().map(|(name, _)| name.as_str()).collect();
        let mut slots = ay_core::kani_compat::DetHashSet::default();
        let mut seen = ay_core::kani_compat::DetHashSet::default();
        let mut stack = vec![body];
        while let Some(term) = stack.pop() {
            if !seen.insert(term) || seen.len() > MAX_SCAN_WORK {
                continue;
            }
            match terms.get(term) {
                TermData::App(symbol, args) => {
                    for (position, &arg) in args.iter().enumerate() {
                        if let TermData::Var(name, _) = terms.get(arg) {
                            if let Some(&binder) = binder_names.get(name.as_str()) {
                                slots.insert((symbol.clone(), position, binder.to_string()));
                            }
                        }
                    }
                    stack.extend(args.iter().copied());
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(condition, then_branch, else_branch) => {
                    stack.extend([*condition, *then_branch, *else_branch]);
                }
                _ => {}
            }
        }
        slots
    }

    /// Ground witnesses for `binder` drawn from the authored scope's OWN
    /// occupants of the body's binder slots: for every slot `(f, k)` the body
    /// gives this binder, every ground authored `(f ... t_k ...)` proposes
    /// `t_k`. Deterministic order, deduplicated, bounded. Purely a hint —
    /// `validate_forall_inst` re-derives sort and substitution for every
    /// proposal, so a junk witness can only cost probe time.
    fn slot_ground_witnesses(
        &self,
        authored: &[TermId],
        slots: &ay_core::kani_compat::DetHashSet<(Symbol, usize, String)>,
        binder: &str,
        sort: &Sort,
        bound_names: &ay_core::kani_compat::DetHashSet<String>,
    ) -> Vec<TermId> {
        const MAX_SCAN_WORK: usize = 20_000;
        const MAX_SLOT_WITNESSES: usize = 8;
        let terms = &self.ctx.terms;
        let mut found: Vec<TermId> = Vec::new();
        let mut seen = ay_core::kani_compat::DetHashSet::default();
        let mut stack = authored.to_vec();
        while let Some(term) = stack.pop() {
            if !seen.insert(term) || seen.len() > MAX_SCAN_WORK {
                continue;
            }
            if found.len() >= MAX_SLOT_WITNESSES {
                break;
            }
            match terms.get(term) {
                TermData::App(symbol, args) => {
                    for (position, &arg) in args.iter().enumerate() {
                        if slots.contains(&(symbol.clone(), position, binder.to_string()))
                            && terms.sort(arg) == sort
                            && !found.contains(&arg)
                            && !crate::ematching::contains_quantifier(terms, arg)
                            && self.term_avoids_names(arg, bound_names)
                        {
                            found.push(arg);
                        }
                    }
                    stack.extend(args.iter().copied());
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(condition, then_branch, else_branch) => {
                    stack.extend([*condition, *then_branch, *else_branch]);
                }
                _ => {}
            }
        }
        found
    }

    /// Stable smallest-terms-first order for fallback witnesses, so the
    /// bounded tuple enumeration spends its budget on the structurally
    /// simplest candidates before nested composites.
    fn order_witnesses_smallest_first(terms: &TermStore, candidates: &mut [TermId]) {
        fn node_count(terms: &TermStore, root: TermId) -> usize {
            const MAX_COUNT_WORK: usize = 512;
            let mut count = 0usize;
            let mut stack = vec![root];
            while let Some(term) = stack.pop() {
                count += 1;
                if count >= MAX_COUNT_WORK {
                    break;
                }
                match terms.get(term) {
                    TermData::App(_, args) => stack.extend(args.iter().copied()),
                    TermData::Not(inner) => stack.push(*inner),
                    TermData::Ite(condition, then_branch, else_branch) => {
                        stack.extend([*condition, *then_branch, *else_branch]);
                    }
                    _ => {}
                }
            }
            count
        }
        candidates.sort_by_key(|&candidate| node_count(terms, candidate));
    }

    /// Admit authored implication consequents as instance SOURCES and return
    /// the set of universals the instance planner may then draw on.
    ///
    /// An implied forall carries NO authority: the implication root AND the
    /// antecedent must both be derivable from the authored scope, and
    /// `consequence_unit` mints `(cl F)` only through an `implies_pos` step the
    /// strict checker re-derives from the implication itself.
    pub(super) fn plan_implied_foralls(
        extra_implied: &[ImpliedForall],
        derivable_sources: &AndConjunctClosure,
        instance_plan: &mut ay_core::kani_compat::DetHashMap<TermId, ConsequencePlan>,
    ) -> ay_core::kani_compat::DetHashSet<TermId> {
        let mut implied_foralls: ay_core::kani_compat::DetHashSet<TermId> =
            ay_core::kani_compat::DetHashSet::default();
        for implied in extra_implied {
            if !derivable_sources.contains(&implied.implication)
                || !derivable_sources.contains(&implied.antecedent)
                || instance_plan.contains_key(&implied.forall)
            {
                continue;
            }
            instance_plan.insert(
                implied.forall,
                ConsequencePlan::ImpliedConsequent {
                    implication: implied.implication,
                    antecedent: implied.antecedent,
                },
            );
            implied_foralls.insert(implied.forall);
        }
        implied_foralls
    }

    /// Derive `(cl consequent)` from an ALREADY-DERIVED `(cl implication)`,
    /// first deriving the antecedent's own unit from the authored scope.
    ///
    /// The antecedent goes through the same recursive unit machinery as any
    /// other consequence, so it may itself be an authored root, an
    /// `and`-conjunct projection, or another planned consequence.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn add_implied_consequent_unit(
        &mut self,
        candidate: &mut Proof,
        implication_unit: ProofId,
        implication: TermId,
        antecedent: TermId,
        consequent: TermId,
        authored_set: &ay_core::kani_compat::DetHashSet<TermId>,
        authored: &[TermId],
        instance_plan: &ay_core::kani_compat::DetHashMap<TermId, ConsequencePlan>,
        unit_ids: &mut ay_core::kani_compat::DetHashMap<TermId, ProofId>,
    ) -> Option<ProofId> {
        let antecedent_unit = self.consequence_unit(
            candidate,
            antecedent,
            authored_set,
            authored,
            instance_plan,
            unit_ids,
        )?;
        Some(self.apply_implication_unit(
            candidate,
            implication,
            implication_unit,
            antecedent,
            antecedent_unit,
            consequent,
        ))
    }
}

#[cfg(test)]
#[path = "implied_ground_inst_tests.rs"]
mod tests;

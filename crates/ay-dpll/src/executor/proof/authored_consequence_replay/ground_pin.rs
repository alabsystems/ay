// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Strict direct refutations from recorded instances and authored value pins.
//!
//! `GroundEqualitySubstitution` is authenticated by AY's native strict checker
//! but has no checked external Alethe spelling. The ordinary native/default
//! result may publish; `:check-proofs-strict true` remains fail-closed.

use super::*;

mod bounds;

const MAX_PINS: usize = 16;
const MAX_CANDIDATE_CHECKS: usize = 4;
/// Shared walk budget for one direct-replay attempt, across all candidate
/// instances and equality pins.
const MAX_OCCURRENCE_WORK: usize = 100_000;
/// Recursive `TermStore::substitute_terms` is safe only after this iterative
/// preflight bounds the longest path through the whole candidate instance.
const MAX_INSTANCE_DEPTH: usize = 512;

#[derive(Clone, Copy)]
struct GroundPin {
    source: TermId,
    /// Key-on-left orientation used by the substitution lemma.
    equality: TermId,
    key: TermId,
    value: TermId,
}

fn fingerprint_mix(state: &mut u64, value: u64) {
    *state ^= value;
    *state = state.wrapping_mul(0x100_0000_01b3);
}

impl Executor {
    pub(super) fn try_distinct_ground_pin(
        &mut self,
        plans: &ay_core::kani_compat::DetHashMap<TermId, ConsequencePlan>,
        instances: &[TermId],
    ) -> Option<Proof> {
        let fingerprint = Self::ground_pin_input_fingerprint(plans, instances);
        let direct_state = self.consequence_replay_direct_state.get();
        let already_tried = direct_state.is_some_and(|(last, _)| last == fingerprint);
        let attempts = direct_state.map_or(0, |(_, attempts)| attempts);
        if already_tried || attempts >= MAX_DIRECT_REPLAY_ATTEMPTS {
            return None;
        }
        self.consequence_replay_direct_state
            .set(Some((fingerprint, attempts + 1)));
        let authored = self.exact_concrete_authored_scope();
        let closure = self.authored_and_conjunct_closure(&authored);
        self.try_ground_pinned_instance_refutation(&authored, &closure, plans, instances)
    }

    /// Fingerprint the exact ordered direct-replay plan. A collision can only
    /// skip a completeness attempt; every accepted proof is still strict.
    pub(super) fn ground_pin_input_fingerprint(
        plans: &ay_core::kani_compat::DetHashMap<TermId, ConsequencePlan>,
        instances: &[TermId],
    ) -> u64 {
        let mut state = 0xcbf2_9ce4_8422_2325;
        fingerprint_mix(&mut state, instances.len() as u64);
        for instance in instances {
            fingerprint_mix(&mut state, u64::from(instance.0));
            match plans.get(instance) {
                Some(ConsequencePlan::ForallInstance {
                    quantifier,
                    binding,
                }) => {
                    fingerprint_mix(&mut state, 1);
                    fingerprint_mix(&mut state, u64::from(quantifier.0));
                    fingerprint_mix(&mut state, binding.len() as u64);
                    for value in binding {
                        fingerprint_mix(&mut state, u64::from(value.0));
                    }
                    // A recorded forall instance may be authorized through a
                    // negated-existential dual plan stored under its source
                    // quantifier. Include that transitive authority edge so a
                    // newly admitted dual plan receives its own bounded scan.
                    match plans.get(quantifier) {
                        Some(ConsequencePlan::NegatedExistsDual {
                            not_exists_root,
                            exists,
                        }) => {
                            fingerprint_mix(&mut state, 5);
                            fingerprint_mix(&mut state, u64::from(not_exists_root.0));
                            fingerprint_mix(&mut state, u64::from(exists.0));
                        }
                        Some(_) => fingerprint_mix(&mut state, 6),
                        None => fingerprint_mix(&mut state, 7),
                    }
                }
                Some(ConsequencePlan::SkolemInstance {
                    source,
                    quantified,
                    witness,
                    instance,
                    positive,
                }) => {
                    fingerprint_mix(&mut state, 2 + u64::from(*positive));
                    for term in [source, quantified, witness, instance] {
                        fingerprint_mix(&mut state, u64::from(term.0));
                    }
                }
                Some(ConsequencePlan::NegatedExistsDual {
                    not_exists_root,
                    exists,
                }) => {
                    fingerprint_mix(&mut state, 4);
                    fingerprint_mix(&mut state, u64::from(not_exists_root.0));
                    fingerprint_mix(&mut state, u64::from(exists.0));
                }
                Some(ConsequencePlan::ImpliedConsequent {
                    implication,
                    antecedent,
                }) => {
                    fingerprint_mix(&mut state, 8);
                    fingerprint_mix(&mut state, u64::from(implication.0));
                    fingerprint_mix(&mut state, u64::from(antecedent.0));
                }
                None => fingerprint_mix(&mut state, 0),
            }
        }
        state
    }

    /// Build a strict refutation from one exact ground instance and authored
    /// equalities that pin its ground applications to literal values.
    pub(super) fn try_ground_pinned_instance_refutation(
        &mut self,
        authored: &[TermId],
        derivable_sources: &AndConjunctClosure,
        instance_plan: &ay_core::kani_compat::DetHashMap<TermId, ConsequencePlan>,
        instances: &[TermId],
    ) -> Option<Proof> {
        let mut occurrence_work = MAX_OCCURRENCE_WORK;
        let mut candidate_checks = 0_usize;
        for &instance in instances {
            if !Self::ground_instance_within_budget(&self.ctx.terms, instance, &mut occurrence_work)
            {
                continue;
            }
            replay_note(|| {
                format!(
                    "ground-pin attempt: instance {instance:?} = {}",
                    ay_proof::render_term_canonical(&self.ctx.terms, instance)
                )
            });
            let Some(pins) =
                self.collect_ground_pins(derivable_sources, instance, &mut occurrence_work)
            else {
                continue;
            };
            let replacements = pins.iter().map(|pin| (pin.key, pin.value)).collect();
            let substituted = self.ctx.terms.substitute_terms(instance, &replacements);
            let pairs: Vec<_> = pins.iter().map(|pin| (pin.key, pin.value)).collect();
            if !ay_proof::ground_substitution_image_matches(
                &self.ctx.terms,
                instance,
                substituted,
                &pairs,
            ) {
                continue;
            }
            if let Some(candidate) = self.build_ground_pin_candidate(
                authored,
                instance_plan,
                instance,
                substituted,
                &pins,
            ) {
                candidate_checks += 1;
                if self.ground_pin_candidate_is_strict(&candidate, authored) {
                    replay_note(|| {
                        format!(
                            "ground-pin built strict candidate for {instance:?} from {} pin(s)",
                            pins.len()
                        )
                    });
                    return Some(candidate);
                }
                if candidate_checks >= MAX_CANDIDATE_CHECKS {
                    return None;
                }
            }
        }
        None
    }

    fn ground_pin_candidate_is_strict(&mut self, candidate: &Proof, authored: &[TermId]) -> bool {
        ay_proof::validate_reachable_assumes_in_problem_scope(candidate, authored).is_ok()
            && Self::proof_derives_empty_clause(candidate)
            && self
                .check_proof_strict_with_datatypes(candidate)
                .is_ok_and(|quality| quality.is_complete())
    }

    fn collect_ground_pins(
        &mut self,
        derivable_sources: &AndConjunctClosure,
        instance: TermId,
        occurrence_work: &mut usize,
    ) -> Option<Vec<GroundPin>> {
        let mut pins = Vec::new();
        let mut value_by_key = ay_core::kani_compat::DetHashMap::default();
        for &source in &derivable_sources.ordered {
            if *occurrence_work == 0 {
                return None;
            }
            let Some(pin) = self.ground_pin_from_source(source, instance, occurrence_work) else {
                continue;
            };
            match value_by_key.get(&pin.key) {
                Some(&prior) if prior != pin.value => return None,
                Some(_) => continue,
                None if pins.len() >= MAX_PINS => return None,
                None => {
                    value_by_key.insert(pin.key, pin.value);
                    pins.push(pin);
                }
            }
        }
        (!pins.is_empty()).then_some(pins)
    }

    fn ground_pin_from_source(
        &mut self,
        source: TermId,
        instance: TermId,
        occurrence_work: &mut usize,
    ) -> Option<GroundPin> {
        let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(source).clone() else {
            return None;
        };
        if name != "=" || args.len() != 2 {
            return None;
        }
        let (key, value, equality) = if !matches!(self.ctx.terms.get(args[0]), TermData::Const(_))
            && matches!(self.ctx.terms.get(args[1]), TermData::Const(_))
        {
            (args[0], args[1], source)
        } else if matches!(self.ctx.terms.get(args[0]), TermData::Const(_))
            && !matches!(self.ctx.terms.get(args[1]), TermData::Const(_))
        {
            let equality =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("="), [args[1], args[0]], Sort::Bool);
            (args[1], args[0], equality)
        } else {
            return None;
        };
        if self.ctx.terms.sort(key) != self.ctx.terms.sort(value) {
            return None;
        }
        let occurs = Self::term_occurs_bounded(&self.ctx.terms, key, instance, occurrence_work);
        replay_note(|| {
            format!(
                "ground-pin equality candidate {source:?}: key={} value={} key-occurs={occurs}",
                ay_proof::render_term_canonical(&self.ctx.terms, key),
                ay_proof::render_term_canonical(&self.ctx.terms, value),
            )
        });
        occurs.then_some(GroundPin {
            source,
            equality,
            key,
            value,
        })
    }

    fn build_ground_pin_candidate(
        &mut self,
        authored: &[TermId],
        instance_plan: &ay_core::kani_compat::DetHashMap<TermId, ConsequencePlan>,
        instance: TermId,
        substituted: TermId,
        pins: &[GroundPin],
    ) -> Option<Proof> {
        let authored_set = authored.iter().copied().collect();
        let mut candidate = Proof::new();
        let mut unit_ids = ay_core::kani_compat::DetHashMap::default();
        let instance_unit = self.consequence_unit(
            &mut candidate,
            instance,
            &authored_set,
            authored,
            instance_plan,
            &mut unit_ids,
        )?;
        let (mut current, mut residual) =
            self.add_ground_substitution_lemma(&mut candidate, instance, substituted, pins)?;
        for &pin in pins {
            let equality_unit = self.ground_pin_equality_unit(
                &mut candidate,
                pin,
                &authored_set,
                authored,
                instance_plan,
                &mut unit_ids,
            )?;
            let negated = self.ctx.terms.mk_not_raw(pin.equality);
            residual.retain(|&literal| literal != negated);
            current =
                candidate.add_resolution(residual.clone(), pin.equality, current, equality_unit);
        }
        residual.retain(|&literal| literal != self.ctx.terms.mk_not_raw(instance));
        current = candidate.add_resolution(residual.clone(), instance, current, instance_unit);
        if residual != [substituted] {
            return None;
        }
        let negated_unit = self.add_closed_false_unit(&mut candidate, substituted)?;
        candidate.add_resolution(Vec::new(), substituted, current, negated_unit);
        Some(candidate)
    }

    fn add_ground_substitution_lemma(
        &mut self,
        candidate: &mut Proof,
        instance: TermId,
        substituted: TermId,
        pins: &[GroundPin],
    ) -> Option<(ProofId, Vec<TermId>)> {
        let mut clause: Vec<_> = pins
            .iter()
            .map(|pin| self.ctx.terms.mk_not_raw(pin.equality))
            .collect();
        clause.push(self.ctx.terms.mk_not_raw(instance));
        clause.push(substituted);
        if !ay_proof::recognize_ground_equality_substitution(&self.ctx.terms, &clause) {
            return None;
        }
        let step = candidate.add_step(ProofStep::TheoryLemma {
            theory: "EUF".to_owned(),
            clause: clause.clone(),
            farkas: None,
            kind: TheoryLemmaKind::GroundEqualitySubstitution,
            lia: None,
        });
        Some((step, clause))
    }

    fn ground_pin_equality_unit(
        &mut self,
        candidate: &mut Proof,
        pin: GroundPin,
        authored_set: &ay_core::kani_compat::DetHashSet<TermId>,
        authored: &[TermId],
        instance_plan: &ay_core::kani_compat::DetHashMap<TermId, ConsequencePlan>,
        unit_ids: &mut ay_core::kani_compat::DetHashMap<TermId, ProofId>,
    ) -> Option<ProofId> {
        let source_unit = self.consequence_unit(
            candidate,
            pin.source,
            authored_set,
            authored,
            instance_plan,
            unit_ids,
        )?;
        if pin.source == pin.equality {
            return Some(source_unit);
        }
        let equivalence =
            self.ctx
                .terms
                .mk_app(Symbol::named("="), [pin.source, pin.equality], Sort::Bool);
        let symmetric = candidate.add_rule_step(
            AletheRule::EqSymmetric,
            vec![equivalence],
            Vec::new(),
            Vec::new(),
        );
        let not_equivalence = self.ctx.terms.mk_not_raw(equivalence);
        let not_source = self.ctx.terms.mk_not_raw(pin.source);
        let TermData::App(_, args) = self.ctx.terms.get(equivalence) else {
            return None;
        };
        let implication_clause = if args.first() == Some(&pin.source) {
            vec![not_equivalence, not_source, pin.equality]
        } else if args.first() == Some(&pin.equality) {
            vec![not_equivalence, pin.equality, not_source]
        } else {
            return None;
        };
        let implication = candidate.add_rule_step(
            if args.first() == Some(&pin.source) {
                AletheRule::EquivPos2
            } else {
                AletheRule::EquivPos1
            },
            implication_clause,
            Vec::new(),
            Vec::new(),
        );
        let bridge = candidate.add_resolution(
            vec![not_source, pin.equality],
            equivalence,
            implication,
            symmetric,
        );
        Some(candidate.add_resolution(vec![pin.equality], pin.source, bridge, source_unit))
    }

    fn add_closed_false_unit(
        &mut self,
        candidate: &mut Proof,
        substituted: TermId,
    ) -> Option<ProofId> {
        let false_term = self.ctx.terms.false_term();
        let equality =
            self.ctx
                .terms
                .mk_app(Symbol::named("="), [substituted, false_term], Sort::Bool);
        let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(equality) else {
            return None;
        };
        if name != "="
            || args.as_slice() != [substituted, false_term]
            || !ay_proof::recognize_ground_evaluate(&self.ctx.terms, equality)
        {
            return None;
        }
        let evaluated =
            candidate.add_rule_step(AletheRule::Evaluate, vec![equality], Vec::new(), Vec::new());
        let not_equality = self.ctx.terms.mk_not_raw(equality);
        let not_substituted = self.ctx.terms.mk_not_raw(substituted);
        let equivalence = candidate.add_rule_step(
            AletheRule::EquivPos2,
            vec![not_equality, not_substituted, false_term],
            Vec::new(),
            Vec::new(),
        );
        let with_false = candidate.add_resolution(
            vec![not_substituted, false_term],
            equality,
            equivalence,
            evaluated,
        );
        let not_false = self.ctx.terms.mk_not_raw(false_term);
        // `AletheRule::False`, NOT `True` (#alethe-false-axiom-mislabel, second
        // of two sites). The clause is exactly `(cl (not false))`, which is
        // Alethe's `false` axiom — as the local name `false_unit` says. Under
        // `True` the printer demoted it to `hole`, correctly: a `true` whose
        // printed conclusion is not `(cl true)` is a MISAPPLIED real rule, and
        // carcara answers `invalid` for the whole document rather than `holey`.
        //
        // Every other site in the tree that builds a `not_false` unit already
        // labels it `False` (`proof.rs`, `finite_select_surface.rs`); these two
        // were the outliers. This one matters most: unlike the closed-universal
        // lane, `authored_consequence_replay` publishes in the DEFAULT posture,
        // so the mislabel put an unverifiable step into shipped certificates.
        let false_unit =
            candidate.add_rule_step(AletheRule::False, vec![not_false], Vec::new(), Vec::new());
        Some(candidate.add_resolution(vec![not_substituted], false_term, false_unit, with_false))
    }
}

#[cfg(test)]
mod tests;

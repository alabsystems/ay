// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Proof-first point consequences of the complete original native query.

use super::NativeUniversalSource;

mod refutation;
#[cfg(test)]
mod tests;
use crate::executor::Executor;
use crate::proof_tracker::ProofTracker;
use ay_core::{
    AletheRule, Proof, ProofId, Sort, Symbol, TermData, TermId, TermStore, TheoryLemmaKind,
};

#[derive(Clone, Copy)]
enum ChoiceKind {
    Exists,
    NegativeForall,
}

#[derive(Clone, Copy)]
struct Choice {
    original: TermId,
    quantified: TermId,
    witness: TermId,
    raw: TermId,
    kind: ChoiceKind,
}

enum Universal {
    Original(TermId),
    NegatedExists {
        original: TermId,
        exists: TermId,
        dual: TermId,
    },
}

impl Universal {
    fn quantified(&self) -> TermId {
        match *self {
            Self::Original(q) => q,
            Self::NegatedExists { dual, .. } => dual,
        }
    }
}

impl Executor {
    /// Only a genuine native source window may move restoration before the
    /// new producer. Text/mixed and unsupported windows keep their existing
    /// post-fold snapshot path. This is restoration data, not proof authority.
    pub(in crate::executor) fn native_source_offer_restoration_preimage(
        &self,
    ) -> Option<Vec<TermId>> {
        if !self.produce_proofs_enabled() {
            return None;
        }
        NativeUniversalSource::capture(self)?;
        self.charge_native_universal(
            self.ctx.assertions.len(),
            self.ctx
                .assertions
                .len()
                .checked_mul(std::mem::size_of::<TermId>())?,
        )?;
        Some(self.ctx.assertions.clone())
    }

    /// Offer no unproved working fact. This runs after original provenance and
    /// the restoration snapshot, before finite expansion can erase an original
    /// quantified source. Refusal preserves all ordinary publication gates.
    pub(in crate::executor) fn offer_native_quantified_source_units(&mut self) -> Option<()> {
        if !self.produce_proofs_enabled() {
            return Some(());
        }
        let initial = NativeUniversalSource::capture(self)?;
        self.native_universal_budget
            .borrow_mut()
            .claim_source_offers()?;
        let (source, choices, universals) = self.plan_native_source_offers(initial, true)?;
        for choice in &choices {
            self.charge_native_universal(1024, 16 * 1024)?;
            let (fragment, raw_literal) = self.native_source_produce(|terms, _, progress| {
                choice_fragment(terms, choice, progress)
            })?;
            let target = self.native_source_produce(|terms, _, progress| {
                nnf(
                    terms,
                    raw_literal,
                    Polarity::Positive,
                    progress,
                    0,
                    &mut 4096,
                )
            })?;
            let fragment = self.native_source_produce(|terms, _, progress| {
                normalize_fragment(terms, fragment, raw_literal, target, progress)
            })?;
            self.install_native_source_unit(&source, fragment, target)?;
            self.replace_native_source_working_unit(choice.original, target)?;
            // Actual producer custody for existing SAT/model/proof consumers;
            // no second Skolemizer will see this replaced source occurrence.
            self.charge_native_universal(
                self.skolem_instance_records
                    .len()
                    .checked_add(self.skolem_witness_records.len())?,
                self.skolem_instance_records
                    .len()
                    .checked_add(1)?
                    .checked_mul(2)?
                    .checked_mul(std::mem::size_of::<crate::executor::SkolemInstanceRecord>())?
                    .checked_add(
                        self.skolem_witness_records
                            .len()
                            .checked_add(1)?
                            .checked_mul(2)?
                            .checked_mul(
                                std::mem::size_of::<crate::executor::SkolemWitnessRecord>(),
                            )?,
                    )?,
            )?;
            self.skolem_instance_records.try_reserve_exact(1).ok()?;
            self.skolem_witness_records.try_reserve_exact(1).ok()?;
            self.skolem_instance_records
                .push(crate::executor::SkolemInstanceRecord {
                    source: choice.original,
                    quantified: choice.quantified,
                    witness: choice.witness,
                    instance: choice.raw,
                    asserted: target,
                    positive: matches!(choice.kind, ChoiceKind::Exists),
                });
            self.skolem_witness_records
                .push(crate::executor::SkolemWitnessRecord {
                    quantified: choice.quantified,
                    witness: choice.witness,
                    instance: choice.raw,
                    positive: matches!(choice.kind, ChoiceKind::Exists),
                });
        }
        let mut count = choices.len();
        for universal in &universals {
            let q = universal.quantified();
            let (data, _) = self.native_source_produce(|terms, _, progress| {
                terms
                    .try_copy_native_proof_node_with_progress(q, progress)
                    .ok()
            })?;
            let TermData::Forall(bindings, body, _) = data else {
                return None;
            };
            let [(binder, sort)] = bindings.as_slice() else {
                continue;
            };
            let mut values = Vec::new();
            self.seed_native_source_offer_values(sort, &mut values)?;
            self.seed_native_universal_source_values(&source, sort, &mut values)?;
            for choice in &choices {
                self.admit_native_universal_terms(&[choice.witness])?;
                self.charge_native_universal(values.len(), 0)?;
                if super::instances::closed_source_sorts_equal(
                    self,
                    self.ctx.terms.sort(choice.witness),
                    sort,
                    0,
                )? && !values.contains(&choice.witness)
                {
                    self.reserve_native_source_vector(&mut values)?;
                    values.push(choice.witness);
                }
            }
            for value in values.into_iter().take(16) {
                if count >= 64 {
                    break;
                }
                self.charge_native_universal(1024, 16 * 1024)?;
                let (fragment, exact) = self.native_source_produce(|terms, _, progress| {
                    universal_fragment(terms, universal, q, body, binder, value, progress)
                })?;
                let target = self.native_source_produce(|terms, _, progress| {
                    nnf(terms, exact, Polarity::Positive, progress, 0, &mut 4096)
                })?;
                let fragment = self.native_source_produce(|terms, _, progress| {
                    normalize_fragment(terms, fragment, exact, target, progress)
                })?;
                self.install_native_source_unit(&source, fragment, target)?;
                self.append_native_source_working_unit(target)?;
                count += 1;
            }
        }
        source.is_current(self).then_some(())
    }

    // The original-only repair shares the exact producer with working offers.
    // Rebuilding a proof never needs to promote a rewritten working occurrence.
    fn plan_native_source_offers(
        &mut self,
        initial: NativeUniversalSource,
        require_working: bool,
    ) -> Option<(NativeUniversalSource, Vec<Choice>, Vec<Universal>)> {
        self.charge_native_universal(
            initial.roots().len(),
            initial.roots().len().checked_mul(32)?,
        )?;
        let roots = initial.roots().to_vec();
        let mut choices = Vec::new();
        let mut universals = Vec::new();
        for &original in &roots {
            // Only an exact working occurrence may be replaced. A previous
            // unrelated preprocessing rewrite needs its own checked transport.
            if require_working {
                self.charge_native_universal(self.ctx.assertions.len(), 0)?;
                if !self.ctx.assertions.contains(&original) {
                    continue;
                }
            }
            self.admit_native_universal_terms(&[original])?;
            let shape = match self.ctx.terms.get(original) {
                TermData::Forall(..) => Some((original, None)),
                TermData::Exists(..) => Some((original, Some(ChoiceKind::Exists))),
                TermData::Not(q) if matches!(self.ctx.terms.get(*q), TermData::Forall(..)) => {
                    Some((*q, Some(ChoiceKind::NegativeForall)))
                }
                _ => None,
            };
            if let Some((q, kind)) = shape {
                let (data, _) = self.native_source_produce(|terms, _, progress| {
                    terms
                        .try_copy_native_proof_node_with_progress(q, progress)
                        .ok()
                })?;
                let (bindings, body) = match data {
                    TermData::Forall(bindings, body, _) | TermData::Exists(bindings, body, _) => {
                        (bindings, body)
                    }
                    _ => continue,
                };
                if bindings.len() != 1
                    || self.native_source_produce(|terms, _, progress| {
                        contains_quantifier(terms, body, progress, 0, &mut 4096)
                    })?
                {
                    continue;
                }
                match kind {
                    None => {
                        self.reserve_native_source_vector(&mut universals)?;
                        universals.push(Universal::Original(q));
                    }
                    Some(kind) => {
                        if choices.len() >= 64 {
                            continue;
                        }
                        self.charge_native_universal(choices.len(), 0)?;
                        if choices.iter().any(|c: &Choice| c.original == original) {
                            continue;
                        }
                        let (binder, sort) = &bindings[0];
                        let witness = self.native_source_produce(|terms, _, progress| {
                            terms
                                .try_fresh_var_with_progress("native_source_choice", sort, progress)
                                .ok()
                        })?;
                        let choice_body = match kind {
                            ChoiceKind::Exists => body,
                            ChoiceKind::NegativeForall => {
                                self.native_source_produce(|terms, _, progress| {
                                    negative_choice_body(terms, body, progress)
                                })?
                            }
                        };
                        self.native_source_produce(|terms, _, progress| {
                            terms
                                .try_register_new_skolem_choice_with_progress(
                                    witness,
                                    binder,
                                    sort,
                                    choice_body,
                                    progress,
                                )
                                .ok()
                        })?;
                        let raw = self.native_source_produce(|terms, _, progress| {
                            substitute(terms, body, binder, witness, progress, 0, &mut 4096, None)
                                .map(|p| p.0)
                        })?;
                        self.reserve_native_source_vector(&mut choices)?;
                        choices.push(Choice {
                            original,
                            quantified: q,
                            witness,
                            raw,
                            kind,
                        });
                    }
                }
                continue;
            }
            if let TermData::Not(exists) = self.ctx.terms.get(original) {
                let exists = *exists;
                if !matches!(self.ctx.terms.get(exists), TermData::Exists(..)) {
                    continue;
                }
                let (data, _) = self.native_source_produce(|terms, _, progress| {
                    terms
                        .try_copy_native_proof_node_with_progress(exists, progress)
                        .ok()
                })?;
                let TermData::Exists(bindings, body, triggers) = data else {
                    continue;
                };
                if bindings.len() != 1
                    || self.native_source_produce(|terms, _, progress| {
                        contains_quantifier(terms, body, progress, 0, &mut 4096)
                    })?
                {
                    continue;
                }
                let dual = self.native_source_produce(|terms, _, progress| {
                    let negative = not(terms, body, progress)?;
                    terms
                        .try_intern_native_proof_with_progress(
                            &TermData::Forall(bindings, negative, triggers),
                            &Sort::Bool,
                            progress,
                        )
                        .ok()
                })?;
                self.reserve_native_source_vector(&mut universals)?;
                universals.push(Universal::NegatedExists {
                    original,
                    exists,
                    dual,
                });
            }
        }
        // The only ignored metadata difference is our OWN completed choice
        // registrations. Epoch/context/root identity and the retained arena
        // prefix still have to match the pre-mint original source.
        let source = NativeUniversalSource::capture(self)?;
        if !initial.epoch.is_same_epoch(&source.epoch)
            || initial.context != source.context
            || initial.depth != source.depth
            || initial.roots() != source.roots()
            || !initial.prefix.is_append_only_prefix_of(&self.ctx.terms)
        {
            return None;
        }
        Some((source, choices, universals))
    }

    pub(super) fn reserve_native_source_vector<T>(&self, values: &mut Vec<T>) -> Option<()> {
        self.charge_native_universal(1, 0)?;
        if values.len() == values.capacity() {
            let capacity = values.len().checked_mul(2)?.max(4);
            self.charge_native_universal(
                values.len().checked_add(capacity)?,
                capacity
                    .checked_mul(std::mem::size_of::<T>())?
                    .checked_mul(2)?,
            )?;
            values
                .try_reserve_exact(capacity.checked_sub(values.len())?)
                .ok()?;
        }
        Some(())
    }

    fn seed_native_source_offer_values(
        &mut self,
        sort: &Sort,
        values: &mut Vec<TermId>,
    ) -> Option<()> {
        if sort == &Sort::Bool {
            self.charge_native_universal(4, 0)?;
            for value in [
                boolean_id(&self.ctx.terms, true)?,
                boolean_id(&self.ctx.terms, false)?,
            ] {
                self.charge_native_universal(values.len(), 0)?;
                if !values.contains(&value) {
                    self.reserve_native_source_vector(values)?;
                    values.push(value);
                }
            }
        } else if sort == &Sort::Int {
            let zero = self.native_source_produce(|terms, _, progress| {
                terms
                    .try_intern_with_progress(
                        &TermData::Const(ay_core::Constant::Int(0.into())),
                        &Sort::Int,
                        progress,
                    )
                    .ok()
            })?;
            self.charge_native_universal(values.len(), 0)?;
            if !values.contains(&zero) {
                self.reserve_native_source_vector(values)?;
                values.push(zero);
            }
        } else if matches!(sort, Sort::Uninterpreted(_)) {
            // This existing helper admits actual live constructor/member
            // metadata. Its native constructor construction is controlled.
            self.seed_native_universal_values(sort, values)?;
        }
        // Other carriers use their genuinely closed original values or an
        // authenticated choice below, not a new unregistered opaque constant.
        Some(())
    }

    pub(super) fn native_source_produce<T>(
        &mut self,
        make: impl FnOnce(
            &mut TermStore,
            &mut ProofTracker,
            &mut dyn FnMut(usize, usize) -> bool,
        ) -> Option<T>,
    ) -> Option<T> {
        self.charge_native_universal(64, 128)?;
        let inherited = ay_core::resource::current_check_stop().ok()?;
        let guard = ay_core::resource::current_guard();
        let interrupt = self.solve_interrupt.clone();
        let owner = &self.native_universal_budget;
        let result = make(
            &mut self.ctx.terms,
            &mut self.proof_tracker,
            &mut |work, bytes| {
                let stopped = super::super::assembly_observations::observe()
                    || inherited.as_ref().is_some_and(|stop| stop())
                    || guard.as_ref().is_some_and(|guard| guard.poll().is_some())
                    || interrupt
                        .as_ref()
                        .is_some_and(|flag| flag.load(std::sync::atomic::Ordering::Relaxed));
                owner.borrow_mut().charge(work, bytes, stopped).is_some()
            },
        );
        self.charge_native_universal(0, 0)?;
        result
    }

    fn install_native_source_unit(
        &mut self,
        source: &NativeUniversalSource,
        fragment: Proof,
        target: TermId,
    ) -> Option<()> {
        if !source.is_current(self) {
            return None;
        }
        self.admit_native_universal_terms(&[target])?;
        let checked = ay_proof::authenticate_premise_clauses_strict_with_context_and_progress(
            &fragment,
            &self.ctx.terms,
            None,
            None,
            source.roots(),
            &mut |work, bytes| self.charge_native_universal(work, bytes).is_some(),
        )
        .ok()?;
        if !source.is_current(self) {
            return None;
        }
        self.native_source_produce(|_, tracker, progress| {
            tracker.append_native_premise(fragment, &checked, target, progress)
        })?;
        source.is_current(self).then_some(())
    }

    fn replace_native_source_working_unit(
        &mut self,
        original: TermId,
        target: TermId,
    ) -> Option<()> {
        self.charge_native_universal(self.ctx.assertions.len(), 0)?;
        for row in &mut self.ctx.assertions {
            if *row == original {
                *row = target;
            }
        }
        Some(())
    }

    fn append_native_source_working_unit(&mut self, target: TermId) -> Option<()> {
        self.charge_native_universal(self.ctx.assertions.len(), 0)?;
        if self.ctx.assertions.contains(&target) {
            return Some(());
        }
        if self.ctx.assertions.len() == self.ctx.assertions.capacity() {
            let capacity = self.ctx.assertions.len().checked_mul(2)?.max(4);
            self.charge_native_universal(capacity, capacity.checked_mul(8)?)?;
            self.ctx
                .assertions
                .try_reserve_exact(capacity.checked_sub(self.ctx.assertions.len())?)
                .ok()?;
        }
        self.ctx.assertions.push(target);
        Some(())
    }
}

type Progress<'a> = &'a mut dyn FnMut(usize, usize) -> bool;

// Choice metadata follows the established producer's top-level mk_not
// canonicalization. The proof instance below independently keeps RAW syntax.
fn negative_choice_body(
    terms: &mut TermStore,
    body: TermId,
    progress: Progress<'_>,
) -> Option<TermId> {
    if !progress(1, 0) {
        return None;
    }
    terms.entry_stamp(body)?;
    let simplified = match terms.get(body) {
        TermData::Not(inner) => Some(*inner),
        TermData::Const(ay_core::Constant::Bool(value)) => return boolean_id(terms, !*value),
        _ => None,
    };
    if let Some(inner) = simplified {
        terms.entry_stamp(inner)?;
        Some(inner)
    } else {
        not(terms, body, progress)
    }
}

fn not(terms: &mut TermStore, value: TermId, progress: Progress<'_>) -> Option<TermId> {
    terms
        .try_intern_native_proof_with_progress(&TermData::Not(value), &Sort::Bool, progress)
        .ok()
}

fn app(
    terms: &mut TermStore,
    name: &str,
    values: &[TermId],
    progress: Progress<'_>,
) -> Option<TermId> {
    if !progress(
        name.len().checked_add(values.len())?,
        name.len().checked_add(values.len().checked_mul(8)?)?,
    ) {
        return None;
    }
    terms
        .try_intern_native_proof_with_progress(
            &TermData::App(Symbol::named(name), values.to_vec()),
            &Sort::Bool,
            progress,
        )
        .ok()
}

// Borrowed per-physical-occurrence walk. No legacy memo/table allocation or
// copied lexical prefix occurs before the original owner has admitted it.
fn contains_quantifier(
    terms: &TermStore,
    root: TermId,
    progress: Progress<'_>,
    depth: usize,
    left: &mut usize,
) -> Option<bool> {
    *left = left.checked_sub(1)?;
    if depth > 64 || !progress(1, 0) {
        return None;
    }
    terms.entry_stamp(root)?;
    match terms.get(root) {
        TermData::Forall(..) | TermData::Exists(..) => Some(true),
        TermData::Not(child) => contains_quantifier(terms, *child, progress, depth + 1, left),
        TermData::Ite(c, t, e) => {
            for id in [*c, *t, *e] {
                if contains_quantifier(terms, id, progress, depth + 1, left)? {
                    return Some(true);
                }
            }
            Some(false)
        }
        TermData::App(_, children) => {
            for &child in children {
                if contains_quantifier(terms, child, progress, depth + 1, left)? {
                    return Some(true);
                }
            }
            Some(false)
        }
        TermData::Var(..) | TermData::Const(..) => Some(false),
        // Lets/future binders need an exact scoped substitution implementation.
        _ => Some(true),
    }
}

fn substitute(
    terms: &mut TermStore,
    root: TermId,
    binder: &str,
    value: TermId,
    progress: Progress<'_>,
    depth: usize,
    left: &mut usize,
    matched: Option<u32>,
) -> Option<(TermId, Option<u32>)> {
    *left = left.checked_sub(1)?;
    if depth > 64 || !progress(1, 0) {
        return None;
    }
    terms.entry_stamp(root)?;
    match terms.get(root) {
        TermData::Var(name, id) => {
            if !progress(name.len().checked_add(binder.len())?, 0) {
                return None;
            }
            if name != binder {
                return Some((root, matched));
            }
            if matched.is_some_and(|old| old != *id) {
                return None;
            }
            return Some((value, Some(*id)));
        }
        TermData::Const(_) => return Some((root, matched)),
        TermData::App(_, _) | TermData::Not(_) | TermData::Ite(..) => {}
        _ => return None,
    }
    if terms.get_lambda_array(root).is_some() {
        return None;
    }
    let (mut data, sort) = terms
        .try_copy_native_proof_node_with_progress(root, progress)
        .ok()?;
    let children: &mut [TermId] = match &mut data {
        TermData::App(_, children) => children,
        TermData::Not(child) => std::slice::from_mut(child),
        TermData::Ite(c, t, e) => {
            let mut ids = [*c, *t, *e];
            let mut seen = matched;
            for id in &mut ids {
                let (new, next) =
                    substitute(terms, *id, binder, value, progress, depth + 1, left, seen)?;
                *id = new;
                seen = next;
            }
            if ids == [*c, *t, *e] {
                return Some((root, seen));
            }
            return Some((
                terms
                    .try_intern_native_proof_with_progress(
                        &TermData::Ite(ids[0], ids[1], ids[2]),
                        &sort,
                        progress,
                    )
                    .ok()?,
                seen,
            ));
        }
        _ => return None,
    };
    let mut seen = matched;
    let mut changed = false;
    for id in children {
        let (new, next) = substitute(terms, *id, binder, value, progress, depth + 1, left, seen)?;
        changed |= new != *id;
        *id = new;
        seen = next;
    }
    Some((
        if changed {
            terms
                .try_intern_native_proof_with_progress(&data, &sort, progress)
                .ok()?
        } else {
            root
        },
        seen,
    ))
}

fn choice_fragment(
    terms: &mut TermStore,
    choice: &Choice,
    progress: Progress<'_>,
) -> Option<(Proof, TermId)> {
    let mut proof = Proof::new();
    let source = proof.add_assume(choice.original, None);
    let equality = app(terms, "=", &[choice.quantified, choice.raw], progress)?;
    let skolem = proof.add_rule_step(
        AletheRule::Skolem,
        vec![equality],
        vec![],
        vec![choice.witness],
    );
    let neq = not(terms, equality, progress)?;
    let (literal, rule, clause) = match choice.kind {
        ChoiceKind::Exists => {
            let nq = not(terms, choice.quantified, progress)?;
            (choice.raw, AletheRule::EquivPos2, vec![neq, nq, choice.raw])
        }
        ChoiceKind::NegativeForall => {
            let ni = not(terms, choice.raw, progress)?;
            (ni, AletheRule::EquivPos1, vec![neq, choice.quantified, ni])
        }
    };
    let side = clause[1];
    let equiv = proof.add_rule_step(rule, clause, vec![], vec![]);
    let implies = proof.add_resolution(vec![side, literal], equality, skolem, equiv);
    proof.add_resolution(vec![literal], choice.quantified, source, implies);
    Some((proof, literal))
}

fn universal_fragment(
    terms: &mut TermStore,
    source: &Universal,
    q: TermId,
    body: TermId,
    binder: &str,
    value: TermId,
    progress: Progress<'_>,
) -> Option<(Proof, TermId)> {
    let exact = substitute(terms, body, binder, value, progress, 0, &mut 4096, None)?.0;
    let mut proof = Proof::new();
    let source_id = match *source {
        Universal::Original(root) => proof.add_assume(root, None),
        Universal::NegatedExists {
            original,
            exists,
            dual,
        } => {
            let root = proof.add_assume(original, None);
            let lemma =
                proof.add_rule_step(AletheRule::QntNegExists, vec![exists, dual], vec![], vec![]);
            proof.add_resolution(vec![dual], exists, root, lemma)
        }
    };
    let negative = not(terms, q, progress)?;
    let implication = app(terms, "or", &[negative, exact], progress)?;
    let instance = proof.add_rule_step(
        AletheRule::ForallInst,
        vec![implication],
        vec![],
        vec![value],
    );
    let clause = proof.add_rule_step(
        AletheRule::Or,
        vec![negative, exact],
        vec![instance],
        vec![],
    );
    proof.add_resolution(vec![exact], q, clause, source_id);
    Some((proof, exact))
}

fn normalize_fragment(
    terms: &mut TermStore,
    mut proof: Proof,
    exact: TermId,
    target: TermId,
    progress: Progress<'_>,
) -> Option<Proof> {
    if exact == target {
        return Some(proof);
    }
    let prior = ProofId(u32::try_from(proof.steps.len().checked_sub(1)?).ok()?);
    let negative = not(terms, exact, progress)?;
    let lemma = proof.add_theory_lemma_with_kind(
        "bool",
        vec![negative, target],
        TheoryLemmaKind::BoolTautology,
    );
    proof.add_resolution(vec![target], exact, prior, lemma);
    Some(proof)
}

#[derive(Clone, Copy)]
enum Polarity {
    Positive,
    Negative,
}

impl Polarity {
    fn flip(self) -> Self {
        match self {
            Self::Positive => Self::Negative,
            Self::Negative => Self::Positive,
        }
    }
}

fn boolean_id(terms: &TermStore, value: bool) -> Option<TermId> {
    let (yes, no) = terms.boolean_constant_ids();
    let id = if value { yes? } else { no? };
    terms.entry_stamp(id)?;
    if terms.sort(id) != &Sort::Bool {
        return None;
    }
    matches!(terms.get(id),TermData::Const(ay_core::Constant::Bool(actual)) if *actual==value)
        .then_some(id)
}

/// QF Boolean normalization is only a proposal. The complete Boolean bridge
/// back to the exact source instance is checked before the result is indexed.
fn nnf(
    terms: &mut TermStore,
    root: TermId,
    polarity: Polarity,
    progress: Progress<'_>,
    depth: usize,
    left: &mut usize,
) -> Option<TermId> {
    *left = left.checked_sub(1)?;
    if depth > 64 || !progress(1, 0) {
        return None;
    }
    terms.entry_stamp(root)?;
    match terms.get(root) {
        TermData::Const(ay_core::Constant::Bool(value)) => {
            return boolean_id(
                terms,
                match polarity {
                    Polarity::Positive => *value,
                    Polarity::Negative => !*value,
                },
            )
        }
        TermData::Var(..) => {
            return match polarity {
                Polarity::Positive => Some(root),
                Polarity::Negative => not(terms, root, progress),
            }
        }
        _ => {}
    }
    let (data, _) = terms
        .try_copy_native_proof_node_with_progress(root, progress)
        .ok()?;
    match data {
        TermData::Not(inner) => nnf(terms, inner, polarity.flip(), progress, depth + 1, left),
        TermData::App(Symbol::Named(name), args) if name == "and" || name == "or" => {
            if !progress(args.len(), args.len().checked_mul(8)?) {
                return None;
            }
            let mut mapped = Vec::new();
            mapped.try_reserve_exact(args.len()).ok()?;
            for arg in args {
                mapped.push(nnf(terms, arg, polarity, progress, depth + 1, left)?);
            }
            let connective = match (name.as_str(), polarity) {
                ("and", Polarity::Positive) | ("or", Polarity::Negative) => "and",
                _ => "or",
            };
            nary(terms, connective, &mapped, progress)
        }
        TermData::App(Symbol::Named(name), args) if name == "=>" && args.len() == 2 => {
            let a = nnf(terms, args[0], polarity.flip(), progress, depth + 1, left)?;
            let b = nnf(terms, args[1], polarity, progress, depth + 1, left)?;
            nary(
                terms,
                match polarity {
                    Polarity::Positive => "or",
                    Polarity::Negative => "and",
                },
                &[a, b],
                progress,
            )
        }
        TermData::Ite(c, t, e) => {
            let c = nnf(terms, c, Polarity::Positive, progress, depth + 1, left)?;
            let t = nnf(terms, t, polarity, progress, depth + 1, left)?;
            let e = nnf(terms, e, polarity, progress, depth + 1, left)?;
            boolean_ite(terms, c, t, e, progress, depth + 1)
        }
        TermData::App(Symbol::Named(name), args)
            if name == "="
                && args.len() == 2
                && terms.sort(args[0]) == &Sort::Bool
                && terms.sort(args[1]) == &Sort::Bool =>
        {
            let a = nnf(
                terms,
                args[0],
                Polarity::Positive,
                progress,
                depth + 1,
                left,
            )?;
            let b = nnf(
                terms,
                args[1],
                Polarity::Positive,
                progress,
                depth + 1,
                left,
            )?;
            let yes = boolean_id(terms, true)?;
            let no = boolean_id(terms, false)?;
            let value = if a == b {
                yes
            } else if a == yes {
                b
            } else if b == yes {
                a
            } else if a == no {
                not(terms, b, progress)?
            } else if b == no {
                not(terms, a, progress)?
            } else {
                app(terms, "=", &[a.min(b), a.max(b)], progress)?
            };
            match polarity {
                Polarity::Positive => Some(value),
                Polarity::Negative => not(terms, value, progress),
            }
        }
        TermData::Forall(..) | TermData::Exists(..) => None,
        _ => match polarity {
            Polarity::Positive => Some(root),
            Polarity::Negative => not(terms, root, progress),
        },
    }
}

fn nary(
    terms: &mut TermStore,
    name: &str,
    args: &[TermId],
    progress: Progress<'_>,
) -> Option<TermId> {
    let yes = boolean_id(terms, true)?;
    let no = boolean_id(terms, false)?;
    let (neutral, absorbing) = if name == "and" { (yes, no) } else { (no, yes) };
    let mut flat = Vec::new();
    for &arg in args {
        if !progress(1, 0) {
            return None;
        }
        if arg == absorbing {
            return Some(absorbing);
        }
        if arg == neutral {
            continue;
        }
        let nested = match terms.get(arg) {
            TermData::App(Symbol::Named(head), children) if head == name => {
                Some(children.as_slice())
            }
            _ => None,
        };
        let children = nested.unwrap_or(std::slice::from_ref(&arg));
        let wanted = flat.len().checked_add(children.len())?;
        if wanted > 4096 || !progress(children.len(), 0) {
            return None;
        }
        if wanted > flat.capacity() {
            let capacity = flat.capacity().checked_mul(2)?.max(wanted).max(4);
            if !progress(flat.len().checked_add(capacity)?, capacity.checked_mul(8)?) {
                return None;
            }
            flat.try_reserve_exact(capacity.checked_sub(flat.len())?)
                .ok()?;
        }
        flat.extend_from_slice(children);
    }
    let width = usize::try_from(usize::BITS - flat.len().max(1).leading_zeros()).ok()?;
    if !progress(flat.len().checked_mul(width.checked_add(1)?)?, 0) {
        return None;
    }
    flat.sort_unstable();
    flat.dedup();
    match flat.as_slice() {
        [] => Some(neutral),
        [only] => Some(*only),
        _ => app(terms, name, &flat, progress),
    }
}

fn boolean_ite(
    terms: &mut TermStore,
    mut c: TermId,
    mut t: TermId,
    mut e: TermId,
    progress: Progress<'_>,
    depth: usize,
) -> Option<TermId> {
    if depth > 64 || !progress(8, 128) {
        return None;
    }
    let yes = boolean_id(terms, true)?;
    let no = boolean_id(terms, false)?;
    if c == yes {
        return Some(t);
    }
    if c == no {
        return Some(e);
    }
    if let TermData::Not(inner) = terms.get(c) {
        c = *inner;
        std::mem::swap(&mut t, &mut e);
    }
    if t == e {
        return Some(t);
    }
    if t == yes && e == no {
        return Some(c);
    }
    if t == no && e == yes {
        return not(terms, c, progress);
    }
    if (t == c && e == no) || (t == yes && e == c) {
        return Some(c);
    }
    if e == no {
        return nary(terms, "and", &[c, t], progress);
    }
    if t == yes {
        return nary(terms, "or", &[c, e], progress);
    }
    if t == no {
        let nc = not(terms, c, progress)?;
        return nary(terms, "and", &[nc, e], progress);
    }
    if e == yes {
        let nc = not(terms, c, progress)?;
        return nary(terms, "or", &[nc, t], progress);
    }
    let nested_then = match terms.get(t) {
        TermData::Ite(inner, then, _) if *inner == c => Some(*then),
        _ => None,
    };
    if let Some(then) = nested_then {
        return boolean_ite(terms, c, then, e, progress, depth + 1);
    }
    let nested_else = match terms.get(e) {
        TermData::Ite(inner, _, otherwise) if *inner == c => Some(*otherwise),
        _ => None,
    };
    if let Some(otherwise) = nested_else {
        return boolean_ite(terms, c, t, otherwise, progress, depth + 1);
    }
    terms
        .try_intern_native_proof_with_progress(&TermData::Ite(c, t, e), &Sort::Bool, progress)
        .ok()
}

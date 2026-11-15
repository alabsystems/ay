// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Epoch- and entry-stamped quantifier derivations for exact SAT fragments.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::TermEntryStamp;
use ay_core::{TermData, TermId};
use ay_frontend::SourceContextStamp;

use crate::executor::{
    Executor, QpfPremiseForcedInstanceRecord, QueryAuthorityEpoch, SkolemInstanceRecord,
};
use crate::preprocess::{PropagateValues, PropagatedEntrySource, PropagatedRewriteRecord};
use crate::sat_proof_manager::{
    FragmentInstanceDerivation, FragmentInstanceRootDerivation, FragmentSkolemDerivation,
};

mod context_derivation;
use context_derivation::CheckedContextDerivation;
mod propagation_entry;

/// Rounds allowed when closing a seeded substitution map under itself in
/// [`CheckedPropagationDerivation::close_seeded_substitution`]. Each round
/// resolves one more link of a chained replacement, so the bound is the
/// longest entry chain the seal will reproduce; it exists to terminate on a
/// cyclic map rather than to ration work.
const MAX_SEED_CLOSURE_ROUNDS: usize = 8;

#[must_use = "checked instantiation evidence must be consumed or discarded"]
pub(super) struct CheckedInstanceDerivation {
    query_epoch: QueryAuthorityEpoch,
    source_context_stamp: SourceContextStamp,
    quantifier: TermId,
    quantifier_entry: TermEntryStamp,
    values: Vec<TermId>,
    value_entries: Vec<TermEntryStamp>,
    instance: TermId,
    instance_entry: TermEntryStamp,
    /// Solver-visible asserted term the fragment map is keyed by. Equal to
    /// `instance` for direct instantiations; the literal `false` term for a
    /// BV-MBQI eval-folded-`false` record.
    asserted: TermId,
    asserted_entry: TermEntryStamp,
}

impl CheckedInstanceDerivation {
    pub(super) fn seal(
        executor: &mut Executor,
        quantifier: TermId,
        values: &[TermId],
        instance: TermId,
        asserted: TermId,
    ) -> Option<Self> {
        let TermData::Forall(bindings, body, _) = executor.ctx.terms.get(quantifier).clone() else {
            return None;
        };
        if bindings.is_empty() || bindings.len() != values.len() {
            return None;
        }
        let mut substitution = HashMap::default();
        for ((name, sort), &value) in bindings.iter().zip(values) {
            if executor.ctx.terms.sort(value) != sort {
                return None;
            }
            substitution.insert(name.clone(), value);
        }
        if crate::ematching::subst_vars_exact_qf(&mut executor.ctx.terms, body, &substitution)?
            != instance
        {
            return None;
        }
        if asserted != instance {
            // Fold-bridged records may target only literal `false`, and the
            // raw instance must independently evaluate to false. The emitted
            // proof bridge is checked again by the strict checker.
            if asserted != executor.ctx.terms.false_term() {
                return None;
            }
            let empty_model = crate::executor::model::Model::empty();
            if !matches!(
                executor.evaluate_term(&empty_model, instance),
                crate::executor::model::EvalValue::Bool(false)
            ) {
                return None;
            }
        }
        Some(Self {
            query_epoch: executor.query_authority_epoch.clone(),
            source_context_stamp: executor.ctx.source_context_stamp(),
            quantifier,
            quantifier_entry: executor.ctx.terms.entry_stamp(quantifier)?,
            values: values.to_vec(),
            value_entries: values
                .iter()
                .map(|&value| executor.ctx.terms.entry_stamp(value))
                .collect::<Option<Vec<_>>>()?,
            instance,
            instance_entry: executor.ctx.terms.entry_stamp(instance)?,
            asserted,
            asserted_entry: executor.ctx.terms.entry_stamp(asserted)?,
        })
    }

    pub(super) fn into_current(
        self,
        executor: &Executor,
    ) -> Option<(TermId, FragmentInstanceDerivation)> {
        (self
            .query_epoch
            .is_same_epoch(&executor.query_authority_epoch)
            && self.source_context_stamp == executor.ctx.source_context_stamp()
            && executor.ctx.terms.entry_stamp(self.quantifier) == Some(self.quantifier_entry)
            && executor.ctx.terms.entry_stamp(self.instance) == Some(self.instance_entry)
            && executor.ctx.terms.entry_stamp(self.asserted) == Some(self.asserted_entry)
            && self.value_entries.iter().copied().map(Some).eq(self
                .values
                .iter()
                .map(|&value| executor.ctx.terms.entry_stamp(value))))
        .then_some((
            self.asserted,
            FragmentInstanceDerivation {
                quantifier: self.quantifier,
                values: self.values,
                instance: self.instance,
            },
        ))
    }
}

#[must_use = "checked Skolemization evidence must be consumed or discarded"]
pub(super) struct CheckedSkolemDerivation {
    query_epoch: QueryAuthorityEpoch,
    source_context_stamp: SourceContextStamp,
    source: TermId,
    source_entry: TermEntryStamp,
    quantified: TermId,
    quantified_entry: TermEntryStamp,
    witness: TermId,
    witness_entry: TermEntryStamp,
    instance: TermId,
    instance_entry: TermEntryStamp,
    asserted: TermId,
    asserted_entry: TermEntryStamp,
    positive: bool,
}

impl CheckedSkolemDerivation {
    pub(super) fn seal(executor: &mut Executor, record: &SkolemInstanceRecord) -> Option<Self> {
        let terms = &mut executor.ctx.terms;
        let (bindings, body) = if record.positive {
            if record.source != record.quantified {
                return None;
            }
            let TermData::Exists(bindings, body, _) = terms.get(record.quantified).clone() else {
                return None;
            };
            (bindings, body)
        } else {
            let TermData::Not(inner) = terms.get(record.source) else {
                return None;
            };
            if *inner != record.quantified {
                return None;
            }
            let TermData::Forall(bindings, body, _) = terms.get(record.quantified).clone() else {
                return None;
            };
            (bindings, body)
        };
        let [(binder, binder_sort)] = bindings.as_slice() else {
            return None;
        };
        let TermData::Var(witness_name, _) = terms.get(record.witness).clone() else {
            return None;
        };
        if !terms.is_skolem_symbol(&witness_name) || terms.sort(record.witness) != binder_sort {
            return None;
        }
        let expected_choice_body = if record.positive {
            body
        } else {
            terms.mk_not(body)
        };
        let choice = terms.skolem_choice(record.witness)?;
        if choice.binder != *binder
            || &choice.sort != binder_sort
            || choice.body != expected_choice_body
        {
            return None;
        }
        let mut substitution = HashMap::default();
        substitution.insert(binder.clone(), record.witness);
        if crate::ematching::subst_vars_exact_qf(terms, body, &substitution)? != record.instance {
            return None;
        }
        Some(Self {
            query_epoch: executor.query_authority_epoch.clone(),
            source_context_stamp: executor.ctx.source_context_stamp(),
            source: record.source,
            source_entry: executor.ctx.terms.entry_stamp(record.source)?,
            quantified: record.quantified,
            quantified_entry: executor.ctx.terms.entry_stamp(record.quantified)?,
            witness: record.witness,
            witness_entry: executor.ctx.terms.entry_stamp(record.witness)?,
            instance: record.instance,
            instance_entry: executor.ctx.terms.entry_stamp(record.instance)?,
            asserted: record.asserted,
            asserted_entry: executor.ctx.terms.entry_stamp(record.asserted)?,
            positive: record.positive,
        })
    }

    pub(super) fn into_current(self, executor: &Executor) -> Option<FragmentSkolemDerivation> {
        (self
            .query_epoch
            .is_same_epoch(&executor.query_authority_epoch)
            && self.source_context_stamp == executor.ctx.source_context_stamp()
            && executor.ctx.terms.entry_stamp(self.source) == Some(self.source_entry)
            && executor.ctx.terms.entry_stamp(self.quantified) == Some(self.quantified_entry)
            && executor.ctx.terms.entry_stamp(self.witness) == Some(self.witness_entry)
            && executor.ctx.terms.entry_stamp(self.instance) == Some(self.instance_entry)
            && executor.ctx.terms.entry_stamp(self.asserted) == Some(self.asserted_entry))
        .then_some(FragmentSkolemDerivation {
            source: self.source,
            quantified: self.quantified,
            witness: self.witness,
            instance: self.instance,
            positive: self.positive,
        })
    }
}

/// Epoch- and entry-stamped evidence that one recorded `PropagateValues`
/// rewrite `before -> after` is exactly reproducible from its stamped
/// licensing entries (#ppp-c7; exact [`CheckedInstanceDerivation`] mirror).
///
/// `seal` independently replays the rewrite through a SEEDED THROWAWAY
/// `PropagateValues` pass whose substitution map is rebuilt first-wins from
/// the stamped entry records, and binds the query epoch, frontend source
/// stamp, and the per-term entry stamps of both endpoints. `into_current`
/// re-verifies every binding at the exact consumption moment and destroys
/// the token. The sealed product remains a HINT: the c7 planner replays the
/// rewrite again and the strict checker re-derives every emitted step.
#[must_use = "checked propagation evidence must be consumed or discarded"]
pub(super) struct CheckedPropagationDerivation {
    query_epoch: QueryAuthorityEpoch,
    source_context_stamp: SourceContextStamp,
    before: TermId,
    before_entry: TermEntryStamp,
    after: TermId,
    after_entry: TermEntryStamp,
    stamp: u32,
}

impl CheckedPropagationDerivation {
    pub(super) fn seal(
        executor: &mut Executor,
        record: &PropagatedRewriteRecord,
        entries: &[PropagatedEntrySource],
    ) -> Option<Self> {
        if record.before == record.after {
            return None;
        }
        // First-wins stamped substitution map, exactly the environment the
        // pipeline pass held when it performed this rewrite.
        let mut seeded: HashMap<TermId, TermId> = HashMap::default();
        for entry in entries {
            if entry.stamp <= record.stamp {
                seeded.entry(entry.expr).or_insert(entry.value);
            }
        }
        // The VERBATIM replay stays the first attempt, so every record that
        // seals today seals by exactly the same route.
        if !Self::seeded_replay_reaches(&mut executor.ctx.terms, &seeded, record) {
            // The producer may be `VariableSubstitution`, whose
            // `substitute_term` applies its map to FIXPOINT: on a map hit it
            // returns `substitute_term(replacement)`, so a replacement that
            // itself mentions a substituted key is chased before it lands.
            // `PropagateValues::rewrite` does NOT chase — it returns the
            // stored value verbatim — so the verbatim replay above
            // reconstructs a term the pass never wrote whenever the recorded
            // entries CHAIN, and the record is dropped before the planner
            // ever sees it. Re-run the replay under the map closed under
            // itself, which is the same function on an acyclic map.
            //
            // This is the seal catching up with the planner: `plan_derive_eq`
            // already composes a chained entry with `trans`
            // (`plan_compose_entry_value`, #4751 `_mod_q`), and
            // `plan_record_bridge` re-derives `before -> after` itself and
            // refuses unless it reaches the recorded `after`. The record is a
            // HINT — a pair worth trying — so sealing one more of them grants
            // no authority; the strict checker still re-validates every step.
            let closed = Self::close_seeded_substitution(&mut executor.ctx.terms, &seeded)?;
            if !Self::seeded_replay_reaches(&mut executor.ctx.terms, &closed, record) {
                return None;
            }
        }
        Some(Self {
            query_epoch: executor.query_authority_epoch.clone(),
            source_context_stamp: executor.ctx.source_context_stamp(),
            before: record.before,
            before_entry: executor.ctx.terms.entry_stamp(record.before)?,
            after: record.after,
            after_entry: executor.ctx.terms.entry_stamp(record.after)?,
            stamp: record.stamp,
        })
    }

    /// Replay `record.before` under `seeded` and report whether it lands
    /// exactly on `record.after`.
    fn seeded_replay_reaches(
        terms: &mut ay_core::TermStore,
        seeded: &HashMap<TermId, TermId>,
        record: &PropagatedRewriteRecord,
    ) -> bool {
        let mut throwaway = PropagateValues::new();
        throwaway.seed_substitution(seeded);
        throwaway.rewrite_seeded(terms, record.before) == record.after
    }

    /// Close a seeded substitution map under itself: rewrite every value
    /// under the map until no value changes, mirroring
    /// `VariableSubstitution::substitute_term`'s fixpoint application of its
    /// own map. On an acyclic map the closed map is the same function, so a
    /// replay through the non-chasing `PropagateValues::rewrite` then
    /// reproduces what the chasing producer wrote.
    ///
    /// Bounded and fail-closed on both sides: a map that has not stabilised
    /// within [`MAX_SEED_CLOSURE_ROUNDS`] (the shape a cyclic `x |-> f(x)`
    /// entry would produce, which the producer's own cycle check is supposed
    /// to have refused) returns `None` and the record is dropped, exactly as
    /// it is today.
    fn close_seeded_substitution(
        terms: &mut ay_core::TermStore,
        seeded: &HashMap<TermId, TermId>,
    ) -> Option<HashMap<TermId, TermId>> {
        // Deterministic visit order: the term store is shared, so a
        // hash-order-dependent closure would make sealing (and therefore
        // which proofs certify) vary run to run.
        let mut keys: Vec<TermId> = seeded.keys().copied().collect();
        keys.sort_unstable_by_key(|term| term.index());
        let mut closed = seeded.clone();
        for _round in 0..MAX_SEED_CLOSURE_ROUNDS {
            let mut pass = PropagateValues::new();
            pass.seed_substitution(&closed);
            let mut changed = false;
            let mut next = closed.clone();
            for &key in &keys {
                let value = *closed.get(&key)?;
                let rewritten = pass.rewrite_seeded(terms, value);
                if rewritten != value {
                    next.insert(key, rewritten);
                    changed = true;
                }
            }
            if !changed {
                return Some(closed);
            }
            closed = next;
        }
        None
    }

    pub(super) fn into_current(self, executor: &Executor) -> Option<(TermId, (TermId, u32))> {
        (self
            .query_epoch
            .is_same_epoch(&executor.query_authority_epoch)
            && self.source_context_stamp == executor.ctx.source_context_stamp()
            && executor.ctx.terms.entry_stamp(self.before) == Some(self.before_entry)
            && executor.ctx.terms.entry_stamp(self.after) == Some(self.after_entry))
        .then_some((self.after, (self.before, self.stamp)))
    }
}

/// Epoch- and entry-stamped evidence that one recorded `PropagateValues`
/// harvest `expr ↦ value` really is licensed by its asserted defining
/// equality (#ppp-c7; same seal/consume discipline).
#[must_use = "checked propagation entry evidence must be consumed or discarded"]
pub(super) struct CheckedPropagationEntry {
    query_epoch: QueryAuthorityEpoch,
    source_context_stamp: SourceContextStamp,
    expr: TermId,
    expr_entry: TermEntryStamp,
    value: TermId,
    value_entry: TermEntryStamp,
    source_assertion: TermId,
    source_entry: TermEntryStamp,
    stamp: u32,
}

impl CheckedPropagationEntry {
    pub(super) fn seal(executor: &Executor, entry: &PropagatedEntrySource) -> Option<Self> {
        let (expr, value) = propagation_entry::checked_pair(&executor.ctx.terms, entry)?;
        Some(Self {
            query_epoch: executor.query_authority_epoch.clone(),
            source_context_stamp: executor.ctx.source_context_stamp(),
            expr,
            expr_entry: executor.ctx.terms.entry_stamp(expr)?,
            value,
            value_entry: executor.ctx.terms.entry_stamp(value)?,
            source_assertion: entry.source_assertion,
            source_entry: executor.ctx.terms.entry_stamp(entry.source_assertion)?,
            stamp: entry.stamp,
        })
    }

    pub(super) fn into_current(
        self,
        executor: &Executor,
    ) -> Option<(TermId, (TermId, TermId, u32))> {
        (self
            .query_epoch
            .is_same_epoch(&executor.query_authority_epoch)
            && self.source_context_stamp == executor.ctx.source_context_stamp()
            && executor.ctx.terms.entry_stamp(self.expr) == Some(self.expr_entry)
            && executor.ctx.terms.entry_stamp(self.value) == Some(self.value_entry)
            && executor.ctx.terms.entry_stamp(self.source_assertion) == Some(self.source_entry))
        .then_some((self.expr, (self.value, self.source_assertion, self.stamp)))
    }
}

/// Epoch- and entry-stamped evidence for one qpf premise-forced instance
/// root (#ppp-c7): the exact substitution replay plus, per eliminated
/// disjunct, an independent model-free `false` re-evaluation.
#[must_use = "checked instance-root evidence must be consumed or discarded"]
pub(super) struct CheckedInstanceRootDerivation {
    query_epoch: QueryAuthorityEpoch,
    source_context_stamp: SourceContextStamp,
    quantifier: TermId,
    quantifier_entry: TermEntryStamp,
    values: Vec<TermId>,
    value_entries: Vec<TermEntryStamp>,
    instance: TermId,
    instance_entry: TermEntryStamp,
    asserted: TermId,
    asserted_entry: TermEntryStamp,
    survivor: TermId,
    survivor_entry: TermEntryStamp,
    refuted_disjuncts: Vec<TermId>,
    refuted_entries: Vec<TermEntryStamp>,
}

impl CheckedInstanceRootDerivation {
    pub(super) fn seal(
        executor: &mut Executor,
        record: &QpfPremiseForcedInstanceRecord,
    ) -> Option<Self> {
        let TermData::Forall(bindings, body, _) = executor.ctx.terms.get(record.quantifier).clone()
        else {
            return None;
        };
        if bindings.is_empty() || bindings.len() != record.values.len() {
            return None;
        }
        let mut substitution = HashMap::default();
        for ((name, sort), &value) in bindings.iter().zip(&record.values) {
            if executor.ctx.terms.sort(value) != sort {
                return None;
            }
            substitution.insert(name.clone(), value);
        }
        if crate::ematching::subst_vars_exact_qf(&mut executor.ctx.terms, body, &substitution)?
            != record.instance
        {
            return None;
        }
        // Partition the raw disjuncts by an independent model-free
        // evaluation: eliminated disjuncts must be definitely `false`
        // without any model, the rest must be one unique survivor. The
        // strict checker later re-decides every eliminated disjunct by
        // exhaustive bounded evaluation — this replay carries no authority.
        let empty_model = crate::executor::model::Model::empty();
        let mut survivor: Option<TermId> = None;
        let mut refuted_disjuncts: Vec<TermId> = Vec::new();
        match executor.ctx.terms.get(record.instance).clone() {
            TermData::App(sym, disjuncts) if sym.name() == "or" && disjuncts.len() >= 2 => {
                for &disjunct in &disjuncts {
                    if matches!(
                        executor.evaluate_term(&empty_model, disjunct),
                        crate::executor::model::EvalValue::Bool(false)
                    ) {
                        if !refuted_disjuncts.contains(&disjunct) {
                            refuted_disjuncts.push(disjunct);
                        }
                        continue;
                    }
                    match survivor {
                        None => survivor = Some(disjunct),
                        Some(existing) if existing == disjunct => {}
                        Some(_) => return None,
                    }
                }
            }
            _ => survivor = Some(record.instance),
        }
        let survivor = survivor?;
        if refuted_disjuncts.is_empty() && survivor != record.instance {
            return None;
        }
        Some(Self {
            query_epoch: executor.query_authority_epoch.clone(),
            source_context_stamp: executor.ctx.source_context_stamp(),
            quantifier: record.quantifier,
            quantifier_entry: executor.ctx.terms.entry_stamp(record.quantifier)?,
            values: record.values.clone(),
            value_entries: record
                .values
                .iter()
                .map(|&value| executor.ctx.terms.entry_stamp(value))
                .collect::<Option<Vec<_>>>()?,
            instance: record.instance,
            instance_entry: executor.ctx.terms.entry_stamp(record.instance)?,
            asserted: record.asserted,
            asserted_entry: executor.ctx.terms.entry_stamp(record.asserted)?,
            survivor,
            survivor_entry: executor.ctx.terms.entry_stamp(survivor)?,
            refuted_entries: refuted_disjuncts
                .iter()
                .map(|&disjunct| executor.ctx.terms.entry_stamp(disjunct))
                .collect::<Option<Vec<_>>>()?,
            refuted_disjuncts,
        })
    }

    pub(super) fn into_current(
        self,
        executor: &Executor,
    ) -> Option<FragmentInstanceRootDerivation> {
        (self
            .query_epoch
            .is_same_epoch(&executor.query_authority_epoch)
            && self.source_context_stamp == executor.ctx.source_context_stamp()
            && executor.ctx.terms.entry_stamp(self.quantifier) == Some(self.quantifier_entry)
            && executor.ctx.terms.entry_stamp(self.instance) == Some(self.instance_entry)
            && executor.ctx.terms.entry_stamp(self.asserted) == Some(self.asserted_entry)
            && executor.ctx.terms.entry_stamp(self.survivor) == Some(self.survivor_entry)
            && self.value_entries.iter().copied().map(Some).eq(self
                .values
                .iter()
                .map(|&value| executor.ctx.terms.entry_stamp(value)))
            && self.refuted_entries.iter().copied().map(Some).eq(self
                .refuted_disjuncts
                .iter()
                .map(|&disjunct| executor.ctx.terms.entry_stamp(disjunct))))
        .then_some(FragmentInstanceRootDerivation {
            quantifier: self.quantifier,
            values: self.values,
            instance: self.instance,
            survivor: self.survivor,
            refuted_disjuncts: self.refuted_disjuncts,
        })
    }
}

mod sealed_maps;

pub(super) use sealed_maps::{
    sealed_context_derivations, sealed_fragment_derivation_maps, sealed_instance_root_derivations,
    sealed_propagation_environment,
};

#[cfg(test)]
mod tests;

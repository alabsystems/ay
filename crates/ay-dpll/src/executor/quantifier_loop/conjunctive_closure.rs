// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! (#conjunctive-closure) Which universals of a snapshot are consequences of
//! it, once the instances of the ones already known to be consequences are
//! counted as facts.
//!
//! # Why
//!
//! Verus states every fuel-controlled definition as
//! `(=> (fuel_bool f) (forall ...))` and asserts `(fuel_bool_default f)`. The
//! prelude axiom `(=> fuel_defaults (forall id. fuel_bool(id) =
//! fuel_bool_default(id)))`, with `fuel_defaults` asserted, is instantiated at
//! `f` in the first E-matching round, and from the second round on
//! `(fuel_bool f)` is a unit fact (#unit-bool-eq) and the definition is
//! instantiated. The refutation then rests on instances of two universals that
//! sit under `=>`. `degrade@277` keeps a refutation only when no such
//! universal was treated as entailed, unless it can show the universal
//! conjunctive itself, and its walk
//! (`forall_ids_entailed_modulo_harvested_units`) sees the snapshot's unit
//! facts only: `(fuel_bool f)` is not among them, so every such refutation was
//! discarded (Verus fix queue, row D1).
//!
//! # The closure
//!
//! `C₀` is the conjunctive set of the snapshot `S` taken modulo `S`'s own unit
//! facts. Each round adds, as facts, the exact instances `B[t̄]` of every
//! recorded E-matching binding `(Q, t̄)` whose universal `Q` is already in the
//! set, plus the support axioms the solve asserted, and walks `S` again modulo
//! the unit facts of `S` and those instances. The set is the union over
//! rounds.
//!
//! The bindings of unconditional universals are recorded too, not only the
//! support axioms. The solve skips an instance the presolve model already
//! satisfies, so it never becomes a support axiom, yet the E-matcher may have
//! read a unit fact through it: `(fuel_bool f)` comes from the instance
//! `(= (fuel_bool f) (fuel_bool_default f))`, which the model satisfies. Without
//! its binding the closure cannot see the guard the matcher saw.
//!
//! Every member is entailed by `S`, by induction: the members of `C₀` are
//! (that is the walk's own contract); an instance of an entailed universal is
//! entailed (`∀x̄.B ⊨ B[t̄]` for every ground `t̄`); unit facts of entailed
//! formulas are entailed; and a universal the walk reaches modulo entailed
//! facts is entailed. The union is taken because the walk is not monotone in
//! its facts (a new unit can satisfy an implication and stop the descent into
//! it), while entailment is: a member stays entailed whatever is added later.
//!
//! Nothing here trusts the E-matcher's own record of what it treated as
//! entailed. A binding contributes only when this closure has shown its
//! universal entailed independently, so a record of a universal the closure
//! cannot reach is simply never replayed, and the gate keeps its distrust.
//! The instance is rebuilt by exact substitution from the binding, never
//! taken from the matcher.

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::TermId;

use super::super::Executor;
use crate::ematching::{contains_quantifier, ForallInstantiationProvenance};

/// Most bindings kept per check-sat. Past it, later ones are dropped: the gate
/// then sees fewer facts, which can only keep its distrust.
const MAX_RECORDS: usize = 20_000;
/// Most closure rounds. A Verus fuel chain needs two.
const MAX_ROUNDS: usize = 8;
/// Enumerated and E-matched binder values kept per public decision as
/// witness hints.
const MAX_WITNESS_HINTS: usize = 64;

/// E-matched bindings `(universal, ground tuple)` of the current check-sat,
/// deduplicated: conditional, guarded and unconditional ones alike.
#[derive(Debug, Default)]
pub(crate) struct MatchedInstanceRecords {
    records: Vec<(TermId, Vec<TermId>)>,
    seen: HashSet<(TermId, Vec<TermId>)>,
}

impl MatchedInstanceRecords {
    pub(in crate::executor) fn clear(&mut self) {
        self.records.clear();
        self.seen.clear();
    }

    fn push(&mut self, quantifier: TermId, binding: &[TermId]) {
        if self.records.len() >= MAX_RECORDS {
            return;
        }
        let key = (quantifier, binding.to_vec());
        if self.seen.insert(key.clone()) {
            self.records.push(key);
        }
    }
}

impl Executor {
    /// Record E-matched bindings. Called by every E-matching lane with its
    /// conditional, guarded and unconditional provenance, before any instance
    /// is filtered out.
    ///
    /// The binder values also go to `instance_witness_hints`
    /// (#iff-split-implied-authority), as the entailed lane's enumerated ones
    /// do: an instance at one of them may be what refuted the query, and the
    /// implied-universal firewall lane can name it in a certificate only if it
    /// is told the value.
    pub(in crate::executor) fn record_matched_instances(
        &mut self,
        records: &[ForallInstantiationProvenance],
    ) {
        for record in records {
            self.matched_instance_records
                .push(record.quantifier, &record.binding);
            for &value in &record.binding {
                self.note_instance_witness_hint(value);
            }
        }
    }

    /// Bounded, deduplicated; a full ledger drops later values, which can only
    /// cost the consuming lane a candidate.
    pub(super) fn note_instance_witness_hint(&mut self, value: TermId) {
        if self.instance_witness_hints.len() >= MAX_WITNESS_HINTS
            || self
                .instance_witness_hints
                .iter()
                .any(|(_, hint)| *hint == value)
        {
            return;
        }
        let sort = self.ctx.terms.sort(value).clone();
        self.instance_witness_hints.push((sort, value));
    }

    /// The universals of `snapshot` that are consequences of it, closed under
    /// the instances of the ones already found (module doc).
    pub(super) fn conjunctive_forall_closure(&mut self, snapshot: &[TermId]) -> HashSet<TermId> {
        let mut conjunctive = self.forall_ids_entailed_modulo_harvested_units(snapshot, &[]);
        if self.matched_instance_records.records.is_empty() {
            return conjunctive;
        }
        let records = self.matched_instance_records.records.clone();
        let mut replayed = vec![false; records.len()];
        // Instances of unconditional conjuncts that the solve asserted are
        // consequences outright; the ones it skipped come from the records.
        let mut facts: Vec<TermId> = self
            .active_support_axioms
            .iter()
            .map(|lit| lit.term)
            .filter(|&term| !contains_quantifier(&self.ctx.terms, term))
            .collect();
        for _ in 0..MAX_ROUNDS {
            let before = facts.len();
            for (index, (quantifier, binding)) in records.iter().enumerate() {
                if replayed[index] || !conjunctive.contains(quantifier) {
                    continue;
                }
                replayed[index] = true;
                let Some(instance) = self.exact_forall_instance(*quantifier, binding) else {
                    continue;
                };
                if !contains_quantifier(&self.ctx.terms, instance) {
                    facts.push(instance);
                }
            }
            if facts.len() == before {
                break;
            }
            let next = self.forall_ids_entailed_modulo_harvested_units(snapshot, &facts);
            let grown = next
                .iter()
                .any(|quantifier| !conjunctive.contains(quantifier));
            conjunctive.extend(next);
            if !grown {
                break;
            }
        }
        conjunctive
    }
}

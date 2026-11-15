// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::preprocess::guarded_store_batch as batch;
use crate::preprocess::{
    PreprocessingPass, PropagationRecords, RecordedVariableSubstitution, VariableSubstitution,
};

pub(super) struct Fixture {
    pub(super) terms: TermStore,
    pub(super) roots: Vec<TermId>,
    pub(super) records: HashMap<TermId, (TermId, u32)>,
    pub(super) entries: HashMap<TermId, (TermId, TermId, u32)>,
    pub(super) units: Vec<ArrayUnitDerivation>,
    pub(super) before: TermId,
    pub(super) after: TermId,
    pub(super) scalar: TermId,
    pub(super) value: TermId,
    pub(super) payload: TermId,
    pub(super) high: TermId,
    pub(super) guard: TermId,
    pub(super) activation: TermId,
    pub(super) stamp: u32,
}

pub(super) fn app(terms: &mut TermStore, name: &str, args: &[TermId]) -> TermId {
    terms.mk_app(Symbol::named(name), args, Sort::Bool)
}

pub(super) fn allow(_: usize, _: usize) -> bool {
    true
}

fn record_substitution(
    terms: &mut TermStore,
    roots: &[TermId],
    discovered: batch::GuardedStoreBatch,
) -> (PropagationRecords, Vec<ArrayUnitDerivation>) {
    let source_sets = roots.iter().map(|&root| vec![root]).collect::<Vec<_>>();
    let prepared = batch::install::prepare(
        terms,
        roots,
        roots,
        &source_sets,
        discovered,
        &mut |_, _| true,
    )
    .unwrap();
    let (mut working, mut sources, units) = prepared.into_parts();
    let substitution = Arc::new(Mutex::new(VariableSubstitution::new()));
    let propagation = Arc::new(Mutex::new(PropagateValues::new()));
    let mut pass = RecordedVariableSubstitution::new(
        substitution,
        Arc::clone(&propagation),
        Box::new(|_, _| true),
    );
    assert!(pass.apply_with_sources(terms, &mut working, &mut sources));
    let recorded = propagation
        .lock()
        .unwrap()
        .take_propagation_records()
        .unwrap();
    (recorded, units)
}

impl Fixture {
    pub(super) fn new(width: u32) -> Self {
        let mut terms = TermStore::new();
        // The old scalar variable precedes H; the newly derived ITE follows H.
        // Canonical ordering must therefore reverse this equality after replay.
        let value = terms.mk_var("original scalar observation", Sort::bitvec(width));
        let array = terms.mk_var(
            "original array",
            Sort::array(Sort::bitvec(8), Sort::bitvec(width)),
        );
        let guards = [terms.mk_var("g", Sort::Bool), terms.mk_var("h", Sort::Bool)];
        let activation = terms.mk_var("q", Sort::Bool);
        let fill = terms.mk_bitvec(0.into(), width);
        let base = terms.mk_const_array(Sort::bitvec(8), fill);
        let key = terms.mk_bitvec(7.into(), 8);
        let high_value = num_bigint::BigInt::from(1) << (width - 1);
        let high = terms.mk_bitvec(high_value.clone(), width);
        let next = terms.mk_bitvec(high_value + 1, width);
        let scalar = app(&mut terms, "=", &[value, high]);
        let mut roots = Vec::new();
        for (guard, cell) in guards.into_iter().zip([high, next]) {
            let stored = terms.mk_app(
                Symbol::named("store"),
                [base, key, cell],
                terms.sort(array).clone(),
            );
            let equality = app(&mut terms, "=", &[array, stored]);
            let observation = app(&mut terms, "=", &[value, cell]);
            let body = app(&mut terms, "and", &[equality, observation]);
            let not_guard = terms.mk_not_raw(guard);
            roots.push(app(&mut terms, "or", &[not_guard, body]));
        }
        let before = roots[0];
        let cover = app(&mut terms, "or", &guards);
        let not_activation = terms.mk_not_raw(activation);
        roots.push(app(&mut terms, "or", &[not_activation, cover]));
        roots.push(activation);
        let read = terms.mk_app(Symbol::named("select"), [array, key], Sort::bitvec(width));
        roots.push(app(&mut terms, "=", &[value, read]));

        let discovered = batch::discover(&mut terms, &roots, &mut |_, _| true).unwrap();
        assert_eq!(discovered.definitions().len(), 1);
        let replacement = discovered.definitions()[0].replacement();
        let TermData::App(_, replacement_args) = terms.get(replacement) else {
            panic!("store")
        };
        let payload = replacement_args[2];
        let TermData::Ite(guard, _, _) = terms.get(payload) else {
            panic!("literal ITE")
        };
        let guard = *guard;
        assert_eq!(guard, guards[0], "source discovery retains the first case");
        let (recorded, units) = record_substitution(&mut terms, &roots, discovered);
        let row = recorded
            .rewrites
            .iter()
            .find(|row| row.before == before)
            .unwrap();
        let (after, stamp) = (row.after, row.stamp);
        let exact = terms.mk_eq_coerce_no_ite_expand(payload, high);
        assert!(
            matches!(terms.get(exact), TermData::App(_, args) if args.as_slice() == [high, payload])
        );
        let duplicate_body = terms.mk_and(vec![exact, exact]);
        assert_eq!(
            duplicate_body, exact,
            "actual Boolean producer deduplicates"
        );
        let not_guard = terms.mk_not_raw(guard);
        let expected_after = terms.mk_or(vec![not_guard, duplicate_body]);
        assert_eq!(after, expected_after);
        assert!(recorded
            .entries
            .iter()
            .any(|entry| entry.expr == value && entry.value == read));
        let mut records = HashMap::default();
        for row in recorded.rewrites {
            records.entry(row.after).or_insert((row.before, row.stamp));
        }
        let mut entries = HashMap::default();
        for entry in recorded.entries {
            entries
                .entry(entry.expr)
                .or_insert((entry.value, entry.source_assertion, entry.stamp));
        }
        Self {
            terms,
            roots,
            records,
            entries,
            units,
            before,
            after,
            scalar,
            value,
            payload,
            high,
            guard,
            activation,
            stamp,
        }
    }

    pub(super) fn plan(&mut self, target: TermId) -> Option<(Proof, ProofId)> {
        let set = self.roots.iter().copied().collect();
        let mut cx = PlanCx::new(&set, &self.roots, &self.records, &self.entries, &[], false)
            .with_array_units(&self.units, &allow);
        let result = PropagationChainPlanner {
            terms: &mut self.terms,
        }
        .plan_derive_clause(&mut cx, target);
        if result.is_none() {
            self.report_decline(&cx);
        }
        let id = result?;
        Some((cx.chain, id))
    }

    pub(super) fn changed_child(&mut self) -> (Proof, EqRes) {
        let set = self.roots.iter().copied().collect();
        let mut cx = PlanCx::new(&set, &self.roots, &self.records, &self.entries, &[], false)
            .with_array_units(&self.units, &allow);
        let child = PropagationChainPlanner {
            terms: &mut self.terms,
        }
        .plan_derive_eq(&mut cx, self.value, self.stamp)
        .unwrap();
        if !matches!(child, EqRes::Changed { to, .. } if to == self.payload) {
            self.report_decline(&cx);
        }
        assert!(matches!(child, EqRes::Changed { to, .. } if to == self.payload));
        (cx.chain, child)
    }

    fn report_decline(&self, cx: &PlanCx<'_>) {
        eprintln!(
            "scalar replay remaining={} steps={}",
            cx.budget,
            cx.chain.steps.len()
        );
        for (&term, &(value, source, stamp)) in &self.entries {
            let result = cx.eq_memo.get(&(term, self.stamp, cx.scalar_equality_mode));
            let target = result.and_then(|result| match result {
                Some(EqRes::Changed { to, .. }) => Some(*to),
                _ => None,
            });
            eprintln!(
                "entry {term:?}->{value:?} source={source:?} stamp={stamp} replay={target:?}"
            );
        }
        for unit in &self.units {
            let mut charged = (0usize, 0usize);
            let accepted = unit
                .reauthenticate(&self.terms, &self.roots, &mut |work, bytes| {
                    charged.0 += work;
                    charged.1 += bytes;
                    true
                })
                .is_some();
            eprintln!(
                "unit {:?} authenticated={accepted} work={} bytes={} local-equivalent={}",
                unit.term(),
                charged.0,
                charged.1,
                charged.0 + charged.1.div_ceil(64)
            );
        }
    }

    pub(super) fn replace_scalar_target(&mut self, scalar: TermId) -> TermId {
        let exact = app(&mut self.terms, "=", &[self.high, self.payload]);
        let body = app(&mut self.terms, "and", &[exact, scalar]);
        let not_guard = self.terms.mk_not_raw(self.guard);
        let target = app(&mut self.terms, "or", &[not_guard, body]);
        self.records.insert(target, (self.before, self.stamp));
        target
    }
}

pub(super) fn authenticate(
    terms: &TermStore,
    roots: &[TermId],
    proof: &Proof,
) -> Result<ay_proof::AuthenticatedPremiseClauses, ay_proof::ProofCheckError> {
    ay_proof::authenticate_premise_clauses_strict_with_context_and_progress(
        proof,
        terms,
        None,
        None,
        roots,
        &mut |_, _| true,
    )
}

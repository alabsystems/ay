// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

pub(in crate::preprocess::guarded_store_definitions::batch) struct Fixture {
    pub(in crate::preprocess::guarded_store_definitions::batch) terms: TermStore,
    pub(in crate::preprocess::guarded_store_definitions::batch) roots: Vec<TermId>,
    pub(in crate::preprocess::guarded_store_definitions::batch) variable: TermId,
    pub(in crate::preprocess::guarded_store_definitions::batch) guards: [TermId; 2],
    pub(in crate::preprocess::guarded_store_definitions::batch) activation: TermId,
    pub(in crate::preprocess::guarded_store_definitions::batch) cover: TermId,
    pub(in crate::preprocess::guarded_store_definitions::batch) aliases: [TermId; 2],
    pub(in crate::preprocess::guarded_store_definitions::batch) stores: [TermId; 2],
}

pub(super) fn app(terms: &mut TermStore, name: &str, args: &[TermId]) -> TermId {
    terms.mk_app(Symbol::named(name), args, Sort::Bool)
}

impl Fixture {
    pub(in crate::preprocess::guarded_store_definitions::batch) fn new(width: u32) -> Self {
        let mut terms = TermStore::new();
        let fill = terms.mk_bitvec(3.into(), width);
        let base = terms.mk_const_array(Sort::Bool, fill);
        let sort = terms.sort(base).clone();
        let variable = terms.mk_var("arbitrary memory", sort.clone());
        let guards = [
            terms.mk_var("right", Sort::Bool),
            terms.mk_var("left", Sort::Bool),
        ];
        let activation = terms.mk_var("originally enabled", Sort::Bool);
        let mut roots = Vec::new();
        let mut stores = [base; 2];
        for index in 0..2 {
            let mut value = num_bigint::BigInt::from(index);
            if width == 129 {
                value += num_bigint::BigInt::from(1) << 128;
            }
            let value = terms.mk_bitvec(value, width);
            let key = terms.false_term();
            stores[index] = terms.mk_app(Symbol::named("store"), [base, key, value], sort.clone());
            let equality = raw_eq(&mut terms, stores[index], variable);
            let truth = terms.true_term();
            let nested = app(&mut terms, "and", &[truth, equality]);
            let not_guard = terms.mk_not_raw(guards[index]);
            roots.push(app(&mut terms, "or", &[nested, not_guard]));
        }
        let alias = terms.mk_var("forwarded memory", sort);
        let array_alias = raw_eq(&mut terms, alias, variable);
        let scalar_left = terms.mk_var("opaque scalar source", Sort::bitvec(width));
        let scalar_right = terms.mk_var("opaque scalar target", Sort::bitvec(width));
        let scalar_alias = raw_eq(&mut terms, scalar_left, scalar_right);
        let cover = app(&mut terms, "or", &guards);
        let inner = app(&mut terms, "and", &[scalar_alias, cover]);
        let body = app(&mut terms, "and", &[array_alias, inner]);
        let not_activation = terms.mk_not_raw(activation);
        roots.push(app(&mut terms, "or", &[not_activation, body]));
        roots.push(activation);
        Self {
            terms,
            roots,
            variable,
            guards,
            activation,
            cover,
            aliases: [array_alias, scalar_alias],
            stores,
        }
    }

    pub(in crate::preprocess::guarded_store_definitions::batch) fn discover(
        &mut self,
    ) -> Option<GuardedStoreBatch> {
        discover(&mut self.terms, &self.roots, &mut |_, _| true)
    }

    pub(super) fn authenticate(&self, proof: &Proof, conclusion: ProofId, unit: TermId) -> bool {
        ay_proof::authenticate_premise_clauses_strict_with_context_and_progress(
            proof,
            &self.terms,
            None,
            None,
            &self.roots,
            &mut |_, _| true,
        )
        .is_ok_and(|checked| checked.clause(conclusion) == Some([unit].as_slice()))
    }
}

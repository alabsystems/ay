// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) struct Fixture {
    pub(super) terms: TermStore,
    pub(super) base: TermId,
    pub(super) key: TermId,
    pub(super) left: TermId,
    pub(super) right: TermId,
    pub(super) variable: TermId,
    pub(super) replacement: TermId,
    pub(super) source: TermId,
    pub(super) roots: Vec<TermId>,
    pub(super) records: HashMap<TermId, (TermId, u32)>,
    pub(super) entries: HashMap<TermId, (TermId, TermId, u32)>,
}

impl Fixture {
    pub(super) fn new(width: u32) -> Self {
        let mut terms = TermStore::new();
        let array = Sort::array(Sort::bitvec(8), Sort::bitvec(width));
        let base = terms.mk_var("base", array.clone());
        let variable = terms.mk_var("variable", array.clone());
        let key = terms.mk_var("key", Sort::bitvec(8));
        let left = terms.mk_var("left", Sort::bitvec(width));
        let right = terms.mk_var("right", Sort::bitvec(width));
        let replacement = terms.mk_app(Symbol::named("store"), [base, key, left], array);
        let source = raw_eq(&mut terms, variable, replacement);
        Self {
            terms,
            base,
            key,
            left,
            right,
            variable,
            replacement,
            source,
            roots: vec![source],
            records: HashMap::default(),
            entries: [(variable, (replacement, source, 1))].into_iter().collect(),
        }
    }

    pub(super) fn store(&mut self, base: TermId, key: TermId, value: TermId) -> TermId {
        self.terms.mk_app(
            Symbol::named("store"),
            [base, key, value],
            self.terms.sort(base).clone(),
        )
    }

    pub(super) fn read(&mut self, array: TermId, key: TermId) -> TermId {
        let Sort::Array(sort) = self.terms.sort(array) else {
            panic!("array fixture")
        };
        let result = sort.element_sort.clone();
        self.terms
            .mk_app(Symbol::named("select"), [array, key], result)
    }

    pub(super) fn plan(&mut self, target: TermId) -> Option<(Proof, ProofId)> {
        let set = self.roots.iter().copied().collect();
        let mut cx = PlanCx::new(&set, &self.roots, &self.records, &self.entries, &[], false);
        let mut planner = PropagationChainPlanner {
            terms: &mut self.terms,
        };
        let id = planner.plan_derive_clause(&mut cx, target)?;
        Some((cx.chain, id))
    }

    pub(super) fn store_term_for_right(&mut self) -> TermId {
        self.store(self.base, self.key, self.right)
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

pub(super) fn assert_source(
    terms: &TermStore,
    roots: &[TermId],
    proof: &Proof,
    id: ProofId,
    term: TermId,
) {
    let checked = authenticate(terms, roots, proof).expect("strict source-bound array replay");
    assert_eq!(checked.clause(id), Some([term].as_slice()));
}

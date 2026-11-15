// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::preprocess::{PreprocessingPass, RecordedVariableSubstitution, VariableSubstitution};
use std::sync::{Arc, Mutex};

pub(super) struct Fixture {
    pub terms: TermStore,
    pub originals: Vec<TermId>,
    pub before: TermId,
    pub after: TermId,
    pub target: TermId,
    pub records: HashMap<TermId, (TermId, u32)>,
    pub entries: HashMap<TermId, (TermId, TermId, u32)>,
}

impl Fixture {
    pub fn recorded() -> Self {
        let mut terms = TermStore::new();
        let length = terms.mk_var("length", Sort::bitvec(64));
        let fill = terms.mk_var("fill", Sort::bitvec(8));
        let x = terms.mk_var("x", Sort::bitvec(8));
        let index = terms.mk_var("__gpc1", Sort::bitvec(64));
        let array = terms.mk_var("a", Sort::array(Sort::bitvec(64), Sort::bitvec(8)));
        let function = terms.mk_app(Symbol::named("f"), [terms.true_term(), x], Sort::bitvec(8));
        let sixty_five = terms.mk_bitvec(65.into(), 64);
        let fill_source = terms.mk_app(Symbol::named("="), [fill, function], Sort::Bool);
        let length_source = terms.mk_app(Symbol::named("="), [length, sixty_five], Sort::Bool);
        let definitions = terms.mk_app(
            Symbol::named("and"),
            [fill_source, length_source],
            Sort::Bool,
        );
        let guard = terms.mk_app(Symbol::named("bvult"), [index, length], Sort::Bool);
        let thirty_two = terms.mk_bitvec(32.into(), 64);
        let lower_bound = terms.mk_app(Symbol::named("bvule"), [thirty_two, index], Sort::Bool);
        let read = terms.mk_app(Symbol::named("select"), [array, index], Sort::bitvec(8));
        let wrong_value = terms.mk_app(Symbol::named("="), [fill, read], Sort::Bool);
        let wrong_value = terms.mk_not_raw(wrong_value);
        let branch = terms.mk_app(
            Symbol::named("and"),
            [guard, lower_bound, wrong_value],
            Sort::Bool,
        );
        let zero = terms.mk_bitvec(0.into(), 64);
        let empty = terms.mk_app(Symbol::named("="), [length, zero], Sort::Bool);
        let before = terms.mk_app(Symbol::named("or"), [branch, empty], Sort::Bool);
        let originals = vec![definitions, before];

        // The actual early-ABV wrapper supplies both scalar variable licenses
        // and the exact canonical parent record. No synthetic rewrite or
        // auxiliary canonicalization pass is added to this fixture.
        let propagation = Arc::new(Mutex::new(PropagateValues::new()));
        let mut pass = RecordedVariableSubstitution::new(
            Arc::new(Mutex::new(VariableSubstitution::new())),
            Arc::clone(&propagation),
            Box::new(|_, _| true),
        );
        let mut working = vec![fill_source, length_source, before];
        assert!(pass.apply(&mut terms, &mut working));
        let after = working[2];
        assert_ne!(after, before);
        let recorded = propagation
            .lock()
            .unwrap()
            .take_propagation_records()
            .unwrap();
        let substitutions: HashMap<_, _> =
            recorded.entries.iter().map(|e| (e.expr, e.value)).collect();
        assert_eq!(substitutions.get(&length), Some(&sixty_five));
        assert_eq!(substitutions.get(&fill), Some(&function));

        assert!(recorded
            .rewrites
            .iter()
            .any(|r| r.before == before && r.after == after));
        let target = terms.mk_bvult(index, sixty_five);
        let rewritten_equality = terms.mk_eq_coerce_no_ite_expand(function, read);
        let rewritten_disagreement = terms.mk_not(rewritten_equality);
        let positional = vec![target, lower_bound, rewritten_disagreement];
        let TermData::App(head, canonical_args) = terms.get(after) else {
            panic!("canonical AND");
        };
        assert_eq!(head.name(), "and");
        assert_eq!(canonical_args.len(), 3);
        assert_ne!(
            &positional, canonical_args,
            "actual canonicalization must reorder the changed guard past the unchanged bound"
        );
        let mut sorted = positional.clone();
        sorted.sort_unstable();
        assert_eq!(&sorted, canonical_args);
        assert!(canonical_args.contains(&target));

        let mut records = HashMap::default();
        let mut entries = HashMap::default();
        for record in recorded.rewrites {
            records
                .entry(record.after)
                .or_insert((record.before, record.stamp));
        }
        for entry in recorded.entries {
            entries
                .entry(entry.expr)
                .or_insert((entry.value, entry.source_assertion, entry.stamp));
        }
        Self {
            terms,
            originals,
            before,
            after,
            target,
            records,
            entries,
        }
    }

    pub fn plan(&mut self, target: TermId, budget: usize) -> Option<(Proof, ProofId)> {
        let source_set = self.originals.iter().copied().collect();
        let mut cx = PlanCx::new(
            &source_set,
            &self.originals,
            &self.records,
            &self.entries,
            &[],
            true,
        );
        cx.budget = budget;
        assert!(cx.eqdv_by_atom.is_none());
        let result = PropagationChainPlanner {
            terms: &mut self.terms,
        }
        .plan_derive_clause(&mut cx, target);
        assert!(cx.in_progress.is_empty());
        assert!(cx.eq_in_progress.is_empty());
        if result.is_none() {
            cx.rollback(0);
            assert!(cx.chain.steps.is_empty());
            assert!(cx.clause_memo.is_empty());
            assert!(cx
                .eq_memo
                .values()
                .all(|entry| !matches!(entry, Some(EqRes::Changed { .. }))));
        }
        result.map(|id| (cx.chain, id))
    }

    pub fn authenticate(&self, proof: &Proof, conclusion: ProofId, target: TermId) {
        assert!(
            ay_proof::validate_reachable_assumes_in_problem_scope(proof, &self.originals).is_ok()
        );
        let checked = ay_proof::authenticate_premise_clauses_strict_with_context_and_progress(
            proof,
            &self.terms,
            None,
            None,
            &self.originals,
            &mut |_, _| true,
        )
        .expect("existing strict rules must authenticate the exact original scope");
        assert_eq!(checked.clause(conclusion), Some([target].as_slice()));
        assert!(!proof
            .steps
            .iter()
            .any(|step| matches!(step, ProofStep::Assume(t) if *t == self.after || *t == target)));
    }
}

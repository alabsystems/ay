// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

mod boundaries;
mod meter_tests;

#[derive(Clone, Copy)]
enum Rule {
    ForallInst,
    Skolem,
}

struct Fixture {
    terms: TermStore,
    body: TermId,
    quantified: TermId,
    instance: TermId,
    witness: TermId,
    implication: TermId,
    equality: TermId,
}

impl Fixture {
    fn new(width: usize) -> Self {
        let mut terms = TermStore::new();
        let x = terms.mk_var("meter_x", Sort::Int);
        let body = terms.mk_app(Symbol::named("meter_p"), vec![x; width], Sort::Bool);
        let quantified = terms.mk_forall(vec![("meter_x".to_string(), Sort::Int)], body);
        let witness = terms.mk_var("meter_w", Sort::Int);
        terms.mark_skolem_symbol("meter_w");
        let instance = terms.mk_app(Symbol::named("meter_p"), vec![witness; width], Sort::Bool);
        let not_quantified = terms.mk_not_raw(quantified);
        let implication = terms.mk_app(Symbol::named("or"), [not_quantified, instance], Sort::Bool);
        let equality = terms.mk_app(Symbol::named("="), [quantified, instance], Sort::Bool);
        Self {
            terms,
            body,
            quantified,
            instance,
            witness,
            implication,
            equality,
        }
    }

    fn validate(
        &self,
        rule: Rule,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<(), ProofCheckError> {
        match rule {
            Rule::ForallInst => validate_forall_inst_with_progress(
                &self.terms,
                ProofId(0),
                &[self.implication],
                0,
                &[self.witness],
                progress,
            ),
            Rule::Skolem => validate_sko_forall_with_progress(
                &self.terms,
                ProofId(0),
                &[self.equality],
                0,
                &[self.witness],
                progress,
            ),
        }
    }

    fn replace_entries(&mut self, entries: Vec<(TermData, Sort)>) {
        let (true_id, false_id) = self.terms.boolean_constant_ids();
        let counter = self.terms.var_counter();
        self.terms = TermStore::from_entries(entries, true_id, false_id, counter);
        self.terms.mark_skolem_symbol("meter_w");
    }
}

fn assert_resource<T>(result: Result<T, ProofCheckError>) {
    assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
}

#[test]
fn callback_controls_match_both_legacy_validators() {
    let fixture = Fixture::new(3);
    validate_forall_inst(
        &fixture.terms,
        ProofId(0),
        &[fixture.implication],
        0,
        &[fixture.witness],
    )
    .expect("legacy forall control");
    validate_sko_forall(
        &fixture.terms,
        ProofId(0),
        &[fixture.equality],
        0,
        &[fixture.witness],
    )
    .expect("legacy Skolem control");
    for rule in [Rule::ForallInst, Rule::Skolem] {
        fixture
            .validate(rule, &mut |_, _| true)
            .expect("metered exact substitution");
        assert_resource(fixture.validate(rule, &mut |_, _| false));
        assert_resource(fixture.validate(rule, &mut |_, bytes| bytes == 0));
    }
}

#[test]
fn first_middle_and_final_cancellation_never_reach_success() {
    let fixture = Fixture::new(3);
    for rule in [Rule::ForallInst, Rule::Skolem] {
        let mut trace = Vec::new();
        fixture
            .validate(rule, &mut |work, bytes| {
                trace.push((work, bytes));
                true
            })
            .expect("trace control");
        assert_eq!(trace.last(), Some(&(0, 0)));
        for stop in [1, trace.len() / 2, trace.len()] {
            let mut calls = 0;
            assert_resource(fixture.validate(rule, &mut |_, _| {
                calls += 1;
                calls < stop
            }));
            assert_eq!(calls, stop, "callback refusal must propagate immediately");
        }
    }
}

#[test]
fn duplicate_source_edges_cannot_hide_behind_distinct_node_limit() {
    let fixture = Fixture::new(4_096);
    for rule in [Rule::ForallInst, Rule::Skolem] {
        let mut spent = 0usize;
        assert_resource(fixture.validate(rule, &mut |work, _| {
            let Some(next) = spent.checked_add(work) else {
                return false;
            };
            if next > 1_024 {
                return false;
            }
            spent = next;
            true
        }));
        fixture
            .validate(rule, &mut |_, _| true)
            .expect("wide exact source remains valid with sufficient allowance");
    }
}

#[test]
fn strict_dispatch_does_not_append_clause_after_refusal() {
    let fixture = Fixture::new(1);
    for (rule, conclusion) in [
        (AletheRule::ForallInst, fixture.implication),
        (AletheRule::Skolem, fixture.equality),
    ] {
        let step = ProofStep::Step {
            rule,
            clause: vec![conclusion],
            premises: vec![],
            args: vec![fixture.witness],
        };
        let mut derived = Vec::new();
        assert_resource(crate::checker::validate_step_with_datatypes_and_progress(
            &fixture.terms,
            &mut derived,
            ProofId(0),
            &step,
            true,
            None,
            None,
            None,
            None,
            None,
            None,
            None,
            &mut |_, _| false,
        ));
        assert!(derived.is_empty());
        crate::checker::validate_step_with_datatypes_and_progress(
            &fixture.terms,
            &mut derived,
            ProofId(0),
            &step,
            true,
            None,
            None,
            None,
            None,
            None,
            None,
            None,
            &mut |_, _| true,
        )
        .expect("valid direct dispatch control");
        assert_eq!(derived, vec![Some(vec![conclusion])]);
    }
}

#[test]
fn authority_helper_retains_the_callers_proof_wide_work_counter() {
    let fixture = Fixture::new(1);
    let mut work = SKOLEM_TERM_WORK_LIMIT - 1;
    assert_resource(validate_sko_forall_with_authority_and_progress(
        &fixture.terms,
        ProofId(0),
        &[fixture.equality],
        0,
        &[fixture.witness],
        SkolemWitnessAuthority::TermStoreRegistry,
        &mut work,
        &mut |_, _| true,
    ));
    assert_eq!(work, SKOLEM_TERM_WORK_LIMIT);
    assert_resource(validate_sko_forall_with_authority_and_progress(
        &fixture.terms,
        ProofId(1),
        &[fixture.equality],
        0,
        &[fixture.witness],
        SkolemWitnessAuthority::TermStoreRegistry,
        &mut work,
        &mut |_, _| true,
    ));
    assert_eq!(work, SKOLEM_TERM_WORK_LIMIT);
}

#[test]
fn pending_queue_is_capped_even_in_legacy_always_allow_wrappers() {
    let fixture = Fixture::new(SKOLEM_TERM_WORK_LIMIT + 1);
    assert_resource(validate_forall_inst(
        &fixture.terms,
        ProofId(0),
        &[fixture.implication],
        0,
        &[fixture.witness],
    ));
    assert_resource(validate_sko_forall(
        &fixture.terms,
        ProofId(0),
        &[fixture.equality],
        0,
        &[fixture.witness],
    ));
}

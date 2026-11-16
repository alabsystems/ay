// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

mod boundaries;
mod semantics;

struct Fixture {
    terms: TermStore,
    proof: Proof,
    source: TermId,
    witness: TermId,
}

fn add_binding(
    terms: &mut TermStore,
    proof: &mut Proof,
    binder: &str,
    witness: TermId,
    dependency: Option<TermId>,
) -> TermId {
    let bound = terms.mk_var(binder, Sort::Int);
    let mut body_args = vec![bound];
    let mut instance_args = vec![witness];
    if let Some(dependency) = dependency {
        body_args.push(dependency);
        instance_args.push(dependency);
    }
    let body = terms.mk_app(Symbol::named("whole_p"), body_args, Sort::Bool);
    let source = terms.mk_forall(vec![(binder.to_string(), Sort::Int)], body);
    let instance = terms.mk_app(Symbol::named("whole_p"), instance_args, Sort::Bool);
    let equality = terms.mk_app(Symbol::named("="), [source, instance], Sort::Bool);
    proof.add_rule_step(AletheRule::Skolem, vec![equality], vec![], vec![witness]);
    source
}

impl Fixture {
    fn new() -> Self {
        let mut terms = TermStore::new();
        let mut proof = Proof::new();
        let witness = terms.mk_var("whole_w", Sort::Int);
        terms.mark_skolem_symbol("whole_w");
        let source = add_binding(&mut terms, &mut proof, "whole_x", witness, None);
        Self {
            terms,
            proof,
            source,
            witness,
        }
    }

    fn add_dependent(&mut self, cyclic: bool) {
        let next = self.terms.mk_var("whole_w_next", Sort::Int);
        self.terms.mark_skolem_symbol("whole_w_next");
        if cyclic {
            self.proof = Proof::new();
            self.source = add_binding(
                &mut self.terms,
                &mut self.proof,
                "whole_x_cycle",
                self.witness,
                Some(next),
            );
        }
        let _dependent_source = add_binding(
            &mut self.terms,
            &mut self.proof,
            "whole_y",
            next,
            Some(self.witness),
        );
    }

    fn authenticate(
        &self,
        roots: &[TermId],
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<Vec<String>, ProofCheckError> {
        authenticate_bundle_skolems_with_progress(
            &self.proof,
            &self.terms,
            roots,
            &HashMap::default(),
            progress,
        )
    }

    fn replace_entries(&mut self, entries: Vec<(TermData, Sort)>) {
        let (true_term, false_term) = self.terms.boolean_constant_ids();
        self.terms =
            TermStore::from_entries(entries, true_term, false_term, self.terms.var_counter());
    }
}

fn assert_resource<T>(result: Result<T, ProofCheckError>) {
    assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
}

fn assert_invalid<T>(result: Result<T, ProofCheckError>, expected: &str) {
    assert!(
        matches!(result, Err(ProofCheckError::InvalidBooleanRule { ref reason, .. }) if reason.contains(expected))
    );
}

#[test]
fn live_and_offline_wrappers_preserve_the_same_valid_bindings() {
    let mut fixture = Fixture::new();
    fixture.add_dependent(false);
    validate_sko_forall_uniqueness(&fixture.proof, &fixture.terms).expect("legacy live control");
    validate_sko_forall_uniqueness_with_progress(&fixture.proof, &fixture.terms, &mut |_, _| true)
        .expect("metered live control");
    let expected =
        authenticate_bundle_skolems(&fixture.proof, &fixture.terms, &[], &HashMap::default())
            .expect("legacy offline control");
    assert_eq!(
        fixture
            .authenticate(&[], &mut |_, _| true)
            .expect("metered offline control"),
        expected
    );
    assert_eq!(expected, ["whole_w", "whole_w_next"]);
    fixture.replace_entries(fixture.terms.entries_snapshot());
    assert!(!fixture.terms.is_skolem_symbol("whole_w"));
    assert_eq!(
        fixture
            .authenticate(&[], &mut |_, _| true)
            .expect("proof content, not live ledger"),
        expected
    );
    assert!(
        !fixture.terms.is_skolem_symbol("whole_w"),
        "authentication itself never restores authority"
    );
    assert_invalid(
        validate_sko_forall_uniqueness_with_progress(
            &fixture.proof,
            &fixture.terms,
            &mut |_, _| true,
        ),
        "not registered",
    );
}

#[test]
fn cancellation_at_every_callback_never_authenticates_a_prefix() {
    let mut fixture = Fixture::new();
    fixture.add_dependent(false);
    for live in [false, true] {
        let validate = |progress: &mut dyn FnMut(usize, usize) -> bool| {
            if live {
                validate_sko_forall_uniqueness_with_progress(
                    &fixture.proof,
                    &fixture.terms,
                    progress,
                )
            } else {
                fixture.authenticate(&[], progress).map(|_| ())
            }
        };
        let mut trace = Vec::new();
        validate(&mut |work, bytes| {
            trace.push((work, bytes));
            true
        })
        .expect("valid trace");
        assert_eq!(trace.first(), Some(&(0, 0)));
        assert_eq!(trace.last(), Some(&(0, 0)));
        for stop in 1..=trace.len() {
            let mut calls = 0usize;
            assert_resource(validate(&mut |_, _| {
                calls += 1;
                calls < stop
            }));
            assert_eq!(
                calls, stop,
                "refusal must propagate without another callback"
            );
        }
    }
}

#[test]
fn work_and_bytes_are_shared_across_all_authentication_phases() {
    let mut fixture = Fixture::new();
    fixture.add_dependent(false);
    let mut totals = (0usize, 0usize);
    fixture
        .authenticate(&[], &mut |work, bytes| {
            totals.0 += work;
            totals.1 += bytes;
            true
        })
        .expect("valid totals");
    for budget in [
        (0, usize::MAX),
        (usize::MAX, 0),
        (totals.0 - 1, usize::MAX),
        (usize::MAX, totals.1 - 1),
    ] {
        let mut remaining = budget;
        assert_resource(fixture.authenticate(&[], &mut |work, bytes| {
            if work > remaining.0 || bytes > remaining.1 {
                return false;
            }
            remaining.0 -= work;
            remaining.1 -= bytes;
            true
        }));
    }
}

#[test]
fn empty_proof_still_observes_entry_and_final_cancellation() {
    let terms = TermStore::new();
    let proof = Proof::new();
    let mut calls = 0usize;
    assert_resource(authenticate_bundle_skolems_with_progress(
        &proof,
        &terms,
        &[],
        &HashMap::default(),
        &mut |_, _| {
            calls += 1;
            calls < 3
        },
    ));
    assert_eq!(calls, 3);
    assert_resource(validate_sko_forall_uniqueness_with_progress(
        &proof,
        &terms,
        &mut |_, _| false,
    ));
}

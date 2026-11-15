// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Raw metadata and unchanged caller-envelope controls for qnt_join.

use super::*;
use ay_core::{AletheRule, ProofStep};

struct Fixture {
    terms: TermStore,
    equality: TermId,
    nested: TermId,
    inner: TermId,
    joined: TermId,
    body: TermId,
}

impl Fixture {
    fn new(width: usize, suffix: &str) -> Self {
        let mut terms = TermStore::new();
        let body = terms.mk_var("join_body", Sort::Bool);
        let outer = vec![(format!("outer{suffix}"), Sort::Int)];
        let inner_names: Vec<_> = (0..width)
            .map(|index| (format!("inner{index}{suffix}"), Sort::Int))
            .collect();
        let inner = terms.mk_exists(inner_names.clone(), body);
        let nested = terms.mk_exists(outer.clone(), inner);
        let mut joined_names = outer;
        joined_names.extend(inner_names);
        let joined = terms.mk_exists(joined_names, body);
        let equality = terms.mk_app(Symbol::named("="), [nested, joined], Sort::Bool);
        Self {
            terms,
            equality,
            nested,
            inner,
            joined,
            body,
        }
    }

    fn replace(&mut self, mutate: impl FnOnce(&mut [(TermData, Sort)])) {
        let mut entries = self.terms.entries_snapshot();
        mutate(&mut entries);
        let (t, f) = self.terms.boolean_constant_ids();
        self.terms = TermStore::from_entries(entries, t, f, self.terms.var_counter());
    }

    fn checked(
        &self,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<(), ProofCheckError> {
        validate_qnt_join_with_progress(&self.terms, ProofId(0), &[self.equality], 0, &[], progress)
    }
}

fn resource(result: Result<(), ProofCheckError>) {
    assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
}

#[test]
fn healthy_metadata_matches_compatibility_and_original_progress() {
    let mut fixture = Fixture::new(2, "");
    validate_qnt_join(&fixture.terms, ProofId(0), &[fixture.equality], 0, &[])
        .expect("unchanged healthy exists");
    fixture
        .checked(&mut |_, _| true)
        .expect("same exists with original callback");
    let nodes = [fixture.nested, fixture.inner, fixture.joined];
    fixture.replace(|entries| {
        for term in nodes {
            let TermData::Exists(binders, body, triggers) = entries[term.index()].0.clone() else {
                panic!("genuine fixture");
            };
            entries[term.index()].0 = TermData::Forall(binders, body, triggers);
        }
    });
    fixture
        .checked(&mut |_, _| true)
        .expect("same healthy forall");
}

#[test]
fn indexed_equality_including_empty_indices_cannot_borrow_named_join() {
    for indices in [vec![], vec![0], vec![7, 4]] {
        let mut fixture = Fixture::new(1, "");
        let eq = fixture.equality;
        fixture.replace(|entries| {
            let TermData::App(_, args) = entries[eq.index()].0.clone() else {
                panic!("equality");
            };
            entries[eq.index()].0 = TermData::App(Symbol::indexed("=", indices), args);
        });
        assert!(fixture.checked(&mut |_, _| true).is_err());
    }
}

#[test]
fn foreign_named_operator_does_not_acquire_equality_semantics() {
    let mut fixture = Fixture::new(1, "");
    let eq = fixture.equality;
    fixture.replace(|entries| {
        let TermData::App(_, args) = entries[eq.index()].0.clone() else {
            panic!("equality");
        };
        entries[eq.index()].0 = TermData::App(Symbol::named("foreign_join"), args);
    });
    assert!(fixture.checked(&mut |_, _| true).is_err());
}

#[test]
fn equality_result_metadata_must_be_boolean() {
    for sort in [Sort::Int, Sort::bitvec(1)] {
        let mut fixture = Fixture::new(1, "");
        let eq = fixture.equality;
        fixture.replace(|entries| entries[eq.index()].1 = sort);
        assert!(fixture.checked(&mut |_, _| true).is_err());
    }
}

#[test]
fn all_three_quantifier_result_sorts_are_checked() {
    for which in 0..3 {
        let mut fixture = Fixture::new(1, "");
        let term = [fixture.nested, fixture.inner, fixture.joined][which];
        fixture.replace(|entries| entries[term.index()].1 = Sort::Int);
        assert!(fixture.checked(&mut |_, _| true).is_err());
    }
}

#[test]
fn identical_shared_body_still_requires_boolean_metadata() {
    let mut fixture = Fixture::new(1, "");
    let body = fixture.body;
    fixture.replace(|entries| entries[body.index()].1 = Sort::Int);
    assert!(fixture.checked(&mut |_, _| true).is_err());
}

#[test]
fn missing_equality_quantifier_and_body_ids_refuse_without_dereference() {
    let fixture = Fixture::new(1, "");
    assert!(validate_qnt_join(&fixture.terms, ProofId(0), &[TermId(u32::MAX)], 0, &[]).is_err());
    for which in 0..3 {
        let mut fixture = Fixture::new(1, "");
        let eq = fixture.equality;
        let nested = fixture.nested;
        let inner = fixture.inner;
        let joined = fixture.joined;
        fixture.replace(|entries| match which {
            0 => {
                let TermData::App(_, args) = &mut entries[eq.index()].0 else {
                    panic!("equality");
                };
                args[0] = TermId(u32::MAX);
            }
            1 => {
                let TermData::Exists(_, body, _) = &mut entries[nested.index()].0 else {
                    panic!("nested");
                };
                *body = TermId(u32::MAX);
            }
            _ => {
                for term in [inner, joined] {
                    let TermData::Exists(_, body, _) = &mut entries[term.index()].0 else {
                        panic!("body");
                    };
                    *body = TermId(u32::MAX);
                }
            }
        });
        assert!(fixture.checked(&mut |_, _| true).is_err());
    }
}

#[test]
fn first_middle_and_final_callback_refusal_is_terminal_for_the_check() {
    let fixture = Fixture::new(3, "");
    let mut trace = Vec::new();
    fixture
        .checked(&mut |work, bytes| {
            trace.push((work, bytes));
            true
        })
        .expect("funded original callback");
    assert_eq!(trace.last(), Some(&(0, 0)));
    for stop in [1, trace.len() / 2, trace.len()] {
        let mut calls = 0;
        resource(fixture.checked(&mut |_, _| {
            calls += 1;
            calls < stop
        }));
        assert_eq!(calls, stop, "no callback or success after refusal");
    }
}

#[test]
fn table_scratch_is_prepaid_before_first_borrowed_name_insertion() {
    let fixture = Fixture::new(3, "");
    let mut reservations = 0;
    resource(fixture.checked(&mut |_, bytes| {
        if bytes > 0 {
            reservations += 1;
            false
        } else {
            true
        }
    }));
    assert_eq!(
        reservations, 1,
        "first scratch reservation refusal propagates"
    );
    fixture
        .checked(&mut |_, _| true)
        .expect("explicit separate healthy allowance");
}

#[test]
fn borrowed_long_names_debit_actual_hash_and_comparison_bytes() {
    let measure = |fixture: &Fixture| {
        let mut work = 0usize;
        fixture
            .checked(&mut |debit, _| {
                work += debit;
                true
            })
            .expect("bounded walk");
        work
    };
    let short = measure(&Fixture::new(2, ""));
    let suffix = "z".repeat(8192);
    let long = measure(&Fixture::new(2, &suffix));
    assert!(
        long >= short + suffix.len() * 3,
        "names are not constant-price metadata"
    );
}

#[test]
fn repeated_checks_share_the_callers_remaining_allowance_without_refund() {
    let fixture = Fixture::new(3, "");
    let mut cost = 0usize;
    fixture
        .checked(&mut |work, _| {
            cost += work;
            true
        })
        .expect("measure");
    let mut remaining = cost;
    let mut stopped = false;
    {
        let mut original = |work: usize, _bytes: usize| {
            if stopped || work > remaining {
                stopped = true;
                return false;
            }
            remaining -= work;
            true
        };
        fixture
            .checked(&mut original)
            .expect("one exact original allowance");
        resource(fixture.checked(&mut original));
        resource(fixture.checked(&mut original));
    }
    assert_eq!(remaining, 0);
    assert!(stopped);
}

#[test]
fn legacy_no_callback_wrapper_still_enforces_existing_local_visit_ceiling() {
    let fixture = Fixture::new(super::super::SKOLEM_TERM_WORK_LIMIT, "");
    resource(validate_qnt_join(
        &fixture.terms,
        ProofId(0),
        &[fixture.equality],
        0,
        &[],
    ));
}

#[test]
fn strict_dispatch_never_appends_a_clause_after_original_owner_refusal() {
    let fixture = Fixture::new(1, "");
    let step = ProofStep::Step {
        rule: AletheRule::QntJoin,
        clause: vec![fixture.equality],
        premises: vec![],
        args: vec![],
    };
    let mut derived = Vec::new();
    resource(crate::checker::validate_step_with_datatypes_and_progress(
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
    .expect("genuine separate healthy dispatch");
    assert_eq!(derived, vec![Some(vec![fixture.equality])]);
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Pure declaration/term data controls, not substitutes for runtime model gates.

use super::*;
use ay_core::{DatatypeConstructor, DatatypeSort};

fn app(terms: &mut TermStore, name: &str, args: &[TermId], sort: Sort) -> TermId {
    terms.mk_app(Symbol::Named(name.into()), args, sort)
}

fn owner(name: &str) -> Sort {
    Sort::Datatype(DatatypeSort::new(
        name,
        vec![
            DatatypeConstructor::new(
                "C",
                vec![
                    DatatypeField::new("p", Sort::Bool),
                    DatatypeField::new("q", Sort::Bool),
                    DatatypeField::new("data", Sort::array(Sort::bitvec(64), Sort::bitvec(8))),
                ],
            ),
            DatatypeConstructor::unit("N"),
        ],
    ))
}

struct Fixture {
    terms: TermStore,
    owner: Sort,
    y: TermId,
    z: TermId,
    fields: [TermId; 3],
    tester: TermId,
    rebuilt: TermId,
    inner: TermId,
    eta: TermId,
}

impl Fixture {
    fn new() -> Self {
        let mut terms = TermStore::new();
        let owner = owner("D");
        let y = terms.mk_var("y", owner.clone());
        let z = terms.mk_var("z", owner.clone());
        let p = app(&mut terms, "p", &[y], Sort::Bool);
        let q = app(&mut terms, "q", &[y], Sort::Bool);
        let data = app(
            &mut terms,
            "data",
            &[y],
            Sort::array(Sort::bitvec(64), Sort::bitvec(8)),
        );
        let fields = [p, q, data];
        let tester = app(&mut terms, "is-C", &[y], Sort::Bool);
        let rebuilt = app(&mut terms, "C", &fields, owner.clone());
        let inner = app(&mut terms, "=", &[y, rebuilt], Sort::Bool);
        let eta = app(&mut terms, "=", &[tester, inner], Sort::Bool);
        Self {
            terms,
            owner,
            y,
            z,
            fields,
            tester,
            rebuilt,
            inner,
            eta,
        }
    }
    fn accepts(&self, term: TermId) -> bool {
        is_constructor_eta(
            &self.terms,
            term,
            &Embedded,
            &mut Budget::new(4096, &|| false),
        )
    }
    fn with_rebuild(&mut self, head: &str, fields: &[TermId], sort: Sort) -> TermId {
        let rebuilt = app(&mut self.terms, head, fields, sort);
        let inner = app(&mut self.terms, "=", &[self.y, rebuilt], Sort::Bool);
        app(&mut self.terms, "=", &[self.tester, inner], Sort::Bool)
    }
}

#[test]
fn array_field_eta_and_all_equality_orientations_are_positive_proofs() {
    let mut f = Fixture::new();
    assert!(f.accepts(f.eta));
    let reversed = app(&mut f.terms, "=", &[f.inner, f.tester], Sort::Bool);
    assert!(f.accepts(reversed));
    let inner = app(&mut f.terms, "=", &[f.rebuilt, f.y], Sort::Bool);
    let reversed = app(&mut f.terms, "=", &[inner, f.tester], Sort::Bool);
    assert!(f.accepts(reversed));
    assert_eq!(
        crate::dt_axiom::dt_axiom_bool(&f.terms, f.eta, 4000),
        Some(true)
    );
    assert!(crate::is_datatype_tautology(&f.terms, f.eta));
    assert!(
        !f.accepts(f.inner),
        "bare eta is not valid for two constructors"
    );
}

#[test]
fn wrong_scrutinee_constructor_tester_and_complete_field_coverage_decline() {
    let mut f = Fixture::new();
    let inner = app(&mut f.terms, "=", &[f.z, f.rebuilt], Sort::Bool);
    let wrong_y = app(&mut f.terms, "=", &[f.tester, inner], Sort::Bool);
    assert!(!f.accepts(wrong_y));
    let wrong_tester = app(&mut f.terms, "is-N", &[f.y], Sort::Bool);
    let wrong_tester = app(&mut f.terms, "=", &[wrong_tester, f.inner], Sort::Bool);
    assert!(!f.accepts(wrong_tester));
    let n = f.with_rebuild("N", &[], f.owner.clone());
    assert!(!f.accepts(n));
    let fields = f.fields;
    for values in [
        vec![fields[1], fields[0], fields[2]],
        vec![fields[0], fields[0], fields[2]],
        vec![fields[0], fields[1]],
        vec![fields[0], fields[1], fields[2], fields[2]],
    ] {
        let malformed = f.with_rebuild("C", &values, f.owner.clone());
        assert!(!f.accepts(malformed));
    }
    let other = f.with_rebuild("C", &fields, owner("Other"));
    assert!(
        !f.accepts(other),
        "same member surfaces in another datatype do not alias"
    );
    let wrong_argument = app(&mut f.terms, "p", &[f.z], Sort::Bool);
    let wrong_argument = f.with_rebuild(
        "C",
        &[wrong_argument, fields[1], fields[2]],
        f.owner.clone(),
    );
    assert!(!f.accepts(wrong_argument));
}

#[derive(Clone, Copy)]
enum Change {
    Ordinary,
    WrongInput,
    WrongResult,
}
struct Changed<'a> {
    name: &'a str,
    change: Change,
}
static EMBEDDED: Embedded = Embedded;

impl Registry for Changed<'_> {
    fn fields<'a>(
        &'a self,
        owner: &'a Sort,
        constructor: &str,
        budget: &mut Budget<'_>,
    ) -> Option<Fields<'a>> {
        EMBEDDED.fields(owner, constructor, budget)
    }
    fn member<'a>(
        &'a self,
        owner: &'a Sort,
        name: &'a str,
        budget: &mut Budget<'_>,
    ) -> Option<Member<'a>> {
        let mut member = EMBEDDED.member(owner, name, budget)?;
        if name == self.name {
            match self.change {
                Change::Ordinary => member.kind = Kind::Ordinary,
                Change::WrongInput => member.arguments = Arguments::Unary(&Sort::Int),
                Change::WrongResult => member.result = &Sort::Int,
            }
        }
        Some(member)
    }
}

#[test]
fn ordinary_uf_and_ill_typed_member_signatures_cannot_license_a_proof() {
    let mut f = Fixture::new();
    for name in ["C", "is-C", "p"] {
        for change in [Change::Ordinary, Change::WrongInput, Change::WrongResult] {
            let registry = Changed { name, change };
            assert!(!is_constructor_eta(
                &f.terms,
                f.eta,
                &registry,
                &mut Budget::new(4096, &|| false)
            ));
        }
    }
    let wrong_sort = app(&mut f.terms, "p", &[f.y], Sort::Int);
    let fields = f.fields;
    let wrong_sort = f.with_rebuild("C", &[wrong_sort, fields[1], fields[2]], f.owner.clone());
    assert!(!f.accepts(wrong_sort));
}

#[test]
fn stopped_and_exhausted_work_decline_without_changing_terms() {
    let f = Fixture::new();
    let before = f.terms.len();
    let is_stopped = || true;
    let mut stopped = Budget::new(4096, &is_stopped);
    assert!(!is_constructor_eta(
        &f.terms,
        f.eta,
        &Embedded,
        &mut stopped
    ));
    let running = || false;
    let mut exhausted = Budget::new(1, &running);
    assert!(!is_constructor_eta(
        &f.terms,
        f.eta,
        &Embedded,
        &mut exhausted
    ));
    assert!(exhausted.remaining <= 1);
    assert_eq!(f.terms.len(), before);
}

#[test]
fn duplicate_declared_field_names_do_not_form_a_complete_characterization() {
    let mut terms = TermStore::new();
    let owner = Sort::Datatype(DatatypeSort::new(
        "Malformed",
        vec![
            DatatypeConstructor::new(
                "C",
                vec![
                    DatatypeField::new("p", Sort::Bool),
                    DatatypeField::new("p", Sort::Bool),
                ],
            ),
            DatatypeConstructor::unit("N"),
        ],
    ));
    let y = terms.mk_var("y", owner.clone());
    let p = app(&mut terms, "p", &[y], Sort::Bool);
    let rebuilt = app(&mut terms, "C", &[p, p], owner);
    let inner = app(&mut terms, "=", &[y, rebuilt], Sort::Bool);
    let tester = app(&mut terms, "is-C", &[y], Sort::Bool);
    let eta = app(&mut terms, "=", &[tester, inner], Sort::Bool);
    assert!(!is_constructor_eta(
        &terms,
        eta,
        &Embedded,
        &mut Budget::new(4096, &|| false)
    ));
}

#[test]
fn an_interrupt_partway_through_metadata_never_resets_the_work_window() {
    use std::cell::Cell;
    let f = Fixture::new();
    let calls = Cell::new(0usize);
    let stop = || {
        calls.set(calls.get() + 1);
        calls.get() >= 8
    };
    let mut budget = Budget::new(4096, &stop);
    assert!(!is_constructor_eta(&f.terms, f.eta, &Embedded, &mut budget));
    let left = budget.remaining;
    assert!(left < 4096 && calls.get() >= 8);
    assert!(!is_constructor_eta(&f.terms, f.eta, &Embedded, &mut budget));
    assert_eq!(budget.remaining, left);
}

#[test]
fn a_refused_first_orientation_or_single_stop_cannot_be_retried_with_fresh_work() {
    use std::cell::Cell;
    let f = Fixture::new();
    let running = || false;
    let mut budget = Budget::new(2, &running);
    // The unequal-cost orientation starts at the inner equality. Even its
    // tiny head admission exhausts this window before the correct direction.
    assert!(oriented(&f.terms, f.inner, f.tester, &Embedded, &mut budget).is_none());
    assert!(budget.refused);
    assert!(oriented(&f.terms, f.tester, f.inner, &Embedded, &mut budget).is_none());
    assert_eq!(budget.remaining, 0);
    let stopped_once = Cell::new(false);
    let callback = || {
        if stopped_once.get() {
            false
        } else {
            stopped_once.set(true);
            true
        }
    };
    let mut budget = Budget::new(4096, &callback);
    assert!(!is_constructor_eta(&f.terms, f.eta, &Embedded, &mut budget));
    assert!(budget.refused);
    assert!(!is_constructor_eta(&f.terms, f.eta, &Embedded, &mut budget));
    assert_eq!(
        budget.remaining, 4096,
        "a stop never replenishes or spends another window"
    );
}

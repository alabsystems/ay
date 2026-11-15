// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The engine asks one resource owner when to stop (design §3.9 R1).

use std::sync::atomic::AtomicBool;
use std::sync::Arc;

use ay_cdclt::{Engine, EngineConfig, Guard, Verdict};
use ay_core::resource::ResourceGuard;
use ay_core::{Sort, TermStore};
use num_bigint::BigInt;
use num_rational::BigRational;

fn box_problem(terms: &mut TermStore) -> Vec<ay_core::TermId> {
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let zero = terms.mk_rational(BigRational::from_integer(BigInt::from(0)));
    let one = terms.mk_rational(BigRational::from_integer(BigInt::from(1)));
    let eq = terms.mk_eq(x, y);
    vec![
        terms.mk_not(eq),
        terms.mk_ge(x, zero),
        terms.mk_le(x, one),
        terms.mk_ge(y, zero),
        terms.mk_le(y, one),
    ]
}

/// A raised cancel flag stops the search before it answers, and the answer
/// says why.
#[test]
fn a_raised_cancel_flag_stops_the_check() {
    let mut terms = TermStore::new();
    let asserts = box_problem(&mut terms);
    let mut engine = Engine::new(EngineConfig::default());
    for a in asserts {
        engine.assert(a);
    }
    let mut resource = ResourceGuard::new();
    resource.set_cancel(Some(Arc::new(AtomicBool::new(true))));
    let outcome = engine.check(&mut terms, &[], &Guard::new().with_resource(resource));
    assert_eq!(outcome.verdict, Verdict::Unknown);
    assert_eq!(outcome.reason.as_deref(), Some("interrupted"));
}

/// An open guard changes nothing: the same problem is decided.
#[test]
fn an_open_guard_decides_as_before() {
    let mut terms = TermStore::new();
    let asserts = box_problem(&mut terms);
    let mut engine = Engine::new(EngineConfig::default());
    for a in asserts {
        engine.assert(a);
    }
    let guard = Guard::new().with_resource(ResourceGuard::new());
    assert_eq!(engine.check(&mut terms, &[], &guard).verdict, Verdict::Sat);
}

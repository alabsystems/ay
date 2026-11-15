// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::original_query::FiniteAdmissionGrant;
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc,
};

fn admission(stop: Arc<AtomicBool>) -> CountedAdmission {
    CountedAdmission::new(
        FiniteAdmissionGrant::new(10_000_000, 64 << 20),
        None,
        Arc::new(move || stop.load(Ordering::Relaxed)),
    )
    .unwrap()
}

#[test]
fn inherited_arithmetic_and_opaque_nodes_preserve_identity_and_child_sorts() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let one = terms.mk_int(1.into());
    let wrong = terms.mk_bool(true);
    let name = "opaque".repeat(50);
    terms.register_declared_function(&name);
    let args = vec![x; 129];
    let source = terms.mk_app(Symbol::named(name.clone()), &args, Sort::Int);
    let arithmetic = terms.mk_app(Symbol::named("+"), [x, one], Sort::Int);
    let owner = admission(Arc::new(AtomicBool::new(false)));
    let mut builder = CountedTermBuilder::new(&mut terms, &owner).unwrap();
    let mut replacement = args.clone();
    replacement[0] = one;
    let rebuilt = builder.rebuild_existing(source, &replacement).unwrap();
    assert_ne!(rebuilt, source);
    assert_eq!(
        builder.terms().get(source),
        &TermData::App(Symbol::named(name.clone()), args)
    );
    assert_eq!(
        builder.terms().get(rebuilt),
        &TermData::App(Symbol::named(name), replacement.clone())
    );
    assert_eq!(
        builder.rebuild_existing(source, &replacement).unwrap(),
        rebuilt
    );
    let before = builder.terms().len();
    replacement[0] = wrong;
    assert_eq!(
        builder.rebuild_existing(source, &replacement),
        Err(CountedTermError::InvalidInput)
    );
    assert_eq!(builder.terms().len(), before);
    let result = builder.rebuild_existing(arithmetic, &[one, one]).unwrap();
    assert_eq!(builder.terms().sort(result), &Sort::Int);
    assert_eq!(
        builder.terms().get(result),
        &TermData::App(Symbol::named("+"), vec![one, one])
    );
    builder.finish().unwrap();
}

#[test]
fn substituted_field_predicate_cannot_keep_a_stale_field_free_mark() {
    let mut terms = TermStore::new();
    let boolean = terms.mk_var("b", Sort::Bool);
    let field = crate::FiniteFieldSort::new(7).unwrap();
    let x = terms.mk_var("x", Sort::FiniteField(field));
    let one = terms.mk_finite_field(1, field);
    let predicate = terms.mk_app(Symbol::named("="), [x, one], Sort::Bool);
    let source = terms.mk_app(Symbol::named("opaque"), [boolean], Sort::Bool);
    assert_eq!(terms.finite_field_presence(source), Some(false));
    let owner = admission(Arc::new(AtomicBool::new(false)));
    let mut builder = CountedTermBuilder::new(&mut terms, &owner).unwrap();
    let rebuilt = builder.rebuild_existing(source, &[predicate]).unwrap();
    assert_eq!(builder.terms().finite_field_presence(rebuilt), Some(true));
    builder.finish().unwrap();
}

#[test]
fn rebuild_refusal_is_sticky_and_precedes_source_growth() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let one = terms.mk_int(1.into());
    let source = terms.mk_app(Symbol::named("+"), [x, one], Sort::Int);
    let stop = Arc::new(AtomicBool::new(false));
    let owner = admission(Arc::clone(&stop));
    let mut builder = CountedTermBuilder::new(&mut terms, &owner).unwrap();
    let before = builder.terms().len();
    stop.store(true, Ordering::Relaxed);
    assert!(builder.rebuild_existing(source, &[one, one]).is_err());
    assert_eq!(builder.terms().len(), before);
    stop.store(false, Ordering::Relaxed);
    assert!(builder.rebuild_existing(source, &[one, one]).is_err());
    drop(builder);
    let fresh = admission(Arc::new(AtomicBool::new(false)));
    let mut builder = CountedTermBuilder::new(&mut terms, &fresh).unwrap();
    assert!(builder.rebuild_existing(source, &[one, one]).is_ok());
    builder.finish().unwrap();
}

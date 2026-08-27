// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Wire-lowering tests for `AletheRule::FreshDefEq`.
//!
//! The step is certified INTERNALLY (`ay-proof`'s `FreshDefRegistry` re-derives
//! freshness from the problem's own symbols) and is deliberately UNCHECKABLE
//! externally: Alethe has no notion of a solver introducing a symbol and
//! defining it. So it renders as an honest `hole` — byte-for-byte what the
//! premiseless `trust` it replaces already rendered as, which is what makes the
//! promotion lane a no-op on the emitted document.
//!
//! Three near-misses these tests exist to prevent:
//!
//! 1. `hole :args (boolarg_7)`. The pinned carcara build rejects `:args` on
//!    `hole` outright, which takes the whole document from `holey` to
//!    `invalid` — strictly worse than the step it replaced. The default
//!    generic-step renderer WOULD print the args, so the dedicated arm is
//!    load-bearing rather than cosmetic.
//! 2. `refl`. It is `=`-shaped and would render, and it would be a FALSE
//!    claim: `(= p body)` is not an instance of `t = t`.
//! 3. `eq_congruent` / `eq_transitive`. Also `=`-shaped, also false: there is
//!    no premise and no congruence here, only a definition.

use super::*;
use ay_core::{AletheRule, Sort, TermStore};
use num_bigint::BigInt;

/// `p := (and g (<= x y))`, the shape `purify_bool_args` actually builds.
fn definitional_equality(terms: &mut TermStore) -> (ProofStep, TermId) {
    let p = terms.mk_var("boolarg_7", Sort::Bool);
    let g = terms.mk_var("g", Sort::Bool);
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let le = terms.mk_le(x, y);
    let body = terms.mk_and(vec![g, le]);
    let atom = terms.mk_eq(p, body);
    (
        ProofStep::Step {
            rule: AletheRule::FreshDefEq,
            clause: vec![atom],
            premises: Vec::new(),
            args: vec![p],
        },
        p,
    )
}

#[test]
fn a_fresh_def_eq_lowers_to_an_honest_hole_with_no_args() {
    let mut terms = TermStore::new();
    let (step, _) = definitional_equality(&mut terms);

    let rendered = AlethePrinter::new(&terms)
        .format_step(&step, ProofId(7))
        .expect("a well-formed fresh-definition equality must render, not error");

    assert!(rendered.starts_with("(step t7 (cl (= "), "{rendered}");
    assert!(rendered.ends_with(":rule hole)"), "{rendered}");
    assert!(!rendered.contains(":args"), "{rendered}");
    assert!(!rendered.contains(":premises"), "{rendered}");
    assert!(!rendered.contains("refl"), "{rendered}");
    assert!(!rendered.contains("eq_congruent"), "{rendered}");
    assert!(!rendered.contains("fresh_def_eq"), "{rendered}");
}

#[test]
fn the_promotion_is_byte_identical_to_the_trust_step_it_replaces() {
    // The whole lane is an INTERNAL certification change. If the emitted
    // document differed, the promotion could regress an external verdict; this
    // pins that it cannot.
    let mut terms = TermStore::new();
    let (promoted, _) = definitional_equality(&mut terms);
    let ProofStep::Step { clause, .. } = &promoted else {
        panic!("built a Step");
    };
    let demoted = ProofStep::Step {
        rule: AletheRule::Trust,
        clause: clause.clone(),
        premises: Vec::new(),
        args: Vec::new(),
    };
    let printer = AlethePrinter::new(&terms);
    let promoted_text = printer
        .format_step(&promoted, ProofId(3))
        .expect("promoted step renders");
    let demoted_text = printer
        .format_step(&demoted, ProofId(3))
        .expect("demoted step renders");
    assert_eq!(promoted_text, demoted_text);
}

#[test]
fn an_array_sorted_definition_lowers_the_same_way() {
    // The equality form is not restricted to the arithmetic sorts `<=` admits,
    // so the printer must handle any sort the definiens can have.
    let mut terms = TermStore::new();
    let array = Sort::array(Sort::Int, Sort::Int);
    let a = terms.mk_var("a", array.clone());
    let d = terms.mk_var("__ay_def!9", array);
    let i = terms.mk_var("i", Sort::Int);
    let v = terms.mk_var("v", Sort::Int);
    let store = terms.mk_store(a, i, v);
    let atom = terms.mk_eq(d, store);
    let step = ProofStep::Step {
        rule: AletheRule::FreshDefEq,
        clause: vec![atom],
        premises: Vec::new(),
        args: vec![d],
    };
    let rendered = AlethePrinter::new(&terms)
        .format_step(&step, ProofId(0))
        .expect("an array-sorted definition renders");
    assert!(rendered.ends_with(":rule hole)"), "{rendered}");
    assert!(!rendered.contains(":args"), "{rendered}");
}

#[test]
fn a_malformed_fresh_def_eq_declines_instead_of_reaching_the_wire() {
    // The printer emits this step's CLAUSE, so a step whose `:args` name a
    // symbol that is on NEITHER side of the `=` must not be printed as though
    // it were a definition. `(= x y)` is an ordinary equation, falsified at
    // `x = 1, y = 0`.
    let mut terms = TermStore::new();
    let d = terms.mk_var("__ay_def!1", Sort::Int);
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let atom = terms.mk_eq(x, y);
    let step = ProofStep::Step {
        rule: AletheRule::FreshDefEq,
        clause: vec![atom],
        premises: Vec::new(),
        args: vec![d],
    };
    let error = AlethePrinter::new(&terms)
        .format_step(&step, ProofId(0))
        .expect_err("a malformed definition must decline");
    assert!(
        matches!(error, AlethePrintError::InvalidSurfaceStep { .. }),
        "{error:?}"
    );
}

#[test]
fn a_multi_literal_fresh_def_eq_declines() {
    // A wider clause is a disjunction and is not a definition; the fail-closed
    // default must be a decline rather than a silent pass-through to the
    // generic renderer, which would print `:args`.
    let mut terms = TermStore::new();
    let d = terms.mk_var("__ay_def!1", Sort::Int);
    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let first = terms.mk_eq(d, x);
    let second = terms.mk_le(zero, x);
    let step = ProofStep::Step {
        rule: AletheRule::FreshDefEq,
        clause: vec![first, second],
        premises: Vec::new(),
        args: vec![d],
    };
    assert!(AlethePrinter::new(&terms)
        .format_step(&step, ProofId(0))
        .is_err());
}

#[test]
fn a_fresh_def_eq_carrying_premises_declines() {
    // A definition is derived from nothing. A step with premises whose text
    // dropped them would be a silent lie about what the step rests on.
    let mut terms = TermStore::new();
    let (step, p) = definitional_equality(&mut terms);
    let ProofStep::Step { clause, .. } = &step else {
        panic!("built a Step");
    };
    let with_premises = ProofStep::Step {
        rule: AletheRule::FreshDefEq,
        clause: clause.clone(),
        premises: vec![ProofId(0)],
        args: vec![p],
    };
    assert!(AlethePrinter::new(&terms)
        .format_step(&with_premises, ProofId(1))
        .is_err());
}

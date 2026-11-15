// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Parity-shape guard for the deep QE pre-pass (`qe_prepass.rs`).
//!
//! A child of `qe_prepass_tests.rs`, kept in its own file so the parent test
//! module stays under the file-size ratchet; it reuses the parent's fixture
//! helpers.

use super::super::deep_qe;
use super::{ci, contains_quantifier, ivar};
use ay_core::term::{Symbol, TermData};
use ay_core::{Sort, TermId, TermStore};
use std::collections::HashSet;

/// Does `t` contain an integer divisibility construct (`mod` / `div` /
/// `divisible`) anywhere in its DAG?
fn contains_divisibility(terms: &TermStore, t: TermId) -> bool {
    let mut seen: HashSet<TermId> = HashSet::new();
    let mut stack = vec![t];
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        match terms.get(t) {
            TermData::App(Symbol::Named(name), args) => {
                if name == "mod" || name == "div" || name == "divisible" {
                    return true;
                }
                stack.extend(args.iter().copied());
            }
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, a, b) => stack.extend([*c, *a, *b]),
            _ => {}
        }
    }
    false
}

/// `deep_qe` fully eliminates the parity shape of
/// `LIA/20190429-UltimateAutomizerSvcomp2019/jain_2…`: coefficient-2
/// existentials (`∃v. t = 2v + 1`) asserted positively, and again under a
/// negated conjunction.
///
/// Cooper's rewrite of each binder mints constant-divisor divisibility atoms.
/// The #quantprod-a adoption screen refuses a divisibility-minting rewrite only
/// when bounded finite-domain expansion can ground the original assertion
/// exactly; it cannot ground these unbounded existentials, so the screen must
/// not refuse this adoption and no quantifier may remain.
///
/// An elimination regression here is invisible at verdict level: `qe_route`
/// withholds the lane's answer either way (see `executor/qe_route.rs` module
/// docs), so a unit test is what notices.
#[test]
fn eliminates_the_sq_arith_parity_shape() {
    // x = 2·v₀ + 1 ∧ y = 2·v₁ + 1, denied at the primed copies, over
    // x′ = x + 2·n₀ ∧ y′ = y + 2·n₁. Cooper turns each `∃v. t = 2v + 1` into a
    // constant-divisor divisibility atom, so nothing may remain quantified.
    let mut terms = TermStore::new();
    let two = ci(&mut terms, 2);
    let one = ci(&mut terms, 1);

    let odd = |terms: &mut TermStore, subject: TermId, binder: &str| {
        let v = ivar(terms, binder);
        let twice = terms.mk_mul(vec![two, v]);
        let shifted = terms.mk_add(vec![twice, one]);
        let eq = terms.mk_eq(subject, shifted);
        terms.mk_exists(vec![(binder.to_string(), Sort::Int)], eq)
    };

    let x = ivar(&mut terms, "x");
    let y = ivar(&mut terms, "y");
    let xp = ivar(&mut terms, "x_primed");
    let yp = ivar(&mut terms, "y_primed");
    let n0 = ivar(&mut terms, "n0");
    let n1 = ivar(&mut terms, "n1");

    let step_x = {
        let d = terms.mk_mul(vec![two, n0]);
        let rhs = terms.mk_add(vec![d, x]);
        terms.mk_eq(xp, rhs)
    };
    let step_y = {
        let d = terms.mk_mul(vec![two, n1]);
        let rhs = terms.mk_add(vec![d, y]);
        terms.mk_eq(yp, rhs)
    };
    let step = terms.mk_and(vec![step_x, step_y]);

    let pre_x = odd(&mut terms, x, "v0");
    let pre_y = odd(&mut terms, y, "v1");
    let pre = terms.mk_and(vec![pre_x, pre_y]);

    let post_x = odd(&mut terms, xp, "v2");
    let post_y = odd(&mut terms, yp, "v3");
    let post = terms.mk_and(vec![post_x, post_y]);
    let denied = terms.mk_not(post);

    let mut goal = vec![step, pre, denied];
    let progressed = deep_qe(&mut terms, &mut goal, None);

    assert!(
        progressed,
        "the pre-pass must adopt a rewrite on this shape"
    );
    let residual: Vec<usize> = goal
        .iter()
        .enumerate()
        .filter(|(_, &a)| contains_quantifier(&terms, a))
        .map(|(i, _)| i)
        .collect();
    assert!(
        residual.is_empty(),
        "Cooper must close every binder of the parity shape; assertions still \
         quantified: {residual:?}"
    );
    assert!(
        goal[1..].iter().all(|&a| contains_divisibility(&terms, a)),
        "each adopted parity rewrite carries a divisibility atom, so this shape \
         exercises the #quantprod-a screen's decline-to-refuse path"
    );
}

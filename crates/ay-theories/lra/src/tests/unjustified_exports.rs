// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #nonlinear-shared-reasons: a model guess never leaves the LRA as a fact,
//! and a term echoed back as a cross-theory reason never makes one justified.
//!
//! The NIA/NRA pin a variable with a bound whose reason is the variable term
//! (`add_gomory_cut(.., reason = var)`). Before this rule the pin left the
//! solver three ways — the interface bridge read its value WITH that reason
//! (`get_value_with_reasons`), the Nelson-Oppen tight-bound scan exported
//! `x = y` citing it, the fixed-term export likewise — and EUF, handing an
//! equality back, put the term on the cross-theory trail, after which every
//! guess on that variable passed `bound_reasons_all_asserted`.

use super::*;
use ay_core::TheorySolver;

fn pin(lra: &mut LraSolver, x: TermId, value: i64) {
    let var = lra.ensure_var_registered(x);
    for is_lower in [true, false] {
        lra.add_gomory_cut(
            &GomoryCut {
                coeffs: vec![(var, BigRational::one())],
                bound: BigRational::from(BigInt::from(value)),
                is_lower,
                reasons: Vec::new(),
                source_term: None,
            },
            x,
        );
    }
}

/// A guessed pin `x = 3` has no exportable reasons; an asserted `y = 3` does,
/// and the tight-bound scan exports nothing that cites the guess.
#[test]
fn a_guessed_pin_is_not_exported() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let y_eq_3 = terms.mk_eq(y, three);
    let mut lra = LraSolver::new(&terms);
    lra.set_combined_theory_mode(true);
    lra.assert_literal(y_eq_3, true);
    let _ = lra.check();
    lra.push();
    pin(&mut lra, x, 3);
    let _ = lra.check();

    let (xv, x_reasons) = lra.get_value_with_reasons(x).expect("x registered");
    assert_eq!(xv, BigRational::from(BigInt::from(3)));
    assert!(
        x_reasons.is_empty(),
        "a guess reports no reasons, so the bridge treats x's value as speculative: {x_reasons:?}"
    );
    let (_, y_reasons) = lra.get_value_with_reasons(y).expect("y registered");
    assert_eq!(y_reasons, vec![TheoryLit::new(y_eq_3, true)]);

    let props = lra.propagate_equalities();
    for eq in &props.equalities {
        assert!(
            eq.reason.iter().all(|lit| lit.term != x),
            "an exported equality cites the guess: {eq:?}"
        );
    }
    assert!(
        lra.stats.unjustified_exports_refused >= 1,
        "the refused pin is counted"
    );
    lra.pop();
}

/// A non-atom term on the cross-theory trail (a reasonless shared equality's
/// placeholder, or a guess's term echoed back by EUF) does not justify a
/// bound that cites it; a Boolean atom on the same trail does.
#[test]
fn an_echoed_term_is_no_premise() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let p = terms.mk_var("p", Sort::Bool);
    let mut lra = LraSolver::new(&terms);
    lra.push();
    pin(&mut lra, x, 1);
    let guess = lra.get_bounds(x).and_then(|(lb, _)| lb).expect("pinned");
    assert!(!lra.bound_reasons_all_asserted(&guess));
    // EUF hands back an equality whose reason is the variable term.
    lra.record_cross_theory_reasons(&[(x, true)]);
    assert!(
        !lra.bound_reasons_all_asserted(&guess),
        "the echoed term must not make the guess justified"
    );
    // A genuine cross-theory atom does justify a bound citing it.
    lra.record_cross_theory_reasons(&[(p, true)]);
    let atom_bound = Bound::new(
        Rational::from(BigInt::from(1)),
        vec![p],
        vec![true],
        Vec::<Rational>::new(),
        false,
    );
    assert!(lra.bound_reasons_all_asserted(&atom_bound));
    lra.pop();
}

fn fix_directly(lra: &mut LraSolver, x: TermId, value: i64, reason: TermId) -> u32 {
    let var = lra.ensure_var_registered(x);
    let bound = || {
        Bound::new(
            Rational::from(BigInt::from(value)),
            vec![reason],
            vec![true],
            Vec::<Rational>::new(),
            false,
        )
    };
    lra.vars[var as usize].lower = Some(bound());
    lra.vars[var as usize].upper = Some(bound());
    lra.register_fixed_term_var(var);
    var
}

/// The fixed-term export for `x` and `y` both pinned to 0, where `y`'s pin is
/// asserted (`y_is_0`) and `x`'s pin is `x_reason`. Returns the requests that
/// relate `x` and `y`.
fn fixed_pair_export(
    x_reason: impl Fn(&mut TermStore, TermId) -> TermId,
) -> Vec<ModelEqualityRequest> {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let y_is_0 = terms.mk_var("y_is_0", Sort::Bool);
    let x_reason = x_reason(&mut terms, x);
    let mut lra = LraSolver::new(&terms);
    lra.set_combined_theory_mode(true);
    lra.record_cross_theory_reasons(&[(y_is_0, true)]);
    if !x_reason.is_sentinel() && *terms.sort(x_reason) == Sort::Bool {
        lra.record_cross_theory_reasons(&[(x_reason, true)]);
    }
    let y_var = fix_directly(&mut lra, y, 0, y_is_0);
    let x_var = fix_directly(&mut lra, x, 0, x_reason);
    assert!(
        lra.pending_fixed_term_equalities.contains(&(x_var, y_var)),
        "the same-value fixings are queued as a candidate pair"
    );
    lra.take_pending_fixed_term_model_equalities()
        .into_iter()
        .filter(|req| [req.lhs, req.rhs].contains(&x) && [req.lhs, req.rhs].contains(&y))
        .collect()
}

/// `x = y` follows from the two fixings together. When `x` is pinned by a
/// guess (its reason is the variable term, no atom), `y`'s reasons alone do
/// not entail it, so the pair is not exported. Exporting it let a UF+NIA
/// solve learn `d = 0 -> x*d = x*e` from a patch pin on `x*e` and answer
/// `unsat` on a satisfiable input.
#[test]
fn a_fixed_pair_is_not_exported_on_one_sides_reasons() {
    let requests = fixed_pair_export(|_, x| x);
    assert!(
        requests.is_empty(),
        "a guessed side must keep the pair from leaving the solver: {requests:?}"
    );
}

/// The same pair with a sentinel pin on `x` (a hypothesis or a cut) is not
/// exported either.
#[test]
fn a_fixed_pair_is_not_exported_over_a_sentinel_pin() {
    let requests = fixed_pair_export(|_, _| TermId::SENTINEL);
    assert!(
        requests.is_empty(),
        "a sentinel side must keep the pair from leaving the solver: {requests:?}"
    );
}

/// Twin: with `x`'s pin asserted too, the pair is exported and cites both.
#[test]
fn a_fixed_pair_with_both_sides_asserted_is_exported() {
    let requests = fixed_pair_export(|terms, _| terms.mk_var("x_is_0", Sort::Bool));
    assert_eq!(requests.len(), 1, "{requests:?}");
    assert_eq!(
        requests[0].reason.len(),
        2,
        "the export cites both fixings: {:?}",
        requests[0].reason
    );
}

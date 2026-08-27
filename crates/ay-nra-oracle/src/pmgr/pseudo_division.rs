// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Sparse-polynomial pseudo-division checks.

use super::*;

// ---------------------------------------------------------------------------
// 2. Pseudo-division
// ---------------------------------------------------------------------------

/// `lc(q,x)^d * p == Q*q + R`, checked exactly in the manager AND at the real
/// roots of the specialized `q` with z3.
pub(crate) fn check_pm_pseudo_div(z3: &Z3, g: &GenPm, sab: Sabotage) -> Outcome {
    let mut manager = OPolyMgr::new();
    let p = {
        let a = manager.mk(&g.a_terms);
        let b = manager.mk(&g.b_terms);
        manager.mul(&a, &b)
    };
    let q = manager.mk(&g.g_terms);
    if manager.is_zero(&q) || manager.is_zero(&p) {
        return Outcome::Skipped("degenerate operand");
    }
    let Some(division) = manager.pseudo_division(&p, &q, X, true) else {
        return Outcome::Declined("pseudo_division refused");
    };
    let mut remainder = division.rem;
    if sab.on() {
        let one = manager.constant(BigInt::one());
        remainder = manager.add(&remainder, &one);
    }
    let leading = manager.lc(&q, X);
    let case = PseudoDivisionCase {
        p: &p,
        q: &q,
        quotient: &division.quot,
        remainder: &remainder,
        leading: &leading,
        exponent: division.d,
    };
    let mut comparisons = 0;
    if let Err(outcome) = add_matches(
        &mut comparisons,
        check_pseudo_div_identity(&mut manager, &case),
    ) {
        return outcome;
    }
    if let Err(outcome) = add_matches(
        &mut comparisons,
        check_pseudo_div_at_z3_roots(z3, g, &mut manager, &case),
    ) {
        return outcome;
    }
    Outcome::Match(comparisons)
}

struct PseudoDivisionCase<'a> {
    p: &'a OMgrPoly,
    q: &'a OMgrPoly,
    quotient: &'a OMgrPoly,
    remainder: &'a OMgrPoly,
    leading: &'a OMgrPoly,
    exponent: u32,
}

fn check_pseudo_div_identity(manager: &mut OPolyMgr, case: &PseudoDivisionCase<'_>) -> Outcome {
    let leading_power = manager.pow(case.leading, case.exponent);
    let lhs = manager.mul(&leading_power, case.p);
    let quotient_product = manager.mul(case.quotient, case.q);
    let rhs = manager.add(&quotient_product, case.remainder);
    if lhs != rhs {
        return Divergence::outcome(
            "pm-pseudo-division",
            "identity",
            format!("lc(q,x)^{} * p != Q*q + R", case.exponent),
            vec![
                ("p".to_string(), render(manager, case.p)),
                ("q".to_string(), render(manager, case.q)),
                ("Q".to_string(), render(manager, case.quotient)),
                ("R".to_string(), render(manager, case.remainder)),
            ],
        );
    }
    if !manager.is_zero(case.remainder)
        && manager.degree(case.remainder, X) >= manager.degree(case.q, X)
    {
        return Divergence::outcome(
            "pm-pseudo-division",
            "identity",
            format!(
                "remainder degree {} is not below divisor degree {}",
                manager.degree(case.remainder, X),
                manager.degree(case.q, X)
            ),
            vec![
                ("q".to_string(), render(manager, case.q)),
                ("R".to_string(), render(manager, case.remainder)),
            ],
        );
    }
    Outcome::Match(2)
}

fn check_pseudo_div_at_z3_roots(
    z3: &Z3,
    g: &GenPm,
    manager: &mut OPolyMgr,
    case: &PseudoDivisionCase<'_>,
) -> Outcome {
    let (Some(q_bar), Some(p_bar), Some(r_bar), Some(leading_bar)) = (
        manager.specialize(case.q, X, &g.point),
        manager.specialize(case.p, X, &g.point),
        manager.specialize(case.remainder, X, &g.point),
        manager.specialize(case.leading, X, &g.point),
    ) else {
        return Outcome::Skipped("specialization left a variable standing");
    };
    if q_bar.len() < 2 {
        return Outcome::Skipped("specialized divisor has no roots to test at");
    }
    let leading_sign = match leading_bar.as_slice() {
        [] => 0,
        [constant] => isign(constant),
        _ => {
            return Divergence::outcome(
                "pm-pseudo-division",
                "identity",
                "lc(q, x) specialized to a non-constant".to_string(),
                vec![("lc".to_string(), render_dense(&leading_bar))],
            );
        }
    };
    let Some(roots) = z3.roots(&to_rationals(&q_bar)) else {
        return Outcome::Skipped("z3 declined the specialized divisor");
    };
    let power_sign = if case.exponent == 0 {
        1
    } else if leading_sign == 0 {
        0
    } else if leading_sign > 0 || case.exponent.is_multiple_of(2) {
        1
    } else {
        -1
    };
    let mut comparisons = 0;
    for root in roots {
        let (Some(remainder_sign), Some(p_sign)) = (
            z3.eval_sign(&to_rationals(&r_bar), root),
            z3.eval_sign(&to_rationals(&p_bar), root),
        ) else {
            return Outcome::Skipped("z3 declined an evaluation");
        };
        comparisons += 1;
        let expected = power_sign * p_sign;
        if remainder_sign != expected {
            return Divergence::outcome(
                "pm-pseudo-division",
                "z3",
                format!(
                    "at q root: sign(R)={remainder_sign}, sign(lc^{})*sign(p)={expected}",
                    case.exponent
                ),
                vec![
                    ("p".to_string(), render(manager, case.p)),
                    ("q".to_string(), render(manager, case.q)),
                    ("R".to_string(), render(manager, case.remainder)),
                    ("p_bar".to_string(), render_dense(&p_bar)),
                    ("q_bar".to_string(), render_dense(&q_bar)),
                    ("R_bar".to_string(), render_dense(&r_bar)),
                    ("lc_bar".to_string(), render_dense(&leading_bar)),
                ],
            );
        }
    }
    Outcome::Match(comparisons)
}

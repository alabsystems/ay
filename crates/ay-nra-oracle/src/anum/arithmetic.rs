// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact algebraic-number arithmetic checks.

use super::*;

// ===========================================================================
// Check 4 — `anum-arith`
// ===========================================================================

/// Exact `add` / `mul` against `Z3_algebraic_add` / `Z3_algebraic_mul`.
///
/// AY's answer is converted to a z3 AST through [`z3_of`], which finds it by
/// asking z3 for the roots of AY's own defining polynomial and selecting the one
/// inside AY's own interval. That conversion is itself an assertion: a result
/// cell whose interval brackets two roots, or none, is caught here.
pub(crate) fn check_arith(z3: &Z3, g: &GenAn, sab: Sabotage) -> Outcome {
    let Some((a, va, _)) = build(z3, &g.p, 0) else {
        return Outcome::Skipped("no root / z3 declined");
    };
    let Some((b, vb, _)) = build(z3, &g.q, 1) else {
        return Outcome::Skipped("no root / z3 declined");
    };
    let mut comparisons = 0;
    for (op, ay, reference) in [
        (Operation::Add, a.add(&b), z3.add(va, vb)),
        (Operation::Multiply, a.mul(&b), z3.mul(va, vb)),
    ] {
        match check_algebraic_binop(z3, g, sab, &a, &b, op, ay, reference) {
            Outcome::Match(n) => comparisons += n,
            other => return other,
        }
    }
    match check_rational_binops(z3, g, sab, &a, va) {
        Outcome::Match(n) => comparisons += n,
        other => return other,
    }
    match check_negation_identity(z3, g, sab, &a, va) {
        Outcome::Match(n) => comparisons += n,
        other => return other,
    }
    Outcome::Match(comparisons)
}

#[derive(Clone, Copy)]
enum Operation {
    Add,
    Multiply,
}

impl Operation {
    fn label(self) -> &'static str {
        match self {
            Self::Add => "add",
            Self::Multiply => "mul",
        }
    }

    fn is_add(self) -> bool {
        matches!(self, Self::Add)
    }
}

fn check_algebraic_binop(
    z3: &Z3,
    g: &GenAn,
    sab: Sabotage,
    a: &ODyadicAnum,
    b: &ODyadicAnum,
    op: Operation,
    answer: Option<ODyadicAnum>,
    reference: Option<Ast>,
) -> Outcome {
    let label = op.label();
    let Some(reference) = reference else {
        return Outcome::Skipped("z3 errored on algebraic add/mul");
    };
    let diag = anum_binop_diag(a, b, op.is_add());
    let must_succeed = !matches!(diag, OAnumOpDiag::OverCeiling | OAnumOpDiag::Degenerate);
    let Some(mut answer) = answer else {
        if must_succeed && !sab.on() {
            return Divergence::outcome(
                "anum-arith",
                "identity",
                format!("{label} declined although its diagnosis is {diag:?}"),
                inputs(g),
            );
        }
        return Outcome::Declined("add/mul over ceiling");
    };
    if sab.on() {
        let Some(shifted) = answer.add(&ODyadicAnum::rational(BigRational::one())) else {
            return Outcome::Skipped("nothing to sabotage");
        };
        answer = shifted;
    }
    if z3.errored() {
        return Outcome::Skipped("z3 errored");
    }
    let ast = match z3_of_strict(z3, &answer) {
        Ok(value) => value,
        Err(true) => return Outcome::Skipped("z3 declined on AY's answer"),
        Err(false) if sab.on() => {
            return Outcome::Declined("sabotaged answer is not isolating");
        }
        Err(false) => {
            return Divergence::outcome(
                "anum-arith",
                "z3",
                format!("{label}: result does not denote exactly one root"),
                inputs(g),
            );
        }
    };
    let Some(equal) = z3.eq(ast, reference) else {
        return Outcome::Skipped("z3 errored while comparing arithmetic results");
    };
    if !equal {
        let ay_bracket = z3
            .bracket(ast, 40)
            .map_or_else(|| "<?>".to_string(), |(lo, hi)| format!("({lo}, {hi})"));
        let z3_bracket = z3
            .bracket(reference, 40)
            .map_or_else(|| "<?>".to_string(), |(lo, hi)| format!("({lo}, {hi})"));
        return Divergence::outcome(
            "anum-arith",
            "z3",
            format!("{label}: AY {ay_bracket} != z3 {z3_bracket}"),
            inputs(g),
        );
    }
    Outcome::Match(2)
}

fn check_rational_binops(z3: &Z3, g: &GenAn, sab: Sabotage, a: &ODyadicAnum, va: Ast) -> Outcome {
    let rational = ODyadicAnum::rational(g.point.clone());
    let Some(point) = z3.rational(&g.point) else {
        return Outcome::Skipped("z3 rejected rational arithmetic operand");
    };
    let mut comparisons = 0;
    for (op, answer, reference) in [
        (Operation::Add, a.add(&rational), z3.add(va, point)),
        (Operation::Multiply, a.mul(&rational), z3.mul(va, point)),
    ] {
        match check_rational_binop(z3, g, sab, a, &rational, op, answer, reference) {
            Outcome::Match(n) => comparisons += n,
            other => return other,
        }
    }
    Outcome::Match(comparisons)
}

fn check_rational_binop(
    z3: &Z3,
    g: &GenAn,
    sab: Sabotage,
    a: &ODyadicAnum,
    rational: &ODyadicAnum,
    op: Operation,
    answer: Option<ODyadicAnum>,
    reference: Option<Ast>,
) -> Outcome {
    let label = match op {
        Operation::Add => "add-rational",
        Operation::Multiply => "mul-rational",
    };
    let Some(reference) = reference else {
        return Outcome::Skipped("z3 errored on rational algebraic add/mul");
    };
    let diag = anum_binop_diag(a, rational, op.is_add());
    let must_succeed = !matches!(diag, OAnumOpDiag::OverCeiling | OAnumOpDiag::Degenerate);
    let Some(answer) = answer else {
        if must_succeed && !sab.on() {
            return Divergence::outcome(
                "anum-arith",
                "identity",
                format!("{label} declined although its diagnosis is {diag:?}"),
                inputs(g),
            );
        }
        return Outcome::Declined("add/mul rational over ceiling");
    };
    if z3.errored() {
        return Outcome::Skipped("z3 errored");
    }
    let ast = match z3_of_strict(z3, &answer) {
        Ok(value) => value,
        Err(true) => return Outcome::Skipped("z3 declined on AY's answer"),
        Err(false) if sab.on() => {
            return Outcome::Declined("sabotaged answer is not isolating");
        }
        Err(false) => {
            return Divergence::outcome(
                "anum-arith",
                "z3",
                format!("{label}: result does not denote exactly one root"),
                inputs(g),
            );
        }
    };
    let Some(equal) = z3.eq(ast, reference) else {
        return Outcome::Skipped("z3 errored while comparing rational arithmetic results");
    };
    if !sab.on() && !equal {
        return Divergence::outcome(
            "anum-arith",
            "z3",
            format!("{label}: AY and z3 disagree at point {}", g.point),
            inputs(g),
        );
    }
    Outcome::Match(2)
}

fn check_negation_identity(z3: &Z3, g: &GenAn, sab: Sabotage, a: &ODyadicAnum, va: Ast) -> Outcome {
    if sab.on() {
        return Outcome::Match(0);
    }
    let Some(negative) = a.neg() else {
        return Outcome::Declined("neg");
    };
    let Some(ast) = z3_of(z3, &negative) else {
        return Outcome::Declined("z3_of neg");
    };
    let Some(zero) = z3.rational(&BigRational::zero()) else {
        return Outcome::Skipped("z3 rejected zero numeral");
    };
    let Some(zero_sum) = z3.add(ast, va) else {
        return Outcome::Skipped("z3 errored on negation identity");
    };
    let Some(equal) = z3.eq(zero_sum, zero) else {
        return Outcome::Skipped("z3 errored while checking negation identity");
    };
    if !equal {
        return Divergence::outcome(
            "anum-arith",
            "z3",
            "neg: a + (-a) is not zero".to_string(),
            inputs(g),
        );
    }
    let diag = anum_binop_diag(a, &negative, true);
    let Some(sum) = a.add(&negative) else {
        if !matches!(diag, OAnumOpDiag::OverCeiling | OAnumOpDiag::Degenerate) {
            return Divergence::outcome(
                "anum-arith",
                "identity",
                format!("a + (-a) declined although its diagnosis is {diag:?}"),
                inputs(g),
            );
        }
        return Outcome::Declined("add neg over ceiling");
    };
    if sum.cmp_anum(&ODyadicAnum::rational(BigRational::zero())) != Some(Ordering::Equal) {
        return Divergence::outcome(
            "anum-arith",
            "identity",
            "AY's own a + (-a) does not compare equal to 0".to_string(),
            inputs(g),
        );
    }
    Outcome::Match(3)
}

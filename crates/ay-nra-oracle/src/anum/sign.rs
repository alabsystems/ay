// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Polynomial-sign checks at algebraic values.

use super::*;

// ===========================================================================
// Check 3 — `anum-sign-at`
// ===========================================================================

/// Exact sign of a polynomial at an algebraic point, against
/// `Z3_algebraic_eval`.
///
/// # The unwitnessed-witness fix
///
/// The zero answer is produced by a gcd/Sturm certificate, and a certificate
/// only ever asked about polynomials that do NOT vanish is a witness that
/// cannot fail. So this check asks the zero case **on purpose**, twice: `q == p`
/// (must be 0) and `q == p * r` for an unrelated `r` (must also be 0, and now
/// the gcd is a proper factor rather than the whole polynomial). The non-zero
/// probe is asked too, so an "always zero" implementation fails as well.
pub(crate) fn check_sign_at(z3: &Z3, g: &GenAn, sab: Sabotage) -> Outcome {
    // A coarse interval makes the refinement ladder and certificate reachable.
    let Some((a, root, _)) = build_with(z3, &g.p, 0, BracketStyle::Widest) else {
        return Outcome::Skipped("no root / z3 declined");
    };
    let mut comparisons = 0;
    for (label, probe) in sign_probes(g) {
        if probe.is_empty() {
            continue;
        }
        match check_sign_probe(z3, g, sab, &a, root, label, &probe) {
            Outcome::Match(n) => comparisons += n,
            other => return other,
        }
    }
    Outcome::Match(comparisons)
}

fn sign_probes(g: &GenAn) -> [(&'static str, Vec<BigInt>); 4] {
    let derivative =
        g.p.iter()
            .enumerate()
            .skip(1)
            .map(|(degree, coefficient)| coefficient * BigInt::from(degree as i64))
            .collect();
    [
        ("q = p (must be 0)", g.p.clone()),
        ("q = p*probe (must be 0)", pmul(&g.p, &g.probe)),
        ("q = probe", g.probe.clone()),
        ("q = p' (root near alpha)", derivative),
    ]
}

fn check_sign_probe(
    z3: &Z3,
    g: &GenAn,
    sab: Sabotage,
    a: &ODyadicAnum,
    root: Ast,
    label: &str,
    probe: &[BigInt],
) -> Outcome {
    let Some((mut sign, trace)) = a.sign_of_poly_traced(probe) else {
        return Outcome::Declined("sign_of_poly");
    };
    if sab.on() {
        sign = if sign == 0 { 1 } else { -sign };
    }
    let Some(z3_sign) = z3.eval_sign(&rationals(probe), root) else {
        return Outcome::Skipped("z3 declined eval");
    };
    if sign != z3_sign {
        return Divergence::outcome(
            "anum-sign-at",
            "z3",
            format!("{label}: AY sign {sign}, z3 sign {z3_sign}"),
            inputs(g),
        );
    }
    if sab.on() {
        return Outcome::Match(1);
    }
    if trace.steps_a > trace.bound {
        return Divergence::outcome(
            "anum-sign-at",
            "identity",
            format!(
                "{label}: steps {} > derived bound {}",
                trace.steps_a, trace.bound
            ),
            inputs(g),
        );
    }
    if a.is_rational() {
        if trace.steps_a != 0 || trace.equal_by_certificate || trace.sep_bits.is_some() {
            return Divergence::outcome(
                "anum-sign-at",
                "identity",
                format!("{label}: the rational path is closed form but reported work"),
                inputs(g),
            );
        }
        return Outcome::Match(3);
    }
    if sign == 0 && !trace.equal_by_certificate {
        return Divergence::outcome(
            "anum-sign-at",
            "identity",
            format!("{label}: answered 0 without the gcd certificate"),
            inputs(g),
        );
    }
    if sign != 0 && trace.equal_by_certificate {
        return Divergence::outcome(
            "anum-sign-at",
            "identity",
            format!("{label}: certificate claimed a root but the sign is {sign}"),
            inputs(g),
        );
    }
    Outcome::Match(4)
}

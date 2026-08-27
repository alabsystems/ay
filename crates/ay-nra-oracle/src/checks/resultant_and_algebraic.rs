// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Included by the parent module to keep one audited namespace.

/// Resultant: AY's Sylvester determinant vs z3's principal subresultant chain.
///
/// `Z3_polynomial_subresultants` returns the NON-ZERO principal subresultant
/// coefficients in ascending index order (`psc_chain_optimized` in
/// `src/math/polynomial/polynomial.cpp` pushes them descending and reverses,
/// skipping zeros; an empty chain is reported as the single element `0`).
/// Two exact facts follow, and the `probe` subcommand pins both against live
/// z3 before any fuzzing happens:
///
///   1. `psc_0 == Res`, exactly and with sign, provided z3's internal
///      argument order is matched — z3 puts the HIGHER-DEGREE polynomial
///      first, so AY's determinant is taken in that same order. (Probe:
///      `Res(x-1, x^3-2)` is `-1` for AY in the given order but z3 answers
///      `1`, which is `Res(x^3-2, x-1)`.)
///   2. z3 does NOT rescale by the content: `Res(2x^2-4, x-1) = -2` on both
///      sides. So integer inputs compare directly, no normalization needed.
///
/// When `Res == 0` the whole `psc_0` entry is skipped by z3 and the chain
/// starts at index `k = deg gcd(f, g)`. That case is checked structurally:
/// AY's gcd must be non-constant, and z3's chain can hold at most
/// `min(deg f, deg g) - k` entries — an over-large AY gcd degree shows up as a
/// chain that is too long for it.
///
/// Restricted to integer coefficients so no denominator-clearing convention
/// can enter the comparison.
struct ResultantEvidence<'a> {
    p: &'a GenPoly,
    q: &'a GenPoly,
    result: BigRational,
    chain: &'a [Ast],
    first: BigRational,
    gcd: OPoly,
    p_degree: usize,
    q_degree: usize,
}

fn validate_resultant(evidence: ResultantEvidence<'_>) -> Outcome {
    let ResultantEvidence {
        p,
        q,
        result,
        chain,
        first,
        gcd,
        p_degree,
        q_degree,
    } = evidence;
    let gcd_degree = gcd.degree().unwrap_or(0);
    if chain.len() == 1 && first.is_zero() {
        if !result.is_zero() {
            return Divergence::outcome(
                "resultant",
                "z3",
                format!("z3's psc chain is [0] (common factor) but AY's resultant is {result}"),
                inputs2(p, q),
            );
        }
        return Outcome::Match(1);
    }
    if !result.is_zero() {
        if first != result {
            return Divergence::outcome(
                "resultant",
                "z3",
                format!("AY resultant {result}, z3 psc_0 {first}"),
                inputs2(p, q),
            );
        }
        if gcd_degree != 0 {
            return Divergence::outcome(
                "resultant",
                "identity",
                format!(
                    "AY's resultant is non-zero but AY's gcd {} has degree {gcd_degree}",
                    polygen::render(&gcd.coeffs())
                ),
                inputs2(p, q),
            );
        }
        return Outcome::Match(2);
    }
    if gcd_degree == 0 {
        return Divergence::outcome(
            "resultant",
            "identity",
            "AY's resultant is zero but AY's gcd says the inputs are coprime".to_string(),
            inputs2(p, q),
        );
    }
    let bound = p_degree.min(q_degree).saturating_sub(gcd_degree);
    if chain.len() > bound {
        return Divergence::outcome(
            "resultant",
            "z3",
            format!(
                "AY's gcd {} has degree {gcd_degree}, so z3's psc chain may hold at most \
                 {bound} entries, but it holds {}",
                polygen::render(&gcd.coeffs()),
                chain.len()
            ),
            inputs2(p, q),
        );
    }
    Outcome::Match(2)
}

pub(crate) fn check_resultant(z3: &Z3, p: &GenPoly, q: &GenPoly, sab: Sabotage) -> Outcome {
    let integral = |g: &GenPoly| g.coeffs.iter().all(|c| c.denom().is_one());
    if !integral(p) || !integral(q) {
        return Outcome::Skipped("non-integer coefficients");
    }
    let (ap, aq) = (poly_of(p), poly_of(q));
    let (Some(dp), Some(dq)) = (ap.degree(), aq.degree()) else {
        return Outcome::Skipped("zero polynomial");
    };
    if dp < 1 || dq < 1 {
        return Outcome::Skipped("degree < 1");
    }
    // Keep the exact determinant affordable: Gaussian elimination over
    // BigRational on an (dp + dq) x (dp + dq) matrix.
    if dp + dq > 12 {
        return Outcome::Skipped("degree sum too large");
    }
    // Match z3's internal ordering: higher degree first, ties keep the
    // caller's order (`psc_chain_optimized`).
    let (hi, lo) = if dp >= dq { (&ap, &aq) } else { (&aq, &ap) };
    let Some(res) = ay::resultant(hi, lo) else {
        return Outcome::Declined("resultant");
    };
    // Sabotage: an off-by-one resultant. This also flips the zero/non-zero
    // branch when the true resultant is 0, so both arms get exercised.
    let res = if sab.on() {
        res + BigRational::one()
    } else {
        res
    };
    let Some(chain) = z3.subresultants(&p.coeffs, &q.coeffs) else {
        return Outcome::Skipped("z3 declined");
    };
    if chain.is_empty() {
        return Outcome::Skipped("empty subresultant chain");
    }
    let Some(first) = z3.numeral_value(chain[0]) else {
        // The leading psc still mentions x; nothing to compare against a
        // scalar resultant.
        return Outcome::Skipped("non-numeral psc");
    };
    let g = ap.gcd(&aq);
    validate_resultant(ResultantEvidence {
        p,
        q,
        result: res,
        chain: &chain,
        first,
        gcd: g,
        p_degree: dp,
        q_degree: dq,
    })
}

/// Largest defining-polynomial degree the exact algebraic ARITHMETIC checks
/// will accept.
///
/// AY computes a cross-point sum or product through a resultant: it evaluates
/// the Sylvester determinant at `deg + 1` sample points and Lagrange-
/// interpolates, then isolates the roots of the result, whose degree is the
/// PRODUCT of the two operand degrees. Two degree-5 operands therefore mean
/// exact Sturm work on a degree-25 polynomial over `BigRational` — one such
/// case measured 47.5 seconds here, buying a single comparison for the price
/// of forty thousand.
///
/// The cap is a throughput decision, not a soundness one: the sum of two
/// degree-3 algebraic numbers exercises exactly the same code path as the sum
/// of two degree-9 ones.
const MAX_ARITH_DEGREE: usize = 3;

/// The same cap for comparison, which refines intervals but does not multiply
/// degrees, and so tolerates more.
const MAX_COMPARE_DEGREE: usize = 5;

/// Pick a real algebraic number from `p`: AY's object and z3's value for the
/// same root, or `None` when the input has no usable irrational root.
fn algebraic_pair(
    z3: &Z3,
    p: &GenPoly,
    pick: u64,
    max_degree: usize,
) -> Result<(OAlg, Ast), &'static str> {
    let ap = poly_of(p);
    if ap.degree().unwrap_or(0) < 1 {
        return Err("degree < 1");
    }
    let sf = ap.square_free_part().ok_or("square_free_part")?;
    if sf.degree().unwrap_or(0) > max_degree {
        return Err("defining degree above the arithmetic budget");
    }
    let markers = sf.isolate_roots().ok_or("isolate_roots")?;
    if markers.is_empty() {
        return Err("no real roots");
    }
    let roots = z3.roots(&p.coeffs).ok_or("z3 declined")?;
    if roots.len() != markers.len() {
        return Err("root counts differ (see roots check)");
    }
    let n = markers.len();
    for step in 0..n {
        let idx = (usize::try_from(pick).unwrap_or(0) + step) % n;
        if let ORoot::Interval(lo, hi) = &markers[idx] {
            if let Some(alpha) = OAlg::new(&sf, lo, hi) {
                return Ok((alpha, roots[idx]));
            }
        }
    }
    Err("no irrational marker")
}

/// Assert that AY's exact scalar lies inside the rational bracket z3 computed
/// for its own value. This is the oracle's universal comparison: it never
/// shares a representation between the two sides, only the real line.
fn scalar_in_bracket(
    ay_value: &ay::OScalar,
    lo: &BigRational,
    hi: &BigRational,
) -> Result<bool, &'static str> {
    if lo == hi {
        // z3 pinned an exact rational.
        return match ay_value.cmp_rational(lo) {
            Some(Ordering::Equal) => Ok(true),
            Some(_) => Ok(false),
            None => Err("cmp_rational"),
        };
    }
    let above = ay_value.cmp_rational(lo).ok_or("cmp_rational")?;
    let below = ay_value.cmp_rational(hi).ok_or("cmp_rational")?;
    Ok(above == Ordering::Greater && below == Ordering::Less)
}

/// Exact algebraic addition and multiplication.
pub(crate) fn check_arith(z3: &Z3, p: &GenPoly, q: &GenPoly, pick: u64, sab: Sabotage) -> Outcome {
    let (alpha, za) = match algebraic_pair(z3, p, pick, MAX_ARITH_DEGREE) {
        Ok(v) => v,
        Err(e) => return skip_or_decline(e),
    };
    let (beta, zb) = match algebraic_pair(z3, q, pick >> 8, MAX_ARITH_DEGREE) {
        Ok(v) => v,
        Err(e) => return skip_or_decline(e),
    };
    if z3.is_value(za) != Some(true) || z3.is_value(zb) != Some(true) {
        return Outcome::Skipped("z3 value not algebraic");
    }
    let mut comparisons = 0u64;
    for op in ["add", "mul"] {
        let zc = if op == "add" {
            z3.add(za, zb)
        } else {
            z3.mul(za, zb)
        };
        let Some(zc) = zc else {
            return Outcome::Skipped("z3 declined");
        };
        let ay_value = if op == "add" {
            alpha.add(&beta)
        } else {
            alpha.mul(&beta)
        };
        let Some(ay_value) = ay_value else {
            return Outcome::Declined("algebraic arithmetic");
        };
        // Sabotage: answer with one operand instead of the combination.
        let ay_value = if sab.on() {
            alpha.to_scalar()
        } else {
            ay_value
        };
        let Some((lo, hi)) = z3.bracket(zc, 48) else {
            return Outcome::Skipped("z3 declined");
        };
        match scalar_in_bracket(&ay_value, &lo, &hi) {
            Ok(true) => comparisons += 1,
            Ok(false) => {
                return Divergence::outcome(
                    "algebraic-arith",
                    "z3",
                    format!(
                        "AY's exact {op} of the two roots is not inside z3's bracket ({lo}, {hi})"
                    ),
                    inputs2(p, q),
                )
            }
            Err(e) => return Outcome::Declined(e),
        }
    }
    Outcome::Match(comparisons)
}

/// Exact comparison of two real algebraic numbers.
pub(crate) fn check_compare(
    z3: &Z3,
    p: &GenPoly,
    q: &GenPoly,
    pick: u64,
    sab: Sabotage,
) -> Outcome {
    let (alpha, za) = match algebraic_pair(z3, p, pick, MAX_COMPARE_DEGREE) {
        Ok(v) => v,
        Err(e) => return skip_or_decline(e),
    };
    let (beta, zb) = match algebraic_pair(z3, q, pick >> 8, MAX_COMPARE_DEGREE) {
        Ok(v) => v,
        Err(e) => return skip_or_decline(e),
    };
    let Some(ay_ord) = alpha.cmp_number(&beta) else {
        return Outcome::Declined("cmp_number");
    };
    // Sabotage: reverse the ordering.
    let ay_ord = if sab.on() { ay_ord.reverse() } else { ay_ord };
    if sab.on() && ay_ord == Ordering::Equal {
        return Outcome::Skipped("nothing to sabotage");
    }
    let Some(less) = z3.lt(za, zb) else {
        return Outcome::Skipped("z3 declined");
    };
    let z3_ord = if less {
        Ordering::Less
    } else {
        let Some(greater) = z3.gt(za, zb) else {
            return Outcome::Skipped("z3 declined");
        };
        if greater {
            Ordering::Greater
        } else {
            let Some(equal) = z3.eq(za, zb) else {
                return Outcome::Skipped("z3 declined");
            };
            if !equal {
                return Outcome::Skipped("z3 returned no total ordering");
            }
            Ordering::Equal
        }
    };
    let mut comparisons = 1u64;
    if ay_ord != z3_ord {
        return Divergence::outcome(
            "algebraic-compare",
            "z3",
            format!("AY says {ay_ord:?}, z3 says {z3_ord:?}"),
            inputs2(p, q),
        );
    }
    // Also pin each number against a rational z3 chose, exercising the
    // rational-vs-algebraic path rather than only algebraic-vs-algebraic.
    if let Some((lo, hi)) = z3.bracket(za, 40) {
        comparisons += 1;
        let want_above = alpha.cmp_rational(&lo);
        let want_below = alpha.cmp_rational(&hi);
        let ok = if lo == hi {
            want_above == Some(Ordering::Equal)
        } else {
            want_above == Some(Ordering::Greater) && want_below == Some(Ordering::Less)
        };
        if !ok {
            return Divergence::outcome(
                "algebraic-compare",
                "z3",
                format!("AY's root is not inside z3's own bracket ({lo}, {hi}) for the same root"),
                inputs1(p),
            );
        }
    }
    Outcome::Match(comparisons)
}

/// Classify an `algebraic_pair` failure: AY's fail-closed `None`s are declines,
/// everything else is an inapplicable input.
fn skip_or_decline(reason: &'static str) -> Outcome {
    match reason {
        "square_free_part" | "isolate_roots" => Outcome::Declined(reason),
        other => Outcome::Skipped(other),
    }
}

/// One case's outcome plus the shapes that produced it (for coverage
/// reporting: a fuzz run that never generated a `wilkinson` is not the run it
/// claims to be).
pub(crate) struct CaseResult {
    pub(crate) outcome: Outcome,
    pub(crate) shapes: Vec<&'static str>,
}

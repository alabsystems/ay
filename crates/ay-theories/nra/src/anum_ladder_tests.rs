// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for [`crate::anum`]'s refinement escalation ladder and the
//! coprime separation shortcut; the fixtures they share are in the parent
//! test module.

use super::*;

// ============================================================================
// The escalation ladder and the coprime separation shortcut
// ============================================================================

/// A small corpus of genuinely algebraic numbers, built the way callers do.
fn ladder_corpus() -> Vec<Anum> {
    let mut out = Vec::new();
    for d in [2i64, 3, 5, 6, 7, 10, 11, 13] {
        // The positive root of `x^2 - d`.
        if let Some(a) = Anum::from_poly_interval(
            &[-BigInt::from(d), BigInt::zero(), BigInt::one()],
            &iv_big(BigInt::zero(), BigInt::from(d) + 1),
        ) {
            out.push(a);
        }
    }
    for (n, d) in [(3usize, 2i64), (3, 5), (4, 2), (4, 7), (5, 3), (6, 2)] {
        // `x^n - d`: `n` coefficients `-d, 0, ..., 0`, then the leading one.
        let mut c = vec![BigInt::zero(); n];
        if let Some(constant) = c.first_mut() {
            *constant = -BigInt::from(d);
        }
        c.push(BigInt::one());
        let isolating = iv_big(BigInt::zero(), BigInt::from(d) + 1);
        if let Some(a) = Anum::from_poly_interval(&c, &isolating) {
            out.push(a);
        }
    }
    out
}

/// THE soundness property the coprime shortcut in `separation_exponent_for_pair`
/// rests on: skipping the square-free radical of the product may only make the
/// derived exponent LARGER — a weaker but still valid separation bound — never
/// smaller.
///
/// A smaller exponent would be an unsound bound, and an unsound bound is how a
/// comparison silently returns the wrong order. This is the one direction that
/// must never regress, so it is asserted directly rather than left to the
/// differential oracle to notice.
#[test]
fn the_coprime_separation_shortcut_never_understates_the_exponent() {
    let corpus = ladder_corpus();
    let mut coprime_pairs = 0u32;
    for a in &corpus {
        for b in &corpus {
            let (Some(ca), Some(cb)) = (a.cell(), b.cell()) else {
                continue;
            };
            let pa = ZPoly::from_coeffs(ca.poly_coeffs().to_vec());
            let pb = ZPoly::from_coeffs(cb.poly_coeffs().to_vec());
            let g = pa.gcd(&pb).unwrap();
            if g.degree() != Some(0) {
                continue;
            }
            coprime_pairs = coprime_pairs.saturating_add(1);
            let fast = separation_exponent_for_pair(&pa, &pb, &g).unwrap();
            // The exact quantity the pre-ladder code computed.
            let slow =
                root_separation_exponent(&normalize_defining(&pa.mul(&pb)).unwrap()).unwrap();
            assert!(
                fast >= slow,
                "shortcut UNDERSTATED the separation exponent: {fast} < {slow}"
            );
        }
    }
    assert!(
        coprime_pairs >= 100,
        "corpus produced only {coprime_pairs} coprime pairs — the assertion above \
         would be vacuous"
    );
}

/// The ladder must answer exactly what an unconditional refinement to the proved
/// bound answers. This is the direct before/after equivalence check: it rebuilds
/// the pre-ladder decision (refine BOTH sides to `2^-(B+2)`, then read the order
/// off the disjoint intervals) and demands agreement on every ordered pair.
#[test]
fn the_ladder_agrees_with_an_unconditional_refinement_to_the_proved_bound(
) -> Result<(), Box<dyn std::error::Error>> {
    let corpus = ladder_corpus();
    let mut compared = 0u32;
    for a in &corpus {
        for b in &corpus {
            let ord = a.cmp_anum(b).expect("comparison is total here");
            let (Some(ca), Some(cb)) = (a.cell(), b.cell()) else {
                continue;
            };
            let pa = ZPoly::from_coeffs(ca.poly_coeffs().to_vec());
            let pb = ZPoly::from_coeffs(cb.poly_coeffs().to_vec());
            let g = pa.gcd(&pb).unwrap();
            if g.degree() != Some(0) {
                // Equal-or-shared-factor pairs go through the certificate, which
                // the ladder does not touch.
                continue;
            }
            let b_bits =
                root_separation_exponent(&normalize_defining(&pa.mul(&pb)).unwrap()).unwrap();
            let exponent = b_bits
                .checked_add(2)
                .ok_or("separation exponent overflows u32")?;
            let target = Bq::inv_two_pow(exponent);
            let (ra, _) = mpbq::refine_to_width(ca.poly_coeffs(), ca.interval(), &target).unwrap();
            let (rb, _) = mpbq::refine_to_width(cb.poly_coeffs(), cb.interval(), &target).unwrap();
            let (Refined::Narrowed(ia), Refined::Narrowed(ib)) = (ra, rb) else {
                continue;
            };
            let reference = if ia.hi().cmp_bq(ib.lo()) != Ordering::Greater {
                Ordering::Less
            } else if ib.hi().cmp_bq(ia.lo()) != Ordering::Greater {
                Ordering::Greater
            } else {
                continue;
            };
            compared = compared.saturating_add(1);
            assert_eq!(
                ord, reference,
                "ladder disagreed with unconditional refinement to 2^-{exponent}"
            );
        }
    }
    assert!(compared >= 100, "only {compared} pairs compared — too weak");
    Ok(())
}

/// The sign ladder's certificate must agree with an unconditional refinement to
/// the proved bound followed by a midpoint evaluation — the rule this function
/// used before the ladder existed.
#[test]
fn the_sign_ladder_agrees_with_the_midpoint_rule_at_the_proved_bound(
) -> Result<(), Box<dyn std::error::Error>> {
    let corpus = ladder_corpus();
    let probes: Vec<Vec<BigInt>> = vec![
        zp(&[-3, 1]).coeffs().to_vec(),
        zp(&[1, 1]).coeffs().to_vec(),
        zp(&[-7, 0, 1]).coeffs().to_vec(),
        zp(&[-3, 1, -3, 1]).coeffs().to_vec(),
        zp(&[5, -2, 0, 1]).coeffs().to_vec(),
    ];
    let mut compared = 0u32;
    for a in &corpus {
        let Some(c) = a.cell() else { continue };
        for q in &probes {
            let s = a.sign_of_poly(q).expect("sign is total here");
            let qz = ZPoly::from_coeffs(q.clone());
            let qs = normalize_defining(&qz).unwrap();
            let pa = ZPoly::from_coeffs(c.poly_coeffs().to_vec());
            let g = pa.gcd(&qs).unwrap();
            if g.degree() != Some(0) {
                continue;
            }
            let b_bits =
                root_separation_exponent(&normalize_defining(&pa.mul(&qs)).unwrap()).unwrap();
            let target = Bq::inv_two_pow(
                b_bits
                    .checked_add(1)
                    .ok_or("separation exponent overflows u32")?,
            );
            let (r, _) = mpbq::refine_to_width(c.poly_coeffs(), c.interval(), &target).unwrap();
            let point = match r {
                Refined::Exact(m) => m,
                Refined::Narrowed(v) => v.midpoint().unwrap(),
            };
            let reference = mpbq::poly_sign_at(q, &point).unwrap();
            compared = compared.saturating_add(1);
            assert_eq!(s, reference, "sign ladder disagreed with the midpoint rule");
        }
    }
    assert!(compared >= 40, "only {compared} probes compared — too weak");
    Ok(())
}

/// The ladder must never report more bisections than the liveness bound it
/// declares, on any pair — the invariant the oracle's `anum-compare` check reads
/// off the trace.
#[test]
fn the_ladder_never_exceeds_its_declared_liveness_bound() {
    let corpus = ladder_corpus();
    let mut seen = 0u32;
    for a in &corpus {
        for b in &corpus {
            let Some((_, t)) = a.cmp_anum_traced(b) else {
                continue;
            };
            seen = seen.saturating_add(1);
            assert!(
                t.steps_a <= t.bound && t.steps_b <= t.bound,
                "steps {}/{} exceeded bound {}",
                t.steps_a,
                t.steps_b,
                t.bound
            );
            if t.equal_by_certificate {
                assert_eq!((t.steps_a, t.steps_b), (0, 0), "certificate path bisected");
            }
        }
    }
    assert!(seen >= 150, "only {seen} traces seen");
}

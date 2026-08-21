//! Focused probe: `select_non_root`'s "first `d+1` consecutive interior
//! integers" claim, on a WHOLLY NEGATIVE interval.
//!
//! `closest_to_zero(m0, m1)` returns `m1` — the LARGEST interior integer — when
//! the whole range is negative. The walk then does `m += 1`, immediately
//! exceeding `m1`, so exactly ONE candidate is probed per exponent instead of
//! `deg + 1`. The doc comment's completeness argument assumes `deg + 1`.

#![allow(unsafe_code)] // Dedicated C-ABI boundary to libz3; sites carry local invariants.

use ay_nra::oracle_api::{obq_select_non_root, OBq, OBqInterval};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Zero};

fn ref_poly_sign(p: &[BigInt], x: &BigRational) -> i32 {
    let mut acc = BigRational::zero();
    for c in p.iter().rev() {
        acc = acc * x + BigRational::from_integer(c.clone());
    }
    match acc.numer().sign() {
        num_bigint::Sign::Minus => -1,
        num_bigint::Sign::NoSign => 0,
        num_bigint::Sign::Plus => 1,
    }
}

/// Multiply `p` by `(c1*x + c0)`.
fn mul_lin(p: &[BigInt], c1: i64, c0: i64) -> Vec<BigInt> {
    let mut out = vec![BigInt::zero(); p.len() + 1];
    for (i, c) in p.iter().enumerate() {
        out[i] += c * BigInt::from(c0);
        out[i + 1] += c * BigInt::from(c1);
    }
    out
}

fn main() {
    // Probes on (-3, -1) are  -1 - 2^-k  for k = 0, 1, 2, ...
    // Plant a root at every one of them: (2^k x + 2^k + 1) has root -1 - 2^-k.
    let mut p = vec![BigInt::one()];
    for k in 0..=6u32 {
        p = mul_lin(&p, 1i64 << k, (1i64 << k) + 1);
    }
    println!(
        "p has degree {} with roots at -1 - 2^-k for k = 0..6",
        p.len() - 1
    );

    let iv = OBqInterval::new(
        &OBq::new(BigInt::from(-3), 0),
        &OBq::new(BigInt::from(-1), 0),
    )
    .unwrap();

    let got = obq_select_non_root(&p, &iv);
    println!(
        "select_non_root on (-3, -1) -> {:?}",
        got.as_ref()
            .map(|v| format!("{}/2^{}", v.numerator(), v.k()))
    );

    // Brute-force: does a dyadic non-root actually exist strictly inside?
    let mut witnesses = vec![];
    for k in 0..=8u32 {
        for m in -(3i64 << k) + 1..(-(1i64 << k)) {
            let r = BigRational::new(BigInt::from(m), BigInt::one() << k);
            if ref_poly_sign(&p, &r) != 0 {
                witnesses.push(format!("{m}/2^{k}"));
                if witnesses.len() >= 5 {
                    break;
                }
            }
        }
        if witnesses.len() >= 5 {
            break;
        }
    }
    println!("brute force finds interior dyadic NON-roots: {witnesses:?}");
    if got.is_none() && !witnesses.is_empty() {
        println!("\n*** INCOMPLETE: declined although non-roots exist ***");
    }

    // Mirror image: the SAME polynomial reflected to a positive interval, where
    // closest_to_zero returns m0 and the walk really does probe deg+1 points.
    let mut q = p.clone();
    for (i, c) in q.iter_mut().enumerate() {
        if i % 2 == 1 {
            *c = -c.clone();
        }
    }
    let piv =
        OBqInterval::new(&OBq::new(BigInt::from(1), 0), &OBq::new(BigInt::from(3), 0)).unwrap();
    let pgot = obq_select_non_root(&q, &piv);
    println!(
        "\nMIRROR: same polynomial reflected, select_non_root on (1, 3) -> {:?}",
        pgot.as_ref()
            .map(|v| format!("{}/2^{}", v.numerator(), v.k()))
    );
    println!("(the positive side succeeds; the asymmetry is the finding)");
}

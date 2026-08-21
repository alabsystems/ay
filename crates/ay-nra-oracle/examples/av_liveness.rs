//! LIVENESS TORTURE for `mpbq`. Every call is timed; anything that does not
//! return is a hang. Run under an external timeout.

#![allow(unsafe_code)] // Dedicated C-ABI boundary to libz3; sites carry local invariants.

use ay_nra::oracle_api::{
    obq_enclose_rational, obq_refine_step_bound, obq_refine_to_width, obq_refine_until_separated,
    obq_select_int, obq_select_non_root, obq_select_small, OBq, OBqInterval, ORefined, OSeparation,
};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::One;
use std::time::Instant;

fn t<T>(label: &str, f: impl FnOnce() -> T, show: impl FnOnce(&T) -> String) {
    let t0 = Instant::now();
    let v = f();
    let ms = t0.elapsed().as_millis();
    println!("  [{ms:>6} ms] {label}: {}", show(&v));
}

fn main() {
    let p = vec![BigInt::from(-2), BigInt::from(0), BigInt::from(1)]; // x^2 - 2
    let iv =
        OBqInterval::new(&OBq::new(BigInt::from(1), 0), &OBq::new(BigInt::from(2), 0)).unwrap();

    println!("=== 1. targets that cannot be met / are unrepresentable ===");
    t(
        "target = 0",
        || obq_refine_to_width(&p, &iv, &OBq::zero()),
        |v| format!("{:?}", v.is_some()),
    );
    t(
        "target < 0",
        || obq_refine_to_width(&p, &iv, &OBq::new(BigInt::from(-1), 3)),
        |v| format!("{:?}", v.is_some()),
    );
    for k in [16_383u32, 16_384, 16_385, 20_000, 100_000, 1_000_000] {
        t(
            &format!("target = 2^-{k} (bound vs MAX_REFINE_STEPS)"),
            || {
                let tt = OBq::inv_two_pow(k);
                (
                    obq_refine_step_bound(&iv.width(), &tt),
                    obq_refine_to_width(&p, &iv, &tt).is_some(),
                )
            },
            |v| format!("bound={:?} refined={}", v.0, v.1),
        );
    }

    println!("\n=== 2. huge denominator exponents fed straight to the entry points ===");
    for k in [1u32 << 20, 1 << 24, 1 << 26] {
        t(
            &format!("refine_step_bound(width=1, target=1/2^{k})"),
            || obq_refine_step_bound(&OBq::one_(), &OBq::inv_two_pow(k)),
            |v| format!("{v:?}"),
        );
    }
    for k in [1u32 << 20, 1 << 24] {
        t(
            &format!("select_small on (0, 1/2^{k}) — ceiling {k}"),
            || {
                OBqInterval::new(&OBq::zero(), &OBq::inv_two_pow(k))
                    .and_then(|i| obq_select_small(&i))
            },
            |v| format!("{:?}", v.as_ref().map(|s| s.0.k())),
        );
    }
    t(
        "select_small ceiling just over MAX_SELECT_K (2^20)",
        || {
            OBqInterval::new(&OBq::zero(), &OBq::inv_two_pow((1 << 20) + 5))
                .and_then(|i| obq_select_small(&i))
        },
        |v| format!("{:?}", v.as_ref().map(|s| s.0.k())),
    );
    for k in [1u32 << 20, 1 << 24] {
        t(
            &format!("enclose_rational at k = {k} (NO guard on k)"),
            || {
                obq_enclose_rational(
                    &BigRational::new(BigInt::one(), BigInt::from(3)),
                    &BigRational::new(BigInt::from(2), BigInt::from(3)),
                    k,
                )
            },
            |v| format!("{:?}", v.as_ref().map(|i| i.max_k())),
        );
    }

    println!("\n=== 3. endpoints that compare equal but are written differently ===");
    let a = OBq::new(BigInt::from(3), 2);
    let b = OBq::new(BigInt::from(12), 4); // same value, different spelling
    t(
        "BqInterval::new(3/2^2, 12/2^4)",
        || OBqInterval::new(&a, &b),
        |v| format!("{:?}", v.is_some()),
    );
    t(
        "BqInterval::new inverted",
        || OBqInterval::new(&b, &OBq::new(BigInt::from(1), 4)),
        |v| format!("{:?}", v.is_some()),
    );
    t(
        "select_int on an equal pair",
        || obq_select_int(&a, &b),
        |v| format!("{v:?}"),
    );

    println!("\n=== 4. separation at the full budget, including EQUAL roots ===");
    let two =
        OBqInterval::new(&OBq::new(BigInt::from(1), 0), &OBq::new(BigInt::from(2), 0)).unwrap();
    for budget in [1_000u32, 16_384, u32::MAX] {
        t(
            &format!("refine_until_separated(x^2-2 vs ITSELF, budget {budget})"),
            || obq_refine_until_separated(&p, &two, &p, &two, budget),
            |v| match v {
                Some((OSeparation::Inconclusive, _, _, r)) => {
                    format!("Inconclusive after {r} rounds")
                }
                Some((OSeparation::Ordered(o), _, _, r)) => format!("Ordered({o:?}) after {r}"),
                None => "None".into(),
            },
        );
    }
    let q = vec![BigInt::from(-3), BigInt::from(0), BigInt::from(1)];
    let thr =
        OBqInterval::new(&OBq::new(BigInt::from(1), 0), &OBq::new(BigInt::from(2), 0)).unwrap();
    t(
        "refine_until_separated(sqrt2 vs sqrt3, budget u32::MAX)",
        || obq_refine_until_separated(&p, &two, &q, &thr, u32::MAX),
        |v| match v {
            Some((OSeparation::Ordered(o), _, _, r)) => format!("Ordered({o:?}) after {r} rounds"),
            Some((OSeparation::Inconclusive, _, _, r)) => format!("Inconclusive after {r}"),
            None => "None".into(),
        },
    );

    println!("\n=== 5. select_non_root against a polynomial with many roots ===");
    // (x-1)(x-2)...(x-30) scaled: 30 roots, all integers, inside (0, 31)
    let mut poly = vec![BigInt::one()];
    for r in 1..=30i64 {
        let mut out = vec![BigInt::from(0); poly.len() + 1];
        for (i, c) in poly.iter().enumerate() {
            out[i] += c * BigInt::from(-r);
            out[i + 1] += c.clone();
        }
        poly = out;
    }
    let wide = OBqInterval::new(&OBq::zero(), &OBq::new(BigInt::from(31), 0)).unwrap();
    t(
        "select_non_root, deg 30, interval (0, 31)",
        || obq_select_non_root(&poly, &wide),
        |v| {
            format!(
                "{:?}",
                v.as_ref().map(|x| format!("{}/2^{}", x.numerator(), x.k()))
            )
        },
    );
    let negw = OBqInterval::new(&OBq::new(BigInt::from(-31), 0), &OBq::zero()).unwrap();
    let mut negpoly = poly.clone();
    for (i, c) in negpoly.iter_mut().enumerate() {
        if i % 2 == 1 {
            *c = -c.clone();
        }
    }
    t(
        "select_non_root, deg 30, MIRRORED to (-31, 0)",
        || obq_select_non_root(&negpoly, &negw),
        |v| {
            format!(
                "{:?}",
                v.as_ref().map(|x| format!("{}/2^{}", x.numerator(), x.k()))
            )
        },
    );

    println!("\n=== 6. the full refinement chain at MAX_REFINE_STEPS ===");
    t(
        "refine_to_width to 2^-16000 from (1, 2)",
        || obq_refine_to_width(&p, &iv, &OBq::inv_two_pow(16_000)),
        |v| match v {
            Some((ORefined::Narrowed(i), tr)) => format!(
                "Narrowed max_k={} steps={} bound={}",
                i.max_k(),
                tr.steps,
                tr.bound
            ),
            Some((ORefined::Exact(_), tr)) => format!("Exact steps={}", tr.steps),
            None => "None".into(),
        },
    );

    println!("\nALL CALLS RETURNED — no hang.");
}

// tiny helper so the example does not need `Bq::one` exposed
trait OneBq {
    fn one_() -> Self;
}
impl OneBq for OBq {
    fn one_() -> Self {
        OBq::new(BigInt::one(), 0)
    }
}

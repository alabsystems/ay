//! Focused repro: `refine_step_bound` at `bits(L) == bits(R)`.

use ay_nra::oracle_api::{obq_refine_step_bound, obq_refine_to_width, OBq, OBqInterval, ORefined};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::One;

fn r_of(a: i64, k: u32) -> BigRational {
    BigRational::new(BigInt::from(a), BigInt::one() << k)
}

fn main() {
    println!("=== 1. refine_step_bound returns a bound that is NOT sufficient ===");
    let cases: [(i64, u32, i64, u32); 6] = [
        (3, 1, 1, 0), // width 3/2, target 1
        (1021, 3, 3677, 5),
        (3, 0, 2, 0), // width 3, target 2
        (5, 0, 3, 0), // width 5, target 3
        (7, 2, 5, 2), // width 7/4, target 5/4
        (1, 0, 3, 2), // width 1, target 3/4
    ];
    for (wa, wk, ta, tk) in cases {
        let w = OBq::new(BigInt::from(wa), wk);
        let t = OBq::new(BigInt::from(ta), tk);
        let (rw, rt) = (r_of(wa, wk), r_of(ta, tk));
        let b = obq_refine_step_bound(&w, &t);
        // truth: smallest n with w/2^n <= t
        let two = BigRational::from_integer(BigInt::from(2));
        let mut cur = rw.clone();
        let mut n = 0u32;
        while cur > rt {
            cur /= &two;
            n += 1;
        }
        // is the RETURNED bound actually sufficient?
        let sufficient = b.map(|b| {
            let mut c = rw.clone();
            for _ in 0..b {
                c /= &two;
            }
            c <= rt
        });
        println!(
            "  width={rw:<24} target={rt:<20} bound={b:?} exact_min={n} bound_sufficient={sufficient:?}"
        );
    }

    println!();
    println!("=== 2. the consequence: refine_to_width SPURIOUSLY DECLINES ===");
    // x^2 - 2, root sqrt(2) ~ 1.4142. (1/2, 2) is a genuine isolating interval:
    // p(1/2) = -7/4 < 0, p(2) = +2 > 0. Width 3/2. Target 1.
    let p = vec![BigInt::from(-2), BigInt::from(0), BigInt::from(1)];
    let iv = OBqInterval::new(&OBq::new(BigInt::from(1), 1), &OBq::new(BigInt::from(2), 0))
        .expect("(1/2, 2) is a valid interval");
    for (ta, tk) in [(1i64, 0u32), (1, 1), (3, 1), (1, 2)] {
        let t = OBq::new(BigInt::from(ta), tk);
        let out = obq_refine_to_width(&p, &iv, &t);
        let desc = match &out {
            None => "None  <-- DECLINED".to_string(),
            Some((ORefined::Narrowed(iv), tr)) => format!(
                "Narrowed ({}/2^{}, {}/2^{}) steps={} bound={}",
                iv.lo().numerator(),
                iv.lo().k(),
                iv.hi().numerator(),
                iv.hi().k(),
                tr.steps,
                tr.bound
            ),
            Some((ORefined::Exact(v), tr)) => {
                format!("Exact {}/2^{} steps={}", v.numerator(), v.k(), tr.steps)
            }
        };
        println!("  target {ta}/2^{tk}  ->  {desc}");
    }

    println!();
    println!("=== 3. how often does bits(L)==bits(R) arise on natural inputs? ===");
    // width = wa/2^wk from a real bisection chain, target = 2^-t as nlsat asks.
    let mut hit = 0u32;
    let mut tot = 0u32;
    for wk in 0..20u32 {
        for wa in [1i64, 3, 5, 7, 9, 11, 13, 15, 17, 33, 63, 65, 127, 129] {
            for t in 0..20u32 {
                let w = OBq::new(BigInt::from(wa), wk);
                let tt = OBq::inv_two_pow(t);
                let (rw, rt) = (r_of(wa, wk), r_of(1, t));
                if rw <= rt {
                    continue;
                }
                tot += 1;
                if let Some(b) = obq_refine_step_bound(&w, &tt) {
                    let two = BigRational::from_integer(BigInt::from(2));
                    let mut c = rw.clone();
                    for _ in 0..b {
                        c /= &two;
                    }
                    if c > rt {
                        hit += 1;
                    }
                }
            }
        }
    }
    println!("  insufficient bound on {hit} of {tot} width/target pairs with width > target");
}

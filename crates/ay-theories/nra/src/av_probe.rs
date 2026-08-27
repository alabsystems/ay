// ADVERSARIAL VERIFICATION probe harness for `crate::ialg`.
// Not part of the lane under review. Independent reference model + fail-open
// probes + liveness probes. Everything here is `#[cfg(test)]`.

#![allow(clippy::needless_range_loop)]

use std::cmp::Ordering;
use std::time::Instant;

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Zero};

use crate::anum::Anum;
use crate::ialg::*;
use crate::mpbq::{Bq, BqInterval};

// ---------------------------------------------------------------- rng
struct R(u64);
impl R {
    fn new(s: u64) -> Self {
        R(s ^ 0x9E37_79B9_7F4A_7C15)
    }
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
    fn below(&mut self, n: u64) -> u64 {
        if n == 0 {
            0
        } else {
            self.next() % n
        }
    }
    fn bit(&mut self) -> bool {
        self.next() & 1 == 1
    }
}

// ---------------------------------------------------------------- builders
fn ri(n: i64) -> Anum {
    Anum::rational(BigRational::from_integer(BigInt::from(n)))
}
fn rq(n: i64, d: i64) -> Anum {
    Anum::rational(BigRational::new(BigInt::from(n), BigInt::from(d)))
}
fn bq_i(n: i64) -> Bq {
    Bq::from_int(BigInt::from(n))
}

/// The unique root of `coeffs` in `(lo, hi)`, as an `Anum`.
fn alg(coeffs: &[i64], lo: i64, hi: i64) -> Anum {
    let c: Vec<BigInt> = coeffs.iter().map(|&v| BigInt::from(v)).collect();
    let iv = BqInterval::new(bq_i(lo), bq_i(hi)).expect("ordered bracket");
    Anum::from_poly_interval(&c, &iv).expect("isolating bracket")
}

/// sqrt(d) as a root of `x^2 - d`.
fn sq(d: i64) -> Anum {
    alg(&[-d, 0, 1], 0, d + 1)
}
/// sqrt(d) as a root of the REDUCIBLE `(x^2 - d)(x^2 - e)` — the SAME real
/// value through a DIFFERENT defining polynomial. The bracket must isolate
/// +sqrt(d) away from +sqrt(e) and from the negative roots, so it is given
/// explicitly rather than guessed.
fn sq_via(d: i64, e: i64, lo: i64, hi: i64) -> Anum {
    // (x^2-d)(x^2-e) = x^4 - (d+e)x^2 + d*e
    alg(&[d * e, 0, -(d + e), 0, 1], lo, hi)
}

fn end(a: &Anum) -> AEnd {
    AEnd::Fin(a.clone())
}

fn mk(lo: AEnd, lo_open: bool, hi: AEnd, hi_open: bool, lit: i32) -> Option<DecidedInterval> {
    DecidedInterval::from_bounds(lo, lo_open, hi, hi_open, Just::of(lit).unwrap())
}

fn nonempty(decision: Option<DecidedInterval>) -> AInterval {
    decision
        .expect("endpoint comparison must decide")
        .into_interval()
        .expect("test interval must be non-empty")
}

#[cfg(test)]
include!("av_probe/failopen.rs");

#[cfg(test)]
include!("av_probe/reference.rs");

#[cfg(test)]
include!("av_probe/degenerate.rs");

// ============================================================================
// PART C — LIVENESS
// ============================================================================

#[test]
fn av_liveness_equal_algebraic_endpoints_do_not_refine_forever() {
    let t = Instant::now();
    let a = sq(10);
    let b = sq_via(10, 5, 3, 4);
    for _ in 0..200 {
        assert_eq!(a.cmp_anum(&b), Some(Ordering::Equal));
    }
    println!(
        "AV-LIVENESS: 200 equal-value/different-poly comparisons in {:?}",
        t.elapsed()
    );

    // The same equality driven through every ialg predicate that could spin.
    let t = Instant::now();
    for _ in 0..200 {
        assert!(
            DecidedInterval::from_bounds(end(&a), true, end(&b), true, Just::none())
                .expect("equal endpoints are comparable")
                .into_interval()
                .is_none()
        );
        let s = IntervalSet::normalize(vec![
            nonempty(DecidedInterval::from_bounds(
                AEnd::NegInf,
                true,
                end(&a),
                false,
                Just::none(),
            )),
            nonempty(DecidedInterval::from_bounds(
                end(&b),
                true,
                AEnd::PosInf,
                true,
                Just::none(),
            )),
        ])
        .unwrap();
        assert_eq!(s.len(), 1);
    }
    println!(
        "AV-LIVENESS: 200 normalize() over equal algebraic endpoints in {:?}",
        t.elapsed()
    );
}

#[test]
fn av_liveness_pathologically_narrow_cells_decline_not_spin() {
    // A cell of width 2^-300 between two RATIONAL roots: the bracket ladder
    // tops out at 2^-256 and must DECLINE.
    let t = Instant::now();
    let k = 300u32;
    let lo = ri(0);
    let hi = Anum::rational(BigRational::new(BigInt::one(), BigInt::one() << k));
    let iv = DecidedInterval::from_bounds(end(&lo), true, end(&hi), true, Just::none())
        .expect("rational endpoints are comparable")
        .into_interval()
        .expect("(0, 2^-300) wrongly empty");
    let s = IntervalSet::normalize(vec![iv]).unwrap();
    assert!(!s.is_empty());
    let p = s.pick();
    println!(
        "AV-LIVENESS: pick on a 2^-300-wide open rational cell -> {:?} in {:?}",
        p.as_ref().map(classify_value),
        t.elapsed()
    );

    // The same shape driven through from_sign_condition: p = 2^300 x^2 - x has
    // roots 0 and 2^-300, so the middle open cell has no dyadic sample.
    let t = Instant::now();
    let big = BigInt::one() << k;
    let poly = vec![BigInt::zero(), BigInt::from(-1), big];
    let r = from_sign_condition(&poly, &[ri(0), hi.clone()], SignCond::Gt, Just::none());
    println!(
        "AV-LIVENESS: from_sign_condition over a 2^-300 cell -> {} in {:?}",
        if r.is_none() {
            "None (DECLINED)"
        } else {
            "Some(..)"
        },
        t.elapsed()
    );
    assert!(
        t.elapsed().as_secs() < 30,
        "from_sign_condition took too long"
    );
}

#[test]
fn av_liveness_at_the_ceilings() {
    // MAX_INTERVALS worth of algebraic-endpoint intervals through the O(n^2)
    // fallible insertion sort, fed in DESCENDING order (worst case).
    let t = Instant::now();
    let n = 256usize;
    let mut ivs = Vec::with_capacity(n);
    for i in (0..n).rev() {
        let base = 4 * i as i64;
        // roots of (x - base)^2 - 2  ->  base +- sqrt(2)
        let c = vec![
            BigInt::from(base * base - 2),
            BigInt::from(-2 * base),
            BigInt::one(),
        ];
        let lo_iv = BqInterval::new(bq_i(base - 2), bq_i(base)).unwrap();
        let hi_iv = BqInterval::new(bq_i(base), bq_i(base + 2)).unwrap();
        let lo = Anum::from_poly_interval(&c, &lo_iv).unwrap();
        let hi = Anum::from_poly_interval(&c, &hi_iv).unwrap();
        ivs.push(nonempty(DecidedInterval::from_bounds(
            AEnd::Fin(lo),
            false,
            AEnd::Fin(hi),
            false,
            Just::none(),
        )));
    }
    let build = Instant::now();
    let s = IntervalSet::normalize(ivs).expect("normalizes at the ceiling");
    let dt = build.elapsed();
    assert_eq!(s.len(), n);
    println!(
        "AV-LIVENESS: normalize(256 descending algebraic intervals) = {:?} (setup {:?})",
        dt,
        t.elapsed().saturating_sub(dt)
    );

    let t2 = Instant::now();
    let c = s.complement();
    println!(
        "AV-LIVENESS: complement at n=256 -> {} in {:?}",
        if c.is_none() {
            "None (ceiling DECLINE)"
        } else {
            "Some(..)"
        },
        t2.elapsed()
    );

    let t3 = Instant::now();
    let i = s.intersect(&s).expect("self-intersection");
    assert_eq!(i.len(), n);
    println!("AV-LIVENESS: intersect(256,256) in {:?}", t3.elapsed());

    let t4 = Instant::now();
    let v = s.pick();
    println!(
        "AV-LIVENESS: pick at n=256 -> {:?} in {:?}",
        v.map(|x| classify_value(&x)),
        t4.elapsed()
    );
}

#[test]
fn av_liveness_chained_intersections_do_not_grow_degree() {
    // 40 chained intersections; degree and cost must stay flat.
    let t = Instant::now();
    let mut s = IntervalSet::full(Just::none());
    let mut rng = R::new(99);
    for step in 0..40 {
        let mut ivs = Vec::new();
        for j in 0..8 {
            let base = (rng.below(20) as i64) - 10 + j * 3;
            let c = vec![
                BigInt::from(base * base - 2),
                BigInt::from(-2 * base),
                BigInt::one(),
            ];
            let lo_iv = BqInterval::new(bq_i(base - 2), bq_i(base)).unwrap();
            let hi_iv = BqInterval::new(bq_i(base), bq_i(base + 2)).unwrap();
            let lo = Anum::from_poly_interval(&c, &lo_iv).unwrap();
            let hi = Anum::from_poly_interval(&c, &hi_iv).unwrap();
            if let Some(interval) = DecidedInterval::from_bounds(
                AEnd::Fin(lo),
                false,
                AEnd::Fin(hi),
                false,
                Just::none(),
            )
            .expect("algebraic endpoints are comparable")
            .into_interval()
            {
                ivs.push(interval);
            }
        }
        let Some(o) = IntervalSet::normalize(ivs) else {
            continue;
        };
        let Some(next) = s.intersect(&o) else {
            println!("AV-LIVENESS: chain DECLINED at step {step}");
            break;
        };
        s = next;
        if s.is_empty() {
            break;
        }
        let maxdeg = s
            .intervals()
            .iter()
            .flat_map(|iv| [iv.lo().value(), iv.hi().value()])
            .flatten()
            .map(Anum::degree)
            .max()
            .unwrap_or(0);
        assert!(
            maxdeg <= 2,
            "endpoint degree GREW to {maxdeg} at step {step}"
        );
    }
    println!(
        "AV-LIVENESS: 40 chained intersections, max endpoint degree 2, {:?}",
        t.elapsed()
    );
}

/// REGRESSION GUARD for the blind spot this probe originally FOUND.
///
/// As first measured (on the pre-integration cut of `ialg.rs`),
/// `from_sign_condition` verified that the root list ASCENDS but never that it
/// IS the root list of `p`. An incomplete list silently produced a wrong
/// feasible set in the UNSOUND direction: the EMPTY set for a non-empty one,
/// i.e. a conflict that does not exist.
///
/// The integrated `ialg.rs` closes it — see the "STRONG half" comment on
/// `from_sign_condition`, which cites this very `p = x^2 - 1` case. The probe is
/// kept, inverted, so the refusal cannot silently regress.
#[test]
fn av_from_sign_condition_refuses_an_unverified_root_list() {
    // p = x^2 - 1, real roots -1 and +1.
    let p = vec![BigInt::from(-1), BigInt::zero(), BigInt::one()];
    let full_roots = vec![ri(-1), ri(1)];
    let partial = vec![ri(1)]; // -1 dropped

    // Ground truth with the COMPLETE list is unchanged: {p<0} is (-1,1).
    let lt_ok = from_sign_condition(&p, &full_roots, SignCond::Lt, Just::none()).unwrap();
    assert!(!lt_ok.is_empty(), "{{p<0}} is (-1,1), not empty");
    assert_eq!(lt_ok.contains(&ri(0)), Some(true));

    // The SAME query with an INCOMPLETE list must now be REFUSED outright,
    // rather than answered with the empty set.
    assert!(
        from_sign_condition(&p, &partial, SignCond::Lt, Just::none()).is_none(),
        "an incomplete root list must be refused, not answered with `empty` \
         (that was the original unsound finding)"
    );
    assert!(
        from_sign_condition(&p, &partial, SignCond::Gt, Just::none()).is_none(),
        "the too-large direction must be refused as well"
    );

    // A root list containing a NON-root must be refused too.
    let bogus = vec![ri(-1), ri(0), ri(1)];
    assert!(
        from_sign_condition(&p, &bogus, SignCond::Eq, Just::none()).is_none(),
        "a non-root (0) in the list must be refused"
    );
}

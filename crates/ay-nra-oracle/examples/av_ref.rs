//! ADVERSARIAL VERIFICATION reference for `mpbq`.
//!
//! Independent model: every dyadic is carried as a plain `BigRational` with NO
//! packed exponent. The "denominator exponent" is recovered by repeatedly
//! dividing the reduced denominator by two and counting — a different algorithm
//! from the bit-twiddling `(bits-1)` test the module uses, and one that shares
//! no code with it. Every predicate below is computed from that rational form.

#![allow(unsafe_code)] // Dedicated C-ABI boundary to libz3; sites carry local invariants.

use ay_nra::oracle_api::{
    obq_candidate_at, obq_enclose_rational, obq_poly_eval_at, obq_poly_sign_at,
    obq_refine_step_bound, obq_refine_to_width, obq_refine_until_separated, obq_select_int,
    obq_select_non_root, obq_select_small, OBq, OBqInterval, ORefined,
};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use std::cmp::Ordering;

// ---------------------------------------------------------------------------
// Tiny deterministic RNG (xorshift64*) so runs are reproducible.
// ---------------------------------------------------------------------------
struct R(u64);
impl R {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }
    fn below(&mut self, n: u64) -> u64 {
        if n == 0 {
            0
        } else {
            self.next() % n
        }
    }
    fn range(&mut self, lo: i64, hi: i64) -> i64 {
        lo + (self.below((hi - lo + 1) as u64) as i64)
    }
}

// ---------------------------------------------------------------------------
// The independent model.
// ---------------------------------------------------------------------------

/// Recover the dyadic exponent of `r` by DIVIDING OUT twos and counting.
/// `None` when the reduced denominator retains an odd factor > 1.
fn ref_exponent(r: &BigRational) -> Option<u32> {
    let mut d = r.denom().clone();
    let two = BigInt::from(2);
    let mut k: u32 = 0;
    while d.is_even_ref() {
        d /= &two;
        k = k.checked_add(1)?;
    }
    if d.is_one() {
        Some(k)
    } else {
        None
    }
}

trait EvenRef {
    fn is_even_ref(&self) -> bool;
}
impl EvenRef for BigInt {
    fn is_even_ref(&self) -> bool {
        !self.is_zero() && (self % BigInt::from(2)).is_zero()
    }
}

fn r_of(a: i64, k: u32) -> BigRational {
    BigRational::new(BigInt::from(a), BigInt::one() << k)
}

fn to_r(v: &OBq) -> BigRational {
    BigRational::new(v.numerator(), BigInt::one() << v.k())
}

fn rfloor(r: &BigRational) -> BigInt {
    r.floor().to_integer()
}
fn rceil(r: &BigRational) -> BigInt {
    r.ceil().to_integer()
}

/// Reference `floor(r * 2^t)`.
fn ref_floor_at(r: &BigRational, t: u32) -> BigInt {
    rfloor(&(r * BigRational::from_integer(BigInt::one() << t)))
}
fn ref_ceil_at(r: &BigRational, t: u32) -> BigInt {
    rceil(&(r * BigRational::from_integer(BigInt::one() << t)))
}

/// Reference step bound: smallest n with width/2^n <= target, found by an
/// explicit loop, not a bit-length formula.
fn ref_step_bound(width: &BigRational, target: &BigRational, cap: u32) -> Option<u32> {
    if !width.is_positive() || !target.is_positive() {
        return None;
    }
    let two = BigRational::from_integer(BigInt::from(2));
    let mut w = width.clone();
    let mut n: u32 = 0;
    while w > *target {
        w /= &two;
        n += 1;
        if n > cap {
            return None;
        }
    }
    Some(n)
}

/// Reference polynomial sign at a rational.
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
fn ref_poly_eval(p: &[BigInt], x: &BigRational) -> BigRational {
    let mut acc = BigRational::zero();
    for c in p.iter().rev() {
        acc = acc * x + BigRational::from_integer(c.clone());
    }
    acc
}

/// Reference `candidate_at`: the interior integer at scale `k` closest to zero.
fn ref_candidate_at(lo: &BigRational, hi: &BigRational, k: u32) -> Option<BigInt> {
    let m0: BigInt = ref_floor_at(lo, k) + 1;
    let m1: BigInt = ref_ceil_at(hi, k) - 1;
    if m0 > m1 {
        return None;
    }
    Some(if m0.is_positive() {
        m0
    } else if m1.is_negative() {
        m1
    } else {
        BigInt::zero()
    })
}

/// Reference minimal-k selection: brute-force scan.
fn ref_select_small(lo: &BigRational, hi: &BigRational, ceiling: u32) -> Option<(u32, BigInt)> {
    for k in 0..=ceiling {
        if let Some(m) = ref_candidate_at(lo, hi, k) {
            return Some((k, m));
        }
    }
    None
}

macro_rules! bad {
    ($n:expr, $($t:tt)*) => {{
        println!("DIVERGENCE [case {}] {}", $n, format!($($t)*));
        return false;
    }};
}

fn one_case(n: u64, rng: &mut R) -> bool {
    // ---- draw two dyadics, including degenerate shapes ---------------------
    let shape = rng.below(6);
    let (xa, xk, ya, yk) = match shape {
        0 => (0i64, rng.below(40) as u32, 0i64, 0u32), // zero, several spellings
        1 => (rng.range(-8, 8), 0, rng.range(-8, 8), 0), // k == 0
        2 => (
            rng.range(-4096, 4096),
            rng.below(60) as u32,
            rng.range(-4096, 4096),
            rng.below(60) as u32,
        ),
        3 => {
            // deliberately equal values written differently: a/2^k vs 2a/2^(k+1)
            let a = rng.range(-100, 100);
            let k = rng.below(20) as u32;
            (a, k, a * 2, k + 1)
        }
        4 => (
            rng.range(-3, 3),
            rng.below(3) as u32,
            rng.range(-3, 3),
            rng.below(3) as u32,
        ),
        _ => (
            rng.range(-i64::pow(2, 40), i64::pow(2, 40)),
            rng.below(200) as u32,
            rng.range(-1000, 1000),
            rng.below(200) as u32,
        ),
    };

    let x = OBq::new(BigInt::from(xa), xk);
    let y = OBq::new(BigInt::from(ya), yk);
    let (rx, ry) = (r_of(xa, xk), r_of(ya, yk));

    // ---- canonical form: k == 0 or numerator odd, zero is (0,0) -----------
    for (v, r) in [(&x, &rx), (&y, &ry)] {
        if to_r(v) != *r {
            bad!(n, "value drifted: {}/2^{} != {}", v.numerator(), v.k(), r);
        }
        if v.numerator().is_zero() && v.k() != 0 {
            bad!(n, "zero not canonical: k={}", v.k());
        }
        if v.k() != 0 && !v.numerator().is_odd_ref() {
            bad!(n, "non-canonical: k={} numerator even", v.k());
        }
        // the recovered exponent must match the packed one
        match ref_exponent(r) {
            Some(k) if k == v.k() => {}
            other => bad!(
                n,
                "exponent mismatch: packed {} vs recovered {:?}",
                v.k(),
                other
            ),
        }
    }

    // ---- structural equality IS numeric equality ---------------------------
    let struct_eq = x.numerator() == y.numerator() && x.k() == y.k();
    if struct_eq != (rx == ry) {
        bad!(
            n,
            "PartialEq unsound: struct {} vs numeric {}",
            struct_eq,
            rx == ry
        );
    }

    // ---- arithmetic --------------------------------------------------------
    if to_r(&x.add(&y)) != &rx + &ry {
        bad!(n, "add wrong");
    }
    if to_r(&x.sub(&y)) != &rx - &ry {
        bad!(n, "sub wrong");
    }
    match x.mul(&y) {
        Some(p) => {
            if to_r(&p) != &rx * &ry {
                bad!(n, "mul wrong");
            }
        }
        None => {
            if (xk as u64) + (yk as u64) <= u32::MAX as u64 {
                bad!(n, "mul declined without overflow (k {} + {})", xk, yk);
            }
        }
    }
    if to_r(&x.neg()) != -&rx {
        bad!(n, "neg wrong");
    }
    if to_r(&x.abs()) != rx.abs() {
        bad!(n, "abs wrong");
    }
    if x.is_int() != rx.is_integer() {
        bad!(n, "is_int wrong at {}", rx);
    }
    if x.sign() != ref_poly_sign(&[BigInt::zero(), BigInt::one()], &rx) {
        bad!(n, "sign wrong");
    }
    let ord = x.cmp_bq(&y);
    let rord = rx.cmp(&ry);
    if ord != rord {
        bad!(n, "cmp wrong: {:?} vs {:?}", ord, rord);
    }
    if x.floor() != rfloor(&rx) {
        bad!(n, "floor wrong at {}: {} vs {}", rx, x.floor(), rfloor(&rx));
    }
    if x.ceil() != rceil(&rx) {
        bad!(n, "ceil wrong at {}: {} vs {}", rx, x.ceil(), rceil(&rx));
    }
    // shifts
    let e = rng.below(70) as u32;
    let two_e = BigRational::from_integer(BigInt::one() << e);
    if to_r(&x.mul_two_pow(e)) != &rx * &two_e {
        bad!(n, "mul_two_pow({}) wrong", e);
    }
    match x.div_two_pow(e) {
        Some(v) => {
            if to_r(&v) != &rx / &two_e {
                bad!(n, "div_two_pow({}) wrong", e);
            }
        }
        None => {
            if (xk as u64) + (e as u64) <= u32::MAX as u64 && !xa == 0 {
                bad!(n, "div_two_pow declined without overflow");
            }
        }
    }
    // scaled rounding at a target both above and below k
    for t in [0u32, 1, xk.saturating_sub(1), xk, xk + 1, xk + 17, e] {
        if x.floor_at(t) != ref_floor_at(&rx, t) {
            bad!(n, "floor_at({}) wrong at {}/2^{}", t, xa, xk);
        }
        if x.ceil_at(t) != ref_ceil_at(&rx, t) {
            bad!(n, "ceil_at({}) wrong at {}/2^{}", t, xa, xk);
        }
    }

    // ---- representability: BOTH directions --------------------------------
    // dyadic positive control (written unreduced)
    let dk = rng.below(12) as u32;
    let dnum = rng.range(-400, 400);
    let dy = BigRational::new(BigInt::from(dnum) * 6, (BigInt::one() << dk) * 6);
    if !OBq::is_representable(&dy) {
        bad!(n, "is_representable said NO to the dyadic {}", dy);
    }
    match OBq::from_rational(&dy) {
        Some(v) if to_r(&v) == dy => {}
        other => bad!(
            n,
            "from_rational lost the dyadic {} -> {:?}",
            dy,
            other.map(|v| to_r(&v))
        ),
    }
    // non-dyadic negative control: odd factor that CANNOT cancel
    let odd = [3i64, 5, 7, 9, 11, 13, 15, 21, 25, 27, 33, 49][rng.below(12) as usize];
    let mut num = rng.range(1, 5000);
    while num % odd == 0 {
        num += 1;
    }
    let nd = BigRational::new(
        BigInt::from(num),
        BigInt::from(odd) * (BigInt::one() << rng.below(6)),
    );
    let truly_dyadic = ref_exponent(&nd).is_some();
    if OBq::is_representable(&nd) != truly_dyadic {
        bad!(
            n,
            "is_representable({}) = {} but truth is {}",
            nd,
            OBq::is_representable(&nd),
            truly_dyadic
        );
    }
    if OBq::from_rational(&nd).is_some() != truly_dyadic {
        bad!(n, "from_rational/is_representable DRIFTED on {}", nd);
    }

    // ---- intervals ---------------------------------------------------------
    let iv = OBqInterval::new(&x, &y);
    let should_exist = rx < ry;
    if iv.is_some() != should_exist {
        bad!(
            n,
            "interval ctor: got {} expected {} for ({}, {})",
            iv.is_some(),
            should_exist,
            rx,
            ry
        );
    }
    if let Some(iv) = iv {
        let w = to_r(&iv.width());
        if w != &ry - &rx {
            bad!(n, "width wrong");
        }
        if !w.is_positive() {
            bad!(n, "width not positive");
        }
        let mid = iv.midpoint().expect("midpoint of a non-empty interval");
        let rmid = (&rx + &ry) / BigRational::from_integer(BigInt::from(2));
        if to_r(&mid) != rmid {
            bad!(n, "midpoint wrong");
        }
        if !(rx < rmid && rmid < ry) {
            bad!(n, "midpoint not strictly inside");
        }
        if mid.k() > x.k().max(y.k()) + 1 {
            bad!(
                n,
                "midpoint k blew up: {} > max({},{})+1",
                mid.k(),
                x.k(),
                y.k()
            );
        }
        if iv.max_k() != x.k().max(y.k()) {
            bad!(n, "max_k wrong");
        }
        let (l, m2, r2) = iv.bisect().expect("bisect");
        if to_r(&m2) != rmid || to_r(&l.hi()) != rmid || to_r(&r2.lo()) != rmid {
            bad!(n, "bisect wrong");
        }

        // --- select_int -----------------------------------------------------
        let si = obq_select_int(&x, &y);
        // reference: scan the integer range
        let m0: BigInt = rfloor(&rx) + 1;
        let m1: BigInt = rceil(&ry) - 1;
        let expect = if m0 > m1 {
            None
        } else if m0.is_positive() {
            Some(m0.clone())
        } else if m1.is_negative() {
            Some(m1.clone())
        } else {
            Some(BigInt::zero())
        };
        if si != expect {
            bad!(
                n,
                "select_int {:?} vs reference {:?} on ({}, {})",
                si,
                expect,
                rx,
                ry
            );
        }
        if let Some(v) = &si {
            let rv = BigRational::from_integer(v.clone());
            if !(rx < rv && rv < ry) {
                bad!(n, "select_int {} NOT strictly inside ({}, {})", v, rx, ry);
            }
        }

        // --- select_small: BOTH halves of the minimality certificate --------
        let ceiling = iv.width().k() + 1;
        match obq_select_small(&iv) {
            Some((v, kc)) => {
                if kc != ceiling {
                    bad!(n, "k_ceiling {} vs derived {}", kc, ceiling);
                }
                let rv = to_r(&v);
                if !(rx < rv && rv < ry) {
                    bad!(n, "select_small {} not strictly inside", rv);
                }
                // POSITIVE half against the brute-force scan
                let refsel = ref_select_small(&rx, &ry, ceiling);
                match refsel {
                    Some((rk, rm)) => {
                        if rk != v.k() {
                            bad!(
                                n,
                                "select_small k={} but reference minimal k={} on ({}, {})",
                                v.k(),
                                rk,
                                rx,
                                ry
                            );
                        }
                        let rrv = BigRational::new(rm.clone(), BigInt::one() << rk);
                        if rrv != rv {
                            bad!(n, "select_small value {} vs reference {}", rv, rrv);
                        }
                    }
                    None => bad!(
                        n,
                        "reference found NO interior dyadic but module returned {}",
                        rv
                    ),
                }
                // NEGATIVE half: nothing strictly inside at any smaller exponent
                for j in 0..v.k() {
                    if let Some(m) = ref_candidate_at(&rx, &ry, j) {
                        bad!(
                            n,
                            "NOT minimal: answered k={} but {}/2^{} is inside ({}, {})",
                            v.k(),
                            m,
                            j,
                            rx,
                            ry
                        );
                    }
                    if obq_candidate_at(&iv, j).is_some() {
                        bad!(
                            n,
                            "candidate_at({}) is Some but select_small chose k={}",
                            j,
                            v.k()
                        );
                    }
                }
                // candidate_at agrees with the reference at every probed level
                for j in 0..=(v.k() + 3).min(ceiling + 3) {
                    if obq_candidate_at(&iv, j) != ref_candidate_at(&rx, &ry, j) {
                        bad!(
                            n,
                            "candidate_at({}) {:?} vs reference {:?}",
                            j,
                            obq_candidate_at(&iv, j),
                            ref_candidate_at(&rx, &ry, j)
                        );
                    }
                }
            }
            None => bad!(
                n,
                "select_small declined on the non-empty interval ({}, {})",
                rx,
                ry
            ),
        }
    }

    // ---- polynomial sign / eval at a dyadic --------------------------------
    let deg = rng.below(5) as usize + 1;
    let poly: Vec<BigInt> = (0..=deg)
        .map(|_| BigInt::from(rng.range(-30, 30)))
        .collect();
    if let Some(s) = obq_poly_sign_at(&poly, &x) {
        if s != ref_poly_sign(&poly, &rx) {
            bad!(
                n,
                "poly_sign_at {} vs reference {} at {}",
                s,
                ref_poly_sign(&poly, &rx),
                rx
            );
        }
    }
    if let Some(v) = obq_poly_eval_at(&poly, &x) {
        if to_r(&v) != ref_poly_eval(&poly, &rx) {
            bad!(n, "poly_eval_at wrong at {}", rx);
        }
    }

    // ---- refine_step_bound -------------------------------------------------
    let wa = rng.range(1, 4096);
    let wk = rng.below(40) as u32;
    let ta = rng.range(-4, 4096);
    let tk = rng.below(40) as u32;
    let (wbq, tbq) = (
        OBq::new(BigInt::from(wa), wk),
        OBq::new(BigInt::from(ta), tk),
    );
    let (wr, tr) = (r_of(wa, wk), r_of(ta, tk));
    let got = obq_refine_step_bound(&wbq, &tbq);
    let want = ref_step_bound(&wr, &tr, 16_384);
    match (got, want) {
        (Some(g), Some(w)) => {
            // the module's bound is allowed to be >= the exact minimum (it is a
            // BOUND) but must never be BELOW it, or the loop cannot converge.
            if g < w {
                bad!(
                    n,
                    "step bound {} BELOW the exact minimum {} (w={} t={})",
                    g,
                    w,
                    wr,
                    tr
                );
            }
            if g > w + 2 {
                bad!(
                    n,
                    "step bound {} far above the exact minimum {} (w={} t={})",
                    g,
                    w,
                    wr,
                    tr
                );
            }
        }
        (None, Some(w)) => {
            if tr.is_positive() && w <= 16_384 {
                bad!(
                    n,
                    "step bound declined but exact minimum is {} (w={} t={})",
                    w,
                    wr,
                    tr
                );
            }
        }
        (Some(g), None) => {
            if !tr.is_positive() {
                bad!(n, "step bound {} on a non-positive target {}", g, tr);
            }
        }
        (None, None) => {}
    }

    // ---- refine_to_width on a REAL isolating interval -----------------------
    // x^2 - d for non-square d: the root is irrational, no midpoint can hit it.
    let d = [2i64, 3, 5, 6, 7, 10, 11, 13][rng.below(8) as usize];
    let p = vec![BigInt::from(-d), BigInt::zero(), BigInt::one()];
    let root = (d as f64).sqrt();
    let lo_i = root.floor() as i64;
    let start = OBqInterval::new(
        &OBq::new(BigInt::from(lo_i), 0),
        &OBq::new(BigInt::from(lo_i + 1), 0),
    )
    .expect("isolating interval");
    let tk2 = 1 + rng.below(30) as u32;
    let target = OBq::inv_two_pow(tk2);
    match obq_refine_to_width(&p, &start, &target) {
        Some((out, tr2)) => {
            if tr2.steps > tr2.bound {
                bad!(
                    n,
                    "steps {} EXCEEDS the derived bound {}",
                    tr2.steps,
                    tr2.bound
                );
            }
            match out {
                ORefined::Narrowed(iv) => {
                    let (a, b) = (to_r(&iv.lo()), to_r(&iv.hi()));
                    // the true root must still be bracketed
                    if ref_poly_sign(&p, &a) * ref_poly_sign(&p, &b) >= 0 {
                        bad!(
                            n,
                            "refined interval ({}, {}) no longer brackets a root of x^2-{}",
                            a,
                            b,
                            d
                        );
                    }
                    if &b - &a > to_r(&target) {
                        bad!(
                            n,
                            "refined width {} exceeds target {}",
                            &b - &a,
                            to_r(&target)
                        );
                    }
                    // exact width identity: width_end * 2^steps == width_start
                    let ws = BigRational::one();
                    let we = &b - &a;
                    if we * BigRational::from_integer(BigInt::one() << tr2.steps) != ws {
                        bad!(n, "width identity broken at steps={}", tr2.steps);
                    }
                    if iv.max_k() != tr2.end_max_k {
                        bad!(
                            n,
                            "end_max_k {} vs interval max_k {}",
                            tr2.end_max_k,
                            iv.max_k()
                        );
                    }
                    // k must grow by EXACTLY one per step, never double
                    if iv.max_k() as u64 > tr2.steps as u64 {
                        bad!(n, "k {} grew faster than steps {}", iv.max_k(), tr2.steps);
                    }
                }
                ORefined::Exact(v) => {
                    if ref_poly_sign(&p, &to_r(&v)) != 0 {
                        bad!(n, "Exact({}) is NOT a root of x^2-{}", to_r(&v), d);
                    }
                }
            }
        }
        None => bad!(
            n,
            "refine_to_width declined on a genuine isolating interval of x^2-{}",
            d
        ),
    }

    // ---- enclose_rational: must never NARROW -------------------------------
    let ln = rng.range(-300, 300);
    let ld = rng.range(1, 40);
    let hn = ln + rng.range(1, 200);
    let (rlo, rhi) = (
        BigRational::new(BigInt::from(ln), BigInt::from(ld)),
        BigRational::new(BigInt::from(hn), BigInt::from(ld)),
    );
    let ek = rng.below(30) as u32;
    match obq_enclose_rational(&rlo, &rhi, ek) {
        Some(iv) => {
            let (a, b) = (to_r(&iv.lo()), to_r(&iv.hi()));
            if a > rlo || b < rhi {
                bad!(
                    n,
                    "enclose_rational NARROWED: ({}, {}) does not contain ({}, {})",
                    a,
                    b,
                    rlo,
                    rhi
                );
            }
            // must land on the 2^-k grid
            if iv.lo().k() > ek || iv.hi().k() > ek {
                bad!(n, "enclose_rational produced k above the requested {}", ek);
            }
            if a != BigRational::new(ref_floor_at(&rlo, ek), BigInt::one() << ek) {
                bad!(n, "enclose_rational lo not floor-rounded");
            }
            if b != BigRational::new(ref_ceil_at(&rhi, ek), BigInt::one() << ek) {
                bad!(n, "enclose_rational hi not ceil-rounded");
            }
        }
        None => {
            if rlo < rhi {
                // only legitimate when the rounded endpoints collapse
                let a = BigRational::new(ref_floor_at(&rlo, ek), BigInt::one() << ek);
                let b = BigRational::new(ref_ceil_at(&rhi, ek), BigInt::one() << ek);
                if a < b {
                    bad!(
                        n,
                        "enclose_rational declined on ({}, {}) at k={}",
                        rlo,
                        rhi,
                        ek
                    );
                }
            }
        }
    }

    // ---- select_non_root: the answer must be inside AND not a root ---------
    let iv2 = OBqInterval::new(
        &OBq::new(BigInt::from(rng.range(-40, 40)), rng.below(8) as u32),
        &OBq::new(BigInt::from(rng.range(41, 200)), rng.below(8) as u32),
    );
    if let Some(iv2) = iv2 {
        if let Some(v) = obq_select_non_root(&poly, &iv2) {
            let rv = to_r(&v);
            if !iv2.contains_open(&v) {
                bad!(n, "select_non_root outside the interval");
            }
            if ref_poly_sign(&poly, &rv) == 0 {
                bad!(n, "select_non_root returned an actual ROOT {}", rv);
            }
        }
    }

    // ---- separation --------------------------------------------------------
    let q = vec![BigInt::from(-7), BigInt::zero(), BigInt::one()];
    let a_iv =
        OBqInterval::new(&OBq::new(BigInt::from(1), 0), &OBq::new(BigInt::from(2), 0)).unwrap();
    let b_iv =
        OBqInterval::new(&OBq::new(BigInt::from(2), 0), &OBq::new(BigInt::from(3), 0)).unwrap();
    let p2 = vec![BigInt::from(-2), BigInt::zero(), BigInt::one()];
    if let Some((sep, _ia, _ib, rounds)) = obq_refine_until_separated(&p2, &a_iv, &q, &b_iv, 40) {
        use ay_nra::oracle_api::OSeparation;
        match sep {
            OSeparation::Ordered(o) => {
                if o != Ordering::Less {
                    bad!(n, "sqrt(2) < sqrt(7) but separation said {:?}", o);
                }
            }
            OSeparation::Inconclusive => {
                if rounds < 40 {
                    bad!(n, "Inconclusive after only {} rounds", rounds);
                }
            }
        }
    }

    true
}

trait OddRef {
    fn is_odd_ref(&self) -> bool;
}
impl OddRef for BigInt {
    fn is_odd_ref(&self) -> bool {
        !(self % BigInt::from(2)).is_zero()
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args
        .iter()
        .position(|a| a == "--seed")
        .and_then(|i| args.get(i + 1))
        .and_then(|s| s.parse().ok())
        .unwrap_or(1);
    let cases: u64 = args
        .iter()
        .position(|a| a == "--cases")
        .and_then(|i| args.get(i + 1))
        .and_then(|s| s.parse().ok())
        .unwrap_or(2000);

    let mut rng = R(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1);
    let mut ok = 0u64;
    let mut bad = 0u64;
    for i in 0..cases {
        if one_case(i, &mut rng) {
            ok += 1;
        } else {
            bad += 1;
            if bad >= 10 {
                println!("... stopping after 10 divergences");
                break;
            }
        }
    }
    println!("av_ref: seed {seed}, {cases} cases -> {ok} agreed, {bad} DIVERGED");
    if bad > 0 {
        std::process::exit(1);
    }
}

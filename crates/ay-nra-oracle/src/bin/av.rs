// ADVERSARIAL VERIFICATION HARNESS for the `anum` lane.
//
// Written from scratch by the verifier; it shares NO code with
// `crates/ay-nra-oracle/src/anum.rs` (the lane's own checks) beyond the z3
// binding. Run it with:
//
//     cargo build --release -p ay-nra-oracle --bin av
//     ./target/release/av --only a|b|c|d|e [--cases N] [--seed S]
//
//   A  equality / liveness on analytic ground truth (11 spellings of sqrt(2),
//      conjugates, overlapping intervals, numbers 2^-258 apart, algebraic zero)
//   B  randomized comparison vs z3 AND vs an independent BigRational model
//   C  add / mul / sign / neg vs z3
//   D  the DERIVED separation bound vs z3's actual root gaps
//   E  growth: mixed-degree chains and the sign evaluation nlsat's inner loop
//      repeats
//
// Every call runs under a watchdog thread, so a hang is reported rather than
// wedging the run.
//
// Independent of `crates/ay-nra-oracle/src/anum.rs`. Three opinions per case:
//   1. AY's `anum` (the code under test)
//   2. z3's `Z3_algebraic_*` through the same dlopen binding
//   3. a SECOND AY implementation: `univariate`'s BigRational Euclidean Sturm
//      chain + `algebraic.rs`, reached through the facade. Different code, same
//      question.

#![allow(unsafe_code)] // Dedicated C-ABI boundary to libz3; sites carry local invariants.
#![allow(clippy::all, dead_code, unused_imports)]

use std::cmp::Ordering;
use std::sync::mpsc;
use std::time::{Duration, Instant};

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use ay_nra::oracle_api::{
    anum_binop_diag, anum_cauchy_bound, anum_max_separation_bits, anum_normalize_defining,
    anum_root_separation_exponent, anum_sturm_count_in, obq_enclose_rational, OAnumOpDiag, OBq,
    OBqInterval, ODyadicAnum, OPoly, ORoot,
};

#[path = "../z3.rs"]
mod z3;
use z3::{Ptr, Z3};

static FAILURES: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(0);
static CHECKS: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(0);

fn bad(name: &str, msg: String) {
    FAILURES.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    println!("FAIL  {name}: {msg}");
}
fn okc() {
    CHECKS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
}

fn ints(v: &[i64]) -> Vec<BigInt> {
    v.iter().map(|&c| BigInt::from(c)).collect()
}
fn rats(p: &[BigInt]) -> Vec<BigRational> {
    p.iter()
        .map(|c| BigRational::from_integer(c.clone()))
        .collect()
}
fn render(p: &[BigInt]) -> String {
    p.iter()
        .enumerate()
        .map(|(i, c)| format!("{c}x^{i}"))
        .collect::<Vec<_>>()
        .join("+")
}
fn iv(lo: i64, hi: i64) -> OBqInterval {
    OBqInterval::new(
        &OBq::from_int(BigInt::from(lo)),
        &OBq::from_int(BigInt::from(hi)),
    )
    .unwrap()
}
fn ivq(lo: &BigRational, hi: &BigRational, k: u32) -> Option<OBqInterval> {
    obq_enclose_rational(lo, hi, k)
}

// --------------------------------------------------------------------------
// Independent model: BigRational Sturm / gcd through `univariate` (a DIFFERENT
// implementation from `anum`'s fraction-free chain over Z).
// --------------------------------------------------------------------------

/// Compare the unique root of `p1` in `(l1,h1)` against the unique root of `p2`
/// in `(l2,h2)`, entirely over `BigRational`.
fn indep_cmp(
    p1: &[BigInt],
    l1: &BigRational,
    h1: &BigRational,
    p2: &[BigInt],
    l2: &BigRational,
    h2: &BigRational,
) -> Option<Ordering> {
    let f1 = OPoly::from_coeffs(rats(p1)).square_free_part()?;
    let f2 = OPoly::from_coeffs(rats(p2)).square_free_part()?;
    // Equality by gcd + Sturm count over Q, on the intersection.
    let g = f1.gcd(&f2);
    if g.degree().is_some_and(|d| d >= 1) {
        let lo = if l1 > l2 { l1.clone() } else { l2.clone() };
        let hi = if h1 < h2 { h1.clone() } else { h2.clone() };
        if lo < hi && g.sturm_count_in(&lo, &hi) >= 1 {
            return Some(Ordering::Equal);
        }
    }
    // Distinct: bisect both over Q until disjoint.
    let (mut a0, mut a1, mut b0, mut b1) = (l1.clone(), h1.clone(), l2.clone(), h2.clone());
    let two = BigRational::from_integer(BigInt::from(2));
    for _ in 0..4000 {
        if a1 <= b0 {
            return Some(Ordering::Less);
        }
        if b1 <= a0 {
            return Some(Ordering::Greater);
        }
        let am = (&a0 + &a1) / &two;
        let sm = crate::sign_q(&f1, &am);
        if sm == 0 {
            // exact root
            a0 = am.clone();
            a1 = am.clone();
        } else if sm == crate::sign_q(&f1, &a0) {
            a0 = am;
        } else {
            a1 = am;
        }
        let bm = (&b0 + &b1) / &two;
        let sn = crate::sign_q(&f2, &bm);
        if sn == 0 {
            b0 = bm.clone();
            b1 = bm.clone();
        } else if sn == crate::sign_q(&f2, &b0) {
            b0 = bm;
        } else {
            b1 = bm;
        }
        if a0 == a1 && b0 == b1 {
            return Some(a0.cmp(&b0));
        }
    }
    None
}

fn sign_q(f: &OPoly, x: &BigRational) -> i32 {
    let v = f.eval(x);
    if v.is_zero() {
        0
    } else if v.is_negative() {
        -1
    } else {
        1
    }
}

// --------------------------------------------------------------------------
// Watchdog: run `f` on a thread and report if it does not finish in `secs`.
// --------------------------------------------------------------------------
fn with_watchdog<T: Send + 'static>(
    name: &str,
    secs: u64,
    f: impl FnOnce() -> T + Send + 'static,
) -> Option<T> {
    let (tx, rx) = mpsc::channel();
    std::thread::spawn(move || {
        let _ = tx.send(f());
    });
    match rx.recv_timeout(Duration::from_secs(secs)) {
        Ok(v) => Some(v),
        Err(_) => {
            bad(name, format!("DID NOT RETURN within {secs}s — HANG"));
            None
        }
    }
}

// ==========================================================================
// SUITE A — equality and liveness, analytic ground truth
// ==========================================================================

fn suite_a() {
    println!("\n=== SUITE A: equality / liveness (analytic ground truth) ===");

    // sqrt(2) written six different ways. All must compare Equal to each other.
    let sqrt2_forms: Vec<(&str, Vec<BigInt>, OBqInterval)> = vec![
        ("x^2-2 on (1,2)", ints(&[-2, 0, 1]), iv(1, 2)),
        ("x^2-2 on (0,2)", ints(&[-2, 0, 1]), iv(0, 2)),
        ("x^2-2 on (1,100)", ints(&[-2, 0, 1]), iv(1, 100)),
        // (x^2-2)^2 — square-free reduction must recover x^2-2
        ("(x^2-2)^2 on (1,2)", ints(&[4, 0, -4, 0, 1]), iv(1, 2)),
        // x^4-4x^2+4 is the same polynomial written out
        ("x^4-4x^2+4 on (1,2)", ints(&[4, 0, -4, 0, 1]), iv(1, 2)),
        // (x^2-2)(x-5): a different, larger defining polynomial
        ("(x^2-2)(x-5) on (1,2)", ints(&[10, -2, -5, 1]), iv(1, 2)),
        // x^3 - 2x = x(x^2-2): shares the factor, has a root at 0 too
        ("x^3-2x on (1,2)", ints(&[0, -2, 0, 1]), iv(1, 2)),
        // (x^2-2)(x^2-3): sqrt(2) is the second of four roots
        (
            "(x^2-2)(x^2-3) on (1,3/2)",
            ints(&[6, 0, -5, 0, 1]),
            OBqInterval::new(&OBq::from_int(BigInt::one()), &OBq::new(BigInt::from(3), 1)).unwrap(),
        ),
        // 3*(x^2-2): content must be divided out
        ("3x^2-6 on (1,2)", ints(&[-6, 0, 3]), iv(1, 2)),
        // -(x^2-2): negative leading coefficient
        ("-x^2+2 on (1,2)", ints(&[2, 0, -1]), iv(1, 2)),
    ];
    let mut built: Vec<(&str, ODyadicAnum)> = Vec::new();
    for (label, p, i) in &sqrt2_forms {
        match ODyadicAnum::from_poly_interval(p, i) {
            Some(a) => built.push((label, a)),
            None => bad(
                "A/construct",
                format!("{label}: from_poly_interval REFUSED"),
            ),
        }
    }
    for i in 0..built.len() {
        for j in 0..built.len() {
            let (na, a) = (built[i].0, built[i].1.clone());
            let (nb, b) = (built[j].0, built[j].1.clone());
            let name = format!("A/eq[{na} vs {nb}]");
            let t = Instant::now();
            let r = with_watchdog(&name, 20, move || a.cmp_anum_traced(&b));
            let el = t.elapsed().as_millis();
            match r {
                Some(Some((Ordering::Equal, tr))) => {
                    okc();
                    if !tr.equal_by_certificate {
                        bad(
                            &name,
                            "Equal but NOT by certificate (would refine forever on a harder input)"
                                .into(),
                        );
                    }
                    if tr.steps_a != 0 || tr.steps_b != 0 {
                        bad(
                            &name,
                            format!("certificate path bisected {}/{}", tr.steps_a, tr.steps_b),
                        );
                    }
                    if el > 2000 {
                        bad(&name, format!("took {el} ms"));
                    }
                }
                Some(Some((o, _))) => bad(&name, format!("answered {o:?}, truth is Equal")),
                Some(None) => bad(&name, "DECLINED on two equal numbers".into()),
                None => {}
            }
        }
    }

    // sqrt(2) vs -sqrt(2): conjugates of the same polynomial, must be Greater.
    let pos = ODyadicAnum::from_poly_interval(&ints(&[-2, 0, 1]), &iv(1, 2)).unwrap();
    let neg = ODyadicAnum::from_poly_interval(&ints(&[-2, 0, 1]), &iv(-2, -1)).unwrap();
    check_cmp("A/conjugates", &pos, &neg, Ordering::Greater);
    check_cmp("A/conjugates-rev", &neg, &pos, Ordering::Less);

    // OVERLAPPING intervals, distinct numbers: sqrt(2) and sqrt(3) both in (1,2).
    let s2 = ODyadicAnum::from_poly_interval(&ints(&[-2, 0, 1]), &iv(1, 2)).unwrap();
    let s3 = ODyadicAnum::from_poly_interval(&ints(&[-3, 0, 1]), &iv(1, 2)).unwrap();
    check_cmp("A/overlap-distinct", &s2, &s3, Ordering::Less);

    // sqrt(2) vs -sqrt(2) through DIFFERENT polynomials that share the factor.
    let s2b = ODyadicAnum::from_poly_interval(&ints(&[10, -2, -5, 1]), &iv(1, 2)).unwrap();
    check_cmp("A/shared-factor-neg", &s2b, &neg, Ordering::Greater);

    // sqrt(2)*sqrt(2) == 2. The DEFERRED minimality case: the answer is an
    // AlgCell over z^2-4, not Rational(2). Comparison must still say Equal.
    let prod = with_watchdog("A/sqrt2sq", 30, {
        let a = s2.clone();
        let b = s2.clone();
        move || a.mul(&b)
    })
    .flatten();
    match prod {
        Some(p) => {
            okc();
            check_cmp_rat(
                "A/sqrt2*sqrt2==2",
                &p,
                &BigRational::from_integer(BigInt::from(2)),
                Ordering::Equal,
            );
            println!(
                "  note: sqrt2*sqrt2 -> is_rational={} degree={} poly={}",
                p.is_rational(),
                p.degree(),
                p.poly_coeffs().map_or("<rational>".into(), |c| render(&c))
            );
        }
        None => bad("A/sqrt2sq", "mul returned None".into()),
    }

    // EXTREMELY CLOSE BUT DISTINCT.
    // alpha = sqrt(2); beta = sqrt(2 + 1/n^2) = root of n^2 x^2 - (2n^2+1).
    for e in [10u32, 20, 30, 40, 60, 90, 128] {
        let n = BigInt::one() << e; // n = 2^e
        let n2 = &n * &n;
        let p2: Vec<BigInt> = vec![
            -(&n2 * BigInt::from(2) + BigInt::one()),
            BigInt::zero(),
            n2.clone(),
        ];
        let a = ODyadicAnum::from_poly_interval(&ints(&[-2, 0, 1]), &iv(1, 2)).unwrap();
        let Some(b) = ODyadicAnum::from_poly_interval(&p2, &iv(1, 2)) else {
            bad("A/close", format!("e={e}: construct failed"));
            continue;
        };
        // |beta - alpha| ~ 2^-(2e+2). Truth: alpha < beta.
        let name = format!("A/close-2^-{}", 2 * e + 2);
        let t = Instant::now();
        let r = with_watchdog(&name, 60, {
            let (a, b) = (a.clone(), b.clone());
            move || a.cmp_anum_traced(&b)
        });
        let el = t.elapsed().as_millis();
        match r {
            Some(Some((o, tr))) => {
                okc();
                if o != Ordering::Less {
                    bad(&name, format!("AY says {o:?}, truth is Less"));
                } else {
                    println!(
                        "  ok {name}: Less  sep_bits={:?} steps={}/{} bound={} {} ms",
                        tr.sep_bits, tr.steps_a, tr.steps_b, tr.bound, el
                    );
                }
            }
            Some(None) => bad(&name, "DECLINED".into()),
            None => {}
        }
    }

    // A number vs its own refinement at many depths (same value, different iv).
    for k in [1u32, 5, 20, 64, 200, 1000] {
        let name = format!("A/refine-eq-k{k}");
        let a = s2.clone();
        let r = with_watchdog(&name, 30, move || {
            a.refine(&OBq::inv_two_pow(k))
                .map(|rf| (a.cmp_anum_traced(&rf), rf.interval().map(|i| i.max_k())))
        });
        match r {
            Some(Some((Some((Ordering::Equal, tr)), mk))) => {
                okc();
                if !tr.equal_by_certificate {
                    bad(&name, "not by certificate".into());
                }
                let _ = mk;
            }
            Some(Some((Some((o, _)), _))) => bad(&name, format!("refinement changed value: {o:?}")),
            Some(Some((None, _))) => bad(&name, "cmp DECLINED against own refinement".into()),
            Some(None) => bad(&name, "refine returned None".into()),
            None => {}
        }
    }

    // Rational / integer / zero / negative corners.
    let zero = ODyadicAnum::rational(BigRational::zero());
    let one = ODyadicAnum::rational(BigRational::one());
    let negthird = ODyadicAnum::rational(BigRational::new(BigInt::from(-1), BigInt::from(3)));
    check_cmp("A/zero-vs-zero", &zero, &zero.clone(), Ordering::Equal);
    check_cmp("A/zero-vs-one", &zero, &one, Ordering::Less);
    check_cmp("A/neg-vs-zero", &negthird, &zero, Ordering::Less);
    // The number zero in ALGEBRAIC form: root of x^3-x in (-1/2, 1/2).
    if let Some(z_alg) = ODyadicAnum::from_poly_interval(
        &ints(&[0, -1, 0, 1]),
        &OBqInterval::new(&OBq::new(BigInt::from(-1), 1), &OBq::new(BigInt::one(), 1)).unwrap(),
    ) {
        check_cmp("A/alg-zero-vs-rat-zero", &z_alg, &zero, Ordering::Equal);
        check_cmp("A/alg-zero-vs-one", &z_alg, &one, Ordering::Less);
        // multiplying by it must give exactly zero
        match z_alg.mul(&s2) {
            Some(p) => {
                check_cmp_rat(
                    "A/alg-zero*sqrt2",
                    &p,
                    &BigRational::zero(),
                    Ordering::Equal,
                );
            }
            None => bad("A/alg-zero*sqrt2", "mul returned None".into()),
        }
    } else {
        bad("A/alg-zero", "could not build algebraic zero".into());
    }

    // An integer in algebraic form: root of x^2-4 in (1,3) is 2.
    if let Some(two_alg) = ODyadicAnum::from_poly_interval(&ints(&[-4, 0, 1]), &iv(1, 3)) {
        check_cmp_rat(
            "A/alg-two==2",
            &two_alg,
            &BigRational::from_integer(BigInt::from(2)),
            Ordering::Equal,
        );
        println!(
            "  note: root of x^2-4 in (1,3): is_rational={}",
            two_alg.is_rational()
        );
    }
}

fn check_cmp(name: &str, a: &ODyadicAnum, b: &ODyadicAnum, want: Ordering) {
    let (x, y) = (a.clone(), b.clone());
    let r = with_watchdog(name, 30, move || x.cmp_anum(&y));
    match r {
        Some(Some(o)) => {
            okc();
            if o != want {
                bad(name, format!("AY says {o:?}, truth is {want:?}"));
            }
        }
        Some(None) => bad(name, "DECLINED".into()),
        None => {}
    }
}

fn check_cmp_rat(name: &str, a: &ODyadicAnum, r: &BigRational, want: Ordering) {
    check_cmp(name, a, &ODyadicAnum::rational(r.clone()), want);
}

// ==========================================================================
// SUITE B — randomized differential against z3 AND the independent model
// ==========================================================================

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        // splitmix64
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    fn below(&mut self, n: u64) -> u64 {
        if n == 0 {
            0
        } else {
            self.next() % n
        }
    }
    fn range(&mut self, lo: i64, hi: i64) -> i64 {
        lo + (self.next() % ((hi - lo + 1) as u64)) as i64
    }
}

/// A wider generator than the oracle's: bigger degrees, bigger coefficients,
/// clustered roots, and intervals of every width from "widest isolating" to
/// `2^-60`.
fn gen_poly(rng: &mut Rng) -> (Vec<BigInt>, &'static str) {
    match rng.below(10) {
        0 => {
            // clustered: (x-a)(x-a-1/2^m)... via integer scaling
            let m = rng.below(20) as u32 + 1;
            let s = BigInt::one() << m;
            let a = BigInt::from(rng.range(-5, 5));
            // (s x - s a)(s x - s a - 1) = s^2 x^2 - ... roots a and a + 1/s
            let p0 = &(&s * &a) * (&(&s * &a) + BigInt::one());
            let p1 = -(&s * (&(&s * &a) * BigInt::from(2) + BigInt::one()));
            let p2 = &s * &s;
            (vec![p0, p1, p2], "clustered")
        }
        1 => {
            // Wilkinson-ish: product of (x - i)
            let n = rng.below(5) as i64 + 2;
            let mut p = vec![BigInt::one()];
            for i in 1..=n {
                let mut q = vec![BigInt::zero(); p.len() + 1];
                for (j, c) in p.iter().enumerate() {
                    q[j] += c * BigInt::from(-i);
                    q[j + 1] += c;
                }
                p = q;
            }
            (p, "wilkinson")
        }
        2 => {
            // high-degree sparse: x^d - k
            let d = rng.below(12) as usize + 2;
            let k = rng.range(2, 200);
            let mut c = vec![BigInt::zero(); d + 1];
            c[0] = BigInt::from(-k);
            c[d] = BigInt::one();
            (c, "x^d-k")
        }
        3 => {
            // huge coefficients
            let d = rng.below(4) as usize + 2;
            let mut c: Vec<BigInt> = (0..=d)
                .map(|_| {
                    BigInt::from(rng.range(-1_000_000_000, 1_000_000_000))
                        * (BigInt::one() << rng.below(64) as u32)
                })
                .collect();
            if c[d].is_zero() {
                c[d] = BigInt::one();
            }
            (c, "huge-coeffs")
        }
        4 => {
            // repeated factors (square-free reduction has real work)
            let r = rng.range(-4, 4);
            let d = rng.range(2, 13);
            let quad = ints(&[-d, 0, 1]);
            let lin = ints(&[-r, 1]);
            let sq = pmul(&quad, &quad);
            (pmul(&sq, &lin), "multiplicity")
        }
        5 => {
            // random dense of odd degree (guaranteed real root)
            let d = 2 * (rng.below(3) as usize) + 3;
            let mut c: Vec<BigInt> = (0..=d).map(|_| BigInt::from(rng.range(-30, 30))).collect();
            if c[d].is_zero() {
                c[d] = BigInt::one();
            }
            (c, "dense-odd")
        }
        6 => {
            // near-rational: n^2 x^2 - (k n^2 + 1)
            let e = rng.below(40) as u32 + 1;
            let n = BigInt::one() << e;
            let n2 = &n * &n;
            let k = rng.range(2, 20);
            (
                vec![-(&n2 * BigInt::from(k) + BigInt::one()), BigInt::zero(), n2],
                "near-rational",
            )
        }
        7 => {
            // pure rational roots, dyadic and not
            let k = rng.below(6) as u32 + 1;
            let a = rng.range(-40, 40);
            let b = rng.range(-9, 9);
            (pmul(&ints(&[-a, 1i64 << k]), &ints(&[-b, 3])), "rational")
        }
        8 => {
            // cubic with 3 real roots, asymmetric
            let a = rng.range(-6, 6);
            let b = rng.range(-6, 6);
            let c = rng.range(-6, 6);
            (
                pmul(&pmul(&ints(&[-a, 1]), &ints(&[-b, 1])), &ints(&[-c, 1])),
                "three-linear",
            )
        }
        _ => {
            // x^2 - d, the classic
            let d = rng.range(2, 60);
            (ints(&[-d, 0, 1]), "quadratic")
        }
    }
}

fn pmul(a: &[BigInt], b: &[BigInt]) -> Vec<BigInt> {
    if a.is_empty() || b.is_empty() {
        return Vec::new();
    }
    let mut out = vec![BigInt::zero(); a.len() + b.len() - 1];
    for (i, x) in a.iter().enumerate() {
        for (j, y) in b.iter().enumerate() {
            out[i + j] += x * y;
        }
    }
    out
}

/// Build an AY cell for z3's root `v` of `p`, at a randomly chosen interval
/// width (including the coarsest isolating one).
fn build_at(
    z3: &Z3,
    p: &[BigInt],
    v: Ptr,
    rng: &mut Rng,
) -> Option<(ODyadicAnum, BigRational, BigRational)> {
    let (lo, hi) = z3.bracket(v, 80)?;
    let eps = BigRational::new(BigInt::one(), BigInt::one() << 70u32);
    let (lo, hi) = if lo == hi {
        (&lo - &eps, &hi + &eps)
    } else {
        (lo, hi)
    };
    let mode = rng.below(3);
    if mode == 0 {
        // coarsest isolating
        for k in 0..=70u32 {
            if let Some(i) = ivq(&lo, &hi, k) {
                if let Some(a) = ODyadicAnum::from_poly_interval(p, &i) {
                    return Some((a, i.lo().to_rational(), i.hi().to_rational()));
                }
            }
        }
        None
    } else {
        let k = if mode == 1 {
            40
        } else {
            20 + rng.below(45) as u32
        };
        let i = ivq(&lo, &hi, k)?;
        let a = ODyadicAnum::from_poly_interval(p, &i)?;
        Some((a, i.lo().to_rational(), i.hi().to_rational()))
    }
}

fn suite_b(z3: &mut Z3, cases: u64, seed: u64) {
    println!("\n=== SUITE B: randomized differential, {cases} cases, seed {seed} ===");
    let mut rng = Rng(seed);
    let mut compared = 0u64;
    let mut declined = 0u64;
    let mut indep_agree = 0u64;
    let mut indep_ran = 0u64;
    let mut slowest = (0u128, String::new());
    for case in 0..cases {
        if case % 200 == 0 {
            z3.recycle();
        }
        let (pa, sa) = gen_poly(&mut rng);
        let (pb, sb) = gen_poly(&mut rng);
        let Some(ra) = z3.roots(&rats(&pa)) else {
            continue;
        };
        let Some(rb) = z3.roots(&rats(&pb)) else {
            continue;
        };
        if ra.is_empty() || rb.is_empty() {
            continue;
        }
        let va = ra[rng.below(ra.len() as u64) as usize];
        let vb = rb[rng.below(rb.len() as u64) as usize];
        let Some((a, al, ah)) = build_at(z3, &pa, va, &mut rng) else {
            continue;
        };
        let Some((b, bl, bh)) = build_at(z3, &pb, vb, &mut rng) else {
            continue;
        };
        if z3.errored() {
            continue;
        }
        let z3_ord = if z3.eq(va, vb) {
            Ordering::Equal
        } else if z3.lt(va, vb) {
            Ordering::Less
        } else if z3.gt(va, vb) {
            Ordering::Greater
        } else {
            continue;
        };
        let t = Instant::now();
        let got = {
            let (x, y) = (a.clone(), b.clone());
            with_watchdog(&format!("B/case{case}"), 90, move || x.cmp_anum_traced(&y))
        };
        let el = t.elapsed().as_micros();
        if el > slowest.0 {
            slowest = (el, format!("case {case} {sa}/{sb}"));
        }
        match got {
            Some(Some((o, tr))) => {
                compared += 1;
                okc();
                if o != z3_ord {
                    bad(
                        &format!("B/case{case}"),
                        format!(
                            "AY {o:?} z3 {z3_ord:?}\n      pa[{sa}]={} iv=({al},{ah})\n      pb[{sb}]={} iv=({bl},{bh})",
                            render(&pa),
                            render(&pb)
                        ),
                    );
                }
                if z3_ord == Ordering::Equal
                    && !a.is_rational()
                    && !b.is_rational()
                    && !tr.equal_by_certificate
                {
                    bad(
                        &format!("B/case{case}"),
                        "EQUAL not decided by certificate".into(),
                    );
                }
                if tr.equal_by_certificate && (tr.steps_a != 0 || tr.steps_b != 0) {
                    bad(&format!("B/case{case}"), "certificate path bisected".into());
                }
                if tr.steps_a > tr.bound || tr.steps_b > tr.bound {
                    bad(
                        &format!("B/case{case}"),
                        "steps exceeded derived bound".into(),
                    );
                }
                // Independent model, third opinion.
                if let Some(io) = indep_cmp(&pa, &al, &ah, &pb, &bl, &bh) {
                    indep_ran += 1;
                    if io == z3_ord {
                        indep_agree += 1;
                    } else {
                        bad(
                            &format!("B/case{case}/indep"),
                            format!("independent BigRational model says {io:?}, z3 says {z3_ord:?} — HARNESS BUG or z3 bracket wrong"),
                        );
                    }
                }
            }
            Some(None) => {
                declined += 1;
                bad(
                    &format!("B/case{case}"),
                    format!(
                        "cmp_anum DECLINED (documented total)\n      pa[{sa}]={} iv=({al},{ah})\n      pb[{sb}]={} iv=({bl},{bh})",
                        render(&pa),
                        render(&pb)
                    ),
                );
            }
            None => {}
        }
    }
    println!(
        "  compared {compared}, declined {declined}, independent model ran {indep_ran} agreed {indep_agree}"
    );
    println!("  slowest single cmp: {} us ({})", slowest.0, slowest.1);
}

// ==========================================================================
// SUITE C — arithmetic and sign, randomized against z3
// ==========================================================================

fn suite_c(z3: &mut Z3, cases: u64, seed: u64) {
    println!("\n=== SUITE C: arith / sign / neg differential, {cases} cases, seed {seed} ===");
    let mut rng = Rng(seed);
    let mut n_ok = 0u64;
    let mut n_dec = 0u64;
    for case in 0..cases {
        if case % 200 == 0 {
            z3.recycle();
        }
        let (pa, sa) = gen_poly(&mut rng);
        let (pb, sb) = gen_poly(&mut rng);
        let Some(ra) = z3.roots(&rats(&pa)) else {
            continue;
        };
        let Some(rb) = z3.roots(&rats(&pb)) else {
            continue;
        };
        if ra.is_empty() || rb.is_empty() {
            continue;
        }
        let va = ra[rng.below(ra.len() as u64) as usize];
        let vb = rb[rng.below(rb.len() as u64) as usize];
        let Some((a, _, _)) = build_at(z3, &pa, va, &mut rng) else {
            continue;
        };
        let Some((b, _, _)) = build_at(z3, &pb, vb, &mut rng) else {
            continue;
        };
        if z3.errored() {
            continue;
        }
        for is_add in [true, false] {
            let diag = anum_binop_diag(&a, &b, is_add);
            let must = !matches!(diag, OAnumOpDiag::OverCeiling | OAnumOpDiag::Degenerate);
            let label = if is_add { "add" } else { "mul" };
            let name = format!("C/case{case}/{label}");
            let got = {
                let (x, y) = (a.clone(), b.clone());
                with_watchdog(
                    &name,
                    120,
                    move || if is_add { x.add(&y) } else { x.mul(&y) },
                )
            };
            let Some(got) = got else { continue };
            let Some(r) = got else {
                if must {
                    n_dec += 1;
                    bad(
                        &name,
                        format!("DECLINED though diag says {diag:?}\n      pa[{sa}]={}\n      pb[{sb}]={}", render(&pa), render(&pb)),
                    );
                }
                continue;
            };
            // Convert AY's answer to a z3 AST by root selection, then compare.
            let zref = if is_add {
                z3.add(va, vb)
            } else {
                z3.mul(va, vb)
            };
            if z3.errored() {
                continue;
            }
            match z3_of(z3, &r) {
                Ok(ast) => {
                    n_ok += 1;
                    okc();
                    if !z3.eq(ast, zref) {
                        bad(
                            &name,
                            format!(
                                "AY != z3\n      pa[{sa}]={}\n      pb[{sb}]={}\n      AY poly={}",
                                render(&pa),
                                render(&pb),
                                r.poly_coeffs().map_or("<rat>".into(), |c| render(&c))
                            ),
                        );
                    }
                }
                Err(false) => bad(
                    &name,
                    format!("AY result interval does not bracket exactly ONE root of AY's own polynomial\n      pa[{sa}]={}\n      pb[{sb}]={}", render(&pa), render(&pb)),
                ),
                Err(true) => {}
            }
        }
        // sign_of_poly against z3's eval, including the deliberate zero case.
        for (lbl, q) in [
            ("q=pa", pa.clone()),
            ("q=pa*pb", pmul(&pa, &pb)),
            ("q=pb", pb.clone()),
        ] {
            if q.is_empty() {
                continue;
            }
            let name = format!("C/case{case}/sign/{lbl}");
            let Some(s) = ({
                let x = a.clone();
                let qq = q.clone();
                with_watchdog(&name, 60, move || x.sign_of_poly(&qq))
            }) else {
                continue;
            };
            let Some(s) = s else {
                bad(&name, "sign_of_poly DECLINED".into());
                continue;
            };
            let Some(zs) = z3.eval_sign(&rats(&q), va) else {
                continue;
            };
            okc();
            if s != zs {
                bad(
                    &name,
                    format!("AY sign {s}, z3 sign {zs}, q={}", render(&q)),
                );
            }
        }
        // neg
        let name = format!("C/case{case}/neg");
        if let Some(Some(na)) = ({
            let x = a.clone();
            with_watchdog(&name, 60, move || x.neg())
        }) {
            if let Ok(ast) = z3_of(z3, &na) {
                okc();
                let zero = z3.rational(&BigRational::zero());
                if !z3.eq(z3.add(ast, va), zero) {
                    bad(&name, format!("a + (-a) != 0, pa[{sa}]={}", render(&pa)));
                }
            }
        }
    }
    println!("  arith compared {n_ok}, unexpected declines {n_dec}");
}

fn z3_of(z3: &Z3, a: &ODyadicAnum) -> Result<Ptr, bool> {
    if let Some(r) = a.to_rational() {
        return Ok(z3.rational(&r));
    }
    let coeffs = rats(&a.poly_coeffs().ok_or(false)?);
    let roots = z3.roots(&coeffs).ok_or(true)?;
    let i = a.interval().ok_or(false)?;
    let lo = z3.rational(&i.lo().to_rational());
    let hi = z3.rational(&i.hi().to_rational());
    let mut found: Option<Ptr> = None;
    for r in roots {
        if z3.gt(r, lo) && z3.lt(r, hi) {
            if found.is_some() {
                return Err(false);
            }
            found = Some(r);
        }
    }
    if z3.errored() {
        return Err(true);
    }
    found.ok_or(false)
}

// ==========================================================================
// SUITE D — the separation bound as a pure function, against z3's real roots
// ==========================================================================

fn suite_d(z3: &mut Z3, cases: u64, seed: u64) {
    println!("\n=== SUITE D: separation bound vs z3's ACTUAL minimum root gap ===");
    let mut rng = Rng(seed);
    let mut worst_slack = f64::INFINITY;
    let mut worst = String::new();
    let mut n = 0u64;
    for case in 0..cases {
        if case % 200 == 0 {
            z3.recycle();
        }
        let (p, s) = gen_poly(&mut rng);
        let Some(norm) = anum_normalize_defining(&p) else {
            continue;
        };
        let Some(b) = anum_root_separation_exponent(&norm) else {
            continue;
        };
        let Some(roots) = z3.roots(&rats(&norm)) else {
            continue;
        };
        if roots.len() < 2 {
            continue;
        }
        let mut br = Vec::new();
        let mut okall = true;
        for v in &roots {
            match z3.bracket(*v, 120) {
                Some(x) => br.push(x),
                None => {
                    okall = false;
                    break;
                }
            }
        }
        if !okall {
            continue;
        }
        let limit = BigRational::new(BigInt::one(), BigInt::one() << b.min(4000));
        for w in br.windows(2) {
            let gap = &w[1].0 - &w[0].1;
            if gap <= BigRational::zero() {
                continue;
            }
            n += 1;
            okc();
            if gap <= limit {
                bad(
                    &format!("D/case{case}"),
                    format!("claimed sep 2^-{b} but actual gap is {gap} — BOUND IS NOT A BOUND, p[{s}]={}", render(&norm)),
                );
            }
            // How much slack? log2(gap) + b, in bits.
            let lg = log2_rat(&gap);
            let slack = lg + f64::from(b);
            if slack < worst_slack {
                worst_slack = slack;
                worst = format!("p[{s}]={} B={b} log2(gap)={lg:.1}", render(&norm));
            }
        }
    }
    println!("  {n} consecutive-root gaps checked");
    println!("  TIGHTEST case: slack = {worst_slack:.1} bits  ({worst})");
    println!("  (slack = log2(actual gap) + B; 0 would mean the bound is exactly tight)");
}

fn log2_rat(r: &BigRational) -> f64 {
    let nb = r.numer().bits() as i64;
    let db = r.denom().bits() as i64;
    (nb - db) as f64
}

// ==========================================================================

// ==========================================================================
// SUITE E — MY OWN adversarial chains: MIXED degrees, plus the operation
// nlsat's inner loop actually performs (sign evaluation at a sample point).
// ==========================================================================

fn root_of(d: usize, k: i64) -> Option<ODyadicAnum> {
    let mut c = vec![BigInt::zero(); d + 1];
    c[0] = BigInt::from(-k);
    c[d] = BigInt::one();
    // (1, k+1) always contains the unique positive real root of x^d - k for k>1.
    ODyadicAnum::from_poly_interval(&c, &iv(1, k + 1))
}

fn suite_e() {
    println!("\n=== SUITE E: mixed-degree chains + nlsat-shaped sign evaluation ===");
    println!("(load: {})", load_avg());

    // E1 — nested quadratic irrationals: sqrt(2)+sqrt(3)+sqrt(5)+... Degrees
    // double every step, which is the cheapest possible growth, so this is the
    // most favourable chain that exists. It is also exactly the shape a CAD
    // sample point takes.
    println!("\n E1: sqrt(p_1) + sqrt(p_2) + ... (degree DOUBLES per step)");
    println!("  step  operand      degree  coeffbits  interval k     step us   outcome");
    let primes = [2i64, 3, 5, 7, 11, 13, 17, 19, 23];
    let mut acc = root_of(2, primes[0]).unwrap();
    for (i, p) in primes.iter().enumerate().skip(1) {
        let Some(next) = root_of(2, *p) else { break };
        let t = Instant::now();
        let out = {
            let (x, y) = (acc.clone(), next.clone());
            with_watchdog(&format!("E1/step{i}"), 600, move || x.add(&y))
        };
        let us = t.elapsed().as_micros();
        match out.flatten() {
            Some(v) => {
                println!(
                    "  {:>4}  sqrt({:<3})  {:>8}  {:>9}  {:>10}  {:>10}   ok",
                    i,
                    p,
                    v.degree(),
                    v.poly_coeffs()
                        .map_or(0, |c| c.iter().map(|x| x.bits()).max().unwrap_or(0)),
                    v.interval().map_or(0, |x| x.max_k()),
                    us
                );
                acc = v;
            }
            None => {
                println!(
                    "  {:>4}  sqrt({:<3})  {:>8}  {:>9}  {:>10}  {:>10}   DECLINED",
                    i, p, "-", "-", "-", us
                );
                break;
            }
        }
    }

    // E2 — MIXED degrees, the realistic nlsat shape: a low-degree sample point
    // combined with the coefficients of a projection polynomial.
    println!("\n E2: mixed-degree chain, acc(deg 2) op root(deg 3,5,7,...)");
    println!("  step  op  operand deg   result deg   coeffbits     step us   outcome");
    let mut acc = root_of(2, 2).unwrap();
    for (i, d) in [3usize, 5, 7, 11, 13].iter().enumerate() {
        let Some(next) = root_of(*d, primes[(i + 1) % primes.len()]) else {
            break;
        };
        let is_add = i % 2 == 0;
        let t = Instant::now();
        let out = {
            let (x, y) = (acc.clone(), next.clone());
            with_watchdog(&format!("E2/step{i}"), 600, move || {
                if is_add {
                    x.add(&y)
                } else {
                    x.mul(&y)
                }
            })
        };
        let us = t.elapsed().as_micros();
        match out.flatten() {
            Some(v) => {
                println!(
                    "  {:>4}   {}  {:>11}  {:>11}  {:>9}  {:>10}   ok",
                    i,
                    if is_add { "+" } else { "*" },
                    d,
                    v.degree(),
                    v.poly_coeffs()
                        .map_or(0, |c| c.iter().map(|x| x.bits()).max().unwrap_or(0)),
                    us
                );
                acc = v;
            }
            None => {
                println!(
                    "  {:>4}   {}  {:>11}  {:>11}  {:>9}  {:>10}   DECLINED",
                    i,
                    if is_add { "+" } else { "*" },
                    d,
                    "-",
                    "-",
                    us
                );
                break;
            }
        }
    }

    // E3 — THE OPERATION NLSAT ACTUALLY REPEATS: the exact sign of a
    // projection polynomial at an algebraic sample point. Measured at each
    // degree a chain can produce.
    println!("\n E3: sign_of_poly at a degree-d sample point (nlsat's inner loop)");
    println!("  sample degree   probe degree      sign us   cmp-vs-rational us");
    for d in [2usize, 4, 8, 16, 32, 64] {
        // A sample point of degree d: root of x^d - 2 in (1,2).
        let Some(a) = root_of(d, 2) else { continue };
        // A probe of modest degree, as a projection polynomial would be.
        let probe: Vec<BigInt> = ints(&[-3, 1, 0, 2, 1]);
        let t = Instant::now();
        let s = {
            let (x, q) = (a.clone(), probe.clone());
            with_watchdog(&format!("E3/{d}"), 600, move || x.sign_of_poly(&q))
        };
        let sign_us = t.elapsed().as_micros();
        let t2 = Instant::now();
        let _ = {
            let x = a.clone();
            with_watchdog(&format!("E3c/{d}"), 600, move || {
                x.cmp_anum(&ODyadicAnum::rational(BigRational::new(
                    BigInt::from(7),
                    BigInt::from(5),
                )))
            })
        };
        let cmp_us = t2.elapsed().as_micros();
        println!(
            "  {:>13}   {:>12}   {:>10}   {:>18}  (sign={:?})",
            d,
            4,
            sign_us,
            cmp_us,
            s.flatten()
        );
    }
    println!("(load after: {})", load_avg());
}

fn load_avg() -> String {
    std::process::Command::new("uptime")
        .output()
        .ok()
        .and_then(|o| String::from_utf8(o.stdout).ok())
        .and_then(|s| {
            s.split("load averages:")
                .nth(1)
                .map(|x| x.trim().to_string())
        })
        .unwrap_or_default()
}

/// Resolve the reference libz3 when `--z3` is absent: `AY_NRA_ORACLE_Z3` wins,
/// else `$HOME/ay/reference/z3/5.0.0/bin/libz3.dylib`.
///
/// This was an absolute path with a username baked into it, which made the
/// default dead on every machine but one — including this one — and leaked a
/// personal home directory into the public snapshot.
fn default_z3() -> String {
    match std::env::var("AY_NRA_ORACLE_Z3") {
        Ok(path) if !path.is_empty() => path,
        _ => format!(
            "{}/ay/reference/z3/5.0.0/bin/libz3.dylib",
            std::env::var("HOME").unwrap_or_default()
        ),
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let path = std::path::PathBuf::from(
        args.iter()
            .position(|a| a == "--z3")
            .and_then(|i| args.get(i + 1))
            .cloned()
            .unwrap_or_else(default_z3),
    );
    let cases: u64 = args
        .iter()
        .position(|a| a == "--cases")
        .and_then(|i| args.get(i + 1))
        .and_then(|s| s.parse().ok())
        .unwrap_or(600);
    let seed: u64 = args
        .iter()
        .position(|a| a == "--seed")
        .and_then(|i| args.get(i + 1))
        .and_then(|s| s.parse().ok())
        .unwrap_or(12345);
    let only = args
        .iter()
        .position(|a| a == "--only")
        .and_then(|i| args.get(i + 1))
        .cloned()
        .unwrap_or_default();

    if only == "e" {
        suite_e();
        report();
        return;
    }
    suite_a();

    let mut z3 = match Z3::open(&path) {
        Ok(z) => z,
        Err(e) => {
            println!("z3 unavailable: {e}");
            report();
            return;
        }
    };
    if only.is_empty() || only == "b" {
        suite_b(&mut z3, cases, seed);
    }
    if only.is_empty() || only == "c" {
        suite_c(&mut z3, cases, seed ^ 0x5555);
    }
    if only.is_empty() || only == "d" {
        suite_d(&mut z3, cases * 2, seed ^ 0xAAAA);
    }
    report();
}

fn report() {
    let checks = CHECKS.load(std::sync::atomic::Ordering::Relaxed);
    let failures = FAILURES.load(std::sync::atomic::Ordering::Relaxed);
    println!("\n==== AV SUMMARY: {checks} checks, {failures} FAILURES ====");
    if failures > 0 {
        std::process::exit(1);
    }
}

//! ADVERSARIAL VERIFICATION of the `anum` separation-ladder change.
//!
//! Independent of the shipped oracle: builds close-but-distinct algebraic
//! pairs, an independent exact Sturm/bisection model written here from
//! scratch, and cross-checks every verdict against z3 driven over SMT-LIB
//! text (a different path from the oracle's libz3 FFI).
#![cfg(feature = "oracle-api")]
#![allow(clippy::all)]

use ay_nra::oracle_api::{OBq, OBqInterval, ODyadicAnum};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use std::cmp::Ordering;
use std::io::Write;
use std::process::{Command, Stdio};

// ===========================================================================
// An INDEPENDENT exact model over Q. Nothing here calls into ay.
// ===========================================================================

#[derive(Clone, Debug, PartialEq)]
struct QP(Vec<BigRational>); // low -> high, trailing zeros trimmed

fn q(i: i64) -> BigRational {
    BigRational::from_integer(BigInt::from(i))
}

impl QP {
    fn from_ints(c: &[BigInt]) -> Self {
        Self::new(
            c.iter()
                .map(|v| BigRational::from_integer(v.clone()))
                .collect(),
        )
    }
    fn new(mut c: Vec<BigRational>) -> Self {
        while c.len() > 0 && c.last().unwrap().is_zero() {
            c.pop();
        }
        QP(c)
    }
    fn deg(&self) -> Option<usize> {
        if self.0.is_empty() {
            None
        } else {
            Some(self.0.len() - 1)
        }
    }
    fn is_zero(&self) -> bool {
        self.0.is_empty()
    }
    fn eval(&self, x: &BigRational) -> BigRational {
        let mut acc = BigRational::zero();
        for c in self.0.iter().rev() {
            acc = acc * x + c;
        }
        acc
    }
    fn sign_at(&self, x: &BigRational) -> i32 {
        let v = self.eval(x);
        if v.is_zero() {
            0
        } else if v.is_negative() {
            -1
        } else {
            1
        }
    }
    fn deriv(&self) -> Self {
        if self.0.len() < 2 {
            return QP(vec![]);
        }
        QP::new(
            self.0
                .iter()
                .enumerate()
                .skip(1)
                .map(|(i, c)| c * BigRational::from_integer(BigInt::from(i)))
                .collect(),
        )
    }
    fn mul(&self, o: &Self) -> Self {
        if self.is_zero() || o.is_zero() {
            return QP(vec![]);
        }
        let mut r = vec![BigRational::zero(); self.0.len() + o.0.len() - 1];
        for (i, a) in self.0.iter().enumerate() {
            for (j, b) in o.0.iter().enumerate() {
                r[i + j] = &r[i + j] + a * b;
            }
        }
        QP::new(r)
    }
    fn neg(&self) -> Self {
        QP::new(self.0.iter().map(|c| -c).collect())
    }
    fn sub(&self, o: &Self) -> Self {
        let n = self.0.len().max(o.0.len());
        let mut r = vec![BigRational::zero(); n];
        for i in 0..n {
            let a = self.0.get(i).cloned().unwrap_or_else(BigRational::zero);
            let b = o.0.get(i).cloned().unwrap_or_else(BigRational::zero);
            r[i] = a - b;
        }
        QP::new(r)
    }
    fn scale(&self, s: &BigRational) -> Self {
        QP::new(self.0.iter().map(|c| c * s).collect())
    }
    fn shift(&self, k: usize) -> Self {
        let mut r = vec![BigRational::zero(); k];
        r.extend(self.0.iter().cloned());
        QP::new(r)
    }
    /// Euclidean remainder over Q.
    fn rem(&self, o: &Self) -> Self {
        let dq = o.deg().expect("div by zero poly");
        let lc = o.0[dq].clone();
        let mut r = self.clone();
        loop {
            let Some(dr) = r.deg() else { return r };
            if dr < dq {
                return r;
            }
            let f = &r.0[dr] / &lc;
            r = r.sub(&o.scale(&f).shift(dr - dq));
            // guard against non-termination from a bug
            assert!(
                r.deg().is_none_or(|degree| degree < dr),
                "rem did not reduce degree"
            );
        }
    }
    fn gcd(&self, o: &Self) -> Self {
        let mut a = self.clone();
        let mut b = o.clone();
        while !b.is_zero() {
            let r = a.rem(&b);
            a = b;
            b = r;
        }
        if let Some(d) = a.deg() {
            let lc = a.0[d].clone();
            a = a.scale(&(BigRational::one() / lc));
        }
        a
    }
    fn square_free(&self) -> Self {
        let g = self.gcd(&self.deriv());
        if g.deg() == Some(0) || g.is_zero() {
            let d = self.deg().unwrap();
            let lc = self.0[d].clone();
            return self.scale(&(BigRational::one() / lc));
        }
        // exact division self/g
        let mut rem = self.clone();
        let dq = g.deg().unwrap();
        let lc = g.0[dq].clone();
        let mut quo = vec![BigRational::zero(); self.deg().unwrap() - dq + 1];
        loop {
            let Some(dr) = rem.deg() else { break };
            if dr < dq {
                break;
            }
            let f = &rem.0[dr] / &lc;
            quo[dr - dq] = f.clone();
            rem = rem.sub(&g.scale(&f).shift(dr - dq));
        }
        let r = QP::new(quo);
        let d = r.deg().unwrap();
        let lc = r.0[d].clone();
        r.scale(&(BigRational::one() / lc))
    }
    /// Sturm chain over Q (square-free input).
    fn sturm(&self) -> Vec<QP> {
        let mut ch = vec![self.clone(), self.deriv()];
        loop {
            let n = ch.len();
            if ch[n - 1].is_zero() || ch[n - 1].deg() == Some(0) {
                break;
            }
            let r = ch[n - 2].rem(&ch[n - 1]).neg();
            if r.is_zero() {
                break;
            }
            ch.push(r);
        }
        ch
    }
    /// Cauchy root bound as an integer.
    fn cauchy(&self) -> BigInt {
        let d = self.deg().unwrap();
        let lc = self.0[d].clone().abs();
        let mut m = BigRational::zero();
        for c in &self.0 {
            let a = c.clone().abs();
            if a > m {
                m = a;
            }
        }
        let v = m / lc + BigRational::one();
        v.ceil().to_integer() + BigInt::one()
    }
}

fn sturm_changes(ch: &[QP], x: &BigRational) -> usize {
    let mut last = 0i32;
    let mut n = 0usize;
    for p in ch {
        let s = p.sign_at(x);
        if s == 0 {
            continue;
        }
        if last != 0 && s != last {
            n += 1;
        }
        last = s;
    }
    n
}

/// Roots of `ch[0]` strictly inside `(a, b)`; `None` if an endpoint is a root.
fn sturm_count(ch: &[QP], a: &BigRational, b: &BigRational) -> Option<usize> {
    if ch[0].sign_at(a) == 0 || ch[0].sign_at(b) == 0 {
        return None;
    }
    Some(sturm_changes(ch, a) - sturm_changes(ch, b))
}

// ---------------------------------------------------------------------------
// Independent isolation on the dyadic grid
// ---------------------------------------------------------------------------

fn dy(a: &BigInt, k: u32) -> BigRational {
    BigRational::new(a.clone(), BigInt::one() << k)
}

/// All isolating OPEN dyadic intervals (a/2^k, b/2^k) for the square-free `p`,
/// found by refining the dyadic grid until every root is alone.
/// Returns (numerator_lo, numerator_hi, k) ascending.
fn isolate(p: &QP) -> Vec<(BigInt, BigInt, u32)> {
    let sf = p.square_free();
    let ch = sf.sturm();
    let m = sf.cauchy();
    let total = sturm_count(
        &ch,
        &BigRational::from_integer(-m.clone()),
        &BigRational::from_integer(m.clone()),
    )
    .expect("cauchy endpoints are not roots");
    let mut k: u32 = 0;
    loop {
        let scale = BigInt::one() << k;
        let lo0 = -(&m * &scale);
        let hi0 = &m * &scale;
        let mut out: Vec<(BigInt, BigInt, u32)> = Vec::new();
        let mut ok = true;
        let mut cur = lo0.clone();
        // walk cells [cur, cur+1) on the 2^-k grid; only feasible for small k,
        // so instead do a recursive split.
        let _ = &mut cur;
        fn rec(
            ch: &[QP],
            lo: BigInt,
            hi: BigInt,
            k: u32,
            depth: u32,
            out: &mut Vec<(BigInt, BigInt, u32)>,
            ok: &mut bool,
        ) {
            let a = dy(&lo, k);
            let b = dy(&hi, k);
            let Some(c) = sturm_count(ch, &a, &b) else {
                *ok = false;
                return;
            };
            if c == 0 {
                return;
            }
            if c == 1 {
                out.push((lo, hi, k));
                return;
            }
            if depth == 0 {
                *ok = false;
                return;
            }
            // split at midpoint on a finer grid
            let lo2: BigInt = &lo * BigInt::from(2);
            let hi2: BigInt = &hi * BigInt::from(2);
            let mid: BigInt = (&lo2 + &hi2) / BigInt::from(2);
            rec(ch, lo2.clone(), mid.clone(), k + 1, depth - 1, out, ok);
            rec(ch, mid, hi2, k + 1, depth - 1, out, ok);
        }
        rec(&ch, lo0, hi0, k, 400, &mut out, &mut ok);
        if ok && out.len() == total {
            out.sort_by(|x, y| dy(&x.0, x.2).cmp(&dy(&y.0, y.2)));
            return out;
        }
        k += 1;
        assert!(k <= 8, "isolation failed");
    }
}

// ---------------------------------------------------------------------------
// The INDEPENDENT verdict for two isolated algebraic numbers
// ---------------------------------------------------------------------------

#[derive(Clone, Debug)]
struct Num {
    p: Vec<BigInt>, // defining poly (may be non-square-free)
    lo: (BigInt, u32),
    hi: (BigInt, u32),
}

impl Num {
    fn qp(&self) -> QP {
        QP::from_ints(&self.p).square_free()
    }
    fn lo_q(&self) -> BigRational {
        dy(&self.lo.0, self.lo.1)
    }
    fn hi_q(&self) -> BigRational {
        dy(&self.hi.0, self.hi.1)
    }
    fn to_ay(&self) -> Option<ODyadicAnum> {
        let iv = OBqInterval::new(
            &OBq::new(self.lo.0.clone(), self.lo.1),
            &OBq::new(self.hi.0.clone(), self.hi.1),
        )?;
        ODyadicAnum::from_poly_interval(&self.p, &iv)
    }
}

/// The independent model's order. Panics rather than guessing.
fn model_cmp(a: &Num, b: &Num) -> Ordering {
    let pa = a.qp();
    let pb = b.qp();
    let g = pa.gcd(&pb);
    if g.deg().map_or(false, |d| d >= 1) {
        let lo = a.lo_q().max(b.lo_q());
        let hi = a.hi_q().min(b.hi_q());
        if lo < hi {
            let gch = g.sturm();
            if let Some(c) = sturm_count(&gch, &lo, &hi) {
                if c >= 1 {
                    return Ordering::Equal;
                }
            }
        }
    }
    // distinct: bisect both, independently, until disjoint
    let (mut al, mut ah) = (a.lo_q(), a.hi_q());
    let (mut bl, mut bh) = (b.lo_q(), b.hi_q());
    let cha = pa.sturm();
    let chb = pb.sturm();
    let two = q(2);
    for _ in 0..9000 {
        if ah <= bl {
            return Ordering::Less;
        }
        if bh <= al {
            return Ordering::Greater;
        }
        let m = (&al + &ah) / &two;
        if pa.sign_at(&m) == 0 {
            al = m.clone();
            ah = m;
        } else if sturm_count(&cha, &al, &m).map_or(false, |c| c >= 1) {
            ah = m;
        } else {
            al = m;
        }
        let m = (&bl + &bh) / &two;
        if pb.sign_at(&m) == 0 {
            bl = m.clone();
            bh = m;
        } else if sturm_count(&chb, &bl, &m).map_or(false, |c| c >= 1) {
            bh = m;
        } else {
            bl = m;
        }
        if al == ah && bl == bh {
            return al.cmp(&bl);
        }
    }
    panic!("model_cmp failed to separate");
}

// ===========================================================================
// z3, over SMT-LIB text (independent of the oracle's FFI path)
// ===========================================================================

fn smt_int(v: &BigInt) -> String {
    // QF_NRA has no `to_real`: real literals must be written with a decimal.
    if v.is_negative() {
        format!("(- {}.0)", -v)
    } else {
        format!("{v}.0")
    }
}

fn smt_rat(r: &BigRational) -> String {
    let n = r.numer();
    let d = r.denom();
    if d.is_one() {
        smt_int(n)
    } else {
        format!("(/ {} {})", smt_int(n), smt_int(d))
    }
}

/// Horner form of the integer polynomial `p` in variable `v`.
fn smt_poly(p: &[BigInt], v: &str) -> String {
    let mut d = p.len();
    while d > 0 && p[d - 1].is_zero() {
        d -= 1;
    }
    if d == 0 {
        return "0.0".to_string();
    }
    let mut acc = smt_int(&p[d - 1]);
    for i in (0..d - 1).rev() {
        acc = format!("(+ (* {v} {acc}) {})", smt_int(&p[i]));
    }
    acc
}

fn z3_sat(script: &str) -> Option<bool> {
    let mut c = Command::new("z3")
        .arg("-in")
        .arg("-T:60")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .ok()?;
    c.stdin.as_mut()?.write_all(script.as_bytes()).ok()?;
    let out = c.wait_with_output().ok()?;
    let s = String::from_utf8_lossy(&out.stdout);
    let t = s.trim();
    if t.starts_with("unsat") {
        Some(false)
    } else if t.starts_with("sat") {
        Some(true)
    } else {
        None
    }
}

fn decl(name: &str, n: &Num) -> String {
    format!(
        "(declare-fun {name} () Real)\n(assert (= 0.0 {}))\n(assert (< {} {name}))\n(assert (< {name} {}))\n",
        smt_poly(&n.p, name),
        smt_rat(&n.lo_q()),
        smt_rat(&n.hi_q()),
    )
}

/// z3's order for two isolated algebraic numbers, by three exclusive queries.
fn z3_cmp(a: &Num, b: &Num) -> Option<Ordering> {
    let base = format!("(set-logic QF_NRA)\n{}{}", decl("x", a), decl("y", b));
    let lt = z3_sat(&format!("{base}(assert (< x y))\n(check-sat)\n"))?;
    let eq = z3_sat(&format!("{base}(assert (= x y))\n(check-sat)\n"))?;
    let gt = z3_sat(&format!("{base}(assert (> x y))\n(check-sat)\n"))?;
    match (lt, eq, gt) {
        (true, false, false) => Some(Ordering::Less),
        (false, true, false) => Some(Ordering::Equal),
        (false, false, true) => Some(Ordering::Greater),
        _ => None,
    }
}

/// z3's order for an algebraic number against a rational.
fn z3_cmp_rat(a: &Num, r: &BigRational) -> Option<Ordering> {
    let base = format!("(set-logic QF_NRA)\n{}", decl("x", a));
    let rr = smt_rat(r);
    let lt = z3_sat(&format!("{base}(assert (< x {rr}))\n(check-sat)\n"))?;
    let eq = z3_sat(&format!("{base}(assert (= x {rr}))\n(check-sat)\n"))?;
    let gt = z3_sat(&format!("{base}(assert (> x {rr}))\n(check-sat)\n"))?;
    match (lt, eq, gt) {
        (true, false, false) => Some(Ordering::Less),
        (false, true, false) => Some(Ordering::Equal),
        (false, false, true) => Some(Ordering::Greater),
        _ => None,
    }
}

/// z3's sign of the integer polynomial `qp` at the algebraic number `a`.
fn z3_sign_at(a: &Num, qp: &[BigInt]) -> Option<i32> {
    let base = format!("(set-logic QF_NRA)\n{}", decl("x", a));
    let e = smt_poly(qp, "x");
    let lt = z3_sat(&format!("{base}(assert (< {e} 0.0))\n(check-sat)\n"))?;
    let eq = z3_sat(&format!("{base}(assert (= {e} 0.0))\n(check-sat)\n"))?;
    let gt = z3_sat(&format!("{base}(assert (> {e} 0.0))\n(check-sat)\n"))?;
    match (lt, eq, gt) {
        (true, false, false) => Some(-1),
        (false, true, false) => Some(0),
        (false, false, true) => Some(1),
        _ => None,
    }
}

// ===========================================================================
// Builders for the close-pair families
// ===========================================================================

fn ints(v: &[i64]) -> Vec<BigInt> {
    v.iter().map(|x| BigInt::from(*x)).collect()
}

/// Build a `Num` for the `i`-th ascending root of `p` (0-based), using the
/// WIDEST grid the independent isolator produces (the coarse path).
fn num_of(p: Vec<BigInt>, i: usize) -> Option<Num> {
    let ivs = isolate(&QP::from_ints(&p));
    let (lo, hi, k) = ivs.get(i)?.clone();
    Some(Num {
        p,
        lo: (lo, k),
        hi: (hi, k),
    })
}

/// `x^2 - 2`
fn p_sqrt2() -> Vec<BigInt> {
    ints(&[-2, 0, 1])
}

/// `N^2 x^2 - (2 N^2 + s)`  -> root sqrt(2 + s/N^2)
fn p_sqrt2_eps(nbits: u32, s: i64) -> Vec<BigInt> {
    let n2: BigInt = BigInt::one() << (2 * nbits);
    let c0: BigInt = -(&n2 * BigInt::from(2) + BigInt::from(s));
    vec![c0, BigInt::zero(), n2]
}

/// `M x^3 - (2 M + s)` -> root cbrt(2 + s/M)
fn p_cbrt2_eps(mbits: u32, s: i64) -> Vec<BigInt> {
    let m: BigInt = BigInt::one() << mbits;
    let c0: BigInt = -(&m * BigInt::from(2) + BigInt::from(s));
    vec![c0, BigInt::zero(), BigInt::zero(), m]
}

/// Continued-fraction convergents of sqrt(2): p/q with |sqrt2 - p/q| ~ 1/(2 q^2)
fn sqrt2_convergents(n: usize) -> Vec<BigRational> {
    let mut out = Vec::new();
    let (mut pnm1, mut pn) = (BigInt::one(), BigInt::from(3));
    let (mut qnm1, mut qn) = (BigInt::one(), BigInt::from(2));
    for _ in 0..n {
        out.push(BigRational::new(pn.clone(), qn.clone()));
        let pn1: BigInt = &pn * BigInt::from(2) + &pnm1;
        let qn1: BigInt = &qn * BigInt::from(2) + &qnm1;
        pnm1 = pn;
        pn = pn1;
        qnm1 = qn;
        qn = qn1;
    }
    out
}

// ===========================================================================
// THE TESTS
// ===========================================================================

struct Tally {
    checked: usize,
    z3_checked: usize,
    wrong: Vec<String>,
    declined: Vec<String>,
}

impl Tally {
    fn new() -> Self {
        Tally {
            checked: 0,
            z3_checked: 0,
            wrong: Vec::new(),
            declined: Vec::new(),
        }
    }
    fn cmp_case(&mut self, tag: &str, a: &Num, b: &Num, use_z3: bool) {
        let (Some(aa), Some(bb)) = (a.to_ay(), b.to_ay()) else {
            self.declined
                .push(format!("{tag}: could not construct AlgCell"));
            return;
        };
        let model = model_cmp(a, b);
        self.checked += 1;
        match aa.cmp_anum(&bb) {
            None => self.declined.push(format!("{tag}: cmp_anum DECLINED")),
            Some(o) => {
                if o != model {
                    self.wrong
                        .push(format!("{tag}: AY {o:?} vs MODEL {model:?}"));
                }
            }
        }
        // antisymmetry
        match (aa.cmp_anum(&bb), bb.cmp_anum(&aa)) {
            (Some(x), Some(y)) if x != y.reverse() => self
                .wrong
                .push(format!("{tag}: NOT antisymmetric {x:?}/{y:?}")),
            _ => {}
        }
        if use_z3 {
            if let Some(z) = z3_cmp(a, b) {
                self.z3_checked += 1;
                if z != model {
                    self.wrong
                        .push(format!("{tag}: MODEL {model:?} vs Z3 {z:?}"));
                }
                if let Some(o) = aa.cmp_anum(&bb) {
                    if o != z {
                        self.wrong.push(format!("{tag}: AY {o:?} vs Z3 {z:?}"));
                    }
                }
            }
        }
    }
    fn report(&self, name: &str) {
        println!(
            "[{name}] checked={} z3_checked={} wrong={} declined={}",
            self.checked,
            self.z3_checked,
            self.wrong.len(),
            self.declined.len()
        );
        for w in &self.wrong {
            println!("  WRONG: {w}");
        }
        for d in self.declined.iter().take(20) {
            println!("  DECLINED: {d}");
        }
        assert!(
            self.wrong.is_empty(),
            "{name}: {} wrong answers",
            self.wrong.len()
        );
        assert!(
            self.checked >= 20,
            "{name}: anti-vacuity floor -- only {} cases checked",
            self.checked
        );
    }
}

/// F1 + F2: DISTINCT pairs whose separation shrinks like 2^-2k, both
/// directions, coprime defining polynomials (the coprime shortcut path).
#[test]
fn av_close_pairs_coprime() {
    let mut t = Tally::new();
    let z3_upto = 14u32; // z3 on every case up to here, then every 4th
    for nb in 0..=45u32 {
        for s in [1i64, -1, 3, -3] {
            let pa = p_sqrt2();
            let pb = p_sqrt2_eps(nb, s);
            let (Some(a), Some(b)) = (num_of(pa, 1), num_of(pb, 1)) else {
                continue;
            };
            let usez3 = nb <= z3_upto || nb % 8 == 0;
            t.cmp_case(&format!("sqrt2 vs sqrt(2+{s}/2^{})", 2 * nb), &a, &b, usez3);
        }
    }
    for mb in 0..=40u32 {
        for s in [1i64, -1] {
            let pa = ints(&[-2, 0, 0, 1]);
            let pb = p_cbrt2_eps(mb, s);
            let (Some(a), Some(b)) = (num_of(pa, 0), num_of(pb, 0)) else {
                continue;
            };
            let usez3 = mb <= 10 || mb % 8 == 0;
            t.cmp_case(&format!("cbrt2 vs cbrt(2+{s}/2^{mb})"), &a, &b, usez3);
        }
    }
    assert!(
        t.z3_checked >= 40,
        "z3 leg went blind: only {} z3 comparisons",
        t.z3_checked
    );
    t.report("close-pairs-coprime");
}

/// F3: two very close roots of the SAME defining polynomial — the
/// `deg(gcd) >= 1` branch, which the change deliberately leaves alone.
#[test]
fn av_close_pairs_same_poly() {
    let mut t = Tally::new();
    for nb in 0..=30u32 {
        let f = QP::from_ints(&p_sqrt2());
        let g = QP::from_ints(&p_sqrt2_eps(nb, 1));
        let prod = f.mul(&g);
        let pi: Vec<BigInt> = prod
            .0
            .iter()
            .map(|c| {
                assert!(c.denom().is_one());
                c.numer().clone()
            })
            .collect();
        let ivs = isolate(&QP::from_ints(&pi));
        if ivs.len() < 4 {
            continue;
        }
        // the two positive roots, adjacent and extremely close
        let a = Num {
            p: pi.clone(),
            lo: (ivs[2].0.clone(), ivs[2].2),
            hi: (ivs[2].1.clone(), ivs[2].2),
        };
        let b = Num {
            p: pi.clone(),
            lo: (ivs[3].0.clone(), ivs[3].2),
            hi: (ivs[3].1.clone(), ivs[3].2),
        };
        t.cmp_case(
            &format!("same-poly roots 2,3 at 2^-{}", 2 * nb),
            &a,
            &b,
            nb <= 10,
        );
    }
    assert!(
        t.z3_checked >= 8,
        "z3 leg went blind: only {} z3 comparisons",
        t.z3_checked
    );
    t.report("close-pairs-same-poly");
}

/// F4: EQUAL numbers written differently. Must be Equal, by certificate, with
/// zero bisections.
#[test]
fn av_equal_written_differently() {
    let mut wrong: Vec<String> = Vec::new();
    let mut n = 0usize;
    let base: Vec<(&str, Vec<BigInt>, usize)> = vec![
        ("x^2-2", ints(&[-2, 0, 1]), 1),
        ("x^4-4x^2+4", ints(&[4, 0, -4, 0, 1]), 1),
        ("(x^2-2)(x^2-3)", ints(&[6, 0, -5, 0, 1]), 2),
        ("(x^2-2)(x-5)", ints(&[10, -2, -5, 1]), 1),
        ("(x^2-2)^3", ints(&[-8, 0, 12, 0, -6, 0, 1]), 1),
        ("(x^2-2)(2x-9)", ints(&[18, -4, -9, 2]), 1),
    ];
    let mut nums: Vec<(String, Num)> = Vec::new();
    for (tag, p, idx) in &base {
        if let Some(mut a) = num_of(p.clone(), *idx) {
            nums.push((format!("{tag}[{idx}]"), a.clone()));
            // and a deliberately narrower interval for the same number
            for extra in 1..6u32 {
                let k = a.lo.1 + extra;
                let lo: BigInt = &a.lo.0 << extra;
                let hi: BigInt = &a.hi.0 << extra;
                // shrink toward the root by walking in from both ends
                let ch = QP::from_ints(&a.p).square_free().sturm();
                let mut l = lo.clone();
                let mut h = hi.clone();
                for _ in 0..extra {
                    let m: BigInt = (&l + &h) / BigInt::from(2);
                    if QP::from_ints(&a.p).square_free().sign_at(&dy(&m, k)) == 0 {
                        break;
                    }
                    if sturm_count(&ch, &dy(&l, k), &dy(&m, k)).map_or(false, |c| c >= 1) {
                        h = m;
                    } else {
                        l = m;
                    }
                }
                let cand = Num {
                    p: a.p.clone(),
                    lo: (l, k),
                    hi: (h, k),
                };
                if cand.to_ay().is_some() {
                    nums.push((format!("{tag}[{idx}]/k+{extra}"), cand));
                }
            }
            a.p = a.p.clone();
        }
    }
    for i in 0..nums.len() {
        for j in 0..nums.len() {
            let (ta, a) = &nums[i];
            let (tb, b) = &nums[j];
            let (Some(aa), Some(bb)) = (a.to_ay(), b.to_ay()) else {
                continue;
            };
            n += 1;
            match aa.cmp_anum_traced(&bb) {
                None => wrong.push(format!("{ta} vs {tb}: DECLINED")),
                Some((o, tr)) => {
                    if o != Ordering::Equal {
                        wrong.push(format!("{ta} vs {tb}: {o:?}, expected Equal"));
                    }
                    if !aa.is_rational() && !bb.is_rational() && !tr.equal_by_certificate {
                        wrong.push(format!("{ta} vs {tb}: Equal but NOT by certificate"));
                    }
                    if tr.equal_by_certificate && (tr.steps_a != 0 || tr.steps_b != 0) {
                        wrong.push(format!("{ta} vs {tb}: certificate path bisected"));
                    }
                }
            }
        }
    }
    println!(
        "[equal-written-differently] pairs={n} wrong={}",
        wrong.len()
    );
    for w in wrong.iter().take(40) {
        println!("  WRONG: {w}");
    }
    assert!(n >= 100, "expected >= 100 equal pairs, got {n}");
    assert!(wrong.is_empty());
}

/// F5: algebraic vs a rational separated by ~2^-k for k growing to ~250.
/// This is the path the injected defect in the report surfaced through.
#[test]
fn av_algebraic_vs_close_rational() {
    let mut wrong: Vec<String> = Vec::new();
    let mut declined = 0usize;
    let mut n = 0usize;
    let mut z3n = 0usize;
    let a = num_of(p_sqrt2(), 1).expect("sqrt2");
    let aa = a.to_ay().expect("cell");
    let convs = sqrt2_convergents(40);
    for (i, r) in convs.iter().enumerate() {
        // exact model: sign of (den*x - num) at sqrt2 == sign of 2*den^2 - num^2
        let cmpq: Ordering = {
            let n2: BigInt = r.numer() * r.numer();
            let d2: BigInt = r.denom() * r.denom() * BigInt::from(2);
            // sqrt2 vs num/den  <=>  2*den^2 vs num^2  (both positive)
            d2.cmp(&n2).reverse().reverse()
        };
        // sqrt2 < r  iff 2*den^2 < num^2
        let model = {
            let n2: BigInt = r.numer() * r.numer();
            let d2: BigInt = r.denom() * r.denom() * BigInt::from(2);
            d2.cmp(&n2)
        };
        let _ = cmpq;
        let rat = ODyadicAnum::rational(r.clone());
        n += 1;
        match aa.cmp_anum(&rat) {
            None => {
                declined += 1;
                wrong.push(format!("conv[{i}] {r}: DECLINED"));
            }
            Some(o) => {
                if o != model {
                    wrong.push(format!("conv[{i}] {r}: AY {o:?} vs MODEL {model:?}"));
                }
                if rat.cmp_anum(&aa) != Some(o.reverse()) {
                    wrong.push(format!("conv[{i}] {r}: not antisymmetric"));
                }
            }
        }
        if i < 12 || i % 6 == 0 {
            if let Some(z) = z3_cmp_rat(&a, r) {
                z3n += 1;
                if z != model {
                    wrong.push(format!("conv[{i}] {r}: MODEL {model:?} vs Z3 {z:?}"));
                }
                if aa.cmp_anum(&rat) != Some(z) {
                    wrong.push(format!("conv[{i}] {r}: AY vs Z3 disagree"));
                }
            }
        }
    }
    // and the same through sign_of_poly on `den*x - num`
    for (i, r) in convs.iter().enumerate() {
        let qq = vec![-r.numer().clone(), r.denom().clone()];
        let model_sign = {
            // sign of (den*sqrt2 - num) = sign of (2 den^2 - num^2) when den>0
            let n2: BigInt = r.numer() * r.numer();
            let d2: BigInt = r.denom() * r.denom() * BigInt::from(2);
            match d2.cmp(&n2) {
                Ordering::Less => -1,
                Ordering::Equal => 0,
                Ordering::Greater => 1,
            }
        };
        n += 1;
        match aa.sign_of_poly(&qq) {
            None => {
                declined += 1;
                wrong.push(format!("sign conv[{i}]: DECLINED"));
            }
            Some(s) => {
                if s != model_sign {
                    wrong.push(format!("sign conv[{i}]: AY {s} vs MODEL {model_sign}"));
                }
            }
        }
        if i < 10 {
            if let Some(z) = z3_sign_at(&a, &qq) {
                z3n += 1;
                if z != model_sign {
                    wrong.push(format!("sign conv[{i}]: MODEL {model_sign} vs Z3 {z}"));
                }
            }
        }
    }
    println!(
        "[alg-vs-close-rational] checked={n} z3_checked={z3n} wrong={} declined={declined}",
        wrong.len()
    );
    assert!(z3n >= 15, "z3 leg went blind: {z3n}");
    for w in wrong.iter().take(40) {
        println!("  WRONG: {w}");
    }
    assert!(wrong.is_empty());
}

/// F6: `sign_of_poly` where `q` has a root extremely close to alpha but not
/// equal to it — the case the Sturm stopping certificate must not fumble.
#[test]
fn av_sign_of_poly_near_root() {
    let mut wrong: Vec<String> = Vec::new();
    let mut n = 0usize;
    let mut z3n = 0usize;
    let a = num_of(p_sqrt2(), 1).expect("sqrt2");
    let aa = a.to_ay().expect("cell");
    for nb in 0..=45u32 {
        for s in [1i64, -1, 5, -5] {
            let qq = p_sqrt2_eps(nb, s);
            // sign of N^2 x^2 - (2N^2+s) at sqrt2 = -s
            let model = if s > 0 { -1 } else { 1 };
            n += 1;
            match aa.sign_of_poly(&qq) {
                None => wrong.push(format!("nb={nb} s={s}: DECLINED")),
                Some(v) => {
                    if v != model {
                        wrong.push(format!("nb={nb} s={s}: AY {v} vs MODEL {model}"));
                    }
                }
            }
            if nb <= 12 {
                if let Some(z) = z3_sign_at(&a, &qq) {
                    z3n += 1;
                    if z != model {
                        wrong.push(format!("nb={nb} s={s}: MODEL {model} vs Z3 {z}"));
                    }
                }
            }
        }
    }
    // exact-zero case: q vanishing at alpha, several shapes
    for qq in [
        p_sqrt2(),
        ints(&[4, 0, -4, 0, 1]),
        ints(&[6, 0, -5, 0, 1]),
        ints(&[-4, 0, 2]),
        ints(&[10, -2, -5, 1]),
    ] {
        n += 1;
        match aa.sign_of_poly(&qq) {
            Some(0) => {}
            other => wrong.push(format!("vanishing q: got {other:?}, expected Some(0)")),
        }
    }
    println!(
        "[sign-near-root] checked={n} z3_checked={z3n} wrong={}",
        wrong.len()
    );
    assert!(z3n >= 30, "z3 leg went blind: {z3n}");
    for w in wrong.iter().take(40) {
        println!("  WRONG: {w}");
    }
    assert!(wrong.is_empty());
}

/// Liveness: nothing spins, and the declared bound is respected. Also pins the
/// separation exponent's monotone direction against the OLD formula.
#[test]
fn av_liveness_and_bound() {
    use std::time::Instant;
    let mut violations: Vec<String> = Vec::new();
    let mut n = 0usize;
    let t0 = Instant::now();
    for nb in [0u32, 8, 20, 40, 60, 90, 120, 200, 400, 800, 1200] {
        for s in [1i64, -1] {
            let pa = p_sqrt2();
            let pb = p_sqrt2_eps(nb, s);
            let (Some(a), Some(b)) = (num_of(pa, 1), num_of(pb, 1)) else {
                continue;
            };
            let (Some(aa), Some(bb)) = (a.to_ay(), b.to_ay()) else {
                continue;
            };
            let t = Instant::now();
            let r = aa.cmp_anum_traced(&bb);
            let el = t.elapsed();
            n += 1;
            if el.as_secs() > 20 {
                violations.push(format!("nb={nb}: cmp took {el:?}"));
            }
            match r {
                None => violations.push(format!("nb={nb} s={s}: DECLINED")),
                Some((o, tr)) => {
                    let model = model_cmp(&a, &b);
                    if o != model {
                        violations.push(format!("nb={nb} s={s}: AY {o:?} vs MODEL {model:?}"));
                    }
                    if tr.steps_a > tr.bound || tr.steps_b > tr.bound {
                        violations.push(format!(
                            "nb={nb} s={s}: steps {}/{} > bound {}",
                            tr.steps_a, tr.steps_b, tr.bound
                        ));
                    }
                }
            }
        }
    }
    println!(
        "[liveness] cases={n} total={:?} violations={}",
        t0.elapsed(),
        violations.len()
    );
    for v in violations.iter().take(40) {
        println!("  VIOLATION: {v}");
    }
    assert!(violations.is_empty());
}

#[cfg(test)]
include!("av_adversarial/dump_verdicts.rs");

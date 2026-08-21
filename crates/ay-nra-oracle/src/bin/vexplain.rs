// Adversarial verification harness: INDEPENDENT implication check.
//
// Generates univariate conflicts, drives `oexplain_univariate`, and emits an
// SMT2 script asking the reference z3 (nlsat, a completely different code path
// from the `Z3_algebraic_*` C API the in-tree oracle uses) whether the CITED
// conjunction is unsatisfiable. A clause that is a theory consequence has an
// unsatisfiable citation set; anything else is a wrong `unsat` in waiting.
//
// Root isolation here is MINE: squarefree part + Sturm chain + bisection over
// exact BigRational, sharing no AY code. AY re-verifies the list anyway.

#![allow(unsafe_code)] // Dedicated C-ABI boundary to libz3; sites carry local invariants.

use num_bigint::BigInt;
use num_rational::BigRational as Q;
use num_traits::{One, Signed, Zero};
use std::io::Write;

use ay_nra::oracle_api::{
    oexplain_clause_is_falsified, oexplain_clause_is_valid, oexplain_countermodel,
    oexplain_relevant_pairs, oexplain_univariate, OBq, OBqInterval, ODyadicAnum, OExplainLit,
    OISignCond,
};

// ---------------------------------------------------------------- my polys

fn qi(n: i64) -> Q {
    Q::from_integer(BigInt::from(n))
}
fn to_q(p: &[BigInt]) -> Vec<Q> {
    p.iter().map(|c| Q::from_integer(c.clone())).collect()
}
fn deg(p: &[Q]) -> Option<usize> {
    p.iter().rposition(|c| !c.is_zero())
}
fn eval(p: &[Q], x: &Q) -> Q {
    let mut acc = Q::zero();
    for c in p.iter().rev() {
        acc = acc * x + c;
    }
    acc
}
fn derive(p: &[Q]) -> Vec<Q> {
    if p.len() <= 1 {
        return vec![Q::zero()];
    }
    (1..p.len()).map(|i| &p[i] * qi(i as i64)).collect()
}
fn prem(a: &[Q], b: &[Q]) -> Vec<Q> {
    let db = match deg(b) {
        Some(d) => d,
        None => return vec![Q::zero()],
    };
    let mut r = a.to_vec();
    while let Some(dr) = deg(&r) {
        if dr < db {
            break;
        }
        let f = &r[dr] / &b[db];
        for i in 0..=db {
            let t = &f * &b[i];
            r[dr - db + i] = &r[dr - db + i] - t;
        }
        r[dr] = Q::zero();
    }
    r
}
fn poly_gcd(a: &[Q], b: &[Q]) -> Vec<Q> {
    let mut x = a.to_vec();
    let mut y = b.to_vec();
    while deg(&y).is_some() {
        let r = prem(&x, &y);
        x = y;
        y = r;
    }
    if let Some(d) = deg(&x) {
        let lc = x[d].clone();
        x.iter().map(|c| c / &lc).collect()
    } else {
        vec![Q::one()]
    }
}
fn pdiv(a: &[Q], b: &[Q]) -> Vec<Q> {
    let db = deg(b).unwrap();
    let mut r = a.to_vec();
    let mut qout = vec![Q::zero(); a.len()];
    while let Some(dr) = deg(&r) {
        if dr < db {
            break;
        }
        let f = &r[dr] / &b[db];
        qout[dr - db] = f.clone();
        for i in 0..=db {
            let t = &f * &b[i];
            r[dr - db + i] = &r[dr - db + i] - t;
        }
        r[dr] = Q::zero();
    }
    qout
}
fn squarefree(p: &[Q]) -> Vec<Q> {
    let g = poly_gcd(p, &derive(p));
    if deg(&g).unwrap_or(0) == 0 {
        p.to_vec()
    } else {
        pdiv(p, &g)
    }
}
fn sturm(p: &[Q]) -> Vec<Vec<Q>> {
    let mut ch = vec![p.to_vec(), derive(p)];
    loop {
        let n = ch.len();
        if deg(&ch[n - 1]).is_none() {
            ch.pop();
            break;
        }
        let r: Vec<Q> = prem(&ch[n - 2], &ch[n - 1]).iter().map(|c| -c).collect();
        if deg(&r).is_none() {
            break;
        }
        ch.push(r);
    }
    ch
}
fn vchanges(ch: &[Vec<Q>], x: &Q) -> usize {
    let mut last = 0i32;
    let mut n = 0;
    for c in ch {
        let v = eval(c, x);
        let s = if v.is_positive() {
            1
        } else if v.is_negative() {
            -1
        } else {
            0
        };
        if s != 0 {
            if last != 0 && s != last {
                n += 1;
            }
            last = s;
        }
    }
    n
}
fn cauchy(p: &[Q]) -> Q {
    let d = deg(p).unwrap();
    let mut m = Q::zero();
    for c in &p[..d] {
        let a = c.abs() / p[d].abs();
        if a > m {
            m = a;
        }
    }
    m + qi(1)
}

/// A root of `p`: either exact rational, or a dyadic isolating open interval.
#[derive(Clone, Debug)]
enum MyRoot {
    Rat(Q),
    Iv(Q, Q),
}

/// Isolate every real root of the integer polynomial `pi`. Fully independent of AY.
fn isolate(pi: &[BigInt]) -> Option<Vec<MyRoot>> {
    let p = to_q(pi);
    if deg(&p).unwrap_or(0) < 1 {
        return Some(vec![]);
    }
    let sf = squarefree(&p);
    let ch = sturm(&sf);
    let b = cauchy(&sf);
    // Integer bound, so all endpoints stay dyadic.
    let bi = b.ceil().to_integer() + BigInt::from(1);
    let (lo0, hi0) = (Q::from_integer(-bi.clone()), Q::from_integer(bi));
    let mut work = vec![(lo0, hi0)];
    let mut out: Vec<MyRoot> = Vec::new();
    let mut guard = 0;
    while let Some((lo, hi)) = work.pop() {
        guard += 1;
        if guard > 20_000 {
            return None;
        }
        let n = vchanges(&ch, &lo).saturating_sub(vchanges(&ch, &hi));
        if n == 0 {
            continue;
        }
        if n == 1 {
            out.push(MyRoot::Iv(lo, hi));
            continue;
        }
        // Split at a dyadic point that is not itself a root.
        let mut mid = (&lo + &hi) / qi(2);
        let mut k = 2u32;
        while eval(&sf, &mid).is_zero() {
            if k > 40 {
                return None;
            }
            let step = (&hi - &lo) / Q::from_integer(BigInt::from(1u32) << k);
            mid = (&lo + &hi) / qi(2) + step;
            k += 1;
        }
        if eval(&sf, &mid).is_zero() {
            return None;
        }
        work.push((lo, mid.clone()));
        work.push((mid, hi));
    }
    // Tighten each interval and detect exact rational roots by bisection.
    let mut fin: Vec<MyRoot> = Vec::new();
    for r in out {
        match r {
            MyRoot::Rat(q) => fin.push(MyRoot::Rat(q)),
            MyRoot::Iv(mut lo, mut hi) => {
                let mut exact = None;
                for _ in 0..60 {
                    if &hi - &lo < Q::new(BigInt::one(), BigInt::from(1u64 << 40)) {
                        break;
                    }
                    let mid = (&lo + &hi) / qi(2);
                    if eval(&sf, &mid).is_zero() {
                        exact = Some(mid);
                        break;
                    }
                    let n = vchanges(&ch, &lo).saturating_sub(vchanges(&ch, &mid));
                    if n == 1 {
                        hi = mid;
                    } else {
                        lo = mid;
                    }
                }
                match exact {
                    Some(q) => fin.push(MyRoot::Rat(q)),
                    None => fin.push(MyRoot::Iv(lo, hi)),
                }
            }
        }
    }
    fin.sort_by(|a, b| {
        let ka = match a {
            MyRoot::Rat(q) => q.clone(),
            MyRoot::Iv(l, _) => l.clone(),
        };
        let kb = match b {
            MyRoot::Rat(q) => q.clone(),
            MyRoot::Iv(l, _) => l.clone(),
        };
        ka.partial_cmp(&kb).unwrap()
    });
    Some(fin)
}

/// Dyadic `Q` -> `OBq`. `None` if the denominator is not a power of two.
fn to_bq(q: &Q) -> Option<OBq> {
    let mut den = q.denom().clone();
    let mut k = 0u32;
    let two = BigInt::from(2);
    while den != BigInt::one() {
        if &den % &two != BigInt::zero() {
            return None;
        }
        den /= &two;
        k += 1;
    }
    Some(OBq::new(q.numer().clone(), k))
}

fn to_anum(pi: &[BigInt], r: &MyRoot) -> Option<ODyadicAnum> {
    match r {
        MyRoot::Rat(q) => Some(ODyadicAnum::rational(q.clone())),
        MyRoot::Iv(lo, hi) => {
            let iv = OBqInterval::new(&to_bq(lo)?, &to_bq(hi)?)?;
            ODyadicAnum::from_poly_interval(pi, &iv)
        }
    }
}

// ---------------------------------------------------------------- smt2

fn smt_poly(p: &[BigInt]) -> String {
    let mut ts: Vec<String> = Vec::new();
    for (i, c) in p.iter().enumerate() {
        if c.is_zero() {
            continue;
        }
        let cs = if c.is_negative() {
            format!("(- {})", -c)
        } else {
            format!("{c}")
        };
        ts.push(match i {
            0 => cs,
            1 => format!("(* {cs} x)"),
            _ => format!("(* {cs} {})", vec!["x"; i].join(" ")),
        });
    }
    if ts.is_empty() {
        return "0".into();
    }
    if ts.len() == 1 {
        return ts.pop().unwrap();
    }
    format!("(+ {})", ts.join(" "))
}

fn smt_atom(p: &[BigInt], c: OISignCond) -> String {
    let e = smt_poly(p);
    match c {
        OISignCond::Lt => format!("(< {e} 0)"),
        OISignCond::Le => format!("(<= {e} 0)"),
        OISignCond::Eq => format!("(= {e} 0)"),
        OISignCond::Ne => format!("(not (= {e} 0))"),
        OISignCond::Ge => format!("(>= {e} 0)"),
        OISignCond::Gt => format!("(> {e} 0)"),
    }
}

// ---------------------------------------------------------------- rng

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n.max(1)
    }
    fn range(&mut self, a: i64, b: i64) -> i64 {
        a + (self.next() % ((b - a + 1) as u64)) as i64
    }
}

fn ints(v: &[i64]) -> Vec<BigInt> {
    v.iter().map(|&c| BigInt::from(c)).collect()
}
fn pmul(a: &[BigInt], b: &[BigInt]) -> Vec<BigInt> {
    let mut out = vec![BigInt::zero(); a.len() + b.len() - 1];
    for (i, x) in a.iter().enumerate() {
        for (j, y) in b.iter().enumerate() {
            out[i + j] += x * y;
        }
    }
    out
}

const CONDS: [OISignCond; 6] = [
    OISignCond::Lt,
    OISignCond::Le,
    OISignCond::Eq,
    OISignCond::Ne,
    OISignCond::Ge,
    OISignCond::Gt,
];

struct Case {
    polys: Vec<Vec<BigInt>>,
    conds: Vec<OISignCond>,
    shape: &'static str,
}

/// Adversarial generator: shapes chosen to break projection/decomposition
/// reasoning — shared roots, zero discriminant (repeated roots), strict vs
/// non-strict boundaries, high degree, near-tangency, and plain random.
fn gencase(rng: &mut Rng) -> Case {
    let k = rng.below(16);
    let shape = match k {
        12 => "padded",
        13 => "content",
        14 => "deg8",
        15 => "mixed-rat-irrat",
        0 => "shared-root",
        1 => "repeated-root",
        2 => "boundary-strict",
        3 => "tangent",
        4 => "high-degree",
        5 => "many-lits",
        6 => "irrational-tight",
        7 => "eq-chain",
        8 => "ne-cover",
        9 => "random-deg3",
        10 => "random-deg4",
        _ => "linear-many",
    };
    let (polys, conds) = match shape {
        // Coefficient vector padded with high-order ZEROS: the true degree is
        // lower than `p.len()-1`, which is where a leading-coefficient
        // assumption goes wrong.
        "padded" => {
            let a = rng.range(-4, 4);
            let mut p = pmul(&ints(&[-a, 1]), &ints(&[-(a + 2), 1]));
            for _ in 0..(1 + rng.below(3)) {
                p.push(BigInt::zero());
            }
            let mut q = ints(&[-rng.range(-4, 4), 1]);
            q.push(BigInt::zero());
            q.push(BigInt::zero());
            (
                vec![p, q],
                vec![CONDS[rng.below(6) as usize], CONDS[rng.below(6) as usize]],
            )
        }
        // A large integer CONTENT factor: same roots, different primitive part.
        "content" => {
            let c = 6 + rng.range(0, 30);
            let a = rng.range(-4, 4);
            let p: Vec<BigInt> = pmul(&ints(&[-a, 1]), &ints(&[-(a + 1), 1]))
                .iter()
                .map(|t| t * BigInt::from(c))
                .collect();
            let q: Vec<BigInt> = ints(&[-rng.range(-6, 6), 2])
                .iter()
                .map(|t| t * BigInt::from(c))
                .collect();
            (
                vec![p, q],
                vec![CONDS[rng.below(6) as usize], CONDS[rng.below(6) as usize]],
            )
        }
        // Degree up to 8, with repeated factors so discriminants vanish.
        "deg8" => {
            let mut p = ints(&[1]);
            for _ in 0..(6 + rng.below(3)) {
                p = pmul(&p, &ints(&[-rng.range(-3, 3), 1]));
            }
            let mut q = ints(&[1]);
            for _ in 0..(2 + rng.below(3)) {
                q = pmul(&q, &ints(&[-rng.range(-3, 3), 1]));
            }
            (
                vec![p, q],
                vec![CONDS[rng.below(6) as usize], CONDS[rng.below(6) as usize]],
            )
        }
        // Rational and irrational roots interleaved and CLOSE together.
        "mixed-rat-irrat" => {
            let ds = [2i64, 3, 5, 6, 7, 8, 10, 11];
            let d = ds[rng.below(8) as usize];
            let p = ints(&[-d, 0, 1]);
            let a = rng.range(-3, 3);
            let q = pmul(&ints(&[-a, 1]), &ints(&[-(a + 1), 1]));
            let r = ints(&[-(d * 4 + 1), 0, 4]);
            (
                vec![p, q, r],
                vec![
                    CONDS[rng.below(6) as usize],
                    CONDS[rng.below(6) as usize],
                    CONDS[rng.below(6) as usize],
                ],
            )
        }
        "shared-root" => {
            // p and q share the root a; strictness decides.
            let a = rng.range(-4, 4);
            let b = rng.range(-4, 4);
            let c = rng.range(-4, 4);
            let p = pmul(&ints(&[-a, 1]), &ints(&[-b, 1]));
            let q = pmul(&ints(&[-a, 1]), &ints(&[-c, 1]));
            (
                vec![p, q],
                vec![CONDS[rng.below(6) as usize], CONDS[rng.below(6) as usize]],
            )
        }
        "repeated-root" => {
            // (x-a)^2 : discriminant zero. Sign never changes at a.
            let a = rng.range(-4, 4);
            let f = ints(&[-a, 1]);
            let p = pmul(&f, &f);
            let b = rng.range(-4, 4);
            (
                vec![p, ints(&[-b, 1])],
                vec![CONDS[rng.below(6) as usize], CONDS[rng.below(6) as usize]],
            )
        }
        "boundary-strict" => {
            // x >= a and x <= a : satisfiable only AT a. Flip strictness by draw.
            let a = rng.range(-4, 4);
            let c0 = if rng.below(2) == 0 {
                OISignCond::Ge
            } else {
                OISignCond::Gt
            };
            let c1 = if rng.below(2) == 0 {
                OISignCond::Le
            } else {
                OISignCond::Lt
            };
            (vec![ints(&[-a, 1]), ints(&[-a, 1])], vec![c0, c1])
        }
        "tangent" => {
            // x^2 - 2a x + a^2 + t : touches zero when t = 0, no real root t>0.
            let a = rng.range(-3, 3);
            let t = rng.range(0, 2);
            let p = ints(&[a * a + t, -2 * a, 1]);
            (
                vec![p, ints(&[-rng.range(-4, 4), 1])],
                vec![CONDS[rng.below(6) as usize], CONDS[rng.below(6) as usize]],
            )
        }
        "high-degree" => {
            let mut p = ints(&[1]);
            let n = 3 + rng.below(3);
            for _ in 0..n {
                p = pmul(&p, &ints(&[-rng.range(-3, 3), 1]));
            }
            let mut q = ints(&[1]);
            for _ in 0..n {
                q = pmul(&q, &ints(&[-rng.range(-3, 3), 1]));
            }
            (
                vec![p, q],
                vec![CONDS[rng.below(6) as usize], CONDS[rng.below(6) as usize]],
            )
        }
        "many-lits" => {
            let n = 4 + rng.below(5);
            let mut ps = Vec::new();
            let mut cs = Vec::new();
            for _ in 0..n {
                let d = 1 + rng.below(2);
                let mut p = ints(&[1]);
                for _ in 0..d {
                    p = pmul(&p, &ints(&[-rng.range(-4, 4), 1]));
                }
                ps.push(p);
                cs.push(CONDS[rng.below(6) as usize]);
            }
            (ps, cs)
        }
        "irrational-tight" => {
            // x^2 - d < 0 with x^2 - e > 0 : conflict iff d <= e. Also nested.
            let ds = [2i64, 3, 5, 6, 7, 10, 11, 13];
            let d = ds[rng.below(8) as usize];
            let e = ds[rng.below(8) as usize];
            (
                vec![ints(&[-d, 0, 1]), ints(&[-e, 0, 1])],
                vec![CONDS[rng.below(6) as usize], CONDS[rng.below(6) as usize]],
            )
        }
        "eq-chain" => {
            let a = rng.range(-4, 4);
            let b = rng.range(-4, 4);
            (
                vec![
                    ints(&[-a, 1]),
                    ints(&[-b, 1]),
                    ints(&[-rng.range(-4, 4), 0, 1]),
                ],
                vec![OISignCond::Eq, OISignCond::Eq, CONDS[rng.below(6) as usize]],
            )
        }
        "ne-cover" => {
            // != on a poly whose roots are all of the other's feasible points.
            let a = rng.range(-3, 3);
            let p = pmul(&ints(&[-a, 1]), &ints(&[-(a + 1), 1]));
            (
                vec![p.clone(), p],
                vec![OISignCond::Ne, CONDS[rng.below(6) as usize]],
            )
        }
        "random-deg3" | "random-deg4" => {
            let d = if shape == "random-deg3" { 3 } else { 4 };
            let n = 2 + rng.below(2);
            let mut ps = Vec::new();
            let mut cs = Vec::new();
            for _ in 0..n {
                let mut c: Vec<BigInt> = (0..=d).map(|_| BigInt::from(rng.range(-5, 5))).collect();
                if c[d].is_zero() {
                    c[d] = BigInt::one();
                }
                ps.push(c);
                cs.push(CONDS[rng.below(6) as usize]);
            }
            (ps, cs)
        }
        _ => {
            let n = 3 + rng.below(6);
            let mut ps = Vec::new();
            let mut cs = Vec::new();
            for _ in 0..n {
                let a = rng.range(-8, 8);
                let m = rng.range(1, 3);
                ps.push(ints(&[-a, m]));
                cs.push(CONDS[rng.below(6) as usize]);
            }
            (ps, cs)
        }
    };
    Case {
        polys,
        conds,
        shape,
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
    let n: usize = args
        .iter()
        .position(|a| a == "--cases")
        .and_then(|i| args.get(i + 1))
        .and_then(|s| s.parse().ok())
        .unwrap_or(200);
    let out = args
        .iter()
        .position(|a| a == "--out")
        .and_then(|i| args.get(i + 1))
        .cloned()
        .unwrap_or_else(|| "/tmp/vexplain".to_string());

    let mut rng = Rng(seed.wrapping_mul(6364136223846793005).wrapping_add(1) | 1);
    let mut smt = String::from("(set-logic QF_NRA)\n(declare-fun x () Real)\n");
    let mut manifest: Vec<String> = Vec::new();
    let mut produced = 0usize;
    let mut declined_isolate = 0usize;
    let mut skipped = 0usize;
    let mut ay_valid_true = 0usize;
    let mut ay_valid_false = 0usize;
    let mut ay_valid_none = 0usize;
    let mut cm_present = 0usize;
    let mut falsified_fail = 0usize;
    let mut shapes: std::collections::BTreeMap<&str, usize> = Default::default();

    for case_id in 0..n {
        let c = gencase(&mut rng);
        // build AY lits with MY roots
        let mut lits: Vec<OExplainLit> = Vec::new();
        let mut ok = true;
        for (i, (p, cd)) in c.polys.iter().zip(&c.conds).enumerate() {
            if p.iter().rposition(|x| !x.is_zero()).unwrap_or(0) < 1 {
                ok = false;
                break;
            }
            let Some(rs) = isolate(p) else {
                ok = false;
                break;
            };
            let mut roots = Vec::new();
            for r in &rs {
                match to_anum(p, r) {
                    Some(a) => roots.push(a),
                    None => {
                        ok = false;
                        break;
                    }
                }
            }
            if !ok {
                break;
            }
            lits.push(OExplainLit {
                lit: (i + 1) as i32,
                p: p.clone(),
                cond: *cd,
                roots,
            });
        }
        if !ok || lits.len() != c.polys.len() {
            declined_isolate += 1;
            continue;
        }
        *shapes.entry(c.shape).or_default() += 1;

        // Drive the module.
        match oexplain_clause_is_valid(&lits) {
            Some(true) => ay_valid_true += 1,
            Some(false) => ay_valid_false += 1,
            None => ay_valid_none += 1,
        }
        let cm = oexplain_countermodel(&lits);
        if matches!(cm, Some(Some(_))) {
            cm_present += 1;
        }
        // relevant_pairs, driven directly
        let _ = oexplain_relevant_pairs(&lits);

        let expl = oexplain_univariate(&lits);

        // FULL conjunction query
        let full: Vec<String> = c
            .polys
            .iter()
            .zip(&c.conds)
            .map(|(p, cd)| smt_atom(p, *cd))
            .collect();
        smt.push_str("(push 1)\n");
        for a in &full {
            smt.push_str(&format!("(assert {a})\n"));
        }
        smt.push_str("(check-sat)\n(pop 1)\n");
        manifest.push(format!(
            "{case_id}\tFULL\t{}\t{}\t{}",
            c.shape,
            expl.is_some(),
            match oexplain_clause_is_valid(&lits) {
                Some(true) => "valid",
                Some(false) => "invalid",
                None => "decline",
            }
        ));

        if let Some(e) = &expl {
            produced += 1;
            // property (a): false under the trail
            let trail: Vec<i32> = lits.iter().map(|l| l.lit).collect();
            if !oexplain_clause_is_falsified(&e.lits, &trail) {
                falsified_fail += 1;
            }
            // CITED conjunction query — MUST be unsat
            smt.push_str("(push 1)\n");
            for cl in &e.cited {
                let l = lits.iter().find(|l| l.lit == *cl).unwrap();
                smt.push_str(&format!("(assert {})\n", smt_atom(&l.p, l.cond)));
            }
            smt.push_str("(check-sat)\n(pop 1)\n");
            manifest.push(format!(
                "{case_id}\tCITED\t{}\t{:?}\t{:?}",
                c.shape, e.lits, e.cited
            ));
        } else {
            skipped += 1;
        }
    }

    std::fs::write(format!("{out}.smt2"), &smt).unwrap();
    std::fs::write(format!("{out}.manifest"), manifest.join("\n")).unwrap();
    let mut err = std::io::stderr();
    writeln!(
        err,
        "seed={seed} cases={n} usable={} produced={} noclause={} isolate_declined={}",
        n - declined_isolate,
        produced,
        skipped,
        declined_isolate
    )
    .unwrap();
    writeln!(
        err,
        "clause_is_valid: true={ay_valid_true} false={ay_valid_false} DECLINE={ay_valid_none}  countermodels={cm_present}  falsified_fail={falsified_fail}"
    )
    .unwrap();
    writeln!(err, "shapes: {shapes:?}").unwrap();
}

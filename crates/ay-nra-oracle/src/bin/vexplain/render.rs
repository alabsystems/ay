// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Included by the binary root; the harness remains a single private namespace.

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

type GeneratedShape = (Vec<Vec<BigInt>>, Vec<OISignCond>);

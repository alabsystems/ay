// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Included by the binary root; the harness remains a single private namespace.

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

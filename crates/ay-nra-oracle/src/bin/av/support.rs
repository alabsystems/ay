// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `av` to preserve existing item DefPaths.

static FAILURES: AtomicU64 = AtomicU64::new(0);
static CHECKS: AtomicU64 = AtomicU64::new(0);
static REFERENCE_CHECKS: AtomicU64 = AtomicU64::new(0);
static REFERENCE_ERRORS: AtomicU64 = AtomicU64::new(0);

fn bad(name: &str, msg: String) {
    FAILURES.fetch_add(1, AtomicOrdering::Relaxed);
    println!("FAIL  {name}: {msg}");
}
fn okc() {
    CHECKS.fetch_add(1, AtomicOrdering::Relaxed);
}

fn reference_okc() {
    REFERENCE_CHECKS.fetch_add(1, AtomicOrdering::Relaxed);
    okc();
}

fn z3_error(name: &str, operation: &str) {
    REFERENCE_ERRORS.fetch_add(1, AtomicOrdering::Relaxed);
    println!("ERROR {name}: reference libz3 failed during {operation}");
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
        let sm = sign_q(&f1, &am);
        if sm == 0 {
            // exact root
            a0 = am.clone();
            a1 = am.clone();
        } else if sm == sign_q(&f1, &a0) {
            a0 = am;
        } else {
            a1 = am;
        }
        let bm = (&b0 + &b1) / &two;
        let sn = sign_q(&f2, &bm);
        if sn == 0 {
            b0 = bm.clone();
            b1 = bm.clone();
        } else if sn == sign_q(&f2, &b0) {
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
        Err(mpsc::RecvTimeoutError::Timeout) => {
            bad(name, format!("DID NOT RETURN within {secs}s — HANG"));
            eprintln!("FATAL: watchdog timeout; refusing to leave a worker running");
            std::process::exit(2);
        }
        Err(mpsc::RecvTimeoutError::Disconnected) => {
            bad(name, "watchdog worker panicked or disconnected".into());
            eprintln!("FATAL: watchdog worker failed");
            std::process::exit(2);
        }
    }
}

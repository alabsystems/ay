//! INDEPENDENT re-measurement of the two envelope rows the campaign quotes,
//! plus a realistic sequence at IRREGULAR sizes. Same file runs on both builds.
#![cfg(feature = "oracle-api")]
#![allow(clippy::all)]

use ay_nra::oracle_api::{OBq, OBqInterval, ODyadicAnum, OIAlgInterval, OIAlgSet};
use num_bigint::BigInt;
use num_traits::{One, Zero};
use std::time::Instant;

fn load() -> String {
    std::process::Command::new("uptime")
        .output()
        .ok()
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
        .unwrap_or_default()
        .split("load average")
        .nth(1)
        .unwrap_or("?")
        .trim_start_matches(|c| c == 's' || c == ':' || c == ' ')
        .to_string()
}

/// `(x - j)^n - c`, whose real root `j + c^(1/n)` sits in `(j+1, j+2)` for
/// `1 < c < 2^n`. Degree `n` endpoints, well separated across `j`.
fn shifted_root(j: i64, n: usize, c: i64) -> Option<ODyadicAnum> {
    // binomial expansion of (x - j)^n
    let mut coeffs: Vec<BigInt> = vec![BigInt::zero(); n + 1];
    let mut binom = BigInt::one();
    for i in 0..=n {
        // coefficient of x^(n-i) is C(n,i) * (-j)^i
        let term = &binom * BigInt::from(-j).pow(i as u32);
        coeffs[n - i] = term;
        binom = &binom * BigInt::from((n - i) as u64) / BigInt::from((i + 1) as u64);
    }
    coeffs[0] -= BigInt::from(c);
    let iv = OBqInterval::new(
        &OBq::from_int(BigInt::from(j + 1)),
        &OBq::from_int(BigInt::from(j + 2)),
    )?;
    ODyadicAnum::from_poly_interval(&coeffs, &iv)
}

/// `k` disjoint intervals whose endpoints all have degree `n`.
fn deg_set(k: usize, n: usize, lit: i32) -> Option<Vec<OIAlgInterval>> {
    let mut out = Vec::with_capacity(k);
    for i in 0..k {
        let lo = shifted_root(2 * i as i64, n, 2)?;
        let hi = shifted_root(2 * i as i64 + 1, n, 2)?;
        out.push(OIAlgInterval {
            lo: Some(lo),
            lo_open: true,
            hi: Some(hi),
            hi_open: true,
            lits: vec![lit],
        });
    }
    Some(out)
}

/// ROW 1 of the campaign's cost table: exact sign of a polynomial at an
/// algebraic point, by ENDPOINT DEGREE.
#[test]
fn av_env_sign_by_endpoint_degree() {
    // Measurement harness, not a regression (the gate forbids disabled
    // tests): no-ops unless opted in (AY_LIA_HOT_LOOP_ITERS class).
    if std::env::var_os("AY_NRA_PROFILE").is_none() {
        return;
    }
    println!("\n== ROW 1: sign_of_poly at an algebraic point, by ENDPOINT DEGREE ==");
    println!("load: {}", load());
    println!(
        "{:>5} {:>14} {:>14} {:>6}",
        "deg", "q=deg2 us", "q=samedeg us", "sign"
    );
    for n in [2usize, 4, 8, 12, 16, 24, 32, 48, 64] {
        let Some(a) = shifted_root(0, n, 2) else {
            println!("{n:>5}   could not build");
            continue;
        };
        // a fixed low-degree probe: 4x^2 - 9  (root 3/2, near 2^(1/n) for big n)
        let q2 = vec![BigInt::from(-9), BigInt::zero(), BigInt::from(4)];
        let t = Instant::now();
        let s2 = a.sign_of_poly(&q2);
        let us2 = t.elapsed().as_micros();
        // a same-degree probe: x^n - 3
        let mut qn = vec![BigInt::zero(); n + 1];
        qn[0] = BigInt::from(-3);
        qn[n] = BigInt::one();
        let t = Instant::now();
        let sn = a.sign_of_poly(&qn);
        let usn = t.elapsed().as_micros();
        println!("{n:>5} {us2:>14} {usn:>14} {:>6}", format!("{s2:?}/{sn:?}"));
    }
    println!("load: {}", load());
}

/// ROW 2 of the campaign's cost table: build a 13-interval set with degree-`d`
/// endpoints, then one intersection step on it.
#[test]
fn av_env_build_13_by_endpoint_degree() {
    // Measurement harness, not a regression (the gate forbids disabled
    // tests): no-ops unless opted in (AY_LIA_HOT_LOOP_ITERS class).
    if std::env::var_os("AY_NRA_PROFILE").is_none() {
        return;
    }
    println!("\n== ROW 2: build a 13-interval set with degree-d endpoints ==");
    println!("load: {}", load());
    println!(
        "{:>5} {:>14} {:>16} {:>10}",
        "deg", "build us", "intersect us", "len"
    );
    for n in [2usize, 3, 4, 6, 8, 10, 12, 16, 20, 24, 32, 40, 48, 64] {
        let Some(parts) = deg_set(13, n, 1) else {
            println!("{n:>5}   could not build endpoints");
            continue;
        };
        let t = Instant::now();
        let s = OIAlgSet::from_parts(&parts);
        let bus = t.elapsed().as_micros();
        let Some(s) = s else {
            println!("{n:>5} {bus:>14}   BUILD DECLINED");
            continue;
        };
        // a second set, shifted by one root, to intersect against
        let Some(parts2) = deg_set(13, n, 2) else {
            continue;
        };
        let Some(s2) = OIAlgSet::from_parts(&parts2) else {
            continue;
        };
        let t = Instant::now();
        let r = s.intersect(&s2);
        let ius = t.elapsed().as_micros();
        println!(
            "{n:>5} {bus:>14} {ius:>16} {:>10}",
            r.map(|x| x.len().to_string()).unwrap_or("DECLINED".into())
        );
    }
    println!("load: {}", load());
}

/// ROW 3: `normalize` a large set, pre-sorted vs shuffled, at IRREGULAR sizes.
#[test]
fn av_env_normalize_order() {
    // Measurement harness, not a regression (the gate forbids disabled
    // tests): no-ops unless opted in (AY_LIA_HOT_LOOP_ITERS class).
    if std::env::var_os("AY_NRA_PROFILE").is_none() {
        return;
    }
    println!("\n== ROW 3: normalize by size and input order (degree-2 endpoints) ==");
    println!("load: {}", load());
    println!("{:>6} {:>14} {:>14}", "n", "sorted us", "shuffled us");
    for n in [37usize, 73, 128, 173, 256] {
        let Some(parts) = deg_set(n, 2, 1) else {
            continue;
        };
        let t = Instant::now();
        let a = OIAlgSet::from_parts(&parts);
        let sus = t.elapsed().as_micros();
        // deterministic shuffle
        let mut sh = parts.clone();
        let mut st = 0x1234_5678u64;
        for i in (1..sh.len()).rev() {
            st ^= st << 13;
            st ^= st >> 7;
            st ^= st << 17;
            let j = (st % (i as u64 + 1)) as usize;
            sh.swap(i, j);
        }
        let t = Instant::now();
        let b = OIAlgSet::from_parts(&sh);
        let hus = t.elapsed().as_micros();
        println!(
            "{n:>6} {sus:>14} {hus:>14}   sorted={:?} shuffled={:?}",
            a.as_ref().map(OIAlgSet::len),
            b.as_ref().map(OIAlgSet::len)
        );
        assert_eq!(
            a.as_ref().map(OIAlgSet::len),
            b.as_ref().map(OIAlgSet::len),
            "sorted and shuffled input must normalize to the same set"
        );
    }
    println!("load: {}", load());
}

/// A REALISTIC sequence at IRREGULAR sizes: build, intersect a chain,
/// complement, pick — degree-2 and degree-4 endpoints.
#[test]
fn av_env_realistic_irregular() {
    // Measurement harness, not a regression (the gate forbids disabled
    // tests): no-ops unless opted in (AY_LIA_HOT_LOOP_ITERS class).
    if std::env::var_os("AY_NRA_PROFILE").is_none() {
        return;
    }
    println!("\n== REALISTIC SEQUENCE at irregular sizes ==");
    println!("load: {}", load());
    println!(
        "{:>6} {:>5} {:>12} {:>14} {:>12} {:>10} {:>12}",
        "n", "deg", "build us", "5x inter us", "compl us", "pick us", "TOTAL us"
    );
    for (n, d) in [
        (11usize, 2usize),
        (37, 2),
        (73, 2),
        (173, 2),
        (11, 3),
        (37, 3),
        (11, 4),
        (37, 4),
    ] {
        let Some(parts) = deg_set(n, d, 1) else {
            continue;
        };
        let whole = Instant::now();
        let t = Instant::now();
        let Some(mut acc) = OIAlgSet::from_parts(&parts) else {
            println!("{n:>6} {d:>5}   BUILD DECLINED");
            continue;
        };
        let bus = t.elapsed().as_micros();
        let t = Instant::now();
        let mut ok = true;
        for k in 0..5i32 {
            let Some(p2) = deg_set(n, d, k + 2) else {
                ok = false;
                break;
            };
            let Some(s2) = OIAlgSet::from_parts(&p2) else {
                ok = false;
                break;
            };
            match acc.intersect(&s2) {
                Some(v) => acc = v,
                None => {
                    ok = false;
                    break;
                }
            }
        }
        let ius = t.elapsed().as_micros();
        if !ok {
            println!("{n:>6} {d:>5} {bus:>12}   INTERSECT DECLINED");
            continue;
        }
        let t = Instant::now();
        let c = acc.complement();
        let cus = t.elapsed().as_micros();
        let t = Instant::now();
        let p = acc.pick();
        let pus = t.elapsed().as_micros();
        let tot = whole.elapsed().as_micros();
        println!("{n:>6} {d:>5} {bus:>12} {ius:>14} {cus:>12} {pus:>10} {tot:>12}   len={} compl={:?} pick={}", acc.len(), c.map(|x| x.len()), p.is_some());
    }
    println!("load: {}", load());
}

/// Where does the DECLINE at high endpoint degree come from? Same probe on
/// both builds.
#[test]
fn av_env_decline_boundary() {
    // Measurement harness, not a regression (the gate forbids disabled
    // tests): no-ops unless opted in (AY_LIA_HOT_LOOP_ITERS class).
    if std::env::var_os("AY_NRA_PROFILE").is_none() {
        return;
    }
    println!("\n== DECLINE boundary by endpoint degree ==");
    println!("load: {}", load());
    println!(
        "{:>5} {:>10} {:>14} {:>12} {:>12}",
        "deg", "endpoints", "cmp_anum", "cmp us", "from_parts"
    );
    for n in [16usize, 20, 22, 23, 24, 26, 32] {
        let a = shifted_root(0, n, 2);
        let b = shifted_root(1, n, 2);
        let built = a.is_some() && b.is_some();
        let (verdict, us) = match (&a, &b) {
            (Some(x), Some(y)) => {
                let t = Instant::now();
                let r = x.cmp_anum(y);
                (format!("{r:?}"), t.elapsed().as_micros())
            }
            _ => ("n/a".to_string(), 0),
        };
        let fp = deg_set(13, n, 1)
            .and_then(|p| OIAlgSet::from_parts(&p))
            .map(|s| s.len().to_string())
            .unwrap_or_else(|| "DECLINED".to_string());
        println!("{n:>5} {built:>10} {verdict:>14} {us:>12} {fp:>12}");
    }
    println!("load: {}", load());
}

/// CHEAP decisive probe: does `from_parts` decline at the SAME degree on both
/// builds? Uses tiny sets so pristine can be measured too.
#[test]
fn av_env_decline_small() {
    // Measurement harness, not a regression (the gate forbids disabled
    // tests): no-ops unless opted in (AY_LIA_HOT_LOOP_ITERS class).
    if std::env::var_os("AY_NRA_PROFILE").is_none() {
        return;
    }
    println!("\n== from_parts DECLINE, small sets (both builds) ==");
    println!("load: {}", load());
    println!("{:>5} {:>4} {:>12} {:>12}", "deg", "k", "result", "us");
    for n in [12usize, 16, 18, 20, 21, 22, 24, 32] {
        for k in [1usize, 2, 3] {
            let Some(parts) = deg_set(k, n, 1) else {
                println!("{n:>5} {k:>4} {:>12}", "NO-ENDPTS");
                continue;
            };
            let t = Instant::now();
            let r = OIAlgSet::from_parts(&parts);
            let us = t.elapsed().as_micros();
            println!(
                "{n:>5} {k:>4} {:>12} {us:>12}",
                r.map(|s| s.len().to_string())
                    .unwrap_or_else(|| "DECLINED".into())
            );
        }
    }
    println!("load: {}", load());
}

/// SPIN ATTEMPT: drive the separation exponent up to and past the declared
/// 8,192-bit ceiling and demand a bounded answer or a clean decline — never a
/// hang. Also the exact k=13 decline case, on whichever build runs this.
#[test]
fn av_spin_attempt() {
    // Measurement harness, not a regression (the gate forbids disabled
    // tests): no-ops unless opted in (AY_LIA_HOT_LOOP_ITERS class).
    if std::env::var_os("AY_NRA_PROFILE").is_none() {
        return;
    }
    println!("\n== SPIN ATTEMPT: exponent driven toward MAX_SEPARATION_BITS ==");
    println!("load: {}", load());
    println!(
        "{:>7} {:>14} {:>12} {:>10}",
        "Nbits", "cmp verdict", "us", "sign us"
    );
    for nb in [100u32, 500, 1000, 1300, 1330, 1360, 1400, 2000, 4000] {
        // x^2 - 2   vs   N^2 x^2 - (2 N^2 + 1),  N = 2^nb
        let n2: BigInt = BigInt::one() << (2 * nb);
        let pa = vec![BigInt::from(-2), BigInt::zero(), BigInt::one()];
        let c0: BigInt = -(&n2 * BigInt::from(2) + BigInt::one());
        let pb = vec![c0, BigInt::zero(), n2];
        let iva = OBqInterval::new(
            &OBq::from_int(BigInt::one()),
            &OBq::from_int(BigInt::from(2)),
        );
        let Some(iva) = iva else { continue };
        let (Some(a), Some(b)) = (
            ODyadicAnum::from_poly_interval(&pa, &iva),
            ODyadicAnum::from_poly_interval(&pb, &iva),
        ) else {
            println!("{nb:>7}   could not construct");
            continue;
        };
        let t = Instant::now();
        let r = a.cmp_anum(&b);
        let us = t.elapsed().as_micros();
        let t = Instant::now();
        let s = a.sign_of_poly(&pb);
        let sus = t.elapsed().as_micros();
        println!(
            "{nb:>7} {:>14} {us:>12} {sus:>10}   sign={s:?}",
            format!("{r:?}")
        );
        // soundness: sqrt(2) < sqrt(2 + 2^-2nb) always
        if let Some(o) = r {
            assert_eq!(o, std::cmp::Ordering::Less, "WRONG ORDER at nb={nb}");
        }
        if let Some(v) = s {
            assert_eq!(v, -1, "WRONG SIGN at nb={nb}");
        }
    }
    println!("load: {}", load());
}

/// The exact k=13 / degree boundary, one degree at a time.
#[test]
fn av_env_k13_boundary() {
    // Measurement harness, not a regression (the gate forbids disabled
    // tests): no-ops unless opted in (AY_LIA_HOT_LOOP_ITERS class).
    if std::env::var_os("AY_NRA_PROFILE").is_none() {
        return;
    }
    println!("\n== k=13 from_parts boundary ==");
    println!("load: {}", load());
    for n in [20usize, 21, 22] {
        let Some(parts) = deg_set(13, n, 1) else {
            continue;
        };
        let t = Instant::now();
        let r = OIAlgSet::from_parts(&parts);
        println!(
            "  deg {n}: {} in {} us",
            r.map(|s| s.len().to_string())
                .unwrap_or_else(|| "DECLINED".into()),
            t.elapsed().as_micros()
        );
    }
    println!("load: {}", load());
}

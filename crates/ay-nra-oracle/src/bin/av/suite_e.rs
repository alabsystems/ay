// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `av` to preserve existing item DefPaths.

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
    suite_e1();
    suite_e2();
    suite_e3();
    println!("(load after: {})", load_avg());
}

const E_PRIMES: [i64; 9] = [2, 3, 5, 7, 11, 13, 17, 19, 23];

fn suite_e1() {
    // E1 — nested quadratic irrationals: sqrt(2)+sqrt(3)+sqrt(5)+... Degrees
    // double every step, which is the cheapest possible growth, so this is the
    // most favourable chain that exists. It is also exactly the shape a CAD
    // sample point takes.
    println!("\n E1: sqrt(p_1) + sqrt(p_2) + ... (degree DOUBLES per step)");
    println!("  step  operand      degree  coeffbits  interval k     step us   outcome");
    let mut acc = root_of(2, E_PRIMES[0]).unwrap();
    for (i, p) in E_PRIMES.iter().enumerate().skip(1) {
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
}

fn suite_e2() {
    // E2 — MIXED degrees, the realistic nlsat shape: a low-degree sample point
    // combined with the coefficients of a projection polynomial.
    println!("\n E2: mixed-degree chain, acc(deg 2) op root(deg 3,5,7,...)");
    println!("  step  op  operand deg   result deg   coeffbits     step us   outcome");
    let mut acc = root_of(2, 2).unwrap();
    for (i, d) in [3usize, 5, 7, 11, 13].iter().enumerate() {
        let Some(next) = root_of(*d, E_PRIMES[(i + 1) % E_PRIMES.len()]) else {
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
}

fn suite_e3() {
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

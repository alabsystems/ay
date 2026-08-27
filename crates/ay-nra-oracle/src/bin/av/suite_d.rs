// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `av` to preserve existing item DefPaths.

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
            if let Err(e) = z3.recycle() {
                eprintln!("FATAL: could not recycle the reference libz3 context: {e}");
                std::process::exit(2);
            }
        }
        let (p, s) = gen_poly(&mut rng);
        let Some(norm) = anum_normalize_defining(&p) else {
            continue;
        };
        let Some(b) = anum_root_separation_exponent(&norm) else {
            continue;
        };
        let Some(roots) = z3.roots(&rats(&norm)) else {
            z3_error(&format!("D/case{case}"), "isolating roots");
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
                    z3_error(&format!("D/case{case}"), "bracketing a root");
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
            reference_okc();
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

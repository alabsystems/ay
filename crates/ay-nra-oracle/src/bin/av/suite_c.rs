// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `av` to preserve existing item DefPaths.

// ==========================================================================
// SUITE C — arithmetic and sign, randomized against z3
// ==========================================================================

struct CCase {
    pa: Vec<BigInt>,
    pb: Vec<BigInt>,
    sa: &'static str,
    sb: &'static str,
    va: Ast,
    vb: Ast,
    a: ODyadicAnum,
    b: ODyadicAnum,
}

fn generate_c_case(z3: &Z3, rng: &mut Rng) -> Result<Option<CCase>, &'static str> {
    let (pa, sa) = gen_poly(rng);
    let (pb, sb) = gen_poly(rng);
    let ra = z3.roots(&rats(&pa)).ok_or("isolating roots of pa")?;
    let rb = z3.roots(&rats(&pb)).ok_or("isolating roots of pb")?;
    if ra.is_empty() || rb.is_empty() {
        return Ok(None);
    }
    let va = ra[rng.below(ra.len() as u64) as usize];
    let vb = rb[rng.below(rb.len() as u64) as usize];
    let Some((a, _, _)) = build_at(z3, &pa, va, rng)? else {
        return Ok(None);
    };
    let Some((b, _, _)) = build_at(z3, &pb, vb, rng)? else {
        return Ok(None);
    };
    if z3.errored() {
        return Err("building AY arithmetic operands");
    }
    Ok(Some(CCase {
        pa,
        pb,
        sa,
        sb,
        va,
        vb,
        a,
        b,
    }))
}

fn check_c_arithmetic(z3: &Z3, case: u64, input: &CCase, n_ok: &mut u64, n_dec: &mut u64) {
    for is_add in [true, false] {
        let diag = anum_binop_diag(&input.a, &input.b, is_add);
        let must = !matches!(diag, OAnumOpDiag::OverCeiling | OAnumOpDiag::Degenerate);
        let label = if is_add { "add" } else { "mul" };
        let name = format!("C/case{case}/{label}");
        let got = {
            let (x, y) = (input.a.clone(), input.b.clone());
            with_watchdog(
                &name,
                120,
                move || if is_add { x.add(&y) } else { x.mul(&y) },
            )
        };
        let Some(got) = got else { continue };
        let Some(r) = got else {
            if must {
                *n_dec += 1;
                bad(
                    &name,
                    format!(
                        "DECLINED though diag says {diag:?}\n      pa[{}]={}\n      pb[{}]={}",
                        input.sa,
                        render(&input.pa),
                        input.sb,
                        render(&input.pb)
                    ),
                );
            }
            continue;
        };
        let zref = if is_add {
            z3.add(input.va, input.vb)
        } else {
            z3.mul(input.va, input.vb)
        };
        let Some(zref) = zref else {
            z3_error(&name, "reference algebraic arithmetic");
            continue;
        };
        match z3_of(z3, &r) {
            Ok(ast) => {
                let Some(equal) = z3.eq(ast, zref) else {
                    z3_error(&name, "comparing arithmetic results");
                    continue;
                };
                *n_ok += 1;
                reference_okc();
                if !equal {
                    bad(
                        &name,
                        format!(
                            "AY != z3\n      pa[{}]={}\n      pb[{}]={}\n      AY poly={}",
                            input.sa,
                            render(&input.pa),
                            input.sb,
                            render(&input.pb),
                            r.poly_coeffs().map_or("<rat>".into(), |c| render(&c))
                        ),
                    );
                }
            }
            Err(false) => bad(
                &name,
                format!(
                    "AY result interval does not bracket exactly ONE root of AY's own polynomial\n      pa[{}]={}\n      pb[{}]={}",
                    input.sa,
                    render(&input.pa),
                    input.sb,
                    render(&input.pb)
                ),
            ),
            Err(true) => z3_error(&name, "naming AY's arithmetic result"),
        }
    }
}

fn check_c_signs(z3: &Z3, case: u64, input: &CCase) {
    for (lbl, q) in [
        ("q=pa", input.pa.clone()),
        ("q=pa*pb", pmul(&input.pa, &input.pb)),
        ("q=pb", input.pb.clone()),
    ] {
        if q.is_empty() {
            continue;
        }
        let name = format!("C/case{case}/sign/{lbl}");
        let Some(s) = ({
            let x = input.a.clone();
            let qq = q.clone();
            with_watchdog(&name, 60, move || x.sign_of_poly(&qq))
        }) else {
            continue;
        };
        let Some(s) = s else {
            bad(&name, "sign_of_poly DECLINED".into());
            continue;
        };
        let Some(zs) = z3.eval_sign(&rats(&q), input.va) else {
            z3_error(&name, "evaluating a polynomial sign");
            continue;
        };
        reference_okc();
        if s != zs {
            bad(
                &name,
                format!("AY sign {s}, z3 sign {zs}, q={}", render(&q)),
            );
        }
    }
}

fn check_c_neg(z3: &Z3, case: u64, input: &CCase) {
    let name = format!("C/case{case}/neg");
    let Some(Some(na)) = ({
        let x = input.a.clone();
        with_watchdog(&name, 60, move || x.neg())
    }) else {
        return;
    };
    let ast = match z3_of(z3, &na) {
        Ok(ast) => ast,
        Err(true) => {
            z3_error(&name, "naming AY's negated result");
            return;
        }
        Err(false) => {
            bad(
                &name,
                "AY negated result interval does not bracket exactly one root of its polynomial"
                    .into(),
            );
            return;
        }
    };
    let Some(zero) = z3.rational(&BigRational::zero()) else {
        z3_error(&name, "building zero");
        return;
    };
    let Some(sum) = z3.add(ast, input.va) else {
        z3_error(&name, "adding a value to its negation");
        return;
    };
    let Some(equal) = z3.eq(sum, zero) else {
        z3_error(&name, "checking the negation identity");
        return;
    };
    reference_okc();
    if !equal {
        bad(
            &name,
            format!("a + (-a) != 0, pa[{}]={}", input.sa, render(&input.pa)),
        );
    }
}

fn suite_c(z3: &mut Z3, cases: u64, seed: u64) {
    println!("\n=== SUITE C: arith / sign / neg differential, {cases} cases, seed {seed} ===");
    let mut rng = Rng(seed);
    let mut n_ok = 0u64;
    let mut n_dec = 0u64;
    for case in 0..cases {
        if case % 200 == 0 {
            if let Err(e) = z3.recycle() {
                eprintln!("FATAL: could not recycle the reference libz3 context: {e}");
                std::process::exit(2);
            }
        }
        let input = match generate_c_case(z3, &mut rng) {
            Ok(Some(input)) => input,
            Ok(None) => continue,
            Err(operation) => {
                z3_error(&format!("C/case{case}"), operation);
                continue;
            }
        };
        check_c_arithmetic(z3, case, &input, &mut n_ok, &mut n_dec);
        check_c_signs(z3, case, &input);
        check_c_neg(z3, case, &input);
    }
    println!("  arith compared {n_ok}, unexpected declines {n_dec}");
}

fn z3_of(z3: &Z3, a: &ODyadicAnum) -> Result<Ast, bool> {
    if let Some(r) = a.to_rational() {
        return z3.rational(&r).ok_or(true);
    }
    let coeffs = rats(&a.poly_coeffs().ok_or(false)?);
    let roots = z3.roots(&coeffs).ok_or(true)?;
    let i = a.interval().ok_or(false)?;
    let lo = z3.rational(&i.lo().to_rational()).ok_or(true)?;
    let hi = z3.rational(&i.hi().to_rational()).ok_or(true)?;
    let mut found: Option<Ast> = None;
    for r in roots {
        if z3.gt(r, lo).ok_or(true)? && z3.lt(r, hi).ok_or(true)? {
            if found.is_some() {
                return Err(false);
            }
            found = Some(r);
        }
    }
    found.ok_or(false)
}

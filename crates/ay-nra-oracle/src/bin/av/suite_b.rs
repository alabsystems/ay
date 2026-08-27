// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `av` to preserve existing item DefPaths.

struct BCase {
    pa: Vec<BigInt>,
    pb: Vec<BigInt>,
    sa: &'static str,
    sb: &'static str,
    a: ODyadicAnum,
    b: ODyadicAnum,
    al: BigRational,
    ah: BigRational,
    bl: BigRational,
    bh: BigRational,
    z3_ord: Ordering,
}

fn generate_b_case(z3: &Z3, rng: &mut Rng) -> Result<Option<BCase>, &'static str> {
    let (pa, sa) = gen_poly(rng);
    let (pb, sb) = gen_poly(rng);
    let ra = z3.roots(&rats(&pa)).ok_or("isolating roots of pa")?;
    let rb = z3.roots(&rats(&pb)).ok_or("isolating roots of pb")?;
    if ra.is_empty() || rb.is_empty() {
        return Ok(None);
    }
    let va = ra[rng.below(ra.len() as u64) as usize];
    let vb = rb[rng.below(rb.len() as u64) as usize];
    let Some((a, al, ah)) = build_at(z3, &pa, va, rng)? else {
        return Ok(None);
    };
    let Some((b, bl, bh)) = build_at(z3, &pb, vb, rng)? else {
        return Ok(None);
    };
    if z3.errored() {
        return Err("building AY comparison operands");
    }
    let z3_ord = if z3.eq(va, vb).ok_or("testing root equality")? {
        Ordering::Equal
    } else if z3.lt(va, vb).ok_or("ordering roots with lt")? {
        Ordering::Less
    } else if z3.gt(va, vb).ok_or("ordering roots with gt")? {
        Ordering::Greater
    } else {
        return Err("establishing a total root ordering");
    };
    Ok(Some(BCase {
        pa,
        pb,
        sa,
        sb,
        a,
        b,
        al,
        ah,
        bl,
        bh,
        z3_ord,
    }))
}

fn recycle_b_context(z3: &mut Z3, case: u64) {
    if case % 200 == 0 {
        if let Err(e) = z3.recycle() {
            eprintln!("FATAL: could not recycle the reference libz3 context: {e}");
            std::process::exit(2);
        }
    }
}

fn next_b_case(z3: &Z3, rng: &mut Rng, case: u64) -> Option<BCase> {
    match generate_b_case(z3, rng) {
        Ok(input) => input,
        Err(operation) => {
            z3_error(&format!("B/case{case}"), operation);
            None
        }
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
        recycle_b_context(z3, case);
        let Some(input) = next_b_case(z3, &mut rng, case) else {
            continue;
        };
        let BCase {
            pa,
            pb,
            sa,
            sb,
            a,
            b,
            al,
            ah,
            bl,
            bh,
            z3_ord,
        } = input;
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
                reference_okc();
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

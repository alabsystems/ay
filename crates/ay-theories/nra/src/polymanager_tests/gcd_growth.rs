// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#[test]
fn coefficient_growth_of_the_two_gcds_is_measured_not_assumed(
) -> Result<(), Box<dyn std::error::Error>> {
    let mut c = Ctx::new();
    let g = {
        let a = c.t(1, 2, 0, 0);
        let b = c.t(-3, 1, 1, 0);
        let d = c.t(7, 0, 0, 1);
        let s = c.add(&a, &b);
        c.add(&s, &d)
    };
    let mut u = g.clone();
    let mut v = g.clone();
    const OVERFLOW: &str = "cofactor coefficient overflows i64";
    for k in 1..=4i64 {
        let fa = c.t(k, 1, 0, 0);
        let fb = c.t(k.checked_add(1).ok_or(OVERFLOW)?, 0, 1, 0);
        let fc_coeff = k.checked_mul(3).and_then(|m| m.checked_sub(1));
        let fc = c.c(fc_coeff.ok_or(OVERFLOW)?);
        let f = c.add(&fa, &fb);
        let f = c.add(&f, &fc);
        u = c.mul(&u, &f);
        let ha = c.t(k.checked_add(2).ok_or(OVERFLOW)?, 1, 0, 0);
        let hb = c.t(k.checked_neg().ok_or(OVERFLOW)?, 0, 0, 1);
        let hc_coeff = k.checked_mul(5).and_then(|m| m.checked_add(2));
        let hc = c.c(hc_coeff.ok_or(OVERFLOW)?);
        let h = c.add(&ha, &hb);
        let h = c.add(&h, &hc);
        v = c.mul(&v, &h);
    }
    let prs = c.m.gcd(&u, &v).unwrap();
    assert!(c.m.divides(&prs, &u) && c.m.divides(&prs, &v));
    if let Some(mg) = c.m.mod_gcd(&u, &v) {
        assert_eq!(mg, prs);
    }
    assert!(
        c.m.max_coeff_bits(&prs) <= c.m.max_coeff_bits(&u),
        "the gcd cannot be wider than the input it divides"
    );
    Ok(())
}

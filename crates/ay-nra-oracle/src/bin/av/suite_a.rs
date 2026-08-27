// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `av` to preserve existing item DefPaths.

// ==========================================================================
// SUITE A — equality and liveness, analytic ground truth
// ==========================================================================

fn suite_a() {
    println!("\n=== SUITE A: equality / liveness (analytic ground truth) ===");
    check_equal_forms();
    let s2 = check_ordering_examples();
    check_product(&s2);
    check_close_numbers();
    check_refinements(&s2);
    check_rational_corners(&s2);
}

fn check_equal_forms() {
    // sqrt(2) written six different ways. All must compare Equal to each other.
    let sqrt2_forms: Vec<(&str, Vec<BigInt>, OBqInterval)> = vec![
        ("x^2-2 on (1,2)", ints(&[-2, 0, 1]), iv(1, 2)),
        ("x^2-2 on (0,2)", ints(&[-2, 0, 1]), iv(0, 2)),
        ("x^2-2 on (1,100)", ints(&[-2, 0, 1]), iv(1, 100)),
        // (x^2-2)^2 — square-free reduction must recover x^2-2
        ("(x^2-2)^2 on (1,2)", ints(&[4, 0, -4, 0, 1]), iv(1, 2)),
        // x^4-4x^2+4 is the same polynomial written out
        ("x^4-4x^2+4 on (1,2)", ints(&[4, 0, -4, 0, 1]), iv(1, 2)),
        // (x^2-2)(x-5): a different, larger defining polynomial
        ("(x^2-2)(x-5) on (1,2)", ints(&[10, -2, -5, 1]), iv(1, 2)),
        // x^3 - 2x = x(x^2-2): shares the factor, has a root at 0 too
        ("x^3-2x on (1,2)", ints(&[0, -2, 0, 1]), iv(1, 2)),
        // (x^2-2)(x^2-3): sqrt(2) is the second of four roots
        (
            "(x^2-2)(x^2-3) on (1,3/2)",
            ints(&[6, 0, -5, 0, 1]),
            OBqInterval::new(&OBq::from_int(BigInt::one()), &OBq::new(BigInt::from(3), 1)).unwrap(),
        ),
        // 3*(x^2-2): content must be divided out
        ("3x^2-6 on (1,2)", ints(&[-6, 0, 3]), iv(1, 2)),
        // -(x^2-2): negative leading coefficient
        ("-x^2+2 on (1,2)", ints(&[2, 0, -1]), iv(1, 2)),
    ];
    let mut built: Vec<(&str, ODyadicAnum)> = Vec::new();
    for (label, p, i) in &sqrt2_forms {
        match ODyadicAnum::from_poly_interval(p, i) {
            Some(a) => built.push((label, a)),
            None => bad(
                "A/construct",
                format!("{label}: from_poly_interval REFUSED"),
            ),
        }
    }
    for i in 0..built.len() {
        for j in 0..built.len() {
            let (na, a) = (built[i].0, built[i].1.clone());
            let (nb, b) = (built[j].0, built[j].1.clone());
            let name = format!("A/eq[{na} vs {nb}]");
            let t = Instant::now();
            let r = with_watchdog(&name, 20, move || a.cmp_anum_traced(&b));
            let el = t.elapsed().as_millis();
            match r {
                Some(Some((Ordering::Equal, tr))) => {
                    okc();
                    if !tr.equal_by_certificate {
                        bad(
                            &name,
                            "Equal but NOT by certificate (would refine forever on a harder input)"
                                .into(),
                        );
                    }
                    if tr.steps_a != 0 || tr.steps_b != 0 {
                        bad(
                            &name,
                            format!("certificate path bisected {}/{}", tr.steps_a, tr.steps_b),
                        );
                    }
                    if el > 2000 {
                        bad(&name, format!("took {el} ms"));
                    }
                }
                Some(Some((o, _))) => bad(&name, format!("answered {o:?}, truth is Equal")),
                Some(None) => bad(&name, "DECLINED on two equal numbers".into()),
                None => {}
            }
        }
    }
}

fn check_ordering_examples() -> ODyadicAnum {
    // sqrt(2) vs -sqrt(2): conjugates of the same polynomial, must be Greater.
    let pos = ODyadicAnum::from_poly_interval(&ints(&[-2, 0, 1]), &iv(1, 2)).unwrap();
    let neg = ODyadicAnum::from_poly_interval(&ints(&[-2, 0, 1]), &iv(-2, -1)).unwrap();
    check_cmp("A/conjugates", &pos, &neg, Ordering::Greater);
    check_cmp("A/conjugates-rev", &neg, &pos, Ordering::Less);

    // OVERLAPPING intervals, distinct numbers: sqrt(2) and sqrt(3) both in (1,2).
    let s2 = ODyadicAnum::from_poly_interval(&ints(&[-2, 0, 1]), &iv(1, 2)).unwrap();
    let s3 = ODyadicAnum::from_poly_interval(&ints(&[-3, 0, 1]), &iv(1, 2)).unwrap();
    check_cmp("A/overlap-distinct", &s2, &s3, Ordering::Less);

    // sqrt(2) vs -sqrt(2) through DIFFERENT polynomials that share the factor.
    let s2b = ODyadicAnum::from_poly_interval(&ints(&[10, -2, -5, 1]), &iv(1, 2)).unwrap();
    check_cmp("A/shared-factor-neg", &s2b, &neg, Ordering::Greater);
    s2
}

fn check_product(s2: &ODyadicAnum) {
    // sqrt(2)*sqrt(2) == 2. The DEFERRED minimality case: the answer is an
    // AlgCell over z^2-4, not Rational(2). Comparison must still say Equal.
    let prod = with_watchdog("A/sqrt2sq", 30, {
        let a = s2.clone();
        let b = s2.clone();
        move || a.mul(&b)
    })
    .flatten();
    match prod {
        Some(p) => {
            okc();
            check_cmp_rat(
                "A/sqrt2*sqrt2==2",
                &p,
                &BigRational::from_integer(BigInt::from(2)),
                Ordering::Equal,
            );
            println!(
                "  note: sqrt2*sqrt2 -> is_rational={} degree={} poly={}",
                p.is_rational(),
                p.degree(),
                p.poly_coeffs().map_or("<rational>".into(), |c| render(&c))
            );
        }
        None => bad("A/sqrt2sq", "mul returned None".into()),
    }
}

fn check_close_numbers() {
    // EXTREMELY CLOSE BUT DISTINCT.
    // alpha = sqrt(2); beta = sqrt(2 + 1/n^2) = root of n^2 x^2 - (2n^2+1).
    for e in [10u32, 20, 30, 40, 60, 90, 128] {
        let n = BigInt::one() << e; // n = 2^e
        let n2 = &n * &n;
        let p2: Vec<BigInt> = vec![
            -(&n2 * BigInt::from(2) + BigInt::one()),
            BigInt::zero(),
            n2.clone(),
        ];
        let a = ODyadicAnum::from_poly_interval(&ints(&[-2, 0, 1]), &iv(1, 2)).unwrap();
        let Some(b) = ODyadicAnum::from_poly_interval(&p2, &iv(1, 2)) else {
            bad("A/close", format!("e={e}: construct failed"));
            continue;
        };
        // |beta - alpha| ~ 2^-(2e+2). Truth: alpha < beta.
        let name = format!("A/close-2^-{}", 2 * e + 2);
        let t = Instant::now();
        let r = with_watchdog(&name, 60, {
            let (a, b) = (a.clone(), b.clone());
            move || a.cmp_anum_traced(&b)
        });
        let el = t.elapsed().as_millis();
        match r {
            Some(Some((o, tr))) => {
                okc();
                if o != Ordering::Less {
                    bad(&name, format!("AY says {o:?}, truth is Less"));
                } else {
                    println!(
                        "  ok {name}: Less  sep_bits={:?} steps={}/{} bound={} {} ms",
                        tr.sep_bits, tr.steps_a, tr.steps_b, tr.bound, el
                    );
                }
            }
            Some(None) => bad(&name, "DECLINED".into()),
            None => {}
        }
    }
}

fn check_refinements(s2: &ODyadicAnum) {
    // A number vs its own refinement at many depths (same value, different iv).
    for k in [1u32, 5, 20, 64, 200, 1000] {
        let name = format!("A/refine-eq-k{k}");
        let a = s2.clone();
        let r = with_watchdog(&name, 30, move || {
            a.refine(&OBq::inv_two_pow(k))
                .map(|rf| (a.cmp_anum_traced(&rf), rf.interval().map(|i| i.max_k())))
        });
        match r {
            Some(Some((Some((Ordering::Equal, tr)), mk))) => {
                okc();
                if !tr.equal_by_certificate {
                    bad(&name, "not by certificate".into());
                }
                let _ = mk;
            }
            Some(Some((Some((o, _)), _))) => bad(&name, format!("refinement changed value: {o:?}")),
            Some(Some((None, _))) => bad(&name, "cmp DECLINED against own refinement".into()),
            Some(None) => bad(&name, "refine returned None".into()),
            None => {}
        }
    }
}

fn check_rational_corners(s2: &ODyadicAnum) {
    // Rational / integer / zero / negative corners.
    let zero = ODyadicAnum::rational(BigRational::zero());
    let one = ODyadicAnum::rational(BigRational::one());
    let negthird = ODyadicAnum::rational(BigRational::new(BigInt::from(-1), BigInt::from(3)));
    check_cmp("A/zero-vs-zero", &zero, &zero.clone(), Ordering::Equal);
    check_cmp("A/zero-vs-one", &zero, &one, Ordering::Less);
    check_cmp("A/neg-vs-zero", &negthird, &zero, Ordering::Less);
    // The number zero in ALGEBRAIC form: root of x^3-x in (-1/2, 1/2).
    if let Some(z_alg) = ODyadicAnum::from_poly_interval(
        &ints(&[0, -1, 0, 1]),
        &OBqInterval::new(&OBq::new(BigInt::from(-1), 1), &OBq::new(BigInt::one(), 1)).unwrap(),
    ) {
        check_cmp("A/alg-zero-vs-rat-zero", &z_alg, &zero, Ordering::Equal);
        check_cmp("A/alg-zero-vs-one", &z_alg, &one, Ordering::Less);
        // multiplying by it must give exactly zero
        match z_alg.mul(&s2) {
            Some(p) => {
                check_cmp_rat(
                    "A/alg-zero*sqrt2",
                    &p,
                    &BigRational::zero(),
                    Ordering::Equal,
                );
            }
            None => bad("A/alg-zero*sqrt2", "mul returned None".into()),
        }
    } else {
        bad("A/alg-zero", "could not build algebraic zero".into());
    }

    // An integer in algebraic form: root of x^2-4 in (1,3) is 2.
    if let Some(two_alg) = ODyadicAnum::from_poly_interval(&ints(&[-4, 0, 1]), &iv(1, 3)) {
        check_cmp_rat(
            "A/alg-two==2",
            &two_alg,
            &BigRational::from_integer(BigInt::from(2)),
            Ordering::Equal,
        );
        println!(
            "  note: root of x^2-4 in (1,3): is_rational={}",
            two_alg.is_rational()
        );
    }
}

fn check_cmp(name: &str, a: &ODyadicAnum, b: &ODyadicAnum, want: Ordering) {
    let (x, y) = (a.clone(), b.clone());
    let r = with_watchdog(name, 30, move || x.cmp_anum(&y));
    match r {
        Some(Some(o)) => {
            okc();
            if o != want {
                bad(name, format!("AY says {o:?}, truth is {want:?}"));
            }
        }
        Some(None) => bad(name, "DECLINED".into()),
        None => {}
    }
}

fn check_cmp_rat(name: &str, a: &ODyadicAnum, r: &BigRational, want: Ordering) {
    check_cmp(name, a, &ODyadicAnum::rational(r.clone()), want);
}

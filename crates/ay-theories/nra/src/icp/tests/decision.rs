// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `icp::tests` to preserve existing test FQNs.

/// End-to-end regression for the triangle-by-three-distances system at
/// the theory level: the SAT witness is irrational (y3 = 3*sqrt(55)/4),
/// so the verdict must come from the Krawczyk existence certificate. Also
/// guards the endpoint-denominator rounding: without
/// `round_interval_outward` this system exhibits exponential bignum
/// growth through the k=1 projections and takes minutes instead of
/// milliseconds.
#[test]
fn icp_triangle_three_distances_certifies_sat() {
    use ay_core::term::TermStore;
    use ay_core::Sort;
    let mut terms = TermStore::new();
    let x2 = terms.mk_var("x2", Sort::Real);
    let x3 = terms.mk_var("x3", Sort::Real);
    let y3 = terms.mk_var("y3", Sort::Real);
    let c100 = terms.mk_rational(rat(100));
    let c64 = terms.mk_rational(rat(64));
    let c49 = terms.mk_rational(rat(49));
    let c0 = terms.mk_rational(rat(0));
    let x2sq = terms.mk_mul(vec![x2, x2]);
    let x3sq = terms.mk_mul(vec![x3, x3]);
    let y3sq = terms.mk_mul(vec![y3, y3]);
    let a1 = terms.mk_eq(x2sq, c100);
    let s2 = terms.mk_add(vec![x3sq, y3sq]);
    let a2 = terms.mk_eq(s2, c64);
    let d = terms.mk_sub(vec![x3, x2]);
    let dsq = terms.mk_mul(vec![d, d]);
    let s3 = terms.mk_add(vec![dsq, y3sq]);
    let a3 = terms.mk_eq(s3, c49);
    let a4 = terms.mk_gt(y3, c0);
    let mut solver = NraSolver::new(&terms);
    use ay_core::TheorySolver;
    solver.assert_literal(a1, true);
    solver.assert_literal(a2, true);
    solver.assert_literal(a3, true);
    solver.assert_literal(a4, true);
    let res = solver.try_icp_branch_and_prune();
    let UniResult::SatAlgebraic(witnesses) = res else {
        panic!(
            "triangle 10/8/7 must be certified SAT via the Krawczyk existence \
             certificate (its witnesses are irrational)"
        );
    };
    // The full witness assignment must be carried: x2 and x3 as exact
    // rationals, y3 as the exact algebraic root with y3^2 = 495/16
    // (y3 = 3*sqrt(55)/4).
    let val = witnesses
        .iter()
        .find_map(|(v, w)| match (v, w) {
            (v, UniWitness::Algebraic(a)) if *v == y3 => Some(a.clone()),
            _ => None,
        })
        .expect("y3 must carry an exact algebraic witness");
    match val.try_mul(&val).expect("same algebraic point") {
        crate::algebraic::RealScalar::Rational(sq) => {
            assert_eq!(
                sq,
                BigRational::new(BigInt::from(495), BigInt::from(16)),
                "y3^2 must be exactly 495/16"
            );
        }
        crate::algebraic::RealScalar::Algebraic(_) => {
            panic!("y3^2 must reduce to the exact rational 495/16")
        }
    }
}

/// An algebraic certificate over only the parsed constraint subset must
/// not authorize SAT while any asserted atom lies outside that subset.
#[test]
fn icp_algebraic_certificate_refuses_unparsed_atoms() {
    use ay_core::term::TermStore;
    use ay_core::Sort;
    use ay_core::TheorySolver;
    let mut terms = TermStore::new();
    let x2 = terms.mk_var("x2", Sort::Real);
    let x3 = terms.mk_var("x3", Sort::Real);
    let y3 = terms.mk_var("y3", Sort::Real);
    let c100 = terms.mk_rational(rat(100));
    let c64 = terms.mk_rational(rat(64));
    let c49 = terms.mk_rational(rat(49));
    let c0 = terms.mk_rational(rat(0));
    let c1000 = terms.mk_rational(rat(1000));
    let x2sq = terms.mk_mul(vec![x2, x2]);
    let x3sq = terms.mk_mul(vec![x3, x3]);
    let y3sq = terms.mk_mul(vec![y3, y3]);
    let a1 = terms.mk_eq(x2sq, c100);
    let s2 = terms.mk_add(vec![x3sq, y3sq]);
    let a2 = terms.mk_eq(s2, c64);
    let d = terms.mk_sub(vec![x3, x2]);
    let dsq = terms.mk_mul(vec![d, d]);
    let s3 = terms.mk_add(vec![dsq, y3sq]);
    let a3 = terms.mk_eq(s3, c49);
    let a4 = terms.mk_gt(y3, c0);
    // This division is outside the parsed multivariate fragment and false
    // at the triangle witness (`10 / 5.56` is nowhere near `> 1000`).
    let quot = terms.mk_div(x2, y3);
    let a5 = terms.mk_gt(quot, c1000);
    let mut solver = NraSolver::new(&terms);
    solver.assert_literal(a1, true);
    solver.assert_literal(a2, true);
    solver.assert_literal(a3, true);
    solver.assert_literal(a4, true);
    solver.assert_literal(a5, true);

    assert!(
        solver.atom_to_multi(a5, true).is_none(),
        "x2 / y3 > 1000 must remain outside the multivariate fragment"
    );
    assert!(
        !solver.asserted_fully_parsed(),
        "the gate must observe the unparsed asserted atom"
    );

    // Build exactly the parsed subset and deliberately emulate a caller
    // that incorrectly claims complete parse coverage. The choke-point guard,
    // not caller discipline, must keep the answer fail-closed.
    let mut constraints: Vec<MultiConstraint> = Vec::new();
    for &(atom, value) in &solver.asserted {
        if let Some(MultiAtom::Constraint(c)) = solver.atom_to_multi(atom, value) {
            constraints.push(c);
        }
    }
    let mut vars: Vec<TermId> = Vec::new();
    for c in &constraints {
        for v in c.poly.variables() {
            if !vars.contains(&v) {
                vars.push(v);
            }
        }
    }
    vars.sort_unstable_by_key(|t| t.0);
    let mut root: VarBox = collect_variable_bounds(&constraints);
    for &v in &vars {
        root.entry(v).or_insert_with(Interval::whole);
    }
    assert!(
        !matches!(
            contract_box(&constraints, &vars, &mut root),
            Contraction::Refuted
        ),
        "the parsed subset alone is satisfiable"
    );

    let result = solver.branch_and_prune(
        &constraints,
        &vars,
        root,
        ParseCoverage::Complete,
        SearchAuthority::Exhaustive,
        MAX_BOXES,
    );
    let got = match result {
        UniResult::Sat(_) => "Sat",
        UniResult::SatAlgebraic(_) => "SatAlgebraic",
        UniResult::Unsat => "Unsat",
        UniResult::Unknown => "Unknown",
    };
    assert_eq!(
        got, "Unknown",
        "an algebraic certificate must not ignore an unparsed asserted atom"
    );
}

#[test]
fn matching_finds_pin_complement() {
    // Two equations over {a, b, c}: eq0 ~ {a, b}, eq1 ~ {b}. A maximum
    // matching must match eq1 -> b, eq0 -> a, leaving c as the pin.
    let a = TermId(1);
    let b = TermId(2);
    let c = TermId(3);
    let eqs = vec![vec![a, b], vec![b]];
    let vars = vec![a, b, c];
    let matched = match_eqs_to_vars(&eqs, &vars).expect("matchable");
    assert!(matched.contains(&a));
    assert!(matched.contains(&b));
    assert!(!matched.contains(&c));
}

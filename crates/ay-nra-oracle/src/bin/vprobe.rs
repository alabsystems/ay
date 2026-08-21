// Fail-open + liveness probe. Feeds `explain` inputs it cannot decide, or
// degenerate ones the in-tree oracle's generator can never build, and reports
// what comes back. A permissive answer on an undecidable input is a soundness
// defect even when no test catches it.

#![allow(unsafe_code)] // Dedicated C-ABI boundary to libz3; sites carry local invariants.

use num_bigint::BigInt;
use num_rational::BigRational as Q;
use num_traits::{One, Zero};
use std::time::Instant;

use ay_nra::oracle_api::{
    oexplain_clause_is_falsified, oexplain_clause_is_valid, oexplain_countermodel,
    oexplain_project, oexplain_relevant_pairs, oexplain_univariate, OBiPoly, OBq, OBqInterval,
    ODyadicAnum, OExplainLit, OISignCond,
};

fn bi(n: i64) -> BigInt {
    BigInt::from(n)
}
fn ints(v: &[i64]) -> Vec<BigInt> {
    v.iter().map(|&c| bi(c)).collect()
}
fn rat(n: i64) -> ODyadicAnum {
    ODyadicAnum::rational(Q::from_integer(bi(n)))
}
fn lit(id: i32, p: &[i64], c: OISignCond, roots: Vec<ODyadicAnum>) -> OExplainLit {
    OExplainLit {
        lit: id,
        p: ints(p),
        cond: c,
        roots,
    }
}
fn show(name: &str, v: Option<bool>) {
    let s = match v {
        Some(true) => "Some(true)  <== PERMISSIVE",
        Some(false) => "Some(false) (conservative)",
        None => "None        (decline)",
    };
    println!("{name:<62} clause_is_valid = {s}");
}

/// sqrt(d) as an Anum, isolated in (0, d+1).
fn sqrt_d(d: i64) -> Option<ODyadicAnum> {
    let iv = OBqInterval::new(&OBq::from_int(bi(0)), &OBq::from_int(bi(d + 1)))?;
    ODyadicAnum::from_poly_interval(&ints(&[-d, 0, 1]), &iv)
}

fn main() {
    println!("=== A. degenerate polynomials (the in-tree generator never builds these) ===");
    // zero polynomial
    show(
        "p = 0 with `!= 0`  (unsat literal; clause SHOULD be valid)",
        oexplain_clause_is_valid(&[lit(1, &[0, 0, 0], OISignCond::Ne, vec![])]),
    );
    show(
        "p = 0 with `= 0`   (true everywhere; clause must NOT be valid)",
        oexplain_clause_is_valid(&[lit(1, &[0], OISignCond::Eq, vec![])]),
    );
    show(
        "p = [] (empty coeff vec) with `!= 0`",
        oexplain_clause_is_valid(&[lit(1, &[], OISignCond::Ne, vec![])]),
    );
    show(
        "p = 5 (nonzero constant) with `< 0` (unsat; clause valid)",
        oexplain_clause_is_valid(&[lit(1, &[5], OISignCond::Lt, vec![])]),
    );
    show(
        "p = 5 with `> 0` (true everywhere; clause must NOT be valid)",
        oexplain_clause_is_valid(&[lit(1, &[5], OISignCond::Gt, vec![])]),
    );
    show(
        "p = [1,0,0] (trailing zeros, deg 0 really) with `< 0`",
        oexplain_clause_is_valid(&[lit(1, &[1, 0, 0], OISignCond::Lt, vec![])]),
    );
    show(
        "p = 0 but a root list is supplied anyway (must refuse)",
        oexplain_clause_is_valid(&[lit(1, &[0], OISignCond::Ne, vec![rat(0)])]),
    );
    show(
        "lit id = 0 (must refuse)",
        oexplain_clause_is_valid(&[lit(0, &[0, 1], OISignCond::Lt, vec![rat(0)])]),
    );
    show(
        "empty literal list (empty clause: must NOT be certified)",
        oexplain_clause_is_valid(&[]),
    );
    println!(
        "clause_is_falsified([], []) = {}   (permissive-looking; safe only because \
         clause_is_valid([]) = Some(false))",
        oexplain_clause_is_falsified(&[], &[])
    );

    println!("\n=== B. the same literal id cited twice with CONTRADICTORY polys ===");
    let dup = vec![
        lit(7, &[0, 1], OISignCond::Lt, vec![rat(0)]),
        lit(7, &[0, 1], OISignCond::Gt, vec![rat(0)]),
    ];
    show(
        "two ConflictLits sharing lit id 7",
        oexplain_clause_is_valid(&dup),
    );
    match oexplain_univariate(&dup) {
        Some(e) => println!(
            "  explain_univariate -> clause {:?} cited {:?}   <== DUPLICATE literal in a clause",
            e.lits, e.cited
        ),
        None => println!("  explain_univariate -> None"),
    }

    println!("\n=== C. WRONG root lists (fail-open in the precondition) ===");
    // (x-1)(x-3) < 0 is satisfiable on (1,3). Drop a root -> must refuse.
    let p = [3i64, -4, 1];
    show(
        "(x-1)(x-3) < 0, correct roots [1,3]  (sat -> not valid)",
        oexplain_clause_is_valid(&[lit(1, &p, OISignCond::Lt, vec![rat(1), rat(3)])]),
    );
    show(
        "  same, root 3 DROPPED (incomplete decomposition)",
        oexplain_clause_is_valid(&[lit(1, &p, OISignCond::Lt, vec![rat(1)])]),
    );
    show(
        "  same, root 1 DROPPED",
        oexplain_clause_is_valid(&[lit(1, &p, OISignCond::Lt, vec![rat(3)])]),
    );
    show(
        "  same, SPURIOUS root 5 added",
        oexplain_clause_is_valid(&[lit(1, &p, OISignCond::Lt, vec![rat(1), rat(3), rat(5)])]),
    );
    show(
        "  same COUNT, root 3 replaced by non-root 5",
        oexplain_clause_is_valid(&[lit(1, &p, OISignCond::Lt, vec![rat(1), rat(5)])]),
    );
    show(
        "  roots out of order [3,1]",
        oexplain_clause_is_valid(&[lit(1, &p, OISignCond::Lt, vec![rat(3), rat(1)])]),
    );
    show(
        "  roots duplicated [1,1,3]",
        oexplain_clause_is_valid(&[lit(1, &p, OISignCond::Lt, vec![rat(1), rat(1), rat(3)])]),
    );
    show(
        "  empty root list for a poly that HAS roots",
        oexplain_clause_is_valid(&[lit(1, &p, OISignCond::Lt, vec![])]),
    );

    println!("\n=== D. non-squarefree / repeated roots ===");
    // (x-2)^2 <= 0 : satisfiable only at x=2.  (x-2)^2 < 0 : unsat.
    let sq = [4i64, -4, 1];
    show(
        "(x-2)^2 < 0 (unsat -> clause valid)",
        oexplain_clause_is_valid(&[lit(1, &sq, OISignCond::Lt, vec![rat(2)])]),
    );
    show(
        "(x-2)^2 <= 0 (sat at x=2 -> not valid)",
        oexplain_clause_is_valid(&[lit(1, &sq, OISignCond::Le, vec![rat(2)])]),
    );
    // roots of (x-2)^2 listed with multiplicity -> must refuse (not distinct)
    show(
        "(x-2)^2 with root list [2,2] (multiplicity listed)",
        oexplain_clause_is_valid(&[lit(1, &sq, OISignCond::Le, vec![rat(2), rat(2)])]),
    );
    // cube (x-2)^3
    let cu = [-8i64, 12, -6, 1];
    show(
        "(x-2)^3 >= 0 AND (x-2)^3 <= 0 (sat only at 2 -> not valid)",
        oexplain_clause_is_valid(&[
            lit(1, &cu, OISignCond::Ge, vec![rat(2)]),
            lit(2, &cu, OISignCond::Le, vec![rat(2)]),
        ]),
    );
    show(
        "(x-2)^3 > 0 AND (x-2)^3 < 0 (unsat -> valid)",
        oexplain_clause_is_valid(&[
            lit(1, &cu, OISignCond::Gt, vec![rat(2)]),
            lit(2, &cu, OISignCond::Lt, vec![rat(2)]),
        ]),
    );

    println!("\n=== E. STRICT vs NON-STRICT boundary (the shape a checker gets wrong) ===");
    for (c0, c1, expect) in [
        (OISignCond::Ge, OISignCond::Le, "sat at 0 -> NOT valid"),
        (OISignCond::Gt, OISignCond::Le, "unsat -> valid"),
        (OISignCond::Ge, OISignCond::Lt, "unsat -> valid"),
        (OISignCond::Gt, OISignCond::Lt, "unsat -> valid"),
    ] {
        show(
            &format!("x {c0:?} 0 AND x {c1:?} 0  ({expect})"),
            oexplain_clause_is_valid(&[
                lit(1, &[0, 1], c0, vec![rat(0)]),
                lit(2, &[0, 1], c1, vec![rat(0)]),
            ]),
        );
    }

    println!("\n=== F. IRRATIONAL boundary: x^2-2 >= 0 AND x^2-2 <= 0 (sat at sqrt2) ===");
    if let Some(s2) = sqrt_d(2) {
        let neg = ODyadicAnum::from_poly_interval(
            &ints(&[-2, 0, 1]),
            &OBqInterval::new(&OBq::from_int(bi(-3)), &OBq::from_int(bi(0))).unwrap(),
        )
        .unwrap();
        show(
            "x^2-2 >= 0 AND x^2-2 <= 0 (sat at +-sqrt2 -> NOT valid)",
            oexplain_clause_is_valid(&[
                lit(
                    1,
                    &[-2, 0, 1],
                    OISignCond::Ge,
                    vec![neg.clone(), s2.clone()],
                ),
                lit(
                    2,
                    &[-2, 0, 1],
                    OISignCond::Le,
                    vec![neg.clone(), s2.clone()],
                ),
            ]),
        );
        show(
            "x^2-2 > 0 AND x^2-2 <= 0 (unsat -> valid)",
            oexplain_clause_is_valid(&[
                lit(
                    1,
                    &[-2, 0, 1],
                    OISignCond::Gt,
                    vec![neg.clone(), s2.clone()],
                ),
                lit(
                    2,
                    &[-2, 0, 1],
                    OISignCond::Le,
                    vec![neg.clone(), s2.clone()],
                ),
            ]),
        );
        // nested annuli: sqrt2 < |x| < sqrt3 vs sqrt5 < |x| : unsat
        let n3 = ODyadicAnum::from_poly_interval(
            &ints(&[-3, 0, 1]),
            &OBqInterval::new(&OBq::from_int(bi(-4)), &OBq::from_int(bi(0))).unwrap(),
        )
        .unwrap();
        let p3 = sqrt_d(3).unwrap();
        show(
            "x^2-2 > 0 AND x^2-3 < 0 (sat on (sqrt2,sqrt3) -> NOT valid)",
            oexplain_clause_is_valid(&[
                lit(1, &[-2, 0, 1], OISignCond::Gt, vec![neg, s2]),
                lit(2, &[-3, 0, 1], OISignCond::Lt, vec![n3, p3]),
            ]),
        );
    }

    println!("\n=== G. LIVENESS: near-coincident irrational roots (ladder exhaustion) ===");
    // x^2 - 2  and  (N^2)x^2 - 2N^2 - 1  : roots sqrt2 and sqrt(2 + 1/N^2).
    for e in [10u32, 40, 80, 130, 200] {
        let n = BigInt::from(1u32) << e;
        let n2 = &n * &n;
        let a: Vec<BigInt> = vec![
            -(&n2 * BigInt::from(2) + BigInt::one()),
            BigInt::zero(),
            n2.clone(),
        ];
        let s2 = sqrt_d(2).unwrap();
        let ivb = OBqInterval::new(&OBq::from_int(bi(0)), &OBq::from_int(bi(3))).unwrap();
        let Some(b) = ODyadicAnum::from_poly_interval(&a, &ivb) else {
            println!("  2^-{e}: AY declined to build the second root");
            continue;
        };
        let negs2 = ODyadicAnum::from_poly_interval(
            &ints(&[-2, 0, 1]),
            &OBqInterval::new(&OBq::from_int(bi(-3)), &OBq::from_int(bi(0))).unwrap(),
        )
        .unwrap();
        let negb = ODyadicAnum::from_poly_interval(
            &a,
            &OBqInterval::new(&OBq::from_int(bi(-3)), &OBq::from_int(bi(0))).unwrap(),
        )
        .unwrap();
        let t = Instant::now();
        let r = oexplain_clause_is_valid(&[
            lit(1, &[-2, 0, 1], OISignCond::Gt, vec![negs2, s2]),
            OExplainLit {
                lit: 2,
                p: a.clone(),
                cond: OISignCond::Lt,
                roots: vec![negb, b],
            },
        ]);
        println!("  roots separated by ~2^-{e}: {:?} in {:?}", r, t.elapsed());
    }

    println!("\n=== H. LIVENESS / ceilings ===");
    let base = lit(1, &[0, 1], OISignCond::Lt, vec![rat(0)]);
    for n in [63usize, 64, 65, 200] {
        let big: Vec<OExplainLit> = (0..n)
            .map(|i| {
                let mut l = base.clone();
                l.lit = (i + 1) as i32;
                l
            })
            .collect();
        let t = Instant::now();
        let r = oexplain_clause_is_valid(&big);
        println!("  {n} literals: {r:?} in {:?}", t.elapsed());
    }
    // MAX_CONFLICT_ROOTS: a single polynomial with 130 distinct roots.
    let mut hp = vec![BigInt::one()];
    let mut roots = Vec::new();
    for k in 0..130i64 {
        let mut np = vec![BigInt::zero(); hp.len() + 1];
        for (i, c) in hp.iter().enumerate() {
            np[i + 1] += c;
            np[i] -= c * bi(k);
        }
        hp = np;
        roots.push(rat(k));
    }
    let t = Instant::now();
    let r = oexplain_clause_is_valid(&[OExplainLit {
        lit: 1,
        p: hp.clone(),
        cond: OISignCond::Lt,
        roots: roots.clone(),
    }]);
    println!(
        "  1 poly with 130 distinct roots (> MAX_CONFLICT_ROOTS=128): {r:?} in {:?}",
        t.elapsed()
    );
    let r2 = oexplain_clause_is_valid(&[OExplainLit {
        lit: 1,
        p: hp,
        cond: OISignCond::Lt,
        roots: roots.clone(),
    }
    .clone()]);
    let _ = r2;
    // 120 roots -> under the ceiling, positive control
    let mut hp2 = vec![BigInt::one()];
    let mut roots2 = Vec::new();
    for k in 0..120i64 {
        let mut np = vec![BigInt::zero(); hp2.len() + 1];
        for (i, c) in hp2.iter().enumerate() {
            np[i + 1] += c;
            np[i] -= c * bi(k);
        }
        hp2 = np;
        roots2.push(rat(k));
    }
    let t = Instant::now();
    let r = oexplain_clause_is_valid(&[OExplainLit {
        lit: 1,
        p: hp2,
        cond: OISignCond::Lt,
        roots: roots2,
    }]);
    println!(
        "  1 poly with 120 distinct roots (UNDER the ceiling): {r:?} in {:?}",
        t.elapsed()
    );

    println!("\n=== I. MINIMIZE_BUDGET / big producer run ===");
    // 40 literals, x - k > 0 for k = 0..19 and x - k < 0 for k = 0..19 -> conflict
    let mut many: Vec<OExplainLit> = Vec::new();
    for k in 0..20i64 {
        many.push(lit((k + 1) as i32, &[-k, 1], OISignCond::Gt, vec![rat(k)]));
    }
    for k in 0..20i64 {
        many.push(lit((k + 21) as i32, &[-k, 1], OISignCond::Lt, vec![rat(k)]));
    }
    let t = Instant::now();
    match oexplain_univariate(&many) {
        Some(e) => println!(
            "  40 literals -> clause of {} lits {:?} in {:?}",
            e.lits.len(),
            e.cited,
            t.elapsed()
        ),
        None => println!("  40 literals -> None in {:?}", t.elapsed()),
    }

    println!("\n=== J. countermodel / relevant_pairs / project degenerate ===");
    let two_sat = vec![
        lit(1, &[0, 1], OISignCond::Gt, vec![rat(0)]),
        lit(2, &[-5, 1], OISignCond::Lt, vec![rat(5)]),
    ];
    println!(
        "  countermodel of a SAT pair: rational = {:?}",
        oexplain_countermodel(&two_sat).map(|o| o.map(|a| a.to_rational()))
    );
    println!(
        "  relevant_pairs(empty) = {:?}",
        oexplain_relevant_pairs(&[])
    );
    let bp = OBiPoly::from_x_coeffs(&[vec![(1u32, bi(1))], vec![], vec![(0u32, bi(1))]]);
    println!(
        "  project(polys=[], pairs=[]) = {:?}",
        oexplain_project(&[], &[]).is_some()
    );
    println!(
        "  project(1 poly, pair (0,0)) = {:?}",
        oexplain_project(&[bp.clone()], &[(0, 0)]).is_some()
    );
    println!(
        "  project(1 poly, pair (0,5)) = {:?}",
        oexplain_project(&[bp.clone()], &[(0, 5)]).is_some()
    );
    println!(
        "  project(1 poly, no pairs)   = {:?}",
        oexplain_project(&[bp], &[]).is_some()
    );
}

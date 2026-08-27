// Re-measurement of projection degree growth on MY OWN conflict shapes, at
// irregular sizes, independent of their explain_cost harness.

use num_bigint::BigInt;
use std::time::Instant;

use ay_nra::oracle_api::{oexplain_project, OBiPoly};

fn bi(n: i64) -> BigInt {
    BigInt::from(n)
}

/// `x^a * y^b` coefficient list, as x-coefficients each a list of (y-exp, coeff).
fn build(terms: &[(u32, u32, i64)]) -> OBiPoly {
    let dx = terms.iter().map(|t| t.0).max().unwrap_or(0) as usize;
    let mut xs: Vec<Vec<(u32, BigInt)>> = vec![Vec::new(); dx + 1];
    for &(a, b, c) in terms {
        xs[a as usize].push((b, bi(c)));
    }
    OBiPoly::from_x_coeffs(&xs)
}

fn measure(name: &str, f: &OBiPoly, g: &OBiPoly, indeg: u32) {
    let t = Instant::now();
    match oexplain_project(&[f.clone(), g.clone()], &[(0, 1)]) {
        Some(p) => {
            let el = t.elapsed();
            println!(
                "  {name:<34} in_deg={:<3} out_deg={:<4} ratio x{:<6.2} factors={} const={} {:?}",
                p.in_max_total_degree,
                p.out_max_total_degree,
                if indeg > 0 {
                    f64::from(p.out_max_total_degree) / f64::from(indeg)
                } else {
                    0.0
                },
                p.factors.len(),
                p.constant_factors,
                el
            );
        }
        None => println!("  {name:<34} DECLINED in {:?}", t.elapsed()),
    }
}

fn main() {
    // #govern: see crates/ay-sys/src/govern.rs.
    ay_sys::govern::arm();
    println!("A. x^d - y^d  vs  x^d - y^d - 1   (irregular ladder, no doubling)");
    for d in [2u32, 3, 5, 6, 9, 13, 17, 23] {
        let f = build(&[(d, 0, 1), (0, d, -1)]);
        let g = build(&[(d, 0, 1), (0, d, -1), (0, 0, -1)]);
        measure(&format!("d={d}"), &f, &g, d);
    }

    println!("\nB. REALISTIC conflict shapes drawn from my own generator");
    // circle vs line
    measure(
        "x^2+y^2-4  vs  x-y",
        &build(&[(2, 0, 1), (0, 2, 1), (0, 0, -4)]),
        &build(&[(1, 0, 1), (0, 1, -1)]),
        2,
    );
    // parabola vs hyperbola
    measure(
        "x^2-y      vs  x*y-3",
        &build(&[(2, 0, 1), (0, 1, -1)]),
        &build(&[(1, 1, 1), (0, 0, -3)]),
        2,
    );
    // shared root shape: two quadratics in x with a common factor in y
    measure(
        "x^2-(y+1)x+y vs x^2-(y+2)x+2y",
        &build(&[(2, 0, 1), (1, 1, -1), (1, 0, -1), (0, 1, 1)]),
        &build(&[(2, 0, 1), (1, 1, -1), (1, 0, -2), (0, 1, 2)]),
        3,
    );
    // repeated root / vanishing discriminant: (x-y)^2
    measure(
        "(x-y)^2    vs  x-y-1",
        &build(&[(2, 0, 1), (1, 1, -2), (0, 2, 1)]),
        &build(&[(1, 0, 1), (0, 1, -1), (0, 0, -1)]),
        2,
    );
    // VANISHING LEADING COEFFICIENT: lc in x is y, which vanishes at y=0
    measure(
        "y*x^2+x+1  vs  x-y   (lc vanishes)",
        &build(&[(2, 1, 1), (1, 0, 1), (0, 0, 1)]),
        &build(&[(1, 0, 1), (0, 1, -1)]),
        3,
    );
    // higher realistic: cubic in x with quadratic y-coefficients
    measure(
        "x^3+y^2x-y vs x^2-y^3",
        &build(&[(3, 0, 1), (1, 2, 1), (0, 1, -1)]),
        &build(&[(2, 0, 1), (0, 3, -1)]),
        3,
    );

    println!("\nC. what one step COSTS relative to the measured substrate ceiling");
    println!("  usable endpoint degree (ialg cost ceiling, prior lane) : 3-4");
    for d in [2u32, 3, 4, 5, 6] {
        let f = build(&[(d, 0, 1), (0, d, -1)]);
        let g = build(&[(d, 0, 1), (0, d, -1), (0, 0, -1)]);
        if let Some(p) = oexplain_project(&[f, g], &[(0, 1)]) {
            let out = p.out_max_total_degree;
            println!(
                "  total degree {d} -> projection degree {out}  ({}) ",
                if out <= 4 {
                    "INSIDE the usable envelope"
                } else {
                    "OUTSIDE -- one step already exits"
                }
            );
        }
    }
}

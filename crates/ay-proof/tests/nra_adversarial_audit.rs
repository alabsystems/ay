// ============================================================================
// ADVERSARIAL SOUNDNESS AUDIT (#nra-cert review) — DO NOT COMMIT
// ============================================================================
//
// Every `assert_rejects` case below is a SATISFIABLE (over R) conjunction
// packaged as a lemma clause. If either recognizer returns `true` for one of
// these, the checker would mint a strict certificate for an invalid
// refutation — a soundness hole. `recognize_* == validate_*.is_ok()` by the
// shared `decide_*` functions (verified by reading nra_interval.rs /
// nra_univariate.rs), so the recognizers ARE the acceptance predicate.
//
// `assert_accepts` cases are genuinely infeasible controls, present to prove
// the audit exercises the accepting paths too (a kernel that rejects
// everything would trivially "pass" the rejection cases).

use ay_core::{Sort, Symbol, TermId, TermStore};
use ay_proof::{recognize_nra_interval_unsat, recognize_nra_univariate_unsat};
use num_bigint::BigInt;
use num_rational::BigRational;

fn rat(n: i64, d: i64) -> BigRational {
    BigRational::new(BigInt::from(n), BigInt::from(d))
}

fn rterm(t: &mut TermStore, n: i64, d: i64) -> TermId {
    t.mk_rational(rat(n, d))
}

/// Blocking clause `[(not (and cs))]` — the mbo/hong production shape.
fn conj_clause(t: &mut TermStore, cs: Vec<TermId>) -> Vec<TermId> {
    let conj = t.mk_and(cs);
    vec![t.mk_not_raw(conj)]
}

/// `coeff * x^k` as a term.
fn mono(t: &mut TermStore, coeff: (i64, i64), x: TermId, k: u32) -> TermId {
    let c = rterm(t, coeff.0, coeff.1);
    let mut args = vec![c];
    for _ in 0..k {
        args.push(x);
    }
    t.mk_mul(args)
}

/// Dense univariate polynomial term from low-to-high integer coefficients.
fn upoly(t: &mut TermStore, x: TermId, coeffs: &[i64]) -> TermId {
    let mut parts = Vec::new();
    for (k, &c) in coeffs.iter().enumerate() {
        if c != 0 {
            parts.push(mono(t, (c, 1), x, k as u32));
        }
    }
    if parts.is_empty() {
        return rterm(t, 0, 1);
    }
    t.mk_add(parts)
}

fn assert_rejects(terms: &TermStore, clause: &[TermId], label: &str) {
    assert!(
        !recognize_nra_univariate_unsat(terms, clause),
        "SOUNDNESS HOLE (univariate kind): satisfiable system accepted: {label}"
    );
    assert!(
        !recognize_nra_interval_unsat(terms, clause),
        "SOUNDNESS HOLE (interval kind): satisfiable system accepted: {label}"
    );
}

// ============================================================================
// (1) Satisfiable univariate systems near the fragment boundary
// ============================================================================

#[test]
fn sat_only_at_irrational_points() {
    // x^2 = 2 && x > 0        (sat at sqrt 2)
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Real);
    let zero = rterm(&mut t, 0, 1);
    let two = rterm(&mut t, 2, 1);
    let sq = t.mk_mul(vec![x, x]);
    let eq = t.mk_eq(sq, two);
    let gt = t.mk_gt(x, zero);
    let clause = conj_clause(&mut t, vec![eq, gt]);
    assert_rejects(&t, &clause, "x^2=2 && x>0");

    // x^2 >= 2 && x^2 <= 2    (equality split; sat only at +-sqrt 2)
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Real);
    let two = rterm(&mut t, 2, 1);
    let sq = t.mk_mul(vec![x, x]);
    let ge = t.mk_ge(sq, two);
    let le = t.mk_le(sq, two);
    let clause = conj_clause(&mut t, vec![ge, le]);
    assert_rejects(&t, &clause, "x^2>=2 && x^2<=2");

    // x^2 < 2 && x > 7/5      (sat on (1.4, sqrt 2))
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Real);
    let two = rterm(&mut t, 2, 1);
    let c75 = rterm(&mut t, 7, 5);
    let sq = t.mk_mul(vec![x, x]);
    let lt = t.mk_lt(sq, two);
    let gt = t.mk_gt(x, c75);
    let clause = conj_clause(&mut t, vec![lt, gt]);
    assert_rejects(&t, &clause, "x^2<2 && x>7/5");

    // x^2 <= 2 && x >= 141/100 && x <= 142/100 (tight window around sqrt 2)
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Real);
    let two = rterm(&mut t, 2, 1);
    let lo = rterm(&mut t, 141, 100);
    let hi = rterm(&mut t, 142, 100);
    let sq = t.mk_mul(vec![x, x]);
    let le = t.mk_le(sq, two);
    let gel = t.mk_ge(x, lo);
    let leh = t.mk_le(x, hi);
    let clause = conj_clause(&mut t, vec![le, gel, leh]);
    assert_rejects(&t, &clause, "x^2<=2 && 1.41<=x<=1.42");

    // x^3 = 2 && x > 5/4 && x < 13/10 (cube root window)
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Real);
    let two = rterm(&mut t, 2, 1);
    let lo = rterm(&mut t, 5, 4);
    let hi = rterm(&mut t, 13, 10);
    let cu = t.mk_mul(vec![x, x, x]);
    let eq = t.mk_eq(cu, two);
    let gt = t.mk_gt(x, lo);
    let lt = t.mk_lt(x, hi);
    let clause = conj_clause(&mut t, vec![eq, gt, lt]);
    assert_rejects(&t, &clause, "x^3=2 && 1.25<x<1.3");
}

#[test]
fn sat_only_at_roots_and_multiplicity_edges() {
    // (x^2-2)^2 <= 0 && x > 0  (non-square-free; sat ONLY at sqrt 2)
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Real);
    let zero = rterm(&mut t, 0, 1);
    let two = rterm(&mut t, 2, 1);
    let sq = t.mk_mul(vec![x, x]);
    let diff = t.mk_sub(vec![sq, two]);
    let quad = t.mk_mul(vec![diff, diff]);
    let le = t.mk_le(quad, zero);
    let gt = t.mk_gt(x, zero);
    let clause = conj_clause(&mut t, vec![le, gt]);
    assert_rejects(&t, &clause, "(x^2-2)^2<=0 && x>0");

    // x^2 <= 0 && x >= 0       (sat exactly at 0; strict/non-strict boundary)
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Real);
    let zero = rterm(&mut t, 0, 1);
    let sq = t.mk_mul(vec![x, x]);
    let le = t.mk_le(sq, zero);
    let ge = t.mk_ge(x, zero);
    let clause = conj_clause(&mut t, vec![le, ge]);
    assert_rejects(&t, &clause, "x^2<=0 && x>=0");

    // x^2 = 9/4 && x > 0       (exact rational root path)
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Real);
    let zero = rterm(&mut t, 0, 1);
    let c = rterm(&mut t, 9, 4);
    let sq = t.mk_mul(vec![x, x]);
    let eq = t.mk_eq(sq, c);
    let gt = t.mk_gt(x, zero);
    let clause = conj_clause(&mut t, vec![eq, gt]);
    assert_rejects(&t, &clause, "x^2=9/4 && x>0");

    // x^3 - x = 0 && x > 1/2   (multiple rational roots; sat at 1)
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Real);
    let zero = rterm(&mut t, 0, 1);
    let half = rterm(&mut t, 1, 2);
    let p = upoly(&mut t, x, &[0, -1, 0, 1]);
    let eq = t.mk_eq(p, zero);
    let gt = t.mk_gt(x, half);
    let clause = conj_clause(&mut t, vec![eq, gt]);
    assert_rejects(&t, &clause, "x^3-x=0 && x>1/2");

    // (x^2-2)(x-3) = 0 && x > 2  (sat at root of the OTHER factor, x=3)
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Real);
    let zero = rterm(&mut t, 0, 1);
    let two = rterm(&mut t, 2, 1);
    let three = rterm(&mut t, 3, 1);
    let sq = t.mk_mul(vec![x, x]);
    let f1 = t.mk_sub(vec![sq, two]);
    let f2 = t.mk_sub(vec![x, three]);
    let prod = t.mk_mul(vec![f1, f2]);
    let eq = t.mk_eq(prod, zero);
    let gt = t.mk_gt(x, two);
    let clause = conj_clause(&mut t, vec![eq, gt]);
    assert_rejects(&t, &clause, "(x^2-2)(x-3)=0 && x>2");

    // x*x >= 4 && x <= 2 && x >= 0   (sat exactly at x=2)
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Real);
    let zero = rterm(&mut t, 0, 1);
    let two = rterm(&mut t, 2, 1);
    let four = rterm(&mut t, 4, 1);
    let sq = t.mk_mul(vec![x, x]);
    let ge = t.mk_ge(sq, four);
    let le = t.mk_le(x, two);
    let ge0 = t.mk_ge(x, zero);
    let clause = conj_clause(&mut t, vec![ge, le, ge0]);
    assert_rejects(&t, &clause, "x^2>=4 && 0<=x<=2");
}

#[test]
fn sat_in_unbounded_tail_and_degenerate_shapes() {
    // x^2 > 10^40 && x > 0  (sat only far out in the tail)
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Real);
    let zero = rterm(&mut t, 0, 1);
    let big = t.mk_rational(BigRational::from(BigInt::from(10u8).pow(40)));
    let sq = t.mk_mul(vec![x, x]);
    let gt = t.mk_gt(sq, big);
    let gt0 = t.mk_gt(x, zero);
    let clause = conj_clause(&mut t, vec![gt, gt0]);
    assert_rejects(&t, &clause, "x^2>10^40 && x>0");

    // x^5 - x - 1 >= 0 && x <= 2  (sat: real root ~1.1673)
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Real);
    let zero = rterm(&mut t, 0, 1);
    let two = rterm(&mut t, 2, 1);
    let p = upoly(&mut t, x, &[-1, -1, 0, 0, 0, 1]);
    let ge = t.mk_ge(p, zero);
    let le = t.mk_le(x, two);
    let clause = conj_clause(&mut t, vec![ge, le]);
    assert_rejects(&t, &clause, "x^5-x-1>=0 && x<=2");

    // x^2 != 2 alone  (sat almost everywhere)
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Real);
    let two = rterm(&mut t, 2, 1);
    let sq = t.mk_mul(vec![x, x]);
    let eq = t.mk_eq(sq, two);
    let ne = t.mk_not_raw(eq);
    let clause = conj_clause(&mut t, vec![ne]);
    assert_rejects(&t, &clause, "x^2!=2");

    // Duplicate atom, same sign: clause [a, a], a = (x^2 < 1): negation x^2>=1, sat
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Real);
    let one = rterm(&mut t, 1, 1);
    let sq = t.mk_mul(vec![x, x]);
    let a = t.mk_lt(sq, one);
    let clause = vec![a, a];
    assert_rejects(&t, &clause, "[x^2<1, x^2<1] (negation sat)");

    // x^2 >= 0 alone (valid constraint, sat everywhere)
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Real);
    let zero = rterm(&mut t, 0, 1);
    let sq = t.mk_mul(vec![x, x]);
    let ge = t.mk_ge(sq, zero);
    let clause = conj_clause(&mut t, vec![ge]);
    assert_rejects(&t, &clause, "x^2>=0 (sat)");
}

// ============================================================================
// (2) Shape attacks: hidden variables, Int sorts, division
// ============================================================================

#[test]
fn shape_attacks_hidden_vars_int_sorts_division() {
    // Int-sorted x: x^2 = 2 && x > 0 is Z-infeasible but R-satisfiable;
    // the R-relaxed checker must NOT refute it (refuting would be sound
    // here, but the kernel decides over R and must answer "satisfiable").
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Int);
    let zero = t.mk_int(BigInt::from(0));
    let two = t.mk_int(BigInt::from(2));
    let sq = t.mk_mul(vec![x, x]);
    let eq = t.mk_eq(sq, two);
    let gt = t.mk_gt(x, zero);
    let clause = conj_clause(&mut t, vec![eq, gt]);
    assert_rejects(&t, &clause, "Int x: x^2=2 && x>0 (R-sat)");

    // Second variable smuggled under an uninterpreted wrapper: f(y) is an
    // opaque leaf; {x^2 <= f(y), x >= 2, f(y) <= 4} is satisfiable
    // (x=2, f(y)=4).
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Real);
    let y = t.mk_var("y", Sort::Real);
    let fy = t.mk_app(Symbol::named("f"), [y], Sort::Real);
    let two = rterm(&mut t, 2, 1);
    let four = rterm(&mut t, 4, 1);
    let sq = t.mk_mul(vec![x, x]);
    let le = t.mk_le(sq, fy);
    let ge = t.mk_ge(x, two);
    let le4 = t.mk_le(fy, four);
    let clause = conj_clause(&mut t, vec![le, ge, le4]);
    assert_rejects(&t, &clause, "x^2<=f(y) && x>=2 && f(y)<=4 (sat)");

    // Division by a variable is opaque: {(x/y)^2 <= 1, x^2 >= 1} sat.
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Real);
    let y = t.mk_var("y", Sort::Real);
    let one = rterm(&mut t, 1, 1);
    let dv = t.mk_div(x, y);
    let dsq = t.mk_mul(vec![dv, dv]);
    let le = t.mk_le(dsq, one);
    let sq = t.mk_mul(vec![x, x]);
    let ge = t.mk_ge(sq, one);
    let clause = conj_clause(&mut t, vec![le, ge]);
    assert_rejects(&t, &clause, "(x/y)^2<=1 && x^2>=1 (sat)");

    // Division by an exact nonzero constant: {(x/2)^2 >= 1, x <= -2} sat at -2.
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Real);
    let one = rterm(&mut t, 1, 1);
    let twoc = rterm(&mut t, 2, 1);
    let m2 = rterm(&mut t, -2, 1);
    let dv = t.mk_div(x, twoc);
    let dsq = t.mk_mul(vec![dv, dv]);
    let ge = t.mk_ge(dsq, one);
    let le = t.mk_le(x, m2);
    let clause = conj_clause(&mut t, vec![ge, le]);
    assert_rejects(&t, &clause, "(x/2)^2>=1 && x<=-2 (sat)");

    // Int pair at the lattice corner: x,y Int, x^2+y^2 <= 2, x>=1, y>=1 (sat (1,1)).
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Int);
    let y = t.mk_var("y", Sort::Int);
    let one = t.mk_int(BigInt::from(1));
    let two = t.mk_int(BigInt::from(2));
    let xs = t.mk_mul(vec![x, x]);
    let ys = t.mk_mul(vec![y, y]);
    let sum = t.mk_add(vec![xs, ys]);
    let le = t.mk_le(sum, two);
    let gx = t.mk_ge(x, one);
    let gy = t.mk_ge(y, one);
    let clause = conj_clause(&mut t, vec![le, gx, gy]);
    assert_rejects(&t, &clause, "Int x,y: x^2+y^2<=2 && x>=1 && y>=1 (sat)");
}

// ============================================================================
// (1b) Interval-kind boundary/openness attacks (multivariate, all satisfiable)
// ============================================================================

#[test]
fn interval_openness_boundary_attacks() {
    // x>=0 && y>=0 && x*y=0 (sat on the axes)
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Real);
    let y = t.mk_var("y", Sort::Real);
    let zero = rterm(&mut t, 0, 1);
    let gx = t.mk_ge(x, zero);
    let gy = t.mk_ge(y, zero);
    let p = t.mk_mul(vec![x, y]);
    let eq = t.mk_eq(p, zero);
    let clause = conj_clause(&mut t, vec![gx, gy, eq]);
    assert_rejects(&t, &clause, "x>=0 && y>=0 && xy=0");

    // x>=0 && y>=0 && x*y<=0 (sat on the axes)
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Real);
    let y = t.mk_var("y", Sort::Real);
    let zero = rterm(&mut t, 0, 1);
    let gx = t.mk_ge(x, zero);
    let gy = t.mk_ge(y, zero);
    let p = t.mk_mul(vec![x, y]);
    let le = t.mk_le(p, zero);
    let clause = conj_clause(&mut t, vec![gx, gy, le]);
    assert_rejects(&t, &clause, "x>=0 && y>=0 && xy<=0");

    // x^2+y^2<=2 && x>=1 && y>=1 (sat exactly at the corner (1,1))
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Real);
    let y = t.mk_var("y", Sort::Real);
    let one = rterm(&mut t, 1, 1);
    let two = rterm(&mut t, 2, 1);
    let xs = t.mk_mul(vec![x, x]);
    let ys = t.mk_mul(vec![y, y]);
    let sum = t.mk_add(vec![xs, ys]);
    let le = t.mk_le(sum, two);
    let gx = t.mk_ge(x, one);
    let gy = t.mk_ge(y, one);
    let clause = conj_clause(&mut t, vec![le, gx, gy]);
    assert_rejects(&t, &clause, "x^2+y^2<=2 && x>=1 && y>=1 (corner)");

    // x>=1 && y>=1 && x*y<=1 (sat exactly at (1,1); reciprocal openness)
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Real);
    let y = t.mk_var("y", Sort::Real);
    let one = rterm(&mut t, 1, 1);
    let gx = t.mk_ge(x, one);
    let gy = t.mk_ge(y, one);
    let p = t.mk_mul(vec![x, y]);
    let le = t.mk_le(p, one);
    let clause = conj_clause(&mut t, vec![gx, gy, le]);
    assert_rejects(&t, &clause, "x>=1 && y>=1 && xy<=1 (corner)");

    // x>=2 && y<=1/2 && x*y>=1 (sat exactly at (2,1/2))
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Real);
    let y = t.mk_var("y", Sort::Real);
    let one = rterm(&mut t, 1, 1);
    let two = rterm(&mut t, 2, 1);
    let half = rterm(&mut t, 1, 2);
    let gx = t.mk_ge(x, two);
    let ly = t.mk_le(y, half);
    let p = t.mk_mul(vec![x, y]);
    let ge = t.mk_ge(p, one);
    let clause = conj_clause(&mut t, vec![gx, ly, ge]);
    assert_rejects(&t, &clause, "x>=2 && y<=1/2 && xy>=1 (corner)");

    // x*y=1 && x>0 && y>0 (sat on the hyperbola)
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Real);
    let y = t.mk_var("y", Sort::Real);
    let zero = rterm(&mut t, 0, 1);
    let one = rterm(&mut t, 1, 1);
    let p = t.mk_mul(vec![x, y]);
    let eq = t.mk_eq(p, one);
    let gx = t.mk_gt(x, zero);
    let gy = t.mk_gt(y, zero);
    let clause = conj_clause(&mut t, vec![eq, gx, gy]);
    assert_rejects(&t, &clause, "xy=1 && x>0 && y>0");

    // x>0 && y>0 && z>=0 && x*y*z=0 (sat at z=0)
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Real);
    let y = t.mk_var("y", Sort::Real);
    let z = t.mk_var("z", Sort::Real);
    let zero = rterm(&mut t, 0, 1);
    let gx = t.mk_gt(x, zero);
    let gy = t.mk_gt(y, zero);
    let gz = t.mk_ge(z, zero);
    let p = t.mk_mul(vec![x, y, z]);
    let eq = t.mk_eq(p, zero);
    let clause = conj_clause(&mut t, vec![gx, gy, gz, eq]);
    assert_rejects(&t, &clause, "x>0 && y>0 && z>=0 && xyz=0");

    // mini-hong flipped: x^2+y^2+z^2 < 4 && x*y*z > 1 (sat, e.g. x=y=z=1.05)
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Real);
    let y = t.mk_var("y", Sort::Real);
    let z = t.mk_var("z", Sort::Real);
    let one = rterm(&mut t, 1, 1);
    let four = rterm(&mut t, 4, 1);
    let xs = t.mk_mul(vec![x, x]);
    let ys = t.mk_mul(vec![y, y]);
    let zs = t.mk_mul(vec![z, z]);
    let sum = t.mk_add(vec![xs, ys, zs]);
    let lt = t.mk_lt(sum, four);
    let p0 = t.mk_mul(vec![y, z]);
    let p = t.mk_mul(vec![x, p0]);
    let gt = t.mk_gt(p, one);
    let clause = conj_clause(&mut t, vec![lt, gt]);
    assert_rejects(&t, &clause, "x^2+y^2+z^2<4 && xyz>1 (sat)");
}

// ============================================================================
// (3) Arithmetic/budget attacks — cap trips must reject, never accept
// ============================================================================

#[test]
fn budget_and_magnitude_attacks_fail_closed() {
    // Huge-coefficient SATISFIABLE system: x^2 >= 10^200 (sat in the tail).
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Real);
    let big = t.mk_rational(BigRational::from(BigInt::from(10u8).pow(200)));
    let sq = t.mk_mul(vec![x, x]);
    let ge = t.mk_ge(sq, big);
    let clause = conj_clause(&mut t, vec![ge]);
    assert_rejects(&t, &clause, "x^2>=10^200 (sat)");

    // Degree-255 (just under the cap) SATISFIABLE monomial system:
    // x^255 >= 1 (sat for x>=1). Must reject as satisfiable, not accept.
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Real);
    let one = rterm(&mut t, 1, 1);
    let m = t.mk_mul(vec![x; 255]);
    let ge = t.mk_ge(m, one);
    let clause = conj_clause(&mut t, vec![ge]);
    assert_rejects(&t, &clause, "x^255>=1 (sat)");

    // Degree bomb beyond the cap: must reject (fail-closed), never accept.
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Real);
    let zero = rterm(&mut t, 0, 1);
    let m = t.mk_mul(vec![x; 300]);
    let gt = t.mk_gt(m, zero);
    let lt = t.mk_lt(m, zero);
    let clause = conj_clause(&mut t, vec![gt, lt]);
    assert_rejects(&t, &clause, "degree-300 bomb");

    // Tiny-window satisfiable system with big denominators around sqrt(2):
    // x^2 <= 2 && x >= 141421356/100000000 (sat on [1.41421356, sqrt2]).
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Real);
    let two = rterm(&mut t, 2, 1);
    let lo = t.mk_rational(BigRational::new(
        BigInt::from(141_421_356i64),
        BigInt::from(100_000_000i64),
    ));
    let sq = t.mk_mul(vec![x, x]);
    let le = t.mk_le(sq, two);
    let ge = t.mk_ge(x, lo);
    let clause = conj_clause(&mut t, vec![le, ge]);
    assert_rejects(&t, &clause, "x^2<=2 && x>=1.41421356 (sat)");
}

// ============================================================================
// Positive controls: genuinely infeasible systems the kernels should accept.
// A failure here is NOT a soundness hole, but proves which paths the audit
// actually reached.
// ============================================================================

#[test]
fn positive_controls_actually_exercise_accepting_paths() {
    // hong_1: x^2 < 1 && x > 1 — univariate accept.
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Real);
    let one = rterm(&mut t, 1, 1);
    let sq = t.mk_mul(vec![x, x]);
    let lt = t.mk_lt(sq, one);
    let gt = t.mk_gt(x, one);
    let clause = conj_clause(&mut t, vec![lt, gt]);
    assert!(
        recognize_nra_univariate_unsat(&t, &clause),
        "control: x^2<1 && x>1 must be accepted by the univariate kind"
    );

    // x^2 <= 2 && x >= 3/2 — infeasible (3/2 > sqrt 2): univariate accept.
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Real);
    let two = rterm(&mut t, 2, 1);
    let c32 = rterm(&mut t, 3, 2);
    let sq = t.mk_mul(vec![x, x]);
    let le = t.mk_le(sq, two);
    let ge = t.mk_ge(x, c32);
    let clause = conj_clause(&mut t, vec![le, ge]);
    assert!(
        recognize_nra_univariate_unsat(&t, &clause),
        "control: x^2<=2 && x>=3/2 must be accepted (infeasible)"
    );

    // (x^2-2)^2 <= 0 && x > 3/2 — sat only at sqrt2 < 3/2: infeasible; accept.
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Real);
    let zero = rterm(&mut t, 0, 1);
    let two = rterm(&mut t, 2, 1);
    let c32 = rterm(&mut t, 3, 2);
    let sq = t.mk_mul(vec![x, x]);
    let diff = t.mk_sub(vec![sq, two]);
    let quad = t.mk_mul(vec![diff, diff]);
    let le = t.mk_le(quad, zero);
    let gt = t.mk_gt(x, c32);
    let clause = conj_clause(&mut t, vec![le, gt]);
    assert!(
        recognize_nra_univariate_unsat(&t, &clause),
        "control: (x^2-2)^2<=0 && x>3/2 must be accepted (infeasible)"
    );

    // x^2 + 1 <= 0 — no real roots: accept.
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Real);
    let zero = rterm(&mut t, 0, 1);
    let one = rterm(&mut t, 1, 1);
    let sq = t.mk_mul(vec![x, x]);
    let p = t.mk_add(vec![sq, one]);
    let le = t.mk_le(p, zero);
    let clause = conj_clause(&mut t, vec![le]);
    assert!(
        recognize_nra_univariate_unsat(&t, &clause),
        "control: x^2+1<=0 must be accepted (infeasible)"
    );

    // x>0 && y>0 && xy=0 — interval accept.
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Real);
    let y = t.mk_var("y", Sort::Real);
    let zero = rterm(&mut t, 0, 1);
    let gx = t.mk_gt(x, zero);
    let gy = t.mk_gt(y, zero);
    let p = t.mk_mul(vec![x, y]);
    let eq = t.mk_eq(p, zero);
    let clause = conj_clause(&mut t, vec![gx, gy, eq]);
    assert!(
        recognize_nra_interval_unsat(&t, &clause),
        "control: x>0 && y>0 && xy=0 must be accepted by the interval kind"
    );

    // x^2+y^2 < 2 && x>=1 && y>=1 — infeasible: interval accept.
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Real);
    let y = t.mk_var("y", Sort::Real);
    let one = rterm(&mut t, 1, 1);
    let two = rterm(&mut t, 2, 1);
    let xs = t.mk_mul(vec![x, x]);
    let ys = t.mk_mul(vec![y, y]);
    let sum = t.mk_add(vec![xs, ys]);
    let lt = t.mk_lt(sum, two);
    let gx = t.mk_ge(x, one);
    let gy = t.mk_ge(y, one);
    let clause = conj_clause(&mut t, vec![lt, gx, gy]);
    assert!(
        recognize_nra_interval_unsat(&t, &clause),
        "control: x^2+y^2<2 && x>=1 && y>=1 must be accepted (infeasible)"
    );

    // x^2 < 4 && x >= 2 — infeasible at the closed/open boundary: accept.
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Real);
    let two = rterm(&mut t, 2, 1);
    let four = rterm(&mut t, 4, 1);
    let sq = t.mk_mul(vec![x, x]);
    let lt = t.mk_lt(sq, four);
    let ge = t.mk_ge(x, two);
    let clause = conj_clause(&mut t, vec![lt, ge]);
    assert!(
        recognize_nra_univariate_unsat(&t, &clause),
        "control: x^2<4 && x>=2 must be accepted (infeasible)"
    );
}

// ============================================================================
// Randomized witness fuzz: systems SATISFIABLE BY CONSTRUCTION.
// Any acceptance is a soundness hole.
// ============================================================================

fn lcg(state: &mut u64) -> u64 {
    *state = state
        .wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407);
    *state >> 33
}

fn pick(state: &mut u64, n: u64) -> u64 {
    lcg(state) % n
}

/// Rational witness fuzz (univariate): random polynomial systems constrained
/// to be satisfied at a random rational witness w. 2000 systems.
#[test]
fn fuzz_univariate_rational_witness_systems_must_reject() {
    let mut seed = 0x5eed_c0de_u64;
    for round in 0..2000 {
        let mut t = TermStore::new();
        let x = t.mk_var("x", Sort::Real);
        // witness w = p/q
        let p = pick(&mut seed, 41) as i64 - 20;
        let q = pick(&mut seed, 9) as i64 + 1;
        let w = rat(p, q);

        let n_constraints = 1 + pick(&mut seed, 4) as usize;
        let mut cs = Vec::new();
        for ci in 0..n_constraints {
            // random dense poly, degree 2..=4; force nonlinearity on the first
            let deg = 2 + pick(&mut seed, 3) as usize;
            let mut coeffs: Vec<i64> = (0..=deg).map(|_| pick(&mut seed, 11) as i64 - 5).collect();
            if ci == 0 && coeffs[2..].iter().all(|&c| c == 0) {
                coeffs[2] = 1 + pick(&mut seed, 4) as i64;
            }
            // exact value at witness
            let mut v = BigRational::from(BigInt::from(0));
            for &c in coeffs.iter().rev() {
                v = v * &w + BigRational::from(BigInt::from(c));
            }
            let pt = upoly(&mut t, x, &coeffs);
            let zero = rterm(&mut t, 0, 1);
            use std::cmp::Ordering::{Equal, Greater, Less};
            let c = match (
                v.cmp(&BigRational::from(BigInt::from(0))),
                pick(&mut seed, 3),
            ) {
                (Greater, 0) => t.mk_gt(pt, zero),
                (Greater, 1) => t.mk_ge(pt, zero),
                (Greater, _) => {
                    let e = t.mk_eq(pt, zero);
                    t.mk_not_raw(e)
                }
                (Less, 0) => t.mk_lt(pt, zero),
                (Less, 1) => t.mk_le(pt, zero),
                (Less, _) => {
                    let e = t.mk_eq(pt, zero);
                    t.mk_not_raw(e)
                }
                (Equal, 0) => t.mk_eq(pt, zero),
                (Equal, 1) => t.mk_ge(pt, zero),
                (Equal, _) => t.mk_le(pt, zero),
            };
            cs.push(c);
        }
        let clause = conj_clause(&mut t, cs);
        assert!(
            !recognize_nra_univariate_unsat(&t, &clause),
            "SOUNDNESS HOLE (fuzz round {round}): univariate kind accepted a system \
             satisfiable at witness {p}/{q}"
        );
        assert!(
            !recognize_nra_interval_unsat(&t, &clause),
            "SOUNDNESS HOLE (fuzz round {round}): interval kind accepted a system \
             satisfiable at witness {p}/{q}"
        );
    }
}

/// Irrational witness fuzz (univariate): systems satisfied at sqrt(a) for
/// non-square a — the class a rational-sampling checker forges. 1500 systems.
#[test]
fn fuzz_univariate_irrational_witness_systems_must_reject() {
    let nonsquares = [2i64, 3, 5, 6, 7, 8, 10, 11, 12, 13];
    let mut seed = 0xa11_5eed_u64;
    for round in 0..1500 {
        let mut t = TermStore::new();
        let x = t.mk_var("x", Sort::Real);
        let a = nonsquares[pick(&mut seed, nonsquares.len() as u64) as usize];
        let isqrt = (1..=a)
            .find(|&k| k * k > a)
            .expect("a positive nonsquare has a bounded integer square-root bracket")
            - 1;
        let zero = rterm(&mut t, 0, 1);
        let a_t = rterm(&mut t, a, 1);
        let sq = t.mk_mul(vec![x, x]);
        let core = t.mk_sub(vec![sq, a_t]); // x^2 - a, zero at witness

        let mut cs = Vec::new();
        // vanishing constraint on (x^2-a) * random poly (still zero at witness)
        let deg = pick(&mut seed, 3) as usize;
        let coeffs: Vec<i64> = (0..=deg).map(|_| pick(&mut seed, 7) as i64 - 3).collect();
        let qt = upoly(&mut t, x, &coeffs);
        let prod = t.mk_mul(vec![core, qt]);
        let v = match pick(&mut seed, 3) {
            0 => t.mk_eq(prod, zero),
            1 => t.mk_ge(prod, zero),
            _ => t.mk_le(prod, zero),
        };
        cs.push(v);
        // even-power pinning: (x^2-a)^2 <= 0 (sat ONLY at +-sqrt a)
        if pick(&mut seed, 2) == 0 {
            let sq2 = t.mk_mul(vec![core, core]);
            cs.push(t.mk_le(sq2, zero));
        }
        // rational window around sqrt(a)
        let lo = rterm(&mut t, isqrt, 1);
        let hi = rterm(&mut t, isqrt + 1, 1);
        cs.push(t.mk_gt(x, lo));
        cs.push(t.mk_lt(x, hi));
        // sign-consistent extra: x^2 - a compared consistently with 0 at witness
        if pick(&mut seed, 2) == 0 {
            cs.push(match pick(&mut seed, 2) {
                0 => t.mk_ge(core, zero),
                _ => t.mk_le(core, zero),
            });
        }

        let clause = conj_clause(&mut t, cs);
        assert!(
            !recognize_nra_univariate_unsat(&t, &clause),
            "SOUNDNESS HOLE (irrational fuzz round {round}): accepted a system \
             satisfiable at sqrt({a})"
        );
        assert!(
            !recognize_nra_interval_unsat(&t, &clause),
            "SOUNDNESS HOLE (irrational fuzz round {round}): interval kind accepted \
             a system satisfiable at sqrt({a})"
        );
    }
}

/// Multivariate rational-witness fuzz (interval kind): random 2-3 variable
/// polynomial systems satisfied at a random rational witness point. 1500 runs.
#[test]
fn fuzz_interval_multivariate_witness_systems_must_reject() {
    let mut seed = 0xdead_2bad_u64;
    for round in 0..1500 {
        let mut t = TermStore::new();
        let nvars = 2 + pick(&mut seed, 2) as usize;
        let vars: Vec<TermId> = (0..nvars)
            .map(|i| t.mk_var(format!("v{i}"), Sort::Real))
            .collect();
        let wit: Vec<BigRational> = (0..nvars)
            .map(|_| {
                let p = pick(&mut seed, 21) as i64 - 10;
                let q = pick(&mut seed, 4) as i64 + 1;
                rat(p, q)
            })
            .collect();

        let n_constraints = 2 + pick(&mut seed, 4) as usize;
        let mut cs = Vec::new();
        for ci in 0..n_constraints {
            let n_monos = 1 + pick(&mut seed, 3) as usize;
            let mut value = BigRational::from(BigInt::from(0));
            let mut parts: Vec<TermId> = Vec::new();
            let mut nonlinear = false;
            for mi in 0..n_monos {
                let c = pick(&mut seed, 9) as i64 - 4;
                if c == 0 {
                    continue;
                }
                let mut exps = vec![0u32; nvars];
                let total = if ci == 0 && mi == 0 {
                    2 + pick(&mut seed, 2)
                } else {
                    pick(&mut seed, 4)
                };
                for _ in 0..total {
                    exps[pick(&mut seed, nvars as u64) as usize] += 1;
                }
                if exps.iter().sum::<u32>() >= 2 {
                    nonlinear = true;
                }
                let mut mv = BigRational::from(BigInt::from(c));
                let cterm = rterm(&mut t, c, 1);
                let mut args = vec![cterm];
                for (vi, &e) in exps.iter().enumerate() {
                    for _ in 0..e {
                        args.push(vars[vi]);
                        mv *= &wit[vi];
                    }
                }
                value += mv;
                parts.push(t.mk_mul(args));
            }
            if parts.is_empty() || (ci == 0 && !nonlinear) {
                let c2 = rterm(&mut t, 1, 1);
                let v0 = vars[0];
                parts.push(t.mk_mul(vec![c2, v0, v0]));
                value += &wit[0] * &wit[0];
            }
            let pt = t.mk_add(parts);
            let zero = rterm(&mut t, 0, 1);
            use std::cmp::Ordering::{Equal, Greater, Less};
            let c = match (
                value.cmp(&BigRational::from(BigInt::from(0))),
                pick(&mut seed, 3),
            ) {
                (Greater, 0) => t.mk_gt(pt, zero),
                (Greater, _) => t.mk_ge(pt, zero),
                (Less, 0) => t.mk_lt(pt, zero),
                (Less, _) => t.mk_le(pt, zero),
                (Equal, 0) => t.mk_eq(pt, zero),
                (Equal, 1) => t.mk_ge(pt, zero),
                (Equal, _) => t.mk_le(pt, zero),
            };
            cs.push(c);
        }
        let clause = conj_clause(&mut t, cs);
        assert!(
            !recognize_nra_interval_unsat(&t, &clause),
            "SOUNDNESS HOLE (interval fuzz round {round}): accepted a satisfiable \
             multivariate system"
        );
        assert!(
            !recognize_nra_univariate_unsat(&t, &clause),
            "SOUNDNESS HOLE (interval fuzz round {round}): univariate kind accepted \
             a satisfiable multivariate system"
        );
    }
}

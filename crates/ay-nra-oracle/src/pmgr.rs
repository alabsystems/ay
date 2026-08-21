// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Differential checks for `crates/ay-theories/nra/src/polymanager.rs` — the
//! sparse multivariate polynomial manager.
//!
//! # The problem these checks had to solve
//!
//! z3's C API exposes exactly two polynomial entry points that an oracle can
//! read back: `Z3_algebraic_roots` / `Z3_algebraic_eval` (univariate, over the
//! reals) and `Z3_polynomial_subresultants`. There is NO C API for a
//! multivariate pseudo-division, GCD or square-free part. So the manager
//! cannot be compared to z3 term-for-term, and an oracle that built its own
//! multivariate normalizer in order to read z3's ASTs back would be an oracle
//! that can manufacture divergences.
//!
//! Every check below therefore crosses to z3 through **specialization**: the
//! non-main variables are fixed at integers, which turns each multivariate
//! answer into a univariate integer polynomial that z3's algebraic layer can
//! be interrogated about directly. The specialization theorem used is stated
//! at each check, together with the side condition it needs, and a case that
//! does not satisfy the side condition is SKIPPED rather than compared.
//!
//! ## What each check actually proves
//!
//! * [`check_pm_rep`] — canonical form, interning, and the recursive
//!   `x`-coefficient view. Reference `identity`: it re-derives the documented
//!   monomial order independently and checks the manager's own output against
//!   it. This is the only check that can see a representation bug that every
//!   algorithm above it happens to be insensitive to.
//!
//! * [`check_pm_pseudo_div`] — z3-backed, and the strongest of the five. The
//!   manager guarantees `lc(q,x)^d * p == Q*q + R`. Specializing the whole
//!   identity at an integer point and then evaluating at a real root `alpha`
//!   of the specialized `q` kills the `Q*q` term outright, leaving
//!
//!   ```text
//!       R_bar(alpha)  ==  L_bar^d * p_bar(alpha)
//!   ```
//!
//!   where `L = lc(q, x)` is free of `x` and so specializes to a CONSTANT.
//!   Both `alpha` and both signs come from z3 (`Z3_algebraic_roots` and
//!   `Z3_algebraic_eval`); AY supplies only `R`, `d` and the polynomials. No
//!   side condition is needed at all — the identity is a polynomial identity,
//!   so it survives every specialization.
//!
//! * [`check_pm_gcd`] — a two-sided sandwich on a PLANTED factor plus a
//!   z3-backed root containment. The generator builds `u = G*A` and `v = G*B`
//!   from independently drawn factors, so the answer `g` must satisfy
//!   `G | g` (it cannot have missed the planted factor) and `g | u`, `g | v`
//!   (it cannot have invented one). The z3 leg then specializes and asserts
//!   that every real root z3 finds for `g_bar` is a root of `u_bar` and of
//!   `v_bar`, checked with `Z3_algebraic_eval`.
//!
//!   HONESTLY SCOPED: the converse — every common real root of `u_bar` and
//!   `v_bar` is a root of `g_bar` — is NOT checked, because it is false.
//!   `u = x - y`, `v = x - z` are coprime, yet at `y = z = 0` both specialize
//!   to `x` and share the root `0`. Specialization creates common roots; the
//!   planted-factor sandwich is what covers maximality instead.
//!
//! * [`check_pm_mod_gcd`] — the modular (Brown) GCD against the PRS GCD. These
//!   are genuinely independent implementations: one is a subresultant PRS over
//!   `Z` recursing on content, the other takes images in `Z_p`, eliminates
//!   variables by evaluation, rebuilds them by Newton interpolation, and lifts
//!   by CRA. They share only the representation. When `mod_gcd` certifies an
//!   answer it must equal the PRS answer exactly; a `None` is a decline, not a
//!   divergence.
//!
//! * [`check_pm_square_free`] — z3-backed root-set EQUALITY. Writing
//!   `p = c * prod f_i^{e_i}` with the `f_i` distinct irreducibles in `x`, the
//!   manager's `square_free_in` returns `prod f_i`. Specializing, `c` becomes a
//!   non-zero constant and both sides have real root set `union roots(f_i_bar)`.
//!   So the root sets must agree EXACTLY — both computed by
//!   `Z3_algebraic_roots`, compared with z3's own `Z3_algebraic_eq`. The only
//!   guard needed is that neither specialization is the zero polynomial.
//!
//! * [`check_pm_square_free_all`] — the WHOLE-POLYNOMIAL `square_free`, which
//!   the five checks above never touched. It is a separate check because the
//!   root-set argument that covers `square_free_in` is structurally blind to
//!   half of what `square_free` returns: an integer scalar divides, preserves
//!   every real root and preserves square-freeness, so dropping the integer
//!   content is a WRONG ANSWER that no root-set leg can see. A verifier proved
//!   exactly that — the defect survived 4,000 cases and the unit test named for
//!   the behaviour. What pins it is Gauss's lemma, as an exact identity:
//!   `int_content(square_free(p)) == int_content(p)`.
//!
//! * [`check_pm_mod_gcd_diag`] — `mod_gcd` through the INSTRUMENTED entry
//!   point. Three statements the check above does not make: the decline
//!   counters are inert (`mod_gcd_diag` and `mod_gcd` must answer identically),
//!   the diagnosis describes what actually happened, and a certified answer is
//!   MAXIMAL rather than merely a common divisor. The last one is the load
//!   bearing statement: `mod_gcd`'s own certificate proves `g | u` and `g | v`,
//!   which a TOO-SMALL candidate also satisfies, so nothing inside the manager
//!   can reject one. Only the comparison against the independent PRS answer and
//!   against the planted factor can. A defect injected into the `Z_p[x]`
//!   content split produced exactly such a candidate and was caught at
//!   `fuzz --seed 1 --case 91`.
//!
//! # Sabotage
//!
//! Every check corrupts AY's ANSWER (never its input) under
//! [`Sabotage::On`], so `ay-nra-oracle selftest` proves each of them can
//! actually fail. See [`crate::checks::Sabotage`].

use ay_nra::oracle_api::{OMgrPoly, OPolyMgr};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use crate::checks::{Divergence, Outcome, Sabotage};
use crate::polygen::Rng;
use crate::z3::Z3;

/// The main variable: the one every specialization leaves standing.
const X: u32 = 0;

/// The variables a generated polynomial may mention.
const NVARS: u32 = 3;

/// Maximum degree in the main variable of a generated FACTOR.
///
/// Products of two factors reach `2 * MAX_DEG_X` and a squared factor reaches
/// the same, so the specialized univariate polynomials z3 isolates roots of
/// top out at degree 6 — inside the band the univariate campaign already runs
/// at, which is what keeps the `pmgr` cases from dominating a mixed run.
///
/// MEASURED at this setting: 93,000 mixed cases over seeds 7/23/41 ran at
/// 93-105 cases/s end to end, with no `pmgr` case appearing as the run's
/// slowest. The value was not swept: raising it would trade campaign
/// throughput for larger numbers through code paths the unit tests already
/// pin, so there is no measurement here claiming it is optimal.
const MAX_DEG_X: u32 = 3;

/// Maximum degree in each auxiliary variable of a generated factor.
const MAX_DEG_AUX: u32 = 2;

/// Maximum number of terms in a generated factor.
const MAX_TERMS: usize = 4;

/// Absolute bound on a generated coefficient.
const MAX_COEFF: i64 = 6;

/// Absolute bound on a specialization coordinate.
///
/// Small on purpose. Large values make the specialized coefficients wide
/// without changing which branch runs, and `0` — which is included — is the
/// value most likely to collapse a leading coefficient, which is exactly the
/// degenerate specialization the checks must survive.
const MAX_POINT: i64 = 3;

// ---------------------------------------------------------------------------
// Generation
// ---------------------------------------------------------------------------

/// One generated case for the manager checks.
pub(crate) struct GenPm {
    /// The planted common factor of `u` and `v`.
    pub(crate) g_terms: Vec<(Vec<(u32, u32)>, BigInt)>,
    /// First cofactor.
    pub(crate) a_terms: Vec<(Vec<(u32, u32)>, BigInt)>,
    /// Second cofactor.
    pub(crate) b_terms: Vec<(Vec<(u32, u32)>, BigInt)>,
    /// A factor that will be SQUARED to build the square-free input.
    pub(crate) s_terms: Vec<(Vec<(u32, u32)>, BigInt)>,
    /// Integer values for the auxiliary variables, `(var, value)`.
    pub(crate) point: Vec<(u32, BigInt)>,
    /// Shape label for reporting.
    pub(crate) shape: &'static str,
}

/// Draw one factor: between one and [`MAX_TERMS`] terms over the three
/// variables, with a non-zero constant term forced often enough that the
/// content/primitive split has something to do.
fn gen_factor(rng: &mut Rng, allow_aux: bool) -> Vec<(Vec<(u32, u32)>, BigInt)> {
    let nterms = 1 + rng.below(MAX_TERMS as u64) as usize;
    let mut out: Vec<(Vec<(u32, u32)>, BigInt)> = Vec::with_capacity(nterms);
    for _ in 0..nterms {
        let mut pows: Vec<(u32, u32)> = Vec::new();
        let dx = rng.below(u64::from(MAX_DEG_X) + 1) as u32;
        if dx > 0 {
            pows.push((X, dx));
        }
        if allow_aux {
            for v in 1..NVARS {
                let d = rng.below(u64::from(MAX_DEG_AUX) + 1) as u32;
                if d > 0 {
                    pows.push((v, d));
                }
            }
        }
        let mut c = rng.range(-MAX_COEFF, MAX_COEFF);
        if c == 0 {
            c = 1;
        }
        out.push((pows, BigInt::from(c)));
    }
    out
}

/// Generate one case.
pub(crate) fn gen_pm(rng: &mut Rng) -> GenPm {
    // Four shapes, weighted so the interesting ones are common:
    //   dense      — every factor may use all three variables
    //   x-only     — every factor is univariate in x (the base case of every
    //                recursion, and the only shape where the modular GCD's
    //                Euclid path runs directly)
    //   content    — one factor is free of x, so the content/primitive split
    //                is non-trivial and `iccp` does real work
    //   monic      — the leading x-coefficient of each factor is a constant,
    //                which is the shape z3's own callers guarantee and the one
    //                where pseudo-division degenerates to ordinary division
    let (shape, allow_aux) = match rng.below(4) {
        0 => ("x-only", false),
        1 => ("content", true),
        2 => ("monic", true),
        _ => ("dense", true),
    };
    let mut g_terms = gen_factor(rng, allow_aux);
    if shape == "content" {
        // Force a factor free of x by stripping the x powers.
        for (pows, _) in g_terms.iter_mut() {
            pows.retain(|&(v, _)| v != X);
        }
        if g_terms.iter().all(|(pows, _)| pows.is_empty()) {
            // A bare integer content is legal but uninteresting; give it a y.
            g_terms.push((vec![(1, 1)], BigInt::from(rng.range(1, MAX_COEFF))));
        }
    }
    if shape == "monic" {
        // Make the top x-power carry a constant coefficient.
        g_terms.push((vec![(X, MAX_DEG_X)], BigInt::one()));
    }
    GenPm {
        g_terms,
        a_terms: gen_factor(rng, allow_aux),
        b_terms: gen_factor(rng, allow_aux),
        s_terms: gen_factor(rng, allow_aux),
        point: (1..NVARS)
            .map(|v| (v, BigInt::from(rng.range(-MAX_POINT, MAX_POINT))))
            .collect(),
        shape,
    }
}

// ---------------------------------------------------------------------------
// Shared helpers
// ---------------------------------------------------------------------------

/// Render a polynomial as a stable string for a divergence report.
fn render(m: &OPolyMgr, p: &OMgrPoly) -> String {
    if m.is_zero(p) {
        return "0".to_string();
    }
    let mut s = String::new();
    for (pows, c) in m.terms(p) {
        if !s.is_empty() {
            s.push_str(" + ");
        }
        s.push_str(&c.to_string());
        for (v, e) in pows {
            s.push_str(&format!("*x{v}^{e}"));
        }
    }
    s
}

/// Render a dense integer coefficient list, low-to-high.
fn render_dense(c: &[BigInt]) -> String {
    if c.is_empty() {
        return "0".to_string();
    }
    c.iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join(",")
}

/// Integer coefficients as the rationals z3's binding wants.
fn to_rationals(c: &[BigInt]) -> Vec<BigRational> {
    c.iter().map(|k| BigRational::from(k.clone())).collect()
}

/// Sign of an integer.
fn isign(c: &BigInt) -> i32 {
    if c.is_zero() {
        0
    } else if c.is_negative() {
        -1
    } else {
        1
    }
}

/// The factor sabotage multiplies into a polynomial answer: `2x - 1`.
///
/// Its root `1/2` is not an integer, so it is never a root of a generated
/// integer-coefficient factor of the shapes above, and it is visible to z3 as
/// an extra distinct real root. Multiplying it in also destroys divisibility,
/// so both the AY-side and the z3-side legs of a check react to it.
fn saboteur(m: &mut OPolyMgr) -> OMgrPoly {
    m.mk(&[(vec![(X, 1)], BigInt::from(2)), (vec![], BigInt::from(-1))])
}

// ---------------------------------------------------------------------------
// 1. Representation
// ---------------------------------------------------------------------------

/// Re-derivation of the manager's documented monomial order, written from the
/// specification rather than shared with it: graded first, then lexicographic
/// with the HIGHER variable index more significant.
fn cmp_mono_spec(a: &[(u32, u32)], b: &[(u32, u32)]) -> std::cmp::Ordering {
    use std::cmp::Ordering;
    let da: u32 = a.iter().map(|&(_, e)| e).sum();
    let db: u32 = b.iter().map(|&(_, e)| e).sum();
    match da.cmp(&db) {
        Ordering::Equal => {}
        other => return other,
    }
    let (mut i, mut j) = (a.len(), b.len());
    loop {
        match (i, j) {
            (0, 0) => return Ordering::Equal,
            (0, _) => return Ordering::Less,
            (_, 0) => return Ordering::Greater,
            _ => {}
        }
        let (va, ea) = a[i - 1];
        let (vb, eb) = b[j - 1];
        if va != vb {
            return va.cmp(&vb);
        }
        if ea != eb {
            return ea.cmp(&eb);
        }
        i -= 1;
        j -= 1;
    }
}

/// Canonical form, interning and the recursive `x`-coefficient view.
pub(crate) fn check_pm_rep(g: &GenPm, sab: Sabotage) -> Outcome {
    let mut m = OPolyMgr::new();
    let p = m.mk(&g.g_terms);
    let a = m.mk(&g.a_terms);
    let prod = m.mul(&p, &a);
    if m.is_zero(&prod) {
        return Outcome::Skipped("generated product is zero");
    }
    let mut comparisons = 0u64;

    // (a) Canonical form of the term list, against an independently written
    //     copy of the documented order.
    let mut terms = m.terms(&prod);
    if sab.on() && terms.len() >= 2 {
        terms.swap(0, 1);
    }
    for w in terms.windows(2) {
        comparisons += 1;
        if cmp_mono_spec(&w[0].0, &w[1].0) != std::cmp::Ordering::Greater {
            return Divergence::new(
                "pm-representation",
                "identity",
                format!(
                    "term list is not strictly descending under graded-lex: {:?} then {:?}",
                    w[0].0, w[1].0
                ),
                vec![("p".to_string(), render(&m, &prod))],
            );
        }
    }
    for (pows, c) in &terms {
        comparisons += 1;
        if c.is_zero() {
            return Divergence::new(
                "pm-representation",
                "identity",
                "a zero coefficient survived normalization".to_string(),
                vec![("p".to_string(), render(&m, &prod))],
            );
        }
        comparisons += 1;
        if pows.iter().any(|&(_, e)| e == 0) || pows.windows(2).any(|w| w[0].0 >= w[1].0) {
            return Divergence::new(
                "pm-representation",
                "identity",
                format!("monomial is not canonical: {pows:?}"),
                vec![("p".to_string(), render(&m, &prod))],
            );
        }
    }

    // (b) Degree queries against a direct recomputation from the term list.
    for v in 0..NVARS {
        let want: u32 = terms
            .iter()
            .map(|(pows, _)| pows.iter().find(|&&(pv, _)| pv == v).map_or(0, |&(_, e)| e))
            .max()
            .unwrap_or(0);
        comparisons += 1;
        if m.degree(&prod, v) != want {
            return Divergence::new(
                "pm-representation",
                "identity",
                format!(
                    "degree(p, x{v}) = {} but the term list says {want}",
                    m.degree(&prod, v)
                ),
                vec![("p".to_string(), render(&m, &prod))],
            );
        }
    }

    // (c) The recursive x-view round-trips.
    let cs = m.x_coeffs(&prod, X);
    let back = m.from_x_coeffs(X, &cs);
    comparisons += 1;
    if back != prod {
        return Divergence::new(
            "pm-representation",
            "identity",
            "from_x_coeffs(x_coeffs(p)) != p".to_string(),
            vec![
                ("p".to_string(), render(&m, &prod)),
                ("back".to_string(), render(&m, &back)),
            ],
        );
    }
    // ... and each bucket agrees with `coeff`.
    for (k, ck) in cs.iter().enumerate() {
        let direct = m.coeff(&prod, X, u32::try_from(k).unwrap_or(u32::MAX));
        comparisons += 1;
        if &direct != ck {
            return Divergence::new(
                "pm-representation",
                "identity",
                format!("coeff(p, x, {k}) disagrees with x_coeffs[{k}]"),
                vec![("p".to_string(), render(&m, &prod))],
            );
        }
    }

    // (d) p - p == 0, and p * 1 == p.
    let diff = m.sub(&prod, &prod);
    comparisons += 1;
    if !m.is_zero(&diff) {
        return Divergence::new(
            "pm-representation",
            "identity",
            "p - p is not the zero polynomial".to_string(),
            vec![("p".to_string(), render(&m, &prod))],
        );
    }
    let one = m.constant(BigInt::one());
    let same = m.mul(&prod, &one);
    comparisons += 1;
    if same != prod {
        return Divergence::new(
            "pm-representation",
            "identity",
            "p * 1 != p".to_string(),
            vec![("p".to_string(), render(&m, &prod))],
        );
    }

    // (e) Substituting the auxiliary variables in either order agrees.
    let mut fwd = prod.clone();
    for (v, val) in &g.point {
        fwd = m.eval_var(&fwd, *v, val);
    }
    let mut rev = prod.clone();
    for (v, val) in g.point.iter().rev() {
        rev = m.eval_var(&rev, *v, val);
    }
    comparisons += 1;
    if fwd != rev {
        return Divergence::new(
            "pm-representation",
            "identity",
            "substitution is order-dependent".to_string(),
            vec![("p".to_string(), render(&m, &prod))],
        );
    }

    Outcome::Match(comparisons)
}

// ---------------------------------------------------------------------------
// 2. Pseudo-division
// ---------------------------------------------------------------------------

/// `lc(q,x)^d * p == Q*q + R`, checked exactly in the manager AND at the real
/// roots of the specialized `q` with z3.
pub(crate) fn check_pm_pseudo_div(z3: &Z3, g: &GenPm, sab: Sabotage) -> Outcome {
    let mut m = OPolyMgr::new();
    let p = {
        let a = m.mk(&g.a_terms);
        let b = m.mk(&g.b_terms);
        m.mul(&a, &b)
    };
    let q = m.mk(&g.g_terms);
    if m.is_zero(&q) || m.is_zero(&p) {
        return Outcome::Skipped("degenerate operand");
    }
    let Some(pd) = m.pseudo_division(&p, &q, X, true) else {
        return Outcome::Declined("pseudo_division refused");
    };
    let mut rem = pd.rem;
    if sab.on() {
        let one = m.constant(BigInt::one());
        rem = m.add(&rem, &one);
    }
    let mut comparisons = 0u64;

    // (a) The exact identity, in the manager's own arithmetic.
    let lcq = m.lc(&q, X);
    let lpow = m.pow(&lcq, pd.d);
    let lhs = m.mul(&lpow, &p);
    let qq = m.mul(&pd.quot, &q);
    let rhs = m.add(&qq, &rem);
    comparisons += 1;
    if lhs != rhs {
        return Divergence::new(
            "pm-pseudo-division",
            "identity",
            format!("lc(q,x)^{} * p != Q*q + R", pd.d),
            vec![
                ("p".to_string(), render(&m, &p)),
                ("q".to_string(), render(&m, &q)),
                ("Q".to_string(), render(&m, &pd.quot)),
                ("R".to_string(), render(&m, &rem)),
            ],
        );
    }
    comparisons += 1;
    if !m.is_zero(&rem) && m.degree(&rem, X) >= m.degree(&q, X) {
        return Divergence::new(
            "pm-pseudo-division",
            "identity",
            format!(
                "remainder is not reduced: deg_x(R) = {}, deg_x(q) = {}",
                m.degree(&rem, X),
                m.degree(&q, X)
            ),
            vec![
                ("q".to_string(), render(&m, &q)),
                ("R".to_string(), render(&m, &rem)),
            ],
        );
    }

    // (b) The z3 leg. At every real root alpha of q_bar,
    //         R_bar(alpha) == L_bar^d * p_bar(alpha)
    //     with L = lc(q, x) free of x, hence a constant after specialization.
    let (Some(qb), Some(pb), Some(rb), Some(lb)) = (
        m.specialize(&q, X, &g.point),
        m.specialize(&p, X, &g.point),
        m.specialize(&rem, X, &g.point),
        m.specialize(&lcq, X, &g.point),
    ) else {
        return Outcome::Skipped("specialization left a variable standing");
    };
    if qb.len() < 2 {
        return Outcome::Skipped("specialized divisor has no roots to test at");
    }
    let l_sign = match lb.len() {
        0 => 0,
        1 => isign(&lb[0]),
        // `lc(q, x)` is free of `x`, so its specialization is a constant. A
        // longer list would mean the specialization did not do its job, which
        // is a representation bug, not a pseudo-division one.
        _ => {
            return Divergence::new(
                "pm-pseudo-division",
                "identity",
                "lc(q, x) specialized to a non-constant".to_string(),
                vec![("lc".to_string(), render_dense(&lb))],
            )
        }
    };
    let Some(roots) = z3.roots(&to_rationals(&qb)) else {
        return Outcome::Skipped("z3 declined the specialized divisor");
    };
    // sign(L^d) = sign(L)^d, INCLUDING `d == 0`, where the answer is 1 for
    // every `L` — even `L == 0`, since `L^0 = 1` and the identity degenerates to
    // `p == R`.
    //
    // This was a FALSE POSITIVE in the check, not a defect in the manager, and
    // it is worth naming because a spurious divergence costs a lane as surely as
    // a blind spot does. The old code tested `l_sign == 0` before `d == 0`, so a
    // specialization that killed the leading coefficient reported
    // `sign(lc^0) * sign(p) = 0` against a correct `sign(R) = -1`. It fired at
    // `repro --seed 7777777 --case 1277 # checks=36`, where `deg_x(p) < deg_x(q)`
    // forces `Q = 0`, `R = p` and `d = 0`: the rendered `R` and `p` in that
    // report are character-for-character identical, which is the tell.
    //
    // 54,000 cases over six seeds never reached it. It surfaced only because
    // appending the `anum` checks re-mapped every case index (see `ALL_CHECKS`)
    // and drew a specialization this check had never been handed.
    let ld_sign = if pd.d == 0 {
        1
    } else if l_sign == 0 {
        0
    } else if l_sign > 0 || pd.d % 2 == 0 {
        1
    } else {
        -1
    };
    for alpha in roots {
        let (Some(rs), Some(ps)) = (
            z3.eval_sign(&to_rationals(&rb), alpha),
            z3.eval_sign(&to_rationals(&pb), alpha),
        ) else {
            return Outcome::Skipped("z3 declined an evaluation");
        };
        comparisons += 1;
        let want = ld_sign * ps;
        if rs != want {
            return Divergence::new(
                "pm-pseudo-division",
                "z3",
                format!(
                    "at a root of q: sign(R) = {rs} but sign(lc^{}) * sign(p) = {want}",
                    pd.d
                ),
                vec![
                    ("p".to_string(), render(&m, &p)),
                    ("q".to_string(), render(&m, &q)),
                    ("R".to_string(), render(&m, &rem)),
                    ("p_bar".to_string(), render_dense(&pb)),
                    ("q_bar".to_string(), render_dense(&qb)),
                    ("R_bar".to_string(), render_dense(&rb)),
                    ("lc_bar".to_string(), render_dense(&lb)),
                ],
            );
        }
    }
    Outcome::Match(comparisons)
}

// ---------------------------------------------------------------------------
// 3. GCD
// ---------------------------------------------------------------------------

/// Shared body of the two GCD checks: `which` selects the PRS or the modular
/// implementation, and the modular one additionally has to agree with the PRS.
fn gcd_body(z3: &Z3, g: &GenPm, sab: Sabotage, modular: bool) -> Outcome {
    let name = if modular { "pm-mod-gcd" } else { "pm-gcd" };
    let mut m = OPolyMgr::new();
    let gg = m.mk(&g.g_terms);
    let aa = m.mk(&g.a_terms);
    let bb = m.mk(&g.b_terms);
    if m.is_zero(&gg) || m.is_zero(&aa) || m.is_zero(&bb) {
        return Outcome::Skipped("degenerate factor");
    }
    let u = m.mul(&gg, &aa);
    let v = m.mul(&gg, &bb);
    if m.is_zero(&u) || m.is_zero(&v) {
        return Outcome::Skipped("degenerate product");
    }

    let Some(prs) = m.gcd_via_prs(&u, &v) else {
        return Outcome::Declined("prs gcd refused");
    };
    let mut answer = if modular {
        match m.mod_gcd(&u, &v) {
            Some(x) => x,
            None => return Outcome::Declined("modular gcd could not certify a candidate"),
        }
    } else {
        prs.clone()
    };
    if sab.on() {
        let f = saboteur(&mut m);
        answer = m.mul(&answer, &f);
    }
    let mut comparisons = 0u64;

    // (a) The modular answer must equal the PRS answer exactly. Two
    //     implementations that share only the representation.
    if modular {
        comparisons += 1;
        if answer != prs {
            return Divergence::new(
                name,
                "identity",
                "modular gcd disagrees with the subresultant PRS gcd".to_string(),
                vec![
                    ("u".to_string(), render(&m, &u)),
                    ("v".to_string(), render(&m, &v)),
                    ("prs".to_string(), render(&m, &prs)),
                    ("modular".to_string(), render(&m, &answer)),
                ],
            );
        }
    }

    // (b) It divides both inputs (it cannot have invented a factor) ...
    comparisons += 1;
    if !m.divides(&answer, &u) {
        return Divergence::new(
            name,
            "identity",
            "the gcd does not divide u".to_string(),
            vec![
                ("u".to_string(), render(&m, &u)),
                ("v".to_string(), render(&m, &v)),
                ("g".to_string(), render(&m, &answer)),
            ],
        );
    }
    comparisons += 1;
    if !m.divides(&answer, &v) {
        return Divergence::new(
            name,
            "identity",
            "the gcd does not divide v".to_string(),
            vec![
                ("u".to_string(), render(&m, &u)),
                ("v".to_string(), render(&m, &v)),
                ("g".to_string(), render(&m, &answer)),
            ],
        );
    }
    // ... and the PLANTED factor divides it (it cannot have missed one).
    comparisons += 1;
    if !m.divides(&gg, &answer) {
        return Divergence::new(
            name,
            "identity",
            "the planted common factor does not divide the gcd".to_string(),
            vec![
                ("planted".to_string(), render(&m, &gg)),
                ("u".to_string(), render(&m, &u)),
                ("v".to_string(), render(&m, &v)),
                ("g".to_string(), render(&m, &answer)),
            ],
        );
    }

    // (c) The z3 leg: every real root of g_bar is a root of u_bar and v_bar.
    let (Some(ub), Some(vb), Some(gb)) = (
        m.specialize(&u, X, &g.point),
        m.specialize(&v, X, &g.point),
        m.specialize(&answer, X, &g.point),
    ) else {
        return Outcome::Skipped("specialization left a variable standing");
    };
    if gb.len() < 2 || ub.is_empty() || vb.is_empty() {
        return Outcome::Skipped("specialized gcd has no roots to test");
    }
    let Some(roots) = z3.roots(&to_rationals(&gb)) else {
        return Outcome::Skipped("z3 declined the specialized gcd");
    };
    for alpha in roots {
        for (label, coeffs) in [("u", &ub), ("v", &vb)] {
            let Some(s) = z3.eval_sign(&to_rationals(coeffs), alpha) else {
                return Outcome::Skipped("z3 declined an evaluation");
            };
            comparisons += 1;
            if s != 0 {
                return Divergence::new(
                    name,
                    "z3",
                    format!("a real root of the gcd is not a root of {label} (sign {s})"),
                    vec![
                        ("u".to_string(), render(&m, &u)),
                        ("v".to_string(), render(&m, &v)),
                        ("g".to_string(), render(&m, &answer)),
                        ("u_bar".to_string(), render_dense(&ub)),
                        ("v_bar".to_string(), render_dense(&vb)),
                        ("g_bar".to_string(), render_dense(&gb)),
                    ],
                );
            }
        }
    }
    Outcome::Match(comparisons)
}

/// The subresultant-PRS GCD.
pub(crate) fn check_pm_gcd(z3: &Z3, g: &GenPm, sab: Sabotage) -> Outcome {
    gcd_body(z3, g, sab, false)
}

/// The modular (Brown) GCD, against the PRS GCD and against z3.
pub(crate) fn check_pm_mod_gcd(z3: &Z3, g: &GenPm, sab: Sabotage) -> Outcome {
    gcd_body(z3, g, sab, true)
}

/// The INSTRUMENTED modular GCD: the decline diagnosis, and the `Z_p[x]`
/// content split the recovery step now rests on.
///
/// Three statements, none of which the plain `pm-mod-gcd` check makes:
///
/// 1. **The instrumentation is inert.** `mod_gcd_diag` and `mod_gcd` must
///    return byte-identical answers on the same inputs. The counters are
///    written on every decline path inside the manager, so a counter write
///    that accidentally short-circuited a branch — the obvious way to break a
///    diagnosis harness — changes the answer, and this catches it.
///
/// 2. **The diagnosis matches the outcome.** `certified()` must agree with
///    `is_some()`, and the `primary()` label must say `"certified"` exactly
///    when the call certified. A diagnosis that disagrees with what happened is
///    worse than none, because the fix it points at is chosen from it.
///
/// 3. **The certified answer is MAXIMAL, not merely a divisor.** It must equal
///    the subresultant PRS answer exactly, and the planted common factor must
///    divide it. This is the statement that pins the content split: the
///    recovery step divides the interpolant by its `Z_p[x]` content, and if the
///    matching split at the top of the level were wrong the answer would come
///    back as `G / cont_Y(G)` — a PROPER DIVISOR of the true GCD, which still
///    divides both inputs and would therefore sail through the exact
///    certificate. Only a comparison against an independent implementation, or
///    against the planted factor, can see that. Both are made here.
pub(crate) fn check_pm_mod_gcd_diag(g: &GenPm, sab: Sabotage) -> Outcome {
    let mut m = OPolyMgr::new();
    let gg = m.mk(&g.g_terms);
    let aa = m.mk(&g.a_terms);
    let bb = m.mk(&g.b_terms);
    if m.is_zero(&gg) || m.is_zero(&aa) || m.is_zero(&bb) {
        return Outcome::Skipped("degenerate factor");
    }
    let u = m.mul(&gg, &aa);
    let v = m.mul(&gg, &bb);
    if m.is_zero(&u) || m.is_zero(&v) {
        return Outcome::Skipped("degenerate product");
    }
    let name = "pm-mod-gcd-diag";
    let mut comparisons = 0u64;

    let plain = m.mod_gcd(&u, &v);
    let (instrumented, diag) = m.mod_gcd_diag(&u, &v);

    // (1) The instrumented entry point answers exactly what the plain one does.
    comparisons += 1;
    if plain != instrumented {
        return Divergence::new(
            name,
            "identity",
            "mod_gcd_diag and mod_gcd disagree — the instrumentation is not inert".to_string(),
            vec![
                ("u".to_string(), render(&m, &u)),
                ("v".to_string(), render(&m, &v)),
                (
                    "plain".to_string(),
                    plain.map_or_else(|| "None".to_string(), |p| render(&m, &p)),
                ),
                (
                    "instrumented".to_string(),
                    instrumented.map_or_else(|| "None".to_string(), |p| render(&m, &p)),
                ),
            ],
        );
    }

    // (2) The diagnosis describes what actually happened.
    comparisons += 1;
    if diag.certified() != instrumented.is_some() {
        return Divergence::new(
            name,
            "identity",
            format!(
                "diag.certified() = {} but mod_gcd returned {}",
                diag.certified(),
                if instrumented.is_some() {
                    "Some"
                } else {
                    "None"
                }
            ),
            vec![
                ("u".to_string(), render(&m, &u)),
                ("v".to_string(), render(&m, &v)),
                ("primary".to_string(), diag.primary().to_string()),
            ],
        );
    }
    comparisons += 1;
    if (diag.primary() == "certified") != diag.certified() {
        return Divergence::new(
            name,
            "identity",
            format!(
                "diag.primary() = {:?} contradicts diag.certified() = {}",
                diag.primary(),
                diag.certified()
            ),
            vec![
                ("u".to_string(), render(&m, &u)),
                ("v".to_string(), render(&m, &v)),
            ],
        );
    }

    let Some(mut answer) = instrumented else {
        // A decline must name a mechanism, not a placeholder. This one is not
        // counted as a comparison: the case ends as `Declined`, and a decline
        // reports no assertion count.
        if diag.primary().is_empty() || diag.primary() == "certified" {
            return Divergence::new(
                name,
                "identity",
                "a decline carries no decline reason".to_string(),
                vec![
                    ("u".to_string(), render(&m, &u)),
                    ("v".to_string(), render(&m, &v)),
                ],
            );
        }
        return Outcome::Declined("modular gcd could not certify a candidate");
    };

    if sab.on() {
        let f = saboteur(&mut m);
        answer = m.mul(&answer, &f);
    }

    // (2b) The WORK COUNTERS are consistent with an answer that came through
    //      the certificate. A verifier corrupted three of them — evaluation
    //      points never counted, trial-division rejects mis-attributed to the
    //      lc_H gate, primes never counted — and got ZERO divergences across
    //      2,000 cases while `growth` printed `primes 0  points 0` on rows it
    //      had just CERTIFIED, which is self-evidently impossible. These
    //      counters are what the next lane will read to decide where to spend
    //      effort, so they are asserted rather than trusted.
    //
    //      Guarded on `shortcuts() == 0`: a zero input, a constant input or a
    //      unit modular image answers without entering the prime loop at all,
    //      and legitimately reports no work.
    if !sab.on() && diag.shortcuts() == 0 {
        comparisons += 1;
        if diag.cert_accepted() == 0 {
            return Divergence::new(
                name,
                "identity",
                "an answer was certified but no accept site fired".to_string(),
                vec![
                    ("u".to_string(), render(&m, &u)),
                    ("v".to_string(), render(&m, &v)),
                ],
            );
        }
        comparisons += 1;
        if diag.primes_used() == 0 {
            return Divergence::new(
                name,
                "identity",
                "the certificate accepted a candidate without entering a single prime".to_string(),
                vec![
                    ("u".to_string(), render(&m, &u)),
                    ("v".to_string(), render(&m, &v)),
                ],
            );
        }
        // The Brown recursion only evaluates when there is a variable to
        // eliminate; a single-variable problem goes straight to base-case
        // Euclid and legitimately consumes no evaluation points.
        let mut nvars = m.vars(&u);
        for x in m.vars(&v) {
            if !nvars.contains(&x) {
                nvars.push(x);
            }
        }
        if nvars.len() >= 2 {
            comparisons += 1;
            if diag.rec_points_tried() == 0 {
                return Divergence::new(
                    name,
                    "identity",
                    format!(
                        "a {}-variable problem was interpolated without consuming one \
                         evaluation point",
                        nvars.len()
                    ),
                    vec![
                        ("u".to_string(), render(&m, &u)),
                        ("v".to_string(), render(&m, &v)),
                    ],
                );
            }
        }
    }

    // (3) Maximality: equal to the PRS answer, and a multiple of the planted
    //     factor. A too-small candidate still divides both inputs, so this is
    //     the only leg that can see one.
    let Some(prs) = m.gcd_via_prs(&u, &v) else {
        return Outcome::Declined("prs gcd refused");
    };
    comparisons += 1;
    if answer != prs {
        return Divergence::new(
            name,
            "identity",
            "the certified modular gcd differs from the subresultant PRS gcd".to_string(),
            vec![
                ("u".to_string(), render(&m, &u)),
                ("v".to_string(), render(&m, &v)),
                ("prs".to_string(), render(&m, &prs)),
                ("modular".to_string(), render(&m, &answer)),
            ],
        );
    }
    comparisons += 1;
    if !m.divides(&gg, &answer) {
        return Divergence::new(
            name,
            "identity",
            "the planted common factor does not divide the certified modular gcd".to_string(),
            vec![
                ("planted".to_string(), render(&m, &gg)),
                ("u".to_string(), render(&m, &u)),
                ("v".to_string(), render(&m, &v)),
                ("g".to_string(), render(&m, &answer)),
            ],
        );
    }
    comparisons += 1;
    if !m.divides(&answer, &u) || !m.divides(&answer, &v) {
        return Divergence::new(
            name,
            "identity",
            "the certified modular gcd does not divide both inputs".to_string(),
            vec![
                ("u".to_string(), render(&m, &u)),
                ("v".to_string(), render(&m, &v)),
                ("g".to_string(), render(&m, &answer)),
            ],
        );
    }
    Outcome::Match(comparisons)
}

// ---------------------------------------------------------------------------
// 4. Square-free
// ---------------------------------------------------------------------------

/// `square_free_in(p, x)` preserves the exact real root set of every
/// specialization, and divides `p`.
pub(crate) fn check_pm_square_free(z3: &Z3, g: &GenPm, sab: Sabotage) -> Outcome {
    let mut m = OPolyMgr::new();
    let s = m.mk(&g.s_terms);
    let other = m.mk(&g.a_terms);
    if m.is_zero(&s) || m.is_zero(&other) {
        return Outcome::Skipped("degenerate factor");
    }
    // p = s^2 * other, so there is always a square to remove.
    let s2 = m.mul(&s, &s);
    let p = m.mul(&s2, &other);
    if m.is_zero(&p) {
        return Outcome::Skipped("degenerate product");
    }
    let Some(mut sf) = m.square_free_in(&p, X) else {
        return Outcome::Declined("square_free_in refused");
    };
    if sab.on() {
        let f = saboteur(&mut m);
        sf = m.mul(&sf, &f);
    }
    let mut comparisons = 0u64;

    // (a) The square-free part divides the input.
    comparisons += 1;
    if !m.divides(&sf, &p) {
        return Divergence::new(
            "pm-square-free",
            "identity",
            "the square-free part does not divide p".to_string(),
            vec![
                ("p".to_string(), render(&m, &p)),
                ("sf".to_string(), render(&m, &sf)),
            ],
        );
    }

    // (b) The z3 leg: identical real root sets after specialization.
    let (Some(pb), Some(sb)) = (
        m.specialize(&p, X, &g.point),
        m.specialize(&sf, X, &g.point),
    ) else {
        return Outcome::Skipped("specialization left a variable standing");
    };
    if pb.is_empty() || sb.is_empty() {
        return Outcome::Skipped("a specialization vanished");
    }
    let (Some(pr), Some(sr)) = (z3.roots(&to_rationals(&pb)), z3.roots(&to_rationals(&sb))) else {
        return Outcome::Skipped("z3 declined a specialization");
    };
    comparisons += 1;
    if pr.len() != sr.len() {
        return Divergence::new(
            "pm-square-free",
            "z3",
            format!(
                "root counts differ: p has {} distinct real roots, its square-free part has {}",
                pr.len(),
                sr.len()
            ),
            vec![
                ("p".to_string(), render(&m, &p)),
                ("sf".to_string(), render(&m, &sf)),
                ("p_bar".to_string(), render_dense(&pb)),
                ("sf_bar".to_string(), render_dense(&sb)),
            ],
        );
    }
    for (i, (a, b)) in pr.iter().zip(sr.iter()).enumerate() {
        comparisons += 1;
        if !z3.eq(*a, *b) {
            return Divergence::new(
                "pm-square-free",
                "z3",
                format!("root #{i} of p and of its square-free part differ"),
                vec![
                    ("p".to_string(), render(&m, &p)),
                    ("sf".to_string(), render(&m, &sf)),
                    ("p_bar".to_string(), render_dense(&pb)),
                    ("sf_bar".to_string(), render_dense(&sb)),
                ],
            );
        }
    }
    Outcome::Match(comparisons)
}

/// `square_free(p)` — the WHOLE-POLYNOMIAL entry point, which recurses through
/// the content instead of working in one variable.
///
/// This check exists because a verifier proved the entry point was invisible.
/// Every other `pm` check calls `square_free_in`; nothing called `square_free`,
/// and dropping its integer content — returning `(x-1)` for `square_free(6(x-1)^2)`
/// instead of `6(x-1)` — produced ZERO divergences over 4,000 cases and still
/// passed the unit test named for that exact behaviour, because that test used
/// an all-±1 input where the dropped factor is 1.
///
/// The reason the obvious legs cannot see it is worth stating: an integer scalar
/// divides, preserves every real root, and preserves square-freeness. Root-set
/// equality — the strongest leg the `square_free_in` check has — is blind to it
/// by construction. What pins it is Gauss's lemma:
///
/// `square_free(p) = i * square_free(c) * sqfpart_x(pp)` where `i` is the integer
/// content of `p` and both `c` and `pp` are integer-primitive; exact division
/// preserves primitivity, so the two right-hand factors contribute content `1` and
///
/// > `int_content(square_free(p)) == int_content(p)`  exactly.
///
/// That identity is leg (b), and it is the leg that catches the defect.
pub(crate) fn check_pm_square_free_all(z3: &Z3, g: &GenPm, sab: Sabotage) -> Outcome {
    let mut m = OPolyMgr::new();
    let s = m.mk(&g.s_terms);
    let other = m.mk(&g.a_terms);
    if m.is_zero(&s) || m.is_zero(&other) {
        return Outcome::Skipped("degenerate factor");
    }
    // A deliberately non-unit integer scalar, so the content leg has something
    // to see on essentially every case rather than only when the generator
    // happens to draw common coefficients. Derived from the case's own point so
    // it stays deterministic and does not perturb the generator's RNG stream.
    let scale = 2 + g.point.first().map_or(0, |(_, v)| {
        (v.magnitude() % 5u32)
            .to_string()
            .parse::<i64>()
            .unwrap_or(0)
    });
    let base = m.mul(&s, &s);
    let base = m.mul(&base, &other);
    let p = m.mul_int(&base, &BigInt::from(scale));
    if m.is_zero(&p) {
        return Outcome::Skipped("degenerate product");
    }
    let Some(mut sf) = m.square_free(&p) else {
        return Outcome::Declined("square_free refused");
    };
    if sab.on() {
        let f = saboteur(&mut m);
        sf = m.mul(&sf, &f);
    }
    let mut comparisons = 0u64;
    let ctx = |m: &OPolyMgr, p: &OMgrPoly, sf: &OMgrPoly| {
        vec![
            ("p".to_string(), render(m, p)),
            ("sf".to_string(), render(m, sf)),
        ]
    };

    // (a) The square-free part divides the input.
    comparisons += 1;
    if !m.divides(&sf, &p) {
        return Divergence::new(
            "pm-square-free-all",
            "identity",
            "the whole-polynomial square-free part does not divide p".to_string(),
            ctx(&m, &p, &sf),
        );
    }

    // (b) Gauss's lemma: the integer content survives EXACTLY. This is the leg
    //     that sees a dropped scalar, and the only one that can.
    comparisons += 1;
    let (ic_p, ic_sf) = (m.int_content(&p), m.int_content(&sf));
    if ic_p != ic_sf {
        return Divergence::new(
            "pm-square-free-all",
            "identity",
            format!(
                "integer content changed: p has {ic_p}, its square-free part has {ic_sf} \
                 (Gauss's lemma forces them equal)"
            ),
            ctx(&m, &p, &sf),
        );
    }

    // (c) Idempotence: the square-free part of a square-free part is itself,
    //     bit for bit. Catches a square that was only partly removed.
    if !sab.on() {
        let Some(sf2) = m.square_free(&sf) else {
            return Outcome::Declined("square_free refused its own output");
        };
        comparisons += 1;
        if sf2 != sf {
            return Divergence::new(
                "pm-square-free-all",
                "identity",
                "square_free is not idempotent: a second application changed the answer"
                    .to_string(),
                ctx(&m, &p, &sf),
            );
        }
    }

    // (d) The planted square really went away: a repeated non-constant factor
    //     must cost the radical some total degree.
    if !m.is_const(&s) {
        comparisons += 1;
        if m.total_degree(&sf) >= m.total_degree(&p) {
            return Divergence::new(
                "pm-square-free-all",
                "identity",
                format!(
                    "p contains the square of a non-constant factor, but its square-free part \
                     did not drop in total degree ({} vs {})",
                    m.total_degree(&sf),
                    m.total_degree(&p)
                ),
                ctx(&m, &p, &sf),
            );
        }
    }

    // (e) Nothing was dropped ENTIRELY: `p | sf^k` for some `k` no larger than
    //     the total degree, since no factor's multiplicity can exceed it. Only
    //     conclusive while that bound is inside the cost cap.
    let td = m.total_degree(&p) as usize;
    let kmax = td.min(6);
    if kmax >= 1 && m.len(&sf) <= 40 {
        let mut ok = false;
        for k in 1..=kmax {
            let powk = m.pow(&sf, u32::try_from(k).unwrap_or(1));
            comparisons += 1;
            if m.divides(&p, &powk) {
                ok = true;
                break;
            }
        }
        if !ok && kmax == td {
            return Divergence::new(
                "pm-square-free-all",
                "identity",
                format!("p divides no power sf^k for k <= {kmax}: a factor was lost outright"),
                ctx(&m, &p, &sf),
            );
        }
    }

    // (f) The z3 leg: identical real root sets after specialization.
    let (Some(pb), Some(sb)) = (
        m.specialize(&p, X, &g.point),
        m.specialize(&sf, X, &g.point),
    ) else {
        return Outcome::Skipped("specialization left a variable standing");
    };
    if pb.is_empty() || sb.is_empty() {
        return Outcome::Skipped("a specialization vanished");
    }
    let (Some(pr), Some(sr)) = (z3.roots(&to_rationals(&pb)), z3.roots(&to_rationals(&sb))) else {
        return Outcome::Skipped("z3 declined a specialization");
    };
    comparisons += 1;
    if pr.len() != sr.len() {
        return Divergence::new(
            "pm-square-free-all",
            "z3",
            format!(
                "root counts differ: p has {} distinct real roots, its square-free part has {}",
                pr.len(),
                sr.len()
            ),
            vec![
                ("p".to_string(), render(&m, &p)),
                ("sf".to_string(), render(&m, &sf)),
                ("p_bar".to_string(), render_dense(&pb)),
                ("sf_bar".to_string(), render_dense(&sb)),
            ],
        );
    }
    for (i, (a, b)) in pr.iter().zip(sr.iter()).enumerate() {
        comparisons += 1;
        if !z3.eq(*a, *b) {
            return Divergence::new(
                "pm-square-free-all",
                "z3",
                format!("root #{i} of p and of its square-free part differ"),
                vec![
                    ("p".to_string(), render(&m, &p)),
                    ("sf".to_string(), render(&m, &sf)),
                    ("p_bar".to_string(), render_dense(&pb)),
                    ("sf_bar".to_string(), render_dense(&sb)),
                ],
            );
        }
    }
    Outcome::Match(comparisons)
}

// ---------------------------------------------------------------------------
// Coefficient growth measurement
// ---------------------------------------------------------------------------

/// A remainder chain aborts once a coefficient passes this width. Reaching it
/// is the MEASUREMENT, not a failure: it records that the chain became
/// unusable rather than letting the process be killed by the OS.
///
/// MEASURED: without this guard the naive chain at depth 6 was SIGKILLed
/// (exit 137) on this machine after producing an 818-bit remainder at depth 5.
const CHAIN_BIT_ABORT: u64 = 60_000;

/// A remainder chain also aborts once a remainder passes this many terms —
/// sparse multivariate blow-up is in the TERM COUNT as much as in the
/// coefficients, and the term count is what actually exhausts memory.
const CHAIN_TERM_ABORT: usize = 40_000;

/// One row of the coefficient-growth measurement.
pub(crate) struct GrowthRow {
    /// How many cofactors were multiplied in on each side.
    pub(crate) depth: usize,
    /// Widest input coefficient, in bits.
    pub(crate) input_bits: u64,
    /// Widest coefficient in a plain pseudo-remainder chain, in bits: no
    /// content removal, no fraction-free division. This is what "naive" costs.
    pub(crate) naive_peak_bits: u64,
    /// Whether the naive chain hit an abort guard.
    pub(crate) naive_aborted: bool,
    /// Widest coefficient the SUBRESULTANT PRS produces on the path
    /// `polymanager::gcd` actually walks, in bits.
    pub(crate) prs_peak_bits: u64,
    /// Whether the subresultant chain hit an abort guard.
    pub(crate) prs_aborted: bool,
    /// Width of the answer the modular path reconstructed, in bits.
    pub(crate) mod_ans_bits: u64,
    /// Whether the two GCD implementations agreed.
    pub(crate) agreed: bool,
    /// Whether the modular path certified an answer at all.
    pub(crate) modular_certified: bool,
    /// Wall time of the PRS gcd, in microseconds.
    pub(crate) prs_us: u128,
    /// Wall time of the modular gcd, in microseconds.
    pub(crate) mod_us: u128,
    /// Widest TERM COUNT a plain pseudo-remainder chain reached.
    pub(crate) naive_peak_terms: usize,
    /// Widest TERM COUNT the subresultant PRS reached.
    ///
    /// Reported because a verifier showed the coefficient columns alone are
    /// misleading: on genuinely multivariate inputs the blow-up is in the term
    /// count and the wall time, NOT in the coefficient width, and this harness
    /// walked a univariate-in-`x` chain where that never showed.
    pub(crate) prs_peak_terms: usize,
}

/// One row of the MULTIVARIATE cost measurement.
///
/// Separate from [`GrowthRow`] because it measures a different failure mode.
/// `GrowthRow` walks a chain that is univariate in `x` with `y`/`z`
/// coefficients, where the subresultant PRS finishes in microseconds and the
/// coefficient ratio is the whole story. A verifier built genuinely
/// multivariate inputs and found the PRS taking SECONDS while returning a
/// 10-bit answer — cost that no coefficient-width column can show, on exactly
/// the inputs where `mod_gcd` declines. Any layer above that comes to depend on
/// `gcd` latency needs this table, not the other one.
pub(crate) struct MvCostRow {
    /// Human-readable shape.
    pub(crate) label: &'static str,
    /// Terms in each input.
    pub(crate) u_terms: usize,
    pub(crate) v_terms: usize,
    /// Degree of the inputs in the main variable.
    pub(crate) deg_x: u32,
    /// Widest input coefficient, in bits.
    pub(crate) input_bits: u64,
    /// Wall time of the PRS gcd, in MILLIseconds — the unit the answer needs.
    pub(crate) prs_ms: u128,
    /// Terms and width of the PRS answer.
    pub(crate) prs_ans_terms: usize,
    pub(crate) prs_ans_bits: u64,
    /// Wall time of both paths in MICROseconds.
    ///
    /// The modular column was milliseconds and now reads `0` on every shape,
    /// which hides the result rather than showing it. Microseconds is the unit
    /// the modular path needs, and the ratio is computed from these so a
    /// sub-millisecond win is not divided by a rounded-down zero.
    pub(crate) prs_us: u128,
    pub(crate) mod_us: u128,
    /// Whether the modular path certified an answer at all.
    pub(crate) mod_certified: bool,
    /// Whether the two agreed (vacuously true when the modular path declined).
    pub(crate) agreed: bool,
    /// WHY the modular path declined (`"certified"` when it did not).
    ///
    /// This column is the one the cost table was missing: "3 of 5 shapes
    /// decline" is a fact with no attached mechanism, and a fix aimed at the
    /// wrong mechanism is how a lane burns itself.
    pub(crate) decline_reason: &'static str,
    /// Primes the attempt actually entered, and evaluation points it consumed
    /// across every level. Together these say whether the work was spent or
    /// abandoned.
    pub(crate) primes_used: u32,
    pub(crate) eval_points: u32,
    /// Wall time of the DISPATCHING entry point `PolyManager::gcd`, in
    /// microseconds — what a caller above this layer actually pays. Distinct
    /// from `prs_us`, which times the PRS with the modular path disabled all
    /// the way down.
    pub(crate) gcd_us: u128,
    /// Whether the dispatching entry point returned the same answer as the
    /// PRS-only path. Preferring a CERTIFIED fast path must not change any
    /// answer, only the time taken to reach it.
    pub(crate) gcd_agrees: bool,
}

/// The multivariate shapes measured. Chosen to bracket the region a verifier
/// found expensive, not swept.
const MV_SHAPES: [(&str, usize, u32, u32, u64); 5] = [
    // label, terms per factor, max deg per var, vars, coefficient bound
    ("2var small", 3, 2, 2, 6),
    ("2var deg4 wide", 5, 4, 2, 64),
    ("3var deg3", 4, 3, 3, 64),
    ("3var deg5", 5, 5, 3, 1024),
    ("3var deg5 wide coeffs", 5, 5, 3, 1_048_576),
];

/// How many shapes the multivariate cost table has.
pub(crate) fn mv_shape_count() -> usize {
    MV_SHAPES.len()
}

/// Build the multivariate GCD problem for one shape.
///
/// Factored out of [`measure_mv_cost`] so that the decline census measures the
/// SAME instances the cost table times — a census taken on a differently
/// generated pool would answer a different question than the one the cost table
/// asks.
#[allow(clippy::cast_possible_truncation)]
pub(crate) fn mv_instance(idx: usize) -> (OPolyMgr, OMgrPoly, OMgrPoly, &'static str) {
    let (label, nterms, maxdeg, nvars, coeff_bound) = MV_SHAPES[idx % MV_SHAPES.len()];
    let mut rng = Rng::new(0xC057_0000 + idx as u64);
    let mut m = OPolyMgr::new();

    let draw = |m: &mut OPolyMgr, rng: &mut Rng| -> OMgrPoly {
        let mut terms: Vec<(Vec<(u32, u32)>, BigInt)> = Vec::new();
        for _ in 0..nterms {
            let mut pows: Vec<(u32, u32)> = Vec::new();
            for v in 0..nvars {
                let e = rng.below(u64::from(maxdeg) + 1) as u32;
                if e > 0 {
                    pows.push((v, e));
                }
            }
            let c = rng.below(coeff_bound * 2 + 1) as i64 - coeff_bound as i64;
            if c != 0 {
                terms.push((pows, BigInt::from(c)));
            }
        }
        if terms.is_empty() {
            terms.push((vec![(0, 1)], BigInt::one()));
        }
        m.mk(&terms)
    };

    // A planted common factor times a distinct cofactor on each side.
    let g = draw(&mut m, &mut rng);
    let a = draw(&mut m, &mut rng);
    let b = draw(&mut m, &mut rng);
    let u = m.mul(&g, &a);
    let v = m.mul(&g, &b);
    (m, u, v, label)
}

/// Build one multivariate GCD problem and MEASURE what it costs in wall time
/// and term count.
#[allow(clippy::cast_possible_truncation)]
pub(crate) fn measure_mv_cost(idx: usize) -> MvCostRow {
    use std::time::Instant;
    let (mut m, u, v, label) = mv_instance(idx);

    let input_bits = m.max_coeff_bits(&u).max(m.max_coeff_bits(&v));
    let (u_terms, v_terms) = (m.len(&u), m.len(&v));
    let deg_x = m.degree(&u, X).max(m.degree(&v, X));

    let t0 = Instant::now();
    let prs = m.gcd_via_prs(&u, &v);
    let prs_us = t0.elapsed().as_micros();
    let tg = Instant::now();
    let dispatched = m.gcd(&u, &v);
    let gcd_us = tg.elapsed().as_micros();
    let t1 = Instant::now();
    let (modular, diag) = m.mod_gcd_diag(&u, &v);
    let mod_us = t1.elapsed().as_micros();
    let prs_ms = prs_us / 1000;

    let (prs_ans_terms, prs_ans_bits) = match &prs {
        Some(x) => (m.len(x), m.max_coeff_bits(x)),
        None => (0, 0),
    };
    MvCostRow {
        label,
        u_terms,
        v_terms,
        deg_x,
        input_bits,
        prs_ms,
        prs_ans_terms,
        prs_ans_bits,
        prs_us,
        mod_us,
        mod_certified: modular.is_some(),
        agreed: match (&prs, &modular) {
            (Some(x), Some(y)) => x == y,
            (_, None) => true, // a decline is not a disagreement
            _ => false,
        },
        decline_reason: diag.primary(),
        primes_used: diag.primes_used(),
        eval_points: diag.rec_points_tried(),
        gcd_us,
        gcd_agrees: dispatched == prs,
    }
}

/// One row of the DECLINE CENSUS: why `mod_gcd` gave up on one instance.
pub(crate) struct DeclineRow {
    pub(crate) label: &'static str,
    pub(crate) reason: &'static str,
    pub(crate) certified: bool,
    pub(crate) primes_used: u32,
    pub(crate) prime_bad_coeff: u32,
    pub(crate) prime_bad_lcg: u32,
    pub(crate) prime_rec_declined: u32,
    pub(crate) lc_gate_rejected: u32,
    pub(crate) cert_reject_u: u32,
    pub(crate) cert_reject_v: u32,
    pub(crate) rec_inner_declined: u32,
    pub(crate) rec_budget_exhausted: u32,
    pub(crate) rec_lch_mismatch: u32,
    pub(crate) rec_trialdiv_reject: u32,
    pub(crate) rec_unlucky_degree: u32,
    pub(crate) rec_base_failed: u32,
    pub(crate) rec_content_failed: u32,
    pub(crate) rec_points_tried: u32,
    pub(crate) rec_reset_smaller: u32,
    pub(crate) rec_max_points_at_level: u32,
    pub(crate) rec_max_deg_bound: u32,
}

fn decline_row(label: &'static str, d: &ay_nra::oracle_api::OModGcdDiag) -> DeclineRow {
    DeclineRow {
        label,
        reason: d.primary(),
        certified: d.certified(),
        primes_used: d.primes_used(),
        prime_bad_coeff: d.prime_bad_coeff(),
        prime_bad_lcg: d.prime_bad_lcg(),
        prime_rec_declined: d.prime_rec_declined(),
        lc_gate_rejected: d.lc_gate_rejected(),
        cert_reject_u: d.cert_reject_u(),
        cert_reject_v: d.cert_reject_v(),
        rec_inner_declined: d.rec_inner_declined(),
        rec_budget_exhausted: d.rec_budget_exhausted(),
        rec_lch_mismatch: d.rec_lch_mismatch(),
        rec_trialdiv_reject: d.rec_trialdiv_reject(),
        rec_unlucky_degree: d.rec_unlucky_degree(),
        rec_base_failed: d.rec_base_failed(),
        rec_content_failed: d.rec_content_failed(),
        rec_points_tried: d.rec_points_tried(),
        rec_reset_smaller: d.rec_reset_smaller(),
        rec_max_points_at_level: d.rec_max_points_at_level(),
        rec_max_deg_bound: d.rec_max_deg_bound(),
    }
}

/// Diagnose one multivariate shape from [`MV_SHAPES`].
pub(crate) fn diagnose_mv(idx: usize) -> DeclineRow {
    let (mut m, u, v, label) = mv_instance(idx);
    let (_, diag) = m.mod_gcd_diag(&u, &v);
    decline_row(label, &diag)
}

/// Diagnose one RANDOM case, drawn from exactly the generator the
/// `pm-mod-gcd` differential check uses, so the census population and the
/// checked population are the same one.
pub(crate) fn diagnose_random(rng: &mut Rng) -> Option<DeclineRow> {
    let g = gen_pm(rng);
    let mut m = OPolyMgr::new();
    let gg = m.mk(&g.g_terms);
    let aa = m.mk(&g.a_terms);
    let bb = m.mk(&g.b_terms);
    if m.is_zero(&gg) || m.is_zero(&aa) || m.is_zero(&bb) {
        return None;
    }
    let u = m.mul(&gg, &aa);
    let v = m.mul(&gg, &bb);
    if m.is_zero(&u) || m.is_zero(&v) {
        return None;
    }
    let (_, diag) = m.mod_gcd_diag(&u, &v);
    Some(decline_row(g.shape, &diag))
}

/// Walk a plain exact-pseudo-remainder chain and report the widest coefficient
/// it produced. No content removal and no fraction-free division: this is the
/// chain a first implementation writes, and the column it fills is the reason
/// z3 does not use one.
fn naive_chain_peak(m: &mut OPolyMgr, u: &OMgrPoly, v: &OMgrPoly) -> (u64, usize, bool) {
    let mut a = u.clone();
    let mut b = v.clone();
    if m.degree(&a, X) < m.degree(&b, X) {
        std::mem::swap(&mut a, &mut b);
    }
    let mut peak = m.max_coeff_bits(&a).max(m.max_coeff_bits(&b));
    let mut peak_terms = m.len(&a).max(m.len(&b));
    for _ in 0..16 {
        if m.is_zero(&b) || m.degree(&b, X) == 0 {
            return (peak, peak_terms, false);
        }
        let Some(pd) = m.pseudo_division(&a, &b, X, true) else {
            return (peak, peak_terms, false);
        };
        peak = peak.max(m.max_coeff_bits(&pd.rem));
        peak_terms = peak_terms.max(m.len(&pd.rem));
        if peak > CHAIN_BIT_ABORT || m.len(&pd.rem) > CHAIN_TERM_ABORT {
            return (peak, peak_terms, true);
        }
        a = b;
        b = pd.rem;
    }
    (peak, peak_terms, false)
}

/// Walk the SUBRESULTANT PRS exactly as `polymanager::gcd_prs` does — content
/// removed up front, and each remainder divided by `g * h^delta` — and report
/// the widest coefficient it produced.
///
/// This is a second, independent transcription of the same recurrence, written
/// against the public facade. Its answer is not compared to the manager's (the
/// manager's `gcd` is what the checks cover); what it is for is measuring the
/// intermediate widths the manager's own path passes through, which no
/// external observer can otherwise see.
fn subresultant_chain_peak(m: &mut OPolyMgr, u: &OMgrPoly, v: &OMgrPoly) -> (u64, usize, bool) {
    let mut a = u.clone();
    let mut b = v.clone();
    if m.degree(&a, X) < m.degree(&b, X) {
        std::mem::swap(&mut a, &mut b);
    }
    let (Some((_, _, mut pp_u)), Some((_, _, mut pp_v))) = (m.iccp(&a, X), m.iccp(&b, X)) else {
        return (0, 0, true);
    };
    let mut peak = m.max_coeff_bits(&pp_u).max(m.max_coeff_bits(&pp_v));
    let mut peak_terms = m.len(&pp_u).max(m.len(&pp_v));
    let mut gg = m.constant(BigInt::one());
    let mut hh = m.constant(BigInt::one());
    for _ in 0..16 {
        if m.is_zero(&pp_v) || m.degree(&pp_v, X) == 0 {
            return (peak, peak_terms, false);
        }
        let delta = m.degree(&pp_u, X) - m.degree(&pp_v, X);
        let Some(pd) = m.pseudo_division(&pp_u, &pp_v, X, true) else {
            return (peak, peak_terms, false);
        };
        let rem = pd.rem;
        peak = peak.max(m.max_coeff_bits(&rem));
        peak_terms = peak_terms.max(m.len(&rem));
        if peak > CHAIN_BIT_ABORT || m.len(&rem) > CHAIN_TERM_ABORT {
            return (peak, peak_terms, true);
        }
        if m.is_zero(&rem) || m.is_const(&rem) {
            return (peak, peak_terms, false);
        }
        let Some(mut next) = m.exact_div(&rem, &gg) else {
            return (peak, peak_terms, true);
        };
        for _ in 0..delta {
            match m.exact_div(&next, &hh) {
                Some(x) => next = x,
                None => return (peak, peak_terms, true),
            }
        }
        pp_u = pp_v;
        pp_v = next;
        peak = peak.max(m.max_coeff_bits(&pp_v));
        peak_terms = peak_terms.max(m.len(&pp_v));
        gg = m.lc(&pp_u, X);
        let mut new_h = m.constant(BigInt::one());
        for _ in 0..delta {
            new_h = m.mul(&new_h, &gg);
        }
        if delta > 1 {
            for _ in 0..delta - 1 {
                match m.exact_div(&new_h, &hh) {
                    Some(x) => new_h = x,
                    None => return (peak, peak_terms, true),
                }
            }
        }
        hh = new_h;
    }
    (peak, peak_terms, false)
}

/// Build an increasingly ill-conditioned GCD problem and MEASURE what each
/// implementation does to the coefficients.
///
/// The instance is a planted quadratic-in-`x` common factor multiplied by
/// `depth` distinct trivariate cofactors on each side. Coefficient growth in a
/// remainder sequence is driven by the number of steps, which is what `depth`
/// controls, so this is the axis that separates the three columns.
pub(crate) fn measure_growth(depth: usize) -> GrowthRow {
    use std::time::Instant;
    let mut m = OPolyMgr::new();
    // g = x^2 - 3xy + 7z
    let g = m.mk(&[
        (vec![(0, 2)], BigInt::from(1)),
        (vec![(0, 1), (1, 1)], BigInt::from(-3)),
        (vec![(2, 1)], BigInt::from(7)),
    ]);
    let mut u = g.clone();
    let mut v = g.clone();
    for k in 1..=depth as i64 {
        let f = m.mk(&[
            (vec![(0, 1)], BigInt::from(k)),
            (vec![(1, 1)], BigInt::from(k + 1)),
            (vec![], BigInt::from(k * 3 - 1)),
        ]);
        u = m.mul(&u, &f);
        let h = m.mk(&[
            (vec![(0, 1)], BigInt::from(k + 2)),
            (vec![(2, 1)], BigInt::from(-k)),
            (vec![], BigInt::from(k * 5 + 2)),
        ]);
        v = m.mul(&v, &h);
    }
    let input_bits = m.max_coeff_bits(&u).max(m.max_coeff_bits(&v));

    let t0 = Instant::now();
    let prs = m.gcd_via_prs(&u, &v);
    let prs_us = t0.elapsed().as_micros();
    let tg = Instant::now();
    let dispatched = m.gcd(&u, &v);
    let gcd_us = tg.elapsed().as_micros();
    let t1 = Instant::now();
    let modular = m.mod_gcd(&u, &v);
    let mod_us = t1.elapsed().as_micros();

    let (naive_peak_bits, naive_peak_terms, naive_aborted) = naive_chain_peak(&mut m, &u, &v);
    let (prs_peak_bits, prs_peak_terms, prs_aborted) = subresultant_chain_peak(&mut m, &u, &v);

    let mod_ans_bits = match &modular {
        Some(x) => m.max_coeff_bits(x),
        None => 0,
    };
    GrowthRow {
        depth,
        input_bits,
        naive_peak_bits,
        naive_aborted,
        prs_peak_bits,
        prs_aborted,
        mod_ans_bits,
        agreed: match (&prs, &modular) {
            (Some(a), Some(b)) => a == b,
            _ => false,
        },
        modular_certified: modular.is_some(),
        prs_us,
        mod_us,
        naive_peak_terms,
        prs_peak_terms,
    }
}

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

/// Variable set available to a generated factor.
#[derive(Clone, Copy)]
enum FactorVariables {
    MainOnly,
    All,
}

/// Draw one factor: between one and [`MAX_TERMS`] terms over the selected
/// variables, with a non-zero constant term forced often enough that the
/// content/primitive split has something to do.
fn gen_factor(rng: &mut Rng, variables: FactorVariables) -> Vec<(Vec<(u32, u32)>, BigInt)> {
    let nterms = 1 + rng.below(MAX_TERMS as u64) as usize;
    let mut out: Vec<(Vec<(u32, u32)>, BigInt)> = Vec::with_capacity(nterms);
    for _ in 0..nterms {
        let mut pows: Vec<(u32, u32)> = Vec::new();
        let dx = rng.below(u64::from(MAX_DEG_X) + 1) as u32;
        if dx > 0 {
            pows.push((X, dx));
        }
        if matches!(variables, FactorVariables::All) {
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
    let (shape, variables) = match rng.below(4) {
        0 => ("x-only", FactorVariables::MainOnly),
        1 => ("content", FactorVariables::All),
        2 => ("monic", FactorVariables::All),
        _ => ("dense", FactorVariables::All),
    };
    let mut g_terms = gen_factor(rng, variables);
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
        a_terms: gen_factor(rng, variables),
        b_terms: gen_factor(rng, variables),
        s_terms: gen_factor(rng, variables),
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

fn add_matches(total: &mut u64, outcome: Outcome) -> Result<(), Outcome> {
    match outcome {
        Outcome::Match(n) => {
            *total += n;
            Ok(())
        }
        other => Err(other),
    }
}

mod gcd;
mod growth;
mod pseudo_division;
mod representation;
mod square_free;

pub(crate) use gcd::{check_pm_gcd, check_pm_mod_gcd, check_pm_mod_gcd_diag};
pub(crate) use growth::{
    diagnose_mv, diagnose_random, measure_growth, measure_mv_cost, mv_shape_count, DeclineRow,
};
pub(crate) use pseudo_division::check_pm_pseudo_div;
pub(crate) use representation::check_pm_rep;
pub(crate) use square_free::{check_pm_square_free, check_pm_square_free_all};

// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The differential checks themselves.
//!
//! Every check compares an ANSWER AY produced against the same answer computed
//! by the reference libz3. Three outcomes are kept strictly apart, because
//! conflating them is how a fuzz campaign talks itself into a clean run:
//!
//!   * **Match** — both sides answered and agreed. Counted.
//!   * **Declined** — AY returned its fail-closed `None` (budget exhausted,
//!     out of fragment). NOT a divergence, but tracked and reported, because a
//!     high decline rate means the oracle is not actually exercising anything.
//!   * **Diverged** — both sides answered and disagreed. This is a bug in AY
//!     (or, far less likely, in z3), and it is dumped as a minimal reproducer.
//!
//! A z3 error or a z3 refusal is `Skipped`, never a divergence: the oracle is
//! not entitled to call a bug on the reference implementation's behalf.

use std::cmp::Ordering;

use ay_nra::oracle_api::{self as ay, OAlg, OPoly, ORoot};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Zero};

use crate::anum;
use crate::explain;
use crate::ialg;
use crate::mpbq;
use crate::mv;
use crate::pmgr;
use crate::polygen::{self, GenPoly, Rng};
use crate::subres;
use crate::upoly;
use crate::z3::{Ptr, Z3};

/// Result of running one check on one generated input.
pub(crate) enum Outcome {
    /// Both sides answered and agreed; `comparisons` individual assertions held.
    Match(u64),
    /// AY fail-closed (`None`). Not a divergence.
    Declined(&'static str),
    /// Input not applicable to this check, or z3 declined / errored.
    Skipped(&'static str),
    /// Both sides answered and disagreed.
    Diverged(Box<Divergence>),
}

/// A divergence, with everything needed to reproduce it from a cold start.
pub(crate) struct Divergence {
    pub(crate) check: &'static str,
    /// `"z3"` for a genuine differential; `"identity"` for an exact algebraic
    /// identity AY violated on its own (also a real bug, but not a z3 verdict).
    pub(crate) reference: &'static str,
    pub(crate) detail: String,
    pub(crate) inputs: Vec<(String, String)>,
}

impl Divergence {
    pub(crate) fn new(
        check: &'static str,
        reference: &'static str,
        detail: String,
        inputs: Vec<(String, String)>,
    ) -> Outcome {
        Outcome::Diverged(Box::new(Self {
            check,
            reference,
            detail,
            inputs,
        }))
    }
}

/// The checks the fuzz driver rotates through.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Check {
    /// Real-root isolation vs `Z3_algebraic_roots`.
    Roots,
    /// Square-free part preserves the exact real root set.
    SquareFree,
    /// GCD's real roots are exactly the shared real roots, and it divides both.
    Gcd,
    /// Sturm root count on `(a, b]` vs z3's root list.
    Sturm,
    /// Sign of a polynomial at a real algebraic point vs `Z3_algebraic_eval`.
    SignAt,
    /// Sylvester resultant vs `Z3_polynomial_subresultants`.
    Resultant,
    /// Exact algebraic addition / multiplication vs `Z3_algebraic_add/mul`.
    Arith,
    /// Exact algebraic comparison vs `Z3_algebraic_lt/eq/gt`.
    Compare,
    /// FULL principal subresultant chain (`subresultant::psc_chain`) vs
    /// `Z3_polynomial_subresultants`.
    PscChain,
    /// `subresultant::discriminant` vs `Res(f, f')` as z3 computes it.
    Discriminant,
    /// `subresultant_chain_prs` vs `subresultant_chain_det` — the module's two
    /// independent implementations of the same chain.
    ChainAgreement,
    /// Bivariate psc chain over `Z[y]`, compared by specialization.
    BivariatePsc,
    /// Bivariate `Res_x`, compared by specialization.
    BivariateResultant,
    /// `mroot::isolate_roots_at` vs `Z3_algebraic_roots` — root isolation of a
    /// MULTIVARIATE polynomial at an algebraic sample point.
    MvRoots,
    /// `mroot::eval_sign_at` vs `Z3_algebraic_eval` — the exact sign at an
    /// algebraic sample point, which is what the root sieve rests on.
    MvSignAt,
    /// `mroot::isolate_roots_closest_at` vs the same selection made from z3's
    /// full root list with z3's own comparisons.
    MvClosest,
    /// `polymanager` canonical form, interning and the recursive x-view.
    PmRep,
    /// `polymanager::pseudo_division` — the exact identity, plus the signs it
    /// forces at the real roots of the specialized divisor.
    PmPseudoDiv,
    /// `polymanager::gcd` — the subresultant PRS GCD.
    PmGcd,
    /// `polymanager::mod_gcd` — Brown's modular GCD, against the PRS GCD.
    PmModGcd,
    /// `polymanager::square_free_in` — real root set preserved exactly.
    PmSquareFree,
    /// `polymanager::square_free` — the whole-polynomial entry point, including
    /// the integer content a root-set leg is structurally blind to.
    PmSquareFreeAll,
    /// `polymanager::mod_gcd` again, through the INSTRUMENTED entry point: the
    /// decline diagnosis must be inert and must describe what happened, and a
    /// certified answer must be MAXIMAL (equal to the PRS answer and a multiple
    /// of the planted factor), not merely a divisor of both inputs.
    PmModGcdDiag,
    /// `upoly`'s `Z` substrate: content/primitive split, pseudo-division, and
    /// reduction mod `p` as a ring homomorphism. z3-backed on the
    /// pseudo-division identity at a real root of the divisor.
    UpSubstrate,
    /// `upoly::ZPoly::square_free_decomposition` — Yun over `Z`, with the
    /// multiplicities. The exact identity `c * prod f_i^i == input`, plus a
    /// z3-backed root-set equality for the radical.
    UpSqfDecomp,
    /// `upoly::Zp::distinct_degree` in isolation, against the field-theoretic
    /// characterization of each bucket and with `ddf_iters` re-derived from
    /// the answer.
    UpZpDdf,
    /// `upoly::Zp::factor` — the exact product identity, plus Rabin's
    /// irreducibility test as an independent witness, plus the `edf_splits`
    /// counter pinned to the answer.
    UpZpFactor,
    /// `mpbq::Bq` — the dyadic type. Arithmetic against `Z3_algebraic_add/mul`
    /// AND against `BigRational`, canonical form, and the representability
    /// predicate with both a positive and a negative control.
    BqArith,
    /// `mpbq::refine_to_width` — the isolating-interval refinement loop,
    /// checked against z3's own root with `Z3_algebraic_lt/gt`, plus the exact
    /// width identity that pins the step counter.
    BqRefine,
    /// `mpbq::select_small` — the simplest dyadic strictly inside an interval.
    /// Minimality is checked in BOTH directions, and against an independent
    /// minimal-`k` search written over `BigRational`.
    BqSelect,
    /// `mpbq`'s guards, fired on purpose and each paired with a positive
    /// control, plus the liveness assertion for the one loop whose bound is a
    /// caller budget rather than a derived quantity.
    BqDegenerate,
    /// `anum`'s representation and its invariant: normalization, the dyadic
    /// isolating interval against `Z3_algebraic_roots`, the DERIVED root index,
    /// refinement, and the constructor's refusals with positive controls.
    AnumRep,
    /// `anum::cmp_anum` vs `Z3_algebraic_lt/_eq/_gt`, including the EQUAL case
    /// through different defining polynomials — the one refinement can never
    /// decide — with the zero-bisection liveness assertion.
    AnumCompare,
    /// `anum::sign_of_poly` vs `Z3_algebraic_eval`, with the zero case asked on
    /// purpose in both directions so the gcd certificate is a real witness.
    AnumSignAt,
    /// `anum::add` / `anum::mul` vs `Z3_algebraic_add` / `Z3_algebraic_mul`,
    /// with an inert decline diagnosis so a failed construction is a divergence
    /// rather than a decline.
    AnumArith,
    /// `anum::root_separation_exponent` and `anum::sturm_count_in` as PURE
    /// functions, validated against z3's root list BEFORE the consumer runs.
    AnumSeparation,
    /// `ialg` set membership and normalisation: AY's normalised set vs
    /// membership in the RAW interval list computed by `Z3_algebraic_lt/_gt/_eq`,
    /// probed at the algebraic endpoints as well as at rationals.
    IaMember,
    /// `ialg::IntervalSet::intersect` vs the conjunction of z3-computed
    /// memberships, plus the justification-union requirement.
    IaIntersect,
    /// `ialg::IntervalSet::complement` / `subtract` vs z3-computed
    /// non-membership, probed at the endpoints where strictness is visible.
    IaComplement,
    /// `ialg::IntervalSet::pick`: z3 adjudicates that the sample point is in
    /// the set, and an independent search adjudicates the rung's MINIMALITY.
    IaPick,
    /// `ialg::from_sign_condition` as a PURE function on z3's own root list,
    /// checked cell-by-cell against `Z3_algebraic_eval`.
    IaSignCells,
    /// `explain::clause_is_valid` — the DEFINING PROPERTY of a learned clause —
    /// against a cell decomposition z3 builds entirely by itself. The highest
    /// stakes check in the oracle: an explanation that is not implied is a
    /// wrong `unsat`, and no other gate can see one.
    ExImplied,
    /// `explain::explain_univariate` end to end: a clause is emitted only for a
    /// real conflict, only when z3 independently agrees the cited conjunction
    /// is unsatisfiable, and only when it is false under the trail.
    ExProduce,
    /// The COUNTERMODEL, adjudicated rather than the verdict: when AY says a
    /// clause is not implied, z3 must agree that AY's witness satisfies every
    /// cited literal.
    ExWitness,
    /// `explain::project` and `explain::relevant_pairs` — the CAD projection
    /// operator, compared against `Z3_polynomial_subresultants` by
    /// specialization.
    ExProject,
}

impl Check {
    /// Short stable name for reporting.
    pub(crate) fn name(self) -> &'static str {
        match self {
            Self::Roots => "roots",
            Self::SquareFree => "square-free",
            Self::Gcd => "gcd",
            Self::Sturm => "sturm-count",
            Self::SignAt => "sign-at-algebraic",
            Self::Resultant => "resultant",
            Self::Arith => "algebraic-arith",
            Self::Compare => "algebraic-compare",
            Self::PscChain => "psc-chain",
            Self::Discriminant => "discriminant",
            Self::ChainAgreement => "subresultant-chain-agreement",
            Self::BivariatePsc => "bivariate-psc",
            Self::BivariateResultant => "bivariate-resultant",
            Self::MvRoots => "mv-isolate-roots",
            Self::MvSignAt => "mv-sign-at",
            Self::MvClosest => "mv-closest-roots",
            Self::PmRep => "pm-representation",
            Self::PmPseudoDiv => "pm-pseudo-division",
            Self::PmGcd => "pm-gcd",
            Self::PmModGcd => "pm-mod-gcd",
            Self::PmSquareFree => "pm-square-free",
            Self::PmSquareFreeAll => "pm-square-free-all",
            Self::PmModGcdDiag => "pm-mod-gcd-diag",
            Self::UpSubstrate => "up-z-substrate",
            Self::UpSqfDecomp => "up-z-sqf-decomp",
            Self::UpZpDdf => "up-zp-ddf",
            Self::UpZpFactor => "up-zp-factor",
            Self::BqArith => "bq-arith",
            Self::BqRefine => "bq-refine",
            Self::BqSelect => "bq-select",
            Self::BqDegenerate => "bq-degenerate",
            Self::AnumRep => "anum-representation",
            Self::AnumCompare => "anum-compare",
            Self::AnumSignAt => "anum-sign-at",
            Self::AnumArith => "anum-arith",
            Self::AnumSeparation => "anum-separation",
            Self::IaMember => "ialg-membership",
            Self::IaIntersect => "ialg-intersect",
            Self::IaComplement => "ialg-complement",
            Self::IaPick => "ialg-pick",
            Self::IaSignCells => "ialg-sign-cells",
            Self::ExImplied => "explain-clause-implied",
            Self::ExProduce => "explain-produce",
            Self::ExWitness => "explain-countermodel",
            Self::ExProject => "explain-projection",
        }
    }
}

/// Every check, in a fixed order (the driver indexes into this).
///
/// # RETRACTED: appending does NOT preserve historical case numbering
///
/// Five consecutive lanes wrote, in this file and in their commit messages,
/// that appending a check leaves earlier residues untouched so a historical
/// `--seed` still reproduces case-for-case. **That is false**, and it was false
/// every time it was written.
///
/// The driver selects with `ALL_CHECKS[i % ALL_CHECKS.len()]`
/// (`main.rs`, `cmd_fuzz`). The modulus IS the length, so growing the array
/// re-maps every case index that is not a multiple of both lengths. MEASURED:
/// `repro --seed 7777777 --case 1277` is `algebraic-arith` at 31 checks
/// (1277 % 31 = 6) and `pm-pseudo-division` at 36 (1277 % 36 = 17).
///
/// The practical consequences, both real:
///
/// * A `(seed, case)` pair identifies a case ONLY together with the check-set
///   size it was recorded under. Divergence reports in older commit messages
///   and reports cannot be replayed against a newer binary by case number.
/// * Adding a check RESHUFFLES the whole corpus, which is not merely a
///   bookkeeping problem — it draws inputs no check had seen before. The `anum`
///   append immediately exposed a genuine pre-existing `pm-pseudo-division`
///   divergence that 54,000 cases across six seeds had never reached.
///
/// Making the numbering genuinely stable would need a fixed rotation modulus
/// with unused residues skipped, which wastes a growing fraction of every run
/// (28 of 64 at today's 36 checks). That trade has not been taken. What is done
/// instead: `fuzz` and `repro` now PRINT the check-set size, so a case
/// reference carries the context needed to replay it.
pub(crate) const ALL_CHECKS: [Check; 45] = [
    Check::Roots,
    Check::SquareFree,
    Check::Gcd,
    Check::Sturm,
    Check::SignAt,
    Check::Resultant,
    Check::Arith,
    Check::Compare,
    Check::PscChain,
    Check::Discriminant,
    Check::ChainAgreement,
    Check::BivariatePsc,
    Check::BivariateResultant,
    Check::MvRoots,
    Check::MvSignAt,
    Check::MvClosest,
    Check::PmRep,
    Check::PmPseudoDiv,
    Check::PmGcd,
    Check::PmModGcd,
    Check::PmSquareFree,
    Check::PmSquareFreeAll,
    Check::PmModGcdDiag,
    Check::UpSubstrate,
    Check::UpSqfDecomp,
    Check::UpZpDdf,
    Check::UpZpFactor,
    Check::BqArith,
    Check::BqRefine,
    Check::BqSelect,
    Check::BqDegenerate,
    Check::AnumRep,
    Check::AnumCompare,
    Check::AnumSignAt,
    Check::AnumArith,
    Check::AnumSeparation,
    // Appended at 36 -> 41. As the RETRACTION above says, this re-maps every
    // case index that is not a multiple of both lengths: a `(seed, case)` pair
    // recorded under 36 checks does NOT name the same case under 41. The
    // reshuffle is useful — it draws inputs no check had seen — and the triage
    // of what it newly exposes is part of this change, not a surprise.
    Check::IaMember,
    Check::IaIntersect,
    Check::IaComplement,
    Check::IaPick,
    Check::IaSignCells,
    // Appended at 41 -> 45. As the RETRACTION above says, this re-maps every
    // case index that is not a multiple of both lengths: a `(seed, case)` pair
    // recorded under 41 checks does NOT name the same case under 45, and the
    // `ialg` append's own note one block up says the same thing about 36 -> 41.
    // The reshuffle draws inputs no check had seen, and triaging what it newly
    // exposes is part of this change.
    Check::ExImplied,
    Check::ExProduce,
    Check::ExWitness,
    Check::ExProject,
];

/// Whether to deliberately corrupt AY's answer before comparing it.
///
/// A fuzz campaign that reports zero divergences is worthless unless the
/// checks can actually fail, and "it found a bug once" is not a standing
/// guarantee. `Sabotage::On` injects a minimal, targeted error into AY's
/// answer — one extra root, one flipped sign, one off-by-one count — at
/// exactly the point where the comparison happens. Every check must then
/// report a divergence. The `selftest` subcommand runs this and fails if any
/// check stays silent.
///
/// The corruption is applied to AY's ANSWER, never to its input, so it
/// exercises the comparison itself rather than the generator.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Sabotage {
    /// Compare honestly. Every real run uses this.
    Off,
    /// Corrupt AY's answer; the check is expected to catch it.
    On,
}

impl Sabotage {
    pub(crate) fn on(self) -> bool {
        self == Self::On
    }
}

/// `x - 1/2`: the factor sabotage multiplies into a polynomial answer.
///
/// Its root `1/2` is small enough to fall inside the fuzzer's usual sampling
/// window and is rarely a root of a randomly generated polynomial, so the
/// injected extra root is almost always observable. Measured catch rate under
/// `selftest`: 213/219 for `square-free` — the misses are inputs that already
/// had `1/2` as a root, where multiplying it in again changes nothing z3 can
/// see (it reports DISTINCT roots).
fn saboteur_factor() -> OPoly {
    OPoly::from_coeffs(vec![
        BigRational::new(BigInt::from(-1), BigInt::from(2)),
        BigRational::one(),
    ])
}

/// Maximum polynomial degree the fuzzer generates.
///
/// Measured at this cap, together with the work budget: median case well under
/// a millisecond, ~260 cases/s overall, worst case 6.1 s over a 50 000-case
/// shard. Degree is the dominant cost term because AY's Sturm sequence is a
/// plain Euclidean remainder chain over `Q` with no primitive-part reduction,
/// so its intermediate coefficients grow multiplicatively; raising this cap
/// makes the run measure bignum throughput rather than agreement.
pub(crate) const MAX_DEGREE: usize = 8;

fn poly_of(g: &GenPoly) -> OPoly {
    OPoly::from_coeffs(g.coeffs.clone())
}

fn inputs1(a: &GenPoly) -> Vec<(String, String)> {
    vec![
        ("p".to_string(), polygen::render(&a.coeffs)),
        ("p.shape".to_string(), a.shape.name().to_string()),
    ]
}

fn inputs2(a: &GenPoly, b: &GenPoly) -> Vec<(String, String)> {
    vec![
        ("p".to_string(), polygen::render(&a.coeffs)),
        ("p.shape".to_string(), a.shape.name().to_string()),
        ("q".to_string(), polygen::render(&b.coeffs)),
        ("q.shape".to_string(), b.shape.name().to_string()),
    ]
}

/// Does AY's marker localize the z3 root `r`?
///
/// A `Rational(q)` marker must be *exactly* z3's root; an `Interval(lo, hi)`
/// marker must strictly contain it. There is no tolerance anywhere: both sides
/// are exact, so a near miss is a miss.
fn marker_matches(z3: &Z3, marker: &ORoot, r: Ptr) -> bool {
    match marker {
        ORoot::Rational(q) => {
            let q_ast = z3.rational(q);
            z3.eq(r, q_ast)
        }
        ORoot::Interval(lo, hi) => {
            let lo_ast = z3.rational(lo);
            let hi_ast = z3.rational(hi);
            z3.gt(r, lo_ast) && z3.lt(r, hi_ast)
        }
    }
}

fn describe_marker(m: &ORoot) -> String {
    match m {
        ORoot::Rational(r) => format!("exact {r}"),
        ORoot::Interval(lo, hi) => format!("({lo}, {hi})"),
    }
}

/// Real-root isolation: AY's markers vs z3's algebraic roots.
pub(crate) fn check_roots(z3: &Z3, p: &GenPoly, sab: Sabotage) -> Outcome {
    let ap = poly_of(p);
    if ap.degree().unwrap_or(0) < 1 {
        return Outcome::Skipped("degree < 1");
    }
    let Some(sf) = ap.square_free_part() else {
        return Outcome::Declined("square_free_part");
    };
    let Some(mut markers) = sf.isolate_roots() else {
        return Outcome::Declined("isolate_roots");
    };
    if sab.on() {
        // Drop a root AY did find; the count comparison must notice.
        if markers.pop().is_none() {
            return Outcome::Skipped("nothing to sabotage");
        }
    }
    let Some(roots) = z3.roots(&p.coeffs) else {
        return Outcome::Skipped("z3 declined");
    };
    if markers.len() != roots.len() {
        return Divergence::new(
            "roots",
            "z3",
            format!(
                "AY isolated {} real roots, z3 found {}",
                markers.len(),
                roots.len()
            ),
            inputs1(p),
        );
    }
    let mut comparisons = 1u64;
    for (i, (m, r)) in markers.iter().zip(roots.iter()).enumerate() {
        comparisons += 1;
        if !marker_matches(z3, m, *r) {
            let bracket = z3.bracket(*r, 64).map_or_else(
                || "<unbracketable>".to_string(),
                |(lo, hi)| format!("({lo}, {hi})"),
            );
            return Divergence::new(
                "roots",
                "z3",
                format!(
                    "root #{i}: AY marker {} does not contain z3's root, which lies in {bracket}",
                    describe_marker(m)
                ),
                inputs1(p),
            );
        }
    }
    Outcome::Match(comparisons)
}

/// The square-free part must have exactly the same real roots as the original,
/// and must divide it.
pub(crate) fn check_square_free(z3: &Z3, p: &GenPoly, sab: Sabotage) -> Outcome {
    let ap = poly_of(p);
    if ap.degree().unwrap_or(0) < 1 {
        return Outcome::Skipped("degree < 1");
    }
    let Some(sf) = ap.square_free_part() else {
        return Outcome::Declined("square_free_part");
    };
    // Exact algebraic identity: the square-free part divides the polynomial.
    if !sab.on() && !sf.is_zero() && !ap.rem(&sf).is_zero() {
        return Divergence::new(
            "square-free",
            "identity",
            format!(
                "square_free_part {} does not divide p",
                polygen::render(&sf.coeffs())
            ),
            inputs1(p),
        );
    }
    // THE PROPERTY THE NAME PROMISES: `sf` must actually BE square-free, i.e.
    // `gcd(sf, sf')` is a non-zero constant.
    //
    // Without this the check is strictly weaker than what its consumers rely on,
    // and provably so: the two assertions around it — "`sf` divides `p`" and
    // "`p` and `sf` have the same distinct real roots" — BOTH hold trivially for
    // a `square_free_part` that returns `p` UNCHANGED, because stripping
    // repeated factors changes multiplicities, never the root SET. An adversary
    // injected exactly that defect and this check reported ZERO divergences over
    // 4,000 cases; only 3 incidental hits leaked out through sturm-count and
    // algebraic-compare.
    //
    // That matters because square-freeness is a PRECONDITION of `isolate_roots`
    // and of nlsat projection — the code the B1 port is being built against. An
    // oracle blind to it would license the port's most load-bearing assumption.
    if !sab.on() && !sf.is_zero() {
        let d = sf.derivative();
        if !d.is_zero() {
            let g = sf.gcd(&d);
            if g.degree().unwrap_or(0) >= 1 {
                return Divergence::new(
                    "square-free",
                    "identity",
                    format!(
                        "square_free_part is NOT square-free: gcd(sf, sf') has degree {} (sf = {}, gcd = {})",
                        g.degree().unwrap_or(0),
                        polygen::render(&sf.coeffs()),
                        polygen::render(&g.coeffs())
                    ),
                    inputs1(p),
                );
            }
        }
    }

    // Sabotage: hand the root comparison a square-free part with one extra
    // real root.
    let sf = if sab.on() {
        sf.mul(&saboteur_factor())
    } else {
        sf
    };
    let sf_coeffs = sf.coeffs();
    let (Some(rp), Some(rs)) = (z3.roots(&p.coeffs), z3.roots(&sf_coeffs)) else {
        return Outcome::Skipped("z3 declined");
    };
    if rp.len() != rs.len() {
        return Divergence::new(
            "square-free",
            "z3",
            format!(
                "p has {} distinct real roots but AY's square-free part has {} (sf = {})",
                rp.len(),
                rs.len(),
                polygen::render(&sf_coeffs)
            ),
            inputs1(p),
        );
    }
    let mut comparisons = 1u64;
    for (i, (a, b)) in rp.iter().zip(rs.iter()).enumerate() {
        comparisons += 1;
        if !z3.eq(*a, *b) {
            let ba = z3.bracket(*a, 60).map_or_else(
                || "?".to_string(),
                |(lo, hi)| format!("({}, {})", to_f64(&lo), to_f64(&hi)),
            );
            let bb = z3.bracket(*b, 60).map_or_else(
                || "?".to_string(),
                |(lo, hi)| format!("({}, {})", to_f64(&lo), to_f64(&hi)),
            );
            let mut inp = inputs1(p);
            inp.push(("sf".to_string(), polygen::render(&sf_coeffs)));
            inp.push(("p.root".to_string(), ba));
            inp.push(("sf.root".to_string(), bb));
            return Divergence::new(
                "square-free",
                "z3",
                format!("root #{i} of p differs from root #{i} of AY's square-free part"),
                inp,
            );
        }
    }
    Outcome::Match(comparisons)
}

/// Decimal rendering of a rational, for human-readable reproducer dumps only.
/// Nothing in the oracle's decision path ever touches a float.
fn to_f64(r: &BigRational) -> String {
    let n = r.numer().to_string().parse::<f64>().unwrap_or(f64::NAN);
    let d = r.denom().to_string().parse::<f64>().unwrap_or(f64::NAN);
    format!("{:.12}", n / d)
}

/// GCD: must divide both inputs, and its real roots must be exactly the roots
/// shared by both inputs (z3's verdict on both root sets).
pub(crate) fn check_gcd(z3: &Z3, p: &GenPoly, q: &GenPoly, sab: Sabotage) -> Outcome {
    let (ap, aq) = (poly_of(p), poly_of(q));
    if ap.degree().unwrap_or(0) < 1 || aq.degree().unwrap_or(0) < 1 {
        return Outcome::Skipped("degree < 1");
    }
    let g = ap.gcd(&aq);
    if g.is_zero() {
        return Divergence::new(
            "gcd",
            "identity",
            "gcd of two non-zero polynomials is zero".to_string(),
            inputs2(p, q),
        );
    }
    if !ap.rem(&g).is_zero() || !aq.rem(&g).is_zero() {
        return Divergence::new(
            "gcd",
            "identity",
            format!(
                "gcd {} does not divide both inputs",
                polygen::render(&g.coeffs())
            ),
            inputs2(p, q),
        );
    }
    // Sabotage: claim a shared factor that is not there.
    let g = if sab.on() {
        g.mul(&saboteur_factor())
    } else {
        g
    };
    let g_coeffs = g.coeffs();
    let (Some(rp), Some(rq)) = (z3.roots(&p.coeffs), z3.roots(&q.coeffs)) else {
        return Outcome::Skipped("z3 declined");
    };
    // z3's view of the shared real roots.
    let mut shared: Vec<Ptr> = Vec::new();
    let mut comparisons = 0u64;
    for a in &rp {
        for b in &rq {
            comparisons += 1;
            if z3.eq(*a, *b) {
                shared.push(*a);
                break;
            }
        }
    }
    let rg = if g.degree().unwrap_or(0) < 1 {
        Vec::new()
    } else {
        match z3.roots(&g_coeffs) {
            Some(v) => v,
            None => return Outcome::Skipped("z3 declined"),
        }
    };
    if rg.len() != shared.len() {
        return Divergence::new(
            "gcd",
            "z3",
            format!(
                "AY's gcd {} has {} real roots but p and q share {}",
                polygen::render(&g_coeffs),
                rg.len(),
                shared.len()
            ),
            inputs2(p, q),
        );
    }
    for (i, (a, b)) in rg.iter().zip(shared.iter()).enumerate() {
        comparisons += 1;
        if !z3.eq(*a, *b) {
            return Divergence::new(
                "gcd",
                "z3",
                format!("shared root #{i} differs from root #{i} of AY's gcd"),
                inputs2(p, q),
            );
        }
    }
    Outcome::Match(comparisons + 1)
}

/// Sturm's theorem: AY's root count on `(a, b]` vs counting z3's roots.
pub(crate) fn check_sturm(
    z3: &Z3,
    p: &GenPoly,
    mut a: BigRational,
    mut b: BigRational,
    sab: Sabotage,
) -> Outcome {
    let ap = poly_of(p);
    if ap.degree().unwrap_or(0) < 1 {
        return Outcome::Skipped("degree < 1");
    }
    if a > b {
        std::mem::swap(&mut a, &mut b);
    }
    if a == b {
        return Outcome::Skipped("empty interval");
    }
    let Some(sf) = ap.square_free_part() else {
        return Outcome::Declined("square_free_part");
    };
    if sf.degree().unwrap_or(0) < 1 {
        return Outcome::Skipped("square-free part is constant");
    }
    // Sabotage: an off-by-one in the root count.
    let ay_count = sf.sturm_count_in(&a, &b) + usize::from(sab.on());
    let Some(roots) = z3.roots(&p.coeffs) else {
        return Outcome::Skipped("z3 declined");
    };
    let a_ast = z3.rational(&a);
    let b_ast = z3.rational(&b);
    // Sturm counts the half-open interval (a, b].
    let z3_count = roots
        .iter()
        .filter(|r| z3.gt(**r, a_ast) && !z3.gt(**r, b_ast))
        .count();
    if ay_count != z3_count {
        return Divergence::new(
            "sturm-count",
            "z3",
            format!("AY counts {ay_count} roots in ({a}, {b}], z3 counts {z3_count}"),
            inputs1(p),
        );
    }
    Outcome::Match(1)
}

/// Sign of a polynomial at a real algebraic point.
pub(crate) fn check_sign_at(
    z3: &Z3,
    p: &GenPoly,
    q: &GenPoly,
    pick: u64,
    sab: Sabotage,
) -> Outcome {
    let ap = poly_of(p);
    if ap.degree().unwrap_or(0) < 1 {
        return Outcome::Skipped("degree < 1");
    }
    let Some(sf) = ap.square_free_part() else {
        return Outcome::Declined("square_free_part");
    };
    let Some(markers) = sf.isolate_roots() else {
        return Outcome::Declined("isolate_roots");
    };
    if markers.is_empty() {
        return Outcome::Skipped("no real roots");
    }
    let Some(roots) = z3.roots(&p.coeffs) else {
        return Outcome::Skipped("z3 declined");
    };
    if roots.len() != markers.len() {
        // Root-count disagreement is `check_roots`' business; do not
        // double-report it here.
        return Outcome::Skipped("root counts differ (see roots check)");
    }
    let idx = usize::try_from(pick).unwrap_or(0) % markers.len();
    let aq = poly_of(q);
    let Some(z3_sign) = z3.eval_sign(&q.coeffs, roots[idx]) else {
        return Outcome::Skipped("z3 declined");
    };

    let (ay_sign, path) = match &markers[idx] {
        ORoot::Rational(r) => {
            // Rational root: AY evaluates exactly, no refinement involved.
            (ay::sign_of(&aq.eval(r)), "rational-eval")
        }
        ORoot::Interval(lo, hi) => {
            let Some(alpha) = OAlg::new(&sf, lo, hi) else {
                return Outcome::Declined("OAlg::new");
            };
            // Cross-check AY against itself: the root index it derives by Sturm
            // counting must be this marker's position in ascending order.
            if alpha.root_index() != idx + 1 {
                return Divergence::new(
                    "sign-at-algebraic",
                    "identity",
                    format!(
                        "AY's derived root index is {} but the marker is #{} in ascending order",
                        alpha.root_index(),
                        idx + 1
                    ),
                    inputs2(p, q),
                );
            }
            match alpha.sign_of_poly(&aq) {
                Some(s) => (s, "sign_of_poly"),
                None => return Outcome::Declined("sign_of_poly"),
            }
        }
    };
    // Sabotage: flip the sign (a zero becomes a positive).
    let ay_sign = if sab.on() {
        if ay_sign == 0 {
            1
        } else {
            -ay_sign
        }
    } else {
        ay_sign
    };
    if ay_sign.signum() != z3_sign.signum() {
        return Divergence::new(
            "sign-at-algebraic",
            "z3",
            format!(
                "at root #{idx} of p, AY says sign(q) = {ay_sign} ({path}) but z3 says {z3_sign}"
            ),
            inputs2(p, q),
        );
    }
    Outcome::Match(1)
}

/// Resultant: AY's Sylvester determinant vs z3's principal subresultant chain.
///
/// `Z3_polynomial_subresultants` returns the NON-ZERO principal subresultant
/// coefficients in ascending index order (`psc_chain_optimized` in
/// `src/math/polynomial/polynomial.cpp` pushes them descending and reverses,
/// skipping zeros; an empty chain is reported as the single element `0`).
/// Two exact facts follow, and the `probe` subcommand pins both against live
/// z3 before any fuzzing happens:
///
///   1. `psc_0 == Res`, exactly and with sign, provided z3's internal
///      argument order is matched — z3 puts the HIGHER-DEGREE polynomial
///      first, so AY's determinant is taken in that same order. (Probe:
///      `Res(x-1, x^3-2)` is `-1` for AY in the given order but z3 answers
///      `1`, which is `Res(x^3-2, x-1)`.)
///   2. z3 does NOT rescale by the content: `Res(2x^2-4, x-1) = -2` on both
///      sides. So integer inputs compare directly, no normalization needed.
///
/// When `Res == 0` the whole `psc_0` entry is skipped by z3 and the chain
/// starts at index `k = deg gcd(f, g)`. That case is checked structurally:
/// AY's gcd must be non-constant, and z3's chain can hold at most
/// `min(deg f, deg g) - k` entries — an over-large AY gcd degree shows up as a
/// chain that is too long for it.
///
/// Restricted to integer coefficients so no denominator-clearing convention
/// can enter the comparison.
pub(crate) fn check_resultant(z3: &Z3, p: &GenPoly, q: &GenPoly, sab: Sabotage) -> Outcome {
    let integral = |g: &GenPoly| g.coeffs.iter().all(|c| c.denom().is_one());
    if !integral(p) || !integral(q) {
        return Outcome::Skipped("non-integer coefficients");
    }
    let (ap, aq) = (poly_of(p), poly_of(q));
    let (Some(dp), Some(dq)) = (ap.degree(), aq.degree()) else {
        return Outcome::Skipped("zero polynomial");
    };
    if dp < 1 || dq < 1 {
        return Outcome::Skipped("degree < 1");
    }
    // Keep the exact determinant affordable: Gaussian elimination over
    // BigRational on an (dp + dq) x (dp + dq) matrix.
    if dp + dq > 12 {
        return Outcome::Skipped("degree sum too large");
    }
    // Match z3's internal ordering: higher degree first, ties keep the
    // caller's order (`psc_chain_optimized`).
    let (hi, lo) = if dp >= dq { (&ap, &aq) } else { (&aq, &ap) };
    let Some(res) = ay::resultant(hi, lo) else {
        return Outcome::Declined("resultant");
    };
    // Sabotage: an off-by-one resultant. This also flips the zero/non-zero
    // branch when the true resultant is 0, so both arms get exercised.
    let res = if sab.on() {
        res + BigRational::one()
    } else {
        res
    };
    let Some(chain) = z3.subresultants(&p.coeffs, &q.coeffs) else {
        return Outcome::Skipped("z3 declined");
    };
    if chain.is_empty() {
        return Outcome::Skipped("empty subresultant chain");
    }
    let Some(first) = z3.numeral_value(chain[0]) else {
        // The leading psc still mentions x; nothing to compare against a
        // scalar resultant.
        return Outcome::Skipped("non-numeral psc");
    };
    let g = ap.gcd(&aq);
    let k = g.degree().unwrap_or(0);

    if chain.len() == 1 && first.is_zero() {
        // z3's "empty chain" encoding: every psc vanished, so the inputs share
        // a factor and the resultant is zero.
        if !res.is_zero() {
            return Divergence::new(
                "resultant",
                "z3",
                format!("z3's psc chain is [0] (common factor) but AY's resultant is {res}"),
                inputs2(p, q),
            );
        }
        return Outcome::Match(1);
    }

    if !res.is_zero() {
        // psc_0 is non-zero, hence present, hence first.
        if first != res {
            return Divergence::new(
                "resultant",
                "z3",
                format!("AY resultant {res}, z3 psc_0 {first}"),
                inputs2(p, q),
            );
        }
        if k != 0 {
            return Divergence::new(
                "resultant",
                "identity",
                format!(
                    "AY's resultant is non-zero but AY's gcd {} has degree {k}",
                    polygen::render(&g.coeffs())
                ),
                inputs2(p, q),
            );
        }
        return Outcome::Match(2);
    }

    // res == 0: the inputs must share a factor, and z3's chain must be short
    // enough to have started at index k.
    if k == 0 {
        return Divergence::new(
            "resultant",
            "identity",
            "AY's resultant is zero but AY's gcd says the inputs are coprime".to_string(),
            inputs2(p, q),
        );
    }
    let bound = dp.min(dq).saturating_sub(k);
    if chain.len() > bound {
        return Divergence::new(
            "resultant",
            "z3",
            format!(
                "AY's gcd {} has degree {k}, so z3's psc chain may hold at most \
                 {bound} entries, but it holds {}",
                polygen::render(&g.coeffs()),
                chain.len()
            ),
            inputs2(p, q),
        );
    }
    Outcome::Match(2)
}

/// Largest defining-polynomial degree the exact algebraic ARITHMETIC checks
/// will accept.
///
/// AY computes a cross-point sum or product through a resultant: it evaluates
/// the Sylvester determinant at `deg + 1` sample points and Lagrange-
/// interpolates, then isolates the roots of the result, whose degree is the
/// PRODUCT of the two operand degrees. Two degree-5 operands therefore mean
/// exact Sturm work on a degree-25 polynomial over `BigRational` — one such
/// case measured 47.5 seconds here, buying a single comparison for the price
/// of forty thousand.
///
/// The cap is a throughput decision, not a soundness one: the sum of two
/// degree-3 algebraic numbers exercises exactly the same code path as the sum
/// of two degree-9 ones.
const MAX_ARITH_DEGREE: usize = 3;

/// The same cap for comparison, which refines intervals but does not multiply
/// degrees, and so tolerates more.
const MAX_COMPARE_DEGREE: usize = 5;

/// Pick a real algebraic number from `p`: AY's object and z3's value for the
/// same root, or `None` when the input has no usable irrational root.
fn algebraic_pair(
    z3: &Z3,
    p: &GenPoly,
    pick: u64,
    max_degree: usize,
) -> Result<(OAlg, Ptr), &'static str> {
    let ap = poly_of(p);
    if ap.degree().unwrap_or(0) < 1 {
        return Err("degree < 1");
    }
    let sf = ap.square_free_part().ok_or("square_free_part")?;
    if sf.degree().unwrap_or(0) > max_degree {
        return Err("defining degree above the arithmetic budget");
    }
    let markers = sf.isolate_roots().ok_or("isolate_roots")?;
    if markers.is_empty() {
        return Err("no real roots");
    }
    let roots = z3.roots(&p.coeffs).ok_or("z3 declined")?;
    if roots.len() != markers.len() {
        return Err("root counts differ (see roots check)");
    }
    let n = markers.len();
    for step in 0..n {
        let idx = (usize::try_from(pick).unwrap_or(0) + step) % n;
        if let ORoot::Interval(lo, hi) = &markers[idx] {
            if let Some(alpha) = OAlg::new(&sf, lo, hi) {
                return Ok((alpha, roots[idx]));
            }
        }
    }
    Err("no irrational marker")
}

/// Assert that AY's exact scalar lies inside the rational bracket z3 computed
/// for its own value. This is the oracle's universal comparison: it never
/// shares a representation between the two sides, only the real line.
fn scalar_in_bracket(
    ay_value: &ay::OScalar,
    lo: &BigRational,
    hi: &BigRational,
) -> Result<bool, &'static str> {
    if lo == hi {
        // z3 pinned an exact rational.
        return match ay_value.cmp_rational(lo) {
            Some(Ordering::Equal) => Ok(true),
            Some(_) => Ok(false),
            None => Err("cmp_rational"),
        };
    }
    let above = ay_value.cmp_rational(lo).ok_or("cmp_rational")?;
    let below = ay_value.cmp_rational(hi).ok_or("cmp_rational")?;
    Ok(above == Ordering::Greater && below == Ordering::Less)
}

/// Exact algebraic addition and multiplication.
pub(crate) fn check_arith(z3: &Z3, p: &GenPoly, q: &GenPoly, pick: u64, sab: Sabotage) -> Outcome {
    let (alpha, za) = match algebraic_pair(z3, p, pick, MAX_ARITH_DEGREE) {
        Ok(v) => v,
        Err(e) => return skip_or_decline(e),
    };
    let (beta, zb) = match algebraic_pair(z3, q, pick >> 8, MAX_ARITH_DEGREE) {
        Ok(v) => v,
        Err(e) => return skip_or_decline(e),
    };
    if !z3.is_value(za) || !z3.is_value(zb) {
        return Outcome::Skipped("z3 value not algebraic");
    }
    let mut comparisons = 0u64;
    for op in ["add", "mul"] {
        let zc = if op == "add" {
            z3.add(za, zb)
        } else {
            z3.mul(za, zb)
        };
        if z3.errored() {
            return Outcome::Skipped("z3 declined");
        }
        let ay_value = if op == "add" {
            alpha.add(&beta)
        } else {
            alpha.mul(&beta)
        };
        let Some(ay_value) = ay_value else {
            return Outcome::Declined("algebraic arithmetic");
        };
        // Sabotage: answer with one operand instead of the combination.
        let ay_value = if sab.on() {
            alpha.to_scalar()
        } else {
            ay_value
        };
        let Some((lo, hi)) = z3.bracket(zc, 48) else {
            return Outcome::Skipped("z3 declined");
        };
        match scalar_in_bracket(&ay_value, &lo, &hi) {
            Ok(true) => comparisons += 1,
            Ok(false) => {
                return Divergence::new(
                    "algebraic-arith",
                    "z3",
                    format!(
                        "AY's exact {op} of the two roots is not inside z3's bracket ({lo}, {hi})"
                    ),
                    inputs2(p, q),
                )
            }
            Err(e) => return Outcome::Declined(e),
        }
    }
    Outcome::Match(comparisons)
}

/// Exact comparison of two real algebraic numbers.
pub(crate) fn check_compare(
    z3: &Z3,
    p: &GenPoly,
    q: &GenPoly,
    pick: u64,
    sab: Sabotage,
) -> Outcome {
    let (alpha, za) = match algebraic_pair(z3, p, pick, MAX_COMPARE_DEGREE) {
        Ok(v) => v,
        Err(e) => return skip_or_decline(e),
    };
    let (beta, zb) = match algebraic_pair(z3, q, pick >> 8, MAX_COMPARE_DEGREE) {
        Ok(v) => v,
        Err(e) => return skip_or_decline(e),
    };
    let Some(ay_ord) = alpha.cmp_number(&beta) else {
        return Outcome::Declined("cmp_number");
    };
    // Sabotage: reverse the ordering.
    let ay_ord = if sab.on() { ay_ord.reverse() } else { ay_ord };
    if sab.on() && ay_ord == Ordering::Equal {
        return Outcome::Skipped("nothing to sabotage");
    }
    let z3_ord = if z3.lt(za, zb) {
        Ordering::Less
    } else if z3.gt(za, zb) {
        Ordering::Greater
    } else {
        Ordering::Equal
    };
    if z3.errored() {
        return Outcome::Skipped("z3 declined");
    }
    let mut comparisons = 1u64;
    if ay_ord != z3_ord {
        return Divergence::new(
            "algebraic-compare",
            "z3",
            format!("AY says {ay_ord:?}, z3 says {z3_ord:?}"),
            inputs2(p, q),
        );
    }
    // Also pin each number against a rational z3 chose, exercising the
    // rational-vs-algebraic path rather than only algebraic-vs-algebraic.
    if let Some((lo, hi)) = z3.bracket(za, 40) {
        comparisons += 1;
        let want_above = alpha.cmp_rational(&lo);
        let want_below = alpha.cmp_rational(&hi);
        let ok = if lo == hi {
            want_above == Some(Ordering::Equal)
        } else {
            want_above == Some(Ordering::Greater) && want_below == Some(Ordering::Less)
        };
        if !ok {
            return Divergence::new(
                "algebraic-compare",
                "z3",
                format!("AY's root is not inside z3's own bracket ({lo}, {hi}) for the same root"),
                inputs1(p),
            );
        }
    }
    Outcome::Match(comparisons)
}

/// Classify an `algebraic_pair` failure: AY's fail-closed `None`s are declines,
/// everything else is an inapplicable input.
fn skip_or_decline(reason: &'static str) -> Outcome {
    match reason {
        "square_free_part" | "isolate_roots" => Outcome::Declined(reason),
        other => Outcome::Skipped(other),
    }
}

/// One case's outcome plus the shapes that produced it (for coverage
/// reporting: a fuzz run that never generated a `wilkinson` is not the run it
/// claims to be).
pub(crate) struct CaseResult {
    pub(crate) outcome: Outcome,
    pub(crate) shapes: Vec<&'static str>,
}

/// Run one check on freshly generated inputs. The driver hands in a seeded RNG
/// so the whole case is reproducible from `(seed, index)`.
///
/// `max_cost` bounds [`polygen::work_cost`] of every generated input; a case
/// above it is reported as `over budget` and NOT run. Pass `usize::MAX` for an
/// unbounded ("heavy") campaign.
pub(crate) fn run_case(
    z3: &Z3,
    check: Check,
    rng: &mut Rng,
    max_cost: usize,
    sab: Sabotage,
) -> CaseResult {
    // Generate every input FIRST, so the RNG stream — and therefore the whole
    // case — is a pure function of (seed, index) regardless of the budget.
    // Changing `max_cost` must never change which polynomials a given case
    // draws, only whether they are run.
    // The bivariate checks draw from their own generator entirely; they take
    // the branch below before any univariate polynomial is built.
    if matches!(check, Check::MvRoots | Check::MvSignAt | Check::MvClosest) {
        // The multivariate checks draw from their own generator entirely.
        let g = mv::gen_mv(rng);
        // Query point for the closest-roots check. Small rationals are used on
        // purpose: they land inside the window where the generated roots
        // actually are, so the selection has something to select.
        let s = BigRational::new(BigInt::from(rng.range(-6, 6)), BigInt::from(2));
        let outcome = match check {
            Check::MvRoots => mv::check_mv_roots(z3, &g, sab),
            Check::MvSignAt => mv::check_mv_sign_at(z3, &g, sab),
            _ => mv::check_mv_closest(z3, &g, &s, sab),
        };
        return CaseResult {
            outcome,
            shapes: vec![g.shape],
        };
    }
    if matches!(
        check,
        Check::PmRep
            | Check::PmPseudoDiv
            | Check::PmGcd
            | Check::PmModGcd
            | Check::PmSquareFree
            | Check::PmSquareFreeAll
            | Check::PmModGcdDiag
    ) {
        // The polynomial-manager checks draw from their own generator: they
        // need multivariate factors and an integer specialization point, none
        // of which the univariate generator produces.
        let g = pmgr::gen_pm(rng);
        let outcome = match check {
            Check::PmRep => pmgr::check_pm_rep(&g, sab),
            Check::PmPseudoDiv => pmgr::check_pm_pseudo_div(z3, &g, sab),
            Check::PmGcd => pmgr::check_pm_gcd(z3, &g, sab),
            Check::PmModGcd => pmgr::check_pm_mod_gcd(z3, &g, sab),
            Check::PmSquareFree => pmgr::check_pm_square_free(z3, &g, sab),
            Check::PmModGcdDiag => pmgr::check_pm_mod_gcd_diag(&g, sab),
            _ => pmgr::check_pm_square_free_all(z3, &g, sab),
        };
        return CaseResult {
            outcome,
            shapes: vec![g.shape],
        };
    }
    if matches!(
        check,
        Check::UpSubstrate | Check::UpSqfDecomp | Check::UpZpDdf | Check::UpZpFactor
    ) {
        // The `upoly` checks draw from their own generator: they need INTEGER
        // coefficients, a planted multiplicity structure and a prime modulus,
        // none of which the rational univariate generator produces.
        let g = upoly::gen_up(rng);
        let outcome = match check {
            Check::UpSubstrate => upoly::check_substrate(z3, &g, sab),
            Check::UpSqfDecomp => upoly::check_sqf_decomp(z3, &g, sab),
            Check::UpZpDdf => upoly::check_ddf(&g, sab),
            _ => upoly::check_factor(&g, sab),
        };
        return CaseResult {
            outcome,
            shapes: vec![g.shape],
        };
    }
    if matches!(
        check,
        Check::BqArith | Check::BqRefine | Check::BqSelect | Check::BqDegenerate
    ) {
        // The `mpbq` checks draw from their own generator: they need dyadic
        // numerators/exponents, a deliberately non-dyadic rational for the
        // negative control, and interval shapes (`straddle`, `adjacent`,
        // `degenerate`) that no other generator produces.
        let g = mpbq::gen_bq(rng);
        let outcome = match check {
            Check::BqArith => mpbq::check_arith(z3, &g, sab),
            Check::BqRefine => mpbq::check_refine(z3, &g, sab),
            Check::BqSelect => mpbq::check_select(&g, sab),
            _ => mpbq::check_degenerate(&g, sab),
        };
        return CaseResult {
            outcome,
            shapes: vec![g.shape],
        };
    }
    if matches!(
        check,
        Check::AnumRep
            | Check::AnumCompare
            | Check::AnumSignAt
            | Check::AnumArith
            | Check::AnumSeparation
    ) {
        // The `anum` checks draw from their own generator: they need INTEGER
        // coefficients with a planted factor structure (a shared irrational
        // factor for the EQUAL case, a repeated factor for normalization, a
        // dyadic rational root for the exact-hit branch, and an ASYMMETRIC root
        // set so the sum and difference resultants can be told apart) that no
        // other generator produces.
        let g = anum::gen_an(rng);
        let outcome = match check {
            Check::AnumRep => anum::check_representation(z3, &g, sab),
            Check::AnumCompare => anum::check_compare(z3, &g, sab),
            Check::AnumSignAt => anum::check_sign_at(z3, &g, sab),
            Check::AnumArith => anum::check_arith(z3, &g, sab),
            _ => anum::check_separation(z3, &g, sab),
        };
        return CaseResult {
            outcome,
            shapes: vec![g.shape],
        };
    }
    if matches!(
        check,
        Check::ExImplied | Check::ExProduce | Check::ExWitness | Check::ExProject
    ) {
        // The explanation checks draw from their own generator: they need a SET
        // of sign conditions on a shared variable, drawn so that roughly half
        // the cases are genuine conflicts and the rest are satisfiable. Both
        // directions are load-bearing — a producer that emits a clause for a
        // satisfiable conjunction is the wrong-`unsat` defect, and it is only
        // visible on inputs where no clause is due.
        let g = explain::gen_ex(rng);
        let outcome = match check {
            Check::ExImplied => explain::check_clause_implied(z3, &g, sab),
            Check::ExProduce => explain::check_produce(z3, &g, sab),
            Check::ExWitness => explain::check_countermodel(z3, &g, sab),
            _ => {
                // The projection check pairs the operator itself with the
                // pair-selection that feeds it; a failure in either is reported
                // under the same name.
                match explain::check_relevant_pairs(z3, &g) {
                    Outcome::Diverged(d) => Outcome::Diverged(d),
                    _ => explain::check_projection(z3, &g, sab),
                }
            }
        };
        return CaseResult {
            outcome,
            shapes: vec![g.shape],
        };
    }
    if matches!(
        check,
        Check::IaMember
            | Check::IaIntersect
            | Check::IaComplement
            | Check::IaPick
            | Check::IaSignCells
    ) {
        // The `ialg` checks draw from their own generator: they need two
        // polynomials whose roots INTERLEAVE (so the intersection scan advances
        // each side in turn rather than draining one), a shape where both
        // polynomials share an irrational factor (so two endpoints can be
        // genuinely equal through different defining polynomials, which is the
        // only way the equality branch of the endpoint comparison and an
        // adjacency at an algebraic point are reached), planted rational and
        // dyadic roots (so the `pick` ladder can reach its simplest rungs), and
        // a sign condition — none of which any other generator produces.
        let g = ialg::gen_ia(rng);
        let outcome = match check {
            Check::IaMember => ialg::check_membership(z3, &g, sab),
            Check::IaIntersect => ialg::check_intersect(z3, &g, sab),
            Check::IaComplement => ialg::check_complement(z3, &g, sab),
            Check::IaPick => ialg::check_pick(z3, &g, sab),
            _ => ialg::check_sign_cells(z3, &g, sab),
        };
        return CaseResult {
            outcome,
            shapes: vec![g.shape],
        };
    }
    if matches!(check, Check::BivariatePsc | Check::BivariateResultant) {
        let f = subres::gen_bivariate(rng);
        let g = subres::gen_bivariate(rng);
        // Specialization point. Zero is included on purpose: it is the value
        // most likely to collapse a leading coefficient, which exercises the
        // degree-preservation guard rather than the comparison.
        let c = BigInt::from(rng.range(-4, 4));
        let outcome = match check {
            Check::BivariatePsc => subres::check_bivariate_psc(z3, &f, &g, &c, sab),
            _ => subres::check_bivariate_resultant(z3, &f, &g, &c, sab),
        };
        return CaseResult {
            outcome,
            shapes: vec!["bivariate"],
        };
    }
    let (deg_p, deg_q) = match check {
        Check::Arith => (MAX_ARITH_DEGREE, MAX_ARITH_DEGREE),
        Check::Compare => (MAX_COMPARE_DEGREE, MAX_COMPARE_DEGREE),
        _ => (MAX_DEGREE, MAX_DEGREE),
    };
    let algebraic_operands = matches!(check, Check::Arith | Check::Compare);
    let p = if algebraic_operands {
        polygen::gen_algebraic_operand(rng, deg_p)
    } else {
        polygen::gen_poly(rng, deg_p)
    };
    let q = if algebraic_operands {
        polygen::gen_algebraic_operand(rng, deg_q)
    } else if check == Check::Gcd && rng.chance(1, 2) {
        // Half the gcd cases get a deliberately shared factor: coprime inputs
        // leave the interesting branch of the check unreachable.
        let f = polygen::gen_poly(rng, MAX_DEGREE / 2);
        let g = polygen::gen_poly(rng, MAX_DEGREE / 2);
        let prod = OPoly::from_coeffs(f.coeffs.clone()).mul(&OPoly::from_coeffs(g.coeffs));
        GenPoly {
            coeffs: prod.coeffs(),
            shape: f.shape,
        }
    } else {
        polygen::gen_poly(rng, deg_q)
    };
    let a = polygen::gen_point(rng);
    let b = polygen::gen_point(rng);
    let pick = rng.next_u64();

    let uses_q = !matches!(check, Check::Roots | Check::SquareFree | Check::Sturm);
    let mut shapes = vec![p.shape.name()];
    if uses_q {
        shapes.push(q.shape.name());
    }

    let cost = polygen::work_cost(&p.coeffs).max(if uses_q {
        polygen::work_cost(&q.coeffs)
    } else {
        0
    });
    if cost > max_cost {
        return CaseResult {
            outcome: Outcome::Skipped("over work budget"),
            shapes,
        };
    }

    let outcome = match check {
        Check::Roots => check_roots(z3, &p, sab),
        Check::SquareFree => check_square_free(z3, &p, sab),
        Check::Gcd => check_gcd(z3, &p, &q, sab),
        Check::Sturm => check_sturm(z3, &p, a, b, sab),
        Check::SignAt => check_sign_at(z3, &p, &q, pick, sab),
        Check::Resultant => check_resultant(z3, &p, &q, sab),
        Check::Arith => check_arith(z3, &p, &q, pick, sab),
        Check::Compare => check_compare(z3, &p, &q, pick, sab),
        Check::PscChain => subres::check_psc_chain(z3, &p, &q, sab),
        Check::Discriminant => subres::check_discriminant(z3, &p, sab),
        Check::ChainAgreement => subres::check_chain_agreement(&p, &q, sab),
        Check::BivariatePsc | Check::BivariateResultant => unreachable!("handled above"),
        Check::MvRoots | Check::MvSignAt | Check::MvClosest => unreachable!("handled above"),
        Check::PmRep
        | Check::PmPseudoDiv
        | Check::PmGcd
        | Check::PmModGcd
        | Check::PmSquareFree
        | Check::PmSquareFreeAll
        | Check::PmModGcdDiag => unreachable!("handled above"),
        Check::UpSubstrate | Check::UpSqfDecomp | Check::UpZpDdf | Check::UpZpFactor => {
            unreachable!("handled above")
        }
        Check::BqArith | Check::BqRefine | Check::BqSelect | Check::BqDegenerate => {
            unreachable!("handled above")
        }
        Check::AnumRep
        | Check::AnumCompare
        | Check::AnumSignAt
        | Check::AnumArith
        | Check::AnumSeparation => unreachable!("handled above"),
        Check::IaMember
        | Check::IaIntersect
        | Check::IaComplement
        | Check::IaPick
        | Check::IaSignCells => unreachable!("handled above"),
        Check::ExImplied | Check::ExProduce | Check::ExWitness | Check::ExProject => {
            unreachable!("handled above")
        }
    };
    CaseResult { outcome, shapes }
}

/// Build a rational from small integers (fixtures and tests).
pub(crate) fn rat(n: i64, d: i64) -> BigRational {
    BigRational::new(BigInt::from(n), BigInt::from(d))
}

/// Build an integer-coefficient polynomial from `i64`s, low-to-high.
pub(crate) fn ipoly(coeffs: &[i64]) -> Vec<BigRational> {
    coeffs
        .iter()
        .map(|c| BigRational::from_integer(BigInt::from(*c)))
        .collect()
}

/// Multiply two coefficient vectors (fixtures build products of factors).
pub(crate) fn mul_coeffs(a: &[BigRational], b: &[BigRational]) -> Vec<BigRational> {
    if a.is_empty() || b.is_empty() {
        return Vec::new();
    }
    let mut out = vec![BigRational::zero(); a.len() + b.len() - 1];
    for (i, x) in a.iter().enumerate() {
        for (j, y) in b.iter().enumerate() {
            out[i + j] += x * y;
        }
    }
    out
}

/// `p^k`.
pub(crate) fn pow_coeffs(p: &[BigRational], k: usize) -> Vec<BigRational> {
    let mut acc = vec![BigRational::one()];
    for _ in 0..k {
        acc = mul_coeffs(&acc, p);
    }
    acc
}

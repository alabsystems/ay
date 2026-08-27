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
//! A z3 refusal remains `Skipped`, never a divergence: the oracle is not
//! entitled to call a bug on the reference implementation's behalf. The
//! binding separately records native/API failures; any such failure makes the
//! whole command inconclusive and forces a non-clean exit.

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
use crate::z3::{Ast, Z3};

/// Result of running one check on one generated input.
pub(crate) enum Outcome {
    /// Both sides answered and agreed; `comparisons` individual assertions held.
    Match(u64),
    /// AY fail-closed (`None`). Not a divergence.
    Declined(&'static str),
    /// Input not applicable to this check, or the reference could not answer.
    /// Recorded native/API failures still make the whole command non-clean.
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
    /// Build the diverged outcome carrying this diagnostic payload.
    pub(crate) fn outcome(
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

    /// Whether a successful case includes a live libz3 comparison.
    pub(crate) fn uses_z3(self) -> bool {
        !matches!(
            self,
            Self::ChainAgreement
                | Self::PmRep
                | Self::PmModGcdDiag
                | Self::UpZpDdf
                | Self::UpZpFactor
                | Self::BqSelect
                | Self::BqDegenerate
        )
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

include!("checks/root_checks.rs");
include!("checks/resultant_and_algebraic.rs");
include!("checks/lane_dispatch.rs");
include!("checks/univariate_dispatch.rs");

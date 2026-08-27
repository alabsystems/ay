// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Included by the parent module to keep one audited namespace.

/// Run one check on freshly generated inputs. The driver hands in a seeded RNG
/// so the whole case is reproducible from `(seed, index)`.
///
/// `max_cost` bounds [`polygen::work_cost`] of every generated input; a case
/// above it is reported as `over budget` and NOT run. Pass `usize::MAX` for an
/// unbounded ("heavy") campaign.
fn run_mv_or_manager_case(
    z3: &Z3,
    check: Check,
    rng: &mut Rng,
    _max_cost: usize,
    sab: Sabotage,
) -> Option<CaseResult> {
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
        return Some(CaseResult {
            outcome,
            shapes: vec![g.shape],
        });
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
        return Some(CaseResult {
            outcome,
            shapes: vec![g.shape],
        });
    }
    None
}

fn run_upoly_or_dyadic_case(
    z3: &Z3,
    check: Check,
    rng: &mut Rng,
    sab: Sabotage,
) -> Option<CaseResult> {
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
        return Some(CaseResult {
            outcome,
            shapes: vec![g.shape],
        });
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
        return Some(CaseResult {
            outcome,
            shapes: vec![g.shape],
        });
    }
    None
}

fn run_anum_or_explain_case(
    z3: &Z3,
    check: Check,
    rng: &mut Rng,
    sab: Sabotage,
) -> Option<CaseResult> {
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
        return Some(CaseResult {
            outcome,
            shapes: vec![g.shape],
        });
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
        return Some(CaseResult {
            outcome,
            shapes: vec![g.shape],
        });
    }
    None
}

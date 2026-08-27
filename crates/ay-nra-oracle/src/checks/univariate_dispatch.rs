// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Included by the parent module to keep one audited namespace.

fn run_interval_or_bivariate_case(
    z3: &Z3,
    check: Check,
    rng: &mut Rng,
    sab: Sabotage,
) -> Option<CaseResult> {
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
        return Some(CaseResult {
            outcome,
            shapes: vec![g.shape],
        });
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
        return Some(CaseResult {
            outcome,
            shapes: vec!["bivariate"],
        });
    }
    None
}

fn run_univariate_case(
    z3: &Z3,
    check: Check,
    rng: &mut Rng,
    max_cost: usize,
    sab: Sabotage,
) -> CaseResult {
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

pub(crate) fn run_case(
    z3: &Z3,
    check: Check,
    rng: &mut Rng,
    max_cost: usize,
    sab: Sabotage,
) -> CaseResult {
    if let Some(result) = run_mv_or_manager_case(z3, check, rng, max_cost, sab) {
        return result;
    }
    if let Some(result) = run_upoly_or_dyadic_case(z3, check, rng, sab) {
        return result;
    }
    if let Some(result) = run_anum_or_explain_case(z3, check, rng, sab) {
        return result;
    }
    if let Some(result) = run_interval_or_bivariate_case(z3, check, rng, sab) {
        return result;
    }
    run_univariate_case(z3, check, rng, max_cost, sab)
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

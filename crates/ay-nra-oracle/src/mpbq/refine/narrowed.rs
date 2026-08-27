// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Narrowed-interval refinement checks.

use super::*;

struct TargetPlan {
    target: OBq,
    bound: u32,
}

pub(super) fn check_narrowed_root(
    case: &RefineCase<'_>,
    sab: Sabotage,
    index: usize,
    root: Ast,
    rational_lo: &BigRational,
    rational_hi: &BigRational,
) -> Result<RootCheck, Outcome> {
    let Some(start) = coarsest_isolating_interval(case, index, rational_lo, rational_hi)? else {
        return Ok(RootCheck::Unusable);
    };
    let plan = target_and_bound(case.g, &start)?;
    let Some((answer, trace)) = obq_refine_to_width(&case.g.poly, &start, &plan.target) else {
        return Err(Outcome::Declined("refine_to_width declined"));
    };
    let mut comparisons = 1;
    add_result(
        &mut comparisons,
        validate_refine_trace(case.g, &trace, plan.bound),
    )?;
    let narrowed = match answer {
        ORefined::Exact(value) => {
            add_result(&mut comparisons, validate_coarse_exact(case, root, &value))?;
            return Ok(RootCheck::Matched(comparisons));
        }
        ORefined::Narrowed(interval) => interval,
    };
    let narrowed = sabotage_interval(narrowed, sab);
    add_result(
        &mut comparisons,
        validate_z3_enclosure(case, index, root, &narrowed),
    )?;
    add_result(
        &mut comparisons,
        validate_interval_trace(case.g, sab, &start, &narrowed, &plan.target, &trace),
    )?;
    Ok(RootCheck::Matched(comparisons))
}

fn add_result(total: &mut u64, outcome: Outcome) -> Result<(), Outcome> {
    match outcome {
        Outcome::Match(n) => {
            *total += n;
            Ok(())
        }
        other => Err(other),
    }
}

fn coarsest_isolating_interval(
    case: &RefineCase<'_>,
    index: usize,
    rational_lo: &BigRational,
    rational_hi: &BigRational,
) -> Result<Option<OBqInterval>, Outcome> {
    for exponent in 0..=48 {
        let Some(candidate) = obq_enclose_rational(rational_lo, rational_hi, exponent) else {
            continue;
        };
        match (
            obq_poly_sign_at(&case.g.poly, &candidate.lo()),
            obq_poly_sign_at(&case.g.poly, &candidate.hi()),
        ) {
            (Some(lo), Some(hi)) if lo != 0 && hi != 0 => {}
            _ => continue,
        }
        let (Some(lo), Some(hi)) = (
            case.z3.rational(&candidate.lo().to_rational()),
            case.z3.rational(&candidate.hi().to_rational()),
        ) else {
            return Err(Outcome::Skipped("z3 could not build endpoint numerals"));
        };
        let Some(inside) = z3_roots_inside(case.z3, case.roots, lo, hi) else {
            return Err(Outcome::Skipped("z3 errored while ordering roots"));
        };
        if inside == vec![index] {
            return Ok(Some(candidate));
        }
    }
    Ok(None)
}

fn target_and_bound(g: &GenBq, interval: &OBqInterval) -> Result<TargetPlan, Outcome> {
    let Some(base) = interval.width().div_two_pow(g.target_k) else {
        return Err(Outcome::Declined("target underflow"));
    };
    let width = interval.width();
    let target = if g.target_mul % 4 == 1 {
        let exponent = 2 + g.target_k % 3;
        match width.div_two_pow(exponent) {
            Some(sliver) => {
                let candidate = width.sub(&sliver);
                if candidate.sign() > 0 && candidate.cmp_bq(&width) == Ordering::Less {
                    candidate
                } else {
                    base
                }
            }
            None => base,
        }
    } else {
        let multiplier = OBq::new(BigInt::from(g.target_mul), 0);
        match base.mul(&multiplier) {
            Some(scaled) if scaled.cmp_bq(&width) == Ordering::Less => scaled,
            _ => base,
        }
    };
    let Some(bound) = obq_refine_step_bound(&width, &target) else {
        return Err(Outcome::Declined("refine_step_bound declined"));
    };
    match width.div_two_pow(bound) {
        Some(shrunk) if shrunk.cmp_bq(&target) != Ordering::Greater => {
            Ok(TargetPlan { target, bound })
        }
        _ => Err(Divergence::outcome(
            "bq-refine",
            "identity",
            format!("step bound {bound} is insufficient: width/2^{bound} exceeds target"),
            vec![("poly".into(), render_poly(&g.poly))],
        )),
    }
}

fn validate_refine_trace(
    g: &GenBq,
    trace: &ay_nra::oracle_api::ORefineTrace,
    bound: u32,
) -> Outcome {
    if trace.bound != bound || trace.steps > trace.bound {
        return Divergence::outcome(
            "bq-refine",
            "identity",
            format!(
                "step bound: trace {} / recomputed {bound} / steps {}",
                trace.bound, trace.steps
            ),
            vec![("poly".into(), render_poly(&g.poly))],
        );
    }
    if trace.steps == 0 {
        return Divergence::outcome(
            "bq-refine",
            "identity",
            format!(
                "zero bisections for target width/2^{}: loop did not run",
                g.target_k
            ),
            vec![("poly".into(), render_poly(&g.poly))],
        );
    }
    Outcome::Match(3)
}

fn validate_coarse_exact(case: &RefineCase<'_>, root: Ast, value: &OBq) -> Outcome {
    let Some(ast) = case.z3.rational(&value.to_rational()) else {
        return Outcome::Skipped("z3 could not build the exact-root numeral");
    };
    let Some(equal) = case.z3.eq(ast, root) else {
        return Outcome::Skipped("z3 errored while comparing the exact root");
    };
    if !equal {
        return Divergence::outcome(
            "bq-refine",
            "z3",
            format!("AY says the root is exactly {}", render_bq(value)),
            vec![
                ("poly".into(), render_poly(&case.g.poly)),
                (
                    "z3 root".into(),
                    case.z3
                        .ast_string(root)
                        .unwrap_or_else(|| "<invalid-z3-ast>".into()),
                ),
            ],
        );
    }
    if obq_poly_sign_at(&case.g.poly, value) != Some(0) {
        return Divergence::outcome(
            "bq-refine",
            "identity",
            format!(
                "claimed exact root {} does not zero the polynomial",
                render_bq(value)
            ),
            vec![("poly".into(), render_poly(&case.g.poly))],
        );
    }
    Outcome::Match(2)
}

fn sabotage_interval(interval: OBqInterval, sab: Sabotage) -> OBqInterval {
    if !sab.on() {
        return interval;
    }
    let step = OBq::inv_two_pow(interval.max_k());
    OBqInterval::new(&interval.lo().add(&step), &interval.hi().add(&step)).unwrap_or(interval)
}

fn validate_z3_enclosure(
    case: &RefineCase<'_>,
    index: usize,
    root: Ast,
    interval: &OBqInterval,
) -> Outcome {
    let (Some(lo), Some(hi)) = (
        case.z3.rational(&interval.lo().to_rational()),
        case.z3.rational(&interval.hi().to_rational()),
    ) else {
        return Outcome::Skipped("z3 could not build refined endpoints");
    };
    let (Some(above_lo), Some(below_hi)) = (case.z3.lt(lo, root), case.z3.gt(hi, root)) else {
        return Outcome::Skipped("z3 errored while ordering the refined root");
    };
    if !above_lo || !below_hi {
        return Divergence::outcome(
            "bq-refine",
            "z3",
            format!(
                "z3 root is not inside ({}, {})",
                render_bq(&interval.lo()),
                render_bq(&interval.hi())
            ),
            vec![
                ("poly".into(), render_poly(&case.g.poly)),
                (
                    "z3 root".into(),
                    case.z3
                        .ast_string(root)
                        .unwrap_or_else(|| "<invalid-z3-ast>".into()),
                ),
                ("target".into(), format!("width/2^{}", case.g.target_k)),
            ],
        );
    }
    let mut comparisons = 2;
    for (other_index, other) in case.roots.iter().copied().enumerate() {
        comparisons += 1;
        if other_index == index {
            continue;
        }
        let (Some(above_lo), Some(below_hi)) = (case.z3.lt(lo, other), case.z3.lt(other, hi))
        else {
            return Outcome::Skipped("z3 errored while ordering roots");
        };
        if above_lo && below_hi {
            return Divergence::outcome(
                "bq-refine",
                "z3",
                format!("root #{other_index} is also inside interval for root #{index}"),
                vec![("poly".into(), render_poly(&case.g.poly))],
            );
        }
    }
    Outcome::Match(comparisons)
}

fn validate_interval_trace(
    g: &GenBq,
    sab: Sabotage,
    start: &OBqInterval,
    refined: &OBqInterval,
    target: &OBq,
    trace: &ay_nra::oracle_api::ORefineTrace,
) -> Outcome {
    if sab.on() {
        return Outcome::Match(0);
    }
    if refined.width().mul_two_pow(trace.steps) != start.width() {
        return Divergence::outcome(
            "bq-refine",
            "identity",
            format!(
                "steps {} does not reproduce width: {} * 2^{} != {}",
                trace.steps,
                render_bq(&refined.width()),
                trace.steps,
                render_bq(&start.width())
            ),
            vec![("poly".into(), render_poly(&g.poly))],
        );
    }
    if trace.end_max_k != refined.max_k() {
        return Divergence::outcome(
            "bq-refine",
            "identity",
            format!("end_max_k {} != {}", trace.end_max_k, refined.max_k()),
            vec![("poly".into(), render_poly(&g.poly))],
        );
    }
    if refined.width().cmp_bq(target) == Ordering::Greater {
        return Divergence::outcome(
            "bq-refine",
            "identity",
            format!(
                "target not met: width {} > target {}",
                render_bq(&refined.width()),
                render_bq(target)
            ),
            vec![("poly".into(), render_poly(&g.poly))],
        );
    }
    let signs = (
        obq_poly_sign_at(&g.poly, &refined.lo()),
        obq_poly_sign_at(&g.poly, &refined.hi()),
    );
    match signs {
        (Some(lo), Some(hi)) if lo != 0 && hi != 0 && lo != hi => Outcome::Match(4),
        _ => Divergence::outcome(
            "bq-refine",
            "identity",
            format!(
                "refined endpoints no longer bracket: {:?} / {:?}",
                signs.0, signs.1
            ),
            vec![("poly".into(), render_poly(&g.poly))],
        ),
    }
}

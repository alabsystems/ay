// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Interval-set intersection checks.

use super::*;

// ===========================================================================
// Check 2 — `ialg-intersect`
// ===========================================================================

/// Intersection, and the justifications it must keep.
///
/// z3 legs: membership in `a n b` equals `member(a) && member(b)` at every
/// probe, computed by z3 on the raw lists; and the conflict direction — an
/// intersection reported EMPTY must contain no probe.
/// Identity legs: commutativity; idempotence; intersecting with `full` and with
/// `empty`; and the justification of every surviving interval must include the
/// literals of BOTH sides, which is what makes the conflict clause entail the
/// conflict.
pub(crate) fn check_intersect(z3: &Z3, g: &GenIA, sab: Sabotage) -> Outcome {
    let (Some(roots_a), Some(roots_b)) = (roots_of(z3, &g.p), roots_of(z3, &g.q)) else {
        return Outcome::Skipped("z3 declined / no isolable root");
    };
    if roots_a.len() < 2 || roots_b.len() < 2 {
        return Outcome::Skipped("fewer than two roots");
    }
    let pairs_a = pairs_from(&roots_a, g.strict, 100, EndpointExtent::Bounded);
    let pairs_b = pairs_from(&roots_b, g.strict >> 7, 200, EndpointExtent::Bounded);
    if pairs_a.is_empty()
        || pairs_b.is_empty()
        || !under_ceilings(&pairs_a)
        || !under_ceilings(&pairs_b)
    {
        return Outcome::Skipped("empty or over declared ceiling");
    }
    let (Some(set_a), Some(set_b)) = (build(&pairs_a), build(&pairs_b)) else {
        return Divergence::outcome(
            "ialg-intersect",
            "z3",
            "from_parts declined under the declared ceilings".to_string(),
            inputs(g),
        );
    };
    let Some(intersection) = set_a.intersect(&set_b) else {
        if sab.on() {
            return Outcome::Declined("sabotage");
        }
        return Divergence::outcome(
            "ialg-intersect",
            "z3",
            "intersect declined under ceilings despite total comparison".to_string(),
            inputs(g),
        );
    };
    let mut all_roots = roots_a.clone();
    all_roots.extend(roots_b.iter().cloned());
    let Some(probes) = probes(z3, g, &all_roots) else {
        return Outcome::Skipped("z3 rejected a rational probe");
    };
    let mut comparisons = 1;
    let case = IntersectionCase {
        pairs_a: &pairs_a,
        pairs_b: &pairs_b,
        set_a: &set_a,
        set_b: &set_b,
        intersection: &intersection,
        probes: &probes,
    };
    if let Err(outcome) = add_matches(
        &mut comparisons,
        check_intersection_membership(z3, g, sab, &case),
    ) {
        return outcome;
    }
    if let Err(outcome) = add_matches(
        &mut comparisons,
        witness_same_set_as(z3, g, sab, &roots_a, &set_a, &set_b),
    ) {
        return outcome;
    }
    if let Err(outcome) = add_matches(
        &mut comparisons,
        check_intersection_identities(g, sab, &set_a, &set_b, &intersection),
    ) {
        return outcome;
    }
    Outcome::Match(comparisons)
}

struct IntersectionCase<'a> {
    pairs_a: &'a [Pair],
    pairs_b: &'a [Pair],
    set_a: &'a OIAlgSet,
    set_b: &'a OIAlgSet,
    intersection: &'a OIAlgSet,
    probes: &'a [Probe],
}

fn check_intersection_membership(
    z3: &Z3,
    g: &GenIA,
    sab: Sabotage,
    case: &IntersectionCase<'_>,
) -> Outcome {
    let mut comparisons = 0;
    for probe in case.probes {
        let (Some(in_a), Some(in_b)) = (
            z3_member(z3, case.pairs_a, probe.z3),
            z3_member(z3, case.pairs_b, probe.z3),
        ) else {
            return Outcome::Skipped("z3 errored while testing membership");
        };
        let expected = in_a && in_b;
        let Some(mut actual) = case.intersection.contains(&probe.ay) else {
            if sab.on() {
                return Outcome::Declined("sabotage");
            }
            return Divergence::outcome(
                "ialg-intersect",
                "z3",
                format!(
                    "contains({}) declined despite total comparison",
                    probe.label
                ),
                inputs(g),
            );
        };
        if sab.on() && probe.label.starts_with("root") {
            actual = !actual;
        }
        comparisons += 1;
        if actual != expected {
            return Divergence::outcome(
                "ialg-intersect",
                "z3",
                format!(
                    "(a n b).contains({}) = {actual}, z3 says {expected} ({} n {} -> {})",
                    probe.label,
                    case.set_a.len(),
                    case.set_b.len(),
                    case.intersection.len()
                ),
                inputs(g),
            );
        }
    }
    if case.intersection.is_empty() {
        for probe in case.probes {
            let (Some(in_a), Some(in_b)) = (
                z3_member(z3, case.pairs_a, probe.z3),
                z3_member(z3, case.pairs_b, probe.z3),
            ) else {
                return Outcome::Skipped("z3 errored while testing membership");
            };
            comparisons += 1;
            if in_a && in_b {
                return Divergence::outcome(
                    "ialg-intersect",
                    "z3",
                    format!(
                        "intersection is empty but z3 places {} in both",
                        probe.label
                    ),
                    inputs(g),
                );
            }
        }
    }
    Outcome::Match(comparisons)
}

fn witness_same_set_as(
    z3: &Z3,
    g: &GenIA,
    sab: Sabotage,
    roots: &[(ODyadicAnum, Ast)],
    set_a: &OIAlgSet,
    set_b: &OIAlgSet,
) -> Outcome {
    if sab.on() {
        return Outcome::Match(0);
    }
    let Some(equal) = set_a.same_set_as(set_b) else {
        return Divergence::outcome(
            "ialg-intersect",
            "identity",
            "same_set_as declined although equality is total here".to_string(),
            inputs(g),
        );
    };
    let Some(probes) = probes(z3, g, roots) else {
        return Outcome::Skipped("z3 rejected a rational probe");
    };
    let mut comparisons = 1;
    for probe in probes {
        if let (Some(in_a), Some(in_b)) = (set_a.contains(&probe.ay), set_b.contains(&probe.ay)) {
            comparisons += 1;
            if equal && in_a != in_b {
                return Divergence::outcome(
                    "ialg-intersect",
                    "identity",
                    "same_set_as says equal but membership differs".to_string(),
                    inputs(g),
                );
            }
        }
    }
    Outcome::Match(comparisons)
}

fn check_intersection_identities(
    g: &GenIA,
    sab: Sabotage,
    set_a: &OIAlgSet,
    set_b: &OIAlgSet,
    intersection: &OIAlgSet,
) -> Outcome {
    if sab.on() {
        return Outcome::Match(0);
    }
    if !set_b
        .intersect(set_a)
        .and_then(|set| set.same_set_as(intersection))
        .unwrap_or(false)
    {
        return Divergence::outcome(
            "ialg-intersect",
            "identity",
            "intersection is not commutative".to_string(),
            inputs(g),
        );
    }
    if !set_a
        .intersect(set_a)
        .and_then(|set| set.same_set_as(set_a))
        .unwrap_or(false)
    {
        return Divergence::outcome(
            "ialg-intersect",
            "identity",
            "intersection is not idempotent".to_string(),
            inputs(g),
        );
    }
    if !set_a
        .intersect(&OIAlgSet::empty())
        .is_some_and(|set| set.is_empty())
    {
        return Divergence::outcome(
            "ialg-intersect",
            "identity",
            "a n empty is not empty".to_string(),
            inputs(g),
        );
    }
    let mut comparisons = 3;
    for interval in intersection.intervals() {
        comparisons += 1;
        let from_a = interval
            .lits
            .iter()
            .any(|literal| (100..200).contains(literal));
        let from_b = interval.lits.iter().any(|literal| *literal >= 200);
        if !from_a || !from_b {
            return Divergence::outcome(
                "ialg-intersect",
                "identity",
                format!(
                    "surviving cell cites {:?}: from_a={from_a} from_b={from_b}",
                    interval.lits
                ),
                inputs(g),
            );
        }
    }
    Outcome::Match(comparisons)
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Interval-set complement checks.

use super::*;

// ===========================================================================
// Check 3 — `ialg-complement`
// ===========================================================================

/// Complement and subtract — how a refuted cell is removed.
///
/// z3 legs: membership in the complement is exactly NON-membership in the raw
/// list, at every probe including the endpoints (which is the only way a
/// strictness flip is visible); and `a \ b` is `member(a) && !member(b)`.
/// Identity legs: double complement is the identity; `a \ a` is empty;
/// `a \ empty` is `a`; complement of `full` is empty and back.
pub(crate) fn check_complement(z3: &Z3, g: &GenIA, sab: Sabotage) -> Outcome {
    let (Some(roots_a), Some(roots_b)) = (roots_of(z3, &g.p), roots_of(z3, &g.q)) else {
        return Outcome::Skipped("z3 declined / no isolable root");
    };
    if roots_a.len() < 2 || roots_b.len() < 2 {
        return Outcome::Skipped("fewer than two roots");
    }
    let pairs_a = pairs_from(&roots_a, g.strict, 100, EndpointExtent::Bounded);
    let pairs_b = pairs_from(&roots_b, g.strict >> 11, 200, EndpointExtent::Bounded);
    if pairs_a.is_empty()
        || pairs_b.is_empty()
        || !under_ceilings(&pairs_a)
        || !under_ceilings(&pairs_b)
    {
        return Outcome::Skipped("empty or over declared ceiling");
    }
    let (Some(set_a), Some(set_b)) = (build(&pairs_a), build(&pairs_b)) else {
        return Divergence::outcome(
            "ialg-complement",
            "z3",
            "from_parts declined under the declared ceilings".to_string(),
            inputs(g),
        );
    };
    let (Some(complement), Some(difference)) = (set_a.complement(), set_a.subtract(&set_b)) else {
        if sab.on() {
            return Outcome::Declined("sabotage");
        }
        return Divergence::outcome(
            "ialg-complement",
            "z3",
            "complement or subtract declined under ceilings".to_string(),
            inputs(g),
        );
    };
    let mut all_roots = roots_a;
    all_roots.extend(roots_b);
    let Some(probes) = probes(z3, g, &all_roots) else {
        return Outcome::Skipped("z3 rejected a rational probe");
    };
    let case = ComplementCase {
        pairs_a: &pairs_a,
        pairs_b: &pairs_b,
        set_a: &set_a,
        set_b: &set_b,
        complement: &complement,
        difference: &difference,
        probes: &probes,
    };
    let mut comparisons = 1;
    if let Err(outcome) = add_matches(
        &mut comparisons,
        check_complement_membership(z3, g, sab, &case),
    ) {
        return outcome;
    }
    if let Err(outcome) = add_matches(&mut comparisons, check_complement_identities(g, sab, &case))
    {
        return outcome;
    }
    Outcome::Match(comparisons)
}

struct ComplementCase<'a> {
    pairs_a: &'a [Pair],
    pairs_b: &'a [Pair],
    set_a: &'a OIAlgSet,
    set_b: &'a OIAlgSet,
    complement: &'a OIAlgSet,
    difference: &'a OIAlgSet,
    probes: &'a [Probe],
}

fn check_complement_membership(
    z3: &Z3,
    g: &GenIA,
    sab: Sabotage,
    case: &ComplementCase<'_>,
) -> Outcome {
    let mut comparisons = 0;
    for probe in case.probes {
        let (Some(in_a), Some(in_b)) = (
            z3_member(z3, case.pairs_a, probe.z3),
            z3_member(z3, case.pairs_b, probe.z3),
        ) else {
            return Outcome::Skipped("z3 errored while testing membership");
        };
        let Some(mut in_complement) = case.complement.contains(&probe.ay) else {
            if sab.on() {
                return Outcome::Declined("sabotage");
            }
            return Divergence::outcome(
                "ialg-complement",
                "z3",
                format!("complement.contains({}) declined", probe.label),
                inputs(g),
            );
        };
        if sab.on() && probe.label.starts_with("root") {
            in_complement = !in_complement;
        }
        comparisons += 1;
        if in_complement == in_a {
            return Divergence::outcome(
                "ialg-complement",
                "z3",
                format!(
                    "complement.contains({}) = {in_complement}, member(a) = {in_a}",
                    probe.label
                ),
                inputs(g),
            );
        }
        let Some(mut in_difference) = case.difference.contains(&probe.ay) else {
            return Divergence::outcome(
                "ialg-complement",
                "z3",
                format!("subtract.contains({}) declined", probe.label),
                inputs(g),
            );
        };
        if sab.on() && probe.label.starts_with("root") {
            in_difference = !in_difference;
        }
        comparisons += 1;
        if in_difference != (in_a && !in_b) {
            return Divergence::outcome(
                "ialg-complement",
                "z3",
                format!(
                    "(a \\ b).contains({}) = {in_difference}, z3 says a={in_a} b={in_b}",
                    probe.label
                ),
                inputs(g),
            );
        }
    }
    Outcome::Match(comparisons)
}

fn check_complement_identities(g: &GenIA, sab: Sabotage, case: &ComplementCase<'_>) -> Outcome {
    if sab.on() {
        return Outcome::Match(0);
    }
    if !case
        .complement
        .complement()
        .and_then(|set| set.same_set_as(case.set_a))
        .unwrap_or(false)
    {
        return Divergence::outcome(
            "ialg-complement",
            "identity",
            "double complement is not the identity".to_string(),
            inputs(g),
        );
    }
    if !case
        .set_a
        .subtract(case.set_a)
        .is_some_and(|set| set.is_empty())
    {
        return Divergence::outcome(
            "ialg-complement",
            "identity",
            "a \\ a is not empty".to_string(),
            inputs(g),
        );
    }
    if !case
        .set_a
        .subtract(&OIAlgSet::empty())
        .and_then(|set| set.same_set_as(case.set_a))
        .unwrap_or(false)
    {
        return Divergence::outcome(
            "ialg-complement",
            "identity",
            "a \\ empty is not a".to_string(),
            inputs(g),
        );
    }
    let Some(intersection) = case.set_a.intersect(case.set_b) else {
        return Outcome::Skipped("intersect declined");
    };
    if !case
        .difference
        .union(&intersection)
        .and_then(|set| set.same_set_as(case.set_a))
        .unwrap_or(false)
    {
        return Divergence::outcome(
            "ialg-complement",
            "identity",
            "(a \\ b) U (a n b) is not a".to_string(),
            inputs(g),
        );
    }
    let Some(full) = OIAlgSet::full(&[3]) else {
        return Outcome::Skipped("full declined");
    };
    if !full.complement().is_some_and(|set| set.is_empty()) {
        return Divergence::outcome(
            "ialg-complement",
            "identity",
            "complement of full is not empty".to_string(),
            inputs(g),
        );
    }
    Outcome::Match(5)
}

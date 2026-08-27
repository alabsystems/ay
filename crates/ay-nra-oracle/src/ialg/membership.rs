// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Interval-set membership and representation checks.

use super::*;

// ===========================================================================
// Check 1 — `ialg-membership`
// ===========================================================================

/// The representation, normalisation, and the roster of entry points.
///
/// z3 legs: for every probe — rational AND algebraic — membership in AY's
/// normalised set must equal membership in the raw interval list as z3
/// computes it. Emptiness must agree in the unsound direction: if AY reports
/// empty, z3 must find no member.
/// Identity legs: `len` respects the merge (a normalised set of `n` raw
/// intervals has at most `n`), justifications survive normalisation, and
/// `full` contains every probe.
/// Guards, fired on purpose with a positive control on the SAME endpoints: a
/// closed infinite endpoint and an over-ceiling interval count are both refused.
pub(crate) fn check_membership(z3: &Z3, g: &GenIA, sab: Sabotage) -> Outcome {
    let Some(roots) = roots_of(z3, &g.p) else {
        return Outcome::Skipped("z3 declined / no isolable root");
    };
    if roots.len() < 2 {
        return Outcome::Skipped("fewer than two roots");
    }
    let pairs = pairs_from(&roots, g.strict, 100, EndpointExtent::OpenEnded);
    if !under_ceilings(&pairs) {
        return Outcome::Skipped("over declared ceiling");
    }
    let Some(set) = build(&pairs) else {
        if sab.on() {
            return Outcome::Declined("sabotage");
        }
        return Divergence::outcome(
            "ialg-membership",
            "z3",
            "from_parts declined under ceilings with total endpoint comparison".to_string(),
            inputs(g),
        );
    };
    let Some(probes) = probes(z3, g, &roots) else {
        return Outcome::Skipped("z3 rejected a rational probe");
    };
    let mut comparisons = 1;
    if let Err(outcome) = add_matches(
        &mut comparisons,
        check_membership_probes(z3, g, sab, &pairs, &set, &probes),
    ) {
        return outcome;
    }
    if let Err(outcome) = add_matches(
        &mut comparisons,
        check_empty_claim(z3, g, &pairs, &set, &probes),
    ) {
        return outcome;
    }
    if let Err(outcome) = add_matches(
        &mut comparisons,
        check_normalization_justification(g, sab, &pairs, &set),
    ) {
        return outcome;
    }
    if let Err(outcome) = add_matches(
        &mut comparisons,
        check_full_empty_union(g, sab, &set, &probes),
    ) {
        return outcome;
    }
    if let Err(outcome) = add_matches(&mut comparisons, check_membership_guards(g, sab, &roots)) {
        return outcome;
    }
    Outcome::Match(comparisons)
}

fn check_membership_probes(
    z3: &Z3,
    g: &GenIA,
    sab: Sabotage,
    pairs: &[Pair],
    set: &OIAlgSet,
    probes: &[Probe],
) -> Outcome {
    let mut comparisons = 0;
    for probe in probes {
        let Some(expected) = z3_member(z3, pairs, probe.z3) else {
            return Outcome::Skipped("z3 errored while testing membership");
        };
        let Some(mut actual) = set.contains(&probe.ay) else {
            if sab.on() {
                return Outcome::Declined("sabotage");
            }
            return Divergence::outcome(
                "ialg-membership",
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
                "ialg-membership",
                "z3",
                format!(
                    "contains({}) = {actual}, z3 says {expected} ({} raw -> {} normalized)",
                    probe.label,
                    pairs.len(),
                    set.len()
                ),
                inputs(g),
            );
        }
    }
    Outcome::Match(comparisons)
}

fn check_empty_claim(
    z3: &Z3,
    g: &GenIA,
    pairs: &[Pair],
    set: &OIAlgSet,
    probes: &[Probe],
) -> Outcome {
    if !set.is_empty() {
        return Outcome::Match(0);
    }
    let mut comparisons = 0;
    for probe in probes {
        let Some(in_set) = z3_member(z3, pairs, probe.z3) else {
            return Outcome::Skipped("z3 errored while testing membership");
        };
        comparisons += 1;
        if in_set {
            return Divergence::outcome(
                "ialg-membership",
                "z3",
                format!("set reported empty but z3 places {} in it", probe.label),
                inputs(g),
            );
        }
    }
    Outcome::Match(comparisons)
}

fn check_normalization_justification(
    g: &GenIA,
    sab: Sabotage,
    pairs: &[Pair],
    set: &OIAlgSet,
) -> Outcome {
    if sab.on() {
        return Outcome::Match(0);
    }
    if set.len() > pairs.len() {
        return Divergence::outcome(
            "ialg-membership",
            "identity",
            format!("normalize grew {} intervals to {}", pairs.len(), set.len()),
            inputs(g),
        );
    }
    let Some(justification) = set.justification() else {
        return Divergence::outcome(
            "ialg-membership",
            "identity",
            "justification declined under the declared ceiling".to_string(),
            inputs(g),
        );
    };
    let mut supplied = Vec::new();
    for pair in pairs {
        for literal in &pair.ay.lits {
            if !supplied.contains(literal) {
                supplied.push(*literal);
            }
        }
    }
    let mut comparisons = 2;
    for literal in &justification {
        comparisons += 1;
        if !supplied.contains(literal) {
            return Divergence::outcome(
                "ialg-membership",
                "identity",
                format!("justification cites unsupplied literal {literal}"),
                inputs(g),
            );
        }
    }
    for pair in pairs {
        for literal in &pair.ay.lits {
            comparisons += 1;
            if !set.is_empty() && !justification.contains(literal) {
                return Divergence::outcome(
                    "ialg-membership",
                    "identity",
                    format!("literal {literal} lost by normalization"),
                    inputs(g),
                );
            }
        }
    }
    Outcome::Match(comparisons)
}

fn check_full_empty_union(g: &GenIA, sab: Sabotage, set: &OIAlgSet, probes: &[Probe]) -> Outcome {
    if sab.on() {
        return Outcome::Match(0);
    }
    let Some(full) = OIAlgSet::full(&[7]) else {
        return Outcome::Skipped("full declined");
    };
    let mut comparisons = 0;
    for probe in probes {
        comparisons += 1;
        if full.contains(&probe.ay) != Some(true) {
            return Divergence::outcome(
                "ialg-membership",
                "identity",
                format!("full does not contain {}", probe.label),
                inputs(g),
            );
        }
        comparisons += 1;
        if OIAlgSet::empty().contains(&probe.ay) != Some(false) {
            return Divergence::outcome(
                "ialg-membership",
                "identity",
                format!("empty contains {}", probe.label),
                inputs(g),
            );
        }
    }
    let Some(union) = set.union(set) else {
        return Divergence::outcome(
            "ialg-membership",
            "identity",
            "union declined under the declared ceilings".to_string(),
            inputs(g),
        );
    };
    for probe in probes {
        comparisons += 1;
        if union.contains(&probe.ay) != set.contains(&probe.ay) {
            return Divergence::outcome(
                "ialg-membership",
                "identity",
                format!("union with self moved {}", probe.label),
                inputs(g),
            );
        }
    }
    Outcome::Match(comparisons)
}

fn check_membership_guards(g: &GenIA, sab: Sabotage, roots: &[(ODyadicAnum, Ast)]) -> Outcome {
    if sab.on() {
        return Outcome::Match(0);
    }
    let closed = OIAlgSet::from_parts(&[OIAlgInterval {
        lo: None,
        lo_open: false,
        hi: Some(roots[0].0.clone()),
        hi_open: true,
        lits: vec![1],
    }]);
    if closed.is_some() {
        return Divergence::outcome(
            "ialg-membership",
            "identity",
            "a closed -inf endpoint was accepted".to_string(),
            inputs(g),
        );
    }
    let open = OIAlgSet::from_parts(&[OIAlgInterval {
        lo: None,
        lo_open: true,
        hi: Some(roots[0].0.clone()),
        hi_open: true,
        lits: vec![1],
    }]);
    if open.is_none() {
        return Divergence::outcome(
            "ialg-membership",
            "identity",
            "the open control on the same endpoint was refused".to_string(),
            inputs(g),
        );
    }
    check_interval_ceiling(g)
}

fn check_interval_ceiling(g: &GenIA) -> Outcome {
    let too_many = (0..=oialg_max_intervals())
        .map(|index| OIAlgInterval {
            lo: Some(ODyadicAnum::rational(BigRational::from_integer(
                BigInt::from(3 * index as i64),
            ))),
            lo_open: false,
            hi: Some(ODyadicAnum::rational(BigRational::from_integer(
                BigInt::from(3 * index as i64 + 1),
            ))),
            hi_open: false,
            lits: vec![1],
        })
        .collect::<Vec<_>>();
    if OIAlgSet::from_parts(&too_many).is_some() {
        return Divergence::outcome(
            "ialg-membership",
            "identity",
            format!("{} intervals accepted past the ceiling", too_many.len()),
            inputs(g),
        );
    }
    if OIAlgSet::from_parts(&too_many[..oialg_max_intervals()]).is_none() {
        return Divergence::outcome(
            "ialg-membership",
            "identity",
            "the at-ceiling control was refused".to_string(),
            inputs(g),
        );
    }
    Outcome::Match(4)
}

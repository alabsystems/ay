// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Sign-cell construction and partition checks.

use super::*;

// ===========================================================================
// Check 5 — `ialg-sign-cells`
// ===========================================================================

/// Construction from a sign condition — the operation that turns a root
/// isolation into a feasible set, and the one where a fail-open predicate would
/// be catastrophic.
///
/// z3 legs: for every probe, membership in AY's constructed set must equal
/// `cond.accepts(sign of p at that probe)` with the SIGN COMPUTED BY z3
/// (`Z3_algebraic_eval`). That single assertion pins the whole cell
/// decomposition: sample-point selection, sign propagation, which cells are
/// kept, and how the closed root cells are glued onto the open ones.
/// Identity legs: complementary conditions partition the line (`Lt` and `Ge`
/// are complements, as are `Le`/`Gt` and `Eq`/`Ne`); the roots themselves are
/// in the `Eq` set and out of the `Ne` set.
/// Guard, fired on purpose: a descending root list is refused.
///
/// # Why this is where the fail-open defect lives
///
/// If the sign at a sample point cannot be evaluated, the permissive answers
/// are "keep the cell" (silently too large) and "drop the cell" (silently too
/// small — and a feasible set wrongly emptied is a CONFLICT THAT DOES NOT
/// EXIST). `from_sign_condition` takes neither and returns `None`. The injected
/// defect used to demonstrate this check replaces that `?` with an assumption,
/// which is the `check_monomial_consistency` shape exactly.
pub(crate) fn check_sign_cells(z3: &Z3, g: &GenIA, sab: Sabotage) -> Outcome {
    let Some(roots) = roots_of(z3, &g.p) else {
        return Outcome::Skipped("z3 declined / no isolable root");
    };
    if 2 * roots.len() + 1 > oialg_max_intervals() {
        return Outcome::Skipped("over declared ceiling");
    }
    let ay_roots = roots
        .iter()
        .map(|(root, _)| root.clone())
        .collect::<Vec<_>>();
    let Some(set) = oialg_from_sign_condition(&g.p, &ay_roots, g.cond, &[5]) else {
        if sab.on() {
            return Outcome::Declined("sabotage");
        }
        return Divergence::outcome(
            "ialg-sign-cells",
            "z3",
            format!(
                "from_sign_condition declined on z3's ascending {}-root list",
                roots.len()
            ),
            inputs(g),
        );
    };
    let Some(probes) = probes(z3, g, &roots) else {
        return Outcome::Skipped("z3 rejected a rational probe");
    };
    let mut comparisons = 1;
    if let Err(outcome) = add_matches(
        &mut comparisons,
        check_sign_cell_membership(z3, g, sab, &roots, &set, &probes),
    ) {
        return outcome;
    }
    if let Err(outcome) = add_matches(
        &mut comparisons,
        check_complementary_conditions(g, sab, &ay_roots),
    ) {
        return outcome;
    }
    if let Err(outcome) = add_matches(
        &mut comparisons,
        check_eq_cells_and_root_order_guard(g, sab, &roots, &ay_roots),
    ) {
        return outcome;
    }
    Outcome::Match(comparisons)
}

fn check_sign_cell_membership(
    z3: &Z3,
    g: &GenIA,
    sab: Sabotage,
    roots: &[(ODyadicAnum, Ast)],
    set: &OIAlgSet,
    probes: &[Probe],
) -> Outcome {
    let coefficients = rationals(&g.p);
    let mut comparisons = 0;
    for probe in probes {
        let Some(sign) = z3.eval_sign(&coefficients, probe.z3) else {
            continue;
        };
        let expected = g.cond.accepts(sign);
        let Some(mut actual) = set.contains(&probe.ay) else {
            if sab.on() {
                return Outcome::Declined("sabotage");
            }
            return Divergence::outcome(
                "ialg-sign-cells",
                "z3",
                format!(
                    "contains({}) declined despite total comparison",
                    probe.label
                ),
                inputs(g),
            );
        };
        if sab.on() {
            actual = !actual;
        }
        comparisons += 1;
        if actual != expected {
            return Divergence::outcome(
                "ialg-sign-cells",
                "z3",
                format!(
                    "cond {:?}: contains({}) = {actual}, z3 sign {sign} requires {expected} \
                     ({} cells, {} roots)",
                    g.cond,
                    probe.label,
                    set.len(),
                    roots.len()
                ),
                inputs(g),
            );
        }
    }
    Outcome::Match(comparisons)
}

fn check_complementary_conditions(g: &GenIA, sab: Sabotage, roots: &[ODyadicAnum]) -> Outcome {
    if sab.on() {
        return Outcome::Match(0);
    }
    let mut comparisons = 0;
    for (condition, complement) in [
        (OISignCond::Lt, OISignCond::Ge),
        (OISignCond::Le, OISignCond::Gt),
        (OISignCond::Eq, OISignCond::Ne),
    ] {
        let (Some(set), Some(other)) = (
            oialg_from_sign_condition(&g.p, roots, condition, &[5]),
            oialg_from_sign_condition(&g.p, roots, complement, &[6]),
        ) else {
            return Divergence::outcome(
                "ialg-sign-cells",
                "identity",
                format!("from_sign_condition declined for {condition:?}/{complement:?}"),
                inputs(g),
            );
        };
        comparisons += 1;
        if !set.intersect(&other).is_some_and(|value| value.is_empty()) {
            return Divergence::outcome(
                "ialg-sign-cells",
                "identity",
                format!("{condition:?} and {complement:?} overlap"),
                inputs(g),
            );
        }
        comparisons += 1;
        if !set
            .complement()
            .and_then(|value| value.same_set_as(&other))
            .unwrap_or(false)
        {
            return Divergence::outcome(
                "ialg-sign-cells",
                "identity",
                format!("complement of {condition:?} is not {complement:?}"),
                inputs(g),
            );
        }
    }
    Outcome::Match(comparisons)
}

fn check_eq_cells_and_root_order_guard(
    g: &GenIA,
    sab: Sabotage,
    roots: &[(ODyadicAnum, Ast)],
    ay_roots: &[ODyadicAnum],
) -> Outcome {
    if sab.on() {
        return Outcome::Match(0);
    }
    let Some(equal_set) = oialg_from_sign_condition(&g.p, ay_roots, OISignCond::Eq, &[5]) else {
        return Outcome::Skipped("Eq declined");
    };
    let mut comparisons = 0;
    for (root, _) in roots {
        comparisons += 1;
        if equal_set.contains(root) != Some(true) {
            return Divergence::outcome(
                "ialg-sign-cells",
                "identity",
                "a root of p is not in the Eq set".to_string(),
                inputs(g),
            );
        }
    }
    comparisons += 1;
    if equal_set.len() != roots.len() {
        return Divergence::outcome(
            "ialg-sign-cells",
            "identity",
            format!(
                "Eq set has {} cells for {} roots",
                equal_set.len(),
                roots.len()
            ),
            inputs(g),
        );
    }
    if roots.len() >= 2 {
        let mut descending = ay_roots.to_vec();
        descending.reverse();
        comparisons += 1;
        if oialg_from_sign_condition(&g.p, &descending, g.cond, &[5]).is_some() {
            return Divergence::outcome(
                "ialg-sign-cells",
                "identity",
                "a descending root list was accepted".to_string(),
                inputs(g),
            );
        }
        comparisons += 1;
        if oialg_from_sign_condition(&g.p, ay_roots, g.cond, &[5]).is_none() {
            return Divergence::outcome(
                "ialg-sign-cells",
                "identity",
                "the ascending control on the same roots was refused".to_string(),
                inputs(g),
            );
        }
    }
    Outcome::Match(comparisons)
}

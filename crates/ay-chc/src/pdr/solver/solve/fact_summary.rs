// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Canonical level-zero summaries for CHC fact clauses.

use crate::{ChcExpr, ChcVar};

/// Rewrite a fact constraint into the predicate's canonical argument frame.
///
/// A must-summary is an under-approximation: every state it describes must be
/// proven reachable. Using the body constraint alone drops constant and
/// repeated-variable head arguments. For example, `(hdr #x00 n)` would become
/// `true`, falsely claiming every `hdr` state is reachable. The reachability
/// fast path could then manufacture a one-step counterexample for a safe
/// system.
///
/// Positions expressible using only canonical predicate variables are pinned:
/// constants become `a_i = constant`, repeated variables become
/// `a_j = a_first`, and a variable's first occurrence supplies the ordinary
/// clause-to-canonical rename. A compound argument is pinned only when every
/// variable it mentions has that canonical binding (admitting a free
/// clause-local name would corrupt ghost-pair certification, array forwarding,
/// and arithmetic proof scoring). Otherwise there is NO sound summary in the
/// canonical frame: dropping the position, as this used to, left `a_i`
/// unconstrained, so `y = 0 => P(true, (mod y 3))` summarized as "every
/// `P(true, _)` is reachable" and PDR published a one-step counterexample for a
/// safe system (CHC differential generator, z3 5.1: `sat`, AY: `unsat`). Such a
/// fact gets no summary: `None`, which the caller skips (a must summary only
/// ever adds reachability evidence).
pub(super) fn rewrite_fact_summary(
    constraint: &ChcExpr,
    head_args: &[ChcExpr],
    canonical_vars: &[ChcVar],
) -> Option<ChcExpr> {
    debug_assert_eq!(head_args.len(), canonical_vars.len());
    // Bind direct variable arguments first so a compound argument can be
    // classified independently of the order of the head positions.
    let mut subst: Vec<(ChcVar, ChcExpr)> = Vec::with_capacity(head_args.len());
    let mut first_seen: Vec<(&ChcVar, &ChcVar)> = Vec::with_capacity(head_args.len());
    for (argument, canonical) in head_args.iter().zip(canonical_vars) {
        if let ChcExpr::Var(variable) = argument {
            if !first_seen.iter().any(|(seen, _)| *seen == variable) {
                first_seen.push((variable, canonical));
                subst.push((variable.clone(), ChcExpr::var(canonical.clone())));
            }
        }
    }

    let rewritten = constraint.substitute(&subst);
    let mut pins = Vec::new();
    for (argument, canonical) in head_args.iter().zip(canonical_vars) {
        match argument {
            ChcExpr::Var(variable) => {
                if let Some((_, first)) = first_seen.iter().find(|(seen, _)| *seen == variable) {
                    if *first != canonical {
                        pins.push(ChcExpr::eq(
                            ChcExpr::var((*first).clone()),
                            ChcExpr::var(canonical.clone()),
                        ));
                    }
                }
            }
            ChcExpr::Bool(_) | ChcExpr::Int(_) | ChcExpr::Real(_, _) | ChcExpr::BitVec(_, _) => {
                pins.push(ChcExpr::eq(
                    ChcExpr::var(canonical.clone()),
                    argument.clone(),
                ));
            }
            compound => {
                let bound = compound
                    .vars()
                    .iter()
                    .all(|variable| subst.iter().any(|(source, _)| source == variable));
                if !bound {
                    return None;
                }
                pins.push(ChcExpr::eq(
                    ChcExpr::var(canonical.clone()),
                    compound.substitute(&subst),
                ));
            }
        }
    }

    if pins.is_empty() {
        Some(rewritten)
    } else {
        pins.insert(0, rewritten);
        Some(ChcExpr::and_all(pins))
    }
}

#[cfg(test)]
mod tests {
    use super::rewrite_fact_summary;
    use crate::{ChcExpr, ChcSort, ChcVar};

    fn canonical() -> [ChcVar; 2] {
        [
            ChcVar::new("__p1_a0", ChcSort::Int),
            ChcVar::new("__p1_a1", ChcSort::Int),
        ]
    }

    #[test]
    fn a_compound_argument_over_a_fact_local_variable_has_no_summary() {
        // `y = 0 => P(1, (mod y 3))`: `y` has no canonical binding.
        let y = ChcExpr::var(ChcVar::new("y", ChcSort::Int));
        let constraint = ChcExpr::eq(y.clone(), ChcExpr::int(0));
        let head = [ChcExpr::int(1), ChcExpr::mod_op(y, ChcExpr::int(3))];
        assert!(rewrite_fact_summary(&constraint, &head, &canonical()).is_none());
    }

    #[test]
    fn constants_and_bound_compound_arguments_are_still_pinned() {
        // `x >= 0 => P(x, x + 1)` pins `a1 = a0 + 1`.
        let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
        let constraint = ChcExpr::ge(x.clone(), ChcExpr::int(0));
        let head = [x.clone(), ChcExpr::add(x, ChcExpr::int(1))];
        let summary = rewrite_fact_summary(&constraint, &head, &canonical()).expect("pinned");
        let text = summary.to_string();
        assert!(
            text.contains("__p1_a1") && text.contains("__p1_a0"),
            "{text}"
        );
    }
}

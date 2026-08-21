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
/// variable it mentions has that canonical binding. Otherwise it keeps the
/// previous weaker treatment; admitting a free clause-local name would corrupt
/// ghost-pair certification, array forwarding, and arithmetic proof scoring.
pub(super) fn rewrite_fact_summary(
    constraint: &ChcExpr,
    head_args: &[ChcExpr],
    canonical_vars: &[ChcVar],
) -> ChcExpr {
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

    let mut rewritten = constraint.substitute(&subst);
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
                if bound {
                    pins.push(ChcExpr::eq(
                        ChcExpr::var(canonical.clone()),
                        compound.substitute(&subst),
                    ));
                } else {
                    // #2492: preserve the historical identity substitution for
                    // constituent variables without treating them as canonical.
                    for variable in compound.vars() {
                        rewritten = rewritten
                            .substitute(&[(variable.clone(), ChcExpr::var(variable.clone()))]);
                    }
                }
            }
        }
    }

    if pins.is_empty() {
        rewritten
    } else {
        pins.insert(0, rewritten);
        ChcExpr::and_all(pins)
    }
}

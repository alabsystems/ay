// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Complete definitional substitution, committed one admitted round at a time.
//!
//! Cancellation or an incomplete growing expression leaves the current round
//! uncommitted. Earlier completed rounds may remain. Individual legacy pure
//! simplification, allocation and hash operations are not latency-bounded.

use crate::bmc::{AcyclicNames, BmcSolver};
use crate::{ChcExpr, ChcOp};
use ay_core::kani_compat::{DetHashMap, DetHashSet};

mod candidates;
mod replacement_session;

use replacement_session::ReplacementSession;

struct Round {
    conjuncts: Vec<ChcExpr>,
    changed: usize,
}

pub(super) fn substitute(
    conjuncts: &mut Vec<ChcExpr>,
    names: &mut AcyclicNames<'_>,
) -> Option<usize> {
    names.poll()?;
    let max_rounds = conjuncts.len().saturating_add(1).min(1024);
    let mut total_changed = 0usize;
    for _ in 0..max_rounds {
        names.check_all(conjuncts)?;
        let substitutions = candidates::collect(conjuncts, names)?;
        if substitutions.is_empty() {
            break;
        }
        let round = build_round(conjuncts, &substitutions, names)?;
        drop(substitutions);
        let Some(total) = total_changed.checked_add(round.changed) else {
            return names.refuse();
        };
        let finished =
            round.changed == 0 || matches!(round.conjuncts.as_slice(), [ChcExpr::Bool(false)]);
        // No partial vector or partial substitution can escape on refusal.
        names.poll()?;
        *conjuncts = round.conjuncts;
        total_changed = total;
        if finished {
            break;
        }
    }
    names.poll()?;
    Some(total_changed)
}

fn build_round(
    conjuncts: &[ChcExpr],
    substitutions: &DetHashMap<String, ChcExpr>,
    names: &mut AcyclicNames<'_>,
) -> Option<Round> {
    names.poll()?;
    let mut output = Vec::new();
    if output.try_reserve_exact(conjuncts.len()).is_err() {
        return names.refuse();
    }
    let mut changed = 0usize;
    let mut replacements = ReplacementSession::new(substitutions, names);
    for conjunct in conjuncts {
        let replaced = replacements.substitute(conjunct)?;
        let simplified =
            replacements.with_names(|names| super::simplify_expression(replaced, names))?;
        // Both sides have passed complete depth/sort/occurrence admission.
        replacements.with_names(AcyclicNames::poll)?;
        if simplified != *conjunct {
            let Some(next) = changed.checked_add(1) else {
                return replacements.with_names(AcyclicNames::refuse);
            };
            changed = next;
        }
        match simplified {
            ChcExpr::Bool(true) => {}
            ChcExpr::Bool(false) => {
                output.clear();
                output.push(ChcExpr::Bool(false));
                break;
            }
            other => output.push(other),
        }
    }
    replacements.with_names(|names| names.check_all(&output))?;
    Some(Round {
        conjuncts: output,
        changed,
    })
}

#[cfg(test)]
mod tests;

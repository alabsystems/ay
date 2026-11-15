// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Checked Boolean/interval rounds for the exact expansion only.
//! Earlier completed rounds may remain on refusal, but neither a partial
//! conjunct vector nor a partially updated interval environment is committed.
//! The inner pure interval/algebraic recursion is not latency-bounded here.

use crate::bmc::{AcyclicNames, BmcSolver, IntInterval};
use crate::ChcExpr;
use ay_core::kani_compat::{DetHashMap, DetHashSet};

struct Rewritten {
    conjuncts: Vec<ChcExpr>,
    changed: bool,
}

pub(super) fn simplify(
    conjuncts: &mut Vec<ChcExpr>,
    env: &mut DetHashMap<String, IntInterval>,
    local_bools: &DetHashSet<String>,
    names: &mut AcyclicNames<'_>,
) -> Option<()> {
    names.check_all(conjuncts)?;
    let mut values = DetHashMap::default();
    let max_rounds = conjuncts.len().saturating_add(4).clamp(1, 32);
    for _ in 0..max_rounds {
        names.check_all(conjuncts)?;
        if !collect_values(conjuncts, local_bools, &mut values, names)? {
            names.poll()?;
            *conjuncts = vec![ChcExpr::Bool(false)];
            break;
        }
        let mut rewritten = rewrite(conjuncts, env, &values, names)?;
        if matches!(rewritten.conjuncts.as_slice(), [ChcExpr::Bool(false)]) {
            names.poll()?;
            *conjuncts = rewritten.conjuncts;
            break;
        }

        let mut next_env = DetHashMap::default();
        for (name, interval) in env.iter() {
            names.poll()?;
            next_env.insert(name.clone(), *interval);
        }
        let before_bool_count = values.len();
        if !super::collect_bounds(&rewritten.conjuncts, &mut next_env, names)?
            || !collect_values(&rewritten.conjuncts, local_bools, &mut values, names)?
        {
            rewritten.conjuncts.clear();
            rewritten.conjuncts.push(ChcExpr::Bool(false));
        }
        let finished = matches!(rewritten.conjuncts.as_slice(), [ChcExpr::Bool(false)])
            || (!rewritten.changed && values.len() == before_bool_count);
        names.check_all(&rewritten.conjuncts)?;
        names.poll()?;
        *conjuncts = rewritten.conjuncts;
        *env = next_env;
        if finished {
            break;
        }
    }
    drop(values);
    names.poll()
}

fn collect_values(
    conjuncts: &[ChcExpr],
    local_bools: &DetHashSet<String>,
    values: &mut DetHashMap<String, bool>,
    names: &mut AcyclicNames<'_>,
) -> Option<bool> {
    for conjunct in conjuncts {
        names.poll()?;
        if !BmcSolver::collect_bool_constant(conjunct, local_bools, values) {
            return Some(false);
        }
    }
    names.poll()?;
    Some(true)
}

fn rewrite(
    conjuncts: &[ChcExpr],
    env: &DetHashMap<String, IntInterval>,
    values: &DetHashMap<String, bool>,
    names: &mut AcyclicNames<'_>,
) -> Option<Rewritten> {
    let mut substitutions = DetHashMap::default();
    for (name, value) in values {
        names.poll()?;
        substitutions.insert(name.clone(), ChcExpr::Bool(*value));
    }
    names.poll()?;
    let mut output = Vec::new();
    if output.try_reserve_exact(conjuncts.len()).is_err() {
        return names.refuse();
    }
    let mut changed = false;
    for conjunct in conjuncts {
        let substituted = names.substitute(conjunct, &substitutions)?;
        let simplified = BmcSolver::simplify_interval_expr(&substituted, env);
        names.check(&simplified)?;
        if simplified != *conjunct {
            changed = true;
        }
        match simplified {
            ChcExpr::Bool(false) => {
                output.clear();
                output.push(ChcExpr::Bool(false));
                break;
            }
            ChcExpr::Bool(true) => changed = true,
            other => output.push(other),
        }
    }
    names.check_all(&output)?;
    drop(substitutions);
    names.poll()?;
    Some(Rewritten {
        conjuncts: output,
        changed,
    })
}

#[cfg(test)]
mod tests;

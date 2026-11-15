// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A tiny DPLL over a few hundred local clauses, used to enumerate the
//! reachable states of a bit-serial circuit (never as a proof).

#![cfg(test)]

use super::{EmissionProgress, T};
use ay_core::kani_compat::DetHashMap as HashMap;

pub(crate) type Clause = Vec<(T, bool)>;

fn propagate(
    db: &[Clause],
    asg: &mut HashMap<T, bool>,
    budget: &mut u64,
    progress: &EmissionProgress<'_>,
) -> Option<bool> {
    loop {
        progress.poll().then_some(())?;
        let mut changed = false;
        for (k, cl) in db.iter().enumerate() {
            super::visited();
            progress.poll().then_some(())?;
            *budget = budget.checked_sub(cl.len() as u64 + 1)?;
            let mut open = None;
            let mut nopen = 0;
            let mut sat = false;
            for &(a, p) in cl {
                progress.poll().then_some(())?;
                match asg.get(&a) {
                    None => {
                        nopen += 1;
                        open = Some((a, p));
                        if nopen > 1 {
                            break;
                        }
                    }
                    Some(&v) if v == p => {
                        sat = true;
                        break;
                    }
                    Some(_) => {}
                }
            }
            if sat || nopen > 1 {
                continue;
            }
            match open {
                None => {
                    progress.poll().then_some(())?;
                    return Some(false);
                }
                Some((a, p)) => {
                    asg.insert(a, p);
                    super::assigned(a, k);
                    changed = true;
                }
            }
        }
        if !changed {
            progress.poll().then_some(())?;
            return Some(true);
        }
    }
}

// Outer None is refusal; inner None is genuine satisfying completion.
fn branch_var(
    db: &[Clause],
    asg: &HashMap<T, bool>,
    progress: &EmissionProgress<'_>,
) -> Option<Option<(T, bool)>> {
    for cl in db {
        progress.poll().then_some(())?;
        let mut sat = false;
        let mut open = None;
        for &(a, p) in cl {
            progress.poll().then_some(())?;
            if asg.get(&a) == Some(&p) {
                sat = true;
                break;
            }
            if open.is_none() && !asg.contains_key(&a) {
                open = Some((a, p));
            }
        }
        if !sat {
            if let Some(choice) = open {
                return Some(Some(choice));
            }
        }
    }
    progress.poll().then_some(())?;
    Some(None)
}

/// A satisfying assignment extending `fixed`, `Some(None)` when unsatisfiable,
/// `None` when the budget is exhausted or the original owner refuses.
pub(crate) fn solve(
    db: &[Clause],
    fixed: &HashMap<T, bool>,
    budget: &mut u64,
    progress: &EmissionProgress<'_>,
) -> Option<Option<HashMap<T, bool>>> {
    progress.poll().then_some(())?;
    let mut stack = vec![fixed.clone()];
    while let Some(mut asg) = stack.pop() {
        progress.poll().then_some(())?;
        if !propagate(db, &mut asg, budget, progress)? {
            continue;
        }
        match branch_var(db, &asg, progress)? {
            None => {
                progress.poll().then_some(())?;
                return Some(Some(asg));
            }
            Some((a, p)) => {
                let mut other = asg.clone();
                other.insert(a, !p);
                stack.push(other);
                asg.insert(a, p);
                stack.push(asg);
            }
        }
    }
    progress.poll().then_some(())?;
    Some(None)
}

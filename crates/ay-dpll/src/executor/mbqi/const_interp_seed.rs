// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Direct observations nominate a constant interpretation, never certify one.
//! Only the caller's unchanged all-original-root checks can install a witness.

use super::{Constant, EvalValue, Executor, Sort, Symbol, TermData, TermEntryStamp, TermId};
use ay_frontend::CheckedProjectionBinding;

mod observations;
#[cfg(test)]
mod tests;

const MAX_DEPTH: usize = 64;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum FlatSort {
    Bool,
    Bv(u32),
    Array(u32, u32),
}

fn flat(sort: &Sort) -> Option<FlatSort> {
    match sort {
        Sort::Bool => Some(FlatSort::Bool),
        Sort::BitVec(bv) if (1..=64).contains(&bv.width) => Some(FlatSort::Bv(bv.width)),
        Sort::Array(array) => match (&array.index_sort, &array.element_sort) {
            (Sort::BitVec(i), Sort::BitVec(c))
                if (1..=64).contains(&i.width) && (1..=64).contains(&c.width) =>
            {
                Some(FlatSort::Array(i.width, c.width))
            }
            _ => None,
        },
        _ => None,
    }
}

/// This ledger covers new discovery, observations and literal construction;
/// it does not replace the existing certifier's per-obligation work limits.
struct Budget<'a> {
    remaining: &'a mut u32,
    deadline: ay_core::time::Instant,
    stopped: bool,
    stop: &'a mut dyn FnMut() -> bool,
}

impl Budget<'_> {
    fn charge(&mut self, exec: &Executor, amount: usize) -> Option<()> {
        if self.stopped {
            return None;
        }
        if (self.stop)()
            || ay_core::time::Instant::now() >= self.deadline
            || exec.external_stop_reason().is_some()
            || exec.poll_evaluation_stop().is_err()
            || exec.w4_budget_exhausted()
        {
            self.stopped = true;
            return None;
        }
        let Some(left) = u32::try_from(amount)
            .ok()
            .and_then(|amount| self.remaining.checked_sub(amount))
        else {
            self.stopped = true;
            return None;
        };
        *self.remaining = left;
        Some(())
    }
}

pub(super) fn build(
    exec: &mut Executor,
    roots: &[TermId],
    heads: &[&CheckedProjectionBinding],
    work: &mut u32,
    deadline: ay_core::time::Instant,
) -> Option<Vec<TermId>> {
    build_with_stop(exec, roots, heads, work, deadline, &mut || false)
}

fn build_with_stop(
    exec: &mut Executor,
    roots: &[TermId],
    heads: &[&CheckedProjectionBinding],
    work: &mut u32,
    deadline: ay_core::time::Instant,
    stop: &mut dyn FnMut() -> bool,
) -> Option<Vec<TermId>> {
    let mut budget = Budget {
        remaining: work,
        deadline,
        stopped: false,
        stop,
    };
    budget.charge(exec, heads.len().checked_mul(8)?)?;
    if heads.len() <= super::MAX_CONST_INTERP_HEADS || heads.len() > super::MAX_CONST_INTERP_COMBOS
    {
        return None;
    }
    for head in heads {
        observations::current_binding(exec, head, &mut budget)?;
    }
    let context = exec.ctx.source_context_stamp();
    let mut seen = Vec::new();
    let mut selected = vec![None; heads.len()];
    census(exec, roots, heads, &mut selected, &mut seen, &mut budget)?;
    // One immutable model supplies the whole batch. These maps have NO per-
    // entry birth stamps: even a well-typed sampled number is only a guess.
    let model = exec.last_model.as_ref()?;
    let mut values = Vec::with_capacity(heads.len());
    for (head, observation) in heads.iter().zip(selected) {
        let term = observation?;
        values.push(observations::read(exec, model, head, term, &mut budget)?);
    }
    budget.charge(exec, roots.len())?;
    if context != exec.ctx.source_context_stamp() {
        return None;
    }
    for (term, stamp) in seen {
        budget.charge(exec, 1)?;
        if exec.ctx.terms.entry_stamp(term) != Some(stamp) {
            return None;
        }
    }
    for head in heads {
        observations::current_binding(exec, head, &mut budget)?;
    }
    // The caller still owns the same ordered borrowed roots. No interning,
    // source mutation or evaluator call happened during collection/recheck.
    let mut result = Vec::with_capacity(heads.len());
    for (head, value) in heads.iter().zip(values) {
        budget.charge(exec, 4)?;
        result.push(observations::materialize(exec, head, value)?);
    }
    budget.charge(exec, 0)?;
    Some(result)
}

#[derive(Clone, Copy)]
struct Value {
    sort: FlatSort,
    ground: bool,
}

fn census(
    exec: &Executor,
    roots: &[TermId],
    heads: &[&CheckedProjectionBinding],
    selected: &mut [Option<TermId>],
    seen: &mut Vec<(TermId, TermEntryStamp)>,
    budget: &mut Budget<'_>,
) -> Option<()> {
    for &root in roots {
        budget.charge(exec, 4)?;
        seen.push((root, exec.ctx.terms.entry_stamp(root)?));
        if flat(exec.ctx.terms.sort(root))? != FlatSort::Bool {
            return None;
        }
        let (body, binders) = match exec.ctx.terms.get(root) {
            TermData::Forall(binders, body, _) => (*body, binders.as_slice()),
            _ => (root, &[][..]),
        };
        for (name, sort) in binders {
            budget.charge(exec, name.len().checked_add(1)?)?;
            if !matches!(flat(sort)?, FlatSort::Bool | FlatSort::Bv(_)) {
                return None;
            }
        }
        for (index, (name, _)) in binders.iter().enumerate() {
            for (prior, _) in &binders[..index] {
                budget.charge(exec, name.len().checked_add(prior.len())?)?;
                if name == prior {
                    return None;
                }
            }
        }
        let mut stack = vec![(body, 0usize, false)];
        let mut values: Vec<Value> = Vec::new();
        while let Some((term, depth, exit)) = stack.pop() {
            budget.charge(exec, 1)?;
            exec.ctx.terms.entry_stamp(term)?;
            let data = exec.ctx.terms.get(term);
            if !exit {
                if depth > MAX_DEPTH {
                    return None;
                }
                let children: &[TermId] = match data {
                    TermData::Const(_) | TermData::Var(..) => &[],
                    TermData::App(_, args) => args,
                    TermData::Not(inner) => std::slice::from_ref(inner),
                    // Separate ITE storage cannot be borrowed as a slice.
                    TermData::Ite(c, a, b) => {
                        if depth == MAX_DEPTH {
                            return None;
                        }
                        budget.charge(exec, 12)?;
                        seen.push((term, exec.ctx.terms.entry_stamp(term)?));
                        stack.push((term, depth, true));
                        stack.extend([
                            (*b, depth + 1, false),
                            (*a, depth + 1, false),
                            (*c, depth + 1, false),
                        ]);
                        continue;
                    }
                    _ => return None,
                };
                if depth == MAX_DEPTH && !children.is_empty() {
                    return None;
                }
                budget.charge(exec, children.len().checked_mul(3)?.checked_add(4)?)?;
                seen.push((term, exec.ctx.terms.entry_stamp(term)?));
                stack.push((term, depth, true));
                stack.extend(
                    children
                        .iter()
                        .rev()
                        .map(|&child| (child, depth + 1, false)),
                );
                continue;
            }
            let count = match data {
                TermData::App(_, args) => args.len(),
                TermData::Not(_) => 1,
                TermData::Ite(..) => 3,
                _ => 0,
            };
            let start = values.len().checked_sub(count)?;
            let value = finish(
                exec,
                term,
                &values[start..],
                binders,
                heads,
                selected,
                budget,
            )?;
            values.truncate(start);
            values.push(value);
        }
        if values.len() != 1 || values[0].sort != FlatSort::Bool {
            return None;
        }
    }
    Some(())
}

fn head_index(
    exec: &Executor,
    name: &str,
    heads: &[&CheckedProjectionBinding],
    budget: &mut Budget<'_>,
) -> Option<usize> {
    for (index, head) in heads.iter().enumerate() {
        let Symbol::Named(candidate) = head.symbol() else {
            return None;
        };
        budget.charge(exec, candidate.len().checked_add(name.len())?)?;
        if candidate.as_ref() == name {
            return Some(index);
        }
    }
    None
}

fn finish(
    exec: &Executor,
    term: TermId,
    children: &[Value],
    binders: &[(String, Sort)],
    heads: &[&CheckedProjectionBinding],
    selected: &mut [Option<TermId>],
    budget: &mut Budget<'_>,
) -> Option<Value> {
    let sort = flat(exec.ctx.terms.sort(term))?;
    let ground = children.iter().all(|child| child.ground);
    match exec.ctx.terms.get(term) {
        TermData::Const(Constant::Bool(_)) if sort == FlatSort::Bool => {}
        TermData::Const(Constant::BitVec { value, width }) if sort == FlatSort::Bv(*width) => {
            observations::valid_bv(value, *width)?;
        }
        TermData::Var(name, _) => {
            for (binder, binder_sort) in binders {
                budget.charge(exec, binder.len().checked_add(name.len())?)?;
                if binder == name {
                    return (flat(binder_sort)? == sort).then_some(Value {
                        sort,
                        ground: false,
                    });
                }
            }
            let index = head_index(exec, name, heads, budget)?;
            if !heads[index].parameter_sorts().is_empty()
                || flat(heads[index].result_sort())? != sort
            {
                return None;
            }
            if matches!(sort, FlatSort::Bv(_)) {
                selected[index].get_or_insert(term);
            }
        }
        TermData::Not(_) if sort == FlatSort::Bool && children[0].sort == FlatSort::Bool => {}
        TermData::Ite(..)
            if children[0].sort == FlatSort::Bool
                && children[1].sort == sort
                && children[2].sort == sort => {}
        TermData::App(Symbol::Named(name), args) => {
            budget.charge(exec, name.len().checked_add(children.len())?)?;
            match name.as_ref() {
                "and" | "or"
                    if sort == FlatSort::Bool
                        && children.iter().all(|c| c.sort == FlatSort::Bool) => {}
                "=" if sort == FlatSort::Bool
                    && children.len() >= 2
                    && children.iter().all(|c| c.sort == children[0].sort) => {}
                "bvult" | "bvule" | "bvugt" | "bvuge" | "bvslt" | "bvsle" | "bvsgt" | "bvsge"
                    if sort == FlatSort::Bool
                        && children.len() == 2
                        && matches!(children[0].sort, FlatSort::Bv(_))
                        && children[0].sort == children[1].sort => {}
                "select" if children.len() == 2 => {
                    let FlatSort::Array(index_width, cell_width) = children[0].sort else {
                        return None;
                    };
                    if children[1].sort != FlatSort::Bv(index_width)
                        || sort != FlatSort::Bv(cell_width)
                    {
                        return None;
                    }
                    if ground {
                        let name = match exec.ctx.terms.get(args[0]) {
                            TermData::Var(name, _) => name.as_str(),
                            TermData::App(Symbol::Named(name), array_args)
                                if array_args.is_empty() =>
                            {
                                name.as_ref()
                            }
                            _ => return None,
                        };
                        let index = head_index(exec, name, heads, budget)?;
                        selected[index].get_or_insert(term);
                    }
                }
                _ => {
                    let index = head_index(exec, name, heads, budget)?;
                    let head = heads[index];
                    if children.len() != head.parameter_sorts().len()
                        || flat(head.result_sort())? != sort
                    {
                        return None;
                    }
                    for (child, parameter) in children.iter().zip(head.parameter_sorts()) {
                        if flat(parameter)? != child.sort {
                            return None;
                        }
                    }
                    if ground && matches!(sort, FlatSort::Bv(_)) {
                        selected[index].get_or_insert(term);
                    }
                }
            }
        }
        _ => return None,
    }
    // No term-only visited cache: a shared term is rechecked in each lexical
    // scope, and only genuinely binder-free occurrences nominate observations.
    Some(Value { sort, ground })
}

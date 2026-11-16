// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact hard-root definitions, original aliases, and complete source closure.

use super::*;

pub(super) struct Plan {
    pub(super) roots: Vec<TermId>,
    pub(super) members: BTreeMap<TermId, Vec<TermId>>,
    pub(super) representative: BTreeMap<TermId, TermId>,
    pub(super) definitions: BTreeMap<TermId, TermId>,
    pub(super) stamps: Vec<(TermId, TermEntryStamp)>,
    pub(super) base_reads: BTreeMap<TermId, Vec<(TermId, TermId)>>,
}

struct Facts {
    variables: BTreeSet<TermId>,
    adjacency: BTreeMap<TermId, Vec<TermId>>,
    definitions: Vec<(TermId, TermId)>,
    base_reads: Vec<(TermId, TermId, TermId)>,
}

fn complete_lambda(exec: &Executor, rhs: TermId) -> bool {
    recognize_range_lambda(&exec.ctx.terms, rhs).is_some()
        || recognize_identity_lambda(&exec.ctx.terms, rhs).is_some()
        || recognize_fill_lambda(&exec.ctx.terms, rhs).is_some()
}

// Eligibility is not evaluation or model authority. The existing capture
// evaluator independently validates every recursive constructor and scalar.
pub(super) fn finite_constructor(exec: &Executor, rhs: TermId) -> bool {
    if (rhs.0 as usize) >= exec.ctx.terms.len() {
        return false;
    }
    let Sort::Array(sort) = exec.ctx.terms.sort(rhs) else {
        return false;
    };
    if !matches!(&sort.index_sort, Sort::BitVec(index) if index.width == 64)
        || !(matches!(&sort.element_sort, Sort::Bool)
            || matches!(&sort.element_sort, Sort::BitVec(cell) if (1..=128).contains(&cell.width)))
    {
        return false;
    }
    let TermData::App(ay_core::Symbol::Named(symbol), args) = exec.ctx.terms.get(rhs) else {
        return false;
    };
    if !matches!(
        (symbol.as_str(), args.len()),
        ("const-array", 1) | ("store", 3)
    ) || args
        .iter()
        .any(|arg| (arg.0 as usize) >= exec.ctx.terms.len())
    {
        return false;
    }
    match (symbol.as_str(), args.as_slice()) {
        ("const-array", [value]) => exec.ctx.terms.sort(*value) == &sort.element_sort,
        ("store", [base, index, value]) => {
            exec.ctx.terms.sort(*base) == exec.ctx.terms.sort(rhs)
                && exec.ctx.terms.sort(*index) == &sort.index_sort
                && exec.ctx.terms.sort(*value) == &sort.element_sort
        }
        _ => false,
    }
}

fn complete_constructor(exec: &Executor, rhs: TermId) -> bool {
    complete_lambda(exec, rhs) || finite_constructor(exec, rhs)
}

fn hard_facts(exec: &Executor, roots: &[TermId]) -> Option<Facts> {
    let bytes = roots.len().checked_mul(size_of::<TermId>())?;
    super::super::super::construction_owner::pay_metadata(exec, roots.len(), bytes).ok()?;
    let mut hard = roots.to_vec();
    let mut variables = BTreeSet::new();
    let mut adjacency: BTreeMap<TermId, Vec<TermId>> = BTreeMap::new();
    let mut definitions = Vec::new();
    let mut base_reads = Vec::new();
    while let Some(term) = hard.pop() {
        super::super::super::construction_owner::pay_metadata(exec, 1, 0).ok()?;
        if (term.0 as usize) >= exec.ctx.terms.len() {
            return None;
        }
        let TermData::App(ay_core::Symbol::Named(symbol), args) = exec.ctx.terms.get(term) else {
            continue;
        };
        if args
            .iter()
            .any(|arg| (arg.0 as usize) >= exec.ctx.terms.len())
        {
            return None;
        }
        if exec.ctx.terms.sort(term) != &Sort::Bool {
            continue;
        }
        if symbol.as_str() == "and" {
            if args
                .iter()
                .any(|arg| exec.ctx.terms.sort(*arg) != &Sort::Bool)
            {
                return None;
            }
            let bytes = args.len().checked_mul(size_of::<TermId>())?;
            super::super::super::construction_owner::pay_metadata(exec, args.len(), bytes).ok()?;
            hard.try_reserve(args.len()).ok()?;
            hard.extend(args.iter().copied());
            continue;
        }
        if symbol.as_str() == "=" && args.len() == 2 {
            for (read, value) in [(args[0], args[1]), (args[1], args[0])] {
                let TermData::App(ay_core::Symbol::Named(select), operands) =
                    exec.ctx.terms.get(read)
                else {
                    continue;
                };
                if select.as_str() == "select"
                    && operands.len() == 2
                    && operands
                        .iter()
                        .all(|arg| (arg.0 as usize) < exec.ctx.terms.len())
                    && matches!(exec.ctx.terms.get(operands[0]), TermData::Var(..))
                    && exec.ctx.terms.sort(read) == exec.ctx.terms.sort(value)
                    && matches!(exec.ctx.terms.sort(operands[0]), Sort::Array(sort)
                        if exec.ctx.terms.sort(operands[1]) == &sort.index_sort
                            && exec.ctx.terms.sort(read) == &sort.element_sort)
                {
                    variables.insert(operands[0]);
                    base_reads.push((operands[0], operands[1], value));
                }
            }
        }
        if symbol.as_str() != "="
            || args.len() != 2
            || exec.ctx.terms.sort(args[0]) != exec.ctx.terms.sort(args[1])
            || !matches!(exec.ctx.terms.sort(args[0]), Sort::Array(_))
        {
            continue;
        }
        for (left, right) in [(args[0], args[1]), (args[1], args[0])] {
            if !matches!(exec.ctx.terms.get(left), TermData::Var(..)) {
                continue;
            }
            variables.insert(left);
            if matches!(exec.ctx.terms.get(right), TermData::Var(..)) {
                variables.insert(right);
                adjacency.entry(left).or_default().push(right);
            } else {
                definitions.push((left, right));
            }
        }
    }
    Some(Facts {
        variables,
        adjacency,
        definitions,
        base_reads,
    })
}

fn alias_classes(
    exec: &Executor,
    variables: &BTreeSet<TermId>,
    adjacency: &BTreeMap<TermId, Vec<TermId>>,
    work: &mut Work,
) -> Option<(BTreeMap<TermId, TermId>, BTreeMap<TermId, Vec<TermId>>)> {
    let mut representative = BTreeMap::new();
    let mut members = BTreeMap::new();
    for &variable in variables {
        if representative.contains_key(&variable) {
            continue;
        }
        let mut stack = vec![variable];
        let mut component = BTreeSet::new();
        while let Some(node) = stack.pop() {
            spend(exec, work, 1)?;
            if !component.insert(node) {
                continue;
            }
            if let Some(next) = adjacency.get(&node) {
                spend(exec, work, next.len())?;
                stack.try_reserve(next.len()).ok()?;
                stack.extend(next.iter().copied());
            }
        }
        let canonical = *component.first()?;
        for &node in &component {
            representative.insert(node, canonical);
        }
        members.insert(canonical, component.into_iter().collect());
    }
    Some((representative, members))
}

fn original_stamps(
    exec: &Executor,
    roots: &[TermId],
    work: &mut Work,
) -> Option<Vec<(TermId, TermEntryStamp)>> {
    let mut stamps = BTreeMap::new();
    let mut stack = roots.to_vec();
    while let Some(term) = stack.pop() {
        spend(exec, work, 1)?;
        if stamps.contains_key(&term) {
            continue;
        }
        stamps.insert(term, exec.ctx.terms.entry_stamp(term)?);
        let children = exec.ctx.terms.children(term);
        spend(exec, work, children.len())?;
        stack.try_reserve(children.len()).ok()?;
        stack.extend(children);
    }
    Some(stamps.into_iter().collect())
}

pub(super) fn capture(exec: &Executor, work: &mut Work) -> Option<Plan> {
    let roots = exec.independent_gate_query_roots().ok()?;
    let Facts {
        mut variables,
        adjacency,
        definitions,
        base_reads,
    } = hard_facts(exec, &roots)?;
    if !definitions
        .iter()
        .any(|(_, rhs)| complete_constructor(exec, *rhs))
    {
        return None;
    }
    for (_, rhs) in &definitions {
        variables.extend(array_variables(exec, *rhs, work)?);
    }
    let (representative, members) = alias_classes(exec, &variables, &adjacency, work)?;
    let mut selected = BTreeMap::new();
    for (variable, rhs) in &definitions {
        let canonical = *representative.get(variable)?;
        if !complete_constructor(exec, *rhs) {
            continue;
        }
        if selected
            .insert(canonical, *rhs)
            .is_some_and(|prior| prior != *rhs)
        {
            return None;
        }
    }
    // A different constructor definition for an owned alias class is not
    // discarded or used as another candidate for the same selected model.
    if definitions.iter().any(|(variable, rhs)| {
        representative
            .get(variable)
            .and_then(|canonical| selected.get(canonical))
            .is_some_and(|chosen| chosen != rhs)
    }) {
        return None;
    }
    let stamps = original_stamps(exec, &roots, work)?;
    let mut reads: BTreeMap<TermId, Vec<(TermId, TermId)>> = BTreeMap::new();
    for (array, index, value) in base_reads {
        spend(exec, work, 1)?;
        reads
            .entry(*representative.get(&array)?)
            .or_default()
            .push((index, value));
    }
    Some(Plan {
        roots,
        members,
        representative,
        definitions: selected,
        stamps,
        base_reads: reads,
    })
}

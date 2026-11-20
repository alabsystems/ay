// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Source-derived interval covers for candidate Int variables. These are
//! producer data: original witness checking and terminal source replay retain
//! all publication/completeness authority.

use super::*;

#[derive(Default)]
struct Endpoints {
    lo: Option<BigInt>,
    hi: Option<BigInt>,
    nonzero: bool,
}

fn merge(
    facts: &mut [Option<Endpoints>],
    var: TermId,
    lo: Option<&BigInt>,
    hi: Option<&BigInt>,
    owner: &CountedAdmission,
) -> Result<()> {
    owner.admit(1, 0)?;
    let fact = facts[var.index()].get_or_insert_with(Endpoints::default);
    if let Some(value) = lo {
        let replace = match &fact.lo {
            Some(old) => {
                range::pay_binary(old.bits(), value.bits(), false, owner)?;
                old < value
            }
            None => true,
        };
        if replace {
            fact.lo = Some(range::paid_copy(value, owner)?);
        }
    }
    if let Some(value) = hi {
        let replace = match &fact.hi {
            Some(old) => {
                range::pay_binary(old.bits(), value.bits(), false, owner)?;
                old > value
            }
            None => true,
        };
        if replace {
            fact.hi = Some(range::paid_copy(value, owner)?);
        }
    }
    Ok(())
}

fn variable(source: &TermStore, id: TermId) -> bool {
    source.sort(id) == &Sort::Int && matches!(source.get(id), TermData::Var(..))
}

fn equality_point(source: &TermStore, id: TermId) -> Option<(TermId, &BigInt)> {
    let TermData::App(Symbol::Named(name), args) = source.get(id) else {
        return None;
    };
    if name != "=" || args.len() != 2 {
        return None;
    }
    for (var, point) in [(args[0], args[1]), (args[1], args[0])] {
        if variable(source, var) {
            if let TermData::Const(Constant::Int(value)) = source.get(point) {
                return Some((var, value));
            }
        }
    }
    None
}

fn choice(
    source: &TermStore,
    args: &[TermId],
    owner: &CountedAdmission,
) -> Result<Vec<(TermId, Range)>> {
    // A disjunction of correlated finite tuples still bounds every component
    // constrained in every alternative. Flatten ORs, then extract only facts
    // implied by each alternative's conjunction. Never combine alternatives
    // as if their component values were independent source assertions.
    let mut marks = Vec::new();
    reserve_counted(&mut marks, source.len(), owner)?;
    owner.admit(source.len(), 0)?;
    marks.resize(source.len(), [0_usize; 3]);
    let mut branch_facts = slots(source.len(), owner)?;
    let mut branches = copy(args, owner)?;
    let mut pending = Vec::new();
    let mut variables = Vec::new();
    let mut result: Option<Vec<(TermId, Range)>> = None;
    let mut generation = 0_usize;
    while let Some(arg) = branches.pop() {
        owner.admit(1, 0)?;
        if let TermData::App(Symbol::Named(name), children) = source.get(arg) {
            if name == "or" {
                if std::mem::replace(&mut marks[arg.index()][2], 1) == 0 {
                    reserve_counted(&mut branches, children.len(), owner)?;
                    owner.admit(children.len(), 0)?;
                    branches.extend_from_slice(children);
                }
                continue;
            }
        }
        generation = generation.checked_add(1).ok_or_else(|| overflow(owner))?;
        reserve_counted(&mut pending, 1, owner)?;
        pending.push((arg, true));
        while let Some((id, positive)) = pending.pop() {
            owner.admit(1, 0)?;
            if std::mem::replace(&mut marks[id.index()][usize::from(positive)], generation)
                == generation
            {
                continue;
            }
            match source.get(id) {
                TermData::Not(child) => {
                    reserve_counted(&mut pending, 1, owner)?;
                    pending.push((*child, !positive));
                }
                TermData::App(Symbol::Named(name), children)
                    if (positive && name == "and") || (!positive && name == "or") =>
                {
                    reserve_counted(&mut pending, children.len(), owner)?;
                    owner.admit(children.len(), 0)?;
                    pending.extend(children.iter().copied().map(|id| (id, positive)));
                }
                _ if positive => {
                    if let Some((var, value)) = equality_point(source, id) {
                        if branch_facts[var.index()].is_none() {
                            reserve_counted(&mut variables, 1, owner)?;
                            variables.push(var);
                            branch_facts[var.index()] = Some(Range::point(value, owner)?);
                        }
                    }
                }
                _ => {}
            }
        }
        result = Some(if let Some(previous) = result {
            let mut common = Vec::new();
            reserve_counted(&mut common, previous.len(), owner)?;
            for (var, interval) in previous {
                owner.admit(1, 0)?;
                if let Some(other) = &branch_facts[var.index()] {
                    common.push((var, interval.hull(other, owner)?));
                }
            }
            common
        } else {
            let mut first = Vec::new();
            reserve_counted(&mut first, variables.len(), owner)?;
            for &var in &variables {
                owner.admit(1, 0)?;
                let interval = branch_facts[var.index()].take().ok_or(Error::Invalid)?;
                first.push((var, interval));
            }
            first
        });
        for var in variables.drain(..) {
            owner.admit(1, 0)?;
            branch_facts[var.index()] = None;
        }
        if result.as_ref().is_some_and(Vec::is_empty) {
            break;
        }
    }
    Ok(result.unwrap_or_default())
}

fn atoms(
    source: &TermStore,
    roots: &[TermId],
    owner: &CountedAdmission,
) -> Result<Vec<(TermId, bool)>> {
    let mut seen = Vec::new();
    reserve_counted(&mut seen, source.len(), owner)?;
    owner.admit(source.len(), 0)?;
    seen.resize(source.len(), [false; 2]);
    let mut pending = Vec::new();
    reserve_counted(&mut pending, roots.len(), owner)?;
    pending.extend(roots.iter().copied().map(|id| (id, true)));
    let mut result = Vec::new();
    while let Some((id, positive)) = pending.pop() {
        owner.admit(1, 0)?;
        if std::mem::replace(&mut seen[id.index()][usize::from(positive)], true) {
            continue;
        }
        match source.get(id) {
            TermData::Not(child) => {
                reserve_counted(&mut pending, 1, owner)?;
                pending.push((*child, !positive));
            }
            TermData::App(Symbol::Named(name), args)
                if (positive && name == "and") || (!positive && name == "or") =>
            {
                reserve_counted(&mut pending, args.len(), owner)?;
                owner.admit(args.len(), 0)?;
                pending.extend(args.iter().copied().map(|id| (id, positive)));
            }
            _ => {
                reserve_counted(&mut result, 1, owner)?;
                result.push((id, positive));
            }
        }
    }
    Ok(result)
}

fn direct_fact(
    source: &TermStore,
    id: TermId,
    positive: bool,
    facts: &mut [Option<Endpoints>],
    owner: &CountedAdmission,
) -> Result<()> {
    let TermData::App(Symbol::Named(name), args) = source.get(id) else {
        return Ok(());
    };
    if positive && name == "or" {
        for (var, interval) in choice(source, args, owner)? {
            owner.admit(1, 0)?;
            merge(facts, var, Some(&interval.lo), Some(&interval.hi), owner)?;
            if interval.nonzero {
                facts[var.index()]
                    .get_or_insert_with(Endpoints::default)
                    .nonzero = true;
            }
        }
        return Ok(());
    }
    if args.len() != 2 {
        return Ok(());
    }
    for (var, constant, reversed) in [(args[0], args[1], false), (args[1], args[0], true)] {
        owner.admit(1, 0)?;
        if !variable(source, var) {
            continue;
        }
        let TermData::Const(Constant::Int(value)) = source.get(constant) else {
            continue;
        };
        if value.is_zero() && ((!positive && name == "=") || (positive && name == "distinct")) {
            facts[var.index()]
                .get_or_insert_with(Endpoints::default)
                .nonzero = true;
            continue;
        }
        let relation = match (name.as_str(), positive, reversed) {
            ("=", true, _) => "=",
            ("<=", true, false) | (">=", true, true) | (">", false, false) | ("<", false, true) => {
                "<="
            }
            ("<", true, false) | (">", true, true) | (">=", false, false) | ("<=", false, true) => {
                "<"
            }
            (">=", true, false) | ("<=", true, true) | ("<", false, false) | (">", false, true) => {
                ">="
            }
            (">", true, false) | ("<", true, true) | ("<=", false, false) | (">=", false, true) => {
                ">"
            }
            _ => continue,
        };
        match relation {
            "=" => merge(facts, var, Some(value), Some(value), owner)?,
            "<=" => merge(facts, var, None, Some(value), owner)?,
            ">=" => merge(facts, var, Some(value), None, owner)?,
            "<" => {
                range::pay_binary(value.bits(), 1, false, owner)?;
                let bound = value - BigInt::one();
                merge(facts, var, None, Some(&bound), owner)?;
            }
            ">" => {
                range::pay_binary(value.bits(), 1, false, owner)?;
                let bound = value + BigInt::one();
                merge(facts, var, Some(&bound), None, owner)?;
            }
            _ => return Err(Error::Invalid),
        }
    }
    Ok(())
}

pub(super) fn infer(
    source: &TermStore,
    roots: &[TermId],
    order: &[TermId],
    owner: &CountedAdmission,
) -> Result<Vec<Option<Range>>> {
    let atoms = atoms(source, roots, owner)?;
    let mut facts = slots(source.len(), owner)?;
    for &(atom, positive) in &atoms {
        direct_fact(source, atom, positive, &mut facts, owner)?;
    }
    let mut bounds = slots(source.len(), owner)?;
    for &id in order {
        owner.admit(1, 0)?;
        if let Some(Endpoints {
            lo: Some(lo),
            hi: Some(hi),
            nonzero,
        }) = &facts[id.index()]
        {
            let mut interval = Range::between(lo, hi, owner)?;
            interval.nonzero |= *nonzero;
            bounds[id.index()] = Some(interval);
        }
    }
    // A finite domain is installed once; nonzero can strengthen once. Thus
    // equality propagation has at most two successful updates per source Int
    // variable, without an unbounded interval-tightening fixpoint.
    loop {
        let mut known = slots(source.len(), owner)?;
        let mut ignored_width = 2;
        for &id in order {
            owner.admit(1, 0)?;
            if source.sort(id) != &Sort::Int {
                continue;
            }
            let ready = match source.get(id) {
                TermData::Const(Constant::Int(_)) => true,
                TermData::Var(..) => bounds[id.index()].is_some(),
                TermData::Ite(_, yes, no) => {
                    known[yes.index()].is_some() && known[no.index()].is_some()
                }
                TermData::App(_, args) => {
                    owner.admit(args.len(), 0)?;
                    args.iter().all(|arg| known[arg.index()].is_some())
                }
                _ => false,
            };
            if ready {
                match integer_range(source, id, &known, &bounds, &mut ignored_width, owner) {
                    Ok(interval) => known[id.index()] = Some(interval),
                    // A later source equality may supply a missing nonzero
                    // property. The final full analysis still refuses every
                    // unsupported expression after this finite fixpoint.
                    Err(Error::Unsupported) => {}
                    Err(error) => return Err(error),
                }
            }
        }
        let mut changed = false;
        for &(atom, positive) in &atoms {
            owner.admit(1, 0)?;
            let TermData::App(Symbol::Named(name), args) = source.get(atom) else {
                continue;
            };
            if !positive || name != "=" || args.len() != 2 {
                continue;
            }
            for (var, other) in [(args[0], args[1]), (args[1], args[0])] {
                owner.admit(1, 0)?;
                if !variable(source, var) {
                    continue;
                }
                let Some(interval) = &known[other.index()] else {
                    continue;
                };
                if let Some(current) = &mut bounds[var.index()] {
                    if interval.nonzero && !current.nonzero {
                        current.nonzero = true;
                        changed = true;
                    }
                    continue;
                }
                merge(
                    &mut facts,
                    var,
                    Some(&interval.lo),
                    Some(&interval.hi),
                    owner,
                )?;
                if interval.nonzero {
                    facts[var.index()]
                        .get_or_insert_with(Endpoints::default)
                        .nonzero = true;
                }
                let Some(Endpoints {
                    lo: Some(lo),
                    hi: Some(hi),
                    nonzero,
                }) = &facts[var.index()]
                else {
                    return Err(Error::Invalid);
                };
                let mut interval = Range::between(lo, hi, owner)?;
                interval.nonzero |= *nonzero;
                bounds[var.index()] = Some(interval);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    for &id in order {
        owner.admit(1, 0)?;
        if variable(source, id) && bounds[id.index()].is_none() {
            return Err(Error::Unsupported);
        }
    }
    Ok(bounds)
}

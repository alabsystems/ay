// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Paid dispatch metadata and typed DAG admission on the current attempt.
use super::*;
use crate::executor::model::CandidateOwner;
use crate::executor_types::UnknownOrigin;

pub(super) struct Fence {
    store: ay_core::term::TermStoreSnapshotStamp,
    source: ay_frontend::SourceContextStamp,
    attempt: super::super::model::EvaluationAttempt,
}
impl Fence {
    pub(super) fn capture(exec: &Executor) -> Self {
        Self {
            store: exec.ctx.terms.snapshot_stamp(),
            source: exec.ctx.source_context_stamp(),
            attempt: exec.evaluation_attempt(),
        }
    }
    fn check(&self, exec: &Executor, owner: &mut CandidateOwner) -> Result<(), UnknownOrigin> {
        owner.poll()?;
        if self.store != exec.ctx.terms.snapshot_stamp()
            || self.source != exec.ctx.source_context_stamp()
            || !self.attempt.is_same_attempt(&exec.evaluation_attempt())
        {
            return Err(owner.refuse(UnknownOrigin::IncompleteSolverLane));
        }
        Ok(())
    }
}

/// Drop copied IDs before releasing their actual original arena custody.
/// This is input DATA for early dispatch, never theorem/model authority.
pub(in crate::executor) struct ProblemRoots {
    roots: Vec<TermId>,
    _owner: CandidateOwner,
}
impl ProblemRoots {
    pub(in crate::executor) fn roots(&self) -> &[TermId] {
        &self.roots
    }
}

pub(super) fn public_problem_roots(exec: &Executor) -> Result<ProblemRoots, UnknownOrigin> {
    let fence = Fence::capture(exec);
    let mut owner = CandidateOwner::capture(exec)?;
    fence.check(exec, &mut owner)?;
    let count = exec
        .ctx
        .assertions
        .len()
        .checked_add(exec.ctx.objectives().len())
        .and_then(|n| n.checked_add(exec.ctx.soft_constraints().len()))
        .ok_or_else(|| owner.refuse(UnknownOrigin::MemoryBudget))?;
    let bytes = count
        .checked_mul(std::mem::size_of::<TermId>())
        .ok_or_else(|| owner.refuse(UnknownOrigin::MemoryBudget))?;
    owner.pay(0, bytes)?;
    fence.check(exec, &mut owner)?;
    let mut roots = Vec::new();
    roots
        .try_reserve_exact(count)
        .map_err(|_| owner.refuse(UnknownOrigin::MemoryBudget))?;
    let extra = roots
        .capacity()
        .checked_sub(count)
        .and_then(|n| n.checked_mul(std::mem::size_of::<TermId>()))
        .ok_or_else(|| owner.refuse(UnknownOrigin::MemoryBudget))?;
    owner.pay(0, extra)?;
    fence.check(exec, &mut owner)?;
    for root in exec
        .ctx
        .assertions
        .iter()
        .copied()
        .chain(exec.ctx.objectives().iter().map(|objective| objective.term))
        .chain(exec.ctx.soft_constraints().iter().map(|soft| soft.term))
    {
        owner.pay(1, 0)?;
        fence.check(exec, &mut owner)?;
        roots.push(root);
    }
    fence.check(exec, &mut owner)?;
    Ok(ProblemRoots {
        roots,
        _owner: owner,
    })
}

pub(super) struct Plan {
    pub seen: HashSet<TermId>,
    pub vars: Vec<(TermId, u32)>,
    pub count: usize,
}
pub(super) enum Inspection {
    Free,
    Unsupported,
    Field(Plan),
}

pub(super) fn pay(
    owner: &mut CandidateOwner,
    budget: &mut usize,
    work: usize,
    bytes: usize,
) -> Result<(), UnknownOrigin> {
    let Some(left) = budget.checked_sub(work) else {
        *budget = 0;
        return Err(owner.refuse(UnknownOrigin::DeterministicResourceBudget));
    };
    *budget = left;
    owner.pay(work, bytes)
}
pub(super) fn reserve<T>(
    out: &mut Vec<T>,
    extra: usize,
    owner: &mut CandidateOwner,
    budget: &mut usize,
) -> Result<(), UnknownOrigin> {
    let needed = out
        .len()
        .checked_add(extra)
        .ok_or_else(|| owner.refuse(UnknownOrigin::MemoryBudget))?;
    if needed > out.capacity() {
        let target = needed
            .max(
                out.capacity()
                    .checked_mul(2)
                    .ok_or_else(|| owner.refuse(UnknownOrigin::MemoryBudget))?,
            )
            .max(4);
        let bytes = target
            .checked_mul(std::mem::size_of::<T>())
            .ok_or_else(|| owner.refuse(UnknownOrigin::MemoryBudget))?;
        pay(
            owner,
            budget,
            out.len()
                .checked_add(target)
                .ok_or_else(|| owner.refuse(UnknownOrigin::DeterministicResourceBudget))?,
            bytes,
        )?;
        out.try_reserve_exact(target - out.len())
            .map_err(|_| owner.refuse(UnknownOrigin::MemoryBudget))?;
        if out.capacity() > target {
            pay(
                owner,
                budget,
                0,
                (out.capacity() - target)
                    .checked_mul(std::mem::size_of::<T>())
                    .ok_or_else(|| owner.refuse(UnknownOrigin::MemoryBudget))?,
            )?;
        }
    }
    Ok(())
}
fn insert(
    seen: &mut HashSet<TermId>,
    id: TermId,
    owner: &mut CandidateOwner,
    budget: &mut usize,
) -> Result<bool, UnknownOrigin> {
    pay(owner, budget, 1, 0)?;
    if seen.contains(&id) {
        return Ok(false);
    }
    if seen.len() == seen.capacity() {
        let target = seen
            .capacity()
            .checked_mul(2)
            .ok_or_else(|| owner.refuse(UnknownOrigin::MemoryBudget))?
            .max(4);
        // Fixed-size keys use the native counted registry envelope for bucket
        // controls/rehash storage, admitted BEFORE the opaque allocation.
        let bytes = target
            .checked_mul(std::mem::size_of::<TermId>())
            .and_then(|n| n.checked_mul(8))
            .and_then(|n| n.checked_add(4096))
            .ok_or_else(|| owner.refuse(UnknownOrigin::MemoryBudget))?;
        pay(
            owner,
            budget,
            seen.len()
                .checked_add(target)
                .ok_or_else(|| owner.refuse(UnknownOrigin::DeterministicResourceBudget))?,
            bytes,
        )?;
        seen.try_reserve(target - seen.len())
            .map_err(|_| owner.refuse(UnknownOrigin::MemoryBudget))?;
    }
    Ok(seen.insert(id))
}

pub(super) fn inspect(
    exec: &Executor,
    roots: &[TermId],
    fence: &Fence,
    owner: &mut CandidateOwner,
    budget: &mut usize,
) -> Result<Inspection, UnknownOrigin> {
    // Reuse only the producer's positive field-free metadata. Cache lookup is
    // native metadata work; no fresh field/search allowance is installed.
    let mut known = false;
    let mut uncertain = false;
    for &root in roots {
        owner.pay(1, 0)?;
        fence.check(exec, owner)?;
        match exec.ctx.terms.finite_field_presence(root) {
            Some(false) => {}
            Some(true) => {
                known = true;
                break;
            }
            None => {
                uncertain = true;
                break;
            }
        }
    }
    if !known && !uncertain {
        return Ok(Inspection::Free);
    }
    // Resolving a reader's metadata cannot promote it into a mutable solver
    // source or let proof construction mutate a positional checker snapshot.
    if !exec.ctx.terms.is_mutable_producer() {
        return Ok(Inspection::Unsupported);
    }
    if !exec.ctx.objectives().is_empty() || !exec.ctx.soft_constraints().is_empty() {
        return Ok(Inspection::Unsupported);
    }
    if let Some(available) = owner.remaining_work() {
        *budget = (*budget).min(usize::try_from(available).unwrap_or(usize::MAX));
    }
    let mut seen = HashSet::default();
    let mut stack = Vec::new();
    reserve(&mut stack, roots.len(), owner, budget)?;
    pay(owner, budget, roots.len(), 0)?;
    stack.extend_from_slice(roots);
    let mut supported = true;
    while let Some(id) = stack.pop() {
        fence.check(exec, owner)?;
        if id.index() >= exec.ctx.terms.len() {
            return Ok(Inspection::Unsupported);
        }
        if !insert(&mut seen, id, owner, budget)? {
            continue;
        }
        let sort = exec.ctx.terms.sort(id);
        known |= matches!(sort, Sort::FiniteField(_));
        if !matches!(sort, Sort::Bool | Sort::FiniteField(_)) {
            supported = false;
        }
        // Composite sort metadata that was not established at construction
        // remains unresolved. Never route it to UF as proven field-free.
        if matches!(sort, Sort::Array(_) | Sort::Seq(_) | Sort::Datatype(_)) {
            return Ok(Inspection::Unsupported);
        }
        let children = match exec.ctx.terms.get(id) {
            TermData::Const(value) => {
                known |= matches!(value, Constant::FiniteField { .. });
                &[][..]
            }
            TermData::Var(..) => &[],
            TermData::App(symbol, args) => {
                if let Symbol::Named(name) = symbol {
                    pay(owner, budget, name.len(), 0)?;
                    known |= matches!(name.as_str(), "ff.add" | "ff.mul" | "ff.neg" | "ff.bitsum");
                }
                args.as_slice()
            }
            TermData::Not(child) => std::slice::from_ref(child),
            TermData::Ite(c, a, b) => {
                reserve(&mut stack, 3, owner, budget)?;
                for child in [*c, *a, *b] {
                    pay(owner, budget, 1, 0)?;
                    if child.index() >= id.index() {
                        return Ok(Inspection::Unsupported);
                    }
                    stack.push(child);
                }
                continue;
            }
            _ => return Ok(Inspection::Unsupported),
        };
        reserve(&mut stack, children.len(), owner, budget)?;
        for &child in children {
            pay(owner, budget, 1, 0)?;
            if child.index() >= id.index() {
                return Ok(Inspection::Unsupported);
            }
            stack.push(child);
        }
    }
    if !known {
        return Ok(Inspection::Free);
    }
    if !supported {
        return Ok(Inspection::Unsupported);
    }
    let mut vars = Vec::new();
    let mut count = 1usize;
    for &id in &seen {
        pay(owner, budget, 1, 0)?;
        fence.check(exec, owner)?;
        let sort = exec.ctx.terms.sort(id);
        let valid = match exec.ctx.terms.get(id) {
            TermData::Const(Constant::Bool(_)) => sort == &Sort::Bool,
            TermData::Const(Constant::FiniteField { value, field }) => {
                *value < field.modulus() && sort == &Sort::FiniteField(*field)
            }
            TermData::Var(..) => {
                let size = match sort {
                    Sort::Bool => 2,
                    Sort::FiniteField(f) => f.modulus(),
                    _ => return Ok(Inspection::Unsupported),
                };
                count = count
                    .checked_mul(size as usize)
                    .filter(|n| *n <= 65536)
                    .unwrap_or(65537);
                if count <= 65536 {
                    reserve(&mut vars, 1, owner, budget)?;
                    vars.push((id, size));
                }
                true
            }
            TermData::Not(a) => sort == &Sort::Bool && exec.ctx.terms.sort(*a) == &Sort::Bool,
            TermData::Ite(c, a, b) => {
                exec.ctx.terms.sort(*c) == &Sort::Bool
                    && exec.ctx.terms.sort(*a) == sort
                    && exec.ctx.terms.sort(*b) == sort
            }
            TermData::App(Symbol::Named(name), args) => {
                pay(
                    owner,
                    budget,
                    name.len()
                        .checked_add(args.len())
                        .ok_or_else(|| owner.refuse(UnknownOrigin::DeterministicResourceBudget))?,
                    0,
                )?;
                if exec.ctx.terms.is_declared_function(name) {
                    false
                } else {
                    match name.as_str() {
                        "ff.add" | "ff.mul" | "ff.bitsum" | "ff.neg" => {
                            matches!(sort, Sort::FiniteField(_))
                                && (if name == "ff.neg" {
                                    args.len() == 1
                                } else {
                                    args.len() >= 2
                                })
                                && args.iter().all(|arg| exec.ctx.terms.sort(*arg) == sort)
                        }
                        "=" | "distinct" => {
                            sort == &Sort::Bool
                                && args.len() >= 2
                                && args.iter().all(|arg| {
                                    exec.ctx.terms.sort(*arg) == exec.ctx.terms.sort(args[0])
                                })
                        }
                        "and" | "or" | "xor" | "=>" | "not" => {
                            sort == &Sort::Bool
                                && args
                                    .iter()
                                    .all(|arg| exec.ctx.terms.sort(*arg) == &Sort::Bool)
                                && (name != "=>" || args.len() == 2)
                                && (name != "not" || args.len() == 1)
                        }
                        _ => false,
                    }
                }
            }
            _ => false,
        };
        if !valid {
            return Ok(Inspection::Unsupported);
        }
    }
    for &root in roots {
        pay(owner, budget, 1, 0)?;
        if exec.ctx.terms.sort(root) != &Sort::Bool {
            return Ok(Inspection::Unsupported);
        }
    }
    fence.check(exec, owner)?;
    Ok(Inspection::Field(Plan { seen, vars, count }))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn problem() -> Executor {
        let mut exec = Executor::new();
        let commands = ay_frontend::parse("(set-logic QF_FF)(declare-const x (_ FiniteField 7))(assert (= x #f1m7))(assert (distinct x #f2m7))").unwrap();
        exec.execute_all(&commands).unwrap();
        exec
    }

    #[test]
    fn refused_field_dispatch_input_copy_never_becomes_an_empty_problem() {
        let mut exec = problem();
        assert_eq!(exec.ctx.assertions.len(), 2);
        exec.term_memory_limit = Some(0);
        assert!(matches!(
            public_problem_roots(&exec),
            Err(UnknownOrigin::MemoryBudget)
        ));
        exec.term_memory_limit = None;
        assert!(public_problem_roots(&exec).is_err());
        let fresh = problem();
        let input = public_problem_roots(&fresh).unwrap();
        assert_eq!(input.roots, fresh.ctx.assertions);
        assert!(!input.roots.is_empty());
    }

    #[test]
    fn field_frontend_fence_binds_actual_attempt_beyond_unchanged_source_stamps() {
        let exec = problem();
        let fence = Fence::capture(&exec);
        let source = exec.ctx.source_context_stamp();
        let store = exec.ctx.terms.snapshot_stamp();
        let _read = exec.begin_external_evaluation_read();
        assert_eq!(exec.ctx.source_context_stamp(), source);
        assert_eq!(exec.ctx.terms.snapshot_stamp(), store);
        let mut owner = CandidateOwner::capture(&exec).unwrap();
        assert!(matches!(
            fence.check(&exec, &mut owner),
            Err(UnknownOrigin::IncompleteSolverLane)
        ));
    }
}

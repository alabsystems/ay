// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Small equality refutations from exact, source-activated Boolean branches.
//!
//! This producer never assumes a preprocessed fact. A selected equality carries
//! its original root, optional separately asserted positive guard, and exact
//! conjunction path. A simple BFS supplies only the nonredundant equality cone;
//! existing strict rules and full-original premise authentication supply all
//! authority. Arrays in the source are not equality-graph vertices.

use ay_core::{AletheRule, Constant, Proof, ProofId, Sort, Symbol, TermData, TermId, TermStore};

mod emit;
mod shape;
#[cfg(test)]
mod tests;
mod wrapper;

const MAX_ROOTS: usize = 64;
const MAX_SOURCE_NODES: usize = 16_384;
const MAX_DEPTH: usize = 64;
const MAX_PLAN_NODES: usize = 4_096;
const MAX_EQUALITIES: usize = 256;
const MAX_GOALS: usize = 16;
const MAX_PROOF_STEPS: usize = 4_096;
const MAX_WORK: usize = 262_144;
const MAX_BYTES: usize = 16 * 1024 * 1024;

/// The same monotonically decreasing allowance covers source admission,
/// retained metadata, every BFS attempt, proof construction and strict replay.
/// These local ceilings only decline a producer; they are not solver knobs.
struct Budget<'a> {
    progress: &'a mut dyn FnMut(usize, usize) -> bool,
    work: usize,
    bytes: usize,
    stopped: bool,
}

impl Budget<'_> {
    fn charge(&mut self, work: usize, bytes: usize) -> Option<()> {
        if self.stopped {
            return None;
        }
        let next = self
            .work
            .checked_add(work)
            .zip(self.bytes.checked_add(bytes));
        let Some((next_work, next_bytes)) = next else {
            self.stopped = true;
            return None;
        };
        if next_work > MAX_WORK || next_bytes > MAX_BYTES || !(self.progress)(work, bytes) {
            self.stopped = true;
            return None;
        }
        self.work = next_work;
        self.bytes = next_bytes;
        Some(())
    }

    /// Prepay the entire new allocation and copying of old elements before a
    /// geometric reserve. Freed or discarded buffers never refund the ledger.
    fn reserve<T>(&mut self, values: &mut Vec<T>, extra: usize) -> Option<()> {
        let needed = values.len().checked_add(extra)?;
        if needed <= values.capacity() {
            return Some(());
        }
        let capacity = needed.max(values.capacity().checked_mul(2)?).max(4);
        let bytes = capacity.checked_mul(size_of::<T>())?;
        self.charge(values.len().checked_add(1)?, bytes.checked_add(64)?)?;
        values
            .try_reserve_exact(capacity.checked_sub(values.len())?)
            .ok()?;
        Some(())
    }

    fn push<T>(&mut self, values: &mut Vec<T>, value: T) -> Option<()> {
        self.charge(1, 0)?;
        self.reserve(values, 1)?;
        values.push(value);
        Some(())
    }

    fn copy<T: Copy>(&mut self, values: &[T]) -> Option<Vec<T>> {
        let mut result = Vec::new();
        self.charge(values.len(), 0)?;
        self.reserve(&mut result, values.len())?;
        result.extend_from_slice(values);
        Some(result)
    }
}

pub(super) fn derive(
    terms: &mut TermStore,
    originals: &[TermId],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Option<Proof> {
    let mut budget = Budget {
        progress,
        work: 0,
        bytes: 0,
        stopped: false,
    };
    budget.charge(0, 0)?;
    if originals.is_empty() || originals.len() > MAX_ROOTS {
        return None;
    }
    admit_source(terms, originals, &mut budget)?;
    let plan = shape::scan(terms, originals, &mut budget)?;
    for goal in &plan.goals {
        let Some(path) = shape::equality_path(&plan.edges, goal, &mut budget)? else {
            continue;
        };
        let (proof, conclusion) = emit::build(terms, &plan, goal, &path, &mut budget)?;
        let authenticated =
            ay_proof::authenticate_premise_clauses_strict_with_context_and_progress(
                &proof,
                terms,
                None,
                None,
                originals,
                &mut |work, bytes| budget.charge(work, bytes).is_some(),
            )
            .ok()?;
        if !authenticated.clause(conclusion)?.is_empty() {
            return None;
        }
        budget.charge(0, 0)?;
        return Some(proof);
    }
    None
}

fn live(terms: &TermStore, term: TermId) -> Option<()> {
    ((term.0 as usize) < terms.len()).then_some(())
}

/// Read all original syntax before retaining recipes. No recursive AST/sort
/// clone or unmetered `children()` allocation is needed. Repeated occurrences
/// and cycles consume the same depth/node allowance, rather than disappearing
/// behind a global seen set. Unsupported source families simply decline.
fn admit_source(terms: &TermStore, originals: &[TermId], budget: &mut Budget<'_>) -> Option<()> {
    let mut stack = Vec::new();
    for &root in originals {
        live(terms, root)?;
        if terms.sort(root) != &Sort::Bool {
            return None;
        }
        budget.push(&mut stack, (root, 0usize))?;
    }
    let mut visited = 0usize;
    while let Some((term, depth)) = stack.pop() {
        visited = visited.checked_add(1)?;
        if visited > MAX_SOURCE_NODES || depth > MAX_DEPTH {
            return None;
        }
        live(terms, term)?;
        budget.charge(1, 0)?;
        admit_sort(terms.sort(term), 0, budget)?;
        let children: &[TermId] = match terms.get(term) {
            TermData::Var(name, _) => {
                budget.charge(name.len(), name.len())?;
                continue;
            }
            TermData::Const(Constant::Bool(_)) if terms.sort(term) == &Sort::Bool => continue,
            TermData::Const(Constant::BitVec { value, width }) => {
                let bits = usize::try_from(value.bits()).ok()?;
                budget.charge(bits.div_ceil(64).checked_add(1)?, bits.div_ceil(8))?;
                if terms.sort(term).bitvec_width() != Some(*width)
                    || value.sign() == num_bigint::Sign::Minus
                    || value.bits() > u64::from(*width)
                {
                    return None;
                }
                continue;
            }
            TermData::App(symbol, args) => {
                budget.charge(symbol.name().len(), symbol.name().len())?;
                if let Symbol::Indexed(_, indices) = symbol {
                    budget.charge(indices.len(), indices.len().checked_mul(4)?)?;
                }
                args
            }
            TermData::Not(child) => {
                live(terms, *child)?;
                if terms.sort(term) != &Sort::Bool || terms.sort(*child) != &Sort::Bool {
                    return None;
                }
                std::slice::from_ref(child)
            }
            TermData::Ite(condition, then_term, else_term) => {
                for child in [*condition, *then_term, *else_term] {
                    live(terms, child)?;
                    admit_sort(terms.sort(child), 0, budget)?;
                }
                if terms.sort(*condition) != &Sort::Bool
                    || terms.sort(*then_term) != terms.sort(term)
                    || terms.sort(*else_term) != terms.sort(term)
                {
                    return None;
                }
                for child in [*condition, *then_term, *else_term] {
                    budget.push(&mut stack, (child, depth.checked_add(1)?))?;
                }
                continue;
            }
            _ => return None,
        };
        if stack.len().checked_add(children.len())? > MAX_SOURCE_NODES {
            return None;
        }
        for &child in children {
            live(terms, child)?;
            budget.push(&mut stack, (child, depth.checked_add(1)?))?;
        }
    }
    Some(())
}

fn admit_sort(sort: &Sort, depth: usize, budget: &mut Budget<'_>) -> Option<()> {
    budget.charge(1, 0)?;
    if depth > MAX_DEPTH {
        return None;
    }
    match sort {
        Sort::Bool => Some(()),
        Sort::BitVec(width)
            if width.width > 0 && width.width <= crate::api::MAX_API_BITVECTOR_WIDTH =>
        {
            budget.charge((width.width as usize).div_ceil(64), 0)
        }
        Sort::Array(array) => {
            admit_sort(&array.index_sort, depth.checked_add(1)?, budget)?;
            admit_sort(&array.element_sort, depth.checked_add(1)?, budget)
        }
        _ => None,
    }
}

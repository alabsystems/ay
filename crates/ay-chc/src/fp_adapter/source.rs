// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Complete typed DAG census before any legacy FP circuit allocation.

use std::collections::BTreeMap;

use ay_core::original_query::WorkBudget;
use ay_core::term::{TermData, TermId, TermStore};
use ay_core::Sort;

use super::{typed, FpAdapterError, FpInputBinding};

pub(super) const MAX_NODES: usize = 512;
pub(super) const MAX_OCCURRENCES: usize = 4096;
pub(super) const MAX_DEPTH: usize = 64;
pub(super) const MAX_ARITY: usize = 64;
pub(super) const MAX_NAME: usize = 256;
const ARITHMETIC_GATES: usize = 262_144;
// The 161-bit restoring core alone uses up to 388_332 primitive gates.
// Including unpack, normalization, rounding and special constraints is below
// 524_288 for binary32/64. Charge the same fee even when pow2 rewriting fires.
const DIVISION_GATES: usize = 524_288;
// Narrow native kernel N(q)=18q²+12q plus all surrounding IEEE paths.
// Independently bounded internal Add/Sub each 16,384; T64=891,990.
// The fixed fee is not a claim that all other costs fit a 4 GiB owner.
const REMAINDER_GATES: usize = 917_504;
// Shared remainder core plus separately bounded magnitude comparison/mux.
// T64<=891,990+4,096=896,086; see the distinct truncating cost proof.
const TRUNCATING_GATES: usize = 917_504;
// Native ceilings 131,072 are NOT the adapter fee: full transfer/cache/link
// and cumulative logical copy costs are separately priced in the source cost.
const SQUARE_ROOT_GATES: usize = 262_144;
const FUSED_GATES: usize = 262_144;
// Complete native/cache/copy/transfer bound: the development design notes
// Emax=6450, Hmax=10618; J=69,139,456 bytes, W=15,498,752 work.
const NUMERIC_GATES: usize = 18_432;
const OTHER_GATES: usize = 4096;
const MAX_GATES: usize = 16_777_216;

#[derive(Clone, Copy)]
struct Counts {
    occurrences: usize,
    arithmetic: usize,
    divisions: usize,
    remainders: usize,
    truncating: usize,
    square_roots: usize,
    fused: usize,
    numeric: usize,
    height: usize,
}

enum Visit {
    Active,
    Done(Counts),
}

pub(super) struct Plan {
    pub gates: usize,
    pub clauses: usize,
    pub occurrences: usize,
}

impl Plan {
    pub fn prepay(&self, budget: &mut WorkBudget<'_>) -> Result<(), FpAdapterError> {
        // See packet cost audit: this deliberately does not tighten the fixed
        // binary64 envelope to the actual format, simplifications or memo hits.
        // It covers intermediate vectors, all CNF/cache retention and copying,
        // output Arc/Vec/name materialization, validation and destruction.
        let work = self
            .gates
            .checked_mul(1024)
            .ok_or_else(|| budget.refuse_exhaustion())?;
        let bytes = self
            .gates
            .checked_mul(4096)
            .ok_or_else(|| budget.refuse_exhaustion())?;
        budget.admit(work, bytes)?;
        Ok(())
    }
}

pub(super) fn plan(
    terms: &TermStore,
    roots: &[TermId],
    bindings: &[FpInputBinding<'_>],
    budget: &mut WorkBudget<'_>,
) -> Result<Plan, FpAdapterError> {
    if roots.is_empty() || roots.len() > MAX_NODES || bindings.len() > MAX_NODES {
        return Err(FpAdapterError::Unsupported("root/input population"));
    }
    // Prepay maps and bounded recursive frames BEFORE their first allocation.
    budget.admit(4096, MAX_NODES * 1024 + MAX_DEPTH * 1024)?;
    validate_bindings(terms, bindings, budget)?;
    let mut seen = BTreeMap::new();
    let mut total = Counts {
        occurrences: 0,
        arithmetic: 0,
        divisions: 0,
        remainders: 0,
        truncating: 0,
        square_roots: 0,
        fused: 0,
        numeric: 0,
        height: 0,
    };
    for &root in roots {
        budget.charge(256)?;
        if terms.entry_stamp(root).is_none() || terms.sort(root) != &Sort::Bool {
            return Err(FpAdapterError::Invalid("root must be live Bool"));
        }
        let counts = visit(terms, root, bindings, &mut seen, 0, budget)?;
        total = combine(total, counts)?;
    }
    let gates = circuit_gates(total)?;
    let clauses = gates
        .checked_mul(4)
        .and_then(|v| v.checked_add(roots.len()))
        .ok_or(FpAdapterError::Unsupported("clause envelope"))?;
    drop(seen);
    budget.charge(0)?;
    Ok(Plan {
        gates,
        clauses,
        occurrences: total.occurrences,
    })
}

fn circuit_gates(total: Counts) -> Result<usize, FpAdapterError> {
    validate_layout(total)?;
    let others = total
        .occurrences
        .checked_sub(total.arithmetic)
        .and_then(|v| v.checked_sub(total.divisions))
        .and_then(|v| v.checked_sub(total.remainders))
        .and_then(|v| v.checked_sub(total.truncating))
        .and_then(|v| v.checked_sub(total.square_roots))
        .and_then(|v| v.checked_sub(total.fused))
        .and_then(|v| v.checked_sub(total.numeric))
        .ok_or(FpAdapterError::Invalid("source recurrence"))?;
    checked_fees(total, others)
}

fn validate_layout(total: Counts) -> Result<(), FpAdapterError> {
    // The new transfer bound uses FULL enum/Arc payloads, not a Bool variant.
    // A different ABI refuses rather than silently borrowing a smaller price.
    if (total.square_roots != 0 || total.fused != 0 || total.truncating != 0 || total.numeric != 0)
        && (std::mem::size_of::<usize>() > 8
            || std::mem::size_of::<crate::ChcExpr>() > 128
            || std::mem::size_of::<crate::ChcVar>() > 64
            || std::mem::size_of::<ay_fp::FpDecomposed>() > 128
            || std::mem::size_of::<TermId>() > 8
            || std::mem::size_of::<ay_core::CnfClause>() > 32)
    {
        return Err(FpAdapterError::Unsupported(
            "rounded adapter layout envelope",
        ));
    }
    if total.numeric != 0 && std::mem::align_of::<crate::ChcExpr>() > 16 {
        return Err(FpAdapterError::Unsupported(
            "numeric adapter alignment envelope",
        ));
    }
    Ok(())
}

fn checked_fees(total: Counts, others: usize) -> Result<usize, FpAdapterError> {
    let gates = total
        .numeric
        .checked_mul(NUMERIC_GATES)
        .and_then(|v| {
            total
                .square_roots
                .checked_mul(SQUARE_ROOT_GATES)
                .and_then(|w| v.checked_add(w))
        })
        .and_then(|v| {
            total
                .fused
                .checked_mul(FUSED_GATES)
                .and_then(|w| v.checked_add(w))
        })
        .and_then(|v| {
            total
                .truncating
                .checked_mul(TRUNCATING_GATES)
                .and_then(|w| v.checked_add(w))
        })
        .and_then(|v| {
            total
                .remainders
                .checked_mul(REMAINDER_GATES)
                .and_then(|w| v.checked_add(w))
        })
        .and_then(|v| {
            total
                .divisions
                .checked_mul(DIVISION_GATES)
                .and_then(|w| v.checked_add(w))
        })
        .and_then(|v| {
            total
                .arithmetic
                .checked_mul(ARITHMETIC_GATES)
                .and_then(|w| v.checked_add(w))
        })
        .and_then(|v| {
            others
                .checked_mul(OTHER_GATES)
                .and_then(|w| v.checked_add(w))
        })
        .and_then(|v| v.checked_add(64))
        .filter(|&v| v <= MAX_GATES && v < i32::MAX as usize)
        .ok_or(FpAdapterError::Unsupported("complete circuit envelope"))?;
    Ok(gates)
}

fn validate_bindings(
    terms: &TermStore,
    bindings: &[FpInputBinding<'_>],
    budget: &mut WorkBudget<'_>,
) -> Result<(), FpAdapterError> {
    let mut ids = BTreeMap::new();
    let mut names = BTreeMap::new();
    for binding in bindings {
        // Bounded strings are compared in a logarithmic map, never hashed.
        budget.charge(8192)?;
        if terms.entry_stamp(binding.source).is_none() {
            return Err(FpAdapterError::Invalid("missing input"));
        }
        let TermData::Var(name, _) = terms.get(binding.source) else {
            return Err(FpAdapterError::Invalid(
                "input is not an original free variable",
            ));
        };
        if name.len() > MAX_NAME
            || name != &binding.target.name
            || !typed::binding_sort(terms.sort(binding.source), &binding.target.sort)
        {
            return Err(FpAdapterError::Invalid("input name/sort mismatch"));
        }
        if ids.insert(binding.source, ()).is_some()
            || names.insert(name.as_str(), binding.source).is_some()
        {
            return Err(FpAdapterError::Invalid("duplicate or aliased input"));
        }
    }
    Ok(())
}

fn visit(
    terms: &TermStore,
    id: TermId,
    bindings: &[FpInputBinding<'_>],
    seen: &mut BTreeMap<TermId, Visit>,
    depth: usize,
    budget: &mut WorkBudget<'_>,
) -> Result<Counts, FpAdapterError> {
    budget.charge(256)?;
    if depth >= MAX_DEPTH || terms.entry_stamp(id).is_none() {
        return Err(FpAdapterError::Invalid("source depth/missing child"));
    }
    match seen.get(&id) {
        Some(Visit::Active) => return Err(FpAdapterError::Invalid("source cycle")),
        Some(Visit::Done(counts)) => return Ok(*counts),
        None => {}
    }
    if seen.len() >= MAX_NODES {
        return Err(FpAdapterError::Unsupported("source node population"));
    }
    seen.insert(id, Visit::Active);
    let (children, cost) = typed::children(terms, id, bindings, budget)?;
    let mut counts = Counts {
        occurrences: 1,
        arithmetic: usize::from(matches!(cost, typed::CostClass::Arithmetic)),
        divisions: usize::from(matches!(cost, typed::CostClass::Division)),
        remainders: usize::from(matches!(cost, typed::CostClass::Remainder)),
        truncating: usize::from(matches!(cost, typed::CostClass::TruncatingRemainder)),
        square_roots: usize::from(matches!(cost, typed::CostClass::SquareRoot)),
        fused: usize::from(matches!(cost, typed::CostClass::Fused)),
        numeric: usize::from(matches!(cost, typed::CostClass::NumericConversion)),
        height: 1,
    };
    for child in children {
        let child = visit(terms, child, bindings, seen, depth + 1, budget)?;
        counts.occurrences = counts
            .occurrences
            .checked_add(child.occurrences)
            .filter(|&v| v <= MAX_OCCURRENCES)
            .ok_or(FpAdapterError::Unsupported("raw source occurrences"))?;
        counts.arithmetic = counts
            .arithmetic
            .checked_add(child.arithmetic)
            .ok_or(FpAdapterError::Unsupported("arithmetic occurrences"))?;
        counts.divisions = counts
            .divisions
            .checked_add(child.divisions)
            .ok_or(FpAdapterError::Unsupported("division occurrences"))?;
        counts.remainders = counts
            .remainders
            .checked_add(child.remainders)
            .ok_or(FpAdapterError::Unsupported("remainder occurrences"))?;
        counts.truncating = counts
            .truncating
            .checked_add(child.truncating)
            .ok_or(FpAdapterError::Unsupported("truncating occurrences"))?;
        counts.square_roots = counts
            .square_roots
            .checked_add(child.square_roots)
            .ok_or(FpAdapterError::Unsupported("square-root occurrences"))?;
        counts.fused = counts
            .fused
            .checked_add(child.fused)
            .ok_or(FpAdapterError::Unsupported("fused occurrences"))?;
        counts.numeric = counts
            .numeric
            .checked_add(child.numeric)
            .ok_or(FpAdapterError::Unsupported("numeric occurrences"))?;
        counts.height = counts.height.max(child.height + 1);
    }
    if counts.height > MAX_DEPTH {
        return Err(FpAdapterError::Unsupported("source height"));
    }
    seen.insert(id, Visit::Done(counts));
    Ok(counts)
}

fn combine(mut left: Counts, right: Counts) -> Result<Counts, FpAdapterError> {
    left.occurrences = left
        .occurrences
        .checked_add(right.occurrences)
        .filter(|&v| v <= MAX_OCCURRENCES)
        .ok_or(FpAdapterError::Unsupported("repeated root occurrences"))?;
    left.arithmetic = left
        .arithmetic
        .checked_add(right.arithmetic)
        .ok_or(FpAdapterError::Unsupported("arithmetic occurrences"))?;
    left.divisions = left
        .divisions
        .checked_add(right.divisions)
        .ok_or(FpAdapterError::Unsupported("division occurrences"))?;
    left.remainders = left
        .remainders
        .checked_add(right.remainders)
        .ok_or(FpAdapterError::Unsupported("remainder occurrences"))?;
    left.truncating = left
        .truncating
        .checked_add(right.truncating)
        .ok_or(FpAdapterError::Unsupported("truncating occurrences"))?;
    left.square_roots = left
        .square_roots
        .checked_add(right.square_roots)
        .ok_or(FpAdapterError::Unsupported("square-root occurrences"))?;
    left.fused = left
        .fused
        .checked_add(right.fused)
        .ok_or(FpAdapterError::Unsupported("fused occurrences"))?;
    left.numeric = left
        .numeric
        .checked_add(right.numeric)
        .ok_or(FpAdapterError::Unsupported("numeric occurrences"))?;
    left.height = left.height.max(right.height);
    Ok(left)
}

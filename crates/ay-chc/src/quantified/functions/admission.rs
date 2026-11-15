// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Allocation-free complete declaration admission before index construction.

use super::*;
use crate::quantified::source::{MAX_BYTES, MAX_DECLARATIONS, MAX_NODES};
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

#[derive(Default)]
pub(super) struct Cost {
    pub(super) work: usize,
    pub(super) bytes: usize,
}

impl Cost {
    fn charge(&mut self, work: usize, bytes: usize) -> ChcResult<()> {
        self.work = self
            .work
            .checked_add(work)
            .ok_or_else(|| invalid("work limit"))?;
        self.bytes = self
            .bytes
            .checked_add(bytes)
            .ok_or_else(|| invalid("copy limit"))?;
        if self.work > MAX_NODES || self.bytes > MAX_BYTES {
            return Err(invalid("source work/copy limit"));
        }
        Ok(())
    }

    fn name(&mut self, name: &str) -> ChcResult<()> {
        if name.is_empty()
            || name.len() > super::super::records::MAX_NAME_BYTES
            || super::super::source::theory_symbol(name)
            || crate::parser::is_builtin_term_symbol(name)
            || matches!(name, "!" | "match" | "par" | "lambda")
            || name
                .bytes()
                .any(|b| b.is_ascii_control() || matches!(b, b'|' | b'\\'))
        {
            return Err(invalid("invalid function or predicate name"));
        }
        // Covers source and index names, quoted rendering and tree-node space.
        self.charge(1 + name.len().div_ceil(64), 512 + name.len() * 8)
    }

    fn sort(&mut self, sort: &ChcSort) -> ChcResult<()> {
        if !scalar(sort) {
            return Err(invalid("expected scalar Bool or bounded BV argument"));
        }
        // This is the scalar case of records::sort_bytes, without invoking its
        // traversal scratch allocation before the borrowed preflight finishes.
        let bytes = 64
            + match sort {
                ChcSort::BitVec(width) if *width > 64 => {
                    usize::try_from(width.div_ceil(8)).map_err(|_| invalid("scalar width limit"))?
                }
                _ => 0,
            };
        // A retained signature, copied signature and rendering scratch all fit
        // this conservative bound, including wide limb-sized admission costs.
        self.charge(
            1 + bytes.div_ceil(64),
            bytes
                .checked_mul(4)
                .ok_or_else(|| invalid("sort copy limit"))?,
        )
    }
}

pub(super) fn scalar(sort: &ChcSort) -> bool {
    matches!(
        sort,
        ChcSort::Bool | ChcSort::BitVec(1..=crate::MAX_BITVECTOR_WIDTH)
    )
}

pub(super) fn check(
    declarations: &[QuantifiedChcFunction],
    problem: &ChcProblem,
    records: &Registry,
) -> ChcResult<Cost> {
    let count = declarations
        .len()
        .checked_add(problem.predicates().len())
        .ok_or_else(|| invalid("declaration count"))?;
    if count > MAX_DECLARATIONS {
        return Err(invalid("combined relation/function declaration count"));
    }
    let mut cost = Cost::default();
    cost.charge(
        declarations.len(),
        declarations
            .len()
            .checked_mul(2 * std::mem::size_of::<QuantifiedChcFunction>())
            .ok_or_else(|| invalid("declaration vector limit"))?,
    )?;
    for declaration in declarations {
        cost.name(&declaration.name)?;
        if records.lookup(&declaration.name).is_some()
            || records.contains_term_symbol(&declaration.name)
            || record_tester(records, &declaration.name, &mut cost)?
        {
            return Err(invalid("function shadows record declaration or operation"));
        }
        if !matches!(
            &declaration.result,
            ChcSort::BitVec(1..=crate::MAX_BITVECTOR_WIDTH)
        ) {
            return Err(invalid(
                "ordinary function result must be bounded BV, not Bool",
            ));
        }
        cost.sort(&declaration.result)?;
        // The length debit precedes iteration over any caller-sized signature.
        cost.charge(
            declaration.args.len(),
            declaration
                .args
                .len()
                .checked_mul(2 * std::mem::size_of::<ChcSort>())
                .ok_or_else(|| invalid("signature size"))?,
        )?;
        for sort in &declaration.args {
            cost.sort(sort)?;
        }
    }
    unique_names(declarations, problem, &mut cost)?;
    Ok(cost)
}

fn record_tester(records: &Registry, name: &str, cost: &mut Cost) -> ChcResult<bool> {
    let Some(tested) = name.strip_prefix("is-") else {
        return Ok(false);
    };
    for sort in records.record_sorts() {
        let ChcSort::Datatype { constructors, .. } = sort else {
            continue;
        };
        for constructor in constructors.iter() {
            cost.charge(1 + tested.len().min(constructor.name.len()).div_ceil(64), 0)?;
            if constructor.name == tested {
                return Ok(true);
            }
        }
    }
    Ok(false)
}

fn unique_names(
    declarations: &[QuantifiedChcFunction],
    problem: &ChcProblem,
    cost: &mut Cost,
) -> ChcResult<()> {
    // Fixed scratch is derived from the existing declaration cap, not a second
    // admission knob. Open addressing performs no allocation; every probe and
    // potential string comparison is charged, including adversarial collisions.
    let mut slots = [usize::MAX; 2 * MAX_DECLARATIONS];
    cost.charge(0, std::mem::size_of_val(&slots))?;
    let predicate_count = problem.predicates().len();
    let name_at = |index: usize| -> &str {
        if index < predicate_count {
            problem.predicates()[index].name.as_str()
        } else {
            declarations[index - predicate_count].name.as_str()
        }
    };
    for index in 0..predicate_count + declarations.len() {
        let name = name_at(index);
        if index < predicate_count {
            cost.name(name)?;
        }
        let mut hash = DefaultHasher::new();
        name.hash(&mut hash);
        let mut slot = hash.finish() as usize % slots.len();
        loop {
            cost.charge(1, 0)?;
            let previous = slots[slot];
            if previous == usize::MAX {
                slots[slot] = index;
                break;
            }
            let previous_name = name_at(previous);
            cost.charge(name.len().min(previous_name.len()).div_ceil(64), 0)?;
            if name == previous_name {
                return Err(invalid("duplicate or cross-family function/predicate name"));
            }
            slot = (slot + 1) % slots.len();
        }
    }
    Ok(())
}

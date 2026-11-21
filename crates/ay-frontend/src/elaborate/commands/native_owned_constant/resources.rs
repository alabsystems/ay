// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{Context, NativeOwnedConstantError as Error, PublicSort, Result};
use ay_core::{
    kani_compat::{hash_table_cost as table, DetHashMap as HashMap, DetHashSet as HashSet},
    Sort,
};
use std::mem::size_of;

pub(in crate::elaborate::commands) struct Gate<'a> {
    progress: &'a mut dyn FnMut(usize, usize, usize) -> bool,
    refused: bool,
}

impl<'a> Gate<'a> {
    pub(in crate::elaborate::commands) fn new(
        progress: &'a mut dyn FnMut(usize, usize, usize) -> bool,
    ) -> Self {
        Self {
            progress,
            refused: false,
        }
    }
    pub(in crate::elaborate::commands) fn pay(
        &mut self,
        work: usize,
        bytes: usize,
        depth: usize,
    ) -> Result<()> {
        if self.refused || work == usize::MAX || bytes == usize::MAX || depth > 128 {
            self.refused = true;
            return Err(Error::ResourceLimit);
        }
        self.refused = true;
        if !(self.progress)(work, bytes, depth) {
            return Err(Error::ResourceLimit);
        }
        self.refused = false;
        Ok(())
    }
}

pub(in crate::elaborate::commands) fn probe<T>(
    allocation: usize,
    len: usize,
    name: &str,
    gate: &mut Gate<'_>,
) -> Result<()> {
    let work =
        table::string_lookup::<T>(allocation, len, name.len()).ok_or(Error::ResourceLimit)?;
    gate.pay(work, 0, 0)
}

pub(in crate::elaborate::commands) fn probe_map<V>(
    map: &HashMap<String, V>,
    name: &str,
    gate: &mut Gate<'_>,
) -> Result<()> {
    probe::<(String, V)>(map.allocation_size(), map.len(), name, gate)
}

pub(in crate::elaborate::commands) fn probe_set(
    set: &HashSet<String>,
    name: &str,
    gate: &mut Gate<'_>,
) -> Result<()> {
    probe::<(String, ())>(set.allocation_size(), set.len(), name, gate)
}

pub(in crate::elaborate::commands) fn reserve_map<V>(
    map: &mut HashMap<String, V>,
    gate: &mut Gate<'_>,
) -> Result<()> {
    let cost = table::reserve_one::<(String, V)>(map.allocation_size(), map.len(), map.capacity())
        .ok_or(Error::ResourceLimit)?;
    gate.pay(cost.work, cost.storage_bytes, 0)?;
    if cost.rehashes {
        gate.pay(
            table::iteration::<(String, V)>(map.allocation_size(), map.len())
                .ok_or(Error::ResourceLimit)?,
            0,
            0,
        )?;
        for name in map.keys() {
            gate.pay(
                table::string_hash_payload(name.len()).ok_or(Error::ResourceLimit)?,
                0,
                0,
            )?;
        }
    }
    map.try_reserve(1).map_err(|_| Error::ResourceLimit)
}

pub(in crate::elaborate::commands) fn reserve_set(
    set: &mut HashSet<String>,
    gate: &mut Gate<'_>,
) -> Result<()> {
    let cost = table::reserve_one::<(String, ())>(set.allocation_size(), set.len(), set.capacity())
        .ok_or(Error::ResourceLimit)?;
    gate.pay(cost.work, cost.storage_bytes, 0)?;
    if cost.rehashes {
        gate.pay(
            table::iteration::<(String, ())>(set.allocation_size(), set.len())
                .ok_or(Error::ResourceLimit)?,
            0,
            0,
        )?;
        for name in set.iter() {
            gate.pay(
                table::string_hash_payload(name.len()).ok_or(Error::ResourceLimit)?,
                0,
                0,
            )?;
        }
    }
    set.try_reserve(1).map_err(|_| Error::ResourceLimit)
}

pub(in crate::elaborate::commands) fn admit_sort(
    context: &Context,
    sort: &Sort,
    gate: &mut Gate<'_>,
    depth: usize,
) -> Result<()> {
    gate.pay(1, size_of::<Sort>(), depth)?;
    match sort {
        Sort::Bool | Sort::Int | Sort::Real | Sort::String | Sort::RegLan | Sort::Char => {}
        Sort::BitVec(width) if width.width > 0 => {}
        Sort::FloatingPoint(e, s) if *e >= 2 && *s >= 2 => {}
        Sort::Uninterpreted(name) => {
            gate.pay(name.len().saturating_add(1), name.len(), depth)?;
            probe_map(&context.sort_defs, name, gate)?;
            // Actual current source ownership, including private incarnations;
            // an arbitrary same-spelled raw U never supplies a declaration.
            let owned = context
                .sort_defs
                .values()
                .any(|sort| matches!(sort, Sort::Uninterpreted(live) if live == name));
            probe_map(&context.datatypes, name, gate)?;
            probe_set(&context.live_datatype_carriers, name, gate)?;
            if !owned
                || (context.datatypes.contains_key(name)
                    && !context.live_datatype_carriers.contains(name))
            {
                return Err(Error::UnsupportedSort);
            }
        }
        Sort::Array(a) => {
            admit_sort(context, &a.index_sort, gate, depth + 1)?;
            admit_sort(context, &a.element_sort, gate, depth + 1)?;
        }
        Sort::Seq(e) => admit_sort(context, e, gate, depth + 1)?,
        _ => return Err(Error::UnsupportedSort),
    }
    Ok(())
}

pub(in crate::elaborate::commands) fn copy_text(text: &str, gate: &mut Gate<'_>) -> Result<String> {
    gate.pay(text.len().saturating_add(1), text.len(), 0)?;
    let mut result = String::new();
    result
        .try_reserve_exact(text.len())
        .map_err(|_| Error::ResourceLimit)?;
    result.push_str(text);
    Ok(result)
}

pub(in crate::elaborate::commands) fn copy_sort(
    sort: &Sort,
    gate: &mut Gate<'_>,
    depth: usize,
) -> Result<Sort> {
    gate.pay(1, size_of::<Sort>(), depth)?;
    Ok(match sort {
        Sort::Uninterpreted(name) => Sort::Uninterpreted(copy_text(name, gate)?),
        Sort::Array(a) => {
            gate.pay(1, size_of::<ay_core::ArraySort>(), depth)?;
            Sort::array(
                copy_sort(&a.index_sort, gate, depth + 1)?,
                copy_sort(&a.element_sort, gate, depth + 1)?,
            )
        }
        Sort::Seq(e) => Sort::seq(copy_sort(e, gate, depth + 1)?),
        Sort::Bool
        | Sort::Int
        | Sort::Real
        | Sort::String
        | Sort::RegLan
        | Sort::Char
        | Sort::BitVec(_)
        | Sort::FloatingPoint(..) => sort.clone(),
        _ => return Err(Error::UnsupportedSort),
    })
}

pub(in crate::elaborate::commands) fn copy_public_sort(
    sort: &Sort,
    gate: &mut Gate<'_>,
    depth: usize,
) -> Result<PublicSort> {
    gate.pay(1, size_of::<PublicSort>(), depth)?;
    Ok(match sort {
        Sort::Array(array) => PublicSort::Array(
            Box::new(copy_public_sort(&array.index_sort, gate, depth + 1)?),
            Box::new(copy_public_sort(&array.element_sort, gate, depth + 1)?),
        ),
        Sort::Seq(element) => {
            PublicSort::Seq(Box::new(copy_public_sort(element, gate, depth + 1)?))
        }
        _ => PublicSort::Core(copy_sort(sort, gate, depth)?),
    })
}

pub(in crate::elaborate::commands) fn admit_macro_invalidation(
    context: &Context,
    gate: &mut Gate<'_>,
) -> Result<()> {
    gate.pay(
        context
            .macro_expansion_memo
            .allocation_size()
            .saturating_add(context.macro_expansion_memo_names.allocation_size()),
        0,
        0,
    )?;
    for ((_, name, args), _) in &context.macro_expansion_memo {
        gate.pay(
            name.len().saturating_add(args.len()).saturating_add(1),
            0,
            0,
        )?;
    }
    for name in &context.macro_expansion_memo_names {
        gate.pay(name.len().saturating_add(1), 0, 0)?;
    }
    Ok(())
}

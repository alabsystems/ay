// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Declaration-order scalar leaf layouts. Repeated record-typed fields have
//! distinct ranges even when their immutable schema is shared.

use super::*;
use crate::quantified::records::{MAX_FLATTENED_LEAVES, MAX_RECORD_DEPTH};
use std::collections::BTreeMap;
use std::ops::Range;

#[derive(Debug)]
pub(super) struct Layout {
    pub(super) leaves: Vec<ChcSort>,
    pub(super) fields: Vec<Range<usize>>,
}

#[derive(Debug)]
pub(super) struct Layouts(BTreeMap<String, Layout>);

impl Layouts {
    pub(super) fn new(registry: &Registry, control: &SourceControl<'_>) -> Option<Self> {
        let mut out = BTreeMap::new();
        for sort in registry.record_sorts() {
            control.poll()?;
            let ChcSort::Datatype { name, constructors } = sort else {
                return None;
            };
            let [constructor] = constructors.as_slice() else {
                return None;
            };
            control.bytes(name.len())?;
            control.charge(constructor.selectors.len())?;
            let mut layout = Layout {
                leaves: Vec::new(),
                fields: Vec::new(),
            };
            layout
                .fields
                .try_reserve_exact(constructor.selectors.len())
                .ok()?;
            for field in &constructor.selectors {
                let start = layout.leaves.len();
                collect_leaves(&field.sort, &mut layout.leaves, control)?;
                layout.fields.push(start..layout.leaves.len());
            }
            if layout.leaves.is_empty() {
                return None;
            }
            out.insert(name.clone(), layout);
        }
        control.poll()?;
        Some(Self(out))
    }

    // Callers authenticated the complete nominal sort with the same registry.
    pub(super) fn get(&self, sort: &ChcSort) -> Option<&Layout> {
        let ChcSort::Datatype { name, .. } = sort else {
            return None;
        };
        self.0.get(name)
    }

    pub(super) fn leaves<'a>(&'a self, sort: &'a ChcSort) -> Option<&'a [ChcSort]> {
        if matches!(sort, ChcSort::Datatype { .. }) {
            Some(&self.get(sort)?.leaves)
        } else {
            Some(std::slice::from_ref(sort))
        }
    }
}

fn collect_leaves(
    sort: &ChcSort,
    out: &mut Vec<ChcSort>,
    control: &SourceControl<'_>,
) -> Option<()> {
    control.charge(1)?;
    let mut pending = vec![(sort, 0usize)];
    while let Some((sort, depth)) = pending.pop() {
        control.charge(1)?;
        if depth > MAX_RECORD_DEPTH {
            return None;
        }
        if let ChcSort::Datatype { constructors, .. } = sort {
            let [constructor] = constructors.as_slice() else {
                return None;
            };
            control.charge(constructor.selectors.len())?;
            pending.try_reserve(constructor.selectors.len()).ok()?;
            pending.extend(
                constructor
                    .selectors
                    .iter()
                    .rev()
                    .map(|field| (&field.sort, depth + 1)),
            );
        } else {
            if out.len() >= MAX_FLATTENED_LEAVES {
                return None;
            }
            control.bytes(sort_bytes(sort)?)?;
            out.try_reserve(1).ok()?;
            out.push(sort.clone());
        }
    }
    control.poll()
}

/// Selector prefixes stay shared, but every leaf path is emitted separately.
/// No product variable from the search is ever used in original replay.
pub(super) fn original_leaves(
    source: Arc<ChcExpr>,
    sort: &ChcSort,
    control: &SourceControl<'_>,
    out: &mut Vec<ChcExpr>,
    depth: usize,
) -> Option<()> {
    control.poll()?;
    if depth > MAX_RECORD_DEPTH {
        return None;
    }
    if let ChcSort::Datatype { constructors, .. } = sort {
        let [constructor] = constructors.as_slice() else {
            return None;
        };
        control.charge(constructor.selectors.len())?;
        for field in &constructor.selectors {
            control.bytes(field.name.len().checked_add(sort_bytes(&field.sort)?)?)?;
            let selector = Arc::new(ChcExpr::FuncApp(
                field.name.clone(),
                field.sort.clone(),
                vec![Arc::clone(&source)],
            ));
            original_leaves(selector, &field.sort, control, out, depth + 1)?;
        }
    } else {
        out.push(expression::copy_root(&source, control)?);
    }
    control.poll()
}

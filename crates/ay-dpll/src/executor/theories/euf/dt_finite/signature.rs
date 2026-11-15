// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The admitted datatype signature (part of the fragment gate, precondition
//! P1): the shape of every admitted sort and the constructor and selector
//! symbols that belong to it. See [`super::scan`] for the sort classes.

use ay_core::kani_compat::DetHashMap as HashMap;

use super::scan::{DtSort, FieldSort, SelKind, SortShape};
use crate::executor::Executor;

/// Mutable state of the gate walk.
#[derive(Default)]
pub(super) struct Signature {
    pub(super) sorts: Vec<DtSort>,
    pub(super) by_name: HashMap<String, Option<u32>>,
    pub(super) visiting: Vec<String>,
    pub(super) ctor_of: HashMap<String, (u32, usize)>,
    pub(super) sel_of: HashMap<String, SelKind>,
}

/// Decide the shape from the classified constructor fields.
pub(super) fn shape_of(
    ctors: &[String],
    fields: &[Vec<(bool, Option<FieldSort>)>],
    sig: &Signature,
) -> Option<SortShape> {
    let recursive: usize = fields.iter().flatten().filter(|(r, _)| *r).count();
    if recursive == 0 {
        if fields.iter().all(Vec::is_empty) {
            return Some(SortShape::Enum {
                ctors: ctors.to_vec(),
            });
        }
        if ctors.len() != 1 {
            return None; // sums with fields: outside M1
        }
        let fs = fields[0]
            .iter()
            .map(|(_, s)| *s)
            .collect::<Option<Vec<_>>>()?;
        return Some(SortShape::Record {
            ctor: ctors[0].clone(),
            fields: fs,
        });
    }
    // List: exactly one cons with exactly one recursive field + one nullary nil.
    if recursive != 1 || ctors.len() != 2 {
        return None;
    }
    let cons_idx = fields.iter().position(|r| r.iter().any(|(rec, _)| *rec))?;
    let nil_idx = 1 - cons_idx;
    if !fields[nil_idx].is_empty() {
        return None;
    }
    let rec_pos = fields[cons_idx].iter().position(|(rec, _)| *rec)?;
    let mut cell_fields = Vec::new();
    for (rec, fs) in &fields[cons_idx] {
        if *rec {
            continue;
        }
        match fs {
            Some(FieldSort::Dt(e))
                if matches!(sig.sorts[*e as usize].shape, SortShape::Enum { .. }) =>
            {
                cell_fields.push(*e)
            }
            _ => return None,
        }
    }
    Some(SortShape::List {
        cons: ctors[cons_idx].clone(),
        nil: ctors[nil_idx].clone(),
        cons_idx,
        rec_pos,
        cell_fields,
    })
}

/// Record the constructor and selector symbols of an admitted sort.
pub(super) fn register_members(sig: &mut Signature, id: u32, exec: &Executor) {
    let (ctors, cons) = match &sig.sorts[id as usize].shape {
        SortShape::Enum { ctors } => (ctors.clone(), None),
        SortShape::Record { ctor, .. } => (vec![ctor.clone()], None),
        SortShape::List { cons, nil, .. } => {
            let order: Vec<String> = exec
                .ctx
                .datatype_constructors(&sig.sorts[id as usize].name)
                .map(<[String]>::to_vec)
                .unwrap_or_default();
            debug_assert!(order.contains(cons) && order.contains(nil));
            (order, Some(cons.clone()))
        }
    };
    for (i, c) in ctors.iter().enumerate() {
        sig.ctor_of.insert(c.clone(), (id, i));
    }
    let Some(ctor) = cons.or_else(|| match &sig.sorts[id as usize].shape {
        SortShape::Record { ctor, .. } => Some(ctor.clone()),
        _ => None,
    }) else {
        return;
    };
    let is_list = matches!(sig.sorts[id as usize].shape, SortShape::List { .. });
    let info = exec
        .ctx
        .constructor_selector_info(&ctor)
        .unwrap_or(&[])
        .to_vec();
    let mut cell = 0usize;
    for (pos, (sel, s)) in info.iter().enumerate() {
        let recursive = exec.datatype_sort_name(s).as_deref() == Some(&sig.sorts[id as usize].name);
        let kind = match (is_list, recursive) {
            (true, true) => SelKind::ListRest { sort: id },
            (true, false) => {
                cell += 1;
                SelKind::ListField {
                    sort: id,
                    field: cell - 1,
                }
            }
            (false, _) => SelKind::RecordField { sort: id, pos },
        };
        sig.sel_of.insert(sel.clone(), kind);
    }
}

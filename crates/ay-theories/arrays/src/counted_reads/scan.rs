// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[derive(Clone, Copy)]
pub(super) enum ArrayKind {
    Free,
    Store {
        base: TermId,
        index: TermId,
        value: TermId,
    },
    Const {
        fill: TermId,
    },
    Ite {
        condition: TermId,
        then_array: TermId,
        else_array: TermId,
    },
}

#[derive(Clone, Copy)]
pub(super) struct ArrayShape {
    pub(super) index: ScalarSort,
    pub(super) element: ScalarSort,
    pub(super) kind: ArrayKind,
}

pub(super) struct Source {
    pub(super) primitives: provenance::Primitives,
    pub(super) shapes: Vec<Option<ArrayShape>>,
    pub(super) requests: Vec<(TermId, TermId)>,
    pub(super) unresolved: Vec<Unresolved>,
}

pub(super) fn source(
    terms: &TermStore,
    roots: &[TermId],
    owner: &CountedAdmission,
) -> Result<Source> {
    let mut out = Source {
        primitives: provenance::Primitives::default(),
        shapes: memory::filled(terms.len(), None, owner)?,
        requests: Vec::new(),
        unresolved: Vec::new(),
    };
    let mut states = memory::filled(terms.len(), 0u8, owner)?;
    let mut pending = Vec::new();
    for &root in roots {
        owner.admit(1, 0)?;
        if terms.entry_stamp(root).is_none() || terms.sort(root) != &Sort::Bool {
            return Err(Error::Invalid);
        }
        memory::push(&mut pending, (root, false), owner)?;
        while let Some((term, done)) = pending.pop() {
            owner.admit(1, 0)?;
            let state = states.get_mut(term.index()).ok_or(Error::Invalid)?;
            if done {
                classify(&mut out, terms, term, owner)?;
                *state = 2;
            } else if *state != 2 {
                if *state == 1 {
                    return Err(Error::Invalid);
                }
                *state = 1;
                memory::push(&mut pending, (term, true), owner)?;
                push_children(terms.get(term), &mut pending, owner)?;
            }
        }
    }
    drop(pending);
    drop(states);
    // No derived term may reinterpret a user-declared builtin lookalike.
    // This also checks identities needed only by later generated clauses.
    out.primitives.validate(terms, owner)?;
    owner.check()?;
    Ok(out)
}

fn push_children(
    node: &TermData,
    pending: &mut Vec<(TermId, bool)>,
    owner: &CountedAdmission,
) -> Result<()> {
    match node {
        TermData::App(_, args) => {
            for &child in args.iter().rev() {
                memory::push(pending, (child, false), owner)?;
            }
        }
        TermData::Not(child) => memory::push(pending, (*child, false), owner)?,
        TermData::Ite(c, t, e) => {
            for child in [*e, *t, *c] {
                memory::push(pending, (child, false), owner)?;
            }
        }
        TermData::Const(_) | TermData::Var(_, _) => {}
        _ => return Err(Error::Unsupported),
    }
    Ok(())
}

fn classify(
    out: &mut Source,
    terms: &TermStore,
    term: TermId,
    owner: &CountedAdmission,
) -> Result<()> {
    owner.admit(1, 0)?;
    if let TermData::App(name, _) = terms.get(term) {
        owner.admit(name.name().len(), 0)?;
        if !matches!(name, ay_core::Symbol::Named(_))
            && matches!(
                name.name(),
                "select" | "store" | "const-array" | "=" | "distinct"
            )
        {
            return Err(Error::Unsupported);
        }
    }
    if matches!(terms.sort(term), Sort::Array(_)) {
        let shape = array_shape(terms, term)?;
        match shape.kind {
            ArrayKind::Store { .. } => out.primitives.observe("store"),
            ArrayKind::Const { .. } => out.primitives.observe("const-array"),
            ArrayKind::Free | ArrayKind::Ite { .. } => {}
        }
        out.shapes[term.index()] = Some(shape);
    } else {
        scalar(terms.sort(term))?;
    }
    if let TermData::App(ay_core::Symbol::Named(name), args) = terms.get(term) {
        match (name.as_str(), args.as_slice()) {
            ("select", [array, index]) => {
                out.primitives.observe("select");
                let (key, value) = signature(terms.sort(*array))?;
                if scalar(terms.sort(*index))? != key || scalar(terms.sort(term))? != value {
                    return Err(Error::Invalid);
                }
                let shape = out.shapes[array.index()].ok_or(Error::Invalid)?;
                // Every non-free read emits an equality, even if no equality
                // occurs in the authored source (e.g. a Boolean const read).
                if !matches!(shape.kind, ArrayKind::Free)
                    || has_distinct_read(out, *array, *index, owner)?
                {
                    out.primitives.observe("=");
                }
                memory::push(&mut out.requests, (*array, *index), owner)?;
            }
            ("=" | "distinct", [left, right]) if matches!(terms.sort(*left), Sort::Array(_)) => {
                out.primitives.observe(name.as_str());
                if signature(terms.sort(*left))? != signature(terms.sort(*right))?
                    || terms.sort(term) != &Sort::Bool
                {
                    return Err(Error::Invalid);
                }
                memory::push(
                    &mut out.unresolved,
                    Unresolved::ArrayRelation {
                        source: term,
                        left: *left,
                        right: *right,
                    },
                    owner,
                )?;
            }
            ("select", _) => return Err(Error::Invalid),
            _ => {}
        }
    }
    Ok(())
}

fn has_distinct_read(
    out: &Source,
    array: TermId,
    index: TermId,
    owner: &CountedAdmission,
) -> Result<bool> {
    // A direct free/free pair also generates '='. Non-free reads already
    // record that dependency, including all recursively generated reads.
    for &(earlier_array, earlier_index) in &out.requests {
        owner.admit(1, 0)?;
        if earlier_array == array && earlier_index != index {
            return Ok(true);
        }
    }
    Ok(false)
}

fn array_shape(terms: &TermStore, term: TermId) -> Result<ArrayShape> {
    let (index, element) = signature(terms.sort(term))?;
    let kind = match terms.get(term) {
        TermData::Var(_, _) => ArrayKind::Free,
        TermData::App(ay_core::Symbol::Named(name), args) => match (name.as_str(), args.as_slice())
        {
            ("store", [base, at, value]) => {
                if signature(terms.sort(*base))? != (index, element)
                    || scalar(terms.sort(*at))? != index
                    || scalar(terms.sort(*value))? != element
                {
                    return Err(Error::Invalid);
                }
                ArrayKind::Store {
                    base: *base,
                    index: *at,
                    value: *value,
                }
            }
            ("const-array", [fill]) if scalar(terms.sort(*fill))? == element => {
                ArrayKind::Const { fill: *fill }
            }
            _ => return Err(Error::Unsupported),
        },
        TermData::Ite(condition, then_array, else_array) => {
            if terms.sort(*condition) != &Sort::Bool
                || signature(terms.sort(*then_array))? != (index, element)
                || signature(terms.sort(*else_array))? != (index, element)
            {
                return Err(Error::Invalid);
            }
            ArrayKind::Ite {
                condition: *condition,
                then_array: *then_array,
                else_array: *else_array,
            }
        }
        _ => return Err(Error::Unsupported),
    };
    Ok(ArrayShape {
        index,
        element,
        kind,
    })
}

fn signature(sort: &Sort) -> Result<(ScalarSort, ScalarSort)> {
    let Sort::Array(array) = sort else {
        return Err(Error::Invalid);
    };
    Ok((scalar(&array.index_sort)?, scalar(&array.element_sort)?))
}

fn scalar(sort: &Sort) -> Result<ScalarSort> {
    match sort {
        Sort::Bool => Ok(ScalarSort::Bool),
        Sort::BitVec(bits) if bits.width > 0 => Ok(ScalarSort::BitVec(bits.width)),
        _ => Err(Error::Unsupported),
    }
}

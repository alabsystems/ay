// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! One borrowed surface descriptor for source reconstruction and canonical
//! rendering. Rendering no longer clones a recursive ParsedSort tree first.

use super::{Context, Sort, SortSurfaceMode};
use crate::command::{Index, Sort as ParsedSort};
use crate::elaborate::NominalSortSurface;
use ay_core::render_admission::{self as output, Owner};

enum Shape<'a> {
    Name(&'a str),
    Indexed(&'static str, [u32; 2], usize),
    Array(&'a Sort, &'a Sort),
    Sequence(&'a Sort),
    Application(&'a str, &'a [Sort]),
}

fn inspect(surface: &NominalSortSurface, owner: Owner<'_>) -> bool {
    match surface {
        NominalSortSurface::Simple(name) => output::pay(owner, name.len().saturating_add(1), 0),
        NominalSortSurface::ParametricDatatype {
            display,
            template,
            arguments,
        } => {
            if !output::pay(
                owner,
                display
                    .len()
                    .saturating_add(template.len())
                    .saturating_add(arguments.len()),
                0,
            ) {
                return false;
            }
            for sort in arguments {
                let result =
                    ay_core::TermStore::inspect_sort_with_progress(sort, &mut |work, bytes| {
                        work.checked_add(bytes)
                            .is_some_and(|work| output::pay(owner, work, 0))
                    });
                if result.is_err() {
                    output::invalid(owner);
                    return false;
                }
            }
            true
        }
    }
}

fn ambiguous(ctx: &Context, identity: &str, owner: Owner<'_>) -> Option<bool> {
    if owner.is_none() {
        return Some(ctx.nominal_sort_surface_is_ambiguous(identity));
    }
    let Some(surface) = ctx.nominal_sort_surfaces.get(identity) else {
        return Some(false);
    };
    for (other, other_surface) in &ctx.nominal_sort_surfaces {
        if !output::pay(
            owner,
            identity.len().saturating_add(other.len()).saturating_add(1),
            0,
        ) {
            return None;
        }
        if other != identity {
            // Read-only preflight before the native recursive comparison;
            // the established snapshot safety walk makes no owned sort copy.
            if !inspect(surface, owner) || !inspect(other_surface, owner) {
                return None;
            }
            if other_surface == surface {
                return Some(true);
            }
        }
    }
    Some(false)
}

fn shape<'a>(
    ctx: &'a Context,
    sort: &'a Sort,
    mode: SortSurfaceMode,
    owner: Owner<'_>,
) -> Option<Shape<'a>> {
    if !output::pay(owner, 1, 0) {
        return None;
    }
    Some(match sort {
        Sort::Bool => Shape::Name("Bool"),
        Sort::Int => Shape::Name("Int"),
        Sort::Real => Shape::Name("Real"),
        Sort::Complex => Shape::Name("Complex"),
        Sort::String => Shape::Name("String"),
        Sort::RegLan => Shape::Name("RegLan"),
        Sort::Char => Shape::Name("Char"),
        Sort::FiniteField(field) => Shape::Indexed("FiniteField", [field.modulus(), 0], 1),
        Sort::BitVec(bits) => Shape::Indexed("BitVec", [bits.width, 0], 1),
        Sort::FloatingPoint(eb, sb) => Shape::Indexed("FloatingPoint", [*eb, *sb], 2),
        Sort::Array(array) => Shape::Array(&array.index_sort, &array.element_sort),
        Sort::Seq(element) => Shape::Sequence(element),
        Sort::Uninterpreted(identity) => {
            if matches!(mode, SortSurfaceMode::ExternalOutput) && ambiguous(ctx, identity, owner)? {
                Shape::Name(identity)
            } else {
                match ctx.nominal_sort_surfaces.get(identity) {
                    Some(NominalSortSurface::Simple(surface)) => Shape::Name(surface),
                    Some(NominalSortSurface::ParametricDatatype {
                        template,
                        arguments,
                        ..
                    }) => Shape::Application(template, arguments),
                    None => Shape::Name(identity),
                }
            }
        }
        Sort::Datatype(datatype) => Shape::Name(&datatype.name),
        Sort::FiniteDomain(name, _) | Sort::TypeVar(name) => Shape::Name(name),
        _ => {
            output::invalid(owner);
            return None;
        }
    })
}

pub(super) fn build(ctx: &Context, sort: &Sort, mode: SortSurfaceMode) -> Option<ParsedSort> {
    Some(match shape(ctx, sort, mode, None)? {
        Shape::Name(name) => ParsedSort::Simple(name.to_owned()),
        Shape::Indexed(name, indices, len) => ParsedSort::Indexed(
            name.to_owned(),
            indices[..len]
                .iter()
                .map(|n| Index::Numeral(n.to_string()))
                .collect(),
        ),
        Shape::Array(index, value) => ParsedSort::Parameterized(
            "Array".into(),
            vec![build(ctx, index, mode)?, build(ctx, value, mode)?],
        ),
        Shape::Sequence(element) => {
            ParsedSort::Parameterized("Seq".into(), vec![build(ctx, element, mode)?])
        }
        Shape::Application(name, arguments) => ParsedSort::Parameterized(
            name.to_owned(),
            arguments
                .iter()
                .map(|sort| build(ctx, sort, mode))
                .collect::<Option<Vec<_>>>()?,
        ),
    })
}

pub(super) fn format(ctx: &Context, sort: &Sort, owner: Owner<'_>) -> Option<String> {
    output::stacked(
        owner,
        || None,
        || {
            let (name, mut arguments) =
                match shape(ctx, sort, SortSurfaceMode::ExternalOutput, owner)? {
                    Shape::Name(name) => return Some(output::quote(owner, name)),
                    Shape::Indexed(name, indices, len) => {
                        let mut values = Vec::new();
                        if !output::reserve(&mut values, len, owner) {
                            return None;
                        }
                        for value in &indices[..len] {
                            values.push(output::format(owner, format_args!("{value}")));
                        }
                        let values = output::join(owner, &values, " ");
                        let name = output::quote(owner, name);
                        return Some(output::format(owner, format_args!("(_ {name} {values})")));
                    }
                    Shape::Array(index, value) => {
                        let mut values = Vec::new();
                        if !output::reserve(&mut values, 2, owner) {
                            return None;
                        }
                        values.push(format(ctx, index, owner)?);
                        values.push(format(ctx, value, owner)?);
                        ("Array", values)
                    }
                    Shape::Sequence(element) => {
                        let mut values = Vec::new();
                        if !output::reserve(&mut values, 1, owner) {
                            return None;
                        }
                        values.push(format(ctx, element, owner)?);
                        ("Seq", values)
                    }
                    Shape::Application(name, args) => {
                        let mut values = Vec::new();
                        if !output::reserve(&mut values, args.len(), owner) {
                            return None;
                        }
                        for arg in args {
                            values.push(format(ctx, arg, owner)?);
                        }
                        (name, values)
                    }
                };
            let name = output::quote(owner, name);
            let result = if arguments.is_empty() {
                output::format(owner, format_args!("({name})"))
            } else {
                let joined = output::join(owner, &arguments, " ");
                output::format(owner, format_args!("({name} {joined})"))
            };
            arguments.clear();
            if output::pay(owner, 0, 0) {
                Some(result)
            } else {
                None
            }
        },
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::original_query::{CountedAdmission, FiniteAdmissionGrant};
    use std::sync::Arc;
    fn owner(bytes: usize) -> CountedAdmission {
        CountedAdmission::new(
            FiniteAdmissionGrant::new(1_000_000, bytes),
            None,
            Arc::new(|| false),
        )
        .unwrap()
    }

    #[test]
    fn admitted_sort_surface_reelaborates_exact_nominal_and_nested_sorts() {
        let mut ctx = Context::new();
        for command in crate::parse("(declare-datatypes ((Box 1)) ((par (T) ((box (value T)))))) (declare-const boxed (Box (_ FiniteField 7)))").unwrap() {
            ctx.process_command(&command).unwrap();
        }
        let declaration = crate::parse("(declare-const witness (Box (_ FiniteField 7)))").unwrap();
        let crate::command::Command::DeclareConst(_, surface) = &declaration[0] else {
            panic!("declaration")
        };
        let nominal = ctx.elaborate_sort(surface).unwrap();
        let sorts = [
            nominal,
            Sort::array(
                Sort::Bool,
                Sort::seq(Sort::FiniteField(ay_core::FiniteFieldSort::new(7).unwrap())),
            ),
        ];
        let admission = owner(1 << 20);
        for sort in sorts {
            let text = ctx.format_sort_surface_admitted(&sort, &admission).unwrap();
            let parsed = crate::parse(&format!("(declare-const result {text})")).unwrap();
            let crate::command::Command::DeclareConst(_, surface) = &parsed[0] else {
                panic!("declaration")
            };
            assert_eq!(ctx.elaborate_sort(surface).unwrap(), sort);
        }
        let tiny = owner(1);
        assert!(ctx
            .format_sort_surface_admitted(&Sort::Bool, &tiny)
            .is_none());
        assert!(ctx
            .format_sort_surface_admitted(&Sort::Bool, &tiny)
            .is_none());
    }
}

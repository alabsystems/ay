// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Shape {
    Flat,
    Composite,
    Wide,
}

/// Only predicate state controls this routing. Unused datatype/function
/// declarations must not divert an otherwise unchanged legacy source.
pub(super) fn source(problem: &QuantifiedChcProblem, control: &SourceControl<'_>) -> Option<Shape> {
    let mut composite = false;
    let mut array = false;
    let mut wide = false;
    for predicate in problem.source_problem().predicates() {
        control.charge(predicate.arg_sorts.len())?;
        for sort in &predicate.arg_sorts {
            let mut pending = vec![sort];
            while let Some(sort) = pending.pop() {
                control.charge(1)?;
                match sort {
                    ChcSort::BitVec(width) => wide |= *width > 64,
                    ChcSort::Array(key, value) => {
                        array = true;
                        composite |= matches!(
                            value.as_ref(),
                            ChcSort::Array(..) | ChcSort::Datatype { .. }
                        );
                        control.charge(2)?;
                        pending.try_reserve(2).ok()?;
                        pending.extend([key.as_ref(), value.as_ref()]);
                    }
                    ChcSort::Datatype { constructors, .. } => {
                        for constructor in constructors.iter() {
                            control.charge(constructor.selectors.len())?;
                            pending.try_reserve(constructor.selectors.len()).ok()?;
                            pending.extend(constructor.selectors.iter().map(|field| &field.sort));
                        }
                    }
                    _ => {}
                }
            }
        }
    }
    control.poll()?;
    Some(if array && wide {
        Shape::Wide
    } else if composite {
        Shape::Composite
    } else {
        Shape::Flat
    })
}

#[cfg(test)]
mod tests;

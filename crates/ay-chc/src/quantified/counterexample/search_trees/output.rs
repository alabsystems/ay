// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Iterative body-order postorder; neither traversal nor teardown follows a
//! recursively owned Rust tree. Only complete original occurrences are copied.

use super::*;
use cursor::Occurrence;

pub(super) fn postorder(nodes: &[Occurrence], control: &SourceControl<'_>) -> Option<Derivation> {
    if nodes.is_empty() {
        return None;
    }
    control.charge(nodes.len())?;
    control.bytes(nodes.len().checked_mul(
        3 * std::mem::size_of::<usize>()
            + std::mem::size_of::<Option<usize>>()
            + std::mem::size_of::<Vec<usize>>(),
    )?)?;
    let mut stack = Vec::new();
    stack.try_reserve_exact(nodes.len()).ok()?;
    stack.push((0usize, 0usize));
    let mut mapped = Vec::new();
    mapped.try_reserve_exact(nodes.len()).ok()?;
    for _ in nodes {
        control.charge(1)?;
        mapped.push(None);
    }
    let mut result = Derivation {
        clause_indices: Vec::new(),
        premise_steps: Vec::new(),
    };
    result.clause_indices.try_reserve_exact(nodes.len()).ok()?;
    result.premise_steps.try_reserve_exact(nodes.len()).ok()?;
    while let Some((node, next)) = stack.last_mut() {
        control.charge(1)?;
        let occurrence = nodes.get(*node)?;
        if let Some(child) = occurrence.children.get(*next) {
            let child = (*child)?;
            if child <= *node || child >= nodes.len() || mapped[child].is_some() {
                return None;
            }
            *next = next.checked_add(1)?;
            stack.push((child, 0));
            continue;
        }
        let node = *node;
        control.bytes(
            occurrence
                .children
                .len()
                .checked_mul(std::mem::size_of::<usize>())?,
        )?;
        let mut premises = Vec::new();
        premises.try_reserve_exact(occurrence.children.len()).ok()?;
        for child in &occurrence.children {
            control.charge(1)?;
            premises.push(mapped[(*child)?]?);
        }
        mapped[node] = Some(result.clause_indices.len());
        result.clause_indices.push(occurrence.clause);
        result.premise_steps.push(premises);
        stack.pop();
    }
    if result.clause_indices.len() != nodes.len() {
        return None;
    }
    drop((stack, mapped));
    control.poll()?;
    Some(result)
}

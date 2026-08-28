// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Resource accounting and iterative rendering bounds for authored bridges.

use super::{
    AlethePrintError, AuthoredAssumeAccounting, AuthoredAssumePlan, MAX_AUTHORED_ASSUME_BRIDGES,
    MAX_CANONICAL_RENDER_NODES, MAX_EQUIVALENCE_BYTES, MAX_EQUIVALENCE_DEPTH,
    MAX_EQUIVALENCE_TOTAL_INPUT_BYTES, MAX_EQUIVALENCE_TOTAL_NODES,
    MAX_EQUIVALENCE_TOTAL_OUTPUT_BYTES,
};
use ay_core::{Constant, ProofId, Symbol, TermData, TermId, TermStore};

pub(super) fn invalid_authored_assume_plan(id: ProofId, reason: &str) -> AlethePrintError {
    AlethePrintError::InvalidSurfaceStep {
        id,
        reason: reason.to_string(),
    }
}

pub(super) fn account_authored_assume_planning_input(
    id: ProofId,
    input_bytes: usize,
    accounting: &mut AuthoredAssumeAccounting,
) -> Result<(), AlethePrintError> {
    let Some(next_input_bytes) = accounting.total_input_bytes.checked_add(input_bytes) else {
        return Err(invalid_authored_assume_plan(
            id,
            "authored assume bridge aggregate input size overflowed",
        ));
    };
    if next_input_bytes > MAX_EQUIVALENCE_TOTAL_INPUT_BYTES {
        return Err(invalid_authored_assume_plan(
            id,
            "authored assume bridges exceed the aggregate input-size bound",
        ));
    }
    accounting.total_input_bytes = next_input_bytes;
    Ok(())
}

fn add_canonical_payload(bytes: &mut usize, amount: usize) -> bool {
    let Some(next) = bytes.checked_add(amount) else {
        return false;
    };
    if next > MAX_EQUIVALENCE_BYTES {
        return false;
    }
    *bytes = next;
    true
}

fn add_canonical_text_payload(bytes: &mut usize, text: &str) -> bool {
    // Quoted SMT symbols and strings add delimiters and can duplicate an
    // escaping character. Four times the UTF-8 payload plus the per-node base
    // charge is a conservative allocation bound.
    text.len()
        .checked_mul(4)
        .is_some_and(|amount| add_canonical_payload(bytes, amount))
}

fn canonical_constant_payload_is_bounded(constant: &Constant, bytes: &mut usize) -> bool {
    let payload = match constant {
        Constant::Bool(_) => 5,
        Constant::Int(value) => match usize::try_from(value.bits()) {
            Ok(bits) => bits.saturating_add(4),
            Err(_) => return false,
        },
        Constant::Rational(value) => {
            let bits = value.0.numer().bits().checked_add(value.0.denom().bits());
            match bits.and_then(|bits| usize::try_from(bits).ok()) {
                Some(bits) => bits.saturating_add(16),
                None => return false,
            }
        }
        Constant::BitVec { value, width } => {
            let rendered_bits = value.bits().max(u64::from(*width));
            match usize::try_from(rendered_bits) {
                Ok(bits) => bits.saturating_add(2),
                Err(_) => return false,
            }
        }
        Constant::String(value) => return add_canonical_text_payload(bytes, value),
        _ => return false,
    };
    add_canonical_payload(bytes, payload)
}

fn canonical_symbol_payload_is_bounded(symbol: &Symbol, bytes: &mut usize) -> bool {
    match symbol {
        // Constant-array rendering recursively formats a sort as well as its
        // child. This narrow arithmetic lane does not admit that unmetered tree.
        Symbol::Named(name) if name == "const-array" => false,
        Symbol::Named(name) => add_canonical_text_payload(bytes, name),
        Symbol::Indexed(name, indices) => {
            add_canonical_text_payload(bytes, name)
                && indices
                    .len()
                    .checked_mul(12)
                    .is_some_and(|amount| add_canonical_payload(bytes, amount))
        }
        _ => false,
    }
}

/// Bound the fully expanded canonical tree before calling the recursive term
/// renderer. Deliberately visits repeated DAG children repeatedly: formatting
/// copies a child's bytes at every occurrence, so unique-node counting would
/// understate both output and stack work on a highly shared term.
pub(super) fn canonical_term_is_bounded_for_authored_assume(
    terms: &TermStore,
    root: TermId,
) -> bool {
    let mut stack = vec![(root, 0usize)];
    let mut nodes = 0usize;
    let mut bytes = 0usize;
    while let Some((term, depth)) = stack.pop() {
        if depth > MAX_EQUIVALENCE_DEPTH {
            return false;
        }
        let Some(next_nodes) = nodes.checked_add(1) else {
            return false;
        };
        if next_nodes > MAX_CANONICAL_RENDER_NODES || !add_canonical_payload(&mut bytes, 32) {
            return false;
        }
        nodes = next_nodes;
        let next_depth = match depth.checked_add(1) {
            Some(next) => next,
            None => return false,
        };
        let mut push_children = |children: &[TermId]| {
            if nodes
                .checked_add(stack.len())
                .and_then(|scheduled| scheduled.checked_add(children.len()))
                .is_none_or(|scheduled| scheduled > MAX_CANONICAL_RENDER_NODES)
            {
                return false;
            }
            stack.extend(children.iter().rev().map(|&child| (child, next_depth)));
            true
        };
        match terms.get(term) {
            TermData::Var(name, _) => {
                if !add_canonical_text_payload(&mut bytes, name) {
                    return false;
                }
            }
            TermData::Const(constant) => {
                if !canonical_constant_payload_is_bounded(constant, &mut bytes) {
                    return false;
                }
            }
            TermData::App(symbol, arguments) => {
                if !canonical_symbol_payload_is_bounded(symbol, &mut bytes)
                    || !push_children(arguments)
                {
                    return false;
                }
            }
            TermData::Not(inner) => {
                if !push_children(std::slice::from_ref(inner)) {
                    return false;
                }
            }
            TermData::Ite(condition, then_branch, else_branch) => {
                if !push_children(&[*condition, *then_branch, *else_branch]) {
                    return false;
                }
            }
            // The supported bridge schemas are quantifier-free applications.
            // Reject binders/lets before their variable/sort payloads can be
            // recursively formatted outside this preflight.
            TermData::Let(..) | TermData::Forall(..) | TermData::Exists(..) => return false,
            _ => return false,
        }
    }
    true
}

pub(super) fn account_authored_assume_emission(
    id: ProofId,
    plan: &AuthoredAssumePlan,
    nodes: usize,
    output_bytes: usize,
    accounting: &mut AuthoredAssumeAccounting,
) -> Result<(), AlethePrintError> {
    let Some(next_bridge_count) = accounting.bridge_count.checked_add(1) else {
        return Err(invalid_authored_assume_plan(
            id,
            "authored assume bridge count overflowed",
        ));
    };
    if next_bridge_count > MAX_AUTHORED_ASSUME_BRIDGES {
        return Err(invalid_authored_assume_plan(
            id,
            "authored assume bridge count exceeds the planner bound",
        ));
    }
    let Some(next_input_bytes) = accounting.total_input_bytes.checked_add(plan.input_bytes) else {
        return Err(invalid_authored_assume_plan(
            id,
            "authored assume bridge aggregate input size overflowed",
        ));
    };
    if next_input_bytes > MAX_EQUIVALENCE_TOTAL_INPUT_BYTES {
        return Err(invalid_authored_assume_plan(
            id,
            "authored assume bridges exceed the aggregate input-size bound",
        ));
    }
    let Some(next_nodes) = accounting.total_nodes.checked_add(nodes) else {
        return Err(invalid_authored_assume_plan(
            id,
            "authored assume bridge node accounting overflowed",
        ));
    };
    if next_nodes > MAX_EQUIVALENCE_TOTAL_NODES {
        return Err(invalid_authored_assume_plan(
            id,
            "authored assume bridges exceed the aggregate node bound",
        ));
    }
    let Some(next_output_bytes) = accounting.total_output_bytes.checked_add(output_bytes) else {
        return Err(invalid_authored_assume_plan(
            id,
            "authored assume bridge aggregate output size overflowed",
        ));
    };
    if next_output_bytes > MAX_EQUIVALENCE_TOTAL_OUTPUT_BYTES {
        return Err(invalid_authored_assume_plan(
            id,
            "authored assume bridges exceed the aggregate output-size bound",
        ));
    }
    accounting.bridge_count = next_bridge_count;
    accounting.total_input_bytes = next_input_bytes;
    accounting.total_nodes = next_nodes;
    accounting.total_output_bytes = next_output_bytes;
    Ok(())
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::kani_compat::DetHashMap;
use compact::{Arena, CompactStep, ValueId, ValueNode};
use num_bigint::BigUint;

pub(super) fn derivation(
    envelope: &wire::Envelope,
    owner: &mut Owner<'_>,
) -> Result<CompactDerivation> {
    let mut arena = Arena::new();
    for (index, node) in envelope.nodes.iter().enumerate() {
        let node = decode_node(node, index, owner)?;
        let id = arena.intern(&node, owner).map_err(native_error)?;
        if usize::try_from(id.0).ok() != Some(index) {
            return Err(error(
                Reason::NonCanonicalEnvelope,
                "duplicate compact value node",
            ));
        }
    }
    let mut steps = Vec::new();
    if steps.try_reserve_exact(envelope.steps.len()).is_err() {
        return refused(owner);
    }
    for (index, step) in envelope.steps.iter().enumerate() {
        admit(
            owner,
            step.bindings.len(),
            step.bindings
                .len()
                .checked_mul(128)
                .ok_or_else(|| error(Reason::CountMismatch, "binding size overflow"))?,
        )?;
        if step.premises.iter().any(|premise| *premise >= index) {
            return Err(error(
                Reason::IndexOutOfRange,
                "compact premise must precede its consumer",
            ));
        }
        let mut env = DetHashMap::default();
        if env.try_reserve(step.bindings.len()).is_err() {
            return refused(owner);
        }
        let mut previous: Option<&str> = None;
        for binding in &step.bindings {
            admit(owner, binding.name.len(), binding.name.len())?;
            if binding.name.contains('\0')
                || previous.is_some_and(|name| name >= binding.name.as_str())
            {
                return Err(error(
                    Reason::BindingSetMismatch,
                    "compact bindings must be ordered unique source names",
                ));
            }
            let id = ValueId(binding.value);
            if arena.get(id).is_none() {
                return Err(error(
                    Reason::IndexOutOfRange,
                    "compact binding value does not exist",
                ));
            }
            previous = Some(&binding.name);
            env.insert(binding.name.clone(), id);
        }
        steps.push(CompactStep {
            clause_index: step.clause_index,
            env,
            premises: step.premises.clone(),
        });
    }
    owner.poll().map_err(native_error)?;
    Ok(CompactDerivation {
        arena,
        steps,
        query_step: envelope.query_step,
    })
}

fn decode_node(node: &wire::Node, index: usize, owner: &mut Owner<'_>) -> Result<ValueNode> {
    Ok(match node {
        wire::Node::Bool { value } => {
            admit(owner, 1, 128)?;
            ValueNode::Bool(*value)
        }
        wire::Node::Bitvector { width, value_hex } => {
            let max_digits = u64::from(*width).div_ceil(4);
            if !(1..=crate::MAX_BITVECTOR_WIDTH).contains(width)
                || value_hex.is_empty()
                || value_hex.len() as u64 > max_digits
                || (value_hex.len() > 1 && value_hex.starts_with('0'))
            {
                return Err(error(
                    Reason::InvalidValue,
                    "noncanonical compact bitvector",
                ));
            }
            admit(
                owner,
                value_hex.len(),
                value_hex
                    .len()
                    .checked_mul(8)
                    .ok_or_else(|| error(Reason::InvalidValue, "numeric size overflow"))?,
            )?;
            if !value_hex
                .bytes()
                .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
            {
                return Err(error(
                    Reason::InvalidValue,
                    "compact bitvector must use lower-case hexadecimal",
                ));
            }
            let value = BigUint::parse_bytes(value_hex.as_bytes(), 16)
                .ok_or_else(|| error(Reason::InvalidValue, "invalid compact bitvector"))?;
            if value.bits() > u64::from(*width) {
                return Err(error(
                    Reason::InvalidValue,
                    "compact bitvector exceeds declared width",
                ));
            }
            ValueNode::BitVec {
                value,
                width: *width,
            }
        }
        wire::Node::Datatype {
            sort,
            constructor,
            fields,
        } => {
            let Some(size) = sort
                .len()
                .checked_add(constructor.len())
                .and_then(|n| fields.len().checked_mul(4).and_then(|m| n.checked_add(m)))
            else {
                return refused(owner);
            };
            admit(owner, size, size)?;
            if fields
                .iter()
                .any(|child| usize::try_from(*child).map_or(true, |id| id >= index))
            {
                return Err(error(
                    Reason::IndexOutOfRange,
                    "compact children must precede their parent",
                ));
            }
            ValueNode::Datatype {
                sort: sort.clone(),
                constructor: constructor.clone(),
                fields: fields.iter().copied().map(ValueId).collect(),
            }
        }
    })
}

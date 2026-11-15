// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use compact::ValueNode;
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct Envelope {
    schema: String,
    schema_version: u32,
    role: String,
    pub(super) normalized_input_schema: String,
    pub(super) normalized_input_sha256: String,
    pub(super) source_clause_sequence_sha256: String,
    pub(super) value_node_count: usize,
    pub(super) step_count: usize,
    pub(super) binding_count: usize,
    pub(super) premise_edge_count: usize,
    pub(super) query_step: usize,
    pub(super) nodes: Vec<Node>,
    pub(super) steps: Vec<Step>,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub(super) enum Node {
    Bool {
        value: bool,
    },
    Bitvector {
        width: u32,
        value_hex: String,
    },
    Datatype {
        sort: String,
        constructor: String,
        fields: Vec<u32>,
    },
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct Step {
    pub(super) clause_index: usize,
    pub(super) premises: Vec<usize>,
    pub(super) bindings: Vec<Binding>,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct Binding {
    pub(super) name: String,
    pub(super) value: u32,
}

impl Envelope {
    pub(super) fn check_header(&self, owner: &mut Owner) -> Result<()> {
        owner.poll().map_err(native_error)?;
        if self.schema != CHC_COMPACT_GROUND_DERIVATION_SCHEMA || self.schema_version != 1 {
            return Err(error(
                Reason::SchemaMismatch,
                "unsupported compact evidence schema",
            ));
        }
        if self.role != CHC_COMPACT_GROUND_DERIVATION_ROLE {
            return Err(error(
                Reason::RoleMismatch,
                "incorrect compact evidence role",
            ));
        }
        let (bindings, edges) = counts(&self.steps, owner)?;
        if self.value_node_count != self.nodes.len()
            || self.step_count != self.steps.len()
            || bindings != self.binding_count
            || edges != self.premise_edge_count
        {
            return Err(error(
                Reason::CountMismatch,
                "compact envelope counts disagree",
            ));
        }
        use crate::ground_derivation::artifact::*;
        if self.nodes.len() > CHC_GROUND_DERIVATION_ARTIFACT_MAX_VALUE_NODES
            || self.steps.len() > CHC_GROUND_DERIVATION_ARTIFACT_MAX_STEPS
            || self.binding_count > CHC_GROUND_DERIVATION_ARTIFACT_MAX_BINDINGS
            || self.premise_edge_count > CHC_GROUND_DERIVATION_ARTIFACT_MAX_PREMISE_EDGES
        {
            return Err(error(
                Reason::ArtifactTooLarge,
                "compact envelope exceeds structural bounds",
            ));
        }
        Ok(())
    }

    pub(super) fn from_derivation(
        derivation: &CompactDerivation,
        identity: (&'static str, String, String),
        owner: &mut Owner,
    ) -> Result<Self> {
        let Some(storage) = derivation
            .arena
            .nodes()
            .len()
            .checked_mul(512)
            .and_then(|n| {
                derivation
                    .steps
                    .len()
                    .checked_mul(512)
                    .and_then(|s| n.checked_add(s))
            })
        else {
            return refused(owner);
        };
        admit(owner, derivation.arena.nodes().len(), storage)?;
        let mut nodes = Vec::new();
        if nodes
            .try_reserve_exact(derivation.arena.nodes().len())
            .is_err()
        {
            return refused(owner);
        }
        for node in derivation.arena.nodes() {
            nodes.push(encode_node(node, owner)?);
        }
        let mut steps = Vec::new();
        if steps.try_reserve_exact(derivation.steps.len()).is_err() {
            return refused(owner);
        }
        for step in &derivation.steps {
            steps.push(encode_step(step, owner)?);
        }
        let (binding_count, premise_edge_count) = counts(&steps, owner)?;
        let envelope = Self {
            schema: CHC_COMPACT_GROUND_DERIVATION_SCHEMA.into(),
            schema_version: 1,
            role: CHC_COMPACT_GROUND_DERIVATION_ROLE.into(),
            normalized_input_schema: identity.0.into(),
            normalized_input_sha256: identity.1,
            source_clause_sequence_sha256: identity.2,
            value_node_count: nodes.len(),
            step_count: steps.len(),
            binding_count,
            premise_edge_count,
            query_step: derivation.query_step,
            nodes,
            steps,
        };
        envelope.check_header(owner)?;
        Ok(envelope)
    }
}

fn counts(steps: &[Step], owner: &mut Owner) -> Result<(usize, usize)> {
    let (mut bindings, mut edges) = (0usize, 0usize);
    for step in steps {
        admit(owner, 1, 0)?;
        let Some(next_bindings) = bindings.checked_add(step.bindings.len()) else {
            return refused(owner);
        };
        let Some(next_edges) = edges.checked_add(step.premises.len()) else {
            return refused(owner);
        };
        bindings = next_bindings;
        edges = next_edges;
    }
    Ok((bindings, edges))
}

fn encode_node(node: &ValueNode, owner: &mut Owner) -> Result<Node> {
    Ok(match node {
        ValueNode::Bool(value) => {
            admit(owner, 1, 128)?;
            Node::Bool { value: *value }
        }
        ValueNode::BitVec { value, width } => {
            let digits = usize::try_from(value.bits().div_ceil(4).max(1))
                .map_err(|_| error(Reason::InvalidValue, "bitvector size overflow"))?;
            let Some(storage) = digits.checked_mul(8) else {
                return refused(owner);
            };
            admit(owner, digits, storage)?;
            Node::Bitvector {
                width: *width,
                value_hex: value.to_str_radix(16),
            }
        }
        ValueNode::Datatype {
            sort,
            constructor,
            fields,
        } => {
            let Some(size) = sort
                .len()
                .checked_add(constructor.len())
                .and_then(|n| fields.len().checked_mul(16).and_then(|m| n.checked_add(m)))
            else {
                return refused(owner);
            };
            let Some(storage) = size.checked_mul(16) else {
                return refused(owner);
            };
            admit(owner, size, storage)?;
            Node::Datatype {
                sort: sort.clone(),
                constructor: constructor.clone(),
                fields: fields.iter().map(|id| id.0).collect(),
            }
        }
    })
}

fn encode_step(step: &compact::CompactStep, owner: &mut Owner) -> Result<Step> {
    let Some(storage) = step.env.len().checked_mul(512).and_then(|n| {
        step.premises
            .len()
            .checked_mul(64)
            .and_then(|m| n.checked_add(m))
    }) else {
        return refused(owner);
    };
    let Some(work) = step.env.len().checked_add(step.premises.len()) else {
        return refused(owner);
    };
    admit(owner, work, storage)?;
    let rounds = usize::BITS as usize - step.env.len().leading_zeros() as usize + 1;
    for name in step.env.keys() {
        let Some(work) = name.len().checked_mul(rounds) else {
            return refused(owner);
        };
        let Some(bytes) = name.len().checked_mul(16) else {
            return refused(owner);
        };
        admit(owner, work, bytes)?;
    }
    let mut bindings: Vec<_> = step
        .env
        .iter()
        .map(|(name, id)| Binding {
            name: name.clone(),
            value: id.0,
        })
        .collect();
    bindings.sort_by(|a, b| a.name.cmp(&b.name));
    Ok(Step {
        clause_index: step.clause_index,
        premises: step.premises.clone(),
        bindings,
    })
}

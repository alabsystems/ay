// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Borrowed DAG playback. Child IDs preserve sharing; no accessor expands a tree.

use super::*;
use compact::{CompactStep, ValueId, ValueNode};
use num_bigint::BigUint;

/// An opaque index scoped to one validated compact snapshot, never global authority.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ChcCompactValueId(u32);

impl ChcCompactValueId {
    /// Stable index within this snapshot's topological node sequence.
    pub fn index(self) -> u32 {
        self.0
    }
}

/// A value borrowed from validated evidence. All constructor fields are present.
pub struct ChcCompactValueView<'a> {
    node: &'a ValueNode,
}

impl<'a> ChcCompactValueView<'a> {
    /// A concrete Boolean leaf, if this is one.
    pub fn boolean(&self) -> Option<bool> {
        match self.node {
            ValueNode::Bool(value) => Some(*value),
            _ => None,
        }
    }
    /// Borrow the exact canonical nonnegative bit pattern and its declared width.
    pub fn bitvector(&self) -> Option<(&'a BigUint, u32)> {
        match self.node {
            ValueNode::BitVec { value, width } => Some((value, *width)),
            _ => None,
        }
    }
    /// Original nominal sort and constructor, if this is a datatype node.
    pub fn datatype(&self) -> Option<(&'a str, &'a str)> {
        match self.node {
            ValueNode::Datatype {
                sort, constructor, ..
            } => Some((sort, constructor)),
            _ => None,
        }
    }
    /// Every child in original selector order; repeated IDs remain repeated.
    pub fn fields(&self) -> impl ExactSizeIterator<Item = ChcCompactValueId> + 'a {
        let fields: &'a [ValueId] = match self.node {
            ValueNode::Datatype { fields, .. } => fields,
            _ => &[],
        };
        fields.iter().map(|id| ChcCompactValueId(id.0))
    }
}

/// Borrowed original clause instance; no constructor, mutation or deserialization.
pub struct ChcCompactGroundStepView<'a> {
    step: &'a CompactStep,
}

impl<'a> ChcCompactGroundStepView<'a> {
    /// Index in the authenticated ORIGINAL ordered clause sequence.
    pub fn clause_index(&self) -> usize {
        self.step.clause_index
    }
    /// Premise step indices in original body-predicate order.
    pub fn premises(&self) -> &'a [usize] {
        &self.step.premises
    }
    /// One original source variable's value root.
    pub fn binding(&self, name: &str) -> Option<ChcCompactValueId> {
        self.step.env.get(name).map(|id| ChcCompactValueId(id.0))
    }
    /// All validated original source bindings, without cloning or tree expansion.
    pub fn bindings(&self) -> impl Iterator<Item = (&'a str, ChcCompactValueId)> + 'a {
        self.step
            .env
            .iter()
            .map(|(name, id)| (name.as_str(), ChcCompactValueId(id.0)))
    }
}

impl ChcValidatedCompactGroundDerivation {
    /// Exact schema of the standalone DAG evidence.
    pub fn artifact_schema(&self) -> &'static str {
        CHC_COMPACT_GROUND_DERIVATION_SCHEMA
    }
    /// Exact deciding evidence role.
    pub fn artifact_role(&self) -> &'static str {
        CHC_COMPACT_GROUND_DERIVATION_ROLE
    }
    /// Hash of the complete canonical bytes, not an unchecked supplied digest.
    pub fn artifact_sha256(&self) -> &str {
        &self.artifact_sha256
    }
    /// Number of complete authenticated artifact bytes.
    pub fn artifact_bytes(&self) -> usize {
        self.artifact_bytes
    }
    /// Schema of the normalized original source hashed in the same run.
    pub fn normalized_input_schema(&self) -> &str {
        &self.normalized_input_schema
    }
    /// Normalized source hash. Revalidate before using this with another source.
    pub fn normalized_input_sha256(&self) -> &str {
        &self.normalized_input_sha256
    }
    /// Order-sensitive identity authenticating clause indices.
    pub fn source_clause_sequence_sha256(&self) -> &str {
        &self.source_clause_sequence_sha256
    }
    /// Query root in the validated step sequence.
    pub fn query_step(&self) -> usize {
        self.derivation.query_step
    }
    /// Number of shared nodes, not the exponentially expanded leaf count.
    pub fn node_count(&self) -> usize {
        self.derivation.arena.nodes().len()
    }
    /// Number of original clause instances.
    pub fn step_count(&self) -> usize {
        self.derivation.steps.len()
    }
    /// Borrow a node named by this snapshot's bindings or field edges.
    pub fn node(&self, id: ChcCompactValueId) -> Option<ChcCompactValueView<'_>> {
        self.derivation
            .arena
            .get(ValueId(id.0))
            .map(|node| ChcCompactValueView { node })
    }
    /// Every distinct shared node, in topological order, without allocation.
    pub fn nodes(
        &self,
    ) -> impl ExactSizeIterator<Item = (ChcCompactValueId, ChcCompactValueView<'_>)> {
        self.derivation
            .arena
            .nodes()
            .iter()
            .enumerate()
            .map(|(index, node)| {
                (
                    ChcCompactValueId(index as u32),
                    ChcCompactValueView { node },
                )
            })
    }
    /// Borrow a step, without allocating or trusting another source.
    pub fn step(&self, index: usize) -> Option<ChcCompactGroundStepView<'_>> {
        self.derivation
            .steps
            .get(index)
            .map(|step| ChcCompactGroundStepView { step })
    }
    /// All original clause instances in well-founded derivation order.
    pub fn steps(&self) -> impl ExactSizeIterator<Item = ChcCompactGroundStepView<'_>> {
        self.derivation
            .steps
            .iter()
            .map(|step| ChcCompactGroundStepView { step })
    }
}

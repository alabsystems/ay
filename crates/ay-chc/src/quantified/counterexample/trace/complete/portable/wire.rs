// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Strict MODEL DATA schema. Neither serde nor a supplied digest seals a trace.

use serde::{Deserialize, Serialize};

pub(super) const SCHEMA: &str = "ay.quantified-chc-complete-trace-artifact/v1";
pub(super) const MAX_NODES: usize = 4096;
pub(super) const MAX_STORES: usize = 32_768;

#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct Wire {
    pub(super) schema: String,
    pub(super) source: String,
    pub(super) steps: Vec<Step>,
    pub(super) graphs: Vec<Graph>,
    pub(super) functions: String,
    pub(super) pinned_sha256: String,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct Step {
    pub(super) clause_index: usize,
    pub(super) premises: Vec<usize>,
    pub(super) bindings: Vec<Local>,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct Local {
    pub(super) name: String,
    pub(super) value: Value,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(tag = "kind", deny_unknown_fields)]
pub(super) enum Value {
    Literal { value: String },
    Functional { graph: usize },
}

#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
#[serde(tag = "kind", deny_unknown_fields)]
pub(super) enum Element {
    Bool,
    BitVec { width: u32 },
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct Graph {
    pub(super) element: Element,
    pub(super) root: usize,
    pub(super) nodes: Vec<Node>,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(tag = "kind", deny_unknown_fields)]
pub(super) enum Scalar {
    Bool { value: bool },
    BitVec { width: u32, value: String },
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct Store {
    pub(super) index: u64,
    pub(super) value: Scalar,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(tag = "kind", deny_unknown_fields)]
pub(super) enum Node {
    Finite {
        default: Scalar,
        stores: Vec<Store>,
    },
    Store {
        base: usize,
        index: u64,
        value: Scalar,
    },
    Range {
        destination: usize,
        source: usize,
        lo: u64,
        hi: u64,
        source_lo: u64,
    },
}

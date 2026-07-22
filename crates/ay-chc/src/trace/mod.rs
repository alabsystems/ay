// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Trace infrastructure with dependency graph for TRL loop detection.
//!
//! This module provides trace representation for TRL/ABMC algorithms where each
//! step stores:
//! 1. The chosen transition ID
//! 2. A syntactic implicant (conjunction of literals satisfied by the model)
//! 3. A projected model for that step
//!
//! Loop detection relies on a **persistent** dependency graph over implicants
//! (not per-trace indices). The graph is not cleared between iterations -
//! edges are learned from consecutive trace steps and persist.
//!
//! # Design Reference
//!
//! Based on LoAT's TRL implementation:
//! - `reference/loat-src/src/trl/trl.cpp:137-158` (trace building)
//! - `reference/loat-src/src/trl/trl.cpp:26-46` (loop detection)
//! - `reference/loat-src/src/lib/util/dependencygraph.hpp` (graph structure)
//!
//! See the development design notes for full design.
//!
//! # Issue
//!
//! Part of #1173 (supports #1163 TRL, #1164 ABMC)

use crate::expr::ChcExpr;
use crate::mbp::Mbp;
use crate::smt::SmtValue;
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

/// Stable identifier for interned implicants in the dependency graph.
///
/// Implicants are interned so that graph edges remain meaningful across
/// trace rebuilds. The same structural implicant always gets the same ID.
pub(crate) type ImplicantId = u32;

/// A single element in an execution trace.
///
/// Each trace element represents one transition step, including:
/// - Which transition was taken (`_transition_id`)
/// - The implicant (interned syntactic cube) for that step
/// - The projected model containing relevant variable values
#[derive(Debug, Clone)]
pub(crate) struct TraceElement {
    /// The transition ID that was taken at this step.
    /// This corresponds to the value of the trace_var in the model.
    pub _transition_id: i128,

    /// Interned ID of the implicant cube for this step.
    /// Used for dependency graph edge queries.
    pub implicant_id: ImplicantId,

    /// Projected model for this step, mapping base variable names to values.
    /// Contains state variables and their _next versions, plus any variables
    /// mentioned in the implicant cube.
    pub model: FxHashMap<String, SmtValue>,
}

/// Dependency graph over interned implicants.
///
/// The graph persists across trace rebuilds - only the trace elements are
/// cleared, not the graph. This allows loop detection to leverage edges
/// learned from previous iterations.
///
/// Nodes are structural implicant expressions (interned to stable IDs).
/// Edges represent "can follow" relationships between consecutive implicants.
#[derive(Debug, Default)]
pub(crate) struct DependencyGraph {
    /// Interning table: structural ChcExpr -> stable node id.
    node_ids: FxHashMap<ChcExpr, ImplicantId>,

    /// Reverse lookup: id -> expression.
    /// Useful for debugging and later TRP/CVP integration.
    nodes: Vec<ChcExpr>,

    /// Directed edges representing "prev -> current" relationships.
    /// If (a, b) is in edges, it means implicant b was observed immediately
    /// after implicant a in some trace.
    edges: FxHashSet<(ImplicantId, ImplicantId)>,
}

impl DependencyGraph {
    /// Create a new empty dependency graph.
    #[cfg(test)]
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Number of interned implicant nodes.
    #[cfg(test)]
    pub(crate) fn num_nodes(&self) -> usize {
        self.nodes.len()
    }

    /// Number of directed edges.
    #[cfg(test)]
    pub(crate) fn num_edges(&self) -> usize {
        self.edges.len()
    }

    /// Intern an implicant expression, returning its stable ID.
    ///
    /// If the expression has been seen before, returns the existing ID.
    /// Otherwise, assigns a new ID and stores the expression.
    pub(crate) fn intern(&mut self, implicant: ChcExpr) -> ImplicantId {
        if let Some(&id) = self.node_ids.get(&implicant) {
            return id;
        }

        let id = self.nodes.len() as ImplicantId;
        self.nodes.push(implicant.clone());
        self.node_ids.insert(implicant, id);
        id
    }

    /// Add a directed edge from `from` to `to`.
    ///
    /// Indicates that implicant `to` was observed immediately after implicant
    /// `from` in some trace step.
    pub(crate) fn add_edge(&mut self, from: ImplicantId, to: ImplicantId) {
        self.edges.insert((from, to));
    }

    /// Check if there is a directed edge from `from` to `to`.
    ///
    /// Used for loop detection: if there's an edge from trace[end] to
    /// trace[start], then the trace contains a potential loop.
    pub(crate) fn has_edge(&self, from: ImplicantId, to: ImplicantId) -> bool {
        self.edges.contains(&(from, to))
    }

    /// Get the expression for an interned implicant ID.
    pub(crate) fn get_expr(&self, id: ImplicantId) -> Option<&ChcExpr> {
        self.nodes.get(id as usize)
    }
}

/// An execution trace with dependency graph.
///
/// The trace stores a sequence of `TraceElement`s representing an execution
/// path. The dependency graph is shared across trace rebuilds - clearing
/// the trace elements does not clear the graph.
#[derive(Debug, Default)]
pub(crate) struct Trace {
    /// The trace elements, one per step.
    /// Cleared between iterations; graph is not.
    pub elements: Vec<TraceElement>,

    /// The dependency graph, persists across trace rebuilds.
    pub graph: DependencyGraph,
}

impl Trace {
    /// Create a new empty trace with fresh dependency graph.
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Number of trace elements.
    #[cfg(test)]
    pub(crate) fn len(&self) -> usize {
        self.elements.len()
    }

    /// Whether the trace has no elements.
    #[cfg(test)]
    pub(crate) fn is_empty(&self) -> bool {
        self.elements.is_empty()
    }

    /// Clear the trace elements but preserve the dependency graph.
    ///
    /// This matches LoAT's behavior where the graph persists across iterations.
    /// (Source: `reference/loat-src/src/trl/trl.cpp:137-158`)
    pub(crate) fn clear(&mut self) {
        self.elements.clear();
        // Note: graph is NOT cleared
    }

    /// Push a trace element, adding a graph edge from the previous element.
    ///
    /// If this is not the first element, adds an edge from the previous
    /// implicant to this one in the dependency graph.
    pub(crate) fn push(&mut self, element: TraceElement) {
        // Add edge from previous implicant to this one
        if let Some(prev) = self.elements.last() {
            self.graph.add_edge(prev.implicant_id, element.implicant_id);
        }
        self.elements.push(element);
    }

    /// Find a looping infix in the trace.
    ///
    /// Returns `Some((start, end))` if there exists indices `start <= end`
    /// such that `graph.has_edge(trace[end].implicant_id, trace[start].implicant_id)`.
    ///
    /// This indicates that the state at `end` can transition back to a state
    /// compatible with `start`, forming a potential loop.
    ///
    /// The search order prefers shorter infixes (smaller `end - start`).
    ///
    /// (Source: `reference/loat-src/src/trl/trl.cpp:26-46`)
    pub(crate) fn find_looping_infix(&self) -> Option<(usize, usize)> {
        let n = self.elements.len();
        if n == 0 {
            return None;
        }

        // Search for looping infix, preferring shorter lengths
        for i in 0..n {
            for start in 0..(n - i) {
                let end = start + i;
                let end_id = self.elements[end].implicant_id;
                let start_id = self.elements[start].implicant_id;
                if self.graph.has_edge(end_id, start_id) {
                    return Some((start, end));
                }
            }
        }
        None
    }
}

/// Build a trace from an SMT model.
///
/// This is the AY analogue of LoAT's `TRL::build_trace()`.
/// (Source: `reference/loat-src/src/trl/trl.cpp:137-158`)
///
/// # Arguments
///
/// * `trace` - The trace to populate (will be cleared first)
/// * `depth` - Number of steps in the current unrolling
/// * `trace_var_name` - Name of the Int variable holding the transition ID
/// * `state_var_names` - Names of the state variables
/// * `rule_map` - Mapping from transition ID to base transition formula
///   (expressed over `x`/`x_next` variables, including `trace_var = id`)
/// * `model` - Time-indexed SMT model from solver
/// * `mbp` - MBP instance for implicant extraction
///
/// # Time Indexing Convention
///
/// Variables in the model use AY's standard time-indexing:
/// - Time 0: base name (e.g., `x`)
/// - Time k > 0: `x_k` (e.g., `x_1`, `x_2`)
///
/// This matches `TransitionSystem::version_var`.
/// (Source: `crates/ay-chc/src/transition_system.rs:90-101`)
pub(crate) fn build_trace(
    trace: &mut Trace,
    depth: usize,
    trace_var_name: &str,
    state_var_names: &[String],
    rule_map: &FxHashMap<i128, ChcExpr>,
    model: &FxHashMap<String, SmtValue>,
    mbp: &Mbp,
) {
    // Clear existing elements but preserve graph
    trace.clear();

    for d in 0..depth {
        // Read _transition_id from the model at time d
        let trace_var_at_d = versioned_name(trace_var_name, d);
        let _transition_id = match model.get(&trace_var_at_d) {
            Some(SmtValue::Int(id)) => *id,
            _ => {
                // If trace_var not found, skip this step
                continue;
            }
        };

        // Build composed step model M_d mapping base names to values
        let mut step_model: FxHashMap<String, SmtValue> = FxHashMap::default();

        // For each state var x:
        //   x := value of x@d in the SMT model
        //   x_next := value of x@(d+1) in the SMT model
        for var_name in state_var_names {
            // Current state: x@d
            let var_at_d = versioned_name(var_name, d);
            if let Some(val) = model.get(&var_at_d) {
                step_model.insert(var_name.clone(), val.clone());
            }

            // Next state: x@(d+1)
            let next_var_name = format!("{var_name}_next");
            let var_at_d_plus_1 = versioned_name(var_name, d + 1);
            if let Some(val) = model.get(&var_at_d_plus_1) {
                step_model.insert(next_var_name, val.clone());
            }
        }

        // Also include trace_var itself
        step_model.insert(trace_var_name.to_string(), SmtValue::Int(_transition_id));

        // Get the rule formula for this transition
        let rule = match rule_map.get(&_transition_id) {
            Some(r) => r,
            None => continue, // Unknown transition, skip
        };

        // Compute implicant cube
        let cube = mbp.implicant_cube(rule, &step_model);

        // Intern the cube to get stable implicant_id
        let implicant_id = trace.graph.intern(cube.clone());

        // Project the step model to relevant variables
        // Include state vars, state_next vars, and vars from the cube
        let mut projected_model: FxHashMap<String, SmtValue> = FxHashMap::default();

        for var_name in state_var_names {
            if let Some(val) = step_model.get(var_name) {
                projected_model.insert(var_name.clone(), val.clone());
            }
            let next_var_name = format!("{var_name}_next");
            if let Some(val) = step_model.get(&next_var_name) {
                projected_model.insert(next_var_name, val.clone());
            }
        }

        // Also include variables mentioned in the cube
        for var in cube.vars() {
            if let Some(val) = step_model.get(&var.name) {
                projected_model.insert(var.name.clone(), val.clone());
            }
        }

        // Push the trace element using trace.push() which handles edge addition
        trace.push(TraceElement {
            _transition_id,
            implicant_id,
            model: projected_model,
        });
    }
}

/// Convert a base variable name to its time-versioned form.
///
/// Uses AY's standard convention:
/// - Time 0: base name (e.g., "x")
/// - Time k > 0: "x_k" (e.g., "x_1", "x_2")
fn versioned_name(base: &str, time: usize) -> String {
    if time == 0 {
        base.to_string()
    } else {
        format!("{base}_{time}")
    }
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
mod tests;

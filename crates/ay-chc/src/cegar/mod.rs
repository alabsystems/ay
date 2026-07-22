// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! CEGAR (Counterexample-Guided Abstraction Refinement) for CHC solving
//!
//! This module implements predicate abstraction with CEGAR refinement,
//! based on the Eldarica approach:
//!
//! Reference: `reference/eldarica/src/main/scala/lazabs/horn/bottomup/CEGAR.scala`
//!
//! ## Algorithm Overview
//!
//! 1. **Predicate Abstraction**: Abstract states track which predicates hold
//! 2. **Edge Generation**: For each clause, generate abstract edges between states
//! 3. **Subsumption**: Track which states subsume others to prune exploration
//! 4. **Counterexample Analysis**: When reaching False, extract counterexample DAG
//! 5. **Refinement**: Use interpolation to discover new predicates
//!
//! ## Key Components
//!
//! - `AbstractState`: A (relation, predicates) pair representing abstract reachability
//! - `AbstractEdge`: Edge in the abstract reachability graph
//! - `StateQueue`: Priority queue for scheduling state expansions
//! - `CegarEngine`: Main CEGAR algorithm implementation

mod abstract_state;
mod engine;
mod predicate_store;
mod state_queue;

pub(crate) use engine::{CegarConfig, CegarEngine, CegarResult};

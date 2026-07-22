// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! LAWI (Lazy Abstraction With Interpolants) engine.
//!
//! This module introduces the core data structures used by LAWI:
//! - Abstract Reachability Tree (ART)
//! - Covering relation
//! - Concrete ART-path encoding and refinement
//! - Solver loop

mod art;
mod covering;
mod path_encoding;
mod solver;

pub(crate) use solver::{LawiConfig, LawiSolver};

#[cfg(test)]
mod tests;

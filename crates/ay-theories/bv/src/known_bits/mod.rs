// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Known-bits cones: the first compiled region (design
//! the development design notes, "Compiled regions").
//!
//! An obligation's cone of Boolean and bit-vector terms runs as a region:
//! from the asserted roots, through every known-bit consequence the
//! transfer rules derive in both directions, to a trail of knowledge
//! changes. A region that reaches a contradiction refutes the obligation,
//! and [`replay`] checks that refutation independently before anyone may
//! accept it.
//!
//! * [`rules`] states each transfer rule's directions once.
//! * [`cone`] builds the region program from a term store.
//! * [`engine`] runs it as ordinary Rust (the interpreted region).
//! * `ay_jit::known_bits_region` compiles the same program per obligation
//!   family through external-codegen-ir and external-codegen (the compiled region).
//! * [`replay`] re-derives the refutation from the assertions alone.

pub mod cone;
pub mod engine;
pub mod ints;
pub mod replay;
pub mod rules;

#[cfg(test)]
mod tests;

pub use cone::{Cone, ConeRefusal};
pub use engine::{run_interpreted, RegionStatus, TrailEntry, DEFAULT_MAX_ROUNDS};
pub use replay::{replay_refutation, ReplayRefusal, ReplayStats};
pub use rules::KnownBits;

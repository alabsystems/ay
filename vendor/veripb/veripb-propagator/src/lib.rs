//! Crate for handling pseudo-Boolean unit propagation in the VeriPB proof checker. The main way to use the this library for pseudo-Boolean propagation is through interaction with the [`PropagationEngine`](`propagation_engine::PropagationEngine`).

// `clippy::restriction` is a menu of house styles, not a soundness group, and
// is allowed wholesale in the four crates that carry this attribute; the
// reasoning, the measurement command, and what the allow costs are recorded
// once, at the top of `veripb-checker/src/lib.rs`. The two members already at
// zero across those crates are re-enabled by name so they cannot come back.
#![allow(clippy::restriction)]
#![warn(clippy::unimplemented, clippy::todo)]

pub mod cardinality_watcher;
pub mod clause_watcher;
pub mod error;
pub mod general_pb_watcher;
pub mod propagation_engine;
pub mod propagation_set;
pub mod propagator;
pub mod trail;
pub mod watcher;

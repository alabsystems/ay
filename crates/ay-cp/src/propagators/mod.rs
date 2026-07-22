// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Constraint propagator implementations.
//!
//! Each propagator implements the [`Propagator`](crate::propagator::Propagator)
//! trait. All propagations must be explainable (produce reason clauses) so that
//! ay-sat's CDCL engine can learn from conflicts.
//!
//! # Priority order (cheapest first)
//!
//! **Binary** (priority 1):
//! - `linear_ne` — linear not-equal propagator (fires when n-1 vars fixed)
//!
//! **Linear** (priority 2):
//! - `linear` — bounds propagation for linear inequalities
//! - `element` — array indexing constraint
//! - `table` — table/extensional constraint (AC via supports)
//! - `alldifferent` — Lopez-Ortiz bounds consistency (O(n log n))
//! - `shifted_alldifferent` — bounds consistency with per-variable offsets
//!
//! **Global** (priority 3):
//! - `alldifferent_ac` — Régin arc consistency (gated: enrolled as a complement
//!   to `alldifferent` bounds propagation when `n >= 3`, every variable domain
//!   has cardinality `<= ALLDIFF_AC_DOMAIN_LIMIT` (128), and at least one
//!   variable has a sparse domain (`domain_size < interval_span`); see
//!   `engine/compile.rs`). Aux-var lifting for shifted AllDifferent (via
//!   LinearLe channeling) remains unimplemented — see the `AC via aux-var
//!   lifting is disabled` comment in `engine/compile.rs` / `engine/detect.rs`.
//! - `cumulative` — scheduling (time-table filtering)
//! - `disjunctive` — edge-finding for non-overlapping tasks (Vilim 2008)
//!
//! # Reference implementations
//!
//! - OR-Tools CP-SAT: `ortools/sat/all_different.h`, `ortools/sat/table.h`, etc.
//! - Chuffed: `chuffed/globals/`
//! - Pumpkin: `pumpkin-solver/src/propagators/`

pub mod alldifferent;
pub mod alldifferent_ac;
pub mod cumulative;
pub mod disjunctive;
pub mod element;
pub mod linear;
pub mod linear_ne;
pub mod shifted_alldifferent;
pub mod table;

// Future propagators (stubs):
// pub mod circuit;
// pub mod inverse;

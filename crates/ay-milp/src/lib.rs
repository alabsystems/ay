// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! # ay-milp: a MILP/LP engine with a typed in-process API
//!
//! The crate exposes a solver-neutral [`Model`] plus reusable [`LpSession`]
//! and [`BabSession`] surfaces. Its float-first search paths are separated
//! from exact-rational validation so callers receive typed outcomes and can
//! independently check exported evidence.
//!
//! ## API guarantees
//!
//! 1. **No silent wrong values.** Anything unwarranted is
//!    [`Outcome::Unknown`] with a [`UnknownReason`] — wrong-optimum classes
//!    are unrepresentable.
//! 2. **Evidence is data.** [`FarkasCertificate`] / [`OptimalityCertificate`]
//!    are values with independent `verify(&Model)` that re-checks the exact
//!    arithmetic with no solver state.
//! 3. **Rigorous bounds flag.** [`Outcome::Bound`] marks `rigorous` only for
//!    directed-rounding-corrected or exact bounds.
//! 4. **Deadlines and determinism.** [`SolveOpts`] deadlines are honored
//!    inside solve loops; determinism gives run-to-run identical outcomes.
//! 5. **`Model: Send + Sync + Clone`**; sessions are `Send`.
//!
//! ## Solver paths
//!
//! [`LpSession`] and continuous [`BabSession`] models use a
//! Dutertre–de Moura bounded-variable simplex over exact rationals. Their
//! verdicts are exact and can carry model-level certificates. Integral models
//! use the native branch-and-bound engine; with the `smt` feature enabled, an
//! in-process ay-dpll lowering provides an exact QF_LRA fallback for binary
//! columns represented as 0/1 disjunctions.

mod bab;
#[doc(hidden)]
pub use bab::{
    diag_dump_root_basis,
    diag_exact_probe,
    diag_float_lp,
    diag_pin_probe,
    diag_presolve,
    diag_refine_probe,
    // STAGE-0 COLD-CLONE READINESS PoC (inert to the serial path; see bab.rs):
    // driven only by tests/parallel_ready.rs.
    NodeBound,
    NodeLpProbe,
};
mod cert;
mod certify;
mod cuts;
mod error;
mod exact;
mod lattice;
mod lu;
mod margin;
#[doc(hidden)]
pub use margin::diag_margin_reframe;
mod model;
mod mps;
mod ns;
mod opts;
mod outcome;
mod parity;
mod presolve;
mod session;
mod simplex;
#[cfg(feature = "smt")]
mod smt;
mod symmetry;
mod tree_cert;

pub use cert::{
    BoundSide, CertificateError, CertifiedRow, FactRef, FarkasCertificate, Multiplier,
    OptimalityCertificate,
};
pub use error::{MilpError, ModelError};
pub use model::{Col, ColKind, Model, PointViolation, Row, Sense};
pub use mps::{read_mps, MpsError, MpsProblem};
pub use opts::SolveOpts;
pub use outcome::{Outcome, UnknownReason};
pub use session::{BabSession, LpSession, ObbtOpts, ObbtReport};
pub use simplex::{px_profile_line, rt_profile_line, sb_profile_line, upd_profile_line};
pub use tree_cert::{MilpInfeasibilityCertificate, TreeNode};

// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Quantifier elimination (QE) for linear integer and real arithmetic.
//!
//! This module hosts quantifier-elimination candidate procedures:
//! Cooper's algorithm for a single existential over a conjunction of LIA
//! literals ([`cooper`]), and Loos-Weispfenning virtual substitution for a
//! single existential over a conjunction of LRA literals ([`lw`]).
//!
//! Every successful elimination is checked against the original formula with a
//! deterministic finite test battery before it is returned. A failed test
//! rejects the candidate. Passing that battery is not a universal equivalence
//! proof, so public verdict paths must keep the exact source formula or compose
//! the candidate with a separate symbolic certificate.

pub mod cooper;
pub mod isint;
pub mod lw;

pub use cooper::{eliminate_exists, QeResult};
pub use lw::eliminate_exists_real;

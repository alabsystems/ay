// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Quantifier elimination (QE) for linear integer and real arithmetic.
//!
//! This module hosts soundness-gated quantifier-elimination procedures:
//! Cooper's algorithm for a single existential over a conjunction of LIA
//! literals ([`cooper`]), and Loos-Weispfenning virtual substitution for a
//! single existential over a conjunction of LRA literals ([`lw`]).
//!
//! Every successful elimination is checked against the original formula with an
//! independent equivalence test before it is returned. If the check fails for
//! any reason, the procedure refuses (returns `None`) and the caller keeps the
//! original quantified formula. The procedure NEVER returns an approximate or
//! wrong result.

pub mod cooper;
pub mod isint;
pub mod lw;

pub use cooper::{eliminate_exists, QeResult};
pub use lw::eliminate_exists_real;

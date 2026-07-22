// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Parity preservation checks and algebraic expression helpers.
//!
//! Verifies that modular arithmetic invariants (var mod k = c) are
//! preserved by transition relations. Includes offset extraction,
//! variable definition lookup, and sum-parity pairing utilities.
//!
//! Submodules:
//! - `preservation`: transition-level parity checks (self-loop + cross-predicate)
//! - `frame_aware`: frame-lemma-aware algebraic offset analysis with CRT
//! - `algebraic`: algebraic parity verification and expression utilities

mod algebraic;
mod frame_aware;
mod preservation;

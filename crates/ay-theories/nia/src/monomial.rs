// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Monomial tracking for NIA solver — delegates to ay_core::nonlinear.

pub use ay_core::nonlinear::Monomial;

#[cfg(test)]
#[path = "monomial_tests.rs"]
mod tests;

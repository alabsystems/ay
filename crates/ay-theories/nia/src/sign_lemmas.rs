// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Sign helpers for NIA solver — delegates to ay_core::nonlinear.
//!
//! Based on Z3's `nla_basics_lemmas.cpp`.

// product_sign re-exported for potential future use by NIA sign lemma callers.
#[allow(unused_imports)]
pub(crate) use ay_core::nonlinear::product_sign;

#[cfg(test)]
#[path = "sign_lemmas_tests.rs"]
mod tests;

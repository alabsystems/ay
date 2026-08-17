// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Sign lemma helpers for NRA solver — delegates to ay_core::nonlinear.
//!
//! Based on Z3's `nla_basics_lemmas.cpp`.

pub(crate) use ay_core::nonlinear::SignConstraint;
#[allow(unused_imports)]
pub(crate) use ay_core::nonlinear::{
    check_sign_consistency, extract_sign_constraint, product_sign, propagate_monomial_signs,
    propagate_product_signs, record_sign_constraint, sign_contradicts, vars_needing_model_sign,
};

#[cfg(test)]
#[path = "sign_tests.rs"]
mod tests;

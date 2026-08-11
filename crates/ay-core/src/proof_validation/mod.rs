// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared semantic validation for theory proof certificates.

mod farkas;
mod lia;

pub use farkas::{
    resolve_equality_coefficient_signs, verify_farkas_annotation_shape,
    verify_farkas_conflict_lits_full, verify_farkas_conflict_lits_linear,
    verify_farkas_signed_shape, FarkasValidationError,
};
pub use lia::{
    recognize_lia_divisibility, recognize_lia_linear_identity, recognize_lia_mod_range,
    validate_lia_mod_range, validate_lia_theory_lemma, LiaValidationError,
};

#[cfg(test)]
mod farkas_tests;

#[cfg(test)]
mod lia_tests;

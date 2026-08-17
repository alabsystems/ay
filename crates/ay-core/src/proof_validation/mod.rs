// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared semantic validation for theory proof certificates.

mod farkas;
#[path = "farkas/metered.rs"]
mod farkas_metered;
mod lia;

pub use farkas::{
    recover_single_equality_farkas, resolve_equality_coefficient_signs,
    verify_farkas_annotation_shape, verify_farkas_conflict_lits_full,
    verify_farkas_conflict_lits_linear, verify_farkas_signed_shape, FarkasValidationError,
};
pub use farkas_metered::{
    farkas_conflict_literal_is_single_inequality, farkas_progress_row_kind,
    verify_affine_equality_farkas_with_progress, verify_pure_inequality_farkas_with_progress,
    FarkasProgressRowKind,
};
pub use lia::{
    recognize_arith_disequality_split, recognize_int_bounds_tautology, recognize_lia_bounds_gap,
    recognize_lia_divisibility, recognize_lia_linear_identity, recognize_lia_mod_range,
    validate_lia_mod_range, validate_lia_theory_lemma, LiaValidationError,
};

#[cfg(test)]
mod farkas_tests;

#[cfg(test)]
mod lia_tests;

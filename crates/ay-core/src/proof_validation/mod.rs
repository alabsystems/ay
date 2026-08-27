// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared semantic validation for theory proof certificates.

mod farkas;
#[path = "farkas/metered.rs"]
mod farkas_metered;
mod fresh_def_bound;
mod fresh_def_eq;
mod lia;
mod lia_bound_lattice;
mod lia_cut_lattice;
mod lia_guarded_split;

pub use farkas::{
    conflict_lits_satisfied_by, recover_single_equality_farkas, resolve_equality_coefficient_signs,
    verify_farkas_annotation_shape, verify_farkas_conflict_lits_full,
    verify_farkas_conflict_lits_full_holds, verify_farkas_conflict_lits_linear,
    verify_farkas_conflict_lits_linear_holds, verify_farkas_signed_shape, FarkasValidationError,
};
pub use farkas_metered::{
    farkas_conflict_literal_is_single_inequality, farkas_progress_row_kind,
    verify_affine_equality_farkas_with_progress, verify_pure_inequality_farkas_with_progress,
    FarkasProgressRowKind,
};
pub use fresh_def_bound::{
    recognize_fresh_def_bound, FreshDefBoundShape, FreshDefBoundShapeError, FreshDefBoundSide,
};
pub use fresh_def_eq::{recognize_fresh_def_eq, FreshDefEqShape, FreshDefEqShapeError};
pub use lia::{
    arith_disequality_split_guard_multiplier, arith_disequality_split_has_primitive_guard,
    recognize_arith_disequality_split, recognize_int_bounds_tautology, recognize_lia_bounds_gap,
    recognize_lia_divisibility, recognize_lia_linear_identity, recognize_lia_mod_range,
    validate_lia_mod_range, validate_lia_theory_lemma, LiaValidationError,
};
pub use lia_bound_lattice::{
    int_bound_lattice_gap_core, recognize_int_bound_lattice_gap, IntBoundLatticeGap,
};
pub use lia_cut_lattice::{
    int_cut_lattice_gap_core, recognize_int_cut_lattice_gap, CutRow, IntCutLatticeGap,
};
pub use lia_guarded_split::recognize_int_guarded_split_gap;

#[cfg(test)]
mod farkas_holds_tests;

#[cfg(test)]
mod farkas_tests;

#[cfg(test)]
mod fresh_def_bound_tests;

#[cfg(test)]
mod fresh_def_eq_tests;

#[cfg(test)]
mod lia_tests;

#[cfg(test)]
mod lia_bound_lattice_tests;

#[cfg(test)]
mod lia_cut_lattice_tests;

#[cfg(test)]
mod lia_guarded_split_tests;

#[cfg(test)]
mod lia_guarded_split_diseq_tests;

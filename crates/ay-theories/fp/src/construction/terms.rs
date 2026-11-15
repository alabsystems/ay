// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Term entry points retain the same poisoned owner as direct arithmetic.

use ay_core::{CnfLit, TermId};

use super::{FpBuildError, FpConstruction};
use crate::FpDecomposed;

impl FpConstruction<'_, '_> {
    /// Decompose a supported FP term, carrying control through recursive inputs.
    ///
    /// Terms and rounding modes retain the ordinary solver's sort/support
    /// preconditions. An unsupported semantic encoding remains a gap, not a
    /// cancellation result or a proof that the input is satisfiable.
    pub fn try_get_fp(&mut self, term: TermId) -> Result<FpDecomposed, FpBuildError> {
        self.encode(|solver, control| solver.get_fp_with_control(term, control))
    }

    /// Encode a Boolean condition, preserving Tseitin links and semantic gaps.
    pub fn try_encode_bool_condition(&mut self, term: TermId) -> Result<CnfLit, FpBuildError> {
        self.encode(|solver, control| solver.encode_bool_condition_with_control(term, control))
    }

    /// Encode the IEEE NaN classification predicate.
    pub fn try_bitblast_is_nan(&mut self, term: TermId) -> Result<CnfLit, FpBuildError> {
        self.encode(|solver, control| solver.bitblast_is_nan_with_control(term, control))
    }

    /// Encode the IEEE infinity classification predicate.
    pub fn try_bitblast_is_infinite(&mut self, term: TermId) -> Result<CnfLit, FpBuildError> {
        self.encode(|solver, control| solver.bitblast_is_infinite_with_control(term, control))
    }

    /// Encode the IEEE zero classification predicate.
    pub fn try_bitblast_is_zero(&mut self, term: TermId) -> Result<CnfLit, FpBuildError> {
        self.encode(|solver, control| solver.bitblast_is_zero_with_control(term, control))
    }

    /// Encode the IEEE normal classification predicate.
    pub fn try_bitblast_is_normal(&mut self, term: TermId) -> Result<CnfLit, FpBuildError> {
        self.encode(|solver, control| solver.bitblast_is_normal_with_control(term, control))
    }

    /// Encode the IEEE subnormal classification predicate.
    pub fn try_bitblast_is_subnormal(&mut self, term: TermId) -> Result<CnfLit, FpBuildError> {
        self.encode(|solver, control| solver.bitblast_is_subnormal_with_control(term, control))
    }

    /// Encode the SMT positive classification predicate.
    pub fn try_bitblast_is_positive(&mut self, term: TermId) -> Result<CnfLit, FpBuildError> {
        self.encode(|solver, control| solver.bitblast_is_positive_with_control(term, control))
    }

    /// Encode the SMT negative classification predicate.
    pub fn try_bitblast_is_negative(&mut self, term: TermId) -> Result<CnfLit, FpBuildError> {
        self.encode(|solver, control| solver.bitblast_is_negative_with_control(term, control))
    }

    /// Encode SMT identity: reflexive on NaN and distinguishing signed zeros.
    pub fn try_bitblast_fp_structural_eq(
        &mut self,
        x: TermId,
        y: TermId,
    ) -> Result<CnfLit, FpBuildError> {
        self.encode(|solver, control| solver.bitblast_fp_structural_eq_with_control(x, y, control))
    }

    /// Encode equality of two rounding-mode terms.
    pub fn try_bitblast_rm_eq(&mut self, x: TermId, y: TermId) -> Result<CnfLit, FpBuildError> {
        self.encode(|solver, control| solver.bitblast_rm_eq_with_control(x, y, control))
    }

    /// Encode IEEE equality: NaN is unequal and signed zeros compare equal.
    pub fn try_bitblast_fp_eq(&mut self, x: TermId, y: TermId) -> Result<CnfLit, FpBuildError> {
        self.encode(|solver, control| solver.bitblast_fp_eq_with_control(x, y, control))
    }

    /// Encode IEEE less-than.
    pub fn try_bitblast_fp_lt(&mut self, x: TermId, y: TermId) -> Result<CnfLit, FpBuildError> {
        self.encode(|solver, control| solver.bitblast_fp_lt_with_control(x, y, control))
    }

    /// Encode IEEE less-than-or-equal.
    pub fn try_bitblast_fp_le(&mut self, x: TermId, y: TermId) -> Result<CnfLit, FpBuildError> {
        self.encode(|solver, control| solver.bitblast_fp_le_with_control(x, y, control))
    }

    /// Encode IEEE greater-than.
    pub fn try_bitblast_fp_gt(&mut self, x: TermId, y: TermId) -> Result<CnfLit, FpBuildError> {
        self.encode(|solver, control| solver.bitblast_fp_gt_with_control(x, y, control))
    }

    /// Encode IEEE greater-than-or-equal.
    pub fn try_bitblast_fp_ge(&mut self, x: TermId, y: TermId) -> Result<CnfLit, FpBuildError> {
        self.encode(|solver, control| solver.bitblast_fp_ge_with_control(x, y, control))
    }

    /// Encode a supported BV predicate; unsupported shape is `Ok(None)`.
    ///
    /// `Err` refuses the whole attempt and must never be treated as unsupported
    /// shape or retried using a different encoding on this owner.
    pub fn try_bitblast_bv_predicate(
        &mut self,
        term: TermId,
    ) -> Result<Option<CnfLit>, FpBuildError> {
        self.encode(|solver, control| solver.bitblast_bv_predicate_with_control(term, control))
    }

    /// Encode composite BV equality, preserving unsupported shape separately.
    pub fn try_bitblast_bv_eq(
        &mut self,
        x: TermId,
        y: TermId,
    ) -> Result<Option<CnfLit>, FpBuildError> {
        self.encode(|solver, control| solver.try_bitblast_bv_eq_with_control(x, y, control))
    }

    /// Snapshot semantic incompleteness without exposing partial encoding data.
    ///
    /// This permits a caller to distinguish base encoding gaps from later
    /// congruence-only gaps. A healthy status is not permission to publish CNF;
    /// successful finalization is still required.
    pub fn try_has_encoding_gap(&mut self) -> Result<bool, FpBuildError> {
        self.encode(|solver, _| Ok(solver.has_encoding_gap()))
    }
}

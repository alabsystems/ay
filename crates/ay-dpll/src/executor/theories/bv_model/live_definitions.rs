// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Which array variables defined only under a nested equality stay withheld
//! from one BV/Bool model.
//!
//! [`Executor::array_vars_defined_only_under_nested_equality`] lists the array
//! variables whose only ground definitions sit below the top level. The model
//! may or may not hold such a definition, its stores were never scanned, and
//! the variable's select-derived interpretation covers only the cells some
//! read reached. Every such variable used to be withheld (read-conflicted)
//! unless the BV/Bool assignment showed that none of its definitions could
//! hold, and an array of arrays also needed the published interpretations to
//! falsify each definition its atom refused.
//!
//! Withholding was a guard while acceptance depended on it: with nothing
//! withheld, the observation pipeline counted an array assertion the
//! bit-blasted encoding covered as verified even when the printed model
//! falsified it, and the fail-closed `arrays-read-conflict-uneval` oracle ran
//! only while some array was withheld (releasing arrays of arrays on a refused
//! atom alone then confirmed models z3 rejects). #bv-array-delegation removed
//! that dependence. An array assertion the printed model evaluates to Unknown
//! or false is never counted verified, the independent gate evaluates every
//! assertion on the arrays `(get-model)` prints (#gate-exact-leaf-memo), and
//! every gate rejection arms the same re-solves (#abv-subst-model-retry). A
//! published partial interpretation is therefore judged on its values like any
//! other, and withholding guards nothing. It only costs, in two ways:
//!
//! * a round whose assertions need the variable stops as unevaluable instead
//!   of being judged on the interpretation the reads give it; and
//! * a round the gate confirms without the variable, every assertion true
//!   whatever its value, answers `sat` while `(get-model)` cannot print it
//!   ("model value for array c is not available").
//!
//! The fail-closed twin is
//! `released_array_of_arrays_holding_its_refused_definition_fails_closed`
//! (`model/tests/bv_array_delegation.rs`): a released array of arrays whose
//! reads hold the definition its atom refused falsifies a covered assertion,
//! and the candidate must end `unknown` with nothing withheld.
//!
//! Measured on 3617 QF_AUFBV fuzz formulas (every `sat` re-checked by z3 5.1.0
//! on the printed model), with the nested read-path refinement
//! (`bv_cegar_array/nested_fc.rs`) on both sides: withholding as before gave
//! 1289 valid models and 208 model errors, publishing gives 2041 and 9, and
//! neither gave an invalid model.
//!
//! Only a variable whose sort the select scans do not interpret
//! ([`Executor::select_scan_depth`]) stays withheld: released, it would carry
//! no interpretation of its own.

use super::*;

impl Executor {
    /// The variables of [`Self::array_vars_defined_only_under_nested_equality`]
    /// whose sort the select scans do not interpret.
    pub(super) fn withheld_nested_definition_vars(
        terms: &TermStore,
        assertions: &[TermId],
    ) -> HashSet<TermId> {
        let mut nested = Self::array_vars_defined_only_under_nested_equality(terms, assertions);
        nested.retain(|&var| Self::select_scan_depth(terms.sort(var)).is_none());
        nested
    }
}

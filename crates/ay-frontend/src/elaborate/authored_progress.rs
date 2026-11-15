// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Allocation-free access to compact authored literal-false provenance.

use super::{AuthoredAssertion, Context, TermId};

impl Context {
    /// Whether an exact term retains authored literal-false provenance.
    ///
    /// Unlike collecting [`Self::concrete_authored_literal_false_terms`], this
    /// lookup allocates nothing. The caller's fallible checkpoint runs before
    /// inspecting each compact row and at entry/final admission. Its error is
    /// returned immediately, without a partial answer or another callback.
    /// Parsed syntax and canonical false IDs alone never establish provenance.
    #[doc(hidden)]
    pub fn concrete_authored_literal_false_contains_with_progress<E>(
        &self,
        term: TermId,
        progress: &mut dyn FnMut() -> Result<(), E>,
    ) -> Result<bool, E> {
        progress()?;
        let mut found = false;
        for assertion in &self.authored_assertions {
            progress()?;
            if matches!(assertion,
                AuthoredAssertion::Concrete {
                    term: candidate,
                    source_is_literal_false: true,
                    ..
                } if *candidate == term)
            {
                found = true;
                break;
            }
        }
        progress()?;
        Ok(found)
    }
}

#[cfg(test)]
mod tests;

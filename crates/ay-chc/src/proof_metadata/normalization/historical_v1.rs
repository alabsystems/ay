// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Historical schema validation, not a replacement for current source identity.
//! The shared canonicalizer visits the actual AST/registry. Only datatype sort
//! spelling differs: inline constructors exactly as AY 48c98a43, instead of v2
//! content references. The ordinary policy and its current bytes are unchanged.

use super::*;

struct Historical<'a>(&'a mut dyn FnMut() -> bool);

impl Progress for Historical<'_> {
    type Error = IdentityHashInterrupted;

    fn poll(&mut self) -> Result<(), Self::Error> {
        if (self.0)() {
            Ok(())
        } else {
            Err(IdentityHashInterrupted)
        }
    }

    fn datatype_spelling(&self) -> DatatypeSpelling {
        DatatypeSpelling::InlineV1
    }
}

impl ChcProblem {
    /// Recompute historical v1 bytes from THIS complete AST and datatype registry.
    ///
    /// This is migration DATA, never a proof, source seal or permission to solve.
    /// Callers must authenticate exact historical bytes/digests and keep current
    /// identity, source coordinates and preparation recipe independently bound.
    /// An observer refusal returns no bytes; no current-schema fallback occurs.
    /// The observer must use the caller's original remaining owner, and callers
    /// must fence again after hashing/cleanup. Recursive inline datatype spelling
    /// can expand shared DAGs: traversal is cooperative, not hard wall/RSS or
    /// primitive allocation accounting. Use only under the original admission.
    pub fn normalized_input_v1_with_progress(
        &self,
        progress: &mut dyn FnMut() -> bool,
    ) -> Option<String> {
        let mut progress = Historical(progress);
        let input = text::normalized_input(self, &mut progress).ok()?;
        progress.poll().ok()?;
        Some(input)
    }
}

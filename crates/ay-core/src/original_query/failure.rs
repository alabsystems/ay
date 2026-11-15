// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{QueryDraft, QueryError};
use std::fmt;

/// Validation refusal retaining caller ownership of the untrusted draft.
///
/// Refusal does not clone or dispose of potentially large input. The caller
/// still owns disposal/resource policy; this does not bound caller cleanup.
/// Debug/Display never traverse or print the draft, and no authored capability
/// is returned on this path.
#[derive(thiserror::Error)]
#[error("{error}")]
pub struct ValidationFailure {
    #[source]
    error: QueryError,
    draft: QueryDraft,
}

impl ValidationFailure {
    pub(super) fn new(error: QueryError, draft: QueryDraft) -> Self {
        Self { error, draft }
    }

    /// Copy the small refusal reason, without scanning the draft.
    pub fn error(&self) -> QueryError {
        self.error
    }

    /// Recover the exact unmodified input for caller-controlled disposal/retry.
    pub fn into_draft(self) -> QueryDraft {
        self.draft
    }
}

impl fmt::Debug for ValidationFailure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("ValidationFailure")
            .field("error", &self.error)
            .finish_non_exhaustive()
    }
}

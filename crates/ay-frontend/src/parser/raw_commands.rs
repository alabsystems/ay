// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Owner-controlled raw list framing, not command grammar or proof authority.

use crate::authored_source::{AuthoredSourceError, SourceCursor, SourceTokenKind};
use ay_core::original_query::WorkBudget;
use std::ops::Range;

/// An exact borrowed top-level list, without normalization or command decoding.
///
/// This is only source framing. Unknown commands, invalid arity and ill-typed
/// terms may still occur. No host, typed query or proof permit is attached.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawCommandFrame<'source> {
    /// Unchanged source bytes from the first opening to its matching close.
    pub raw: &'source str,
    /// Byte offsets in the separately retained complete original input.
    pub span: Range<usize>,
    /// Ordered lexical occurrence indices, including the outer delimiters.
    pub tokens: Range<usize>,
}

/// Fail-closed raw framing or original-owner refusal; not an accepted query.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum RawCommandError {
    /// The same original lexical/work/deadline/cancellation owner refused.
    #[error(transparent)]
    Source(#[from] AuthoredSourceError),
    /// A raw token sequence cannot form complete top-level command lists.
    #[error("invalid raw command framing at byte {offset}: {message}")]
    Framing {
        /// Original byte offset, not a position in rendered text.
        offset: usize,
        /// Static rejection data; no owned diagnostic allocation is needed.
        message: &'static str,
    },
}

/// Zero-allocation raw command ranges under one borrowed original work owner.
///
/// Construction scans the COMPLETE input for lexical/list-framing failures
/// before exposing a cursor. Enumeration then scans those same immutable bytes
/// again, borrowing the SAME WorkBudget, without a new allowance or adapter.
/// Both actual passes are charged. No earlier frame escapes failed construction.
///
/// Enumeration refusal is sticky, and EOF remains an original-owner observation.
/// No decoded String, SExpr, Command, retained token tree or recovery is used.
/// Downstream native parsing, elaboration, host creation and proof checking are
/// not priced or authorized by this cursor; retained frame copies are caller-owned.
pub struct RawCommandCursor<'source, 'work, 'owner> {
    source: SourceCursor<'source, 'work, 'owner>,
    refused: Option<RawCommandError>,
}

impl<'source, 'work, 'owner> RawCommandCursor<'source, 'work, 'owner> {
    /// Validate complete raw framing, then enumerate with the same owner.
    ///
    /// A framing success does NOT establish valid command grammar, typing,
    /// semantics, source-to-term equivalence or proof/source authority.
    pub fn new(
        original: &'source str,
        work: &'work mut WorkBudget<'owner>,
    ) -> Result<Self, RawCommandError> {
        validate_complete(original, work)?;
        // Only healthy COMPLETE validation reaches this second lexical pass.
        // The original work ledger, cumulative grant and deadline are unchanged.
        Ok(Self {
            source: SourceCursor::new(original, work)?,
            refused: None,
        })
    }

    /// Borrow the complete unchanged input, including trivia and later commands.
    pub fn original(&self) -> &'source str {
        self.source.original()
    }

    /// Pull one borrowed raw list, or owner-polled EOF; never recover after error.
    ///
    /// Earlier enumerated raw frames remain nonqualifying descriptors if a later
    /// owner stop occurs. A successful preflight cannot authorize later execution.
    pub fn next_frame(&mut self) -> Result<Option<RawCommandFrame<'source>>, RawCommandError> {
        if let Some(error) = &self.refused {
            return Err(error.clone());
        }
        let result = self.next_frame_inner();
        if let Err(error) = &result {
            self.refused = Some(error.clone());
        }
        result
    }

    fn next_frame_inner(&mut self) -> Result<Option<RawCommandFrame<'source>>, RawCommandError> {
        // Fixed scalar framing work is admitted before cursor/range inspection.
        // SourceCursor separately admits actual bytes and token metadata.
        self.source.charge_work(8)?;
        let token_start = self.source.token_count();
        let Some(first) = self.source.next_token()? else {
            return Ok(None);
        };
        if first.kind != SourceTokenKind::LeftParen {
            return Err(RawCommandError::Framing {
                offset: first.span.start,
                message: "expected a top-level parenthesized list",
            });
        }
        let start = first.span.start;
        let mut depth = 1usize;
        loop {
            self.source.charge_work(8)?;
            let Some(token) = self.source.next_token()? else {
                return Err(RawCommandError::Framing {
                    offset: self.source.position(),
                    message: "unterminated top-level list",
                });
            };
            match token.kind {
                SourceTokenKind::LeftParen => {
                    depth = depth.checked_add(1).ok_or(RawCommandError::Framing {
                        offset: token.span.start,
                        message: "list depth overflow",
                    })?;
                }
                SourceTokenKind::RightParen => {
                    depth -= 1;
                    if depth == 0 {
                        self.source.charge_work(8)?;
                        let end = token.span.end;
                        let raw = self.source.original().get(start..end).ok_or(
                            RawCommandError::Framing {
                                offset: start,
                                message: "invalid original command range",
                            },
                        )?;
                        return Ok(Some(RawCommandFrame {
                            raw,
                            span: start..end,
                            tokens: token_start..self.source.token_count(),
                        }));
                    }
                }
                _ => {}
            }
        }
    }
}

// This helper's work borrow ends on return. Constructing Self with the final
// cursor's explicit 'work lifetime here would unnecessarily retain that borrow.
fn validate_complete(original: &str, work: &mut WorkBudget<'_>) -> Result<(), RawCommandError> {
    let mut validation = RawCommandCursor {
        source: SourceCursor::new(original, work)?,
        refused: None,
    };
    while validation.next_frame()?.is_some() {}
    Ok(())
}

#[cfg(test)]
mod tests;

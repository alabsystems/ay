// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! DRUP/DRAT carry a sequence of clauses in `:args`, not ordinary terms.
//!
//! The shared Boolean emitter's `Proof::drup_step` and the transported
//! bit-blast chain both emit these clauses. Clean's vendored Carcara parses
//! `Reserved::Cl` into `Operator::Cl`; its `tests/rules/drup.rs` exercises
//! both empty and nonempty clause arguments for DRUP and DRAT. Keep this
//! permission at the named rules' argument boundary: a clause is still not
//! accepted as a literal, assume, definition body or nested ordinary term.
//!
//! This remains a document check, not RUP/RAT validation. The independent
//! checker must still derive each argument clause from the cited premises.

use super::*;

impl AletheDocumentChecker {
    pub(super) fn parse_rup_arguments(
        &mut self,
        lexer: &mut Lexer<'_>,
        keyword_pos: Pos,
    ) -> Result<(), AletheDefect> {
        let (opening, pos) = lexer.next_token()?;
        if opening != Tok::Open {
            return Err(AletheDefect::UnexpectedToken {
                pos,
                expected: "'(' opening a clause argument sequence",
                found: opening.describe(),
            });
        }
        let mut count = 0usize;
        loop {
            let (token, pos) = lexer.next_token()?;
            match token {
                Tok::Close => break,
                Tok::Open => self.parse_rup_clause(lexer)?,
                Tok::Eof => {
                    return Err(AletheDefect::UnexpectedEof {
                        pos,
                        expected: "')' closing the clause argument sequence",
                    });
                }
                other => {
                    return Err(AletheDefect::UnexpectedToken {
                        pos,
                        expected: "'(' opening a clause argument",
                        found: other.describe(),
                    });
                }
            }
            count += 1;
        }
        if count == 0 {
            return Err(AletheDefect::EmptySequence {
                pos: keyword_pos,
                keyword: ":args".to_string(),
            });
        }
        Ok(())
    }

    fn parse_rup_clause(&mut self, lexer: &mut Lexer<'_>) -> Result<(), AletheDefect> {
        // A quoted |cl| is an ordinary identifier, not Carcara's reserved
        // clause constructor. The lexer otherwise normalizes both to Symbol.
        lexer.skip_trivia();
        let quoted = lexer.peek() == Some(b'|');
        let (head, head_pos) = lexer.next_token()?;
        if quoted || !matches!(&head, Tok::Symbol(name) if name == "cl") {
            return Err(AletheDefect::ClauseNotCl {
                pos: head_pos,
                found: head.describe(),
            });
        }
        let mut binders = self.frame_bound_vars();
        loop {
            let (token, pos) = lexer.next_token()?;
            match token {
                Tok::Close => return Ok(()),
                Tok::Eof => {
                    return Err(AletheDefect::UnexpectedEof {
                        pos,
                        expected: "')' closing the clause argument",
                    });
                }
                other => self.parse_term_from(lexer, other, pos, &mut binders, 0)?,
            }
        }
    }
}

#[cfg(test)]
mod tests;

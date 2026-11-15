// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

impl Walk<'_> {
    pub(super) fn let_bindings(
        &mut self,
        lexer: &mut Lexer<'_>,
        depth: usize,
        names: Vec<String>,
    ) -> Result<(), AletheDefect> {
        let (token, pos) = lexer.next_token()?;
        if token == Tok::Close {
            if names.is_empty() {
                return Err(AletheDefect::EmptySequence {
                    pos,
                    keyword: "let".to_string(),
                });
            }
            let mark = self.binders.len();
            self.binders.extend(names);
            self.pending.push(Frame::Close {
                mark,
                expected: "')' closing the let",
            });
            self.pending.push(Frame::ReadTerm(depth + 1));
            return Ok(());
        }
        if token != Tok::Open {
            return Err(unexpected(pos, "'(' opening a let binding", token));
        }
        let (token, pos) = lexer.next_token()?;
        let Tok::Symbol(name) = token else {
            return Err(unexpected(pos, "a let-bound name", token));
        };
        // Parallel let: hold all introduced names outside the live scope until
        // every RHS has been parsed against precisely the outer binders.
        self.pending.push(Frame::LetValue { depth, names, name });
        self.pending.push(Frame::ReadTerm(depth + 1));
        Ok(())
    }

    pub(super) fn binder(
        &mut self,
        lexer: &mut Lexer<'_>,
        depth: usize,
    ) -> Result<(), AletheDefect> {
        self.checker
            .expect_token(lexer, &Tok::Open, "'(' opening the binder list")?;
        let mark = self.binders.len();
        loop {
            let (token, pos) = lexer.next_token()?;
            if token == Tok::Close {
                if self.binders.len() == mark {
                    return Err(AletheDefect::EmptySequence {
                        pos,
                        keyword: "binder".to_string(),
                    });
                }
                break;
            }
            if token != Tok::Open {
                return Err(unexpected(pos, "'(' opening a sorted variable", token));
            }
            let (token, pos) = lexer.next_token()?;
            let Tok::Symbol(name) = token else {
                return Err(unexpected(pos, "a bound variable name", token));
            };
            self.checker.parse_sort(lexer)?;
            self.checker
                .expect_token(lexer, &Tok::Close, "')' closing the sorted variable")?;
            self.binders.push(name);
        }
        self.pending.push(Frame::Close {
            mark,
            expected: "')' closing the binder",
        });
        self.pending.push(Frame::ReadTerm(depth + 1));
        Ok(())
    }

    pub(super) fn annotation(&mut self, lexer: &mut Lexer<'_>) -> Result<(), AletheDefect> {
        loop {
            let (token, pos) = lexer.next_token()?;
            match token {
                Tok::Close => return Ok(()),
                Tok::Keyword(_) => {
                    let (value, pos) = lexer.next_token()?;
                    match value {
                        Tok::Close => return Err(unexpected(pos, "an annotation value", value)),
                        Tok::Open => self.checker.skip_balanced(lexer)?,
                        _ => {}
                    }
                }
                other => return Err(unexpected(pos, "an annotation keyword", other)),
            }
        }
    }
}

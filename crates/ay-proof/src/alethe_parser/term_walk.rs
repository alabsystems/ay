// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Defunctionalized term descent: input nesting grows a bounded heap stack,
//! never the native call stack. Frames retain the ordinary parser's order,
//! parallel-let scope, binder retirement and proof define-fun arity checks.

use super::*;

mod scopes;
pub(super) mod sorts;
#[cfg(test)]
mod tests;

type Arity = Option<(usize, String, Pos)>;

enum Frame {
    ReadTerm(usize),
    Arguments {
        depth: usize,
        count: usize,
        arity: Arity,
    },
    Qualified(usize),
    QualifiedTail,
    Close {
        mark: usize,
        expected: &'static str,
    },
    LetBindings {
        depth: usize,
        names: Vec<String>,
    },
    LetValue {
        depth: usize,
        names: Vec<String>,
        name: String,
    },
    Annotation,
}

struct Walk<'a> {
    checker: &'a mut AletheDocumentChecker,
    binders: &'a mut Vec<String>,
    pending: Vec<Frame>,
}

pub(super) fn check(
    checker: &mut AletheDocumentChecker,
    lexer: &mut Lexer<'_>,
    token: Tok,
    pos: Pos,
    binders: &mut Vec<String>,
    depth: usize,
) -> Result<(), AletheDefect> {
    let mark = binders.len();
    let mut walk = Walk {
        checker,
        binders,
        pending: Vec::new(),
    };
    let result = (|| {
        walk.term(lexer, token, pos, depth)?;
        while let Some(frame) = walk.pending.pop() {
            walk.resume(lexer, frame)?;
        }
        Ok(())
    })();
    // A failure inside a let RHS, sort, head or body cannot leak local names.
    walk.binders.truncate(mark);
    result
}

impl Walk<'_> {
    fn term(
        &mut self,
        lexer: &mut Lexer<'_>,
        token: Tok,
        pos: Pos,
        depth: usize,
    ) -> Result<(), AletheDefect> {
        check_depth(depth, pos)?;
        match token {
            Tok::Numeral(_) | Tok::Decimal(_) | Tok::StringLit(_) | Tok::BitVec(_) => Ok(()),
            Tok::Symbol(name) => self.checker.resolve_symbol(&name, pos, self.binders),
            Tok::Open => self.application(lexer, depth),
            Tok::Eof => Err(AletheDefect::UnexpectedEof {
                pos,
                expected: "a term",
            }),
            other => Err(unexpected(pos, "a term", other)),
        }
    }

    fn resume(&mut self, lexer: &mut Lexer<'_>, frame: Frame) -> Result<(), AletheDefect> {
        match frame {
            Frame::ReadTerm(depth) => {
                let (token, pos) = lexer.next_token()?;
                self.term(lexer, token, pos, depth)
            }
            Frame::Arguments {
                depth,
                count,
                arity,
            } => self.arguments(lexer, depth, count, arity),
            Frame::Qualified(depth) => self.qualified(lexer, depth),
            Frame::QualifiedTail => {
                self.checker.parse_sort(lexer)?;
                self.checker.expect_token(
                    lexer,
                    &Tok::Close,
                    "')' closing the qualified identifier",
                )
            }
            Frame::Close { mark, expected } => {
                self.binders.truncate(mark);
                self.checker.expect_token(lexer, &Tok::Close, expected)
            }
            Frame::LetBindings { depth, names } => self.let_bindings(lexer, depth, names),
            Frame::LetValue {
                depth,
                mut names,
                name,
            } => {
                self.checker
                    .expect_token(lexer, &Tok::Close, "')' closing the let binding")?;
                names.push(name);
                self.pending.push(Frame::LetBindings { depth, names });
                Ok(())
            }
            Frame::Annotation => self.annotation(lexer),
        }
    }

    fn application(&mut self, lexer: &mut Lexer<'_>, depth: usize) -> Result<(), AletheDefect> {
        let (head, pos) = lexer.next_token()?;
        let arity = match head {
            Tok::Symbol(name) => match name.as_str() {
                "let" => {
                    self.checker
                        .expect_token(lexer, &Tok::Open, "'(' opening the let bindings")?;
                    self.pending.push(Frame::LetBindings {
                        depth,
                        names: Vec::new(),
                    });
                    return Ok(());
                }
                "forall" | "exists" | "lambda" | "choice" => return self.binder(lexer, depth),
                "match" => return Err(AletheDefect::ForbiddenConstruct { pos, what: "match" }),
                "par" => return Err(AletheDefect::ForbiddenConstruct { pos, what: "par" }),
                "!" => {
                    self.pending.push(Frame::Annotation);
                    self.pending.push(Frame::ReadTerm(depth + 1));
                    return Ok(());
                }
                "_" => return self.checker.parse_indexed_tail(lexer, pos),
                "as" => {
                    self.pending.push(Frame::QualifiedTail);
                    self.pending.push(Frame::ReadTerm(depth + 1));
                    return Ok(());
                }
                "cl" => {
                    return Err(unexpected(
                        pos,
                        "a term (a nested 'cl' is not a term)",
                        Tok::Symbol(name),
                    ))
                }
                _ => {
                    self.checker.resolve_symbol(&name, pos, self.binders)?;
                    self.checker
                        .defines
                        .get(&name)
                        .copied()
                        .map(|arity| (arity, name, pos))
                }
            },
            Tok::Open => {
                self.pending.push(Frame::Arguments {
                    depth,
                    count: 0,
                    arity: None,
                });
                self.pending.push(Frame::Qualified(depth));
                return Ok(());
            }
            other => return Err(unexpected(pos, "an application head", other)),
        };
        self.pending.push(Frame::Arguments {
            depth,
            count: 0,
            arity,
        });
        Ok(())
    }

    fn arguments(
        &mut self,
        lexer: &mut Lexer<'_>,
        depth: usize,
        count: usize,
        arity: Arity,
    ) -> Result<(), AletheDefect> {
        let (token, pos) = lexer.next_token()?;
        if token == Tok::Close {
            if let Some((expected, name, pos)) = arity {
                if expected != count {
                    return Err(AletheDefect::UnexpectedToken {
                        pos,
                        expected: "the declared arity of a proof define-fun",
                        found: format!("{name} applied to {count} arguments (expects {expected})"),
                    });
                }
            }
            return Ok(());
        }
        if token == Tok::Eof {
            return Err(AletheDefect::UnexpectedEof {
                pos,
                expected: "')' closing the application",
            });
        }
        self.pending.push(Frame::Arguments {
            depth,
            count: count + 1,
            arity,
        });
        self.term(lexer, token, pos, depth + 1)
    }

    fn qualified(&mut self, lexer: &mut Lexer<'_>, depth: usize) -> Result<(), AletheDefect> {
        let (token, pos) = lexer.next_token()?;
        check_depth(depth, pos)?;
        match token {
            Tok::Symbol(name) if name == "_" => self.checker.parse_indexed_tail(lexer, pos),
            Tok::Symbol(name) if name == "lambda" => self.binder(lexer, depth),
            Tok::Symbol(name) if name == "as" => {
                let (inner, pos) = lexer.next_token()?;
                self.pending.push(Frame::QualifiedTail);
                match inner {
                    Tok::Symbol(name) if name == "const" => Ok(()),
                    Tok::Symbol(name) => self.checker.resolve_symbol(&name, pos, self.binders),
                    Tok::Open => {
                        self.pending.push(Frame::Qualified(depth + 1));
                        Ok(())
                    }
                    other => Err(unexpected(pos, "an identifier after 'as'", other)),
                }
            }
            other => Err(unexpected(
                pos,
                "'_', 'as' or 'lambda' in an application head",
                other,
            )),
        }
    }
}

fn check_depth(depth: usize, pos: Pos) -> Result<(), AletheDefect> {
    if depth > MAX_TERM_DEPTH {
        Err(AletheDefect::TermTooDeep { pos })
    } else {
        Ok(())
    }
}

fn unexpected(pos: Pos, expected: &'static str, token: Tok) -> AletheDefect {
    AletheDefect::UnexpectedToken {
        pos,
        expected,
        found: token.describe(),
    }
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `spec.rs`; keep parser items in `ay_search::spec`.

#[derive(Debug, Clone, Copy)]
enum ParsedRelation {
    Eq,
    Le,
    Ge,
    Ne,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum TokenKind {
    Identifier(String),
    Integer(i128),
    Plus,
    Minus,
    Star,
    LeftParen,
    RightParen,
    Eq,
    Ne,
    Le,
    Ge,
    End,
}

#[derive(Debug, Clone)]
struct Token {
    kind: TokenKind,
    position: usize,
}

struct Parser<'a> {
    tokens: Vec<Token>,
    cursor: usize,
    model: &'a Model,
    /// Current `(`-nesting depth. Bounded so hostile input cannot overflow the
    /// stack through the parse_atom -> parse_sum recursion (this parser is
    /// reachable from the public `ay_search_solve_json` C ABI).
    depth: usize,
}

/// Maximum `(`-nesting depth accepted by the spec expression parser. Any real
/// linear-expression spec is a handful of levels; the bound exists so a
/// stranger's input fails with a parse error instead of a stack overflow.
const MAX_EXPR_DEPTH: usize = 128;

impl<'a> Parser<'a> {
    fn new(input: &str, model: &'a Model) -> Result<Self, SearchError> {
        if input.len() > MAX_EXPRESSION_BYTES {
            return Err(SearchError::ExpressionLimit {
                resource: "input byte length",
                limit: MAX_EXPRESSION_BYTES,
            });
        }
        Ok(Self {
            tokens: lex(input)?,
            cursor: 0,
            model,
            depth: 0,
        })
    }

    fn parse_sum(&mut self) -> Result<LinearExpr, SearchError> {
        let mut expression = self.parse_product()?;
        loop {
            match self.peek().kind {
                TokenKind::Plus => {
                    self.cursor += 1;
                    expression = expression + self.parse_product()?;
                }
                TokenKind::Minus => {
                    self.cursor += 1;
                    expression = expression - self.parse_product()?;
                }
                _ => return Ok(expression),
            }
        }
    }

    fn parse_product(&mut self) -> Result<LinearExpr, SearchError> {
        let mut expression = self.parse_unary()?;
        while matches!(self.peek().kind, TokenKind::Star) {
            self.cursor += 1;
            let rhs = self.parse_unary()?;
            // `constant_value` intentionally exposes the stored value even
            // after checked arithmetic records overflow. Multiplication may
            // use that value to preserve the expression shape, but it must
            // never launder the overflow bit by returning the other operand.
            // Without this taint, `((i128::MAX + 1) * x) - i128::MAX*x - x`
            // incorrectly normalizes to `-x` instead of failing closed.
            let overflowed = expression.overflowed || rhs.overflowed;
            expression = match (expression.constant_value(), rhs.constant_value()) {
                (Some(left), _) => rhs.scaled(left),
                (_, Some(right)) => expression.scaled(right),
                (None, None) => return Err(SearchError::NonlinearExpression),
            };
            expression.overflowed |= overflowed;
        }
        Ok(expression)
    }

    fn parse_unary(&mut self) -> Result<LinearExpr, SearchError> {
        // Iterative on purpose: a recursive descent here means one stack frame
        // per leading `+`/`-`, and a long `----…x` chain from untrusted input
        // overflows the stack (observed at ~42k frames via the C ABI). Fold
        // the whole prefix into a sign first.
        let mut negate = false;
        loop {
            match self.peek().kind {
                TokenKind::Plus => self.cursor += 1,
                TokenKind::Minus => {
                    negate = !negate;
                    self.cursor += 1;
                }
                _ => break,
            }
        }
        let atom = self.parse_atom()?;
        Ok(if negate { -atom } else { atom })
    }

    fn parse_atom(&mut self) -> Result<LinearExpr, SearchError> {
        let token = self.peek().clone();
        match token.kind {
            TokenKind::Integer(value) => {
                self.cursor += 1;
                Ok(LinearExpr {
                    terms: BTreeMap::new(),
                    constant: value,
                    overflowed: false,
                })
            }
            TokenKind::Identifier(name) => {
                self.cursor += 1;
                Ok(LinearExpr::from(resolve_variable(&name, self.model)?))
            }
            TokenKind::LeftParen => {
                if self.depth >= MAX_EXPR_DEPTH {
                    return Err(SearchError::ExpressionLimit {
                        resource: "parenthesis nesting depth",
                        limit: MAX_EXPR_DEPTH,
                    });
                }
                self.depth += 1;
                self.cursor += 1;
                let expression = self.parse_sum();
                self.depth -= 1;
                let expression = expression?;
                if !matches!(self.peek().kind, TokenKind::RightParen) {
                    return Err(parse_error(self.peek(), "expected `)`"));
                }
                self.cursor += 1;
                Ok(expression)
            }
            _ => Err(parse_error(&token, "expected a number, variable, or `(`")),
        }
    }

    fn peek(&self) -> &Token {
        &self.tokens[self.cursor]
    }
}

fn parse_linear_expression(input: &str, model: &Model) -> Result<LinearExpr, SearchError> {
    let mut parser = Parser::new(input, model)?;
    let expression = parser.parse_sum()?;
    if !matches!(parser.peek().kind, TokenKind::End) {
        return Err(parse_error(
            parser.peek(),
            "unexpected token after expression",
        ));
    }
    Ok(expression)
}

fn parse_relation(
    input: &str,
    model: &Model,
) -> Result<(LinearExpr, ParsedRelation, LinearExpr), SearchError> {
    let mut parser = Parser::new(input, model)?;
    let lhs = parser.parse_sum()?;
    let relation = match parser.peek().kind {
        TokenKind::Eq => ParsedRelation::Eq,
        TokenKind::Ne => ParsedRelation::Ne,
        TokenKind::Le => ParsedRelation::Le,
        TokenKind::Ge => ParsedRelation::Ge,
        TokenKind::End => return Err(SearchError::MissingRelation),
        _ => return Err(parse_error(parser.peek(), "expected ==, !=, <=, or >=")),
    };
    parser.cursor += 1;
    let rhs = parser.parse_sum()?;
    if !matches!(parser.peek().kind, TokenKind::End) {
        return Err(parse_error(parser.peek(), "only one relation is allowed"));
    }
    Ok((lhs, relation, rhs))
}

fn lex(input: &str) -> Result<Vec<Token>, SearchError> {
    let bytes = input.as_bytes();
    let mut tokens = Vec::new();
    let mut cursor = 0;
    while cursor < bytes.len() {
        if bytes[cursor].is_ascii_whitespace() {
            cursor += 1;
            continue;
        }
        let position = cursor;
        let kind = match bytes[cursor] {
            b'+' => {
                cursor += 1;
                TokenKind::Plus
            }
            b'-' => {
                cursor += 1;
                TokenKind::Minus
            }
            b'*' => {
                cursor += 1;
                TokenKind::Star
            }
            b'(' => {
                cursor += 1;
                TokenKind::LeftParen
            }
            b')' => {
                cursor += 1;
                TokenKind::RightParen
            }
            b'=' if bytes.get(cursor + 1) == Some(&b'=') => {
                cursor += 2;
                TokenKind::Eq
            }
            b'!' if bytes.get(cursor + 1) == Some(&b'=') => {
                cursor += 2;
                TokenKind::Ne
            }
            b'<' if bytes.get(cursor + 1) == Some(&b'=') => {
                cursor += 2;
                TokenKind::Le
            }
            b'>' if bytes.get(cursor + 1) == Some(&b'=') => {
                cursor += 2;
                TokenKind::Ge
            }
            byte if byte.is_ascii_digit() => {
                let start = cursor;
                while cursor < bytes.len() && bytes[cursor].is_ascii_digit() {
                    cursor += 1;
                }
                let digits = &input[start..cursor];
                let value = digits
                    .parse::<i128>()
                    .map_err(|_| SearchError::ExpressionParse {
                        position: start,
                        message: "integer literal is too large".to_owned(),
                    })?;
                TokenKind::Integer(value)
            }
            byte if byte == b'_' || byte.is_ascii_alphabetic() => {
                let start = cursor;
                cursor += 1;
                while cursor < bytes.len()
                    && (bytes[cursor] == b'_' || bytes[cursor].is_ascii_alphanumeric())
                {
                    cursor += 1;
                }
                TokenKind::Identifier(input[start..cursor].to_owned())
            }
            _ => {
                return Err(SearchError::ExpressionParse {
                    position,
                    message: "unsupported character".to_owned(),
                });
            }
        };
        if tokens.len() >= MAX_EXPRESSION_TOKENS {
            return Err(SearchError::ExpressionLimit {
                resource: "token count",
                limit: MAX_EXPRESSION_TOKENS,
            });
        }
        tokens.push(Token { kind, position });
    }
    tokens.push(Token {
        kind: TokenKind::End,
        position: input.len(),
    });
    Ok(tokens)
}

fn parse_error(token: &Token, message: &str) -> SearchError {
    SearchError::ExpressionParse {
        position: token.position,
        message: message.to_owned(),
    }
}

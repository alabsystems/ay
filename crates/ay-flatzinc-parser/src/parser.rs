// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
// FlatZinc 2.8.5 recursive descent parser — model-level parsing

use crate::ast::*;
use crate::error::ParseError;
use crate::lexer::{Lexer, Located, Token};

pub struct Parser<'a> {
    tokens: Vec<Located>,
    pos: usize,
    _input: &'a str,
}

impl<'a> Parser<'a> {
    pub fn new(input: &'a str) -> Result<Self, ParseError> {
        let mut lexer = Lexer::new(input);
        let tokens = lexer.tokenize_all()?;
        Ok(Self {
            tokens,
            pos: 0,
            _input: input,
        })
    }

    pub(crate) fn peek(&self) -> &Token {
        self.tokens
            .get(self.pos)
            .map(|l| &l.token)
            .unwrap_or(&Token::Eof)
    }

    pub(crate) fn loc(&self) -> (usize, usize) {
        self.tokens
            .get(self.pos)
            .map(|l| (l.line, l.col))
            .unwrap_or((0, 0))
    }

    pub(crate) fn advance(&mut self) -> &Token {
        let t = self
            .tokens
            .get(self.pos)
            .map(|l| &l.token)
            .unwrap_or(&Token::Eof);
        if self.pos < self.tokens.len() {
            self.pos += 1;
        }
        t
    }

    pub(crate) fn expect(&mut self, expected: &Token) -> Result<(), ParseError> {
        let (line, col) = self.loc();
        let tok = self.advance().clone();
        if std::mem::discriminant(&tok) == std::mem::discriminant(expected) {
            Ok(())
        } else {
            Err(ParseError::UnexpectedToken {
                line,
                col,
                expected: format!("{expected:?}"),
                found: format!("{tok:?}"),
            })
        }
    }

    pub(crate) fn expect_semicolon(&mut self) -> Result<(), ParseError> {
        self.expect(&Token::Semicolon)
    }

    pub(crate) fn expect_ident(&mut self) -> Result<String, ParseError> {
        let (line, col) = self.loc();
        let tok = self.advance().clone();
        match tok {
            Token::Ident(s) => Ok(s),
            _ => Err(ParseError::UnexpectedToken {
                line,
                col,
                expected: "identifier".to_string(),
                found: format!("{tok:?}"),
            }),
        }
    }

    pub(crate) fn expect_int(&mut self) -> Result<i64, ParseError> {
        let (line, col) = self.loc();
        let tok = self.advance().clone();
        match tok {
            Token::IntLit(v) => Ok(v),
            _ => Err(ParseError::UnexpectedToken {
                line,
                col,
                expected: "integer".to_string(),
                found: format!("{tok:?}"),
            }),
        }
    }

    pub(crate) fn unexpected<T>(&self, expected: &str) -> Result<T, ParseError> {
        let (line, col) = self.loc();
        let tok = self.peek().clone();
        Err(ParseError::UnexpectedToken {
            line,
            col,
            expected: expected.to_string(),
            found: format!("{tok:?}"),
        })
    }

    /// Parse a complete FlatZinc model.
    pub fn parse_model(&mut self) -> Result<FznModel, ParseError> {
        let mut predicates = Vec::new();
        let mut parameters = Vec::new();
        let mut variables = Vec::new();
        let mut constraints = Vec::new();
        let mut solve = None;

        loop {
            match self.peek() {
                Token::Eof => break,
                Token::Predicate => predicates.push(self.parse_predicate()?),
                Token::Constraint => constraints.push(self.parse_constraint()?),
                Token::Solve => {
                    let (line, _) = self.loc();
                    if solve.is_some() {
                        return Err(ParseError::DuplicateSolveItem { line });
                    }
                    solve = Some(self.parse_solve()?);
                }
                Token::Var => variables.push(self.parse_var_decl()?),
                Token::Array => {
                    self.parse_array_decl(&mut parameters, &mut variables)?;
                }
                Token::Bool
                | Token::Int
                | Token::Float
                | Token::Set
                | Token::Par
                | Token::IntLit(_)
                | Token::LBrace => {
                    parameters.push(self.parse_par_decl()?);
                }
                _ => return self.unexpected("declaration, constraint, or solve"),
            }
        }

        let solve = solve.ok_or(ParseError::MissingSolveItem)?;
        Ok(FznModel {
            predicates,
            parameters,
            variables,
            constraints,
            solve,
        })
    }

    fn parse_predicate(&mut self) -> Result<PredicateDecl, ParseError> {
        self.expect(&Token::Predicate)?;
        let id = self.expect_ident()?;
        self.expect(&Token::LParen)?;
        let params = self.parse_comma_list(Self::parse_predicate_param)?;
        self.expect(&Token::RParen)?;
        self.expect_semicolon()?;
        Ok(PredicateDecl { id, params })
    }

    fn parse_predicate_param(&mut self) -> Result<PredicateParam, ParseError> {
        let ty = self.parse_param_type()?;
        self.expect(&Token::Colon)?;
        let id = self.expect_ident()?;
        Ok(PredicateParam { ty, id })
    }

    fn parse_comma_list<T>(
        &mut self,
        parse_item: fn(&mut Self) -> Result<T, ParseError>,
    ) -> Result<Vec<T>, ParseError> {
        // Caller handles empty check via surrounding delimiters
        let mut items = Vec::new();
        if *self.peek() != Token::RParen {
            items.push(parse_item(self)?);
            while *self.peek() == Token::Comma {
                self.advance();
                items.push(parse_item(self)?);
            }
        }
        Ok(items)
    }

    fn parse_par_decl(&mut self) -> Result<ParDecl, ParseError> {
        let ty = self.parse_fzn_type(false)?;
        self.expect(&Token::Colon)?;
        let id = self.expect_ident()?;
        let annotations = self.parse_annotations()?;
        self.expect(&Token::Assign)?;
        let value = self.parse_expr()?;
        self.expect_semicolon()?;
        Ok(ParDecl {
            ty,
            id,
            value,
            annotations,
        })
    }

    fn parse_var_decl(&mut self) -> Result<VarDecl, ParseError> {
        self.expect(&Token::Var)?;
        let ty = self.parse_fzn_type(true)?;
        self.expect(&Token::Colon)?;
        let id = self.expect_ident()?;
        let annotations = self.parse_annotations()?;
        let value = if *self.peek() == Token::Assign {
            self.advance();
            Some(self.parse_expr()?)
        } else {
            None
        };
        self.expect_semicolon()?;
        Ok(VarDecl {
            ty,
            id,
            value,
            annotations,
        })
    }

    fn parse_array_decl(
        &mut self,
        parameters: &mut Vec<ParDecl>,
        variables: &mut Vec<VarDecl>,
    ) -> Result<(), ParseError> {
        self.expect(&Token::Array)?;
        self.expect(&Token::LBracket)?;
        let index = self.parse_index_set()?;
        self.expect(&Token::RBracket)?;
        self.expect(&Token::Of)?;

        let is_var = *self.peek() == Token::Var;
        if is_var {
            self.advance();
        }

        let elem_ty = self.parse_fzn_type(is_var)?;
        let ty = FznType::ArrayOf {
            index,
            elem: Box::new(elem_ty),
        };
        self.expect(&Token::Colon)?;
        let id = self.expect_ident()?;
        let annotations = self.parse_annotations()?;

        if is_var {
            let value = if *self.peek() == Token::Assign {
                self.advance();
                Some(self.parse_expr()?)
            } else {
                None
            };
            self.expect_semicolon()?;
            variables.push(VarDecl {
                ty,
                id,
                value,
                annotations,
            });
        } else {
            self.expect(&Token::Assign)?;
            let value = self.parse_expr()?;
            self.expect_semicolon()?;
            parameters.push(ParDecl {
                ty,
                id,
                value,
                annotations,
            });
        }
        Ok(())
    }

    fn parse_constraint(&mut self) -> Result<ConstraintItem, ParseError> {
        self.expect(&Token::Constraint)?;
        let id = self.expect_ident()?;
        self.expect(&Token::LParen)?;
        let mut args = Vec::new();
        if *self.peek() != Token::RParen {
            args.push(self.parse_expr()?);
            while *self.peek() == Token::Comma {
                self.advance();
                args.push(self.parse_expr()?);
            }
        }
        self.expect(&Token::RParen)?;
        let annotations = self.parse_annotations()?;
        self.expect_semicolon()?;
        Ok(ConstraintItem {
            id,
            args,
            annotations,
        })
    }

    fn parse_solve(&mut self) -> Result<SolveItem, ParseError> {
        self.expect(&Token::Solve)?;
        let annotations = self.parse_annotations()?;
        let kind = match self.peek() {
            Token::Satisfy => {
                self.advance();
                SolveKind::Satisfy
            }
            Token::Minimize => {
                self.advance();
                SolveKind::Minimize(self.parse_expr()?)
            }
            Token::Maximize => {
                self.advance();
                SolveKind::Maximize(self.parse_expr()?)
            }
            _ => return self.unexpected("satisfy, minimize, or maximize"),
        };
        self.expect_semicolon()?;
        Ok(SolveItem { kind, annotations })
    }

    pub(crate) fn parse_annotations(&mut self) -> Result<Vec<Annotation>, ParseError> {
        let mut anns = Vec::new();
        while *self.peek() == Token::ColonColon {
            self.advance();
            anns.push(self.parse_annotation()?);
        }
        Ok(anns)
    }

    fn parse_annotation(&mut self) -> Result<Annotation, ParseError> {
        let id = self.expect_ident()?;
        if *self.peek() == Token::LParen {
            self.advance();
            let mut args = Vec::new();
            if *self.peek() != Token::RParen {
                args.push(self.parse_ann_expr()?);
                while *self.peek() == Token::Comma {
                    self.advance();
                    args.push(self.parse_ann_expr()?);
                }
            }
            self.expect(&Token::RParen)?;
            Ok(Annotation::Call(id, args))
        } else {
            Ok(Annotation::Atom(id))
        }
    }
}

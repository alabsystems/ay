// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
// FlatZinc type and expression parsing (split from parser.rs)

use crate::ast::*;
use crate::error::ParseError;
use crate::lexer::Token;
use crate::parser::Parser;

impl Parser<'_> {
    pub(crate) fn parse_param_type(&mut self) -> Result<ParamType, ParseError> {
        match self.peek() {
            Token::Var => {
                self.advance();
                self.parse_var_param_type()
            }
            Token::Array => {
                self.advance();
                self.expect(&Token::LBracket)?;
                let index = self.parse_index_set()?;
                self.expect(&Token::RBracket)?;
                self.expect(&Token::Of)?;
                if *self.peek() == Token::Var {
                    self.advance();
                    let elem = self.parse_var_param_type()?;
                    Ok(ParamType::VarArrayOf {
                        index,
                        elem: Box::new(elem),
                    })
                } else {
                    let elem = self.parse_base_param_type()?;
                    Ok(ParamType::ArrayOf {
                        index,
                        elem: Box::new(elem),
                    })
                }
            }
            _ => self.parse_base_param_type(),
        }
    }

    fn parse_var_param_type(&mut self) -> Result<ParamType, ParseError> {
        match self.peek() {
            Token::Bool => {
                self.advance();
                Ok(ParamType::VarBool)
            }
            Token::Int => {
                self.advance();
                Ok(ParamType::VarInt)
            }
            Token::Float => {
                self.advance();
                Ok(ParamType::VarFloat)
            }
            Token::Set => {
                self.advance();
                self.expect(&Token::Of)?;
                match self.peek() {
                    Token::IntLit(_) => {
                        let lo = self.expect_int()?;
                        self.expect(&Token::DotDot)?;
                        let hi = self.expect_int()?;
                        Ok(ParamType::VarSetOfIntRange(lo, hi))
                    }
                    _ => {
                        self.expect(&Token::Int)?;
                        Ok(ParamType::VarSetOfInt)
                    }
                }
            }
            Token::IntLit(_) => {
                let lo = self.expect_int()?;
                self.expect(&Token::DotDot)?;
                let hi = self.expect_int()?;
                Ok(ParamType::VarIntRange(lo, hi))
            }
            _ => {
                let (line, col) = self.loc();
                let tok = self.peek().clone();
                Err(ParseError::UnexpectedToken {
                    line,
                    col,
                    expected: "var type (bool, int, float, set, range)".to_string(),
                    found: format!("{tok:?}"),
                })
            }
        }
    }

    fn parse_base_param_type(&mut self) -> Result<ParamType, ParseError> {
        match self.peek() {
            Token::Bool => {
                self.advance();
                Ok(ParamType::Bool)
            }
            Token::Int => {
                self.advance();
                Ok(ParamType::Int)
            }
            Token::Float => {
                self.advance();
                Ok(ParamType::Float)
            }
            Token::Set => {
                self.advance();
                self.expect(&Token::Of)?;
                match self.peek() {
                    Token::IntLit(_) => {
                        let lo = self.expect_int()?;
                        self.expect(&Token::DotDot)?;
                        let hi = self.expect_int()?;
                        Ok(ParamType::SetOfIntRange(lo, hi))
                    }
                    _ => {
                        self.expect(&Token::Int)?;
                        Ok(ParamType::SetOfInt)
                    }
                }
            }
            Token::IntLit(_) => {
                let lo = self.expect_int()?;
                self.expect(&Token::DotDot)?;
                let hi = self.expect_int()?;
                Ok(ParamType::IntRange(lo, hi))
            }
            _ => self.unexpected("type (bool, int, float, set, range)"),
        }
    }

    pub(crate) fn parse_index_set(&mut self) -> Result<IndexSet, ParseError> {
        match self.peek() {
            Token::Int => {
                self.advance();
                Ok(IndexSet::Int)
            }
            Token::IntLit(_) => {
                let lo = self.expect_int()?;
                self.expect(&Token::DotDot)?;
                let hi = self.expect_int()?;
                Ok(IndexSet::Range(lo, hi))
            }
            _ => self.unexpected("index set (int or range)"),
        }
    }

    pub(crate) fn parse_fzn_type(&mut self, _is_var: bool) -> Result<FznType, ParseError> {
        match self.peek() {
            Token::Bool => {
                self.advance();
                Ok(FznType::Bool)
            }
            Token::Int => {
                self.advance();
                Ok(FznType::Int)
            }
            Token::Float => {
                self.advance();
                Ok(FznType::Float)
            }
            Token::Set => {
                self.advance();
                self.expect(&Token::Of)?;
                match self.peek() {
                    Token::IntLit(_) | Token::LBrace => self.parse_set_domain(),
                    _ => {
                        self.expect(&Token::Int)?;
                        Ok(FznType::SetOfInt)
                    }
                }
            }
            Token::IntLit(_) => {
                let lo = self.expect_int()?;
                self.expect(&Token::DotDot)?;
                let hi = self.expect_int()?;
                Ok(FznType::IntRange(lo, hi))
            }
            Token::LBrace => self.parse_int_set_type(),
            _ => self.unexpected("type"),
        }
    }

    fn parse_int_set_type(&mut self) -> Result<FznType, ParseError> {
        self.advance(); // consume '{'
        let mut vals = Vec::new();
        if *self.peek() != Token::RBrace {
            vals.push(self.expect_int()?);
            while *self.peek() == Token::Comma {
                self.advance();
                vals.push(self.expect_int()?);
            }
        }
        self.expect(&Token::RBrace)?;
        Ok(FznType::IntSet(vals))
    }

    fn parse_set_domain(&mut self) -> Result<FznType, ParseError> {
        match self.peek() {
            Token::IntLit(_) => {
                let lo = self.expect_int()?;
                self.expect(&Token::DotDot)?;
                let hi = self.expect_int()?;
                Ok(FznType::SetOfIntRange(lo, hi))
            }
            Token::LBrace => {
                self.advance();
                let mut vals = Vec::new();
                if *self.peek() != Token::RBrace {
                    vals.push(self.expect_int()?);
                    while *self.peek() == Token::Comma {
                        self.advance();
                        vals.push(self.expect_int()?);
                    }
                }
                self.expect(&Token::RBrace)?;
                Ok(FznType::SetOfIntSet(vals))
            }
            _ => self.unexpected("set domain"),
        }
    }

    /// Parse annotation argument expression (can contain nested annotations).
    ///
    /// Unlike `parse_expr()`, this recognizes `ident(...)` as annotation
    /// function calls and `[...]` as arrays whose elements may themselves
    /// be annotation expressions (e.g. `seq_search([int_search(x, ...)])`).
    pub(crate) fn parse_ann_expr(&mut self) -> Result<Expr, ParseError> {
        match self.peek().clone() {
            Token::Ident(ref s) => {
                let s = s.clone();
                self.advance();
                if *self.peek() == Token::LParen {
                    self.advance();
                    let args = self.parse_comma_list_ann()?;
                    self.expect(&Token::RParen)?;
                    Ok(Expr::Annotation(Box::new(Annotation::Call(s, args))))
                } else if *self.peek() == Token::LBracket {
                    self.advance();
                    let idx = self.parse_expr()?;
                    self.expect(&Token::RBracket)?;
                    Ok(Expr::ArrayAccess(s, Box::new(idx)))
                } else {
                    Ok(Expr::Ident(s))
                }
            }
            Token::LBracket => {
                self.advance(); // consume '['
                let mut elems = Vec::new();
                if *self.peek() != Token::RBracket {
                    elems.push(self.parse_ann_expr()?);
                    while *self.peek() == Token::Comma {
                        self.advance();
                        elems.push(self.parse_ann_expr()?);
                    }
                }
                self.expect(&Token::RBracket)?;
                Ok(Expr::ArrayLit(elems))
            }
            _ => self.parse_expr(),
        }
    }

    fn parse_comma_list_ann(&mut self) -> Result<Vec<Expr>, ParseError> {
        let mut items = Vec::new();
        if *self.peek() != Token::RParen {
            items.push(self.parse_ann_expr()?);
            while *self.peek() == Token::Comma {
                self.advance();
                items.push(self.parse_ann_expr()?);
            }
        }
        Ok(items)
    }

    /// Parse an expression.
    pub fn parse_expr(&mut self) -> Result<Expr, ParseError> {
        match self.peek().clone() {
            Token::True => {
                self.advance();
                Ok(Expr::Bool(true))
            }
            Token::False => {
                self.advance();
                Ok(Expr::Bool(false))
            }
            Token::IntLit(v) => {
                self.advance();
                if *self.peek() == Token::DotDot {
                    self.advance();
                    let hi = self.expect_int()?;
                    Ok(Expr::IntRange(v, hi))
                } else {
                    Ok(Expr::Int(v))
                }
            }
            Token::FloatLit(v) => {
                self.advance();
                Ok(Expr::Float(v))
            }
            Token::StringLit(ref s) => {
                let s = s.clone();
                self.advance();
                Ok(Expr::Str(s))
            }
            Token::Ident(ref s) => {
                let s = s.clone();
                self.advance();
                if *self.peek() == Token::LBracket {
                    self.advance();
                    let idx = self.parse_expr()?;
                    self.expect(&Token::RBracket)?;
                    Ok(Expr::ArrayAccess(s, Box::new(idx)))
                } else {
                    Ok(Expr::Ident(s))
                }
            }
            Token::LBracket => self.parse_array_lit(),
            Token::LBrace => self.parse_set_lit(),
            _ => self.unexpected("expression"),
        }
    }

    fn parse_array_lit(&mut self) -> Result<Expr, ParseError> {
        self.advance(); // consume '['
        let mut elems = Vec::new();
        if *self.peek() != Token::RBracket {
            elems.push(self.parse_expr()?);
            while *self.peek() == Token::Comma {
                self.advance();
                elems.push(self.parse_expr()?);
            }
        }
        self.expect(&Token::RBracket)?;
        Ok(Expr::ArrayLit(elems))
    }

    fn parse_set_lit(&mut self) -> Result<Expr, ParseError> {
        self.advance(); // consume '{'
        if *self.peek() == Token::RBrace {
            self.advance();
            return Ok(Expr::EmptySet);
        }
        let mut elems = Vec::new();
        elems.push(self.parse_expr()?);
        while *self.peek() == Token::Comma {
            self.advance();
            elems.push(self.parse_expr()?);
        }
        self.expect(&Token::RBrace)?;
        Ok(Expr::SetLit(elems))
    }
}

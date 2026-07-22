// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
// FlatZinc 2.8.5 AST types

/// A complete FlatZinc model.
#[derive(Debug, Clone, PartialEq)]
pub struct FznModel {
    pub predicates: Vec<PredicateDecl>,
    pub parameters: Vec<ParDecl>,
    pub variables: Vec<VarDecl>,
    pub constraints: Vec<ConstraintItem>,
    pub solve: SolveItem,
}

/// Predicate declaration: `predicate <id>(<params>);`
#[derive(Debug, Clone, PartialEq)]
pub struct PredicateDecl {
    pub id: String,
    pub params: Vec<PredicateParam>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct PredicateParam {
    pub ty: ParamType,
    pub id: String,
}

/// Parameter type in predicate declarations.
#[derive(Debug, Clone, PartialEq)]
pub enum ParamType {
    Bool,
    Int,
    Float,
    IntRange(i64, i64),
    FloatRange(f64, f64),
    SetOfInt,
    SetOfIntRange(i64, i64),
    ArrayOf { index: IndexSet, elem: Box<Self> },
    VarBool,
    VarInt,
    VarFloat,
    VarIntRange(i64, i64),
    VarFloatRange(f64, f64),
    VarSetOfInt,
    VarSetOfIntRange(i64, i64),
    VarArrayOf { index: IndexSet, elem: Box<Self> },
}

/// Index set for arrays: `1..N` or `int`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IndexSet {
    Range(i64, i64),
    Int,
}

/// FlatZinc type for parameters and variables.
#[derive(Debug, Clone, PartialEq)]
pub enum FznType {
    Bool,
    Int,
    Float,
    IntRange(i64, i64),
    FloatRange(f64, f64),
    IntSet(Vec<i64>),
    SetOfInt,
    SetOfIntRange(i64, i64),
    SetOfIntSet(Vec<i64>),
    ArrayOf { index: IndexSet, elem: Box<Self> },
}

/// Parameter declaration: `<type>: <id> = <expr>;`
#[derive(Debug, Clone, PartialEq)]
pub struct ParDecl {
    pub ty: FznType,
    pub id: String,
    pub value: Expr,
    pub annotations: Vec<Annotation>,
}

/// Variable declaration: `var <type>: <id> [= <expr>] <annotations>;`
#[derive(Debug, Clone, PartialEq)]
pub struct VarDecl {
    pub ty: FznType,
    pub id: String,
    pub value: Option<Expr>,
    pub annotations: Vec<Annotation>,
}

/// Constraint item: `constraint <id>(<args>) <annotations>;`
#[derive(Debug, Clone, PartialEq)]
pub struct ConstraintItem {
    pub id: String,
    pub args: Vec<Expr>,
    pub annotations: Vec<Annotation>,
}

/// Solve item.
#[derive(Debug, Clone, PartialEq)]
pub struct SolveItem {
    pub kind: SolveKind,
    pub annotations: Vec<Annotation>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum SolveKind {
    Satisfy,
    Minimize(Expr),
    Maximize(Expr),
}

/// Annotation: `:: <id>` or `:: <id>(<args>)`.
#[derive(Debug, Clone, PartialEq)]
pub enum Annotation {
    Atom(String),
    Call(String, Vec<Expr>),
}

/// Expression (literals, identifiers, arrays, sets).
#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Bool(bool),
    Int(i64),
    Float(f64),
    Str(String),
    Ident(String),
    ArrayAccess(String, Box<Self>),
    ArrayLit(Vec<Self>),
    SetLit(Vec<Self>),
    IntRange(i64, i64),
    EmptySet,
    Annotation(Box<Annotation>),
}

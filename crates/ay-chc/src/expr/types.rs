// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Core CHC expression types.
//!
//! Extracted from `mod.rs` for code health (#5970).

use std::fmt;
use std::sync::Arc;

pub use super::datatype_identity::{ChcDtConstructors, ChcDtId};
use crate::PredicateId;

/// A selector (field) in a datatype constructor.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ChcDtSelector {
    pub name: String,
    pub sort: ChcSort,
}

/// A constructor in a datatype definition.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ChcDtConstructor {
    pub name: String,
    pub selectors: Vec<ChcDtSelector>,
}

/// Sort (type) of expressions
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[non_exhaustive]
pub enum ChcSort {
    Bool,
    Int,
    Real,
    BitVec(u32),
    /// Array sort: (Array key_sort value_sort)
    Array(Box<Self>, Box<Self>),
    /// Uninterpreted sort
    Uninterpreted(String),
    /// Algebraic datatype with constructor/selector/tester metadata.
    ///
    /// The constructors are hash-consed and identified by content
    /// ([`ChcDtConstructors`]): a copy shares them, and `Eq`, `Hash` and `Ord`
    /// cost the name plus `O(1)`, however deeply other datatypes nest inside.
    Datatype {
        name: String,
        constructors: ChcDtConstructors,
    },
}

impl fmt::Display for ChcSort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Bool => write!(f, "Bool"),
            Self::Int => write!(f, "Int"),
            Self::Real => write!(f, "Real"),
            Self::BitVec(w) => write!(f, "(_ BitVec {w})"),
            Self::Array(k, v) => write!(f, "(Array {k} {v})"),
            Self::Uninterpreted(name) | Self::Datatype { name, .. } => write!(f, "{name}"),
        }
    }
}

impl ChcSort {
    /// Short symbol-safe tag used by [`ChcVar::sort_qualified_name`]: `Bool`,
    /// `Int`, `Real`, `BV<w>`, and a letters/digits/underscore rendering of
    /// compound sorts (`ArrayIntInt`).
    pub fn qualifier_tag(&self) -> String {
        match self {
            Self::Bool => "Bool".to_string(),
            Self::Int => "Int".to_string(),
            Self::Real => "Real".to_string(),
            Self::BitVec(w) => format!("BV{w}"),
            other => other
                .to_string()
                .chars()
                .filter(|c| c.is_ascii_alphanumeric() || *c == '_')
                .collect(),
        }
    }
}

// ============================================================================
// From implementations for Sort conversions (#1626)
// ============================================================================

use ay_core::Sort as CoreSort;

impl From<CoreSort> for ChcSort {
    fn from(s: CoreSort) -> Self {
        crate::term_bridge::sort::core_sort_to_chc_lossy(&s)
    }
}

impl From<ChcSort> for CoreSort {
    fn from(s: ChcSort) -> Self {
        crate::term_bridge::sort::chc_sort_to_core(&s)
    }
}

/// A variable in CHC expressions
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ChcVar {
    pub name: String,
    pub sort: ChcSort,
}

impl ChcVar {
    pub fn new(name: impl Into<String>, sort: ChcSort) -> Self {
        Self {
            name: name.into(),
            sort,
        }
    }

    /// `name!<tag>` — the sort-qualified spelling a text script uses when
    /// two same-named variables of different sorts share one query (Rung 0,
    /// see `crate::smt::sort_unique`). `!` is a legal SMT-LIB simple-symbol
    /// character, so the name round-trips through `get-model` unchanged.
    pub fn sort_qualified_name(&self) -> String {
        format!("{}!{}", self.name, self.sort.qualifier_tag())
    }

    /// Check if this is a primed variable (ends with ')
    pub fn is_primed(&self) -> bool {
        self.name.ends_with('\'')
    }

    /// Get the base name (without prime suffix)
    pub fn base_name(&self) -> &str {
        if self.is_primed() {
            &self.name[..self.name.len() - 1]
        } else {
            &self.name
        }
    }

    /// Create a primed version of this variable
    pub fn primed(&self) -> Self {
        if self.is_primed() {
            self.clone()
        } else {
            Self {
                name: format!("{}'", self.name),
                sort: self.sort.clone(),
            }
        }
    }

    /// Create an unprimed version of this variable
    pub fn unprimed(&self) -> Self {
        Self {
            name: self.base_name().to_string(),
            sort: self.sort.clone(),
        }
    }
}

impl fmt::Display for ChcVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

/// Operations in CHC expressions
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[non_exhaustive]
pub enum ChcOp {
    // Boolean operations
    Not,
    And,
    Or,
    Implies,
    Iff,

    // Arithmetic operations
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Neg,

    // Comparisons
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,

    // Conditional
    Ite,

    // Array operations
    /// select(arr, idx) - read from array
    Select,
    /// store(arr, idx, val) - write to array
    Store,

    // Bitvector arithmetic (binary, return BitVec)
    BvAdd,
    BvSub,
    BvMul,
    BvUDiv,
    BvURem,
    BvSDiv,
    BvSRem,
    BvSMod,

    // Bitvector bitwise (binary, return BitVec)
    BvAnd,
    BvOr,
    BvXor,
    BvNand,
    BvNor,
    BvXnor,

    // Bitvector unary (return BitVec)
    BvNot,
    BvNeg,

    // Bitvector shift (binary, return BitVec)
    BvShl,
    BvLShr,
    BvAShr,

    // Bitvector comparison (binary, return Bool)
    BvULt,
    BvULe,
    BvUGt,
    BvUGe,
    BvSLt,
    BvSLe,
    BvSGt,
    BvSGe,
    /// bvcomp: bitwise equality, returns 1-bit BitVec
    BvComp,

    // Bitvector concat (variadic, return BitVec)
    BvConcat,

    /// bv2nat: convert bitvector to natural number
    Bv2Nat,

    // Bitvector indexed operations (carry width/index parameters)
    /// extract high low — extract bits \[high:low\]
    BvExtract(u32, u32),
    /// zero_extend n — extend with n zero bits
    BvZeroExtend(u32),
    /// sign_extend n — extend with n sign bits
    BvSignExtend(u32),
    /// rotate_left n
    BvRotateLeft(u32),
    /// rotate_right n
    BvRotateRight(u32),
    /// repeat n — concatenate n copies
    BvRepeat(u32),
    /// int2bv width — convert integer to bitvector
    Int2Bv(u32),
}

impl ChcOp {
    /// Negate a comparison operator: `<` ↔ `>=`, `<=` ↔ `>`, `=` ↔ `!=`.
    /// Returns `None` for non-comparison operators.
    pub fn negate_comparison(&self) -> Option<Self> {
        match self {
            Self::Lt => Some(Self::Ge),
            Self::Le => Some(Self::Gt),
            Self::Gt => Some(Self::Le),
            Self::Ge => Some(Self::Lt),
            Self::Eq => Some(Self::Ne),
            Self::Ne => Some(Self::Eq),
            // BV unsigned comparisons
            Self::BvULt => Some(Self::BvUGe),
            Self::BvULe => Some(Self::BvUGt),
            Self::BvUGt => Some(Self::BvULe),
            Self::BvUGe => Some(Self::BvULt),
            // BV signed comparisons
            Self::BvSLt => Some(Self::BvSGe),
            Self::BvSLe => Some(Self::BvSGt),
            Self::BvSGt => Some(Self::BvSLe),
            Self::BvSGe => Some(Self::BvSLt),
            _ => None,
        }
    }
}

/// CHC expression
///
/// `PartialEq`/`Eq` and `Hash` are implemented manually (`expr/structural.rs`); `Ord`
/// stays derived and structural. All three are pure functions of structure,
/// so `a == b ⟹ hash(a) == hash(b)` and `a == b ⟺ cmp(a, b) == Equal` hold.
/// The manual impls exist because children are shared `Arc`s: an expression
/// is a DAG whose tree expansion can be exponentially larger, and a walk per
/// incoming edge (what the derives do) costs the tree size (WP-F F0a).
#[derive(Debug, Clone, PartialOrd, Ord)]
#[non_exhaustive]
pub enum ChcExpr {
    /// Boolean constant
    Bool(bool),
    /// Integer constant
    ///
    /// i128-lockstep: widened from `i64` together with `SmtValue::Int` (they
    /// convert into each other in `expr/evaluate/mod.rs`); values beyond i128
    /// still Horner-encode via `ChcParser::encode_large_int`.
    Int(i128),
    /// Real constant as rational (numerator, denominator)
    Real(i64, i64),
    /// Bitvector constant: (value, width)
    BitVec(u128, u32),
    /// Variable reference
    Var(ChcVar),
    /// Operation application
    Op(ChcOp, Vec<Arc<Self>>),
    /// Predicate application (uninterpreted relation call)
    /// Contains: predicate name, predicate ID, and argument expressions
    PredicateApp(String, PredicateId, Vec<Arc<Self>>),
    /// Function application (uninterpreted function / constructor / selector / tester).
    ///
    /// Contains: function name, return sort, and argument expressions.
    FuncApp(String, ChcSort, Vec<Arc<Self>>),
    /// Internal marker for constant array parsing - should not appear in user-facing expressions.
    /// Carries the key sort from `(as const (Array KeySort ValSort))`.
    #[doc(hidden)]
    ConstArrayMarker(ChcSort),
    /// Internal marker for datatype tester syntax: `(_ is Ctor)`.
    ///
    /// This appears only while parsing `((_ is Ctor) x)` and is immediately
    /// eliminated by the parser when applied to an argument.
    #[doc(hidden)]
    IsTesterMarker(String),
    /// Constant array: all elements have the same value.
    /// Fields: (key_sort, value_expr).
    ConstArray(ChcSort, Arc<Self>),
    /// Single-index array lambda, represented by closed code and explicit captures.
    /// Boxed to preserve the common expression's 128-byte FP adapter budget.
    ArrayLambda(Box<super::ChcArrayLambda>),
}

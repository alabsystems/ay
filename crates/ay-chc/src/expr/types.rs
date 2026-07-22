// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Core CHC expression types.
//!
//! Extracted from `mod.rs` for code health (#5970).

use std::fmt;
use std::sync::Arc;

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
    /// `Arc` avoids cloning the metadata on every sort copy.
    Datatype {
        name: String,
        constructors: Arc<Vec<ChcDtConstructor>>,
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
/// `PartialEq`/`Eq` are implemented manually (see below) with an `Arc::ptr_eq`
/// short-circuit for the hash-cons fast core; `Hash`/`Ord` stay derived and
/// structural so the trait laws hold by construction.
// Structural derived `Hash` is consistent with the manual `PartialEq`/`Eq`
// (whose `Arc::ptr_eq` short-circuit only agrees faster with structural equality);
// the trait laws hold by construction, so the derive/manual-eq pair is intentional.
#[allow(clippy::derived_hash_with_manual_eq)]
#[derive(Debug, Clone, Hash, PartialOrd, Ord)]
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
}

impl PartialEq for ChcExpr {
    /// Structural equality with an `Arc::ptr_eq` fast path on children
    /// (#9077, fast-core P1).
    ///
    /// This returns *exactly* the same result as the previously-derived
    /// structural `PartialEq` — for every child pair `(x, y)` it evaluates
    /// `Arc::ptr_eq(x, y) || x == y`, and `ptr_eq ⟹ same allocation ⟹
    /// structurally equal`, so the disjunction equals structural equality at
    /// every node (the Decoupling Theorem in
    /// the development design notes). Interning makes
    /// the `ptr_eq` branch fire on shared subterms (O(1) instead of O(tree));
    /// correctness never depends on interning, because the structural fallback
    /// is always taken otherwise. `Hash`/`Ord` remain derived & structural, so
    /// `a == b ⟹ hash(a) == hash(b)` and `a == b ⟺ cmp(a, b) == Equal` hold.
    ///
    /// NOTE: `Real(n, d)` compares structurally (numerator AND denominator),
    /// identical to the derive — `1/2` and `2/4` are NOT equal here.
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Bool(a), Self::Bool(b)) => a == b,
            (Self::Int(a), Self::Int(b)) => a == b,
            (Self::Real(an, ad), Self::Real(bn, bd)) => an == bn && ad == bd,
            (Self::BitVec(av, aw), Self::BitVec(bv, bw)) => av == bv && aw == bw,
            (Self::Var(a), Self::Var(b)) => a == b,
            (Self::Op(ao, aa), Self::Op(bo, ba)) => ao == bo && children_eq(aa, ba),
            (Self::PredicateApp(an, ai, aa), Self::PredicateApp(bn, bi, ba)) => {
                ai == bi && an == bn && children_eq(aa, ba)
            }
            (Self::FuncApp(an, asort, aa), Self::FuncApp(bn, bsort, ba)) => {
                an == bn && asort == bsort && children_eq(aa, ba)
            }
            (Self::ConstArrayMarker(a), Self::ConstArrayMarker(b)) => a == b,
            (Self::IsTesterMarker(a), Self::IsTesterMarker(b)) => a == b,
            (Self::ConstArray(asort, av), Self::ConstArray(bsort, bv)) => {
                asort == bsort && (Arc::ptr_eq(av, bv) || av == bv)
            }
            _ => false,
        }
    }
}

impl Eq for ChcExpr {}

/// Compare child slices with a per-element `Arc::ptr_eq` short-circuit before
/// the structural recursion. Same result as `aa == ba` on the slices.
#[inline]
fn children_eq(aa: &[Arc<ChcExpr>], ba: &[Arc<ChcExpr>]) -> bool {
    aa.len() == ba.len()
        && aa
            .iter()
            .zip(ba.iter())
            .all(|(x, y)| Arc::ptr_eq(x, y) || x == y)
}

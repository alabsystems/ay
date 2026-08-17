// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::sort::Sort;
use num_bigint::BigInt;
use num_rational::BigRational;
use serde::{Deserialize, Serialize};
use std::fmt;
use std::hash::{Hash, Hasher};

/// A term identifier (index into the term store)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
#[must_use = "TermId must be used (discarding it usually indicates a bug)"]
pub struct TermId(pub u32);

impl TermId {
    /// Sentinel value used by the LRA simplex solver for bounds that have no
    /// SAT-level atom reason (e.g., Gomory/HNF cuts, model-seed probing).
    /// Must never collide with a real interned term ID.
    pub const SENTINEL: Self = Self(u32::MAX);

    /// Create a new TermId
    pub fn new(id: u32) -> Self {
        Self(id)
    }

    /// Returns true if this is the sentinel (no real atom reason).
    pub fn is_sentinel(self) -> bool {
        self.0 == u32::MAX
    }

    /// Get the raw index
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

impl fmt::Display for TermId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "t{}", self.0)
    }
}

/// What a Skolem CONSTANT minted for a single-binder quantifier denotes: the
/// Hilbert choice term `(choice ((binder sort)) body)`.
///
/// Skolemization replaces `∃x. B` by `B[x := sk]`. Read as "sk is some fresh
/// constant" that is only equisatisfiable, and an external proof checker is
/// right to reject it: nothing licenses a fresh constant satisfying `B`. Read
/// as "sk is `εx. B`" it is an EQUIVALENCE — `∃x. B ⟺ B[x := εx. B]` is the
/// epsilon axiom — which is why Alethe's `sko_ex`/`sko_forall` rules are stated
/// over `choice` terms. The same holds for the negative universal case
/// (`¬∀x. B ≡ ∃x. ¬B`), where `body` is the already-negated body.
///
/// `body` is captured at the substitution site with every OUTER Skolem already
/// substituted in, so a witness minted later can mention one minted earlier and
/// the pair is renderable in mint (i.e. `TermId`) order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SkolemChoice {
    /// Bound variable of the source quantifier (the `choice` binder).
    pub binder: String,
    /// Sort of the bound variable — also the witness's own sort.
    pub sort: Sort,
    /// `choice` body: the quantifier body this witness was chosen to satisfy,
    /// still mentioning `binder` free.
    pub body: TermId,
}

/// The actual term data
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum TermData {
    /// A constant value
    Const(Constant),
    /// A variable with name and unique ID
    Var(String, u32),
    /// Function application: function symbol + arguments
    App(Symbol, Vec<TermId>),
    /// Let binding (after expansion this should not appear)
    Let(Vec<(String, TermId)>, TermId),
    /// Negation (special case for efficient handling)
    Not(TermId),
    /// If-then-else
    Ite(TermId, TermId, TermId),
    /// Universal quantifier: forall ((x1 S1) (x2 S2) ...) body
    ///
    /// Triggers are multi-patterns:
    /// - Outer Vec = alternative trigger sets (disjunction)
    /// - Inner Vec = multi-trigger patterns (conjunction; currently flattened by E-matching)
    Forall(Vec<(String, Sort)>, TermId, Vec<Vec<TermId>>),
    /// Existential quantifier: exists ((x1 S1) (x2 S2) ...) body
    ///
    /// Triggers are multi-patterns:
    /// - Outer Vec = alternative trigger sets (disjunction)
    /// - Inner Vec = multi-trigger patterns (conjunction; currently flattened by E-matching)
    Exists(Vec<(String, Sort)>, TermId, Vec<Vec<TermId>>),
}

impl Hash for TermData {
    fn hash<H: Hasher>(&self, state: &mut H) {
        std::mem::discriminant(self).hash(state);
        match self {
            Self::Const(c) => c.hash(state),
            Self::Var(name, id) => {
                name.hash(state);
                id.hash(state);
            }
            Self::App(sym, args) => {
                sym.hash(state);
                args.hash(state);
            }
            Self::Let(bindings, body) => {
                bindings.hash(state);
                body.hash(state);
            }
            Self::Not(t) => t.hash(state),
            Self::Ite(c, t, e) => {
                c.hash(state);
                t.hash(state);
                e.hash(state);
            }
            Self::Forall(vars, body, triggers) | Self::Exists(vars, body, triggers) => {
                for (name, sort) in vars {
                    name.hash(state);
                    sort.hash(state);
                }
                body.hash(state);
                triggers.hash(state);
            }
        }
    }
}

/// Function/predicate symbol
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum Symbol {
    /// Named function (user-defined or built-in)
    Named(String),
    /// Indexed function like (_ extract 7 4)
    Indexed(String, Vec<u32>),
}

impl Symbol {
    /// Create a named symbol
    pub fn named(name: impl Into<String>) -> Self {
        Self::Named(name.into())
    }

    /// Create an indexed symbol
    pub fn indexed(name: impl Into<String>, indices: Vec<u32>) -> Self {
        Self::Indexed(name.into(), indices)
    }

    /// Get the name of the symbol
    pub fn name(&self) -> &str {
        match self {
            Self::Named(n) | Self::Indexed(n, _) => n,
        }
    }
}

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Named(n) => write!(f, "{n}"),
            Self::Indexed(n, indices) => {
                write!(f, "(_ {n}")?;
                for idx in indices {
                    write!(f, " {idx}")?;
                }
                write!(f, ")")
            }
        }
    }
}

/// Constant values
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
#[non_exhaustive]
pub enum Constant {
    /// Boolean constant
    Bool(bool),
    /// Integer constant (arbitrary precision)
    Int(BigInt),
    /// Rational constant
    Rational(RationalWrapper),
    /// Bitvector constant with value and width
    BitVec {
        /// The numeric value of the bitvector
        value: BigInt,
        /// The bit width of the bitvector
        width: u32,
    },
    /// String constant
    String(String),
}

/// Wrapper for BigRational to implement Eq and Hash
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RationalWrapper(pub BigRational);

impl PartialEq for RationalWrapper {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl Eq for RationalWrapper {}

impl Hash for RationalWrapper {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // Hash the normalized form
        self.0.numer().hash(state);
        self.0.denom().hash(state);
    }
}

impl From<BigRational> for RationalWrapper {
    fn from(r: BigRational) -> Self {
        Self(r)
    }
}

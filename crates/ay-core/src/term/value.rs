// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::sort::Sort;
use num_bigint::BigInt;
use num_rational::BigRational;
use serde::{Deserialize, Serialize};
use std::fmt;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

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

/// Interned symbol name: a refcounted `str` that behaves like a `String` at
/// every use site.
///
/// #symbol-intern. `TermData::App` holds a `Symbol`, and term-graph traversals
/// clone `TermData` pervasively, so a `String` payload made every clone a heap
/// allocation plus memcpy. Profiling a QF_UFDTLIA memout put `String::clone`
/// under `TermData::clone` at the top of the allocation profile. `Arc<str>`
/// makes the clone a refcount bump.
///
/// The `Deref<Target = str>` plus the `PartialEq<str>`/`PartialEq<&str>` impls
/// below exist so the ~2100 existing sites that pattern-match the variant and
/// then compare (`name == "select"`) or call `&str` methods keep compiling
/// unchanged. Only construction from an owned `String` differs, and that goes
/// through `Symbol::named`/`indexed` for all but a handful of call sites.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SymName(Arc<str>);

impl SymName {
    /// Wrap an owned or borrowed name.
    pub fn new(name: impl AsRef<str>) -> Self {
        Self(Arc::from(name.as_ref()))
    }
    /// Borrow as `&str`.
    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl std::ops::Deref for SymName {
    type Target = str;
    fn deref(&self) -> &str {
        &self.0
    }
}
impl AsRef<str> for SymName {
    fn as_ref(&self) -> &str {
        &self.0
    }
}
impl std::borrow::Borrow<str> for SymName {
    fn borrow(&self) -> &str {
        &self.0
    }
}
impl PartialEq<str> for SymName {
    fn eq(&self, other: &str) -> bool {
        &*self.0 == other
    }
}
impl PartialEq<&str> for SymName {
    fn eq(&self, other: &&str) -> bool {
        &*self.0 == *other
    }
}
impl PartialEq<String> for SymName {
    fn eq(&self, other: &String) -> bool {
        &*self.0 == other.as_str()
    }
}
impl PartialEq<SymName> for str {
    fn eq(&self, other: &SymName) -> bool {
        self == &*other.0
    }
}
impl PartialEq<SymName> for &str {
    fn eq(&self, other: &SymName) -> bool {
        *self == &*other.0
    }
}
impl From<String> for SymName {
    fn from(s: String) -> Self {
        Self(Arc::from(s))
    }
}
impl From<&str> for SymName {
    fn from(s: &str) -> Self {
        Self(Arc::from(s))
    }
}
impl Serialize for SymName {
    fn serialize<S: serde::Serializer>(&self, ser: S) -> Result<S::Ok, S::Error> {
        ser.serialize_str(&self.0)
    }
}
impl<'de> Deserialize<'de> for SymName {
    fn deserialize<D: serde::Deserializer<'de>>(de: D) -> Result<Self, D::Error> {
        Ok(Self(Arc::from(String::deserialize(de)?)))
    }
}
/// Capacity of the underlying buffer, for the term-store memory accounting that
/// used to call `String::capacity`. An `Arc<str>` is exactly its length.
impl SymName {
    #[must_use]
    pub fn capacity(&self) -> usize {
        self.0.len()
    }
}
impl PartialEq<SymName> for String {
    fn eq(&self, other: &SymName) -> bool {
        self.as_str() == &*other.0
    }
}

impl fmt::Display for SymName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

/// Function/predicate symbol
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum Symbol {
    /// Named function (user-defined or built-in)
    ///
    /// #symbol-intern: the payload is `Arc<str>`, not `String`, so cloning a
    /// `Symbol` — and therefore cloning the `TermData::App` that holds it — is a
    /// refcount bump rather than a heap allocation plus memcpy. Term-graph
    /// traversals clone `TermData` pervasively (28 `terms.get(x).clone()` sites in
    /// the EUF theory alone), and profiling a QF_UFDTLIA memout put
    /// `String::clone` under `TermData::clone` at the top of the allocation
    /// profile. The public API is unchanged: `named`/`indexed` still take
    /// `impl Into<String>` and `name()` still returns `&str`.
    Named(SymName),
    /// Indexed function like (_ extract 7 4)
    Indexed(SymName, Vec<u32>),
}

impl Symbol {
    /// Create a named symbol
    pub fn named(name: impl Into<String>) -> Self {
        Self::Named(SymName::new(name.into()))
    }

    /// Create an indexed symbol
    pub fn indexed(name: impl Into<String>, indices: Vec<u32>) -> Self {
        Self::Indexed(SymName::new(name.into()), indices)
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
    Int(#[serde(with = "crate::serde_bignum::bigint")] BigInt),
    /// Rational constant
    Rational(RationalWrapper),
    /// Bitvector constant with value and width
    BitVec {
        /// The numeric value of the bitvector
        #[serde(with = "crate::serde_bignum::bigint")]
        value: BigInt,
        /// The bit width of the bitvector
        width: u32,
    },
    /// String constant
    String(String),
}

/// Wrapper for BigRational to implement Eq and Hash
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RationalWrapper(#[serde(with = "crate::serde_bignum::bigrational")] pub BigRational);

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

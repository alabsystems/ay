// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

//! Term builders shared by both frontends.
//!
//! The scalar/bitvector/array/datatype operators are already complete on
//! [`ay_bindings::Expr`] (e.g. `bvadd`, `select`, `store`); callers use those
//! directly. This module adds the *theory wrappers* that today are either
//! hand-rolled in ty or open-coded in model-checker-consumer:
//!
//! - [`seq`]   — AY native sequences (replaces the model-checker consumer's `sequence_encoder`),
//! - [`set`]   — finite sets over the `Array element Bool` encoding
//!   (replaces the model-checker consumer's `finite_set`),
//! - [`map`]   — total/partial maps over arrays (replaces the model-checker consumer's
//!   `function_encoder`),
//! - [`string`] — AY native strings (replaces the model-checker consumer's `string_intern`).
//!
//! Where a wrapper bottoms out on an [`ay_bindings::Expr`] method that already
//! exists, it delegates — including the sequence/string `concat` / `len`
//! primitives (`seq_concat` / `seq_len` / `str_concat` / `str_len` are present
//! on `Expr`; see `ay-bindings/src/expr/{seq,string}.rs`). The only wrappers
//! that remain unavailable are the finite-set algebra ([`set::union`] /
//! [`set::intersect`] / [`set::difference`]): a *pure* closed-form term for the
//! pointwise Boolean combination of two characteristic arrays needs a native
//! array-map/lambda primitive that `ay_bindings::Expr` does not yet expose. The
//! call-site contract is fixed regardless so consumers can migrate now.

/// Native-sequence term builders (replaces the model-checker consumer's `SequenceEncoder`).
///
/// AY has a native `Seq` sort ([`crate::sorts::seq`]); these wrappers expose
/// the sequence theory so ty no longer has to encode `Seq` as `Array+len` with
/// per-index store/select loops bounded by `max_len`.
pub mod seq {
    use ay_bindings::{Expr, Sort};

    /// The empty sequence of the given element sort. Delegates to native AY.
    #[must_use]
    pub fn empty(element: Sort) -> Expr {
        Expr::seq_empty(element)
    }

    /// The singleton sequence `[x]`. Delegates to native AY.
    #[must_use]
    pub fn unit(x: Expr) -> Expr {
        x.seq_unit()
    }

    /// `s[index]` — the element at 0-based `index`. Delegates to native AY.
    #[must_use]
    pub fn nth(s: Expr, index: Expr) -> Expr {
        s.seq_nth(index)
    }

    /// The subsequence of `s` starting at `offset` of length `len`.
    /// Delegates to native AY (`seq.extract`).
    #[must_use]
    pub fn extract(s: Expr, offset: Expr, len: Expr) -> Expr {
        s.seq_extract(offset, len)
    }

    /// The 0-based index of subsequence `t` in `s` at/after `start`, or `-1`.
    /// Delegates to native AY.
    #[must_use]
    pub fn index_of(s: Expr, t: Expr, start: Expr) -> Expr {
        s.seq_indexof(t, start)
    }

    /// Concatenation `s ++ t`. Delegates to native AY (`seq.++`).
    ///
    /// # Panics
    /// Panics if `s` and `t` are not matching `Seq` sorts.
    #[must_use]
    pub fn concat(s: Expr, t: Expr) -> Expr {
        s.seq_concat(t)
    }

    /// Length `|s|` as an `Int`. Delegates to native AY (`seq.len`).
    ///
    /// # Panics
    /// Panics if `s` is not a `Seq` sort.
    #[must_use]
    pub fn len(s: Expr) -> Expr {
        s.seq_len()
    }
}

/// Finite-set term builders over the `Array element Bool` encoding
/// (replaces the model-checker consumer's `FiniteSetEncoder`).
///
/// A set value is its characteristic array ([`crate::sorts::set_of`]). These
/// builders express membership and the Boolean set algebra *symbolically* on
/// the array, rather than the model-checker consumer's pointwise expansion over an explicit universe.
pub mod set {
    use ay_bindings::Expr;

    /// `x ∈ s` — set membership: `select(s, x)`.
    #[must_use]
    pub fn member(s: Expr, x: Expr) -> Expr {
        s.select(x)
    }

    /// `s ∪ {x}` — insert `x`: `store(s, x, true)`.
    #[must_use]
    pub fn insert(s: Expr, x: Expr) -> Expr {
        s.store(x, Expr::bool_const(true))
    }

    /// `s \ {x}` — remove `x`: `store(s, x, false)`.
    #[must_use]
    pub fn remove(s: Expr, x: Expr) -> Expr {
        s.store(x, Expr::bool_const(false))
    }

    /// Union `a ∪ b` (pointwise `or` of the two characteristic arrays).
    ///
    /// BLOCKED on a missing `ay_bindings` primitive. A closed-form, *pure* term
    /// for the pointwise `or` of two `Array element Bool` characteristic arrays
    /// requires either a native array-map combinator
    /// (`Expr::array_map2(BoolOp::Or, a, b)` — an "`(map or)`" lambda over the
    /// array element sort) or a first-class lambda/array-comprehension on
    /// [`ay_bindings::Expr`]. Neither exists today: the only array ops on `Expr`
    /// are `select` / `store` / `const_array` (see
    /// `ay-bindings/src/expr/arrays.rs`), and there is no `Set` sort with a
    /// native `set.union`. the model-checker consumer's `FiniteSetEncoder::encode_union` sidesteps this
    /// by declaring a *fresh* result array and asserting the pointwise equality
    /// `\A u in universe: select(r,u) = or(select(a,u), select(b,u))` into the
    /// solver — that needs a `&mut Solver` and a known finite `universe`, which
    /// this pure builder deliberately does not take. The operation returns a
    /// typed unsupported error until `ay_bindings::Expr` gains an array-map/
    /// lambda primitive (proposed: `Expr::array_map2`).
    pub fn union(_a: Expr, _b: Expr) -> crate::Result<Expr> {
        Err(crate::EncodeError::Unimplemented(
            "set union requires an array-map/lambda primitive",
        ))
    }

    /// Intersection `a ∩ b` (pointwise `and` of the characteristic arrays).
    ///
    /// BLOCKED on the same missing `ay_bindings` primitive as [`union`]: a
    /// native array-map/lambda over `Expr` (proposed
    /// `Expr::array_map2(BoolOp::And, a, b)`). See [`union`] for the full
    /// rationale.
    pub fn intersect(_a: Expr, _b: Expr) -> crate::Result<Expr> {
        Err(crate::EncodeError::Unimplemented(
            "set intersection requires an array-map/lambda primitive",
        ))
    }

    /// Difference `a \ b` (pointwise `and-not` of the characteristic arrays).
    ///
    /// BLOCKED on the same missing `ay_bindings` primitive as [`union`]: a
    /// native array-map/lambda over `Expr` (proposed
    /// `Expr::array_map2(BoolOp::AndNot, a, b)`). See [`union`] for the full
    /// rationale.
    pub fn difference(_a: Expr, _b: Expr) -> crate::Result<Expr> {
        Err(crate::EncodeError::Unimplemented(
            "set difference requires an array-map/lambda primitive",
        ))
    }
}

/// Map / function term builders over the `Array key value` encoding
/// (replaces the model-checker consumer's `FunctionEncoder`).
///
/// A total map is just an array. A *partial* map is carried as a `(domain,
/// mapping)` pair where `domain` is a [`crate::sorts::set_of`] of the keys and
/// `mapping` is the `Array key value`; [`Partial`] names that pairing once.
pub mod map {
    use ay_bindings::Expr;

    /// A partial map value: a domain set paired with the backing array.
    ///
    /// `lookup` is only meaningful for keys in `domain`; callers guard with
    /// [`crate::terms::set::member`] on `domain` before reading `mapping`.
    #[derive(Debug, Clone)]
    pub struct Partial {
        /// Characteristic array of the key domain (`Array key Bool`).
        pub domain: Expr,
        /// Total backing array (`Array key value`).
        pub mapping: Expr,
    }

    /// `m[k]` on a total map: `select(m, k)`.
    #[must_use]
    pub fn get(m: Expr, k: Expr) -> Expr {
        m.select(k)
    }

    /// `m[k := v]` on a total map: `store(m, k, v)`.
    #[must_use]
    pub fn put(m: Expr, k: Expr, v: Expr) -> Expr {
        m.store(k, v)
    }

    impl Partial {
        /// `k ∈ dom(self)`.
        #[must_use]
        pub fn contains_key(&self, k: Expr) -> Expr {
            crate::terms::set::member(self.domain.clone(), k)
        }

        /// `self[k]` (defined only where [`contains_key`](Self::contains_key)).
        #[must_use]
        pub fn lookup(&self, k: Expr) -> Expr {
            get(self.mapping.clone(), k)
        }
    }
}

/// Native-string term builders (replaces the model-checker consumer's `string_intern` / `intern_string`).
///
/// Uses AY's native `String` sort ([`crate::sorts::string`]) so ty can drop the
/// String→Int interning table.
pub mod string {
    use ay_bindings::Expr;

    /// A string literal. Delegates to native AY.
    #[must_use]
    pub fn constant(value: impl Into<String>) -> Expr {
        Expr::string_const(value)
    }

    /// `s[index]` — the unit-length string at `index`. Delegates to native AY.
    #[must_use]
    pub fn at(s: Expr, index: Expr) -> Expr {
        s.str_at(index)
    }

    /// Substring of `s` from `offset` of length `len`. Delegates to native AY.
    #[must_use]
    pub fn substr(s: Expr, offset: Expr, len: Expr) -> Expr {
        s.str_substr(offset, len)
    }

    /// `indexof(s, t, start)`. Delegates to native AY.
    #[must_use]
    pub fn index_of(s: Expr, t: Expr, start: Expr) -> Expr {
        s.str_indexof(t, start)
    }

    /// Concatenation `s ++ t`. Delegates to native AY (`str.++`).
    ///
    /// # Panics
    /// Panics if `s` and `t` are not `String` sorts.
    #[must_use]
    pub fn concat(s: Expr, t: Expr) -> Expr {
        s.str_concat(t)
    }

    /// Length `|s|` as an `Int`. Delegates to native AY (`str.len`).
    ///
    /// # Panics
    /// Panics if `s` is not a `String` sort.
    #[must_use]
    pub fn len(s: Expr) -> Expr {
        s.str_len()
    }
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

//! Sort builders shared by both frontends.
//!
//! Thin, intention-revealing constructors over [`ay_bindings::Sort`]. The
//! scalar/aggregate sorts (Bool/Int/Real/BV/Array/Datatype/Seq/String) map
//! 1:1 onto native AY sorts. **Set** and **Map** have *no* native [`Sort`]
//! variant in `ay-bindings` (the recon confirmed: Array models maps); we expose
//! them here as first-class *constructors* that lower to the established Array
//! encoding so callers write `set_of` / `map_of` instead of re-deriving the
//! `Array I Bool` / `Array K V` shape at every call site.
//!
//! This consolidates the model-checker consumer's `finite_set` (Set as `Array Int Bool`) and
//! `function_encoder` (Function/Map as domain-set + mapping array) sort choices
//! into one shared place, and gives model-checker-consumer the same vocabulary.

use ay_bindings::Sort;

/// `Bool`.
#[must_use]
pub fn bool() -> Sort {
    Sort::bool()
}

/// `Int` (mathematical integers — used by ty for Int/String-interned domains).
#[must_use]
pub fn int() -> Sort {
    Sort::int()
}

/// `Real`.
#[must_use]
pub fn real() -> Sort {
    Sort::real()
}

/// `(_ BitVec width)` — model-checker-consumer's primary scalar sort for bit-precise MIR.
#[must_use]
pub fn bitvec(width: u32) -> Sort {
    Sort::bitvec(width)
}

/// `(Array index element)`.
#[must_use]
pub fn array(index: Sort, element: Sort) -> Sort {
    Sort::array(index, element)
}

/// AY's native `Seq` sort over `element`.
///
/// This is the sort behind the model-checker consumer's opt-in `native_seq` path; using it lets the
/// solver's native sequence theory replace the model-checker consumer's hand-rolled `sequence_encoder`
/// (Array+len with bounded store/select loops).
#[must_use]
pub fn seq(element: Sort) -> Sort {
    Sort::seq(element)
}

/// AY's native `String` sort.
///
/// Replaces the model-checker consumer's `string_intern` (String→Int) duplication once the native
/// string theory is wired through [`crate::terms::string`].
#[must_use]
pub fn string() -> Sort {
    Sort::string()
}

/// A **Set** of `element`, encoded as its characteristic array `(Array element Bool)`.
///
/// AY has no native `Set` [`Sort`] variant, so a set *is* an array-to-Bool;
/// this constructor names that choice once. The matching membership / union /
/// intersection term builders live in [`crate::terms::set`].
#[must_use]
pub fn set_of(element: Sort) -> Sort {
    Sort::array(element, Sort::bool())
}

/// A total **Map** (function) from `key` to `value`, encoded as `(Array key value)`.
///
/// AY models maps with arrays (no native `Map` [`Sort`] variant in
/// `ay-bindings`). Partial maps additionally need a domain set
/// ([`set_of`]) carried alongside; that pairing is a *term-level* concern and
/// lives in [`crate::terms::map`], keeping this sort total and simple.
#[must_use]
pub fn map_of(key: Sort, value: Sort) -> Sort {
    Sort::array(key, value)
}

/// An uninterpreted sort with the given name (opaque domain).
#[must_use]
pub fn uninterpreted(name: impl Into<String>) -> Sort {
    Sort::uninterpreted(name)
}

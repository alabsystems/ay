// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! One canonical identity implementation for ordinary and cooperative callers.
//!
//! Polls cover each expression/sort node, declaration/argument/selector/row,
//! canonicalization phase and bounded SHA input chunk. Sorting/comparison,
//! JSON and scalar formatting, joins, allocation and destruction still have
//! opaque intervals. Recursive source depth and total work are not bounded by
//! this module. These hooks do not promise a wall-clock deadline or a memory
//! budget; the artifact source validator supplies its own structural limits.

use super::{
    json_string, NORMALIZED_CHC_INPUT_DATATYPE_REFERENCE_SCHEMA, NORMALIZED_CHC_INPUT_SCHEMA,
};
use crate::{ChcExpr, ChcOp, ChcProblem, ChcSort, ClauseHead, HornClause, PredicateId};
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use std::convert::Infallible;

mod historical_v1;
mod ordered;
mod payload;
pub(super) mod prepared;
mod text;
pub(crate) mod wire_sort;
use wire_sort::Key;

/// Caller refusal, never a semantic indeterminate or an identity value.
#[derive(Clone, Copy, Debug, Eq, PartialEq, thiserror::Error)]
#[error("CHC source identity hashing interrupted")]
pub(crate) struct IdentityHashInterrupted;

trait Progress {
    type Error;
    fn poll(&mut self) -> Result<(), Self::Error>;

    fn sort<T>(&mut self, rows: &mut [T], key: impl Fn(&T) -> Key<'_>) -> Result<(), Self::Error> {
        rows.sort_by(|a, b| key(a).cmp(&key(b)));
        Ok(())
    }

    fn datatype_spelling(&self) -> DatatypeSpelling {
        DatatypeSpelling::ReferenceV2
    }
}

enum DatatypeSpelling {
    ReferenceV2,
    InlineV1,
}

struct AlwaysContinue;

impl Progress for AlwaysContinue {
    type Error = Infallible;

    fn poll(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }
}

struct Callback<'a>(&'a mut dyn FnMut() -> bool);

impl Progress for Callback<'_> {
    type Error = IdentityHashInterrupted;

    fn poll(&mut self) -> Result<(), Self::Error> {
        if (self.0)() {
            Ok(())
        } else {
            Err(IdentityHashInterrupted)
        }
    }
}

fn infallible<T>(result: Result<T, Infallible>) -> T {
    match result {
        Ok(value) => value,
        Err(impossible) => match impossible {},
    }
}

pub(super) fn input(problem: &ChcProblem) -> String {
    match prepared::legacy_input(problem) {
        Ok(input) => input,
        Err(_) => infallible(text::normalized_input(problem, &mut AlwaysContinue)),
    }
}

pub(super) fn input_hash(problem: &ChcProblem) -> String {
    normalized_chc_input_identity(problem).1
}

/// Return the schema and digest from one canonicalization, without an observer.
pub(crate) fn normalized_chc_input_identity(problem: &ChcProblem) -> (&'static str, String) {
    infallible(input_identity_with_control(problem, &mut AlwaysContinue))
}

pub(super) fn ordered_hash(problem: &ChcProblem) -> String {
    infallible(ordered::hash(problem, &mut AlwaysContinue))
}

/// One sort's spelling. A datatype is spelled by reference; its definition
/// is not part of this string.
pub(super) fn sort(sort: &ChcSort) -> String {
    infallible(payload::normalized_sort(
        sort,
        &mut AlwaysContinue,
        &mut payload::DatatypeRefs::default(),
    ))
}

/// Hash exactly the existing normalized input, polling throughout traversal.
///
/// Refusal propagates immediately, with no retry or partially returned hash.
/// See this module's remaining opaque-interval limitations.
#[cfg(test)]
pub(crate) fn normalized_chc_input_sha256_with_progress(
    problem: &ChcProblem,
    progress: &mut dyn FnMut() -> bool,
) -> Result<String, IdentityHashInterrupted> {
    Ok(input_identity_with_control(problem, &mut Callback(progress))?.1)
}

/// Hash the normalized input together with the schema that the same canonical
/// text names (v1 unless a datatype sort is referenced).
pub(crate) fn normalized_chc_input_identity_with_progress(
    problem: &ChcProblem,
    progress: &mut dyn FnMut() -> bool,
) -> Result<(&'static str, String), IdentityHashInterrupted> {
    input_identity_with_control(problem, &mut Callback(progress))
}

/// Hash exactly the existing order-sensitive source-clause identity.
pub(crate) fn ordered_chc_clause_sequence_sha256_with_progress(
    problem: &ChcProblem,
    progress: &mut dyn FnMut() -> bool,
) -> Result<String, IdentityHashInterrupted> {
    ordered::hash(problem, &mut Callback(progress))
}

pub(super) fn bytes_hash_with_progress(
    bytes: &[u8],
    progress: &mut dyn FnMut() -> bool,
) -> Result<String, IdentityHashInterrupted> {
    let mut progress = Callback(progress);
    progress.poll()?;
    let mut digest = Sha256::new();
    update_bytes(&mut digest, bytes, &mut progress)?;
    finish_hash(digest, &mut progress)
}

fn input_identity_with_control<P: Progress>(
    problem: &ChcProblem,
    progress: &mut P,
) -> Result<(&'static str, String), P::Error> {
    let input = text::normalized_input(problem, progress)?;
    progress.poll()?;
    let schema = produced_schema(&input);
    let mut digest = Sha256::new();
    update_bytes(&mut digest, input.as_bytes(), progress)?;
    Ok((schema, finish_hash(digest, progress)?))
}

/// The schema line [`text::normalized_input`] wrote: it writes exactly one of
/// the two.
fn produced_schema(input: &str) -> &'static str {
    match input.split_once('\n') {
        Some((NORMALIZED_CHC_INPUT_DATATYPE_REFERENCE_SCHEMA, _)) => {
            NORMALIZED_CHC_INPUT_DATATYPE_REFERENCE_SCHEMA
        }
        _ => NORMALIZED_CHC_INPUT_SCHEMA,
    }
}

// SHA chunking changes no input bytes, prefix lengths or digest semantics.
const HASH_CHUNK_BYTES: usize = 4096;

fn update_bytes<P: Progress>(
    digest: &mut Sha256,
    bytes: &[u8],
    progress: &mut P,
) -> Result<(), P::Error> {
    for chunk in bytes.chunks(HASH_CHUNK_BYTES) {
        progress.poll()?;
        digest.update(chunk);
    }
    progress.poll()
}

fn finish_hash<P: Progress>(digest: Sha256, progress: &mut P) -> Result<String, P::Error> {
    progress.poll()?;
    let digest = digest.finalize();
    let mut hex = String::with_capacity(digest.len() * 2);
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    for byte in digest {
        progress.poll()?;
        hex.push(DIGITS[(byte >> 4) as usize] as char);
        hex.push(DIGITS[(byte & 0x0f) as usize] as char);
    }
    progress.poll()?;
    Ok(hex)
}

fn fallback_predicate_name(pred: PredicateId) -> String {
    format!("p?{}", pred.index())
}

#[cfg(test)]
mod tests;

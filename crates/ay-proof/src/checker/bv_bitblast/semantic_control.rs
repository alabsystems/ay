// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Cancellation-only control shared by one semantic BV validation attempt.

use super::ProofCheckError;

pub(super) type Poll<'a> = &'a mut dyn FnMut() -> Result<(), ProofCheckError>;

pub(super) fn any<T: Copy>(
    values: &[T],
    poll: Poll<'_>,
    mut predicate: impl FnMut(T) -> bool,
) -> Result<bool, ProofCheckError> {
    for &value in values {
        poll()?;
        if predicate(value) {
            return Ok(true);
        }
    }
    Ok(false)
}

pub(super) fn all<T: Copy>(
    values: &[T],
    poll: Poll<'_>,
    mut predicate: impl FnMut(T) -> bool,
) -> Result<bool, ProofCheckError> {
    for &value in values {
        poll()?;
        if !predicate(value) {
            return Ok(false);
        }
    }
    Ok(true)
}

/// Poll entry and keep refusal sticky. The operation polls its success boundary
/// before publishing acceptance; an already-returned validation error must not
/// be replaced by a new post-error callback. Existing aggregate charges remain
/// unchanged: these checkpoints charge zero work and bytes.
pub(super) fn run<T>(
    progress: &mut dyn FnMut(usize, usize) -> bool,
    operation: impl FnOnce(Poll<'_>) -> Result<T, ProofCheckError>,
) -> Result<T, ProofCheckError> {
    let mut refused = false;
    let mut poll = || {
        if refused {
            return Err(ProofCheckError::ResourceLimit);
        }
        // Latch before invoking user code so a caught panic cannot permit a
        // subsequent fallback, retry or acceptance in this attempt.
        refused = true;
        if progress(0, 0) {
            refused = false;
            Ok(())
        } else {
            Err(ProofCheckError::ResourceLimit)
        }
    };
    poll()?;
    operation(&mut poll)
}

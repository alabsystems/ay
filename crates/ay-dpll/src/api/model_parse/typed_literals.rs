// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Closed typed value data, without native-model or solver provenance.

use super::{admission, typed::Decoder};
use crate::api::types::ModelValue;
use ay_core::Sort;
use ay_frontend::sexp::parse_sexp;

mod storage;

const MAX_LITERALS: usize = 4096;

pub(crate) fn decode_typed_literals(input: &[(&str, &Sort)]) -> Option<Vec<ModelValue>> {
    decode_with(input, &mut Decoder::new())
}

fn decode_with(input: &[(&str, &Sort)], decoder: &mut Decoder<'_>) -> Option<Vec<ModelValue>> {
    let result = decode(input, decoder);
    if result.is_none() {
        decoder.refuse_literal_batch();
    }
    result
}

fn preflight(input: &[(&str, &Sort)], decoder: &mut Decoder<'_>) -> Option<()> {
    if input.len() > MAX_LITERALS {
        return None;
    }
    decoder.reserve_literal_resources(
        input.len(),
        input.len().checked_mul(size_of::<ModelValue>())?,
    )?;
    let mut admission = admission::Admission::new();
    for (text, sort) in input {
        // No AST, source schema clone or literal value exists yet. Shared
        // lexical and decoder counters never reset for another batch element.
        admission.admit(text)?;
        let (work, bytes) = storage::allowance(text)?;
        decoder.reserve_literal_resources(work, bytes)?;
        decoder.preflight_literal_sort(sort)?;
    }
    Some(())
}

fn decode(input: &[(&str, &Sort)], decoder: &mut Decoder<'_>) -> Option<Vec<ModelValue>> {
    preflight(input, decoder)?;
    let mut values = Vec::new();
    values.try_reserve_exact(input.len()).ok()?;
    for (text, sort) in input {
        // parse_sexp checks EOF: a second term or command is not a literal.
        // Parser/AST/drop intervals have prepaid fixed allowances, not active
        // cancellation or exact allocator accounting. No error text is copied.
        let parsed = parse_sexp(text).ok()?;
        let value = decoder.decode(&parsed, sort)?;
        drop(parsed);
        values.push(value);
    }
    Some(values)
}

#[cfg(test)]
mod tests;

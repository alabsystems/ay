// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact, bounded decoding of a native get-value batch. The legacy whole-model
//! parser remains best-effort; it is not used to recover these typed values.

#[cfg(test)]
mod tests;

use ay_core::{TermId, TermStore};
use ay_frontend::{sexp::parse_sexp, sexp::parse_sexps, Context};

use super::{admission, typed::Decoder};
use crate::api::types::ModelValue;

pub(in crate::api) const MAX_GET_VALUE_TERMS: usize = 4096;

pub(in crate::api) fn parse_get_value_output(
    output: &str,
    requests: &[(String, TermId)],
    term_store: &TermStore,
    context: &Context,
) -> Option<Vec<ModelValue>> {
    if requests.len() > MAX_GET_VALUE_TERMS {
        return None;
    }
    // Admit both the response and all echoed requests before building any
    // S-expression tree. Native formatting/printing happened in the caller;
    // these limits do not claim to cap those allocations or process RSS.
    let mut admission = admission::Admission::new();
    admission.admit(output)?;
    for (request, _) in requests {
        admission.admit(request)?;
    }
    let sexps = parse_sexps(output).ok()?;
    let [response] = sexps.as_slice() else {
        return None;
    };
    let pairs = response.as_list()?;
    if pairs.len() != requests.len() {
        return None;
    }
    let mut decoder = Decoder::with_context(context);
    let mut values = Vec::with_capacity(requests.len());
    for (pair, (request, id)) in pairs.iter().zip(requests) {
        let [echo, value] = pair.as_list()? else {
            return None;
        };
        if *echo != parse_sexp(request).ok()? {
            return None;
        }
        // The caller resolves and authenticates all handles before formatting.
        // Exact core carriers retain declaration identity even after pop/reuse.
        values.push(decoder.decode(value, term_store.sort(*id))?);
    }
    Some(values)
}

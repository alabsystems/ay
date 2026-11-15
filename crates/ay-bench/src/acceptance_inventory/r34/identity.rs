// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::capture;
use crate::Result;
use ay_chc::ChcProblem;

pub(super) enum Comparison {
    Exact,
    Historical { captured: String, current: String },
    Refused(String),
}

/// A historical digest authenticates the complete actual AST, never a map from
/// an arbitrary new digest to an old one. Current identities remain unchanged.
pub(super) fn compare(
    problem: &ChcProblem,
    current: &str,
    expected: &str,
    captured_bytes: Option<&str>,
    progress: &mut dyn FnMut() -> bool,
) -> Result<Option<Comparison>> {
    if !progress() {
        return Ok(None);
    }
    if let Some(bytes) = captured_bytes {
        capture::require_hash(
            &capture::digest(bytes.as_bytes()),
            expected,
            "captured prepared bytes",
        )?;
    }
    let current_hash = capture::digest(current.as_bytes());
    if current_hash == expected && captured_bytes.is_none_or(|bytes| bytes == current) {
        return Ok(Some(Comparison::Exact));
    }
    if !current.starts_with("ay.chc.normalized-input/v2\n") {
        return Ok(Some(Comparison::Refused(format!(
            "captured={expected}, current={current_hash}; not the historical datatype schema extension, no solve"
        ))));
    }
    let Some(historical) = problem.normalized_input_v1_with_progress(progress) else {
        return Ok(None);
    };
    let historical_hash = capture::digest(historical.as_bytes());
    let identical =
        historical_hash == expected && captured_bytes.is_none_or(|bytes| bytes == historical);
    drop(historical);
    if !progress() {
        return Ok(None);
    }
    Ok(Some(if identical {
        Comparison::Historical {
            captured: expected.to_owned(),
            current: current_hash,
        }
    } else {
        Comparison::Refused(format!(
            "captured={expected}, current={current_hash}, actual AST as v1={historical_hash}; historical AST identity mismatch, no solve"
        ))
    }))
}

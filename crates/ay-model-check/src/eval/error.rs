// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Internal failure classes: only an absent model interpretation permits a
//! model-completion fallback. Diagnostic text never grants that permission.

use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum EvalResource {
    Depth,
    Work,
    Assignments,
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) enum EvalError {
    ModelUnavailable(String),
    Refused(String),
    Resource {
        kind: EvalResource,
        reason: String,
    },
    /// Only `(default <alias-of-dependent-lambda>)` may recover this shape.
    NonFiniteLambdaArray,
}

pub(crate) type EvalResult<T> = Result<T, EvalError>;

impl EvalError {
    pub(crate) fn is_model_unavailable(&self) -> bool {
        matches!(self, Self::ModelUnavailable(_))
    }

    pub(crate) fn resource(kind: EvalResource, reason: impl Into<String>) -> Self {
        Self::Resource {
            kind,
            reason: reason.into(),
        }
    }

    /// An unsupported operand does not identify the enclosing result's shape.
    /// Only transparent result aliases may carry the lambda-array marker.
    pub(crate) fn operand(self) -> Self {
        match self {
            Self::NonFiniteLambdaArray => Self::Refused(self.to_string()),
            other => other,
        }
    }

    /// Add diagnostics without changing fallback authority. A lambda-shape
    /// marker wrapped by another operation is no longer a direct default site.
    pub(crate) fn context(self, prefix: &str) -> Self {
        let reason = format!("{prefix}{self}");
        match self {
            Self::ModelUnavailable(_) => Self::ModelUnavailable(reason),
            Self::Resource { kind, .. } => Self::Resource { kind, reason },
            Self::Refused(_) | Self::NonFiniteLambdaArray => Self::Refused(reason),
        }
    }

    /// A later absent model value must not erase an already observed refusal.
    /// Boolean callers may still settle their result by an exact decisive arm.
    pub(crate) fn record(pending: &mut Option<Self>, next: Self) {
        if pending.as_ref().is_none_or(Self::is_model_unavailable) {
            *pending = Some(next);
        }
    }
}

impl From<String> for EvalError {
    fn from(reason: String) -> Self {
        Self::Refused(reason)
    }
}

impl From<&str> for EvalError {
    fn from(reason: &str) -> Self {
        Self::Refused(reason.to_owned())
    }
}

impl fmt::Display for EvalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ModelUnavailable(reason)
            | Self::Refused(reason)
            | Self::Resource { reason, .. } => f.write_str(reason),
            Self::NonFiniteLambdaArray => {
                f.write_str("binder-dependent lambda-array has no finite array representation")
            }
        }
    }
}

impl std::error::Error for EvalError {}

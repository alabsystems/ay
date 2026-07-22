// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![forbid(unsafe_code)]

//! ay-lean-bridge: Lean 4 integration for AY SMT solver
//!
//! This crate exports AY formulas to Lean syntax. It does not invoke the
//! Lean kernel or certify solver verdicts; callers must check any generated
//! proof artifact through a separately named checker.
//!
//! # Example
//!
//! ```text
//! use ay_lean_bridge::LeanExporter;
//! use ay_core::TermStore;
//!
//! let store = TermStore::new();
//! // ... build formula in store ...
//!
//! // Export to Lean
//! let exporter = LeanExporter::new(&store);
//! let lean_code = exporter.export_term(formula)?;
//! ```

mod exporter;

pub use exporter::LeanExporter;

use ay_core::Sort;
use thiserror::Error;

/// Errors that can occur when interacting with Lean.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum LeanError {
    /// Lean proof failed
    #[error("Lean proof failed: {message}")]
    ProofFailed { message: String },
    /// A ay-core enum variant (e.g. new `Sort`, `TermData`, or `Constant`
    /// variant) is not handled by the Lean exporter yet.
    ///
    /// Because `ay_core::Sort` / `TermData` / `Constant` are `#[non_exhaustive]`,
    /// a future release of `ay-core` can introduce variants that this bridge
    /// does not understand. Returning a typed error here — instead of
    /// `unreachable!()` — keeps the library panic-free and surfaces the exact
    /// unhandled variant to the caller for debugging.
    #[error("unsupported ay-core variant for Lean export: {kind}")]
    Unsupported {
        /// Short debug tag identifying the unhandled variant, e.g.
        /// `"Sort"`, `"TermData"`, or `"Constant"`.
        kind: &'static str,
    },
}

/// Export a sort to Lean type syntax.
pub(crate) fn export_sort_to_lean(sort: &Sort) -> Result<String, LeanError> {
    let rendered = match sort {
        Sort::Bool => "Bool".to_string(),
        Sort::Int => "Int".to_string(),
        Sort::Real => "Real".to_string(),
        Sort::BitVec(bv) => format!("BitVec {}", bv.width),
        Sort::Array(arr) => {
            format!(
                "Array {} {}",
                export_sort_to_lean(&arr.index_sort)?,
                export_sort_to_lean(&arr.element_sort)?
            )
        }
        Sort::String => "String".to_string(),
        Sort::RegLan => "RegLan".to_string(),
        Sort::FloatingPoint(eb, sb) => format!("FloatingPoint {eb} {sb}"),
        Sort::Uninterpreted(name) => sanitize_lean_name(name),
        Sort::Datatype(dt) => sanitize_lean_name(&dt.name),
        Sort::Seq(elem) => format!("List {}", export_sort_to_lean(elem)?),
        // `Sort` is `#[non_exhaustive]` in ay-core. Return a typed error for
        // any unhandled variant rather than panicking.
        _ => {
            return Err(LeanError::Unsupported {
                kind: "Sort::<unhandled-variant>",
            })
        }
    };
    Ok(rendered)
}

/// Sanitize a name for use in Lean.
pub(crate) fn sanitize_lean_name(name: &str) -> String {
    // Lean identifiers can contain letters, digits, underscores, and apostrophes
    // They must start with a letter or underscore
    let mut result = String::with_capacity(name.len());
    let mut first = true;

    for c in name.chars() {
        if c.is_ascii_alphanumeric() || c == '_' || c == '\'' {
            if first && c.is_ascii_digit() {
                result.push('_');
            }
            result.push(c);
            first = false;
        } else if c == '!' || c == '?' {
            // Keep these for Lean naming conventions
            result.push(c);
            first = false;
        } else {
            // Replace other characters with underscore
            result.push('_');
            first = false;
        }
    }

    if result.is_empty() {
        return "_unnamed".to_string();
    }

    // Check for Lean reserved words
    if is_lean_reserved(&result) {
        format!("{result}_")
    } else {
        result
    }
}

/// Check if a name is a Lean reserved word.
fn is_lean_reserved(name: &str) -> bool {
    matches!(
        name,
        "def"
            | "theorem"
            | "lemma"
            | "axiom"
            | "example"
            | "structure"
            | "class"
            | "instance"
            | "inductive"
            | "where"
            | "with"
            | "do"
            | "if"
            | "then"
            | "else"
            | "match"
            | "let"
            | "in"
            | "have"
            | "show"
            | "by"
            | "fun"
            | "forall"
            | "exists"
            | "true"
            | "false"
            | "Type"
            | "Prop"
            | "Sort"
            | "Bool"
            | "Nat"
            | "Int"
    )
}

/// Escape a string for use in Lean string literals.
pub(crate) fn escape_lean_string(s: &str) -> String {
    let mut result = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '"' => result.push_str("\\\""),
            '\\' => result.push_str("\\\\"),
            '\n' => result.push_str("\\n"),
            '\r' => result.push_str("\\r"),
            '\t' => result.push_str("\\t"),
            _ => result.push(c),
        }
    }
    result
}

#[cfg(test)]
#[path = "lib_tests.rs"]
mod tests;

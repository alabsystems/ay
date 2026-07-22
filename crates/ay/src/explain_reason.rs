// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Phase 1 reason-code classification for `--explain` (#8693).
//!
//! The full [`crate::explain`] module produces rich English walk-throughs of a
//! SAT or UNSAT answer. That output is useful but it answers the *instance-
//! level* question ("which constraints conflict?") rather than the *engine-
//! level* question ("*how* did the solver decide?"). Phase 1 adds the latter:
//! a small, stable enum of reason codes plus a one-to-three-sentence template
//! explanation per code, optionally emitted as JSON for tooling consumers.
//!
//! The reason codes are intentionally coarse — they classify the *path* that
//! produced UNSAT, not the semantic core. Later phases (SAT model explanation,
//! proof-tree visualization, minimal UNSAT core in English) build on top.
//!
//! Detection strategy (Phase 1):
//! * Ask the executor for the assertion list via [`Command::GetAssertions`].
//! * If any assertion is the literal `false`, the preprocessing layer (parser
//!   / elaborator) has already established UNSAT without CDCL search →
//!   [`ReasonCode::PreprocessingDetected`].
//! * If the assertion list is empty yet the solver reports UNSAT, record
//!   [`ReasonCode::EmptyAssertions`] (anomalous — empty is vacuously SAT;
//!   the caller is expected to skip explanation entirely when emptiness is
//!   detected before solving).
//! * Otherwise inspect [`ay_dpll::Statistics::theory_conflicts`] and the
//!   per-theory `smt.conflicts.<theory>` counters. If a theory registered at
//!   least one conflict, report [`ReasonCode::TheoryConflict`] with that
//!   theory name; otherwise fall back to
//!   [`ReasonCode::UnitPropagationContradiction`].
//!
//! This is deliberately a post-hoc heuristic — it requires no changes to the
//! solver pipeline and is therefore safe to enable for any logic.

use ay_dpll::Executor;
use ay_frontend::Command;

/// Phase 1 reason codes for UNSAT explanations.
///
/// The variant set is fixed and stable: new reasons should be added behind
/// new variants rather than by reusing existing ones, so downstream tooling
/// can match exhaustively.
///
/// `KnownTheorem` and `Unknown` are reserved for later phases (cache lookup,
/// classifier fallback); they are intentionally unused in Phase 1 so that
/// the JSON schema is stable from day one.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
#[allow(dead_code)]
pub(crate) enum ReasonCode {
    /// A `(assert false)` (or equivalent constant-false assertion) was present
    /// in the input. The parser / elaborator detected UNSAT before CDCL was
    /// invoked.
    PreprocessingDetected,
    /// The assertion set was empty. Empty assertion sets are vacuously
    /// satisfiable; encountering this variant on an UNSAT path indicates a
    /// caller bug rather than a real contradiction.
    EmptyAssertions,
    /// A theory solver emitted at least one conflict during search. The
    /// contained string names the theory (`"LIA"`, `"LRA"`, `"EUF"`,
    /// `"arrays"`, or `"unknown"` when classification fails).
    TheoryConflict(String),
    /// Purely propositional UNSAT — CDCL derived the empty clause via unit
    /// propagation and conflict analysis without involving any theory solver.
    UnitPropagationContradiction,
    /// UNSAT was established by looking up a previously-proven equivalent
    /// theorem in the cache. Reserved for future phases; Phase 1 never emits
    /// this variant.
    KnownTheorem,
    /// None of the above patterns matched.
    Unknown,
}

impl ReasonCode {
    /// Stable identifier used in JSON output.
    pub(crate) fn tag(&self) -> &'static str {
        match self {
            Self::PreprocessingDetected => "PreprocessingDetected",
            Self::EmptyAssertions => "EmptyAssertions",
            Self::TheoryConflict(_) => "TheoryConflict",
            Self::UnitPropagationContradiction => "UnitPropagationContradiction",
            Self::KnownTheorem => "KnownTheorem",
            Self::Unknown => "Unknown",
        }
    }

    /// Theory name parameter for [`ReasonCode::TheoryConflict`].
    pub(crate) fn theory(&self) -> Option<&str> {
        match self {
            Self::TheoryConflict(name) => Some(name.as_str()),
            _ => None,
        }
    }

    /// 1-3 sentence template explanation for this reason.
    pub(crate) fn template(&self) -> String {
        match self {
            Self::PreprocessingDetected => {
                "The formula contains an assertion that reduces to `false` at preprocessing time. \
                 No search was needed: the parser or elaborator already proved unsatisfiability."
                    .to_string()
            }
            Self::EmptyAssertions => {
                "The assertion set is empty, so the formula is vacuously satisfiable. \
                 Seeing this reason on an UNSAT result indicates a caller bug."
                    .to_string()
            }
            Self::TheoryConflict(theory) => format!(
                "A {theory} theory solver detected an arithmetic or equality conflict during search. \
                 The combined Boolean + theory reasoning chain could not be satisfied by any assignment."
            ),
            Self::UnitPropagationContradiction => {
                "CDCL derived the empty clause purely through unit propagation and conflict analysis. \
                 No theory reasoning was involved — the propositional skeleton alone is unsatisfiable."
                    .to_string()
            }
            Self::KnownTheorem => {
                "The formula matches a previously-proven unsatisfiable theorem in the cache."
                    .to_string()
            }
            Self::Unknown => {
                "The solver returned UNSAT, but the reason could not be classified into any known \
                 Phase 1 category."
                    .to_string()
            }
        }
    }
}

/// Format selector for the Phase 1 reason-code output.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub(crate) enum ExplainFormat {
    /// Plain-text block, printed alongside the existing rich explanation.
    #[default]
    Plain,
    /// Single-line JSON object with `reason`, `theory`, and `message` fields.
    Json,
}

/// Detect the reason code for the current UNSAT result by inspecting the
/// executor's statistics and assertion list.
///
/// This is a post-hoc read-only pass. It runs after `(check-sat)` has already
/// produced `unsat`, so it never influences the solve result.
pub(crate) fn detect_reason_code(executor: &mut Executor) -> ReasonCode {
    // 1. Look at the assertion list. If it contains a literal `false`, the
    //    input was already UNSAT before search; if it is empty, flag the
    //    anomaly. `get_assertions` can fail for pathological back-ends — in
    //    that case we fall through to the theory/CDCL heuristic.
    if let Ok(Some(text)) = executor.execute(&Command::GetAssertions) {
        let assertions = parse_top_level_assertions(&text);
        if assertions.is_empty() {
            return ReasonCode::EmptyAssertions;
        }
        if assertions.iter().any(|a| is_literal_false(a.trim())) {
            return ReasonCode::PreprocessingDetected;
        }
    }

    // 2. Inspect theory conflict counters. The first theory with a non-zero
    //    `smt.conflicts.<theory>` counter wins. If no theory registered a
    //    conflict but `theory_conflicts` is non-zero, classify as a generic
    //    unknown theory conflict.
    let stats = executor.statistics();
    for (key, name) in [
        ("smt.conflicts.lia", "LIA"),
        ("smt.conflicts.lra", "LRA"),
        ("smt.conflicts.euf", "EUF"),
        ("smt.conflicts.arrays", "arrays"),
    ] {
        if stats.get_int(key).unwrap_or(0) > 0 {
            return ReasonCode::TheoryConflict(name.to_string());
        }
    }
    if stats.theory_conflicts > 0 {
        return ReasonCode::TheoryConflict("unknown".to_string());
    }

    // 3. No theory conflicts at all — purely propositional UNSAT.
    ReasonCode::UnitPropagationContradiction
}

/// Emit the Phase 1 reason-code block to stdout for an UNSAT result.
///
/// Plain-text output is printed as a short, human-readable block prefixed
/// with `Reason:` and `Explanation:` lines. JSON output is a single-line
/// object with the stable `reason` tag, optional `theory` field, and the
/// template `message`.
pub(crate) fn emit_unsat_reason(executor: &mut Executor, format: ExplainFormat) {
    let reason = detect_reason_code(executor);
    match format {
        ExplainFormat::Plain => {
            safe_println!();
            safe_println!("=== Reason code (UNSAT, Phase 1) ===");
            match reason.theory() {
                Some(t) => safe_println!("Reason: {}({t})", reason.tag()),
                None => safe_println!("Reason: {}", reason.tag()),
            }
            safe_println!("Explanation: {}", reason.template());
        }
        ExplainFormat::Json => {
            let json = format_reason_json(&reason);
            safe_println!("{json}");
        }
    }
}

/// Build the JSON line for a reason code. We hand-format rather than pull in
/// `serde_json` on the hot path — the output is simple enough that a fixed
/// template with escaped strings is sufficient.
fn format_reason_json(reason: &ReasonCode) -> String {
    let tag = reason.tag();
    let message = json_escape(&reason.template());
    match reason.theory() {
        Some(theory) => {
            let theory = json_escape(theory);
            format!(r#"{{"reason":"{tag}","theory":"{theory}","message":"{message}"}}"#)
        }
        None => format!(r#"{{"reason":"{tag}","theory":null,"message":"{message}"}}"#),
    }
}

/// Minimal JSON string escaper: backslash, double-quote, and control chars.
fn json_escape(input: &str) -> String {
    let mut out = String::with_capacity(input.len());
    for ch in input.chars() {
        match ch {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => {
                out.push_str(&format!("\\u{:04x}", c as u32));
            }
            c => out.push(c),
        }
    }
    out
}

/// Parse top-level assertion sexprs from `(get-assertions)` output.
///
/// The executor returns either `()` (empty list) or `( <expr_1> <expr_2> ... )`.
/// This helper extracts each balanced `expr_i` as a trimmed string and also
/// returns bare (non-parenthesized) tokens like `false`.
fn parse_top_level_assertions(text: &str) -> Vec<String> {
    let trimmed = text.trim();
    if trimmed.is_empty() || trimmed == "()" {
        return Vec::new();
    }
    let inner = if let Some(stripped) = trimmed.strip_prefix('(').and_then(|s| s.strip_suffix(')'))
    {
        stripped
    } else {
        trimmed
    };

    let mut out = Vec::new();
    let mut depth: i32 = 0;
    let mut current = String::new();

    for ch in inner.chars() {
        match ch {
            '(' => {
                depth += 1;
                current.push(ch);
            }
            ')' => {
                depth -= 1;
                current.push(ch);
                if depth == 0 {
                    let s = current.trim().to_string();
                    if !s.is_empty() {
                        out.push(s);
                    }
                    current.clear();
                }
            }
            c if depth == 0 && c.is_whitespace() => {
                let s = current.trim().to_string();
                if !s.is_empty() {
                    out.push(s);
                    current.clear();
                }
            }
            _ => current.push(ch),
        }
    }
    let tail = current.trim().to_string();
    if !tail.is_empty() {
        out.push(tail);
    }
    out
}

/// Detect whether an assertion string is the literal Boolean `false`.
///
/// Accepts bare `false`, `(false)` (rare but legal under some back-ends), and
/// `(not true)` because preprocessing sometimes canonicalizes the former to
/// the latter on round-trip.
fn is_literal_false(assertion: &str) -> bool {
    let a = assertion.trim();
    if a == "false" || a == "(false)" {
        return true;
    }
    // Strip outer parens if balanced and retest.
    if let Some(inner) = a.strip_prefix('(').and_then(|s| s.strip_suffix(')')) {
        let inner = inner.trim();
        if inner == "false" {
            return true;
        }
        if inner == "not true" {
            return true;
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_reason_code_tag_stable() {
        assert_eq!(
            ReasonCode::PreprocessingDetected.tag(),
            "PreprocessingDetected"
        );
        assert_eq!(ReasonCode::EmptyAssertions.tag(), "EmptyAssertions");
        assert_eq!(
            ReasonCode::TheoryConflict("LIA".to_string()).tag(),
            "TheoryConflict"
        );
        assert_eq!(
            ReasonCode::UnitPropagationContradiction.tag(),
            "UnitPropagationContradiction"
        );
        assert_eq!(ReasonCode::KnownTheorem.tag(), "KnownTheorem");
        assert_eq!(ReasonCode::Unknown.tag(), "Unknown");
    }

    #[test]
    fn test_reason_code_theory_name_round_trip() {
        let r = ReasonCode::TheoryConflict("LIA".to_string());
        assert_eq!(r.theory(), Some("LIA"));
        assert_eq!(ReasonCode::PreprocessingDetected.theory(), None);
    }

    #[test]
    fn test_template_mentions_theory_name() {
        let r = ReasonCode::TheoryConflict("LRA".to_string());
        let template = r.template();
        assert!(
            template.contains("LRA"),
            "expected LRA in template, got: {template}"
        );
    }

    #[test]
    fn test_is_literal_false_variants() {
        assert!(is_literal_false("false"));
        assert!(is_literal_false("(false)"));
        assert!(is_literal_false("(not true)"));
        assert!(!is_literal_false("true"));
        assert!(!is_literal_false("(> x 0)"));
        assert!(!is_literal_false(""));
    }

    #[test]
    fn test_parse_top_level_assertions_empty() {
        assert!(parse_top_level_assertions("").is_empty());
        assert!(parse_top_level_assertions("()").is_empty());
    }

    #[test]
    fn test_parse_top_level_assertions_literal_false() {
        // `(get-assertions)` for `(assert false)` returns `(false)`.
        let parsed = parse_top_level_assertions("(false)");
        assert_eq!(parsed, vec!["false".to_string()]);
    }

    #[test]
    fn test_parse_top_level_assertions_nested() {
        let parsed = parse_top_level_assertions("((= x 1) (> y 0))");
        assert_eq!(parsed.len(), 2);
        assert_eq!(parsed[0], "(= x 1)");
        assert_eq!(parsed[1], "(> y 0)");
    }

    #[test]
    fn test_format_reason_json_shape() {
        let r = ReasonCode::UnitPropagationContradiction;
        let json = format_reason_json(&r);
        assert!(json.starts_with('{'));
        assert!(json.ends_with('}'));
        assert!(json.contains(r#""reason":"UnitPropagationContradiction""#));
        assert!(json.contains(r#""theory":null"#));
        assert!(json.contains(r#""message":"#));
    }

    #[test]
    fn test_format_reason_json_theory_field_populated() {
        let r = ReasonCode::TheoryConflict("LIA".to_string());
        let json = format_reason_json(&r);
        assert!(json.contains(r#""reason":"TheoryConflict""#));
        assert!(json.contains(r#""theory":"LIA""#));
    }

    #[test]
    fn test_json_escape_handles_control_chars() {
        assert_eq!(json_escape("a\"b"), "a\\\"b");
        assert_eq!(json_escape("a\\b"), "a\\\\b");
        assert_eq!(json_escape("a\nb"), "a\\nb");
    }
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The model diagnostics a decision command wrote, or under `--z3-mode` would
//! have written, to stderr, kept for `(get-info :all-statistics)`.
//!
//! z3 writes nothing to stderr during a normal session, so `--z3-mode` does not
//! print the `MODEL-UNCONFIRMED` line or the `[AY SOUNDNESS GATE]` banner.
//! `last_statistics` cannot carry them instead: a later phase of the same
//! check-sat (a re-solve, a quantifier round, a restored snapshot) replaces it,
//! so a candidate rejected on the way to a published `sat` left no trace. This
//! record lives beside it and is cleared only when the next outermost decision
//! command starts.

use ay_core::string_literal;

/// Longest detail kept, in characters. A detail can quote a whole assertion.
const MAX_DETAIL_CHARS: usize = 300;

#[derive(Debug, Default)]
pub(in crate::executor) struct StderrDiagnostics {
    model_unconfirmed: u64,
    last_model_unconfirmed: String,
    invalid_models: u64,
    last_invalid_model: String,
}

impl StderrDiagnostics {
    pub(in crate::executor) fn clear(&mut self) {
        *self = Self::default();
    }

    /// A `MODEL-UNCONFIRMED` line: a model or verdict AY could not confirm.
    pub(in crate::executor) fn record_model_unconfirmed(&mut self, detail: &str) {
        self.model_unconfirmed += 1;
        self.last_model_unconfirmed = bounded_detail(detail);
    }

    /// An `[AY SOUNDNESS GATE]` banner: a model that falsifies an assertion.
    pub(in crate::executor) fn record_invalid_model(&mut self, assertion: &str, assignment: &str) {
        self.invalid_models += 1;
        self.last_invalid_model =
            bounded_detail(&format!("{assertion} falsified under model: {assignment}"));
    }

    /// `(key, value)` statistics entries in SMT-LIB form, keys without the
    /// colon; none when nothing was recorded.
    pub(in crate::executor) fn statistics_entries(&self) -> Vec<(String, String)> {
        let mut entries = Vec::new();
        if self.model_unconfirmed > 0 {
            entries.push((
                "model-unconfirmed".to_string(),
                self.model_unconfirmed.to_string(),
            ));
            entries.push((
                "model-unconfirmed.last-detail".to_string(),
                string_literal(&self.last_model_unconfirmed),
            ));
        }
        if self.invalid_models > 0 {
            entries.push((
                "soundness-gate.invalid-models".to_string(),
                self.invalid_models.to_string(),
            ));
            entries.push((
                "soundness-gate.last-invalid-model".to_string(),
                string_literal(&self.last_invalid_model),
            ));
        }
        entries
    }
}

/// Prints the `MODEL-UNCONFIRMED` stderr line, capped process-wide: CHC
/// engines run thousands of internal queries per solve, and one line per caught
/// model (each with the whole falsified assertion) reached 4 MB of stderr on
/// sally om1 instances, past the harness capture limit. Statistics still count
/// every occurrence.
pub(in crate::executor) fn print_model_unconfirmed_capped(tier: &str, detail: &str) {
    static PRINTED: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    const MAX_PRINTED: u64 = 3;
    let n = PRINTED.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let line = match n.cmp(&MAX_PRINTED) {
        std::cmp::Ordering::Less => format!(
            "c !! MODEL-UNCONFIRMED [{tier}] (not a refutation — see [AY SOUNDNESS GATE] for caught invalid models) {}",
            bounded_detail(detail)
        ),
        std::cmp::Ordering::Equal => {
            "c !! MODEL-UNCONFIRMED: further lines suppressed (counted in statistics)".to_string()
        }
        std::cmp::Ordering::Greater => return,
    };
    ay_core::safe_eprintln!("{line}");
}

/// One line of at most [`MAX_DETAIL_CHARS`] characters.
fn bounded_detail(detail: &str) -> String {
    let mut out: String = detail
        .chars()
        .take(MAX_DETAIL_CHARS)
        .map(|c| if c.is_control() { ' ' } else { c })
        .collect();
    if detail.chars().nth(MAX_DETAIL_CHARS).is_some() {
        out.push_str("...");
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn nothing_recorded_adds_no_entry() {
        assert!(StderrDiagnostics::default().statistics_entries().is_empty());
    }

    #[test]
    fn entries_count_every_event_and_keep_the_last_detail_on_one_bounded_line() {
        let mut diagnostics = StderrDiagnostics::default();
        diagnostics.record_invalid_model(&format!("(a\n{})", "b".repeat(500)), "x = 1");
        diagnostics.record_invalid_model("(= y 2)", "y = 3");
        assert_eq!(
            diagnostics.statistics_entries(),
            [
                ("soundness-gate.invalid-models".to_string(), "2".to_string()),
                (
                    "soundness-gate.last-invalid-model".to_string(),
                    "\"(= y 2) falsified under model: y = 3\"".to_string()
                ),
            ]
        );

        diagnostics.clear();
        diagnostics.record_model_unconfirmed(&format!("a\nb{}", "c".repeat(400)));
        let entries = diagnostics.statistics_entries();
        assert_eq!(entries.len(), 2);
        assert_eq!(
            entries[0],
            ("model-unconfirmed".to_string(), "1".to_string())
        );
        let detail = &entries[1].1;
        assert!(
            detail.starts_with("\"a b") && detail.ends_with("...\""),
            "{detail}"
        );
        assert!(!detail.contains('\n'));
        // The two quotes, the bounded detail and the ellipsis.
        assert_eq!(detail.chars().count(), MAX_DETAIL_CHARS + 5);
    }
}

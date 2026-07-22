// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared bridge between the string MODEL-CONSTRUCTION paths and the
//! content-positive regex witness search `ay_strings::we_regex::find_witness`
//! (strings increments W1-W3, `AY_STR_WITNESS=1`, default OFF).
//!
//! ## Why this module exists
//!
//! AY's string model construction is content-blind: a variable receives
//! content only by EQC-merge with a literal already in the file, by a pinned
//! pre-pass candidate, by copying a SAT-true equality's other side, or by
//! padding with a single repeated letter. A variable that is length-pinned
//! *and* language-constrained (`(str.in_re x R)`) therefore gets `"aaa"`,
//! the evaluator computes the membership definitively false, the retracting
//! gate discards the completion, and a genuine SAT degrades to Unknown —
//! no AY path could emit a character that is not a literal in the formula or
//! the pad letter. `find_witness` does content-POSITIVE construction from the
//! regex derivatives, so it can produce exactly those characters.
//!
//! ## Soundness contract (identical for every increment here)
//!
//! Everything in this module only ever produces a CANDIDATE value. Each
//! candidate rides the pre-existing validation gates completely unchanged:
//!
//! * `complete_constrained_gaps` re-checks the completed model with
//!   `verify_model_strict` AND the independent model-check gate, and RETRACTS
//!   on any refutation (W1, W3);
//! * `materialize_string_witnesses` strictly re-validates by full
//!   substitution and rolls back on any definitely-false assertion (W2).
//!
//! No gate is weakened, no verdict logic is touched. A constructed witness
//! can therefore only CONVERT a would-be Unknown into a gate-validated SAT,
//! or cost time — it can never mis-answer.

use ay_core::term::{TermData, TermId};
use ay_strings::we_regex::WeRegex;

use super::{Executor, Model};

/// Maximum number of regex memberships intersected for one witness search.
/// `find_witness` walks the product of the derivative automata, so the state
/// count is exponential in the number of conjoined constraints; the cap keeps
/// the search bounded. Dropping constraints is SOUND for construction (a
/// witness satisfying fewer constraints is simply more likely to be refuted
/// by the gates) — it is never used to justify an answer.
pub(in crate::executor) const MAX_WITNESS_REGEXES: usize = 8;

/// Maximum witness length this bridge is willing to construct, mirroring the
/// existing seq/string reconstruction caps.
pub(in crate::executor) const MAX_WITNESS_CONSTRUCT_LEN: usize = 4096;

/// Search-depth bound handed to
/// [`ay_strings::we_regex::find_witness_bounded`] when no exact length is
/// pinned. The default feasibility knob (64 under S1) is far below the
/// literal lengths industrial regex chains carry, so a witness that plainly
/// exists is never reached. Bounding work, not soundness.
pub(in crate::executor) const WITNESS_SEARCH_MAX_LEN: usize = 512;

/// Strings witness-construction master switch (`AY_STR_WITNESS=1`, default
/// OFF).
///
/// Default OFF keeps every model-construction path byte-identical to
/// pre-W1 behavior.
pub(in crate::executor) fn str_witness_enabled() -> bool {
    static V: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    // DEFAULT-ON: W1b converts 4 automatark files (z3-verified), 0 losses,
    // 0 disagreements, fuzz clean; W1/W2/W3 are inert on this corpus but
    // correct and gated. AY_STR_WITNESS=0 kills it.
    *V.get_or_init(|| !matches!(std::env::var("AY_STR_WITNESS").ok().as_deref(), Some("0")))
}

/// Per-increment kill switch: `AY_STR_WITNESS_W<n>=0` disables increment `n`
/// while the master switch is on (all increments are on when the master
/// switch is on and the per-increment variable is unset).
fn sub_enabled(var: &str) -> bool {
    str_witness_enabled() && !matches!(std::env::var(var).ok().as_deref(), Some("0"))
}

/// W1: regex-aware witness construction in the gap-completion pass.
pub(in crate::executor) fn str_witness_w1() -> bool {
    static V: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *V.get_or_init(|| sub_enabled("AY_STR_WITNESS_W1"))
}

/// W1b: content-positive regex witness construction in the QF_S/QF_SLIA
/// regex×length PRE-PASS (`strings_regex_len.rs`), for the variables whose
/// finite-enumeration gates (bounded length window, closed alphabet ≤ 16
/// characters) bail. Rides the SAME validated-assumption machinery
/// (`try_string_var_witnesses`: pin `x = "..."`, re-solve, validate the FULL
/// model) the enumeration path already uses.
pub(in crate::executor) fn str_witness_w1b() -> bool {
    static V: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *V.get_or_init(|| sub_enabled("AY_STR_WITNESS_W1B"))
}

/// W2: regex-aware string materializer.
pub(in crate::executor) fn str_witness_w2() -> bool {
    static V: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *V.get_or_init(|| sub_enabled("AY_STR_WITNESS_W2"))
}

/// W3: per-variable retract in the gap-completion pass.
pub(in crate::executor) fn str_witness_w3() -> bool {
    static V: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *V.get_or_init(|| sub_enabled("AY_STR_WITNESS_W3"))
}

impl Executor {
    /// Harvest `var`'s `str.in_re` memberships FROM THE SAT ASSIGNMENT as
    /// [`WeRegex`] constraints (W1).
    ///
    /// Scans ALL `str.in_re` applications over `var` (not only top-level
    /// syntactic conjuncts) and reads each atom's polarity with the same
    /// `term_value(sat_model, term_to_var, atom)` lookup
    /// `derive_string_from_sat_true_equalities` uses:
    ///
    /// * assigned TRUE  -> the translated regex;
    /// * assigned FALSE -> its EXACT complement (`WeRegex::comp` is exact over
    ///   the full SMT-LIB alphabet, so a negative membership constrains the
    ///   search rather than being dropped);
    /// * UNDECIDED (absent from `term_to_var`, so `term_value` yields `None`)
    ///   -> skipped, never assumed.
    ///
    /// A membership whose regex `translate_we_regex` cannot render EXACTLY is
    /// skipped. Skipping constraints only makes the constructed value more
    /// likely to be refuted by the unchanged gates; it can never justify a
    /// wrong answer.
    pub(in crate::executor) fn harvest_sat_regex_memberships(
        &self,
        model: &Model,
        var: TermId,
    ) -> Vec<WeRegex> {
        let mut out: Vec<WeRegex> = Vec::new();
        for idx in 0..self.ctx.terms.len() {
            let tid = TermId(idx as u32);
            let TermData::App(sym, args) = self.ctx.terms.get(tid) else {
                continue;
            };
            if !matches!(sym.name(), "str.in_re" | "str.in.re") || args.len() != 2 {
                continue;
            }
            // Only memberships whose SUBJECT is exactly `var`: a concat
            // subject constrains the concatenation, not this variable alone.
            if args[0] != var {
                continue;
            }
            // The atom must be DECIDED by the SAT model; an undecided atom is
            // absent from `term_to_var` and is skipped (never assumed).
            let Some(polarity) = self.term_value(&model.sat_model, &model.term_to_var, tid) else {
                continue;
            };
            let Some(regex) = self.translate_we_regex(args[1], 0) else {
                continue;
            };
            out.push(if polarity {
                regex
            } else {
                WeRegex::comp(regex)
            });
            if out.len() >= MAX_WITNESS_REGEXES {
                break;
            }
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn witness_flags_default_off() {
        // The suite runs without the env var set, so every increment must be
        // off by default (byte-identical pipeline).
        if std::env::var("AY_STR_WITNESS").is_err() {
            assert!(!str_witness_enabled(), "AY_STR_WITNESS must default OFF");
            assert!(!str_witness_w1(), "W1 must default OFF");
            assert!(!str_witness_w2(), "W2 must default OFF");
            assert!(!str_witness_w3(), "W3 must default OFF");
        }
    }
}

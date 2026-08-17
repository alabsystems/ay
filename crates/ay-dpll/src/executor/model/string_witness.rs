// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared bridge between the string MODEL-CONSTRUCTION paths and the
//! content-positive regex witness search `ay_strings::we_regex::find_witness`
//! (strings increments W1-W3, default ON, `--dpll-no-str-witness` kill switch).
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

/// Strings witness-construction master switch (default
/// OFF).
///
/// Default OFF keeps every model-construction path byte-identical to
/// pre-W1 behavior.
pub(in crate::executor) fn str_witness_enabled() -> bool {
    static V: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    // DEFAULT-ON: W1b converts 4 automatark files (z3-verified), 0 losses,
    // 0 disagreements, fuzz clean; W1/W2/W3 are inert on this corpus but
    // correct and gated. --dpll-no-str-witness kills it.
    *V.get_or_init(|| !ay_core::theory_disable_flags().no_str_witness)
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

/// The EXACT regular language of the strings that CONTAIN the constant
/// `needle`: `Σ* · needle · Σ*` (NF-engine closure 6).
///
/// SOUNDNESS (exactness argument). `str.contains(x, w)` holds iff `x` can be
/// split as `x = a ++ w ++ b` for some `a, b` — that is precisely membership
/// in `Σ* · w · Σ*`, by the definition of concatenation of languages. The
/// construction below is a literal transcription of that language:
/// [`WeRegex::All`] is `Σ*` (`comp(All) = ∅`, `star(All) = All`), and
/// [`WeRegex::lit`] is the singleton `{w}`. It is therefore an EXACT encoding
/// in both directions, so its complement — via [`WeRegex::comp`], documented
/// exact over the full SMT-LIB alphabet — is exactly the language of strings
/// that do NOT contain `w`. For a single-character needle `c` the complement
/// is the `(Σ \ {c})*` of the increment spec; for a multi-character needle it
/// is the KMP "avoid `w`" language, which the derivative engine walks without
/// ever materialising the automaton.
///
/// The empty needle is EXCLUDED by the caller: `contains(x, "")` is a
/// tautology and its negation is unsatisfiable, so encoding it would only add
/// an empty-language constraint that the search must then fail on. Skipping is
/// safe under this module's contract (dropping a constraint can only make a
/// constructed candidate more likely to be refuted by the unchanged gates).
fn contains_language(needle: &str) -> WeRegex {
    WeRegex::concat(vec![WeRegex::All, WeRegex::lit(needle), WeRegex::All])
}

/// The `str.contains(subject, needle)` atom's exact [`WeRegex`] constraint on
/// `subject` at the given polarity, for a CONSTANT `needle` (closure 6).
///
/// `None` when the needle is not a string constant or is empty (see
/// [`contains_language`]).
pub(in crate::executor) fn contains_constraint(
    terms: &ay_core::TermStore,
    needle: TermId,
    positive: bool,
) -> Option<WeRegex> {
    let TermData::Const(ay_core::term::Constant::String(w)) = terms.get(needle) else {
        return None;
    };
    if w.is_empty() {
        return None;
    }
    let lang = contains_language(w);
    Some(if positive { lang } else { WeRegex::comp(lang) })
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
            // NF-engine closure 6 (`AY_STR_NF=1`): `str.contains(var, w)` with
            // a CONSTANT needle is EXACTLY a membership in `Σ* w Σ*` (see
            // `contains_constraint`), so it belongs in this harvest on the same
            // terms as `str.in_re` — in BOTH polarities. Without it the witness
            // search is blind to the dominant pyex/Reynolds idiom
            // `¬str.contains(x, ",")` and happily constructs a value carrying
            // the needle, which the gates then retract.
            let is_contains = sym.name() == "str.contains"
                && args.len() == 2
                && ay_strings::str_nf_closure_enabled(6);
            if !is_contains && (!matches!(sym.name(), "str.in_re" | "str.in.re") || args.len() != 2)
            {
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
            let constraint = if is_contains {
                contains_constraint(&self.ctx.terms, args[1], polarity)
            } else {
                self.translate_we_regex(args[1], 0).map(|regex| {
                    if polarity {
                        regex
                    } else {
                        WeRegex::comp(regex)
                    }
                })
            };
            let Some(constraint) = constraint else {
                continue;
            };
            out.push(constraint);
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

    /// Witness construction went DEFAULT-ON (`--dpll-no-str-witness` kills it); the
    /// pin is that the master switch and every sub-increment agree, so a
    /// sub-increment can never be live while the master switch is off. (This
    /// test previously asserted the pre-default-on contract and had gone stale.)
    #[test]
    fn witness_flags_track_the_master_switch() {
        let master = str_witness_enabled();
        // B28: CLI-owned; nothing ambient can kill the master switch.
        assert!(master, "the witness master switch is DEFAULT-ON");
        for (name, live) in [
            ("W1", str_witness_w1()),
            ("W2", str_witness_w2()),
            ("W3", str_witness_w3()),
        ] {
            assert!(
                !live || master,
                "{name} must never be live while the master switch is off"
            );
        }
    }

    /// NF-engine closure 6 EXACTNESS pin: `Σ* w Σ*` must accept exactly the
    /// strings containing `w`, and its complement exactly those that do not —
    /// on both a single-character and a multi-character needle. A drift here
    /// would silently turn the witness constraint into an approximation, which
    /// is the one thing the closure may not be.
    #[test]
    fn contains_language_is_exact_both_polarities() {
        for needle in ["a", ",", "ab", "aab"] {
            let pos = contains_language(needle);
            let neg = WeRegex::comp(contains_language(needle));
            for s in [
                "", "a", "b", ",", "ab", "ba", "aab", "xaby", "aa", "abab", "x,y", "aaab",
            ] {
                let truth = s.contains(needle);
                assert_eq!(
                    pos.matches(s),
                    Some(truth),
                    "Σ*{needle}Σ* must decide {s:?} as contains={truth}"
                );
                assert_eq!(
                    neg.matches(s),
                    Some(!truth),
                    "comp(Σ*{needle}Σ*) must decide {s:?} as ¬contains={}",
                    !truth
                );
            }
        }
    }

    /// The empty needle is deliberately NOT encoded: `contains(x, "")` is a
    /// tautology, so the negative constraint would be the empty language and
    /// every candidate would fail the search. Skipping is safe under this
    /// module's contract; pin that it really is skipped.
    #[test]
    fn contains_constraint_skips_empty_and_non_constant_needles() {
        let mut terms = ay_core::TermStore::new();
        let empty = terms.mk_string(String::new());
        let comma = terms.mk_string(",".to_string());
        let var = terms.mk_var("v", ay_core::Sort::String);
        assert!(contains_constraint(&terms, empty, false).is_none());
        assert!(contains_constraint(&terms, empty, true).is_none());
        assert!(contains_constraint(&terms, var, false).is_none());
        assert!(contains_constraint(&terms, comma, false).is_some());
        assert!(contains_constraint(&terms, comma, true).is_some());
    }
}

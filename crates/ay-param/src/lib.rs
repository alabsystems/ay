// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![forbid(unsafe_code)]

//! THE PARAMETER SUBSTRATE: one place a knob is declared, resolved and audited.
//!
//! # What this replaces
//!
//! 799 distinct `AY_*` names across 1,160 literal `env::var` sites in twelve
//! crates. Only `ay-milp` has a ledger; the other ~470 names have no inventory, no
//! typo guard, no soundness class and no typed surface.
//!
//! # The three resolution shapes, preserved exactly
//!
//! `ay-milp` spells "this switch is on" **three different ways** at different call
//! sites, and `tune.rs` documents why unifying them silently is not an option:
//! normalising would change behaviour at whichever sites did not match the normal
//! form, and every result in `reports/` is an A/B between two environments. So
//! [`Shape`] enumerates them rather than picking one, and a migration that changes a
//! site's shape is a deliberate act with its own measurement.
//!
//! The trap worth naming: **`--dfs` reads as ON**, because [`Shape::On`]
//! tests presence and nothing else.
//!
//! # No `linkme`, no `inventory`, no ctors
//!
//! A link-time registry is the obvious design and it is wrong here. `ay-sat`,
//! `ay-pb` and `ay-maxsat` are `optional = true` behind the `cli` feature, `ay-ffi`
//! is built as `cdylib`/`staticlib`/`rlib`, the musl build goes through a zig-cc
//! driver, and `[profile.release-perf]` is `lto = "fat"`. A registry that silently
//! drops entries under any of those is **strictly worse than a hand-maintained
//! table**: the hand table's staleness is caught by a source scan, and a dropped
//! `link_section` is caught by nothing.
//!
//! Totality is therefore a CI property, not a language one — `knobs.rs` +
//! `tests/env_ledger.rs` raised a level. That is the honest claim and no more.
//!
//! # Prior art
//!
//! LLVM's `cl::opt` has given `-help` a total view of self-registering typed
//! options for twenty years, and Kconfig is the same idea for build settings. The
//! parts specific to AY are the soundness class, the evidence record, and the
//! trap-derived migration alphabet below — not the registry.

use std::ffi::OsStr;

/// How a call site turns an environment string into a decision.
///
/// Every variant is a shape that exists in the tree today. They are preserved
/// individually because they disagree on real inputs, and the disagreements are
/// load-bearing for reproducing recorded measurements.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Shape {
    /// PRESENCE means on: `env::var_os(K).is_some()`.
    ///
    /// The trap: `K=0` reads as **on**. Documented in `tune.rs` against
    /// `--dfs`, and preserved deliberately — changing it would silently flip
    /// behaviour for anyone who ever wrote `=0` expecting off.
    On,
    /// Exactly `"1"` means on; any other explicit value means off.
    OnStrict,
    /// On unless explicitly `"0"`, and on when unset.
    OnUnlessZero,
    /// A parsed integer, falling back to the compiled default.
    ///
    /// An explicitly set but UNPARSEABLE value takes the compiled default, not the
    /// policy. `tune.rs` gives the reason: the pre-migration sites spell it
    /// `.ok().and_then(|v| v.parse().ok()).unwrap_or(DEFAULT)`, so
    /// `--gmi-rounds=garbage` yields `DEFAULT`, and preserving that is what
    /// makes a migrated site behave identically for *every* input string.
    Num,
    /// A finite, non-negative real: a share, a multiplier, or a seconds value.
    ///
    /// The domain is part of the shape, not a caller's problem: every consumer
    /// feeds these to `Duration::from_secs_f64`/`mul_f64`, **both of which panic**
    /// on a negative or non-finite input. `--sat-stop-mult=-1` was an abort
    /// inside a consumer's solve.
    Real,
}

/// Values outside this range are rejected by [`Shape::Real`].
///
/// The upper bound is not decoration. `Duration::from_secs_f64` panics above
/// `u64::MAX` seconds, so `--sat-stop-secs=1e26` — a perfectly well-formed
/// `f64` — aborted the process. `1e15` seconds is ~31 million years.
pub const MAX_REAL: f64 = 1e15;

/// Is `v` an admissible [`Shape::Real`]?
#[must_use]
pub fn in_real_domain(v: f64) -> bool {
    v.is_finite() && (0.0..=MAX_REAL).contains(&v)
}

/// Resolve a boolean knob from its raw environment value.
///
/// `raw` is `env::var_os(name)`. Passing the `OsStr` rather than a `&str` preserves
/// the presence-vs-UTF-8 distinction [`Shape::On`] rests on: a non-UTF-8 value is
/// *present* to `var_os` and *absent* to `var`, and collapsing that would silently
/// turn a consumer's kill switch off.
#[must_use]
pub fn resolve_flag(shape: Shape, raw: Option<&OsStr>, default: bool) -> bool {
    match shape {
        Shape::On => raw.is_some(),
        Shape::OnStrict => raw.and_then(OsStr::to_str) == Some("1"),
        Shape::OnUnlessZero => match raw.and_then(OsStr::to_str) {
            Some(v) => v != "0",
            None => default,
        },
        Shape::Num | Shape::Real => default,
    }
}

/// Resolve an integer knob. An explicit but unparseable value takes `default`.
///
/// **Not trimmed.** `--dive-max-pins` parse-fails today and leaves the
/// dive uncapped at `usize::MAX`; a `.trim()` here would reinterpret that exact
/// recipe as a cap of five — a 10^18 change, and a *different measured arm* from the
/// one the journal recorded against the identical string.
#[must_use]
pub fn resolve_num(raw: Option<&OsStr>, default: i64) -> i64 {
    match raw.and_then(OsStr::to_str) {
        Some(v) => v.parse::<i64>().unwrap_or(default),
        None => default,
    }
}

/// Resolve a real knob, rejecting anything outside [`in_real_domain`].
///
/// Rejection rather than clamping: a share of `0` is a materially different
/// instruction from a malformed one, and silently reading `-0.5` as "no budget"
/// would be a configuration the operator never asked for.
#[must_use]
pub fn resolve_real(raw: Option<&OsStr>, default: f64) -> f64 {
    match raw.and_then(OsStr::to_str) {
        Some(v) => v
            .parse::<f64>()
            .ok()
            .filter(|x| in_real_domain(*x))
            .unwrap_or(default),
        None => default,
    }
}

/// The input alphabet a migration must be proved behaviour-preserving over.
///
/// Every entry is a documented in-tree trap, not a guess:
///
/// | input | why it is here |
/// |---|---|
/// | `"0"` | reads as **on** under [`Shape::On`] (`--dfs`) |
/// | `" 5"` | must keep parse-failing or `--dive-max-pins` moves by 10^18 |
/// | `"1e26"` | a well-formed `f64` that aborted the process via `Duration` |
/// | `"-1"` | `--sat-stop-mult=-1` panicked `Duration::mul_f64` |
/// | `""` | present, parses as nothing |
/// | `"on"`, `"true"` | plausible operator input that every shape rejects |
///
/// The alphabet is the contribution here; differential equivalence checking is a
/// mature technique and this crate does not claim it.
pub const TRAP_ALPHABET: &[&str] = &["", "0", "1", "2", "-1", "on", "true", " 5", "1e26"];

#[cfg(test)]
mod tests {
    use super::*;
    use std::ffi::OsString;

    fn os(s: &str) -> OsString {
        OsString::from(s)
    }

    /// THE THREE SPELLINGS DISAGREE, which is why they are three variants and not
    /// one normalised accessor. `"0"` is the input that separates all three.
    #[test]
    fn the_three_on_shapes_disagree_on_zero() {
        let zero = os("0");
        let raw = Some(zero.as_os_str());
        assert!(
            resolve_flag(Shape::On, raw, false),
            "presence-is-on reads `=0` as ON -- the documented --dfs trap"
        );
        assert!(!resolve_flag(Shape::OnStrict, raw, false));
        assert!(!resolve_flag(Shape::OnUnlessZero, raw, true));
    }

    /// Unset is where `OnUnlessZero` differs from the other two: it defaults ON.
    #[test]
    fn unset_is_where_on_unless_zero_differs() {
        assert!(!resolve_flag(Shape::On, None, true), "absence is absence");
        assert!(!resolve_flag(Shape::OnStrict, None, true));
        assert!(resolve_flag(Shape::OnUnlessZero, None, true));
    }

    /// A non-UTF-8 value is PRESENT to `On` and unparseable to everything else.
    /// Collapsing this would silently turn a consumer's kill switch off.
    #[test]
    fn a_non_utf8_value_is_present_but_not_parseable() {
        #[cfg(unix)]
        {
            use std::os::unix::ffi::OsStringExt;
            let bad = OsString::from_vec(vec![0xff, 0xfe]);
            let raw = Some(bad.as_os_str());
            assert!(resolve_flag(Shape::On, raw, false), "var_os sees it");
            assert!(!resolve_flag(Shape::OnStrict, raw, false), "var does not");
            assert_eq!(resolve_num(raw, 7), 7, "falls back to the compiled default");
        }
    }

    /// The whole trap alphabet must resolve without panicking, on every shape. This
    /// is the property that makes a migration safe to apply mechanically.
    #[test]
    fn no_input_in_the_trap_alphabet_panics_on_any_shape() {
        for s in TRAP_ALPHABET {
            let v = os(s);
            let raw = Some(v.as_os_str());
            for shape in [
                Shape::On,
                Shape::OnStrict,
                Shape::OnUnlessZero,
                Shape::Num,
                Shape::Real,
            ] {
                let _ = resolve_flag(shape, raw, false);
            }
            let _ = resolve_num(raw, 0);
            let _ = resolve_real(raw, 0.0);
        }
    }

    /// The two inputs that were real aborts: a negative multiplier and an
    /// over-large seconds value. Both must resolve to the compiled default rather
    /// than reach `Duration`.
    #[test]
    fn the_values_that_aborted_a_consumer_resolve_to_the_default() {
        for bad in ["-1", "1e26", "nan", "inf"] {
            let v = os(bad);
            assert_eq!(
                resolve_real(Some(v.as_os_str()), 1.5),
                1.5,
                "{bad} must not reach Duration"
            );
        }
        // ... and a legitimate zero is NOT malformed and must survive.
        let z = os("0");
        assert_eq!(resolve_real(Some(z.as_os_str()), 1.5), 0.0);
    }

    /// Whitespace is not tolerated, deliberately: `" 5"` parse-fails today, and
    /// reinterpreting it would change a recorded arm.
    #[test]
    fn leading_whitespace_still_parse_fails() {
        let v = os(" 5");
        assert_eq!(resolve_num(Some(v.as_os_str()), 99), 99);
    }
}

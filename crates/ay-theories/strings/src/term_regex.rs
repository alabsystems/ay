// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact translation from ground SMT-LIB regex terms to [`WeRegex`].
//!
//! The word-equation/witness machinery and the ground membership evaluator
//! both consume regex terms. Keeping their translation here ensures that SAT
//! construction, UNSAT pruning, and derivative evaluation agree on the
//! language denoted by every supported term.
//!
//! Translation is exact-or-bail: unsupported or non-ground constructs, depth
//! and size limit exhaustion, and a caller-supplied work-budget stop all return
//! `None`. Callers must treat `None` as no information and use their existing
//! conservative fallback.

use ay_core::term::{Constant, TermData, TermId, TermStore};
use ay_core::Symbol;

use crate::we_regex::WeRegex;

/// Bounds for one exact term-to-regex translation.
///
/// These limits control work only. Every returned [`WeRegex`] is exactly
/// equivalent to the source term regardless of the chosen limits.
#[derive(Debug, Clone, Copy)]
pub struct TranslateLimits {
    /// Maximum node size of the translated regex.
    pub max_size: usize,
    /// Largest `(_ re.loop lo hi)` upper bound to unroll.
    pub max_loop: u32,
    /// Whether a larger loop may use the exact counter-carrying
    /// [`WeRegex::loop_bounded`] representation instead of bailing.
    pub bounded_loop_node: bool,
    /// Maximum recursive translation depth, including depth zero at the root.
    pub max_depth: usize,
}

impl TranslateLimits {
    /// Limits for concrete ground-membership evaluation.
    #[must_use]
    pub fn for_ground_eval() -> Self {
        Self {
            max_size: 4096,
            max_loop: 12,
            bounded_loop_node: true,
            max_depth: 32,
        }
    }
}

/// Translate ground regex term `term` into an exactly equivalent [`WeRegex`].
///
/// Returns `None` for unsupported or non-ground syntax and when a limit is
/// reached.
#[must_use]
pub fn translate(terms: &TermStore, term: TermId, limits: &TranslateLimits) -> Option<WeRegex> {
    translate_with_charge(terms, term, limits, &mut |_| true)
}

/// [`translate`] with a cooperative structural-work charge.
///
/// The ground evaluator uses this to keep speculative derivative translation
/// inside the same operation-wide budget as its memoised fallback. Returning
/// `false` from `charge` stops before the corresponding structural step.
pub(crate) fn translate_with_charge(
    terms: &TermStore,
    term: TermId,
    limits: &TranslateLimits,
    charge: &mut impl FnMut(usize) -> bool,
) -> Option<WeRegex> {
    let out = translate_at(terms, term, 0, limits, charge)?;
    (out.size() <= limits.max_size).then_some(out)
}

fn translate_at(
    terms: &TermStore,
    term: TermId,
    depth: usize,
    limits: &TranslateLimits,
    charge: &mut impl FnMut(usize) -> bool,
) -> Option<WeRegex> {
    if depth > limits.max_depth || !charge(1) {
        return None;
    }
    let TermData::App(sym, args) = terms.get(term) else {
        return None;
    };

    let out = match sym.name() {
        "re.none" if args.is_empty() => WeRegex::None,
        "re.all" if args.is_empty() => WeRegex::All,
        "re.allchar" if args.is_empty() => WeRegex::AnyChar,
        // SMT-LIB makes a range with non-singleton endpoints or lo > hi the
        // empty language; `WeRegex::range` performs exactly that fold.
        "re.range" if args.len() == 2 => WeRegex::range(
            string_constant(terms, args[0])?,
            string_constant(terms, args[1])?,
        ),
        "str.to_re" | "str.to.re" if args.len() == 1 => {
            let value = string_constant(terms, args[0])?;
            // Charge long literal materialization before cloning it. This is
            // the same structural weight used by `WeRegex::size`.
            let literal_size = 1usize.saturating_add(value.len() / 8);
            if literal_size > limits.max_size || !charge(literal_size) {
                return None;
            }
            WeRegex::lit(value)
        }
        "re.++" if !args.is_empty() => {
            WeRegex::concat(translate_all(terms, args, depth, limits, charge)?)
        }
        "re.union" if !args.is_empty() => {
            WeRegex::union(translate_all(terms, args, depth, limits, charge)?)
        }
        "re.inter" if !args.is_empty() => {
            WeRegex::inter(translate_all(terms, args, depth, limits, charge)?)
        }
        "re.*" if args.len() == 1 => {
            WeRegex::star(translate_at(terms, args[0], depth + 1, limits, charge)?)
        }
        "re.+" if args.len() == 1 => {
            WeRegex::plus(translate_at(terms, args[0], depth + 1, limits, charge)?)
        }
        "re.opt" if args.len() == 1 => {
            WeRegex::opt(translate_at(terms, args[0], depth + 1, limits, charge)?)
        }
        // Complement is over the full SMT-LIB string alphabet.
        "re.comp" if args.len() == 1 => {
            WeRegex::comp(translate_at(terms, args[0], depth + 1, limits, charge)?)
        }
        // re.diff(R, S) = R intersect complement(S).
        "re.diff" if args.len() == 2 => WeRegex::inter(vec![
            translate_at(terms, args[0], depth + 1, limits, charge)?,
            WeRegex::comp(translate_at(terms, args[1], depth + 1, limits, charge)?),
        ]),
        // `(_ re.loop lo hi) R` is the empty language for lo > hi. Small
        // loops use the existing exact unrolling; larger loops can retain exact
        // counters when the caller's policy permits it.
        "re.loop" if args.len() == 1 => {
            let Symbol::Indexed(_, indices) = sym else {
                return None;
            };
            if indices.len() != 2 {
                return None;
            }
            let (lo, hi) = (indices[0], indices[1]);
            if lo > hi {
                WeRegex::None
            } else if hi > limits.max_loop {
                if !limits.bounded_loop_node {
                    return None;
                }
                WeRegex::loop_bounded(
                    translate_at(terms, args[0], depth + 1, limits, charge)?,
                    lo,
                    hi,
                )
            } else {
                let body = translate_at(terms, args[0], depth + 1, limits, charge)?;
                let capacity = usize::try_from(hi).ok()?;
                if capacity > limits.max_size {
                    return None;
                }
                let mut parts = Vec::new();
                parts.try_reserve(capacity).ok()?;
                for _ in 0..lo {
                    parts.push(body.clone());
                }
                for _ in lo..hi {
                    parts.push(WeRegex::opt(body.clone()));
                }
                WeRegex::concat(parts)
            }
        }
        _ => return None,
    };

    (out.size() <= limits.max_size).then_some(out)
}

fn translate_all(
    terms: &TermStore,
    args: &[TermId],
    depth: usize,
    limits: &TranslateLimits,
    charge: &mut impl FnMut(usize) -> bool,
) -> Option<Vec<WeRegex>> {
    // Every source child costs at least one structural node before smart
    // constructor simplification. Declining a wider input is exact-or-bail and
    // prevents an attacker-controlled capacity request ahead of the size cap.
    if args.len() > limits.max_size {
        return None;
    }
    let mut out = Vec::new();
    out.try_reserve(args.len()).ok()?;
    for &arg in args {
        out.push(translate_at(terms, arg, depth + 1, limits, charge)?);
    }
    Some(out)
}

fn string_constant(terms: &TermStore, term: TermId) -> Option<&str> {
    match terms.get(term) {
        TermData::Const(Constant::String(value)) => Some(value),
        _ => None,
    }
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// ---------------------------------------------------------------------------
// `str.in_re` LENGTH-INVARIANT firewall emitter.
//
// Grounded in the verified `AySoundness.RegexThy` membership length invariants
// (`mem_len_dvd` / `mem_minLen_le` / `mem_maxLen_ge` and their conflict
// corollaries). Closes the shape
//
//     (assert (str.in_re X R))          -- X a declared String symbol
//     (assert (= (str.len X) C))        -- or <=, <, >=, >
//
// when the structural length abstraction of `R` is incompatible with the pin.
//
// AUTHORITY BOUNDARY (do not overstate this). The Lean side establishes exactly
// one thing: that no `List Nat` string is simultaneously in `L(re1)` and of the
// pinned length. Everything else is this emitter's obligation and is NOT
// discharged by any kernel check:
//
//   * that `re1` faithfully renders the SMT-LIB regex `R` (see
//     `parse_regex_ast`, which DECLINES on every constructor it cannot render
//     exactly or one-sidedly);
//   * that the string literals were decoded with SMT-LIB 2.6 semantics — they
//     come pre-decoded by `ay_core::unescape_string_contents` through
//     `ay_frontend::sexp`, which is the same decoder the solver itself used, so
//     the emitter cannot disagree with the solver about a literal's length;
//   * that both rendered assertions are IN SCOPE at the `check-sat` whose
//     verdict the artifact accompanies — enforced by declining outright on any
//     query that used `push`/`pop` or reached a second `check-sat`.
//
// "The emitted file kernel-checks with clean axioms" is NOT a soundness
// criterion for any of those three; a front-end misclassification produces a
// file that kernel-checks and certifies the WRONG query.
// ---------------------------------------------------------------------------

/// Every SMT-LIB operator name this emitter interprets STRUCTURALLY.
///
/// Each is checked against [`ay_frontend::is_reserved_op_name`] before any
/// rendering happens, so a future edit that makes one of them user-declarable
/// fails closed instead of conflating a user function with the builtin. Names
/// are matched EXACTLY — never by prefix: `re.x`, `str.lenient` and `bvf` are
/// all legal user symbols under the SMT-LIB simple-symbol grammar.
const REGEX_LEN_INTERPRETED_OPS: &[&str] = &[
    "str.in_re",
    "str.in.re",
    "str.len",
    "str.to_re",
    "str.to.re",
    "re.++",
    "re.union",
    "re.inter",
    "re.*",
    "re.+",
    "re.opt",
    "re.range",
    "re.none",
    "re.all",
    "re.allchar",
];

/// Regex constructors this emitter explicitly DECLINES, with the reason. Kept
/// as data so the decline is a deliberate, testable decision rather than an
/// accident of the matcher's shape (`re.loop` / `re.^` in particular reach the
/// parser as `IndexedApp`, so a `_ => None` arm would decline them by luck).
const REGEX_LEN_DECLINED_OPS: &[(&str, &str)] = &[
    // No sound one-sided length rule: the complement/difference of a language
    // with a length invariant has none.
    ("re.comp", "complement has no structural length bound"),
    ("re.diff", "difference has no structural length bound"),
    // Bounded repetition: `AySoundness.RegexThy` proves no kdvd/minLen/maxLen
    // extension for it, and the `n > m` case denotes the EMPTY language, which
    // a naive `cat`-unrolling would get wrong.
    (
        "re.loop",
        "bounded repetition is unproven in AySoundness.RegexThy",
    ),
    (
        "re.^",
        "bounded repetition is unproven in AySoundness.RegexThy",
    ),
];

/// The largest regex node count and total literal length the emitter renders.
/// Both bound the KERNEL's work: the emitted file discharges `kdvd`/`minLen`/
/// `maxLen` by `decide`, which reduces the structure inside the kernel.
const REGEX_LEN_MAX_NODES: usize = 128;
const REGEX_LEN_MAX_LITERAL_CHARS: usize = 2048;

/// The SMT-LIB alphabet is code points `0 .. 0x2FFFF` (SMT-LIB 2.6 Unicode
/// strings). A literal carrying anything outside it is not a well-formed
/// string literal, so the emitter declines rather than render a code point the
/// model does not describe.
const SMTLIB_MAX_CODE_POINT: u32 = 0x0002_FFFF;

/// A regular expression, mirroring `AySoundness.RegexThy.Re` constructor for
/// constructor. Every derived SMT-LIB form (`re.+`, `re.opt`, n-ary `re.++`)
/// is desugared here EXACTLY as the Lean `plus` / `opt` abbreviations do.
#[derive(Debug, Clone, PartialEq, Eq)]
enum ReAst {
    /// `re.none` — the empty language.
    Empty,
    /// `str.to_re w` — the singleton `{w}`, as code points.
    Lit(Vec<u32>),
    /// `re.allchar`, and the one-sided over-approximation of `re.range`.
    AnyChar,
    Cat(Box<ReAst>, Box<ReAst>),
    Union(Box<ReAst>, Box<ReAst>),
    Inter(Box<ReAst>, Box<ReAst>),
    Star(Box<ReAst>),
}

impl ReAst {
    /// Render as a Lean `AySoundness.RegexThy.Re` expression.
    fn render(&self, out: &mut String) {
        match self {
            Self::Empty => out.push_str("RegexThy.Re.none"),
            Self::Lit(w) => {
                out.push_str("(RegexThy.Re.lit [");
                for (i, c) in w.iter().enumerate() {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    out.push_str(&c.to_string());
                }
                out.push_str("])");
            }
            Self::AnyChar => out.push_str("RegexThy.Re.anyChar"),
            Self::Cat(a, b) | Self::Union(a, b) | Self::Inter(a, b) => {
                let head = match self {
                    Self::Cat(_, _) => "cat",
                    Self::Union(_, _) => "union",
                    _ => "inter",
                };
                out.push_str("(RegexThy.Re.");
                out.push_str(head);
                out.push(' ');
                a.render(out);
                out.push(' ');
                b.render(out);
                out.push(')');
            }
            Self::Star(a) => {
                out.push_str("(RegexThy.Re.star ");
                a.render(out);
                out.push(')');
            }
        }
    }

    /// Mirror of `AySoundness.RegexThy.kdvd`. The Lean side re-checks this by
    /// `decide`, so a disagreement makes the artifact fail to compile (fail
    /// closed) rather than certify anything.
    fn kdvd(&self, k: u64) -> bool {
        match self {
            Self::Empty => true,
            Self::Lit(w) => divides(k, w.len() as u64),
            Self::AnyChar => divides(k, 1),
            Self::Cat(a, b) | Self::Union(a, b) => a.kdvd(k) && b.kdvd(k),
            Self::Inter(a, b) => a.kdvd(k) || b.kdvd(k),
            Self::Star(a) => a.kdvd(k),
        }
    }

    /// A modulus `k` for which `kdvd k self` holds, chosen as large (i.e. as
    /// constraining) as the structural rule allows. `0` means "every member is
    /// empty" and is the strongest value, so it absorbs in the `gcd`.
    fn modulus(&self) -> u64 {
        match self {
            Self::Empty => 0,
            Self::Lit(w) => w.len() as u64,
            Self::AnyChar => 1,
            Self::Cat(a, b) | Self::Union(a, b) => gcd(a.modulus(), b.modulus()),
            // `kdvd` is one-sided (`||`) here, so either operand's modulus is
            // admissible; `0` (all-empty) is strictly the most constraining,
            // otherwise take the larger.
            Self::Inter(a, b) => {
                let (x, y) = (a.modulus(), b.modulus());
                if x == 0 || y == 0 {
                    0
                } else {
                    x.max(y)
                }
            }
            Self::Star(a) => a.modulus(),
        }
    }

    /// Mirror of `AySoundness.RegexThy.minLen`. `None` on arithmetic overflow.
    fn min_len(&self) -> Option<u64> {
        match self {
            Self::Empty | Self::Star(_) => Some(0),
            Self::Lit(w) => Some(w.len() as u64),
            Self::AnyChar => Some(1),
            Self::Cat(a, b) => a.min_len()?.checked_add(b.min_len()?),
            Self::Union(a, b) => Some(a.min_len()?.min(b.min_len()?)),
            Self::Inter(a, b) => Some(a.min_len()?.max(b.min_len()?)),
        }
    }

    /// Mirror of `AySoundness.RegexThy.maxLen`: `Some(n)` certifies the
    /// language is length-bounded by `n`, `None` gives up (fail-closed).
    fn max_len(&self) -> Option<u64> {
        match self {
            Self::Empty => Some(0),
            Self::Lit(w) => Some(w.len() as u64),
            Self::AnyChar => Some(1),
            Self::Cat(a, b) => a.max_len()?.checked_add(b.max_len()?),
            Self::Union(a, b) => Some(a.max_len()?.max(b.max_len()?)),
            Self::Inter(a, b) => match (a.max_len(), b.max_len()) {
                (Some(x), Some(y)) => Some(x.min(y)),
                (Some(x), None) => Some(x),
                (None, Some(y)) => Some(y),
                (None, None) => None,
            },
            // Only a language whose sole member is `ε` iterates to a bounded
            // language; anything else stars to an unbounded one.
            Self::Star(a) => match a.max_len() {
                Some(0) => Some(0),
                _ => None,
            },
        }
    }

    fn node_count(&self) -> usize {
        match self {
            Self::Empty | Self::Lit(_) | Self::AnyChar => 1,
            Self::Cat(a, b) | Self::Union(a, b) | Self::Inter(a, b) => {
                1 + a.node_count() + b.node_count()
            }
            Self::Star(a) => 1 + a.node_count(),
        }
    }

    fn literal_chars(&self) -> usize {
        match self {
            Self::Empty | Self::AnyChar => 0,
            Self::Lit(w) => w.len(),
            Self::Cat(a, b) | Self::Union(a, b) | Self::Inter(a, b) => {
                a.literal_chars() + b.literal_chars()
            }
            Self::Star(a) => a.literal_chars(),
        }
    }
}

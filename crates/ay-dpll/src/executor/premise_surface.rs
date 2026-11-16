// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The premises a published certificate may `assume`: the problem's own
//! assertions, as written, in a spelling-insensitive form.
//!
//! An external checker matches each `assume` of an Alethe certificate against
//! the premises it parsed from the problem file. AY's term-level provenance
//! checks cannot see a premise AY printed in a NORMALIZED form (a `define-fun`
//! expanded, `distinct` as `not =`, one conjunct of an `and`), because the
//! terms AY stores are already normalized. The `--strict-proofs` admission
//! decision and the `c ay.proof.certificate` disclosure in the `ay` binary
//! therefore compare the printed `assume` text with the authored assertions,
//! through [`normalize_premise_surface`].

use ay_core::kani_compat::DetHashSet as HashSet;

use super::proof_surface_syntax::{format_authored_frontend_term, format_frontend_term};
use super::Executor;

mod int_let;
pub use int_let::premise_int_let_binding;

/// Widest bit-vector literal [`normalize_premise_surface`] respells. A wider
/// literal keeps its own spelling, so it can only compare unequal (never
/// equal) to another spelling of the same value.
const MAX_CANONICAL_BV_WIDTH: usize = 4096;

/// The canonical `#b` spelling of a bit-vector literal given as `#b`, `#x` or
/// the indexed `(_ bvN W)` form, or `None` when `token` is not one (or is past
/// [`MAX_CANONICAL_BV_WIDTH`]).
fn canonical_bv_literal(token: &str) -> Option<String> {
    if let Some(bits) = token.strip_prefix("#b") {
        return (!bits.is_empty()
            && bits.len() <= MAX_CANONICAL_BV_WIDTH
            && bits.bytes().all(|b| b == b'0' || b == b'1'))
        .then(|| token.to_string());
    }
    if let Some(hex) = token.strip_prefix("#x") {
        if hex.is_empty() || hex.len() * 4 > MAX_CANONICAL_BV_WIDTH {
            return None;
        }
        let mut out = String::with_capacity(2 + hex.len() * 4);
        out.push_str("#b");
        for digit in hex.chars() {
            let value = digit.to_digit(16)?;
            out.push_str(&format!("{value:04b}"));
        }
        return Some(out);
    }
    let inner = token.strip_prefix("(_ bv")?.strip_suffix(')')?;
    let (value, width) = inner.split_once(' ')?;
    let width: usize = width.parse().ok()?;
    if width == 0
        || width > MAX_CANONICAL_BV_WIDTH
        || value.is_empty()
        || !value.bytes().all(|b| b.is_ascii_digit())
    {
        return None;
    }
    // Decimal to binary by repeated halving of the digit string: the value
    // may be wider than any machine integer.
    let mut digits: Vec<u8> = value.bytes().map(|b| b - b'0').collect();
    let mut bits = Vec::with_capacity(width);
    while digits.iter().any(|&d| d != 0) {
        let mut remainder = 0u8;
        for digit in &mut digits {
            let current = remainder * 10 + *digit;
            *digit = current / 2;
            remainder = current % 2;
        }
        bits.push(b'0' + remainder);
        if bits.len() > width {
            // The value does not fit the width: not a well-formed literal.
            return None;
        }
    }
    bits.resize(width, b'0');
    bits.reverse();
    Some(format!("#b{}", String::from_utf8(bits).ok()?))
}

/// Whether `symbol` may be written without `|...|` quotes (SMT-LIB 2.6
/// §3.1, simple symbols), so that `|symbol|` and `symbol` are one symbol.
fn is_simple_symbol(symbol: &str) -> bool {
    const RESERVED: [&str; 13] = [
        "!",
        "_",
        "as",
        "BINARY",
        "DECIMAL",
        "exists",
        "HEXADECIMAL",
        "forall",
        "let",
        "match",
        "NUMERAL",
        "par",
        "STRING",
    ];
    let mut chars = symbol.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    let allowed = |c: char| c.is_ascii_alphanumeric() || "~!@$%^&*_-+=<>.?/".contains(c);
    !first.is_ascii_digit()
        && allowed(first)
        && chars.all(allowed)
        && !RESERVED.contains(&symbol)
        // A bare `-2` is the number, so `|-2|` keeps its quotes.
        && !ay_frontend::sexp::is_negative_numeric_literal(symbol)
}

/// One atom of whitespace-normalized text, respelled canonically: a
/// bit-vector literal as `#b`, a decimal with an all-zero fraction as its
/// numeral (`0.0` and `0` are one constant where a real is expected), and a
/// quoted symbol that needs no quotes without them.
fn canonical_atom(atom: &str) -> String {
    if atom.starts_with('#') {
        return canonical_bv_literal(atom).unwrap_or_else(|| atom.to_string());
    }
    if let Some((whole, fraction)) = atom.split_once('.') {
        if !whole.is_empty()
            && whole.bytes().all(|b| b.is_ascii_digit())
            && !fraction.is_empty()
            && fraction.bytes().all(|b| b == b'0')
        {
            return whole.to_string();
        }
    }
    if let Some(inner) = atom.strip_prefix('|').and_then(|a| a.strip_suffix('|')) {
        if is_simple_symbol(inner) {
            return inner.to_string();
        }
    }
    atom.to_string()
}

/// Respell every literal and quoted symbol in whitespace-normalized text
/// canonically (see [`canonical_atom`]; `(_ bvN W)` is read as one literal).
fn canonicalize_atoms(text: &str) -> String {
    let bytes = text.as_bytes();
    let mut out = String::with_capacity(text.len());
    let mut i = 0usize;
    while i < bytes.len() {
        match bytes[i] {
            b'"' => {
                // A string literal is copied verbatim; `""` escapes a quote.
                let start = i;
                i += 1;
                while i < bytes.len() {
                    if bytes[i] == b'"' {
                        if bytes.get(i + 1) == Some(&b'"') {
                            i += 2;
                            continue;
                        }
                        i += 1;
                        break;
                    }
                    i += 1;
                }
                out.push_str(&text[start..i]);
            }
            b'|' => {
                let end = text[i + 1..]
                    .find('|')
                    .map_or(bytes.len(), |len| i + len + 2);
                out.push_str(&canonical_atom(&text[i..end]));
                i = end;
            }
            b'(' if text[i..].starts_with("(_ bv") => {
                let end = text[i..]
                    .find(')')
                    .map_or(bytes.len(), |close| i + close + 1);
                match canonical_bv_literal(&text[i..end]) {
                    Some(literal) => out.push_str(&literal),
                    None => out.push_str(&text[i..end]),
                }
                i = end;
            }
            b'(' | b')' | b' ' => {
                out.push(char::from(bytes[i]));
                i += 1;
            }
            _ => {
                let end = text[i..]
                    .find([' ', '(', ')', '"', '|'])
                    .map_or(bytes.len(), |len| i + len);
                out.push_str(&canonical_atom(&text[i..end]));
                i = end;
            }
        }
    }
    out
}

/// The form in which two spellings of one SMT-LIB term compare equal exactly
/// when a parser reads them as the same term: every run of whitespace outside
/// a string literal or a quoted symbol becomes one space (none next to a
/// parenthesis); every bit-vector literal is spelled `#b` (`#xAA`,
/// `#b10101010` and `(_ bv170 8)` are one constant); a decimal with an
/// all-zero fraction is its numeral (`0.0` where the input wrote `0` against a
/// real); and `|x|` is `x` when `x` needs no quotes. Nothing else is
/// rewritten: a `define-fun` name and its body, `distinct` and its `not =`
/// expansion, one conjunct and its `and`, `(= a b)` and `(= b a)` stay
/// different, because the external checker matches an `assume` against the
/// premises it PARSED and does not rewrite those.
///
/// Calibrated against `clean cert verify-external` on the certificates of the
/// merged tree before this check existed: token-for-token comparison called
/// certificates foreign that clean verifies (a `#b0` printed for an authored
/// `(_ bv0 1)`, `0.0` for `0`, `_3` for `|_3|`); each of those spellings is
/// now one form, and every certificate clean refused at an `assume` still
/// compares foreign.
#[must_use]
pub fn normalize_premise_surface(text: &str) -> String {
    canonicalize_atoms(&collapse_premise_whitespace(text))
}

fn collapse_premise_whitespace(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut chars = text.trim().chars().peekable();
    let mut pending_space = false;
    while let Some(c) = chars.next() {
        match c {
            '"' | '|' => {
                if pending_space && !out.ends_with('(') {
                    out.push(' ');
                }
                pending_space = false;
                out.push(c);
                // Copy the literal verbatim up to its closing delimiter. A
                // doubled `""` inside a string literal is an escaped quote.
                while let Some(inner) = chars.next() {
                    out.push(inner);
                    if inner == c {
                        if c == '"' && chars.peek() == Some(&'"') {
                            out.push(chars.next().unwrap_or('"'));
                            continue;
                        }
                        break;
                    }
                }
            }
            c if c.is_whitespace() => pending_space = !out.is_empty(),
            '(' | ')' => {
                // A space next to a parenthesis carries no token boundary.
                if pending_space && c == '(' && !out.ends_with('(') {
                    out.push(' ');
                }
                pending_space = false;
                out.push(c);
            }
            _ => {
                if pending_space && !out.ends_with('(') {
                    out.push(' ');
                }
                pending_space = false;
                out.push(c);
            }
        }
    }
    out
}

impl Executor {
    /// Every premise the current query's problem states VERBATIM, as
    /// whitespace-normalized text ([`normalize_premise_surface`]): each
    /// authored assertion on the current stack exactly as the problem wrote it
    /// (with and without its `!` annotations), each `check-sat-assuming`
    /// literal the caller supplied to the last query, and the premise
    /// `(= a body)` of each nullary `define-fun` the printer may read through
    /// (pinned carcara, run without `--apply-function-defs`, holds it).
    ///
    /// This is the reference an `assume` in a published certificate is
    /// compared against. An external checker matches an `assume` against the
    /// problem's own premises, so a leaf AY printed in a normalized form —
    /// `(not (= b c))` for an authored `(distinct b c)`, a `define-fun`
    /// application expanded, a bit-vector literal respelled, one conjunct of an
    /// authored `and` — is not a premise of the problem, whatever AY's
    /// term-level provenance says. The term-level detector cannot see those,
    /// because it compares the terms AY STORES, which are already normalized.
    ///
    /// `None` when an authored assertion on the stack has no retained surface
    /// syntax (a native-API assertion, or parsed retention off): the reference
    /// is then incomplete, and a caller must not read absence from it as
    /// foreignness or as authorship.
    #[must_use]
    pub fn authored_premise_surfaces(&self) -> Option<HashSet<String>> {
        let mut surfaces = HashSet::default();
        for assertion in self.ctx.authored_assertions_for_display() {
            match assertion {
                ay_frontend::AuthoredAssertionRef::Parsed(parsed) => {
                    surfaces.insert(normalize_premise_surface(&format_authored_frontend_term(
                        parsed,
                    )));
                    surfaces.insert(normalize_premise_surface(&format_frontend_term(parsed)));
                }
                ay_frontend::AuthoredAssertionRef::Elaborated(_) => return None,
            }
        }
        // Each nullary `define-fun` premise `(= a body)` the printer may
        // assume (`proof_authored_assume_spelling/export_surfaces.rs`): pinned
        // carcara, run without `--apply-function-defs`, holds it as a premise.
        for (name, body) in self.nullary_definition_premises() {
            surfaces.insert(normalize_premise_surface(&format!("(= {name} {body})")));
        }
        // The caller's `check-sat-assuming` literals AS WRITTEN, never the
        // solver's own (see `unsat_query_caller_assumptions`) and never their
        // elaborated terms: elaboration rewrites `(not (distinct a b))` to
        // `(= a b)`, and a certificate that assumes the rewritten form is one
        // an external checker rejects at that `assume`. With no current query
        // epoch the caller's literals are unknown; if any assumption was in
        // play the reference is incomplete. The same holds when assumptions
        // are bound but their surface syntax is not retained.
        let caller_assumptions = match self.unsat_query_caller_assumptions() {
            Some(assumptions) => assumptions,
            None if self.last_assumptions.as_ref().is_none_or(Vec::is_empty) => &[],
            None => return None,
        };
        if !caller_assumptions.is_empty() {
            let authored = self.unsat_query_authored_assumption_surfaces()?;
            surfaces.extend(authored.iter().cloned());
        }
        Some(surfaces)
    }
}

#[cfg(test)]
mod premise_surface_tests {
    use super::normalize_premise_surface as n;

    #[test]
    fn whitespace_never_distinguishes_two_spellings() {
        assert_eq!(n("( =  a\n\tb )"), "(= a b)");
        assert_eq!(
            n("(assume-free |a  b| \"x  y\")"),
            "(assume-free |a  b| \"x  y\")"
        );
    }

    #[test]
    fn every_bit_vector_literal_spelling_is_one_constant() {
        assert_eq!(n("#xAA"), "#b10101010");
        assert_eq!(n("(_ bv170 8)"), "#b10101010");
        assert_eq!(n("#b10101010"), "#b10101010");
        assert_eq!(n("(= mode (_ bv0 1))"), n("(= mode #b0)"));
        assert_eq!(
            n("(bvadd x (_ bv18446744073709551615 64))"),
            n("(bvadd x #xffffffffffffffff)")
        );
        // Width is part of the constant.
        assert_ne!(n("(_ bv1 2)"), n("#b1"));
        // A value that does not fit its width is left as written.
        assert_eq!(n("(_ bv4 2)"), "(_ bv4 2)");
        // Inside a quoted symbol or string nothing is a literal.
        assert_eq!(n("|#xAA|"), "|#xAA|");
        assert_eq!(n("\"#xAA\""), "\"#xAA\"");
    }

    #[test]
    fn a_quoted_simple_symbol_is_the_symbol() {
        assert_eq!(n("(= |_3| |num_vars|)"), "(= _3 num_vars)");
        assert_eq!(n("|self*.0#s4_2|"), "|self*.0#s4_2|");
        assert_eq!(n("|a b|"), "|a b|");
        assert_eq!(n("|let|"), "|let|");
        assert_eq!(n("|1x|"), "|1x|");
    }

    #[test]
    fn a_decimal_with_a_zero_fraction_is_its_numeral() {
        assert_eq!(n("(< x 0.0)"), n("(< x 0)"));
        assert_eq!(n("(< x 12.000)"), "(< x 12)");
        assert_ne!(n("(< x 0.5)"), n("(< x 0)"));
    }

    #[test]
    fn a_rewriting_the_checker_does_not_undo_stays_distinct() {
        assert_ne!(n("(distinct a b)"), n("(not (= a b))"));
        assert_ne!(n("(= a b)"), n("(= b a)"));
        assert_ne!(n("m1"), n("(= mode (_ bv0 1))"));
        assert_ne!(n("(and p q)"), n("p"));
    }
}

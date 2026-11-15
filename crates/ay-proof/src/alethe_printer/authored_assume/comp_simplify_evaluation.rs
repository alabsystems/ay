// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! When pinned carcara's `comp_simplify` EVALUATES a strict comparison
//! instead of rewriting it.
//!
//! `comp_simplify` (`checker/rules/simplification.rs` at `9a352ee`) rewrites
//! `(< t1 t2)` to `(not (<= t2 t1))` only when neither earlier case fires:
//! two `Term::as_fraction` constants evaluate to `true`/`false`, and one term
//! twice rewrites to `false`. The rule rewrites at the root to a fixpoint in
//! either direction, so the `(not (<= ..))` leg of a strict comparison
//! reversal (`comparison_reversal_step`) does not check when its `(< ..)`
//! side is evaluated. MEASURED on the operand-swapped comparison schema
//! (`surface_equivalence/comparison.rs`) before this decline: the confined
//! `forall_inst` instance `(> 3 3)` of `(forall ((w Int)) (> w 3))` shipped
//! `(= (not (<= 3 3)) (< 3 3))`, pinned carcara answered `invalid`, and
//! `--strict-proofs` published `unsat` with it.
//!
//! The judgement reads only printed text and errs toward "evaluated", which
//! can only decline a reversal carcara would have accepted:
//! * an operand spelled only with numerals, `-`, `/` and `div` counts as a
//!   constant (a superset of `as_fraction`);
//! * two operands count as one term when they agree after the parser's own
//!   identifications: a `|quoted|` symbol is its simple symbol, a numeral or
//!   decimal is its value (`2`, `2.0` and `2.00` alike), and a bit-vector
//!   literal (`#x03`, `#b00000011`, `(_ bv3 8)`) is its value and width;
//! * an operand carrying a `let` (which `--expand-let-bindings` expands) or
//!   an annotation `!` (whose `:named` carcara applies as a definition) is
//!   not judged at all, because parsing may rewrite it.

use num_bigint::BigUint;

/// Whether pinned carcara's `comp_simplify` may evaluate `(< left right)`
/// (either order) instead of rewriting it to `(not (<= right left))`.
pub(super) fn comp_simplify_evaluates_less_than(left: &str, right: &str) -> bool {
    let (Some(left), Some(right)) = (parsed_spelling(left), parsed_spelling(right)) else {
        return true;
    };
    left == right || (numeric_constant(&left) && numeric_constant(&right))
}

/// Whether pinned carcara's `comp_simplify` rewrites the self comparison
/// `(< operand operand)` / `(> operand operand)` through `(not (<= ..))`
/// instead of evaluating it: `operand` parses unchanged and is not a numeric
/// constant (two constants are evaluated, never reordered).
pub(super) fn comp_simplify_reorders_self_comparison(operand: &str) -> bool {
    parsed_spelling(operand).is_some_and(|tokens| !numeric_constant(&tokens))
}

/// Whether every token is a numeral or one of `( ) - / div`.
fn numeric_constant(tokens: &[String]) -> bool {
    !tokens.is_empty()
        && tokens.iter().all(|token| {
            matches!(token.as_str(), "(" | ")" | "s:-" | "s:/" | "s:div") || token.starts_with("n:")
        })
}

/// The tokens of `text` under the parser's identifications, or `None` when
/// parsing may rewrite it (`let`, `!`) or it does not tokenize.
fn parsed_spelling(text: &str) -> Option<Vec<String>> {
    let raw = tokens(text)?;
    if raw
        .iter()
        .any(|token| matches!(token.as_str(), "s:let" | "s:!"))
    {
        return None;
    }
    let mut spelled = Vec::with_capacity(raw.len());
    let mut index = 0;
    while index < raw.len() {
        if let Some(literal) = indexed_bitvector_literal(&raw[index..]) {
            spelled.push(literal);
            index += 5;
        } else {
            spelled.push(raw[index].clone());
            index += 1;
        }
    }
    Some(spelled)
}

/// `( _ bvN W )` at the start of `tokens`, as its value and width.
fn indexed_bitvector_literal(tokens: &[String]) -> Option<String> {
    let [open, underscore, value, width, close, ..] = tokens else {
        return None;
    };
    if open != "(" || underscore != "s:_" || close != ")" {
        return None;
    }
    let value = value.strip_prefix("s:bv")?;
    let width = width.strip_prefix("n:")?;
    if value.is_empty() || !value.bytes().all(|byte| byte.is_ascii_digit()) || width.contains('.') {
        return None;
    }
    let value = BigUint::parse_bytes(value.as_bytes(), 10)?;
    Some(format!("b:{value}:{width}"))
}

/// Parentheses, symbols (`s:`, quoted or not), numerals (`n:`), bit-vector
/// literals (`b:`) and string literals (`t:`); `None` for an unterminated
/// quote or string.
fn tokens(text: &str) -> Option<Vec<String>> {
    let mut out = Vec::new();
    let mut chars = text.char_indices().peekable();
    while let Some((start, c)) = chars.next() {
        match c {
            '(' | ')' => out.push(c.to_string()),
            '|' => {
                let mut symbol = String::new();
                loop {
                    match chars.next()? {
                        (_, '|') => break,
                        (_, '\\') => return None,
                        (_, ch) => symbol.push(ch),
                    }
                }
                out.push(format!("s:{symbol}"));
            }
            '"' => {
                let mut literal = String::new();
                loop {
                    match chars.next()? {
                        (_, '"') if chars.peek().is_some_and(|(_, ch)| *ch == '"') => {
                            chars.next();
                            literal.push_str("\"\"");
                        }
                        (_, '"') => break,
                        (_, ch) => literal.push(ch),
                    }
                }
                out.push(format!("t:{literal}"));
            }
            c if c.is_whitespace() => {}
            _ => {
                let mut end = start + c.len_utf8();
                while let Some(&(at, ch)) = chars.peek() {
                    if matches!(ch, '(' | ')' | '|' | '"') || ch.is_whitespace() {
                        break;
                    }
                    end = at + ch.len_utf8();
                    chars.next();
                }
                out.push(atom(&text[start..end]));
            }
        }
    }
    Some(out)
}

/// One unquoted word under the parser's identifications.
fn atom(word: &str) -> String {
    let digits = |part: &str| !part.is_empty() && part.bytes().all(|byte| byte.is_ascii_digit());
    let (whole, fraction) = word.split_once('.').unwrap_or((word, ""));
    if digits(whole) && ((fraction.is_empty() && !word.ends_with('.')) || digits(fraction)) {
        let whole = whole.trim_start_matches('0');
        let whole = if whole.is_empty() { "0" } else { whole };
        let fraction = fraction.trim_end_matches('0');
        return if fraction.is_empty() {
            format!("n:{whole}")
        } else {
            format!("n:{whole}.{fraction}")
        };
    }
    let literal = |digits: &str, radix: u32, bits: usize| {
        BigUint::parse_bytes(digits.as_bytes(), radix)
            .map(|value| format!("b:{value}:{}", digits.len() * bits))
    };
    let bitvector = match (word.strip_prefix("#x"), word.strip_prefix("#b")) {
        (Some(hex), _) => literal(hex, 16, 4),
        (_, Some(binary)) => literal(binary, 2, 1),
        _ => None,
    };
    bitvector.unwrap_or_else(|| format!("s:{word}"))
}

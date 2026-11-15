// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A printed term against the spelling a lane built for it, up to the spelling
//! of bit-vector literals.
//!
//! The circuit lane builds each node's spelling bottom-up from the term DAG,
//! and the printer spells every bit-vector constant there in binary. The
//! exporter, though, spells an assertion the problem wrote with `(_ bvN W)` or
//! `#x` literals as written: the published proof is the raw-authored bit-blast
//! refutation (ee79327a8; published since d739a98f5, build 11467, whose sweep
//! can print its lemma), and the whole-query lemma's root is the assertion's
//! term as written, so `format_term(root)` keeps `(_ bv1 64)` where the lane
//! built `#b0..01`. The lane compared the two strings exactly and declined
//! every such root. external-codegen writes every constant as `(_ bvN W)`, so from
//! build 11467 on its 128-bit arithmetic theorems (`AddU128`, `SubU128`,
//! `NegI128`) and the merged `PairJoin` spelling fell through to the complete
//! bit-blast, whose documents are two to five times larger and take Clean up
//! to sixty times longer: `SubU128` went from an 18.9 MB document in 6-12 s to
//! 83.5 MB in 30-60 s.
//!
//! The consumer reads both spellings as ONE constant, in an `assume` and as a
//! resolution pivot alike: Clean 5f09e36c fully verifies the circuit
//! document whose `assume`, subproof hypothesis and conclusion keep `(_ bv1 64)`
//! while its steps spell `#b0..01`, and rejects it once that hypothesis says
//! `(_ bv2 64)` (measured 2026-10-05 on external-codegen's `AddU128`). So exactly the
//! literal spelling is forgiven here: each literal is rewritten to the binary
//! digits of its own value at its own width, so a different value or width,
//! or any other difference of text, still compares unequal.

/// Whether `printed` (the printer's spelling of a term) and `built` (a lane's
/// spelling of the same term) are the same text once every bit-vector literal
/// is spelled in binary.
pub(super) fn prints_alike(printed: &str, built: &str) -> bool {
    printed == built
        || binary_spelled(printed).is_some_and(|printed| Some(printed) == binary_spelled(built))
}

/// The tokens of `text` with every `#x` literal and indexed `(_ bvN W)`
/// constant rewritten to `#b` digits; `None` for text this reader does not
/// tokenize (an unterminated quoted symbol or string).
fn binary_spelled(text: &str) -> Option<Vec<String>> {
    let tokens = tokens(text)?;
    let mut out = Vec::with_capacity(tokens.len());
    let mut index = 0;
    while index < tokens.len() {
        if let Some(binary) = tokens
            .get(index..index + 5)
            .and_then(|window| indexed_constant_in_binary(window))
        {
            out.push(binary);
            index += 5;
            continue;
        }
        let token = tokens[index];
        out.push(hexadecimal_in_binary(token).unwrap_or_else(|| token.to_string()));
        index += 1;
    }
    Some(out)
}

/// `( _ bvN W )` as `#b` digits: only for a decimal `N` below `2^W` and
/// `1 <= W <= 4096`.
fn indexed_constant_in_binary(window: &[&str]) -> Option<String> {
    let ["(", "_", name, width, ")"] = window else {
        return None;
    };
    let width: usize = width
        .bytes()
        .all(|byte| byte.is_ascii_digit())
        .then(|| width.parse().ok())
        .flatten()
        .filter(|width| (1..=4096).contains(width))?;
    let digits = name.strip_prefix("bv")?;
    if digits.is_empty() || !digits.bytes().all(|byte| byte.is_ascii_digit()) {
        return None;
    }
    let value = num_bigint::BigUint::parse_bytes(digits.as_bytes(), 10)?;
    if value.bits() > width as u64 {
        return None;
    }
    let bits = if value.bits() == 0 {
        String::new()
    } else {
        value.to_str_radix(2)
    };
    Some(format!("#b{}{bits}", "0".repeat(width - bits.len())))
}

/// `#xHH..` as `#b` digits, four per hexadecimal digit.
fn hexadecimal_in_binary(token: &str) -> Option<String> {
    let digits = token.strip_prefix("#x")?;
    if digits.is_empty() {
        return None;
    }
    let mut binary = String::with_capacity(2 + 4 * digits.len());
    binary.push_str("#b");
    for digit in digits.chars() {
        binary.push_str(&format!("{:04b}", digit.to_digit(16)?));
    }
    Some(binary)
}

/// SMT-LIB tokens: parentheses, quoted symbols `|..|`, string literals
/// `".."` (with `""` escapes), and whitespace-separated atoms.
fn tokens(text: &str) -> Option<Vec<&str>> {
    let bytes = text.as_bytes();
    let mut out = Vec::new();
    let mut index = 0;
    while index < bytes.len() {
        let start = index;
        match bytes[index] {
            byte if byte.is_ascii_whitespace() => {
                index += 1;
                continue;
            }
            b'(' | b')' => index += 1,
            b'|' => {
                index += 1 + bytes[index + 1..].iter().position(|&byte| byte == b'|')? + 1;
            }
            b'"' => {
                index += 1;
                loop {
                    index += bytes[index..].iter().position(|&byte| byte == b'"')? + 1;
                    if bytes.get(index) != Some(&b'"') {
                        break;
                    }
                    index += 1;
                }
            }
            _ => {
                while index < bytes.len()
                    && !bytes[index].is_ascii_whitespace()
                    && !matches!(bytes[index], b'(' | b')' | b'|' | b'"')
                {
                    index += 1;
                }
            }
        }
        out.push(text.get(start..index)?);
    }
    Some(out)
}

#[cfg(test)]
#[path = "literal_spelling_tests.rs"]
mod tests;

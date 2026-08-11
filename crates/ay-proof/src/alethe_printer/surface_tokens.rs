// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Balanced tokenization shared by surface-aware Alethe rules.

/// Failure from bounded tokenization of an effective Alethe surface term.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AletheSurfaceParseError {
    /// The input is not one complete, balanced SMT-LIB application.
    Malformed,
    /// The input or its immediate argument list exceeds the caller's cap.
    BudgetExceeded,
}

/// Split one exact rendered application into borrowed immediate arguments.
///
/// The scanner is UTF-8 safe and understands balanced applications, SMT-LIB
/// strings with doubled quotes, and AY/Z3 quoted-symbol escapes (`\|` and
/// `\\`). It allocates only the returned, caller-capped slice vector; argument
/// text remains borrowed from `input`.
pub fn split_alethe_application_bounded<'a>(
    input: &'a str,
    head: &str,
    max_arguments: usize,
    max_bytes: usize,
) -> Result<Vec<&'a str>, AletheSurfaceParseError> {
    if input.len() > max_bytes {
        return Err(AletheSurfaceParseError::BudgetExceeded);
    }
    let inner = input
        .strip_prefix('(')
        .and_then(|input| input.strip_suffix(')'))
        .ok_or(AletheSurfaceParseError::Malformed)?;
    let max_fields = max_arguments.saturating_add(1);
    let mut fields = split_smt_term_slices_bounded(inner, max_fields, max_bytes)?;
    if fields.first().copied() != Some(head) {
        return Err(AletheSurfaceParseError::Malformed);
    }
    fields.remove(0);
    Ok(fields)
}

/// Split an SMT-LIB fragment into balanced top-level terms.
pub(super) fn split_smt_terms(s: &str) -> Option<Vec<String>> {
    split_smt_term_slices_bounded(s, usize::MAX, usize::MAX)
        .ok()
        .map(|terms| terms.into_iter().map(str::to_string).collect())
}

/// Borrow the top-level terms in one SMT-LIB fragment under explicit caps.
pub(super) fn split_smt_term_slices_bounded(
    input: &str,
    max_terms: usize,
    max_bytes: usize,
) -> Result<Vec<&str>, AletheSurfaceParseError> {
    if input.len() > max_bytes {
        return Err(AletheSurfaceParseError::BudgetExceeded);
    }
    let bytes = input.as_bytes();
    let mut terms = Vec::with_capacity(max_terms.min(8));
    let mut index = 0usize;
    while index < bytes.len() {
        while index < bytes.len() && bytes[index].is_ascii_whitespace() {
            index += 1;
        }
        if index == bytes.len() {
            break;
        }
        if terms.len() >= max_terms {
            return Err(AletheSurfaceParseError::BudgetExceeded);
        }
        let start = index;
        match bytes[index] {
            b'(' => {
                index = scan_parenthesized_term(bytes, index)?;
            }
            b'"' => {
                index = scan_string_term(bytes, index)?;
            }
            b'|' => {
                index = scan_quoted_symbol(bytes, index)?;
            }
            b')' => return Err(AletheSurfaceParseError::Malformed),
            _ => {
                while index < bytes.len()
                    && !bytes[index].is_ascii_whitespace()
                    && !matches!(bytes[index], b'(' | b')' | b'"' | b'|')
                {
                    index += 1;
                }
            }
        }
        if start == index {
            return Err(AletheSurfaceParseError::Malformed);
        }
        // `start` and `index` are either input boundaries or ASCII delimiter
        // positions, hence valid UTF-8 slice boundaries even though scanning
        // itself is byte-oriented.
        terms.push(&input[start..index]);
    }
    Ok(terms)
}

fn scan_parenthesized_term(
    bytes: &[u8],
    mut index: usize,
) -> Result<usize, AletheSurfaceParseError> {
    let mut depth = 0usize;
    let mut quoted_symbol = false;
    let mut string = false;
    while index < bytes.len() {
        let byte = bytes[index];
        if string {
            if byte == b'"' {
                if bytes.get(index + 1) == Some(&b'"') {
                    index += 2;
                    continue;
                }
                string = false;
            }
            index += 1;
            continue;
        }
        if quoted_symbol {
            if byte == b'\\' && matches!(bytes.get(index + 1), Some(b'|' | b'\\')) {
                index += 2;
                continue;
            }
            if byte == b'|' {
                quoted_symbol = false;
            }
            index += 1;
            continue;
        }
        match byte {
            b'"' => string = true,
            b'|' => quoted_symbol = true,
            b'(' => {
                depth = depth
                    .checked_add(1)
                    .ok_or(AletheSurfaceParseError::Malformed)?;
            }
            b')' => {
                depth = depth
                    .checked_sub(1)
                    .ok_or(AletheSurfaceParseError::Malformed)?;
                index += 1;
                if depth == 0 {
                    return Ok(index);
                }
                continue;
            }
            _ => {}
        }
        index += 1;
    }
    Err(AletheSurfaceParseError::Malformed)
}

fn scan_string_term(bytes: &[u8], mut index: usize) -> Result<usize, AletheSurfaceParseError> {
    index += 1;
    while index < bytes.len() {
        if bytes[index] == b'"' {
            if bytes.get(index + 1) == Some(&b'"') {
                index += 2;
                continue;
            }
            return Ok(index + 1);
        }
        index += 1;
    }
    Err(AletheSurfaceParseError::Malformed)
}

fn scan_quoted_symbol(bytes: &[u8], mut index: usize) -> Result<usize, AletheSurfaceParseError> {
    index += 1;
    while index < bytes.len() {
        if bytes[index] == b'\\' && matches!(bytes.get(index + 1), Some(b'|' | b'\\')) {
            index += 2;
            continue;
        }
        if bytes[index] == b'|' {
            return Ok(index + 1);
        }
        index += 1;
    }
    Err(AletheSurfaceParseError::Malformed)
}

#[cfg(test)]
mod tests {
    use super::{split_alethe_application_bounded, AletheSurfaceParseError};

    #[test]
    fn bounded_application_handles_strings_and_escaped_quoted_symbols() {
        let input = r#"(and (= s "a)""b") |a\|b\\c| p)"#;
        let fields = split_alethe_application_bounded(input, "and", 3, input.len())
            .expect("balanced exotic operands");
        assert_eq!(fields, [r#"(= s "a)""b")"#, r#"|a\|b\\c|"#, "p"]);
    }

    #[test]
    fn bounded_application_distinguishes_malformed_and_budget_exhaustion() {
        assert_eq!(
            split_alethe_application_bounded("(and a b)", "and", 1, 64),
            Err(AletheSurfaceParseError::BudgetExceeded)
        );
        assert_eq!(
            split_alethe_application_bounded("(and a", "and", 2, 64),
            Err(AletheSurfaceParseError::Malformed)
        );
        assert_eq!(
            split_alethe_application_bounded("(andalso a)", "and", 2, 64),
            Err(AletheSurfaceParseError::Malformed)
        );
    }

    #[test]
    fn bounded_application_accepts_legal_delimiter_adjacency() {
        assert_eq!(
            split_alethe_application_bounded("(and(not a)(not b))", "and", 2, 64)
                .expect("head-to-list adjacency"),
            ["(not a)", "(not b)"]
        );
        assert_eq!(
            split_alethe_application_bounded("(and (not a)(not b))", "and", 2, 64)
                .expect("list-to-list adjacency"),
            ["(not a)", "(not b)"]
        );
    }
}

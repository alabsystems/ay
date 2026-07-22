// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Parse SMT-LIB `(get-value ...)` output into a variable->value map.
///
/// ay outputs get-value results in the form:
/// ```text
/// ((x 5)
///  (y (- 3))
///  (z true))
/// ```
///
/// When the optimization loop issues multiple `(get-value ...)` commands,
/// ay returns multiple response blocks:
/// ```text
/// ((x 1) (y 2))
/// ((obj 5))
/// ```
///
/// This parser handles both single and multi-block responses, merging all
/// pairs into one map. Nested S-expressions for negative integers `(- N)`
/// are preserved as-is.
pub fn parse_get_value(lines: &[String]) -> Result<HashMap<String, String>, SolverError> {
    let mut values = HashMap::default();
    let joined = lines.join(" ");

    let content = joined.trim();
    if content.is_empty() {
        return Ok(values);
    }

    let mut chars = content.chars().peekable();

    // Parse one or more blocks: ((name val) ...) ((name val) ...)
    loop {
        skip_whitespace(&mut chars);
        match chars.peek() {
            None => break,
            Some(&'(') => {
                chars.next(); // consume outer '(' of this block
                parse_pairs_in_block(&mut chars, &mut values);
                // consume the outer ')' that closes this block
                skip_whitespace(&mut chars);
                if chars.peek() == Some(&')') {
                    chars.next();
                }
            }
            Some(_) => {
                chars.next(); // skip unexpected chars
            }
        }
    }

    Ok(values)
}

/// Parse `(name value)` pairs inside one response block.
///
/// Expects to be called after the outer `(` has been consumed.
/// Stops when it sees the matching `)` or runs out of input.
fn parse_pairs_in_block(
    chars: &mut std::iter::Peekable<std::str::Chars<'_>>,
    values: &mut HashMap<String, String>,
) {
    loop {
        skip_whitespace(chars);
        match chars.peek() {
            None | Some(&')') => break,
            Some(&'(') => {
                chars.next(); // consume '('
                skip_whitespace(chars);
                let name = read_token(chars);
                skip_whitespace(chars);
                let value = read_sexp_value(chars);
                skip_whitespace(chars);
                if chars.peek() == Some(&')') {
                    chars.next();
                }
                if !name.is_empty() {
                    values.insert(name, value);
                }
            }
            Some(_) => {
                chars.next();
            }
        }
    }
}

/// Parse an SMT-LIB integer value string to i64.
///
/// Handles both positive integers ("42") and negative integers in
/// SMT-LIB format ("(- 42)").
pub fn parse_smt_int(s: &str) -> Result<i64, SolverError> {
    let s = s.trim();
    if let Some(inner) = s.strip_prefix("(- ") {
        if let Some(num_str) = inner.strip_suffix(')') {
            // Parse as u64 to handle i64::MIN correctly: its absolute value
            // (9223372036854775808) overflows i64 but fits in u64.
            let n: u64 = num_str
                .trim()
                .parse()
                .map_err(|_| SolverError::ParseIntError(s.to_string()))?;
            if i64::try_from(n).is_ok() {
                Ok(-(n as i64))
            } else if n == (i64::MAX as u64) + 1 {
                Ok(i64::MIN)
            } else {
                Err(SolverError::ParseIntError(s.to_string()))
            }
        } else {
            Err(SolverError::ParseIntError(s.to_string()))
        }
    } else {
        s.parse::<i64>()
            .map_err(|_| SolverError::ParseIntError(s.to_string()))
    }
}

// --- S-expression parsing helpers ---

fn skip_whitespace(chars: &mut std::iter::Peekable<std::str::Chars<'_>>) {
    while let Some(&c) = chars.peek() {
        if c.is_whitespace() {
            chars.next();
        } else {
            break;
        }
    }
}

fn read_token(chars: &mut std::iter::Peekable<std::str::Chars<'_>>) -> String {
    let mut token = String::new();
    while let Some(&c) = chars.peek() {
        if c.is_whitespace() || c == ')' || c == '(' {
            break;
        }
        token.push(c);
        chars.next();
    }
    token
}

/// Read a value which may be a simple token or a nested S-expression like `(- 3)`.
fn read_sexp_value(chars: &mut std::iter::Peekable<std::str::Chars<'_>>) -> String {
    skip_whitespace(chars);
    match chars.peek() {
        Some(&'(') => {
            // Read until matching close paren
            let mut depth = 0;
            let mut value = String::new();
            while let Some(&c) = chars.peek() {
                if c == '(' {
                    depth += 1;
                } else if c == ')' {
                    depth -= 1;
                    if depth == 0 {
                        value.push(c);
                        chars.next();
                        return value;
                    }
                }
                value.push(c);
                chars.next();
            }
            value
        }
        _ => read_token(chars),
    }
}

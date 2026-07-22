// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! Shared SMT-LIB string operation evaluation.
//!
//! Pure functions implementing SMT-LIB string operation semantics.
//! Used by both the string theory solver (`core.rs`) and the DPLL
//! model evaluator (`ay-dpll/executor/model/mod.rs`) to ensure
//! identical semantics (#5813).

use num_bigint::BigInt;

/// Evaluate `str.at(s, i)`: character at position i (0-based, char-level).
///
/// Returns empty string if i < 0 or i >= |s| (SMT-LIB semantics).
pub fn eval_str_at(s: &str, i: &BigInt) -> Option<String> {
    // An index outside `usize` is either negative or `>= |s|`: both give "".
    let Ok(idx) = usize::try_from(i) else {
        return Some(String::new());
    };
    Some(s.chars().nth(idx).map_or(String::new(), |c| c.to_string()))
}

/// Evaluate `str.substr(s, i, n)`: substring of s starting at i with length n.
///
/// SMT-LIB semantics: if i < 0 or i >= |s| or n <= 0, returns "".
/// Otherwise returns s[i..min(i+n, |s|)] — note `n` only ever CLAMPS, so an
/// `n` too large for a machine integer selects the whole suffix rather than
/// making the operation unevaluable (#string-substr-length-overflow).
pub fn eval_str_substr(s: &str, i: &BigInt, n: &BigInt) -> Option<String> {
    if *n <= BigInt::from(0) {
        return Some(String::new());
    }
    // A start outside `usize` is either negative or `>= |s|`: both give "".
    let Ok(start) = usize::try_from(i) else {
        return Some(String::new());
    };
    let chars: Vec<char> = s.chars().collect();
    if start >= chars.len() {
        return Some(String::new());
    }
    let avail = chars.len() - start;
    let take = usize::try_from(n).map_or(avail, |v| std::cmp::min(v, avail));
    Some(chars[start..start + take].iter().collect())
}

/// Evaluate `str.replace(s, t, u)`: replace first occurrence of t in s with u.
///
/// SMT-LIB semantics: if t is empty, prepend u to s.
/// If t is not found, return s unchanged.
pub fn eval_str_replace(s: &str, t: &str, u: &str) -> String {
    if t.is_empty() {
        // SMT-LIB: str.replace(s, "", u) = str.++(u, s)
        let mut result = u.to_string();
        result.push_str(s);
        return result;
    }
    // Replace first occurrence only.
    match s.find(t) {
        Some(pos) => {
            let mut result = s[..pos].to_string();
            result.push_str(u);
            result.push_str(&s[pos + t.len()..]);
            result
        }
        None => s.to_string(),
    }
}

/// Evaluate `str.indexof(s, t, i)`: index of first occurrence of t in s starting from i.
///
/// SMT-LIB semantics: returns -1 if t is not found or i < 0 or i > |s|.
/// If t is empty and 0 <= i <= |s|, returns i.
pub fn eval_str_indexof(s: &str, t: &str, start: &BigInt) -> Option<BigInt> {
    let chars: Vec<char> = s.chars().collect();
    // A start outside `usize` is either negative or `> |s|`: both give -1.
    let Ok(i) = usize::try_from(start) else {
        return Some(BigInt::from(-1));
    };
    if i > chars.len() {
        return Some(BigInt::from(-1));
    }
    if t.is_empty() {
        return Some(BigInt::from(i));
    }
    // Search from position i in char-level representation.
    let suffix: String = chars[i..].iter().collect();
    let t_chars: Vec<char> = t.chars().collect();
    let t_str: String = t_chars.iter().collect();
    match suffix.find(&t_str) {
        Some(byte_pos) => {
            // Convert byte offset to char offset.
            let char_offset = suffix[..byte_pos].chars().count();
            Some(BigInt::from(i + char_offset))
        }
        None => Some(BigInt::from(-1)),
    }
}

/// Evaluate `str.to_int(s)`: convert string to integer.
///
/// SMT-LIB semantics: returns -1 if s contains non-digit characters or is empty.
pub fn eval_str_to_int(s: &str) -> BigInt {
    if s.is_empty() || !s.chars().all(|c| c.is_ascii_digit()) {
        BigInt::from(-1)
    } else {
        s.parse::<BigInt>().unwrap_or(BigInt::from(-1))
    }
}

/// Evaluate `str.from_int(n)`: convert non-negative integer to string.
///
/// SMT-LIB semantics: returns "" if n < 0.
pub fn eval_str_from_int(n: &BigInt) -> String {
    if *n < BigInt::from(0) {
        String::new()
    } else {
        n.to_string()
    }
}

/// Evaluate `str.replace_all(s, t, u)`: replace all occurrences of t in s with u.
///
/// SMT-LIB semantics: if t is empty, returns s unchanged.
pub fn eval_str_replace_all(s: &str, t: &str, u: &str) -> String {
    if t.is_empty() {
        return s.to_string();
    }
    s.replace(t, u)
}

/// Evaluate `str.to_code(s)`: Unicode code point of single-character string.
///
/// SMT-LIB semantics: returns -1 if |s| != 1; otherwise the code point
/// (in the SMT-LIB character universe [0, 196607]).
pub fn eval_str_to_code(s: &str) -> BigInt {
    let mut chars = s.chars();
    match (chars.next(), chars.next()) {
        (Some(c), None) => {
            let cp = c as u32;
            if cp <= 196_607 {
                BigInt::from(cp)
            } else {
                BigInt::from(-1)
            }
        }
        _ => BigInt::from(-1),
    }
}

/// Evaluate `str.from_code(n)`: character from Unicode code point.
///
/// SMT-LIB semantics: returns "" if n < 0 or n > 196607 or n is not a
/// valid Unicode scalar value.
pub fn eval_str_from_code(n: &BigInt) -> String {
    let val: i64 = match n.try_into() {
        Ok(v) => v,
        Err(_) => return String::new(),
    };
    if !(0..=196_607).contains(&val) {
        return String::new();
    }
    match char::from_u32(val as u32) {
        Some(c) => c.to_string(),
        None => String::new(),
    }
}

/// Evaluate `str.is_digit(s)`: whether s is a single ASCII digit character.
///
/// SMT-LIB semantics: true iff |s| = 1 and the character is in '0'..'9'.
pub fn eval_str_is_digit(s: &str) -> bool {
    s.len() == 1 && s.chars().next().is_some_and(|c| c.is_ascii_digit())
}

/// Evaluate `str.to_lower(s)`: convert all characters to lowercase.
pub fn eval_str_to_lower(s: &str) -> String {
    s.to_lowercase()
}

/// Evaluate `str.to_upper(s)`: convert all characters to uppercase.
pub fn eval_str_to_upper(s: &str) -> String {
    s.to_uppercase()
}

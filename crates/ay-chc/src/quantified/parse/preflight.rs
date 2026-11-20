// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Allocation-free lexical admission before the frontend builds S-expressions.
//!
//! This initial ingress accepts ASCII only. It is not an SMT lexer: ordinary
//! runs are conservatively charged, and the frontend still checks actual token
//! syntax. Comments do not contribute tokens; quoted symbols can contain spaces
//! and parentheses. Quoted syntax names are refused because `SExpr::Symbol`
//! does not retain whether its spelling was quoted.

use crate::{ChcError, ChcResult};

pub(super) const MAX_INPUT_BYTES: usize = 8 * 1024 * 1024;
pub(super) const MAX_DEPTH: usize = 64;
pub(super) const MAX_TOKENS: usize = 65_536;
pub(super) const MAX_TOKEN_BYTES: usize = 16_384;

fn invalid(message: &str) -> ChcError {
    ChcError::Parse(format!("quantified source lexical admission: {message}"))
}

pub(super) fn check(input: &str) -> ChcResult<()> {
    if input.len() > MAX_INPUT_BYTES {
        return Err(invalid("input byte limit"));
    }
    let bytes = input.as_bytes();
    if bytes
        .iter()
        .copied()
        .any(|byte| !matches!(byte, b'\t' | b'\r' | b'\n' | b' '..=b'~'))
    {
        return Err(invalid("only printable ASCII and tab/CR/LF are supported"));
    }
    let mut cursor = 0;
    let mut depth = 0usize;
    let mut tokens = 0usize;
    while cursor < bytes.len() {
        let added = match bytes[cursor] {
            b' ' | b'\t' | b'\r' | b'\n' => {
                cursor += 1;
                0
            }
            b';' => {
                while cursor < bytes.len() && !matches!(bytes[cursor], b'\r' | b'\n') {
                    cursor += 1;
                }
                0
            }
            b'(' => {
                cursor += 1;
                depth += 1;
                if depth > MAX_DEPTH {
                    return Err(invalid("nesting depth limit"));
                }
                1
            }
            b')' => {
                cursor += 1;
                depth = depth
                    .checked_sub(1)
                    .ok_or_else(|| invalid("unmatched close parenthesis"))?;
                1
            }
            b'|' => {
                quoted(input, &mut cursor)?;
                1
            }
            b'"' | b'\\' => return Err(invalid("strings and backslashes are unsupported")),
            _ => ordinary(bytes, &mut cursor)?,
        };
        // Both operands are bounded by the fixed input/run caps, well below
        // usize::MAX even on 32-bit hosts. No frontend allocation has occurred.
        tokens += added;
        if tokens > MAX_TOKENS {
            return Err(invalid("token limit"));
        }
    }
    if depth != 0 {
        return Err(invalid("unclosed parenthesis"));
    }
    Ok(())
}

fn quoted(input: &str, cursor: &mut usize) -> ChcResult<()> {
    let bytes = input.as_bytes();
    let start = *cursor;
    *cursor += 1;
    while *cursor < bytes.len() {
        let byte = bytes[*cursor];
        *cursor += 1;
        if *cursor - start > MAX_TOKEN_BYTES {
            return Err(invalid("quoted token byte limit"));
        }
        if byte == b'\\' {
            return Err(invalid("quoted-symbol escapes are unsupported"));
        }
        if byte == b'|' {
            // check() authenticated ASCII, so these byte offsets are UTF-8
            // boundaries. Delimiters count towards the raw token-size limit.
            if quoted_syntax(&input[start + 1..*cursor - 1]) {
                return Err(invalid("quoted syntax or theory identifier is unsupported"));
            }
            return Ok(());
        }
    }
    Err(invalid("unclosed quoted symbol"))
}

fn ordinary(bytes: &[u8], cursor: &mut usize) -> ChcResult<usize> {
    let start = *cursor;
    let mut cost = 1usize;
    let mut hash = false;
    while *cursor < bytes.len() {
        let byte = bytes[*cursor];
        if matches!(
            byte,
            b' ' | b'\t' | b'\r' | b'\n' | b';' | b'(' | b')' | b'|' | b'"' | b'\\'
        ) {
            break;
        }
        // The frontend can split adjacent numerals/symbols (1abc) or keywords
        // (a:b). Counting a whitespace-delimited run as one would undercharge.
        // Extra boundaries inside legal symbols are deliberately conservative.
        if (*cursor > start && bytes[*cursor - 1].is_ascii_digit() && !byte.is_ascii_digit())
            || byte == b':'
        {
            cost += 1;
        }
        hash |= byte == b'#';
        *cursor += 1;
        if *cursor - start > MAX_TOKEN_BYTES {
            return Err(invalid("ordinary token byte limit"));
        }
    }
    // Bitvector token boundaries depend on radix digits, e.g. #x1z. Charging
    // each byte of such a run is an upper bound without reproducing the lexer.
    Ok(if hash { *cursor - start } else { cost })
}

fn quoted_syntax(name: &str) -> bool {
    crate::parser::is_builtin_term_symbol(name)
        || matches!(
            name,
            "!" | "xor"
                | "match"
                | "par"
                | "lambda"
                | "Bool"
                | "BitVec"
                | "Array"
                | "Int"
                | "Real"
                | "String"
                | "RegLan"
                | "Seq"
                | "FloatingPoint"
                | "RoundingMode"
                | "HORN"
                | "extract"
                | "repeat"
                | "zero_extend"
                | "sign_extend"
                | "rotate_left"
                | "rotate_right"
                | "int2bv"
                | "int_to_bv"
                | "set-logic"
                | "set-info"
                | "set-option"
                | "declare-var"
                | "declare-rel"
                | "declare-fun"
                | "declare-const"
                | "declare-sort"
                | "declare-datatype"
                | "declare-datatypes"
                | "define-fun"
                | "define-fun-rec"
                | "define-funs-rec"
                | "define-sort"
                | "assert"
                | "rule"
                | "query"
                | "check-sat"
                | "check-sat-assuming"
                | "push"
                | "pop"
                | "reset"
                | "reset-assertions"
                | "exit"
                | "get-model"
                | "get-value"
                | "get-proof"
                | "get-unsat-core"
                | "get-assertions"
                | "get-info"
                | "get-option"
                | "echo"
        )
        || name
            .as_bytes()
            .first()
            .copied()
            .is_some_and(|byte| byte.is_ascii_digit() || matches!(byte, b'#' | b':'))
        || name.strip_prefix("bv").is_some_and(|suffix| {
            !suffix.is_empty() && suffix.bytes().all(|byte| byte.is_ascii_digit())
        })
}

#[cfg(test)]
mod tests;

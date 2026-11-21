// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! CPLEX LP format tokenizer.
//!
//! Splits the input text into a stream of [`SpannedTok`]s. A line that holds
//! only a section keyword (`Subject To`, `s.t.`, `Bounds`, ...) becomes one
//! [`Tok::Header`]; the reading of every token is documented in `lp.rs`.
//! Numbers are kept as the exact rational their decimal text denotes
//! ([`crate::exact::decimal::parse_decimal`]).

use num_rational::BigRational;

use crate::error::LpError;
use crate::exact::decimal::parse_decimal;
use crate::model::Sense;

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum Tok {
    Word(String),
    Num(BigRational),
    Colon,
    Plus,
    Minus,
    Le,
    Ge,
    Eq,
    /// Header tokens emitted by the tokenizer after keyword folding.
    Header(Section),
    End,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Section {
    Objective(Sense),
    Subject,
    Bounds,
    General,
    Binary,
}

#[derive(Debug, Clone)]
pub(crate) struct SpannedTok {
    pub(crate) tok: Tok,
    pub(crate) line: usize,
}

fn refuse(line: usize, msg: impl Into<String>) -> LpError {
    LpError::Parse {
        line,
        msg: msg.into(),
    }
}

pub(crate) fn tokenize(input: &str) -> Result<Vec<SpannedTok>, LpError> {
    let mut out = Vec::new();
    for (idx, raw) in input.lines().enumerate() {
        let line_no = idx + 1;
        let stripped = strip_comment(raw, line_no)?;
        if let Some(tok) = match_header(stripped.trim(), line_no)? {
            out.push(SpannedTok { tok, line: line_no });
            continue;
        }
        tokenize_line(stripped, line_no, &mut out)?;
    }
    Ok(out)
}

fn tokenize_line(line: &str, line_no: usize, out: &mut Vec<SpannedTok>) -> Result<(), LpError> {
    let bytes = line.as_bytes();
    let mut i = 0;
    let mut push = |tok| out.push(SpannedTok { tok, line: line_no });
    while i < bytes.len() {
        let c = bytes[i];
        let next = bytes.get(i + 1).copied();
        if c.is_ascii_whitespace() {
            i += 1;
            continue;
        }
        let (tok, used) = match (c, next) {
            (b'-', Some(b'>')) => {
                return Err(refuse(
                    line_no,
                    "indicator constraints ('->') are not supported",
                ))
            }
            (b'[' | b']' | b'^', _) => {
                return Err(refuse(line_no, "quadratic terms are not supported"))
            }
            (b'+', _) => (Tok::Plus, 1),
            (b'-', _) => (Tok::Minus, 1),
            (b':', _) => (Tok::Colon, 1),
            (b'=', Some(b'<')) | (b'<', Some(b'=')) => (Tok::Le, 2),
            (b'=', Some(b'>')) | (b'>', Some(b'=')) => (Tok::Ge, 2),
            (b'=', Some(b'=')) => (Tok::Eq, 2),
            (b'=', _) => (Tok::Eq, 1),
            (b'<', _) => (Tok::Le, 1),
            (b'>', _) => (Tok::Ge, 1),
            _ if c.is_ascii_digit() || c == b'.' => {
                let (value, used) = read_number(&bytes[i..], line_no)?;
                (Tok::Num(value), used)
            }
            _ if is_name_start(c) => {
                let mut end = i;
                while end < bytes.len() && is_name_cont(bytes[end]) {
                    end += 1;
                }
                let word = std::str::from_utf8(&bytes[i..end]).unwrap_or("");
                (Tok::Word(word.to_string()), end - i)
            }
            _ => {
                return Err(refuse(
                    line_no,
                    format!("unexpected character '{}'", char::from(c)),
                ))
            }
        };
        push(tok);
        i += used;
    }
    Ok(())
}

/// `digits [. digits] [e [+-] digits]`, read exactly; the text must be a
/// number of [`parse_decimal`]'s grammar and in its range.
fn read_number(bytes: &[u8], line: usize) -> Result<(BigRational, usize), LpError> {
    let mut j = 0;
    while j < bytes.len() && (bytes[j].is_ascii_digit() || bytes[j] == b'.') {
        j += 1;
    }
    if j < bytes.len() && (bytes[j] == b'e' || bytes[j] == b'E') {
        j += 1;
        if j < bytes.len() && (bytes[j] == b'+' || bytes[j] == b'-') {
            j += 1;
        }
        while j < bytes.len() && bytes[j].is_ascii_digit() {
            j += 1;
        }
    }
    let raw = std::str::from_utf8(&bytes[..j]).unwrap_or("");
    parse_decimal(raw)
        .map(|value| (value, j))
        .ok_or_else(|| LpError::InvalidNumber {
            line,
            raw: raw.to_string(),
        })
}

fn is_name_start(c: u8) -> bool {
    c.is_ascii_alphabetic() || matches!(c, b'_' | b'.' | b'!' | b'#' | b'$' | b'%' | b'&' | b'?')
}

fn is_name_cont(c: u8) -> bool {
    // `-` is deliberately excluded so that `x-1` tokenizes as `x`, `-`, `1`.
    is_name_start(c) || c.is_ascii_digit()
}

/// The line before its comment: `\` starts a comment that runs to the end of
/// the line. A `\*` comment must close (`*\`) on its own line: a block
/// comment spanning lines would be read as content by a line reader.
fn strip_comment(line: &str, line_no: usize) -> Result<&str, LpError> {
    let Some(pos) = line.find('\\') else {
        return Ok(line);
    };
    let comment = &line[pos..];
    if comment.starts_with("\\*") && !comment[2..].contains("*\\") {
        return Err(refuse(
            line_no,
            "a '\\*' comment that does not close on its line is not supported",
        ));
    }
    Ok(&line[..pos])
}

/// The header token of a line holding only a section keyword, an error for a
/// section ay does not read, `None` for any other line.
fn match_header(line: &str, line_no: usize) -> Result<Option<Tok>, LpError> {
    let canonical = line
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ")
        .to_ascii_lowercase();
    let tok = match canonical.as_str() {
        "minimize" | "minimise" | "minimum" | "min" => Tok::Header(Section::Objective(Sense::Min)),
        "maximize" | "maximise" | "maximum" | "max" => Tok::Header(Section::Objective(Sense::Max)),
        "subject to" | "such that" | "st" | "s.t." | "st." => Tok::Header(Section::Subject),
        "bounds" | "bound" => Tok::Header(Section::Bounds),
        "general" | "generals" | "gen" | "integer" | "integers" => Tok::Header(Section::General),
        "binary" | "binaries" | "bin" => Tok::Header(Section::Binary),
        "end" => Tok::End,
        "semi-continuous"
        | "semi-continuous variables"
        | "semi"
        | "semis"
        | "semicontinuous"
        | "sos"
        | "sos1"
        | "sos2"
        | "lazy constraints"
        | "user cuts"
        | "pwlobj"
        | "gin"
        | "general constraints"
        | "genconstrs"
        | "gencons"
        | "scenarios"
        | "multi-objectives"
        | "semi-integer"
        | "semi-integers"
        | "sint" => {
            return Err(refuse(
                line_no,
                format!("section '{}' is not supported", line.trim()),
            ))
        }
        _ => return Ok(None),
    };
    Ok(Some(tok))
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! CPLEX LP format tokenizer.
//!
//! Splits the input text into a stream of [`SpannedTok`]s. Multi-word headers
//! (`Subject To`, `s.t.`, `Such That`) are folded into single [`Tok::Header`]
//! entries so the parser in `lp.rs` can dispatch on them directly.

use crate::error::LpError;
use crate::model::Sense;

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum Tok {
    Word(String),
    Num(f64),
    Colon,
    Plus,
    Minus,
    Le,
    Ge,
    Eq,
    LBracket,
    RBracket,
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
    Integer,
    Binary,
}

pub(crate) struct SpannedTok {
    pub(crate) tok: Tok,
    pub(crate) line: usize,
}

impl Clone for SpannedTok {
    fn clone(&self) -> Self {
        Self {
            tok: self.tok.clone(),
            line: self.line,
        }
    }
}

pub(crate) fn tokenize(input: &str) -> Result<Vec<SpannedTok>, LpError> {
    let mut out = Vec::new();
    for (idx, raw) in input.lines().enumerate() {
        let line_no = idx + 1;
        let stripped = strip_comment(raw);

        // Detect multi-word section headers first (case-insensitive).
        let trimmed = stripped.trim();
        if let Some(section) = match_header(trimmed) {
            let tok = match section {
                HeaderKind::Min => Tok::Header(Section::Objective(Sense::Min)),
                HeaderKind::Max => Tok::Header(Section::Objective(Sense::Max)),
                HeaderKind::Subject => Tok::Header(Section::Subject),
                HeaderKind::Bounds => Tok::Header(Section::Bounds),
                HeaderKind::General => Tok::Header(Section::General),
                HeaderKind::Integer => Tok::Header(Section::Integer),
                HeaderKind::Binary => Tok::Header(Section::Binary),
                HeaderKind::End => Tok::End,
            };
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
    while i < bytes.len() {
        let c = bytes[i];
        if c.is_ascii_whitespace() {
            i += 1;
            continue;
        }
        match c {
            b'+' => {
                out.push(SpannedTok {
                    tok: Tok::Plus,
                    line: line_no,
                });
                i += 1;
            }
            b'-' => {
                out.push(SpannedTok {
                    tok: Tok::Minus,
                    line: line_no,
                });
                i += 1;
            }
            b':' => {
                out.push(SpannedTok {
                    tok: Tok::Colon,
                    line: line_no,
                });
                i += 1;
            }
            b'[' => {
                out.push(SpannedTok {
                    tok: Tok::LBracket,
                    line: line_no,
                });
                i += 1;
            }
            b']' => {
                out.push(SpannedTok {
                    tok: Tok::RBracket,
                    line: line_no,
                });
                i += 1;
            }
            b'=' => {
                // `=<`, `=>` (old-style) or bare `=`.
                if i + 1 < bytes.len() && (bytes[i + 1] == b'<' || bytes[i + 1] == b'=') {
                    let op = if bytes[i + 1] == b'<' {
                        Tok::Le
                    } else {
                        Tok::Eq
                    };
                    out.push(SpannedTok {
                        tok: op,
                        line: line_no,
                    });
                    i += 2;
                } else if i + 1 < bytes.len() && bytes[i + 1] == b'>' {
                    out.push(SpannedTok {
                        tok: Tok::Ge,
                        line: line_no,
                    });
                    i += 2;
                } else {
                    out.push(SpannedTok {
                        tok: Tok::Eq,
                        line: line_no,
                    });
                    i += 1;
                }
            }
            b'<' => {
                let step = usize::from(i + 1 < bytes.len() && bytes[i + 1] == b'=');
                out.push(SpannedTok {
                    tok: Tok::Le,
                    line: line_no,
                });
                i += 1 + step;
            }
            b'>' => {
                let step = usize::from(i + 1 < bytes.len() && bytes[i + 1] == b'=');
                out.push(SpannedTok {
                    tok: Tok::Ge,
                    line: line_no,
                });
                i += 1 + step;
            }
            _ if c.is_ascii_digit() || c == b'.' => {
                let (n, used) = read_number(&bytes[i..], line_no)?;
                out.push(SpannedTok {
                    tok: Tok::Num(n),
                    line: line_no,
                });
                i += used;
            }
            _ if is_name_start(c) => {
                let start = i;
                while i < bytes.len() && is_name_cont(bytes[i]) {
                    i += 1;
                }
                let word = std::str::from_utf8(&bytes[start..i]).unwrap_or("");
                // Word-form comparators keep `free` and `inf` as identifiers;
                // the parser dispatches on them by context.
                out.push(SpannedTok {
                    tok: Tok::Word(word.to_string()),
                    line: line_no,
                });
            }
            _ => {
                return Err(LpError::Parse {
                    line: line_no,
                    msg: format!("unexpected character '{}'", c as char),
                });
            }
        }
    }
    Ok(())
}

fn read_number(bytes: &[u8], line: usize) -> Result<(f64, usize), LpError> {
    let mut j = 0;
    // Optional leading sign is already consumed by the +/- lexer path, but we
    // accept it here too to make the parser forgiving for expressions like
    // `1e-3`.
    if j < bytes.len() && (bytes[j] == b'+' || bytes[j] == b'-') {
        j += 1;
    }
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
    let parsed = raw.parse::<f64>().map_err(|_| LpError::InvalidNumber {
        line,
        raw: raw.to_string(),
    })?;
    if parsed.is_finite() {
        Ok((parsed, j))
    } else {
        Err(LpError::InvalidNumber {
            line,
            raw: raw.to_string(),
        })
    }
}

fn is_name_start(c: u8) -> bool {
    c.is_ascii_alphabetic() || matches!(c, b'_' | b'.' | b'!' | b'#' | b'$' | b'%' | b'&' | b'?')
}

fn is_name_cont(c: u8) -> bool {
    // `-` is deliberately excluded so that `x-1` tokenizes as `x`, `-`, `1`.
    is_name_start(c) || c.is_ascii_digit()
}

fn strip_comment(line: &str) -> &str {
    if let Some(pos) = line.find('\\') {
        &line[..pos]
    } else {
        line
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum HeaderKind {
    Min,
    Max,
    Subject,
    Bounds,
    General,
    Integer,
    Binary,
    End,
}

fn match_header(line: &str) -> Option<HeaderKind> {
    // Some headers are multi-word. Normalize whitespace and compare against a
    // small table of canonical forms.
    let canonical: String = line.split_whitespace().collect::<Vec<_>>().join(" ");
    let lower = canonical.to_ascii_lowercase();
    match lower.as_str() {
        "minimize" | "minimise" | "min" => Some(HeaderKind::Min),
        "maximize" | "maximise" | "max" => Some(HeaderKind::Max),
        "subject to" | "such that" | "st" | "s.t." | "st." => Some(HeaderKind::Subject),
        "bounds" | "bound" => Some(HeaderKind::Bounds),
        "general" | "generals" | "gin" => Some(HeaderKind::General),
        "integer" | "integers" => Some(HeaderKind::Integer),
        "binary" | "binaries" | "bin" => Some(HeaderKind::Binary),
        "end" => Some(HeaderKind::End),
        _ => None,
    }
}

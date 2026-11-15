// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The SMT-LIB lexing every pinned-Carcara guard shares: top-level commands,
//! atoms with their depth, symbol names and a flat parenthesis structure, with
//! `;` comments, `|quoted symbols|` and `"strings"` read the way SMT-LIB reads
//! them and every atom ended where pinned Carcara's lexer ends that token
//! ([`atom_end`]); and the names Carcara expands that carry a flagged operator.

use std::collections::BTreeSet;

/// A symbol's name: SMT-LIB reads `|x|` and `x` as one symbol, and so does
/// pinned Carcara (measured: `(|bvsge| #xf #xe)` is its `bvsge`, and
/// `:rule |evaluate|` its `evaluate`). Keywords and strings are unchanged.
pub(super) fn symbol_name(atom: &str) -> &str {
    atom.strip_prefix('|')
        .and_then(|inner| inner.strip_suffix('|'))
        .unwrap_or(atom)
}

/// The top-level commands of an Alethe document, in order.
///
/// `;` comments, `|quoted symbols|` and `"strings"` are skipped the way
/// SMT-LIB lexes them, so a comment or a quoted symbol that happens to spell
/// `:rule evaluate` is never read as part of a command, and a command printed
/// over several lines is read whole.
pub(super) fn alethe_commands(document: &str) -> Vec<&str> {
    let bytes = document.as_bytes();
    let mut commands = Vec::new();
    let (mut depth, mut start, mut index) = (0usize, 0usize, 0usize);
    while index < bytes.len() {
        match bytes[index] {
            b';' => {
                while index < bytes.len() && bytes[index] != b'\n' {
                    index += 1;
                }
            }
            b'|' | b'"' => index = closing_delimiter(bytes, index),
            b'(' => {
                if depth == 0 {
                    start = index;
                }
                depth += 1;
            }
            b')' if depth > 0 => {
                depth -= 1;
                if depth == 0 {
                    commands.push(&document[start..=index]);
                }
            }
            _ => {}
        }
        index += 1;
    }
    commands
}

/// Index of the delimiter closing the quoted symbol or string that opens at
/// `open` (a string's `""` is an escaped quote), or the last index.
pub(super) fn closing_delimiter(bytes: &[u8], open: usize) -> usize {
    let delimiter = bytes[open];
    let mut index = open + 1;
    while index < bytes.len() {
        if bytes[index] == delimiter {
            if delimiter == b'"' && bytes.get(index + 1) == Some(&b'"') {
                index += 2;
                continue;
            }
            return index;
        }
        index += 1;
    }
    bytes.len().saturating_sub(1)
}

/// Whether pinned Carcara skips `byte` between tokens. Its lexer
/// (`parser/lexer.rs`, `Lexer::consume_whitespace`) skips every
/// `char::is_whitespace` character, so the vertical tab and non-ASCII spaces
/// such as U+00A0 separate tokens too, and it rejects any other non-ASCII
/// character outside a quoted symbol or string: on every document it accepts,
/// a non-ASCII byte there belongs to a space.
fn separates_atoms(byte: u8) -> bool {
    byte.is_ascii_whitespace() || byte == 0x0b || !byte.is_ascii()
}

/// Pinned Carcara's `utils::is_symbol_character`.
fn continues_symbol(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || b"+-/*=%?!.$_~&^<>@'".contains(&byte)
}

/// The index just past the atom opening at `start` (an ASCII byte that is no
/// parenthesis, separator, `;`, `|` or `"`), ended where pinned Carcara's
/// `Lexer::next_token` ends that token: a simple symbol or keyword at its
/// first non-symbol character, a numeral or decimal after its digits, a
/// bit-vector literal after the digits of its base. So `bvmul#x02` is read as
/// `bvmul` and `#x02`, and `2m` as `2` and `m`, as Carcara reads them: ending
/// an atom only at a space or a parenthesis would hide the operator or name it
/// carries from every scan. A byte Carcara cannot start a token with (it
/// rejects the document) is an atom of its own. Never splits more finely than
/// Carcara on a document it lexes, so two spellings lexed alike are one term
/// to it.
fn atom_end(bytes: &[u8], start: usize) -> usize {
    let run = |from: usize, accepts: fn(u8) -> bool| {
        let tail = bytes.get(from..).unwrap_or_default();
        from + tail.iter().take_while(|&&byte| accepts(byte)).count()
    };
    let number = |from: usize| {
        let integer = run(from, |byte| byte.is_ascii_digit());
        match bytes.get(integer) {
            Some(b'.' | b'/') => run(integer + 1, |byte| byte.is_ascii_digit()),
            _ => integer,
        }
    };
    let end = match (bytes[start], bytes.get(start + 1)) {
        (b'#', Some(b'b')) => run(start + 2, |byte| matches!(byte, b'0' | b'1')),
        (b'#', Some(b'x')) => run(start + 2, |byte| byte.is_ascii_hexdigit()),
        (b'-', Some(digit)) if digit.is_ascii_digit() => number(start + 1),
        (digit, _) if digit.is_ascii_digit() => number(start),
        (b':', _) => run(start + 1, continues_symbol),
        (symbol, _) if continues_symbol(symbol) => run(start + 1, continues_symbol),
        _ => start + 1,
    };
    end.max(start + 1)
}

/// Every atom of one command (symbol, keyword, literal, quoted symbol or
/// string, the latter two whole), with its parenthesis depth: the command's
/// own fields are at depth 1.
pub(super) fn command_atoms(command: &str) -> Vec<(usize, &str)> {
    let bytes = command.as_bytes();
    let mut atoms = Vec::new();
    let (mut depth, mut index) = (0usize, 0usize);
    while index < bytes.len() {
        match bytes[index] {
            b'(' => depth += 1,
            b')' => depth = depth.saturating_sub(1),
            b';' => {
                while index < bytes.len() && bytes[index] != b'\n' {
                    index += 1;
                }
            }
            byte if separates_atoms(byte) => {}
            b'|' | b'"' => {
                let close = closing_delimiter(bytes, index);
                atoms.push((depth, &command[index..=close]));
                index = close;
            }
            _ => {
                let end = atom_end(bytes, index);
                atoms.push((depth, &command[index..end]));
                index = end - 1;
            }
        }
        index += 1;
    }
    atoms
}

/// The rule of a `(step ..)` command: the field right after its `:rule`.
pub(super) fn step_rule_of<'a>(atoms: &[(usize, &'a str)]) -> Option<&'a str> {
    if atoms.first() != Some(&(1, "step")) {
        return None;
    }
    let keyword = atoms.iter().position(|&atom| atom == (1, ":rule"))?;
    match atoms.get(keyword + 1) {
        Some(&(1, rule)) => Some(symbol_name(rule)),
        _ => None,
    }
}

/// Whether one command's atoms apply one of `operators` or a name already in
/// `names`. If they do, the names the command introduces (a `define-fun`'s
/// name, every `:named` label) are recorded in `names` too: pinned Carcara
/// expands both before any rule runs, and the whole command is attributed to
/// each, which can only flag more.
pub(super) fn record_names_applying<'a>(
    atoms: &[(usize, &'a str)],
    operators: &[&str],
    names: &mut BTreeSet<&'a str>,
) -> bool {
    let applies = atoms.iter().any(|&(_, atom)| {
        let symbol = symbol_name(atom);
        operators.contains(&symbol) || names.contains(symbol)
    });
    if applies {
        if let [(1, "define-fun"), (1, name), ..] = atoms {
            names.insert(symbol_name(name));
        }
        let labels = atoms.windows(2).filter(|pair| pair[0].1 == ":named");
        names.extend(labels.map(|pair| symbol_name(pair[1].1)));
    }
    applies
}

/// One lexed token of a document (a pinned-Carcara guard's input).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum SexpToken<'a> {
    Open,
    Close,
    Atom(&'a str),
}

/// A document's tokens, lexed the way `command_atoms` lexes it (comments
/// skipped, quoted symbols and strings whole, every other atom ended where
/// pinned Carcara ends it), and each token's last index:
/// the matching `Close` of an `Open` (the last token, when unbalanced), the
/// token itself otherwise. Flat, so neither building nor dropping it recurses
/// on a deeply nested term.
pub(super) struct LexedDocument<'a> {
    pub(super) tokens: Vec<SexpToken<'a>>,
    pub(super) last: Vec<usize>,
}

impl<'a> LexedDocument<'a> {
    pub(super) fn new(document: &'a str) -> Self {
        let bytes = document.as_bytes();
        let mut tokens = Vec::new();
        let mut index = 0usize;
        while index < bytes.len() {
            match bytes[index] {
                b';' => {
                    while index < bytes.len() && bytes[index] != b'\n' {
                        index += 1;
                    }
                }
                b'(' => tokens.push(SexpToken::Open),
                b')' => tokens.push(SexpToken::Close),
                byte if separates_atoms(byte) => {}
                b'|' | b'"' => {
                    let close = closing_delimiter(bytes, index);
                    tokens.push(SexpToken::Atom(&document[index..=close]));
                    index = close;
                }
                _ => {
                    let end = atom_end(bytes, index);
                    tokens.push(SexpToken::Atom(&document[index..end]));
                    index = end - 1;
                }
            }
            index += 1;
        }
        let mut last: Vec<usize> = (0..tokens.len()).collect();
        let mut open = Vec::new();
        for (position, token) in tokens.iter().enumerate() {
            match token {
                SexpToken::Open => open.push(position),
                SexpToken::Close => {
                    if let Some(start) = open.pop() {
                        last[start] = position;
                    }
                }
                SexpToken::Atom(_) => {}
            }
        }
        for start in open {
            last[start] = tokens.len() - 1;
        }
        Self { tokens, last }
    }

    pub(super) fn is_open(&self, position: usize) -> bool {
        self.tokens.get(position) == Some(&SexpToken::Open)
    }

    /// The symbol at `position`, when it is an atom.
    pub(super) fn symbol(&self, position: usize) -> Option<&'a str> {
        match self.tokens.get(position) {
            Some(SexpToken::Atom(atom)) => Some(symbol_name(atom)),
            _ => None,
        }
    }

    /// The first atom of the list opening at `open`.
    pub(super) fn head(&self, open: usize) -> Option<&'a str> {
        if self.is_open(open) {
            self.symbol(open + 1)
        } else {
            None
        }
    }

    /// The first index of each immediate child of the list opening at `open`.
    pub(super) fn children(&self, open: usize) -> Vec<usize> {
        let mut children = Vec::new();
        if !self.is_open(open) {
            return children;
        }
        let mut position = open + 1;
        while position < self.last[open] {
            children.push(position);
            position = self.last[position] + 1;
        }
        children
    }
}

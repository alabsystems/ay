// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The printed document as the consumer reads it: s-expressions as AY's own
//! SMT-LIB lexer reads them (see [`read_sexps`]), the proof's
//! nullary `define-fun` macros (Carcara's parser inlines them before any rule
//! runs) and, on the consumer's parsing boundary (Clean 7330fa6c
//! `carcara_verify`), every bit-vector literal in one spelling
//! (`bv_literals::normalize` plus Carcara's lexer: `#b`, `#x` and `(_ bvN w)`
//! are one constant) and `((_ zero_extend k) x)` rewritten to
//! `(concat #b0…0 x)`, or `x` when `k` is 0 (`zero_extend::normalize`).

use ay_frontend::SExpr;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum Sexp {
    Atom(String),
    List(Vec<Sexp>),
}

impl Sexp {
    pub(super) fn head(&self) -> Option<&str> {
        match self {
            Sexp::List(items) => match items.first() {
                Some(Sexp::Atom(head)) => Some(head),
                _ => None,
            },
            Sexp::Atom(_) => None,
        }
    }

    pub(super) fn args(&self) -> &[Sexp] {
        match self {
            Sexp::List(items) if !items.is_empty() => &items[1..],
            _ => &[],
        }
    }

    pub(super) fn is_atom(&self, text: &str) -> bool {
        matches!(self, Sexp::Atom(atom) if atom == text)
    }
}

/// The commands of `text` as AY's own SMT-LIB front end lexes them
/// (`ay_frontend::sexp`): string literals, quoted symbols and comments are
/// tokens, never structure. A symbol is spelled bare only when its bare text
/// lexes back as that symbol; otherwise it keeps its bars, so the user symbol
/// `|#b1|` is never the literal `#b1`, nor `|false|` the constant `false`.
pub(super) fn read_sexps(text: &str) -> Result<Vec<Sexp>, String> {
    let parsed = ay_frontend::sexp::parse_sexps(text).map_err(|error| error.to_string())?;
    Ok(parsed.iter().map(from_frontend).collect())
}

pub(super) fn from_frontend(sexp: &SExpr) -> Sexp {
    match sexp {
        SExpr::Symbol(name) => Sexp::Atom(symbol(name)),
        SExpr::Keyword(text)
        | SExpr::Numeral(text)
        | SExpr::Decimal(text)
        | SExpr::Hexadecimal(text)
        | SExpr::Binary(text) => Sexp::Atom(text.clone()),
        SExpr::String(contents) => Sexp::Atom(ay_core::string_literal(contents)),
        SExpr::True => Sexp::Atom("true".to_string()),
        SExpr::False => Sexp::Atom("false".to_string()),
        SExpr::List(items) => Sexp::List(items.iter().map(from_frontend).collect()),
        other => Sexp::Atom(unread(other)),
    }
}

/// An atom no lexed token is spelled as (it starts with a NUL), for a
/// front-end form this reader does not know: it matches nothing.
pub(super) fn unread(form: &impl std::fmt::Debug) -> String {
    format!("\u{0}unread {form:?}")
}

/// The spelling of the symbol `name`: bare when the bare text lexes back as
/// the same single symbol, else quoted.
pub(super) fn symbol(name: &str) -> String {
    const EXTRA: &[char] = &[
        '+', '-', '/', '*', '=', '%', '?', '!', '.', '$', '_', '~', '&', '^', '<', '>', '@',
    ];
    let bare = !name.is_empty()
        && !name.starts_with(|c: char| c.is_ascii_digit())
        && name
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || EXTRA.contains(&c))
        && !matches!(name, "true" | "false");
    if bare {
        name.to_string()
    } else {
        let mut quoted = String::from("|");
        for character in name.chars() {
            if matches!(character, '|' | '\\') {
                quoted.push('\\');
            }
            quoted.push(character);
        }
        quoted.push('|');
        quoted
    }
}

pub(super) struct Step {
    pub(super) id: String,
    pub(super) clause: Vec<Sexp>,
    pub(super) rule: String,
    pub(super) premises: Vec<String>,
    pub(super) args: Vec<Sexp>,
    pub(super) discharge: Vec<String>,
}

pub(super) enum Command {
    Assume(String, Sexp),
    Step(Step),
    /// `(anchor :step <id> …)`: a subproof that ends at step `<id>`, and
    /// whether it binds a context (`:args`).
    Anchor(String, bool),
}

pub(super) fn keyword<'a>(items: &'a [Sexp], key: &str) -> Option<&'a Sexp> {
    let at = items.iter().position(|item| item.is_atom(key))?;
    items.get(at + 1)
}

pub(super) fn read_step(command: &Sexp) -> Step {
    let args = command.args();
    let Some(Sexp::Atom(id)) = args.first() else {
        panic!("step without an id: {command:?}")
    };
    let clause = match args.get(1) {
        Some(clause @ Sexp::List(_)) if clause.head() == Some("cl") => clause.args().to_vec(),
        other => panic!("step {id} without a clause: {other:?}"),
    };
    let rule = match keyword(args, ":rule") {
        Some(Sexp::Atom(rule)) => rule.clone(),
        _ => panic!("step {id} without a rule"),
    };
    let list = |key| match keyword(args, key) {
        Some(Sexp::List(items)) => items.clone(),
        _ => Vec::new(),
    };
    let ids = |key| {
        list(key)
            .into_iter()
            .map(|premise| match premise {
                Sexp::Atom(id) => id,
                Sexp::List(_) => format!("{premise:?}"),
            })
            .collect()
    };
    Step {
        id: id.clone(),
        clause,
        rule,
        premises: ids(":premises"),
        args: list(":args"),
        discharge: ids(":discharge"),
    }
}

/// `#x…` in binary: Carcara's lexer reads both as one bit-vector constant.
pub(super) fn hex_as_binary(atom: &str) -> Option<String> {
    let digits = atom.strip_prefix("#x")?;
    let mut binary = String::from("#b");
    for digit in digits.chars() {
        binary.push_str(&format!("{:04b}", digit.to_digit(16)?));
    }
    Some(binary)
}

/// `(_ bvN w)` as `#b` with exactly `w` digits, N reduced modulo 2^w
/// (`bv_literals::normalize`).
pub(super) fn decimal_literal(items: &[Sexp]) -> Option<String> {
    let [under, Sexp::Atom(value), Sexp::Atom(width)] = items else {
        return None;
    };
    let value = value.strip_prefix("bv")?;
    if !under.is_atom("_") || value.is_empty() || !value.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    let width: usize = width.parse().ok().filter(|&width| width > 0)?;
    // Long division by two on the decimal digits, least significant bit first.
    let mut digits: Vec<u8> = value.bytes().map(|b| b - b'0').collect();
    let mut bits = Vec::with_capacity(width);
    while bits.len() < width {
        let mut remainder = 0;
        for digit in &mut digits {
            let current = remainder * 10 + *digit;
            *digit = current / 2;
            remainder = current % 2;
        }
        bits.push(if remainder == 1 { '1' } else { '0' });
    }
    Some(format!("#b{}", bits.iter().rev().collect::<String>()))
}

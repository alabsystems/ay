// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The ascribed spelling of a datatype constructor, `(as nil L1)`
//! (#overloaded-nil-surface), and readings of printed model text that take it
//! back.
//!
//! [`ascribed_constructor_spelling`] gives the ascription and
//! [`bare_constructor_spelling`] takes it back to the constructor's
//! [`symbol_token`]; both refuse what [`ascription_may_name_constructor`]
//! refuses, for example `(as seq.empty (Seq Int))`. [`smtlib_term_len`]
//! measures one term of printed text, [`smtlib_application_parts`] splits
//! one into its head and arguments, and [`model_constant_definition`] reads
//! one constant definition of a model.

use std::borrow::Cow;

use crate::symbol_token;

/// Heads [`ascription_may_name_constructor`] refuses under any sort: theory
/// constants, such as `seq.empty` in `(as seq.empty (Seq Int))`. `const` is
/// not listed: a script may name a constructor `const`.
pub const ASCRIPTION_THEORY_VALUE_HEADS: &[&str] = &[
    "seq.empty",
    "set.empty",
    "multiset.empty",
    "map.empty",
    "re.none",
    "re.all",
    "re.allchar",
];

/// Sort constructors `H` under which [`ascription_may_name_constructor`]
/// refuses `(as head (H ...))`: `_` (an indexed sort, such as the
/// finite-field literal `(as ff3 (_ FiniteField 7))`) and theory sort
/// constructors such as `Seq`. A script may declare a parametric datatype
/// named, for example, `Bag` or `Tuple`, so those are not listed.
pub const ASCRIPTION_THEORY_SORT_HEADS: &[&str] =
    &["_", "Array", "Seq", "Set", "FiniteSet", "Multiset", "Map"];

/// Whether `(as head S)` may be a constructor ascription, decided by syntax
/// alone.
///
/// `head` is the name, unquoted (the empty name of the constructor `||` is
/// admitted). `compound_sort_head` is the first symbol of `S` when `S` is a
/// list (`List` of `(List Int)`), and `None` when `S` is a plain symbol. It
/// is false exactly for:
///
/// - a head starting with `@` (an abstract element such as `(as @S!0 S)`, or
///   a constructor a script named `|@a|`);
/// - a head in [`ASCRIPTION_THEORY_VALUE_HEADS`];
/// - any head under a sort constructor in [`ASCRIPTION_THEORY_SORT_HEADS`].
pub fn ascription_may_name_constructor(head: &str, compound_sort_head: Option<&str>) -> bool {
    !head.starts_with('@')
        && !ASCRIPTION_THEORY_VALUE_HEADS.contains(&head)
        && compound_sort_head.is_none_or(|sort| !ASCRIPTION_THEORY_SORT_HEADS.contains(&sort))
}

/// `(as c sort)`, `c` the [`symbol_token`] of `constructor`, or `None`
/// exactly when `sort_len` does not span all of the trimmed `printed_sort`,
/// when [`ascription_may_name_constructor`] refuses it, or when
/// [`bare_constructor_spelling`] would not read the spelling back as `c`.
///
/// `constructor` is the constructor's name, unquoted. `printed_sort` is a
/// printed sort (`L1`, `|L#1|`, `(List Int)`).
pub fn ascribed_constructor_spelling(constructor: &str, printed_sort: &str) -> Option<String> {
    let sort = printed_sort.trim();
    let (len, compound_sort_head) = sort_len(sort)?;
    if len != sort.len()
        || !ascription_may_name_constructor(constructor, compound_sort_head.as_deref())
    {
        return None;
    }
    let token = symbol_token(constructor);
    let ascribed = format!("(as {token} {sort})");
    (bare_constructor_spelling(&ascribed) == token).then_some(ascribed)
}

/// `text` with each constructor ascription `(as c S)` replaced by the token
/// `c` as written (`(as |pop| L1)` gives `|pop|`, `(as || L1)` gives `||`).
///
/// An ascription here is `(`, `as`, `c`, `S` and `)`, with whitespace after
/// `as` and after `c` (and optionally after `(` and `S`): `c` is a `|quoted|`
/// symbol or a run of characters up to whitespace, a parenthesis, a bar or a
/// double quote, `S` is a symbol or a balanced list headed by one that holds
/// no string literal, and [`ascription_may_name_constructor`] admits the name
/// `c` spells under `S`. So `(as a|b L1)` stays as written, and the
/// application `(as nil e1)` of a constructor named `as` is replaced.
///
/// An ascription after `(` and only ASCII whitespace (the head of an
/// application, as in `((as const A) 0)`) is not replaced; the scan goes on
/// inside it. A token that starts with `|` or `"` runs to its closing quote,
/// or to the end of the text if there is none, and nothing in it is
/// replaced; any other token runs to the next
/// ASCII whitespace or parenthesis, so a bar or a double quote inside it
/// (`a|b`) opens no quote. Text without the substring `(as` is returned as
/// it is.
pub fn bare_constructor_spelling(text: &str) -> Cow<'_, str> {
    if !text.contains("(as") {
        return Cow::Borrowed(text);
    }
    let mut out = String::new();
    let mut copied = 0;
    let mut at = 0;
    // Whether the next term is the head of an application.
    let mut at_head = false;
    while at < text.len() {
        let rest = &text[at..];
        let first = rest.as_bytes()[0];
        let step = match first {
            b'"' => string_literal_len(rest),
            b'|' => symbol_len(rest).unwrap_or(rest.len()),
            b'(' => match ascription(rest).filter(|_| !at_head) {
                Some((len, constructor)) => {
                    out.push_str(&text[copied..at]);
                    out.push_str(constructor);
                    copied = at + len;
                    len
                }
                None => 1,
            },
            b')' => 1,
            _ if first.is_ascii_whitespace() => 1,
            // Any other atom, up to the next whitespace or parenthesis.
            _ => rest
                .find(|ch: char| ch.is_ascii_whitespace() || matches!(ch, '(' | ')'))
                .unwrap_or(rest.len()),
        };
        if !first.is_ascii_whitespace() {
            at_head = first == b'(' && step == 1;
        }
        at += step;
    }
    if copied == 0 {
        return Cow::Borrowed(text);
    }
    out.push_str(&text[copied..]);
    Cow::Owned(out)
}

/// The byte length of the ascription `text` starts with and its token `c`,
/// when it has the shape and passes the test [`bare_constructor_spelling`]
/// states.
fn ascription(text: &str) -> Option<(usize, &str)> {
    let after_as = text.strip_prefix("(")?.trim_start().strip_prefix("as")?;
    let rest = after_as.trim_start();
    if rest.len() == after_as.len() {
        return None;
    }
    let constructor = &rest[..symbol_len(rest)?];
    let after_constructor = &rest[constructor.len()..];
    let sort = after_constructor.trim_start();
    if sort.len() == after_constructor.len() {
        return None;
    }
    let (sort_len, compound_sort_head) = sort_len(sort)?;
    let close = sort[sort_len..].trim_start().strip_prefix(')')?;
    ascription_may_name_constructor(&unquoted(constructor), compound_sort_head.as_deref())
        .then_some((text.len() - close.len(), constructor))
}

/// Byte length of the sort-shaped text `text` starts with: a symbol, or a
/// balanced list that starts with a symbol and holds no string literal; with
/// the list's first symbol, unquoted (`List` of `(List Int)`).
fn sort_len(text: &str) -> Option<(usize, Option<String>)> {
    let Some(inner) = text.strip_prefix('(') else {
        return Some((symbol_len(text)?, None));
    };
    let inner = inner.trim_start();
    let head = &inner[..symbol_len(inner)?];
    let mut depth = 1usize;
    let mut rest = inner;
    while depth > 0 {
        let step = match rest.chars().next()? {
            '(' => {
                depth += 1;
                1
            }
            ')' => {
                depth -= 1;
                1
            }
            ch if ch.is_whitespace() => ch.len_utf8(),
            '"' => return None,
            _ => symbol_len(rest)?,
        };
        rest = &rest[step..];
    }
    Some((text.len() - rest.len(), Some(unquoted(head))))
}

/// Byte length of the term `text` starts with: an atom, a closed string
/// literal, or a parenthesised list with its matching closer.
///
/// An atom is a `|quoted|` symbol, or a run of characters up to whitespace,
/// a parenthesis, a bar or a double quote (for example `nil`, `-5`, `#x0f`,
/// `:k`, `a#b`); the scan does not check that a run is an SMT-LIB symbol or
/// literal (`a;b` is one atom). A string literal and a quoted symbol are one
/// token each, whatever parentheses, bars and spaces they hold. `None` when
/// `text` starts with whitespace, `)` or nothing, or the term is not closed:
/// an unbalanced list, an unterminated string or quoted symbol.
pub fn smtlib_term_len(text: &str) -> Option<usize> {
    let mut depth = 0usize;
    let mut at = 0;
    loop {
        let rest = &text[at..];
        match rest.chars().next()? {
            '(' => {
                depth += 1;
                at += 1;
            }
            ')' => {
                depth = depth.checked_sub(1)?;
                at += 1;
            }
            '"' => at += closed_string_literal_len(rest)?,
            ch if ch.is_whitespace() => {
                if depth == 0 {
                    return None;
                }
                at += ch.len_utf8();
            }
            _ => at += symbol_len(rest)?,
        }
        if depth == 0 {
            return Some(at);
        }
    }
}

/// The head and the top-level arguments of the one term the trimmed `text`
/// is, each one [`smtlib_term_len`] term: `(cons 1 (cons 2 nil))` gives
/// `cons` with `1` and `(cons 2 nil)`, `(|a b| x)` gives `|a b|` with `x`,
/// and an atom such as `nil` or `|a b|` gives itself with no arguments.
/// `None` when the trimmed text is not one term, or is a list that is empty
/// or headed by a list (`((as const A) 0)`).
pub fn smtlib_application_parts(text: &str) -> Option<(&str, Vec<&str>)> {
    let text = text.trim();
    if smtlib_term_len(text)? != text.len() {
        return None;
    }
    let Some(inner) = text.strip_prefix('(') else {
        return Some((text, Vec::new()));
    };
    let mut parts = Vec::new();
    let mut rest = inner.trim_start();
    while !rest.starts_with(')') {
        let len = smtlib_term_len(rest)?;
        parts.push(&rest[..len]);
        rest = rest[len..].trim_start();
    }
    if parts.first()?.starts_with('(') {
        return None;
    }
    let head = parts.remove(0);
    Some((head, parts))
}

/// The name and the value of the constant one model line defines,
/// `(define-fun name () Sort value)`, or `None`, for example for a function
/// with parameters or a line with no value.
///
/// The name and the sort are each one [`smtlib_term_len`] term, so a quoted
/// symbol holding a space (`|My List|`) stays whole. When the value is one
/// such term followed by the definition's closer, that term is returned with
/// [`bare_constructor_spelling`] applied to it (`(cons 1 (as nil L1))` gives
/// `(cons 1 nil)`). Otherwise, for example for the values `my nil`, `x(y`
/// and `a|b`, the text after the sort, less one final `)`, is returned as it
/// stands.
pub fn model_constant_definition(line: &str) -> Option<(&str, Cow<'_, str>)> {
    let rest = line.trim().strip_prefix("(define-fun")?;
    let name_start = rest.trim_start();
    if name_start.len() == rest.len() || name_start.starts_with(['(', '"']) {
        return None;
    }
    let (name, rest) = name_start.split_at(smtlib_term_len(name_start)?);
    // The parameter list of a constant is empty.
    let rest = rest.trim_start().strip_prefix('(')?;
    let rest = rest.trim_start().strip_prefix(')')?.trim_start();
    if rest.starts_with('"') {
        return None;
    }
    let after_sort = rest[smtlib_term_len(rest)?..].trim();
    let value = match smtlib_term_len(after_sort) {
        Some(len) if after_sort[len..].trim_start() == ")" => {
            bare_constructor_spelling(&after_sort[..len])
        }
        _ => Cow::Borrowed(
            after_sort
                .strip_suffix(')')
                .unwrap_or(after_sort)
                .trim_end(),
        ),
    };
    (!value.is_empty()).then_some((name, value))
}

/// Byte length of the atom `text` starts with: a whole `|quoted symbol|`, or
/// a run of characters up to whitespace, a parenthesis, a bar or a double
/// quote. `None` when that run is empty or the quote is unterminated.
fn symbol_len(text: &str) -> Option<usize> {
    if let Some(quoted) = text.strip_prefix('|') {
        let mut escaped = false;
        for (at, ch) in quoted.char_indices() {
            match ch {
                _ if escaped => escaped = false,
                '\\' => escaped = true,
                '|' => return Some(at + 2),
                _ => {}
            }
        }
        return None;
    }
    let len = text
        .find(|ch: char| ch.is_whitespace() || matches!(ch, '(' | ')' | '|' | '"'))
        .unwrap_or(text.len());
    (len > 0).then_some(len)
}

/// Byte length of the string literal `text` starts with (`""` is an escaped
/// quote); the whole of `text` when the literal is not closed.
fn string_literal_len(text: &str) -> usize {
    closed_string_literal_len(text).unwrap_or(text.len())
}

/// Byte length of the closed string literal `text` starts with (`""` is an
/// escaped quote); `None` when the literal is not closed.
fn closed_string_literal_len(text: &str) -> Option<usize> {
    let bytes = text.as_bytes();
    let mut at = 1;
    while at < bytes.len() {
        if bytes[at] == b'"' {
            if bytes.get(at + 1) != Some(&b'"') {
                return Some(at + 1);
            }
            at += 1;
        }
        at += 1;
    }
    None
}

/// The name a symbol token spells: quotes removed, and inside them `\|` and
/// `\\` read as `|` and `\`.
fn unquoted(symbol: &str) -> String {
    let Some(inner) = symbol
        .strip_prefix('|')
        .and_then(|inner| inner.strip_suffix('|'))
    else {
        return symbol.to_string();
    };
    let mut name = String::with_capacity(inner.len());
    let mut characters = inner.chars().peekable();
    while let Some(character) = characters.next() {
        match (character, characters.peek()) {
            ('\\', Some(&escaped @ ('|' | '\\'))) => {
                characters.next();
                name.push(escaped);
            }
            _ => name.push(character),
        }
    }
    name
}

#[cfg(test)]
mod tests {
    use super::*;

    /// For the names and sorts below, every spelling
    /// `ascribed_constructor_spelling` returns reads back, alone and nested,
    /// as the constructor's `symbol_token`.
    #[test]
    fn a_printed_ascription_always_reads_back_as_the_bare_constructor() {
        let constructors = [
            "nil",
            "const",
            "bag.empty",
            "set.universe",
            "my nil",
            "a|b",
            r"a\b",
            r"a\|b",
            r"a\\|b\",
            "as",
            "pop",
            "let",
            "a#b",
            "x(y",
            "seq.empty",
            "re.none",
            "@S!0",
            "",
        ];
        let sorts = [
            "L1",
            "|L#1|",
            "|L 1|",
            "|L(1|",
            "(List Int)",
            "(Tuple Int Bool)",
            "(Bag Int)",
            "(Relation Int Int)",
            "(|My List| (Pair Int |a b|))",
            "(Array Int Int)",
            "(Seq Int)",
            "(_ FiniteField 7)",
            "(|_| Int)",
            "()",
            "((List) Int)",
            "L1 L2",
            "\"L\"",
        ];
        let mut printed = 0;
        for constructor in constructors {
            for sort in sorts {
                let Some(ascribed) = ascribed_constructor_spelling(constructor, sort) else {
                    continue;
                };
                printed += 1;
                let bare = symbol_token(constructor);
                assert_eq!(bare_constructor_spelling(&ascribed), bare, "{ascribed}");
                let nested = format!("(w {ascribed} (cons 1 {ascribed}))");
                assert_eq!(
                    bare_constructor_spelling(&nested),
                    format!("(w {bare} (cons 1 {bare}))"),
                    "{nested}"
                );
            }
        }
        // Fifteen of these names under nine of these sorts: not `seq.empty`,
        // `re.none` or `@S!0`, and not the last eight sorts.
        assert_eq!(printed, 15 * 9);
        for (constructor, sort) in [
            ("const", "L1"),
            ("bag.empty", "(Bag Int)"),
            ("set.universe", "|L#1|"),
            ("nil", "(Tuple Int Bool)"),
            ("nil", "(Relation Int Int)"),
        ] {
            assert!(
                ascribed_constructor_spelling(constructor, sort).is_some(),
                "({constructor} {sort}) is declarable, so it is ascribed"
            );
        }
    }

    /// Each text of the first list starts with the term paired with it; no
    /// text of the second list starts with a term.
    #[test]
    fn a_term_ends_at_its_token_boundary() {
        for (text, term) in [
            ("nil)", "nil"),
            ("|My List| (as nil |My List|))", "|My List|"),
            ("(as nil |My List|))", "(as nil |My List|)"),
            ("(|My List| Int) nil)", "(|My List| Int)"),
            ("(cons 1 (as nil |a ) b|)) x", "(cons 1 (as nil |a ) b|))"),
            (
                "\"a | (as nil L1) \"\" )\" tail",
                "\"a | (as nil L1) \"\" )\"",
            ),
            (
                "(mk \"|\" \"(as nil L1)\" |x \" y|))",
                "(mk \"|\" \"(as nil L1)\" |x \" y|)",
            ),
            ("(- 5))", "(- 5)"),
            ("-5)", "-5"),
            ("#x0f)", "#x0f"),
            ("()", "()"),
            ("( ) x", "( )"),
            (r"|a\|b| c", r"|a\|b|"),
            ("(_ bv5 8)(x)", "(_ bv5 8)"),
        ] {
            assert_eq!(smtlib_term_len(text).map(|len| &text[..len]), Some(term));
        }
        for text in [
            "",
            " nil",
            ")",
            "(cons 1 nil",
            "(cons 1 |nil)",
            "\"open",
            "(mk \"open)",
            "|open",
        ] {
            assert_eq!(smtlib_term_len(text), None, "{text}");
        }
        // `a|b)` starts with the term `a`.
        assert_eq!(smtlib_term_len("a|b)"), Some(1));
    }

    /// Each text of the first list splits into the head and the arguments
    /// paired with it; no text of the second list splits.
    #[test]
    fn an_application_splits_at_its_term_boundaries() {
        for (text, head, arguments) in [
            ("nil", "nil", vec![]),
            (" nil ", "nil", vec![]),
            ("(cons A (cons B nil))", "cons", vec!["A", "(cons B nil)"]),
            (
                "(mk (cons A nil) false)",
                "mk",
                vec!["(cons A nil)", "false"],
            ),
            ("(|a b| x)", "|a b|", vec!["x"]),
            ("|a b|", "|a b|", vec![]),
            ("||", "||", vec![]),
            ("(c1 4 ||)", "c1", vec!["4", "||"]),
            (r"(|a\|b| |x y| (- 7))", r"|a\|b|", vec!["|x y|", "(- 7)"]),
            ("(rec \"a ) b\" k)", "rec", vec!["\"a ) b\"", "k"]),
            ("(as |a b| D)", "as", vec!["|a b|", "D"]),
        ] {
            assert_eq!(
                smtlib_application_parts(text),
                Some((head, arguments)),
                "{text}"
            );
        }
        for text in [
            "",
            "a b",
            "(cons A",
            "()",
            "((as const (Array Int Int)) 0)",
            "|open",
            "nil)",
        ] {
            assert_eq!(smtlib_application_parts(text), None, "{text}");
        }
    }

    /// Each name below spells an ascription or a part of one. Its
    /// `symbol_token` is a quoted symbol that `bare_constructor_spelling`
    /// leaves as written, and its ascribed spelling under `L1` reads back as
    /// that token.
    #[test]
    fn a_name_that_spells_an_ascription_reads_back_as_its_token() {
        for name in [
            "(as nil L)",
            "(w (as nil L) 1)",
            "(as |pop| (List Int))",
            "(as @S!0 S)",
            "(as seq.empty (Seq Int))",
            "(as",
            "as nil L",
        ] {
            let token = symbol_token(name);
            assert_eq!(bare_constructor_spelling(&token), token, "{name}");
            let ascribed = ascribed_constructor_spelling(name, "L1").expect(name);
            assert_eq!(bare_constructor_spelling(&ascribed), token, "{ascribed}");
        }
    }

    /// Each line of the first list gives the name and the value paired with
    /// it; no line of the second gives a definition.
    #[test]
    fn a_definition_line_gives_the_name_and_the_whole_value() {
        for (line, name, value) in [
            ("(define-fun n () Int (- 5))", "n", "(- 5)"),
            ("  (define-fun n () Real (- (/ 1 2)))", "n", "(- (/ 1 2))"),
            ("(define-fun t () |My List| nil)", "t", "nil"),
            ("(define-fun t () |My List| (as nil |My List|))", "t", "nil"),
            (
                "(define-fun t () (|My Pair| Int Bool) (cons 1 (as nil L1)))",
                "t",
                "(cons 1 nil)",
            ),
            (
                "(define-fun r () Rec (rec \"| (as nil L1) )\" (as nil L1) (- 7)))",
                "r",
                "(rec \"| (as nil L1) )\" nil (- 7))",
            ),
            ("(define-fun |a b| () L1 (as |pop| L1))", "|a b|", "|pop|"),
            ("(define-fun s () String \"a ) |\")", "s", "\"a ) |\""),
        ] {
            let (read_name, read_value) = model_constant_definition(line).expect(line);
            assert_eq!((read_name, read_value.as_ref()), (name, value), "{line}");
        }
        for line in [
            "(define-fun f ((x0 Int)) Int 0)",
            "(declare-fun n () Int)",
            "(define-fun n () Int)",
            "(model",
            ")",
        ] {
            assert_eq!(model_constant_definition(line), None, "{line}");
        }
    }

    /// Each line below gives the value paired with it: its text after the
    /// sort, less the final `)`.
    #[test]
    fn a_value_that_is_no_term_is_returned_as_written() {
        for (line, value) in [
            ("(define-fun top () L1 x (as nil L1) y)", "x (as nil L1) y"),
            ("(define-fun top () L1 my nil)", "my nil"),
            ("(define-fun top () L1 a|b)", "a|b"),
            ("(define-fun top () L1 x(y)", "x(y"),
            (
                "(define-fun r () Rec (rec p|q (as nil L1) c\"d))",
                "(rec p|q (as nil L1) c\"d)",
            ),
        ] {
            let (_, read) = model_constant_definition(line).expect(line);
            assert_eq!(read, value, "{line}");
        }
    }

    /// `bare_constructor_spelling` leaves each text of the first list as
    /// written, and gives each later text the text paired with it.
    #[test]
    fn theory_values_and_other_text_keep_their_spelling() {
        for text in [
            "(as seq.empty (Seq Int))",
            "(as set.empty (Set Int))",
            "((as const (Array Int Int)) 0)",
            "((as const A) 0)",
            "( (as const A) (mk ( (as nil L))))",
            "(as ff3 (_ FiniteField 7))",
            "(as @S!0 S)",
            "(as |@S 1!0| S)",
            "(as nil (Seq Int))",
            "(as nil L extra)",
            "(as nil (List Int) extra)",
            "(as nil)",
            "(as nil ())",
            "(as nil ((List) Int))",
            "(as (nil) L)",
            "(as nil |L)",
            "(as nil \"L\")",
            "(asnil L)",
            "\"(as nil L)\"",
            "|(as nil L)|",
            "(w \"a \"\" (as nil L)\" 1)",
        ] {
            assert_eq!(bare_constructor_spelling(text), text, "{text}");
        }
        assert_eq!(
            bare_constructor_spelling("((as const (Array Int L)) (as nil L))"),
            "((as const (Array Int L)) nil)"
        );
        assert_eq!(
            bare_constructor_spelling("(mk (as  |my nil|   (|My List| Int) ) \"(as\")"),
            "(mk |my nil| \"(as\")"
        );
        // Atoms that hold a bar or a double quote, and the quoted symbol
        // `|a b|`, beside an ascription or a string literal.
        for (ascribed, bare) in [
            ("(w2 a|b (as nil L1))", "(w2 a|b nil)"),
            ("(w3 a|b (as nil L1) c|d)", "(w3 a|b nil c|d)"),
            ("(w3 a\"b (as nil L1) c\"d)", "(w3 a\"b nil c\"d)"),
            ("(w2 a|b \"(as nil L1)\")", "(w2 a|b \"(as nil L1)\")"),
            ("(w2 |a b| (as nil L1))", "(w2 |a b| nil)"),
        ] {
            assert_eq!(bare_constructor_spelling(ascribed), bare, "{ascribed}");
        }
        // Here each quoted name keeps its quotes.
        for (ascribed, bare) in [
            ("(as |pop| Op1)", "|pop|"),
            ("(w (as |pop| Op1) (as |a#b| Op2))", "(w |pop| |a#b|)"),
            ("(as |let| L)", "|let|"),
            (r"(as |a\|b| L)", r"|a\|b|"),
            (r"(as |a\\b| L)", r"|a\\b|"),
            ("(as || L)", "||"),
            ("(cons 1 (as || L))", "(cons 1 ||)"),
        ] {
            assert_eq!(bare_constructor_spelling(ascribed), bare, "{ascribed}");
        }
    }
}

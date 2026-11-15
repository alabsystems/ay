// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Splitting an SMT-LIB command's source text into the raw text of its items
//! (see the parent module): the rewrite of a recursive definition keeps the
//! caller's own spelling of every sort, parameter and body.

/// Skip whitespace and `;` comments from `at`.
fn skip_blank(bytes: &[u8], mut at: usize) -> usize {
    while at < bytes.len() {
        match bytes[at] {
            b' ' | b'\t' | b'\n' | b'\r' => at += 1,
            b';' => {
                while at < bytes.len() && bytes[at] != b'\n' {
                    at += 1;
                }
            }
            _ => break,
        }
    }
    at
}

/// The end (exclusive) of the item starting at `at`.
fn item_end(bytes: &[u8], at: usize) -> Option<usize> {
    let mut depth = 0usize;
    let mut i = at;
    loop {
        let byte = *bytes.get(i)?;
        match byte {
            b'(' => {
                depth += 1;
                i += 1;
            }
            b')' => {
                depth = depth.checked_sub(1)?;
                i += 1;
                if depth == 0 {
                    return Some(i);
                }
            }
            b'|' => {
                i += 1;
                while *bytes.get(i)? != b'|' {
                    i += 1;
                }
                i += 1;
                if depth == 0 {
                    return Some(i);
                }
            }
            b'"' => {
                i += 1;
                loop {
                    if *bytes.get(i)? == b'"' {
                        if bytes.get(i + 1) == Some(&b'"') {
                            i += 2;
                            continue;
                        }
                        break;
                    }
                    i += 1;
                }
                i += 1;
                if depth == 0 {
                    return Some(i);
                }
            }
            b';' => {
                while i < bytes.len() && bytes[i] != b'\n' {
                    i += 1;
                }
            }
            b' ' | b'\t' | b'\n' | b'\r' => {
                if depth == 0 {
                    return Some(i);
                }
                i += 1;
            }
            _ => {
                i += 1;
                if depth == 0 && matches!(bytes.get(i), None | Some(b'(' | b')' | b'"' | b'|')) {
                    return Some(i);
                }
            }
        }
    }
}

/// The raw text of each item of the list `text` (one parenthesized
/// expression, possibly surrounded by blanks); `None` when `text` is not a
/// list.
pub(super) fn list_items(text: &str) -> Option<Vec<&str>> {
    let bytes = text.as_bytes();
    let open = skip_blank(bytes, 0);
    if bytes.get(open) != Some(&b'(') {
        return None;
    }
    let close = item_end(bytes, open)?;
    let mut items = Vec::new();
    let mut at = open + 1;
    loop {
        at = skip_blank(bytes, at);
        if at + 1 >= close {
            break;
        }
        let end = item_end(bytes, at)?;
        items.push(text.get(at..end)?);
        at = end;
    }
    Some(items)
}

/// The surface name of a symbol spelled `text` (`|a b|` is `a b`).
pub(super) fn symbol_name(text: &str) -> String {
    let text = text.trim();
    text.strip_prefix('|')
        .and_then(|inner| inner.strip_suffix('|'))
        .unwrap_or(text)
        .to_string()
}

/// How many top-level `assert` commands `text` holds.
pub(super) fn count_asserts(text: &str) -> usize {
    let bytes = text.as_bytes();
    let mut at = 0usize;
    let mut count = 0usize;
    loop {
        at = skip_blank(bytes, at);
        if at >= bytes.len() {
            break;
        }
        let Some(end) = item_end(bytes, at) else {
            break;
        };
        if list_items(&text[at..end]).is_some_and(|items| items.first() == Some(&"assert")) {
            count += 1;
        }
        at = end;
    }
    count
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn items_keep_the_callers_spelling() {
        let items = list_items(
            "(define-fun-rec |f g| ((x Int) (|y z| (_ BitVec 8))) Int ; c\n (ite (> x 0) \"a)\" x))",
        )
        .expect("a list");
        assert_eq!(
            items,
            vec![
                "define-fun-rec",
                "|f g|",
                "((x Int) (|y z| (_ BitVec 8)))",
                "Int",
                "(ite (> x 0) \"a)\" x)"
            ]
        );
        assert_eq!(symbol_name("|f g|"), "f g");
        assert_eq!(
            count_asserts("(declare-fun f (Int) Int)(assert (= 1 1)) (assert true)"),
            2
        );
    }
}

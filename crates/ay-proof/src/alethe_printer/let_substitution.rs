// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Compare a simple printed `let` expansion without allocating its tree.
//!
//! An authored DAG can expand exponentially even when its eliminated term is
//! small or differs at the first token. Retain borrowed source slices, descend
//! only into bindings from an outer scope, and compare each output piece
//! directly with the existing document spelling. Every scan is charged before
//! it runs; failure never installs a rendering or a certified bridge.

use super::{HashMap, PrintedLetLevel};

/// One delimiter or whole token, keeping quoted symbols and strings atomic.
fn piece<'a>(
    text: &'a str,
    admit: &mut impl FnMut(usize) -> bool,
) -> Option<(&'a str, &'a str, bool)> {
    let first = text.chars().next()?;
    if first == '(' || first == ')' || first.is_whitespace() {
        let end = first.len_utf8();
        return admit(end).then_some((&text[..end], &text[end..], false));
    }
    let mut quote = None;
    for (offset, c) in text.char_indices() {
        if !admit(c.len_utf8()) {
            return None;
        }
        if let Some(delimiter) = quote {
            if c == delimiter {
                quote = None;
            }
        } else if c == '|' || c == '"' {
            quote = Some(c);
        } else if c == '(' || c == ')' || c.is_whitespace() {
            return Some((&text[..offset], &text[offset..], true));
        }
    }
    quote.is_none().then_some((text, "", true))
}

/// The simple-let proof has no capture-avoiding renaming rule for an embedded
/// binder. Such a subtree can pass unchanged only when no active substitution
/// reaches it; otherwise refuse before comparing any expanded text.
fn inspect_source(
    mut text: &str,
    owner: Option<usize>,
    bindings: &HashMap<&str, (&str, usize)>,
    admit: &mut impl FnMut(usize) -> bool,
) -> bool {
    let mut at_head = false;
    let mut depth = 0usize;
    let mut opaque_binder = None;
    while !text.is_empty() {
        let Some((head, tail, token)) = piece(text, admit) else {
            return false;
        };
        if token {
            if at_head
                && matches!(
                    head,
                    "let" | "forall" | "exists" | "lambda" | "choice" | "match"
                )
            {
                opaque_binder.get_or_insert(depth);
            }
            if !admit(head.len()) {
                return false;
            }
            if let Some(&(_, bound)) = bindings.get(head) {
                if owner == Some(bound)
                    || (opaque_binder.is_some() && owner.is_none_or(|level| bound < level))
                {
                    return false;
                }
            }
            at_head = false;
        } else if head == "(" {
            let Some(next_depth) = depth.checked_add(1) else {
                return false;
            };
            depth = next_depth;
            at_head = true;
        } else if head == ")" {
            if opaque_binder == Some(depth) {
                opaque_binder = None;
            }
            let Some(next_depth) = depth.checked_sub(1) else {
                return false;
            };
            depth = next_depth;
            at_head = false;
        }
        text = tail;
    }
    depth == 0
}

/// Only unique names without references within a parallel level are admitted.
/// Those restrictions are the certified `let` bridge's original simple-binding
/// profile; rejecting them here cannot silently choose sequential semantics.
pub(super) fn matches(
    levels: &[PrintedLetLevel],
    body: &str,
    mut expected: &str,
    mut admit: impl FnMut(usize) -> bool,
) -> bool {
    if levels.len() > 64 || !admit(65 * std::mem::size_of::<(&str, usize)>()) {
        return false;
    }
    let binding_count = levels.iter().try_fold(0usize, |count, (bindings, _)| {
        count.checked_add(bindings.len())
    });
    let Some(binding_count) = binding_count else {
        return false;
    };
    let Some(table_work) =
        binding_count.checked_mul(2 * std::mem::size_of::<(&str, &str, usize)>())
    else {
        return false;
    };
    if !admit(table_work) {
        return false;
    }
    let mut bindings = HashMap::default();
    bindings.reserve(binding_count);
    for (level, (entries, _)) in levels.iter().enumerate() {
        for (name, value) in entries {
            if !admit(name.len())
                || bindings
                    .insert(name.as_str(), (value.as_str(), level))
                    .is_some()
            {
                return false;
            }
        }
    }
    for (level, (entries, _)) in levels.iter().enumerate() {
        for (_, value) in entries {
            if !inspect_source(value, Some(level), &bindings, &mut admit) {
                return false;
            }
        }
    }
    if !inspect_source(body, None, &bindings, &mut admit) {
        return false;
    }
    let mut stack = Vec::with_capacity(levels.len() + 1);
    stack.push((body, levels.len()));
    while let Some((text, scope)) = stack.pop() {
        if text.is_empty() {
            continue;
        }
        // The lexer charges before each character; hashing and comparing the
        // resulting piece are charged before either operation too.
        let Some((head, tail, token)) = piece(text, &mut admit) else {
            return false;
        };
        if !admit(head.len().saturating_mul(2)) {
            return false;
        }
        stack.push((tail, scope));
        let binding = token
            .then(|| bindings.get(head).copied())
            .flatten()
            .filter(|&(_, level)| level < scope);
        if let Some((value, outer_scope)) = binding {
            stack.push((value, outer_scope));
        } else if let Some(rest) = expected.strip_prefix(head) {
            expected = rest;
        } else {
            return false;
        }
    }
    expected.is_empty()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn compare(surface: &str, expected: &str) -> bool {
        let (levels, body) = super::super::peel_printed_lets(surface).expect("let fixture");
        matches(&levels, &body, expected, |_| true)
    }

    #[test]
    fn nested_bindings_expand_in_their_own_outer_scope() {
        assert!(compare(
            "(let ((a p)) (let ((b (f a a))) (= b (f p a))))",
            "(= (f p p) (f p p))"
        ));
        // `inner` in an outer binding value remains a free symbol, even
        // though the inner level later introduces a binding with that name.
        assert!(compare(
            "(let ((outer inner)) (let ((inner p)) (= outer inner)))",
            "(= inner p)"
        ));
    }

    #[test]
    fn token_boundaries_and_quoted_literals_are_preserved() {
        assert!(compare(
            "(let ((a p)) (f a ab |a b| \"a b\" \"a\"\"b\"))",
            "(f p ab |a b| \"a b\" \"a\"\"b\")"
        ));
        assert!(compare("(let ((|a b| p)) (= |a b| q))", "(= p q)"));
        assert!(compare(
            "(let ((a p) (s \"x a y\")) (= s \"x a y\"))",
            "(= \"x a y\" \"x a y\")"
        ));
        assert!(!compare("(let ((a p)) (f a))", "(f q)"));
        assert!(!compare("(let ((a p)) (f a))", "(f p)extra"));
    }

    #[test]
    fn shadowing_and_parallel_references_cannot_certify() {
        assert!(!compare("(let ((a p)) (let ((a q)) a))", "q"));
        assert!(!compare("(let ((a p) (b a)) b)", "p"));
        assert!(!compare("(let ((a a)) a)", "a"));
    }

    #[test]
    fn embedded_binders_cannot_capture_a_substituted_free_name() {
        for (body, captured) in [
            ("(forall ((y Bool)) (= a y))", "(forall ((y Bool)) (= y y))"),
            ("(exists ((y Bool)) (= a y))", "(exists ((y Bool)) (= y y))"),
            ("(lambda ((y Bool)) (= a y))", "(lambda ((y Bool)) (= y y))"),
            ("(choice ((y Bool)) (= a y))", "(choice ((y Bool)) (= y y))"),
            (
                "(f (let ((y true)) (= a y)))",
                "(f (let ((y true)) (= y y)))",
            ),
            ("(match v (((C y) (= a y))))", "(match v (((C y) (= y y))))"),
        ] {
            let source = format!("(let ((a y)) {body})");
            assert!(!compare(&source, &captured), "{source}");
        }
        assert!(compare(
            "(let ((a (forall ((y Bool)) (= z y)))) (f a))",
            "(f (forall ((y Bool)) (= z y)))"
        ));
        assert!(!compare(
            "(let ((a y)) (let ((b (forall ((y Bool)) (= a y)))) (f b)))",
            "(f (forall ((y Bool)) (= y y)))"
        ));
        assert!(compare(
            "(let ((unused p)) (or s (let ((inner q)) (and p inner r))))",
            "(or s (let ((inner q)) (and p inner r)))"
        ));
        assert!(compare("(let ((a y)) (f a |forall|))", "(f y |forall|)"));
    }

    #[test]
    fn exponential_expansion_stops_at_the_first_mismatch() {
        let mut surface = "x63".to_string();
        for level in (1..64).rev() {
            surface = format!(
                "(let ((x{level} (f x{} x{}))) {surface})",
                level - 1,
                level - 1
            );
        }
        surface = format!("(let ((x0 p)) {surface})");
        let (levels, body) = super::super::peel_printed_lets(&surface).expect("64 levels");
        let mut work = 0usize;
        assert!(!matches(&levels, &body, "q", |charge| {
            work += charge;
            work <= 16 * 1024
        }));
        assert!(work < 16 * 1024, "first-token mismatch used {work} work");
    }

    #[test]
    fn exhausted_work_cannot_certify_even_an_exact_expansion() {
        let (levels, body) = super::super::peel_printed_lets("(let ((a p)) (= a p))").expect("let");
        assert!(!matches(&levels, &body, "(= p p)", |_| false));
    }
}

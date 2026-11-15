// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The one premise spelling pinned Carcara's sorts tell apart although
//! [`super::normalize_premise_surface`] equates it: a `let` variable bound to
//! an `Int`-sorted numeral term, in a logic with reals and no integers.

/// A parsed s-expression of a printed premise: an atom (a symbol, numeral,
/// decimal, or a quoted symbol / string literal kept whole) or a list.
enum Sexp<'a> {
    Atom(&'a str),
    List(Vec<Sexp<'a>>),
}

/// Deepest list nesting [`parse_sexp`] reads; a deeper premise is not judged
/// (every walk below recurses once per level).
const MAX_DEPTH: usize = 1024;

/// Parse the first s-expression of `text`, or `None` when it is malformed or
/// nested deeper than [`MAX_DEPTH`].
fn parse_sexp(text: &str) -> Option<Sexp<'_>> {
    fn parse<'a>(text: &'a str, at: &mut usize, depth: usize) -> Option<Sexp<'a>> {
        if depth > MAX_DEPTH {
            return None;
        }
        let bytes = text.as_bytes();
        while *at < bytes.len() && bytes[*at].is_ascii_whitespace() {
            *at += 1;
        }
        match *bytes.get(*at)? {
            b'(' => {
                *at += 1;
                let mut items = Vec::new();
                loop {
                    while *at < bytes.len() && bytes[*at].is_ascii_whitespace() {
                        *at += 1;
                    }
                    match *bytes.get(*at)? {
                        b')' => {
                            *at += 1;
                            return Some(Sexp::List(items));
                        }
                        _ => items.push(parse(text, at, depth + 1)?),
                    }
                }
            }
            b')' => None,
            delimiter @ (b'"' | b'|') => {
                let start = *at;
                *at += 1;
                loop {
                    let byte = *bytes.get(*at)?;
                    *at += 1;
                    if byte == delimiter {
                        if delimiter == b'"' && bytes.get(*at) == Some(&b'"') {
                            *at += 1;
                            continue;
                        }
                        return Some(Sexp::Atom(&text[start..*at]));
                    }
                }
            }
            _ => {
                let start = *at;
                while *at < bytes.len()
                    && !bytes[*at].is_ascii_whitespace()
                    && !matches!(bytes[*at], b'(' | b')' | b'"' | b'|')
                {
                    *at += 1;
                }
                Some(Sexp::Atom(&text[start..*at]))
            }
        }
    }
    parse(text, &mut 0, 0)
}

/// Whether a printed term is `Int`-sorted in a logic that has no `Int`
/// symbol: with no `Int` variable to read, only a numeral, arithmetic over
/// such terms, an `ite` whose branch is one, or a `let` variable bound to one.
fn int_sorted(term: &Sexp<'_>, int_vars: &[&str]) -> bool {
    match term {
        Sexp::Atom(atom) => {
            (!atom.is_empty() && atom.bytes().all(|b| b.is_ascii_digit()))
                || int_vars.contains(atom)
        }
        Sexp::List(items) => match items.as_slice() {
            [Sexp::Atom(op), args @ ..]
                if matches!(*op, "+" | "-" | "*" | "div" | "mod" | "abs") && !args.is_empty() =>
            {
                args.iter().all(|arg| int_sorted(arg, int_vars))
            }
            [Sexp::Atom("ite"), _, then, _] => int_sorted(then, int_vars),
            [Sexp::Atom("!"), inner, ..] => int_sorted(inner, int_vars),
            [Sexp::Atom("let"), Sexp::List(bindings), body] => {
                let mut scope = int_vars.to_vec();
                for binding in bindings {
                    if let Sexp::List(pair) = binding {
                        if let [Sexp::Atom(name), value] = pair.as_slice() {
                            if int_sorted(value, int_vars) {
                                scope.push(name);
                            }
                        }
                    }
                }
                int_sorted(body, &scope)
            }
            _ => false,
        },
    }
}

/// The first `let` variable a printed premise binds to an `Int`-sorted term,
/// in a logic with reals and no integers, or `None`.
fn int_let_binder<'a>(term: &Sexp<'a>, int_vars: &mut Vec<&'a str>) -> Option<&'a str> {
    let Sexp::List(items) = term else {
        return None;
    };
    if let [Sexp::Atom("let"), Sexp::List(bindings), body] = items.as_slice() {
        let depth = int_vars.len();
        let mut found = None;
        for binding in bindings {
            if let Sexp::List(pair) = binding {
                if let [Sexp::Atom(name), value] = pair.as_slice() {
                    found = found.or_else(|| int_let_binder(value, &mut int_vars.clone()));
                    if int_sorted(value, int_vars) {
                        found = found.or(Some(*name));
                    }
                }
            }
        }
        if found.is_none() {
            found = int_let_binder(body, int_vars);
        }
        int_vars.truncate(depth);
        return found;
    }
    items.iter().find_map(|item| int_let_binder(item, int_vars))
}

/// The first `let` variable a printed premise binds to an `Int`-sorted term,
/// for a premise of a problem whose logic has reals and no integers, or
/// `None`.
///
/// [`super::normalize_premise_surface`] equates `4` with `4.0`, and pinned Carcara
/// agrees for a constant: it reads the problem's numerals as `Real`s in such
/// a logic and the certificate's as `Int`s, and matches the two by value. It
/// does NOT match a `let` whose variable has a different sort on the two
/// sides: where AY keeps an authored numeral term `Int`-sorted (`(ite c 4 0)`
/// compared only with numerals) and binds it in a `let`, the certificate's
/// variable is an `Int` and the problem's a `Real`, so the `assume` is not the
/// premise Carcara parsed and it reports the certificate *invalid* there.
/// Measured on the D7 list (2026-10-08, `carcara check
/// --allow-int-real-subtyping`): `QF_LRA/.../Carpark2-ausgabe-1.smt2` was
/// disclosed `foreign_assumes=no` and "holey" and refused ("could not match
/// term to any of the original problem premises"); `(let ((v (ite b 4 0)))
/// (= v 4))` is refused and `(= (ite b 4 0) 4)` is accepted, so the rule is
/// the binder, not the numeral (a numeral-only rule mispredicted four D7
/// files Carcara accepts).
#[must_use]
pub fn premise_int_let_binding(text: &str) -> Option<String> {
    let term = parse_sexp(text)?;
    int_let_binder(&term, &mut Vec::new()).map(str::to_string)
}

#[cfg(test)]
mod tests {
    use super::premise_int_let_binding as int_let;

    /// Pinned Carcara matches a problem's `Real` numeral with a certificate's
    /// `Int` one by value, but not a `let` variable whose sort differs.
    #[test]
    fn only_a_let_bound_int_term_is_found() {
        assert_eq!(
            int_let("(let ((v (ite b 4 0))) (and b (= x (ite (= v 4) 20.0 1.0))))").as_deref(),
            Some("v")
        );
        assert_eq!(int_let("(= (ite b 4 0) 4)"), None);
        assert_eq!(int_let("(let ((v (ite b 4.0 0.0))) (= v 4.0))"), None);
        assert_eq!(int_let("(let ((v (* x (/ 1770 689)))) (<= v 0))"), None);
        assert_eq!(
            int_let("(let ((v (+ 1 (* 2 3)))) (= v 7))").as_deref(),
            Some("v")
        );
        // A variable bound to an Int-sorted variable is Int-sorted too.
        assert_eq!(
            int_let("(let ((a (- 3))) (let ((b (ite p a 1.0)) (c (ite p a 2))) (= b c)))")
                .as_deref(),
            Some("a")
        );
        assert_eq!(int_let("(let ((a (< x 1.0))) a)"), None);
        assert_eq!(int_let("(let ((a |7|)) a)"), None);
        // Too deep to judge: no answer rather than a deep recursion.
        let deep = format!("(let ((v 1)) {}v{})", "(+ ".repeat(5000), ")".repeat(5000));
        assert_eq!(int_let(&deep), None);
    }
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Whether two printed terms differ only by EXACT linear-arithmetic
//! respellings: the lenient negative literal (`-2` against `(- 2)`) and a
//! literal-zero summand (`(+ x 0)` against `x`).
//!
//! THE SHAPE. The frontend interns `(+ x1 0)` as `x1` and reads the lenient
//! `-2` as the numeral it means; the surface-override ledger prints both back
//! as authored. A theory lemma over such an atom then prints `(< x0 -1)` where
//! the term DAG renders `(< x0 (- 1))`, and the wire classifier called that a
//! changed clause, so a Farkas lemma the printed-row replay accepts shipped as
//! a `hole` (measured on the OR-substitution fuzz).
//!
//! WHAT THIS PROMISES, AND WHAT IT DOES NOT. Both respellings denote the same
//! arithmetic term, so the printed atom is the SAME atom, like the converse
//! spelling `surface_order_reversal` recognises. They are not the same TERM to
//! pinned Carcara's parser (`-2` is a constant, `(- 2)` unary minus), so a
//! clause classified this way is
//! [`super::ClauseSurfaceAgreement::LinearRespelled`]: callers publish numeric
//! evidence for it only after replaying the certificate over the exact printed
//! clause, as they do for an equality printed in reverse.
//!
//! The comparison parses each text once and visits every node of the left
//! tree at most once, so it is linear in the two texts.

/// One parsed node of a printed term.
enum Node<'a> {
    Atom(&'a str),
    List(Vec<Node<'a>>),
}

/// Whether `left` and `right` print the same arithmetic term up to the exact
/// respellings above. Byte-identical texts are trivially related; a text that
/// does not parse as one balanced term relates only to itself.
pub(super) fn equal_modulo_linear_respelling(left: &str, right: &str) -> bool {
    if left == right {
        return true;
    }
    match (parse(left), parse(right)) {
        (Some(left), Some(right)) => related(&left, &right),
        _ => false,
    }
}

fn related(left: &Node<'_>, right: &Node<'_>) -> bool {
    if negative_literal_pair(left, right) || negative_literal_pair(right, left) {
        return true;
    }
    if let Some(survivor) = sole_nonzero_summand(left) {
        return related(survivor, right);
    }
    if let Some(survivor) = sole_nonzero_summand(right) {
        return related(left, survivor);
    }
    match (left, right) {
        (Node::Atom(left), Node::Atom(right)) => left == right,
        (Node::List(left), Node::List(right)) => {
            left.len() == right.len()
                && left
                    .iter()
                    .zip(right)
                    .all(|(left, right)| related(left, right))
        }
        _ => false,
    }
}

/// `literal` is the lenient `-n` and `applied` is `(- n)`.
fn negative_literal_pair(literal: &Node<'_>, applied: &Node<'_>) -> bool {
    let (Node::Atom(literal), Node::List(applied)) = (literal, applied) else {
        return false;
    };
    let [Node::Atom("-"), Node::Atom(magnitude)] = applied.as_slice() else {
        return false;
    };
    literal.strip_prefix('-') == Some(*magnitude) && is_unsigned_number(magnitude)
}

/// The one summand left of `(+ ..)` once its literal zeros are dropped, when
/// every other summand is a literal zero and at least one is.
fn sole_nonzero_summand<'n, 'a>(node: &'n Node<'a>) -> Option<&'n Node<'a>> {
    let Node::List(items) = node else {
        return None;
    };
    let (Node::Atom("+"), summands) = items.split_first()? else {
        return None;
    };
    let mut survivors = summands
        .iter()
        .filter(|summand| !matches!(summand, Node::Atom("0" | "0.0")));
    let survivor = survivors.next()?;
    (survivors.next().is_none() && summands.len() > 1).then_some(survivor)
}

fn is_unsigned_number(text: &str) -> bool {
    text.starts_with(|c: char| c.is_ascii_digit())
        && text.chars().all(|c| c.is_ascii_digit() || c == '.')
}

/// Parse one balanced printed term: parentheses, `|quoted|` symbols and
/// `"string"` literals (with `""` escapes) are honoured. `None` for anything
/// else, including trailing text.
fn parse(text: &str) -> Option<Node<'_>> {
    let mut tokens = tokens(text)?.into_iter();
    let mut stack: Vec<Vec<Node<'_>>> = Vec::new();
    let mut root = None;
    for token in tokens.by_ref() {
        if root.is_some() {
            return None;
        }
        match token {
            "(" => stack.push(Vec::new()),
            ")" => {
                let list = Node::List(stack.pop()?);
                match stack.last_mut() {
                    Some(parent) => parent.push(list),
                    None => root = Some(list),
                }
            }
            atom => match stack.last_mut() {
                Some(parent) => parent.push(Node::Atom(atom)),
                None => root = Some(Node::Atom(atom)),
            },
        }
    }
    stack.is_empty().then_some(root).flatten()
}

fn tokens(text: &str) -> Option<Vec<&str>> {
    let bytes = text.as_bytes();
    let mut tokens = Vec::new();
    let mut index = 0;
    while index < bytes.len() {
        let start = index;
        match bytes[index] {
            b' ' | b'\t' | b'\n' | b'\r' => {
                index += 1;
                continue;
            }
            b'(' | b')' => index += 1,
            b'|' => {
                index += 1 + bytes[index + 1..].iter().position(|&byte| byte == b'|')? + 1;
            }
            b'"' => {
                index += 1;
                loop {
                    index += bytes[index..].iter().position(|&byte| byte == b'"')? + 1;
                    if bytes.get(index) != Some(&b'"') {
                        break;
                    }
                    index += 1;
                }
            }
            _ => {
                while index < bytes.len()
                    && !matches!(bytes[index], b' ' | b'\t' | b'\n' | b'\r' | b'(' | b')')
                {
                    index += 1;
                }
            }
        }
        tokens.push(text.get(start..index)?);
    }
    Some(tokens)
}

#[cfg(test)]
mod tests {
    use super::equal_modulo_linear_respelling as same;

    #[test]
    fn a_lenient_negative_literal_is_its_unary_minus() {
        assert!(same("(< x0 -1)", "(< x0 (- 1))"));
        assert!(same("(<= 3 (+ x0 -2))", "(<= 3 (+ x0 (- 2)))"));
        assert!(!same("(< x0 -1)", "(< x0 (- 2))"));
        assert!(!same("(< x0 -x)", "(< x0 (- x))"));
    }

    #[test]
    fn a_literal_zero_summand_drops() {
        assert!(same("(<= x4 (+ x3 0))", "(<= x4 x3)"));
        assert!(same("(= x2 (+ 0 x0))", "(= x2 x0)"));
        assert!(same("(+ (+ y -3) 0)", "(+ y (- 3))"));
        assert!(!same("(<= x4 (+ x3 1))", "(<= x4 x3)"));
        assert!(!same("(+ x 0 y)", "x"));
    }

    #[test]
    fn any_other_difference_is_a_different_term() {
        assert!(!same("(< x y)", "(< y x)"));
        assert!(!same("(< x y)", "(<= x y)"));
        assert!(!same("(f x)", "(f x x)"));
        assert!(!same("(< x", "(< x)"));
        assert!(same("|a b|", "|a b|"));
        assert!(!same("(= |a)| 0)", "(= |a| 0)"));
    }
}

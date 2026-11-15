// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The consumer's equality rules (Clean's Carcara `reflexivity.rs`,
//! `transitivity.rs`, `congruence.rs`, `symm`/`not_symm` from `extras.rs`),
//! its array rules (`arrays.rs`, without `arrays_ext`) and the `assume`
//! check, with the comparison modulo reordering of equalities (`polyeq`) that
//! `refl` and `assume` fall back on.

use std::collections::HashMap;

use super::document::Document;
use super::{negation, refuse, require, same, shape, undecided, Checked, StepInput, Verdict};

/// `(= a b)`: its two sides.
fn sides(document: &Document, term: u32) -> Result<(u32, u32), Verdict> {
    shape(document, term, "=", 2).map(|sides| (sides[0], sides[1]))
}

/// `polyeq` modulo reordering of equalities, for terms without binders:
/// `Some(false)` only when the terms differ; `None` where a binder (whose
/// renaming the consumer's comparison allows) or the depth bound is met.
pub(super) fn polyeq(document: &Document, a: u32, b: u32) -> Option<bool> {
    fn go(
        document: &Document,
        a: u32,
        b: u32,
        depth: usize,
        memo: &mut HashMap<(u32, u32), Option<bool>>,
    ) -> Option<bool> {
        if a == b {
            return Some(true);
        }
        if depth > 10_000 {
            return None;
        }
        if let Some(&known) = memo.get(&(a, b)) {
            return known;
        }
        let binder = |id| {
            matches!(
                document.head(id),
                Some("forall" | "exists" | "let" | "choice" | "lambda" | "match")
            )
        };
        let result = match (document.node(a), document.node(b)) {
            _ if binder(a) || binder(b) => None,
            (super::document::Node::List(x), super::document::Node::List(y)) => {
                let (x, y) = (x.clone(), y.clone());
                if document.head(a) == Some("=")
                    && document.head(b) == Some("=")
                    && x.len() == 3
                    && y.len() == 3
                {
                    let straight = both(go(document, x[1], y[1], depth + 1, memo), || {
                        go(document, x[2], y[2], depth + 1, memo)
                    });
                    if straight == Some(true) {
                        Some(true)
                    } else {
                        let flipped = both(go(document, x[1], y[2], depth + 1, memo), || {
                            go(document, x[2], y[1], depth + 1, memo)
                        });
                        match (straight, flipped) {
                            (_, Some(true)) => Some(true),
                            (Some(false), Some(false)) => Some(false),
                            _ => None,
                        }
                    }
                } else if x.len() != y.len() {
                    Some(false)
                } else {
                    let mut result = Some(true);
                    for (&p, &q) in x.iter().zip(&y) {
                        result = both(result, || go(document, p, q, depth + 1, memo));
                        if result == Some(false) {
                            break;
                        }
                    }
                    result
                }
            }
            _ => Some(false),
        };
        memo.insert((a, b), result);
        result
    }
    fn both(first: Option<bool>, second: impl FnOnce() -> Option<bool>) -> Option<bool> {
        match first {
            Some(false) => Some(false),
            Some(true) => second(),
            None => match second() {
                Some(false) => Some(false),
                _ => None,
            },
        }
    }
    go(document, a, b, 0, &mut HashMap::new())
}

/// `assert_polyeq`.
pub(super) fn polyequal(document: &Document, a: u32, b: u32) -> Checked {
    match polyeq(document, a, b) {
        Some(true) => Ok(()),
        Some(false) => refuse(format!(
            "{} and {} differ",
            document.show(a),
            document.show(b)
        )),
        None => undecided("a comparison under a binder is not mirrored"),
    }
}

/// The consumer's `assume`: the term is a problem assertion, or equal to one
/// modulo reordering of equalities (its further n-ary matching is not
/// mirrored, so a miss is `Undetermined`).
pub(super) fn assumption(document: &mut Document, term: u32) -> Checked {
    if document.assertions.contains(&term) {
        return Ok(());
    }
    let assertions = document.assertions.clone();
    if assertions
        .iter()
        .any(|&premise| polyeq(document, term, premise) == Some(true))
    {
        return Ok(());
    }
    undecided("not a problem assertion up to reordering of equalities")
}

pub(super) fn eq_reflexive(document: &mut Document, input: &StepInput) -> Checked {
    let (a, b) = sides(document, input.unit()?)?;
    same(document, a, b)
}

pub(super) fn refl(document: &mut Document, input: &StepInput) -> Checked {
    let (left, right) = sides(document, input.unit()?)?;
    match polyeq(document, left, right) {
        Some(true) => Ok(()),
        _ if input.in_context => undecided("a subproof's context substitution is not mirrored"),
        Some(false) => refuse(format!(
            "{} is not {}",
            document.show(left),
            document.show(right)
        )),
        None => undecided("a comparison under a binder is not mirrored"),
    }
}

/// `find_chain`: the consumer's greedy walk from one side of the conclusion.
fn find_chain(
    document: &Document,
    (mut from, to): (u32, u32),
    premises: &mut [(u32, u32)],
) -> Checked {
    let mut start = 0;
    while from != to {
        let found = premises[start..]
            .iter()
            .position(|&(t, u)| t == from || u == from);
        let Some(offset) = found else {
            return refuse(format!("the chain breaks at {}", document.show(from)));
        };
        let (t, u) = premises[start + offset];
        premises.swap(start, start + offset);
        from = if t == from { u } else { t };
        start += 1;
    }
    Ok(())
}

pub(super) fn eq_transitive(document: &mut Document, input: &StepInput) -> Checked {
    let Some((&last, links)) = input
        .conclusion
        .split_last()
        .filter(|_| input.conclusion.len() >= 3)
    else {
        return refuse("fewer than three literals");
    };
    let conclusion = sides(document, last)?;
    let mut premises = links
        .iter()
        .map(|&link| sides(document, negation(document, link)?))
        .collect::<Result<Vec<_>, _>>()?;
    find_chain(document, conclusion, &mut premises)
}

pub(super) fn trans(document: &mut Document, input: &StepInput) -> Checked {
    let conclusion = sides(document, input.unit()?)?;
    let mut premises = input
        .premises
        .iter()
        .map(|premise| match premise[..] {
            [term] => sides(document, term),
            _ => refuse("a premise is not a unit clause"),
        })
        .collect::<Result<Vec<_>, _>>()?;
    find_chain(document, conclusion, &mut premises)
}

pub(super) fn symm(document: &mut Document, input: &StepInput) -> Checked {
    let (p, q) = sides(document, input.premise_term()?)?;
    let (q2, p2) = sides(document, input.unit()?)?;
    same(document, p, p2)?;
    same(document, q, q2)
}

pub(super) fn not_symm(document: &mut Document, input: &StepInput) -> Checked {
    let (p, q) = sides(document, negation(document, input.premise_term()?)?)?;
    let (q2, p2) = sides(document, negation(document, input.unit()?)?)?;
    same(document, p, p2)?;
    same(document, q, q2)
}

/// An application's head and arguments: the consumer's `Op`, `App` and
/// indexed operator all read as a list whose first element is the head.
/// A binder, `let` or `match` is neither: the consumer refuses it.
fn application(document: &Document, term: u32) -> Option<(u32, Vec<u32>)> {
    if matches!(
        document.head(term),
        Some("forall" | "exists" | "let" | "choice" | "lambda" | "match" | "!")
    ) {
        return None;
    }
    match document.node(term) {
        super::document::Node::List(children) if !children.is_empty() => {
            Some((children[0], children[1..].to_vec()))
        }
        _ => None,
    }
}

/// `check_cong`: premises consumed in order, an argument pair skipped only
/// when equal and the next premise does not justify it.
fn check_cong(premises: &[(u32, u32)], f_args: &[u32], g_args: &[u32]) -> bool {
    let mut next = premises.iter().peekable();
    for (&f, &g) in f_args.iter().zip(g_args) {
        match next.peek() {
            Some(&&(t, u)) if (f, g) == (t, u) || (f, g) == (u, t) => {
                next.next();
            }
            _ if f == g => {}
            _ => return false,
        }
    }
    next.next().is_none()
}

pub(super) fn cong(document: &mut Document, input: &StepInput) -> Checked {
    require(!input.premises.is_empty(), || "no premises".to_string())?;
    let premises = input
        .premises
        .iter()
        .map(|premise| match premise[..] {
            [term] => sides(document, term),
            _ => refuse("a premise is not a unit clause"),
        })
        .collect::<Result<Vec<_>, _>>()?;
    let (f, g) = sides(document, input.unit()?)?;
    if let (Ok(x), Ok(y)) = (shape(document, f, "=", 2), shape(document, g, "=", 2)) {
        let (fx, gx) = ([x[1], x[0]], [y[1], y[0]]);
        let valid = check_cong(&premises, &x, &y)
            || check_cong(&premises, &fx, &y)
            || check_cong(&premises, &x, &gx)
            || check_cong(&premises, &fx, &gx);
        return require(valid, || {
            "the premises do not justify the arguments".to_string()
        });
    }
    let (Some((f_head, f_args)), Some((g_head, g_args))) =
        (application(document, f), application(document, g))
    else {
        return refuse("not two applications");
    };
    require(f_head == g_head, || {
        "different functions or operators".to_string()
    })?;
    require(f_args.len() == g_args.len(), || {
        "different numbers of arguments".to_string()
    })?;
    require(check_cong(&premises, &f_args, &g_args), || {
        "the premises do not justify the arguments".to_string()
    })
}

/// `generic_congruent_rule`: `Op` or `App` only (an indexed operator is
/// refused), one premise per argument, in order, either orientation.
fn congruent(document: &Document, premises: &[u32], (p, q): (u32, u32)) -> Checked {
    let premises = premises
        .iter()
        .map(|&t| sides(document, t))
        .collect::<Result<Vec<_>, _>>()?;
    let (Some((f_head, f_args)), Some((g_head, g_args))) =
        (application(document, p), application(document, q))
    else {
        return refuse("not two applications");
    };
    require(document.atom_text(f_head).is_some(), || {
        "an indexed operator".to_string()
    })?;
    require(f_head == g_head, || {
        "different functions or operators".to_string()
    })?;
    require(f_args.len() == g_args.len(), || {
        "different numbers of arguments".to_string()
    })?;
    require(premises.len() == f_args.len(), || {
        "not one premise per argument".to_string()
    })?;
    for ((t, u), (&f, &g)) in premises.into_iter().zip(f_args.iter().zip(&g_args)) {
        require((f, g) == (t, u) || (f, g) == (u, t), || {
            "a premise does not justify its argument".to_string()
        })?;
    }
    Ok(())
}

pub(super) fn eq_congruent(document: &mut Document, input: &StepInput) -> Checked {
    let Some((&last, links)) = input
        .conclusion
        .split_last()
        .filter(|_| input.conclusion.len() >= 2)
    else {
        return refuse("fewer than two literals");
    };
    let premises = links
        .iter()
        .map(|&l| negation(document, l))
        .collect::<Result<Vec<_>, _>>()?;
    congruent(document, &premises, sides(document, last)?)
}

pub(super) fn eq_congruent_pred(document: &mut Document, input: &StepInput) -> Checked {
    let n = input.conclusion.len();
    require(n >= 3, || "fewer than three literals".to_string())?;
    let premises = input.conclusion[..n - 2]
        .iter()
        .map(|&l| negation(document, l))
        .collect::<Result<Vec<_>, _>>()?;
    let (p, q) = (input.conclusion[n - 2], input.conclusion[n - 1]);
    let pair = match negation(document, p) {
        Ok(p) => (p, q),
        Err(_) => (p, negation(document, q)?),
    };
    congruent(document, &premises, pair)
}

/// `(select (store a i e) j)`: `(a, i, e, j)`.
fn read_over_write(document: &Document, term: u32) -> Result<(u32, u32, u32, u32), Verdict> {
    let select = shape(document, term, "select", 2)?;
    let store = shape(document, select[0], "store", 3)?;
    Ok((store[0], store[1], store[2], select[1]))
}

pub(super) fn arrays_idx(document: &mut Document, input: &StepInput) -> Checked {
    let (left, right) = sides(document, input.unit()?)?;
    let (_, i, e, j) = read_over_write(document, left)?;
    same(document, i, j)?;
    same(document, e, right)
}

pub(super) fn arrays_row(document: &mut Document, input: &StepInput) -> Checked {
    let (ip, jp) = sides(document, negation(document, input.premise_term()?)?)?;
    let (left, right) = sides(document, input.unit()?)?;
    let (a, ic, _, jc) = read_over_write(document, left)?;
    let read = shape(document, right, "select", 2)?;
    same(document, a, read[0])?;
    same(document, jc, read[1])?;
    same(document, ip, ic)?;
    same(document, jp, jc)
}

pub(super) fn arrays_row_contra(document: &mut Document, input: &StepInput) -> Checked {
    let (left, right) = sides(document, negation(document, input.premise_term()?)?)?;
    let (a, ip, _, jp) = read_over_write(document, left)?;
    let read = shape(document, right, "select", 2)?;
    same(document, a, read[0])?;
    same(document, jp, read[1])?;
    let (ic, jc) = sides(document, input.unit()?)?;
    if ip != ic {
        same(document, ip, jc)?;
        same(document, jp, ic)
    } else {
        same(document, jp, jc)
    }
}

/// `subproof`: the closing step's clause is the discharged assumptions,
/// negated, then the previous command's one literal (`false` for `(cl)`).
pub(super) fn subproof(document: &mut Document, input: &StepInput) -> Checked {
    let Some(previous) = &input.previous else {
        return refuse("not the last step of a subproof");
    };
    require(input.conclusion.len() == input.discharge.len() + 1, || {
        format!(
            "{} literals for {} discharged assumptions",
            input.conclusion.len(),
            input.discharge.len()
        )
    })?;
    for (assumption, &literal) in input.discharge.iter().zip(&input.conclusion) {
        let Some(term) = assumption else {
            return refuse("a discharged command is not an assume");
        };
        let literal = negation(document, literal)?;
        polyequal(document, *term, literal)?;
    }
    let phi = match previous[..] {
        [] => document.atom("false"),
        [literal] => literal,
        _ => return refuse("the previous command's clause is not a unit"),
    };
    let last = input.conclusion[input.conclusion.len() - 1];
    polyequal(document, last, phi)
}

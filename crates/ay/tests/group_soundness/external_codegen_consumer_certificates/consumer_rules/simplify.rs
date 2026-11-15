// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The consumer's simplification rules as Clean 7330fa6c has them
//! (`simplification.rs`: `and_simplify`/`or_simplify` WITHOUT the later fix
//! that accepts `(= (and true (and p q)) (and p q))`, `ite_simplify`,
//! `equiv_simplify`) and `ite_intro` (`tautology.rs`).

use super::document::Document;
use super::equality::polyeq;
use super::{nary, refuse, require, shape, undecided, Checked, StepInput};

/// `generic_and_or_simplify`, read over the expanded terms: drop the identity
/// operands, then duplicates, then look for a short circuit, and compare
/// what survives with the ARGUMENTS of the result when the result is an
/// application of the same connective.
fn and_or(document: &mut Document, input: &StepInput, gate: &str) -> Checked {
    let sides = shape(document, input.unit()?, "=", 2)?;
    let (left, right) = (sides[0], sides[1]);
    let (skip, short) = if gate == "and" {
        ("true", "false")
    } else {
        ("false", "true")
    };
    let mut phis = nary(document, left, gate)?;
    if let [only] = phis[..] {
        if document.head(only) == Some(gate) {
            phis = document.args(only);
        }
    }
    let result_args = if document.head(right) == Some(gate) {
        document.args(right)
    } else {
        vec![right]
    };
    phis.retain(|&phi| !document.is_atom(phi, skip));
    if result_args == phis {
        return Ok(());
    }
    let mut seen = Vec::new();
    phis.retain(|&phi| {
        let fresh = !seen.contains(&phi);
        seen.push(phi);
        fresh
    });
    if result_args == phis {
        return Ok(());
    }
    let strip = |document: &Document, mut term: u32| {
        let mut polarity = true;
        while let Some([inner]) = document.op(term, "not").as_deref() {
            term = *inner;
            polarity = !polarity;
        }
        (polarity, term)
    };
    let stripped: Vec<(bool, u32)> = phis.iter().map(|&phi| strip(document, phi)).collect();
    for &phi in &phis {
        let (polarity, inner) = strip(document, phi);
        if stripped.contains(&(!polarity, inner)) || document.is_atom(phi, short) {
            let short_circuited =
                matches!(result_args[..], [only] if document.is_atom(only, short));
            return require(short_circuited, || {
                format!("short-circuited to {short}, not {}", document.show(right))
            });
        }
    }
    if phis.is_empty() {
        let empty = matches!(result_args[..], [only] if document.is_atom(only, skip));
        return require(empty, || {
            format!("an empty {gate} is {skip}, not {}", document.show(right))
        });
    }
    refuse(format!(
        "the surviving operands of the {gate} are not {}",
        document.show(right)
    ))
}

pub(super) fn and_simplify(document: &mut Document, input: &StepInput) -> Checked {
    and_or(document, input, "and")
}

pub(super) fn or_simplify(document: &mut Document, input: &StepInput) -> Checked {
    and_or(document, input, "or")
}

/// `generic_simplify_rule`: rewrite the root until it is the other side or a
/// fixed point (a cycle refuses), from either side.
fn fixed_point(
    document: &mut Document,
    input: &StepInput,
    rewrite: fn(&mut Document, u32) -> Option<u32>,
) -> Checked {
    let sides = shape(document, input.unit()?, "=", 2)?;
    let (left, right) = (sides[0], sides[1]);
    let run =
        |document: &mut Document, mut current: u32, goal: u32| -> Result<u32, super::Verdict> {
            let mut seen = std::collections::HashSet::new();
            loop {
                if !seen.insert(current) {
                    return refuse("a cycle in the simplification");
                }
                match rewrite(document, current) {
                    Some(next) if next == goal => return Ok(next),
                    Some(next) => current = next,
                    None => return Ok(current),
                }
            }
        };
    if run(document, left, right)? == right {
        return Ok(());
    }
    let back = run(document, right, left)?;
    require(back == left, || {
        format!(
            "{} does not simplify to {}",
            document.show(left),
            document.show(right)
        )
    })
}

/// One `ite_simplify` rewrite at the root, the first pattern that matches.
fn ite_rewrite(document: &mut Document, term: u32) -> Option<u32> {
    let [phi, t1, t2] = <[u32; 3]>::try_from(document.op(term, "ite")?).ok()?;
    let is = |document: &Document, id: u32, text: &str| document.is_atom(id, text);
    let ite_of = |document: &Document, id: u32| -> Option<[u32; 3]> {
        <[u32; 3]>::try_from(document.op(id, "ite")?).ok()
    };
    Some(if is(document, phi, "true") {
        t1
    } else if is(document, phi, "false") {
        t2
    } else if t1 == t2 {
        t1
    } else if is(document, t1, "true") && is(document, t2, "false") {
        phi
    } else if is(document, t1, "false") && is(document, t2, "true") {
        document.app("not", &[phi])
    } else if let Some([inner]) = document
        .op(phi, "not")
        .and_then(|a| <[u32; 1]>::try_from(a).ok())
    {
        document.app("ite", &[inner, t2, t1])
    } else if let Some([p, a, _]) = ite_of(document, t1).filter(|[p, _, _]| *p == phi) {
        document.app("ite", &[p, a, t2])
    } else if let Some([p, _, c]) = ite_of(document, t2).filter(|[p, _, _]| *p == phi) {
        document.app("ite", &[p, t1, c])
    } else if is(document, t1, "true") {
        document.app("or", &[phi, t2])
    } else if is(document, t2, "false") {
        document.app("and", &[phi, t1])
    } else if is(document, t1, "false") {
        let not_phi = document.app("not", &[phi]);
        document.app("and", &[not_phi, t2])
    } else if is(document, t2, "true") {
        let not_phi = document.app("not", &[phi]);
        document.app("or", &[not_phi, t1])
    } else {
        return None;
    })
}

pub(super) fn ite_simplify(document: &mut Document, input: &StepInput) -> Checked {
    fixed_point(document, input, ite_rewrite)
}

/// One `equiv_simplify` rewrite at the root, the first pattern that matches.
fn equiv_rewrite(document: &mut Document, term: u32) -> Option<u32> {
    let [a, b] = <[u32; 2]>::try_from(document.op(term, "=")?).ok()?;
    let not = |document: &Document, id: u32| -> Option<u32> {
        let operands = document.op(id, "not")?;
        (operands.len() == 1).then(|| operands[0])
    };
    Some(match (not(document, a), not(document, b)) {
        (Some(p), Some(q)) => document.app("=", &[p, q]),
        _ if a == b => document.atom("true"),
        (None, Some(q)) if a == q => document.atom("false"),
        (Some(p), None) if p == b => document.atom("false"),
        _ if document.is_atom(a, "true") => b,
        _ if document.is_atom(b, "true") => a,
        _ if document.is_atom(a, "false") => document.app("not", &[b]),
        _ if document.is_atom(b, "false") => document.app("not", &[a]),
        _ => return None,
    })
}

pub(super) fn equiv_simplify(document: &mut Document, input: &StepInput) -> Checked {
    fixed_point(document, input, equiv_rewrite)
}

/// `polyeq`, decided: `Ok(false)` when the terms differ.
fn equivalent(document: &Document, a: u32, b: u32) -> Result<bool, super::Verdict> {
    polyeq(document, a, b).map_or_else(
        || undecided("a comparison under a binder is not mirrored"),
        Ok,
    )
}

pub(super) fn ite_intro(document: &mut Document, input: &StepInput) -> Checked {
    let sides = shape(document, input.unit()?, "=", 2)?;
    let (root, right) = (sides[0], sides[1]);
    if equivalent(document, root, right)? {
        return Ok(());
    }
    let us = nary(document, right, "and")?;
    let Some((&first, rest)) = us.split_first() else {
        return refuse("an empty conjunction");
    };
    require(equivalent(document, first, root)?, || {
        "the conjunction does not start with the term".to_string()
    })?;
    for &u in rest {
        let [cond, first_eq, second_eq] =
            <[u32; 3]>::try_from(shape(document, u, "ite", 3)?).unwrap_or([0; 3]);
        let (x, y) = (
            shape(document, first_eq, "=", 2)?,
            shape(document, second_eq, "=", 2)?,
        );
        let valid = |document: &Document,
                     r1: u32,
                     s1: u32,
                     r2: u32,
                     s2: u32|
         -> Result<bool, super::Verdict> {
            if !equivalent(document, s1, s2)? {
                return Ok(false);
            }
            let Some([c, b, e]) = document
                .op(s1, "ite")
                .and_then(|args| <[u32; 3]>::try_from(args).ok())
            else {
                return Ok(false);
            };
            Ok(equivalent(document, c, cond)?
                && equivalent(document, b, r1)?
                && equivalent(document, e, r2)?)
        };
        let (a, b, c, d) = (x[0], x[1], y[0], y[1]);
        let ok = valid(document, a, b, c, d)?
            || valid(document, b, a, c, d)?
            || valid(document, a, b, d, c)?
            || valid(document, b, a, d, c)?;
        require(ok, || {
            format!("{} is not a valid ite_intro conjunct", document.show(u))
        })?;
    }
    Ok(())
}

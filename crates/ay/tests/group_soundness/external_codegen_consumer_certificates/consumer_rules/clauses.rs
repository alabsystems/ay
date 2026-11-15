// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The consumer's tautology and clausification rules (Clean's Carcara
//! `tautology.rs`, `clausification.rs`) and `contraction`: each matches one
//! term against a connective's shape and compares the clause's literals with
//! its operands, negated where the rule says so.

use std::collections::HashMap;

use super::document::Document;
use super::{nary, negation, refuse, require, same, shape, Checked, StepInput};

/// A rule of the form: the term (the first literal, or the one premise's
/// term) is `(op a1 … an)`, negated when `negated`; the remaining literals
/// are, in order, `a_index`, negated when their flag says so.
struct Shape {
    from_premise: bool,
    negated: bool,
    op: &'static str,
    arity: usize,
    literals: &'static [(usize, bool)],
}

fn check(document: &mut Document, input: &StepInput, rule: &Shape) -> Checked {
    let (term, rest) = if rule.from_premise {
        (input.premise_term()?, &input.conclusion[..])
    } else {
        match input.conclusion.split_first() {
            Some((&first, rest)) => (first, rest),
            None => return refuse("an empty clause"),
        }
    };
    require(rest.len() == rule.literals.len(), || {
        format!(
            "{} literals, not {}",
            input.conclusion.len(),
            rule.literals.len()
        )
    })?;
    let term = if rule.negated {
        negation(document, term)?
    } else {
        term
    };
    let operands = shape(document, term, rule.op, rule.arity)?;
    for (&(index, negated), &literal) in rule.literals.iter().zip(rest) {
        let literal = if negated {
            negation(document, literal)?
        } else {
            literal
        };
        same(document, operands[index], literal)?;
    }
    Ok(())
}

macro_rules! shaped {
    ($($name:ident: $premise:expr, $negated:expr, $op:expr, $arity:expr, $literals:expr;)*) => {$(
        pub(super) fn $name(document: &mut Document, input: &StepInput) -> Checked {
            check(document, input, &Shape {
                from_premise: $premise,
                negated: $negated,
                op: $op,
                arity: $arity,
                literals: &$literals,
            })
        }
    )*};
}

// (literal index into the operands, whether the literal is that operand negated)
shaped! {
    xor_pos1: false, true, "xor", 2, [(0, false), (1, false)];
    xor_pos2: false, true, "xor", 2, [(0, true), (1, true)];
    xor_neg1: false, false, "xor", 2, [(0, false), (1, true)];
    xor_neg2: false, false, "xor", 2, [(0, true), (1, false)];
    implies_pos: false, true, "=>", 2, [(0, true), (1, false)];
    implies_neg1: false, false, "=>", 2, [(0, false)];
    implies_neg2: false, false, "=>", 2, [(1, true)];
    equiv_pos1: false, true, "=", 2, [(0, false), (1, true)];
    equiv_pos2: false, true, "=", 2, [(0, true), (1, false)];
    equiv_neg1: false, false, "=", 2, [(0, true), (1, true)];
    equiv_neg2: false, false, "=", 2, [(0, false), (1, false)];
    ite_pos1: false, true, "ite", 3, [(0, false), (2, false)];
    ite_pos2: false, true, "ite", 3, [(0, true), (1, false)];
    ite_neg1: false, false, "ite", 3, [(0, false), (2, true)];
    ite_neg2: false, false, "ite", 3, [(0, true), (1, true)];
    equiv1: true, false, "=", 2, [(0, true), (1, false)];
    equiv2: true, false, "=", 2, [(0, false), (1, true)];
    not_equiv1: true, true, "=", 2, [(0, false), (1, false)];
    not_equiv2: true, true, "=", 2, [(0, true), (1, true)];
    ite1: true, false, "ite", 3, [(0, false), (2, false)];
    ite2: true, false, "ite", 3, [(0, true), (1, false)];
    not_ite1: true, true, "ite", 3, [(0, false), (2, true)];
    not_ite2: true, true, "ite", 3, [(0, true), (1, true)];
    xor1: true, false, "xor", 2, [(0, false), (1, false)];
    xor2: true, false, "xor", 2, [(0, true), (1, true)];
    not_xor1: true, true, "xor", 2, [(0, false), (1, true)];
    not_xor2: true, true, "xor", 2, [(0, true), (1, false)];
    implies: true, false, "=>", 2, [(0, true), (1, false)];
    not_implies1: true, true, "=>", 2, [(0, false)];
    not_implies2: true, true, "=>", 2, [(1, true)];
}

pub(super) fn r#true(document: &mut Document, input: &StepInput) -> Checked {
    let literal = input.unit()?;
    require(document.is_atom(literal, "true"), || {
        "the literal is not true".to_string()
    })
}

pub(super) fn r#false(document: &mut Document, input: &StepInput) -> Checked {
    let literal = negation(document, input.unit()?)?;
    require(document.is_atom(literal, "false"), || {
        "the literal is not (not false)".to_string()
    })
}

pub(super) fn not_not(document: &mut Document, input: &StepInput) -> Checked {
    let [first, second] = input.conclusion[..] else {
        return refuse("not two literals");
    };
    let mut inner = first;
    for _ in 0..3 {
        inner = negation(document, inner)?;
    }
    same(document, inner, second)
}

/// The operands of the first literal `(op …)` (negated when `negated`), which
/// must number `count` when given.
fn first_operands(
    document: &Document,
    input: &StepInput,
    negated: bool,
    op: &str,
    count: Option<usize>,
) -> Result<Vec<u32>, super::Verdict> {
    let Some(&first) = input.conclusion.first() else {
        return refuse("an empty clause");
    };
    let term = if negated {
        negation(document, first)?
    } else {
        first
    };
    let operands = nary(document, term, op)?;
    if let Some(count) = count {
        require(operands.len() == count, || {
            format!("{op} of {} operands, not {count}", operands.len())
        })?;
    }
    Ok(operands)
}

/// The `index` argument's operand, or the consumer's refusal.
fn operand(operands: &[u32], index: usize) -> Result<u32, super::Verdict> {
    operands
        .get(index)
        .copied()
        .map_or_else(|| refuse(format!("no operand {index}")), Ok)
}

pub(super) fn and_pos(document: &mut Document, input: &StepInput) -> Checked {
    require(input.conclusion.len() == 2, || {
        "not two literals".to_string()
    })?;
    let index = input.index(document)?;
    let operands = first_operands(document, input, true, "and", None)?;
    same(document, input.conclusion[1], operand(&operands, index)?)
}

pub(super) fn or_neg(document: &mut Document, input: &StepInput) -> Checked {
    require(input.conclusion.len() == 2, || {
        "not two literals".to_string()
    })?;
    let index = input.index(document)?;
    let operands = first_operands(document, input, false, "or", None)?;
    let other = negation(document, input.conclusion[1])?;
    same(document, other, operand(&operands, index)?)
}

/// `and_neg` (negated literals) and `or_pos`.
fn spread(
    document: &mut Document,
    input: &StepInput,
    negated: bool,
    op: &str,
    negated_literals: bool,
) -> Checked {
    let rest = input.conclusion.len().checked_sub(1).filter(|&n| n >= 1);
    let Some(rest) = rest else {
        return refuse("fewer than two literals");
    };
    let operands = first_operands(document, input, negated, op, Some(rest))?;
    for (&operand, &literal) in operands.iter().zip(&input.conclusion[1..]) {
        let literal = if negated_literals {
            negation(document, literal)?
        } else {
            literal
        };
        same(document, operand, literal)?;
    }
    Ok(())
}

pub(super) fn and_neg(document: &mut Document, input: &StepInput) -> Checked {
    spread(document, input, false, "and", true)
}

pub(super) fn or_pos(document: &mut Document, input: &StepInput) -> Checked {
    spread(document, input, true, "or", false)
}

/// Clausification of the one premise `(op …)` (negated when `negated`).
fn premise_operands(
    document: &Document,
    input: &StepInput,
    negated: bool,
    op: &str,
) -> Result<Vec<u32>, super::Verdict> {
    let term = input.premise_term()?;
    let term = if negated {
        negation(document, term)?
    } else {
        term
    };
    nary(document, term, op)
}

pub(super) fn and(document: &mut Document, input: &StepInput) -> Checked {
    let index = input.index(document)?;
    let literal = input.unit()?;
    let operands = premise_operands(document, input, false, "and")?;
    same(document, literal, operand(&operands, index)?)
}

pub(super) fn not_or(document: &mut Document, input: &StepInput) -> Checked {
    let index = input.index(document)?;
    let literal = negation(document, input.unit()?)?;
    let operands = premise_operands(document, input, true, "or")?;
    same(document, literal, operand(&operands, index)?)
}

/// `or` and `not_and`: one literal per operand.
fn split(document: &mut Document, input: &StepInput, negated: bool, op: &str) -> Checked {
    let operands = premise_operands(document, input, negated, op)?;
    require(input.conclusion.len() == operands.len(), || {
        format!(
            "{} literals, not {}",
            input.conclusion.len(),
            operands.len()
        )
    })?;
    for (&operand, &literal) in operands.iter().zip(&input.conclusion) {
        let literal = if negated {
            negation(document, literal)?
        } else {
            literal
        };
        same(document, operand, literal)?;
    }
    Ok(())
}

pub(super) fn or(document: &mut Document, input: &StepInput) -> Checked {
    split(document, input, false, "or")
}

pub(super) fn not_and(document: &mut Document, input: &StepInput) -> Checked {
    split(document, input, true, "and")
}

/// The same literals as the one premise, each at most as often and at least once.
pub(super) fn contraction(_: &mut Document, input: &StepInput) -> Checked {
    let [premise] = &input.premises[..] else {
        return refuse(format!("{} premises, not one", input.premises.len()));
    };
    let count = |clause: &[u32]| {
        let mut counts: HashMap<u32, usize> = HashMap::new();
        for &literal in clause {
            *counts.entry(literal).or_default() += 1;
        }
        counts
    };
    let (premise, conclusion) = (count(premise), count(&input.conclusion));
    for (literal, &times) in &premise {
        let got = conclusion.get(literal).copied().unwrap_or(0);
        require(got != 0 && got <= times, || {
            "a literal is missing or repeated".to_string()
        })?;
    }
    for (literal, &times) in &conclusion {
        let had = premise.get(literal).copied().unwrap_or(0);
        require(had >= times, || "an extra literal".to_string())?;
    }
    Ok(())
}

/// `reordering`: the one premise's literals, as a multiset, in any order.
pub(super) fn reordering(_: &mut Document, input: &StepInput) -> Checked {
    let [premise] = &input.premises[..] else {
        return refuse(format!("{} premises, not one", input.premises.len()));
    };
    let count = |clause: &[u32]| {
        let mut counts: HashMap<u32, usize> = HashMap::new();
        for &literal in clause {
            *counts.entry(literal).or_default() += 1;
        }
        counts
    };
    require(
        premise.len() == input.conclusion.len() && count(premise) == count(&input.conclusion),
        || "not a reordering of the premise".to_string(),
    )
}

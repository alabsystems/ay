// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! One-step mirrors of pinned carcara's Boolean simplification rules
//! (`carcara/src/checker/rules/simplification.rs`, `clausification.rs`,
//! `tautology.rs` at git `9a352ee`), read over printed text. See the parent
//! module for the contract each mirror keeps.

use super::super::super::split_alethe_application_bounded;
use super::super::super::surface_literal::same_printed_term;
use super::super::split_application;
use super::super::{MAX_EQUIVALENCE_BYTES, MAX_EQUIVALENCE_NODES};

pub(super) const TRUE: &str = "true";
pub(super) const FALSE: &str = "false";

/// One printed rewrite rule, spelled literally so the wire-rule inventory
/// reads every name this module can emit off this table.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum FoldRule {
    AndSimplify,
    OrSimplify,
    NotSimplify,
    EqSimplify,
    EquivSimplify,
    IteSimplify,
    ImpliesSimplify,
    DistinctElim,
    ConnectiveDef,
}

impl FoldRule {
    /// The premise-free step concluding `(= from to)`.
    pub(super) fn step(self, id: &str, from: &str, to: &str) -> String {
        let clause = format!("(cl (= {from} {to}))");
        match self {
            Self::AndSimplify => format!("(step {id} {clause} :rule and_simplify)"),
            Self::OrSimplify => format!("(step {id} {clause} :rule or_simplify)"),
            Self::NotSimplify => format!("(step {id} {clause} :rule not_simplify)"),
            Self::EqSimplify => format!("(step {id} {clause} :rule eq_simplify)"),
            Self::EquivSimplify => format!("(step {id} {clause} :rule equiv_simplify)"),
            Self::IteSimplify => format!("(step {id} {clause} :rule ite_simplify)"),
            Self::ImpliesSimplify => format!("(step {id} {clause} :rule implies_simplify)"),
            Self::DistinctElim => format!("(step {id} {clause} :rule distinct_elim)"),
            Self::ConnectiveDef => format!("(step {id} {clause} :rule connective_def)"),
        }
    }

    /// Whether the rewrite removes structure. `distinct_elim` and
    /// `connective_def` only re-spell a connective.
    pub(super) fn folds(self) -> bool {
        !matches!(self, Self::DistinctElim | Self::ConnectiveDef)
    }
}

/// The one operand of a printed `(not x)`.
pub(super) fn negation_operand(text: &str) -> Option<String> {
    negation_operand_borrowed(text).map(str::to_string)
}

fn negation_operand_borrowed(text: &str) -> Option<&str> {
    let operands = split_alethe_application_bounded(text, "not", 1, MAX_EQUIVALENCE_BYTES).ok()?;
    match operands.as_slice() {
        [operand] => Some(*operand),
        _ => None,
    }
}

/// One `and_simplify` (`conjunction`) or `or_simplify` result exactly as
/// carcara's `generic_and_or_simplify` accepts it, or `None` when the rule
/// changes nothing or carcara could not state the result.
pub(super) fn and_or_simplify(operands: &[String], conjunction: bool) -> Option<String> {
    and_or_simplify_with_progress(operands, conjunction, &mut |_| true)
}

fn same_with_progress(
    left: &str,
    right: &str,
    progress: &mut dyn FnMut(u64) -> bool,
) -> Option<bool> {
    // The existing literal-spelling matcher traverses at most depth 64 and
    // copies token text at each level. Charge before calling that matcher.
    let bytes = left.len().checked_add(right.len())?.checked_mul(64)?;
    progress(u64::try_from(bytes).ok()?).then(|| same_printed_term(left, right))
}

fn polarity_with_progress<'a>(
    text: &'a str,
    progress: &mut dyn FnMut(u64) -> bool,
) -> Option<(bool, &'a str)> {
    let mut positive = true;
    let mut current = text;
    loop {
        if !progress(u64::try_from(current.len()).ok()?) {
            return None;
        }
        let Some(inner) = negation_operand_borrowed(current) else {
            break;
        };
        positive = !positive;
        current = inner;
    }
    Some((positive, current))
}

/// The legacy application guard copies its parsed fields. Admit a conservative
/// scan, field-storage, and copied-text bound before invoking that same parser.
fn owned_application_present_with_progress(
    text: &str,
    head: &str,
    progress: &mut dyn FnMut(u64) -> bool,
) -> Option<bool> {
    let charge = text.len().checked_mul(64)?.checked_add(64)?;
    if !progress(u64::try_from(charge).ok()?) {
        return None;
    }
    Some(split_application(text, head).is_some())
}

fn and_or_simplify_with_progress(
    operands: &[String],
    conjunction: bool,
    progress: &mut dyn FnMut(u64) -> bool,
) -> Option<String> {
    let (head, neutral, absorbing) = if conjunction {
        ("and", TRUE, FALSE)
    } else {
        ("or", FALSE, TRUE)
    };
    if operands.is_empty()
        || operands.len() > MAX_EQUIVALENCE_NODES
        || !progress(operands.len() as u64)
    {
        return None;
    }
    // carcara unwraps a unary application of the rule's own operator.
    if operands.len() == 1 && owned_application_present_with_progress(&operands[0], head, progress)?
    {
        return None;
    }
    let mut survivors: Vec<&String> = Vec::with_capacity(operands.len());
    for operand in operands {
        if !progress(operand.len() as u64) {
            return None;
        }
        if operand == neutral {
            continue;
        }
        let mut repeated = false;
        for kept in &survivors {
            if same_with_progress(kept, operand, progress)? {
                repeated = true;
                break;
            }
        }
        if !repeated {
            survivors.push(operand);
        }
    }
    let signed = survivors
        .iter()
        .map(|term| polarity_with_progress(term, progress))
        .collect::<Option<Vec<_>>>()?;
    let mut short_circuits = false;
    for (term, (positive, inner)) in survivors.iter().zip(&signed) {
        if term.as_str() == absorbing {
            short_circuits = true;
            break;
        }
        for (other, text) in &signed {
            if *other != *positive && same_with_progress(text, inner, progress)? {
                short_circuits = true;
                break;
            }
        }
        if short_circuits {
            break;
        }
    }
    // A unary application is still rewritten to its one operand.
    if !short_circuits && survivors.len() == operands.len() && operands.len() > 1 {
        return None;
    }
    let output_bound = operands
        .iter()
        .try_fold(16usize, |sum, text| sum.checked_add(text.len() + 1))?;
    if !progress(u64::try_from(output_bound).ok()?) {
        return None;
    }
    Some(if short_circuits {
        absorbing.to_string()
    } else if survivors.is_empty() {
        neutral.to_string()
    } else if let [only] = survivors.as_slice() {
        if owned_application_present_with_progress(only, head, progress)? {
            return None;
        }
        (*only).clone()
    } else {
        let joined: Vec<&str> = survivors.iter().map(|survivor| survivor.as_str()).collect();
        format!("({head} {})", joined.join(" "))
    })
}

/// `not_simplify`'s first matching pattern.
pub(super) fn not_simplify(operand: &str) -> Option<String> {
    if let Some(inner) = negation_operand(operand) {
        return Some(inner);
    }
    match operand {
        FALSE => Some(TRUE.to_string()),
        TRUE => Some(FALSE.to_string()),
        _ => None,
    }
}

/// The same first-matching rule, under a shared pre-debit/poll callback.
pub(super) fn top_rewrite_with_progress(
    head: &str,
    operands: &[String],
    progress: &mut dyn FnMut(u64) -> bool,
) -> Option<(FoldRule, String)> {
    if operands.len() > MAX_EQUIVALENCE_NODES {
        return None;
    }
    match head {
        "and" => {
            return and_or_simplify_with_progress(operands, true, progress)
                .map(|text| (FoldRule::AndSimplify, text))
        }
        "or" => {
            return and_or_simplify_with_progress(operands, false, progress)
                .map(|text| (FoldRule::OrSimplify, text))
        }
        _ => {}
    }
    // Non-variadic rules perform a fixed number of bounded spelling scans and
    // copies. Keep their exact first-match order in the existing mirror.
    let bytes = operands
        .iter()
        .try_fold(0usize, |sum, text| sum.checked_add(text.len()))?;
    let charge = bytes.checked_mul(256)?.checked_add(256)?;
    if !progress(u64::try_from(charge).ok()?) {
        return None;
    }
    top_rewrite(head, operands)
}

/// A binary equality: `eq_simplify` for the reflexive pattern, otherwise
/// `equiv_simplify`'s first matching pattern in carcara's order.
pub(super) fn equality_simplify(left: &str, right: &str) -> Option<(FoldRule, String)> {
    if same_printed_term(left, right) {
        return Some((FoldRule::EqSimplify, TRUE.to_string()));
    }
    let (left_inner, right_inner) = (negation_operand(left), negation_operand(right));
    let rewrite = if let (Some(l), Some(r)) = (&left_inner, &right_inner) {
        format!("(= {l} {r})")
    } else if right_inner
        .as_deref()
        .is_some_and(|inner| same_printed_term(left, inner))
        || left_inner
            .as_deref()
            .is_some_and(|inner| same_printed_term(inner, right))
    {
        FALSE.to_string()
    } else if left == TRUE {
        right.to_string()
    } else if right == TRUE {
        left.to_string()
    } else if left == FALSE {
        format!("(not {right})")
    } else if right == FALSE {
        format!("(not {left})")
    } else {
        return None;
    };
    Some((FoldRule::EquivSimplify, rewrite))
}

/// `ite_simplify`'s first matching pattern, or `None` when none matches or
/// the first match is a nested-condition pattern this mirror does not
/// reproduce.
pub(super) fn ite_simplify(
    condition: &str,
    then_branch: &str,
    else_branch: &str,
) -> Option<String> {
    if condition == TRUE {
        return Some(then_branch.to_string());
    }
    if condition == FALSE {
        return Some(else_branch.to_string());
    }
    if same_printed_term(then_branch, else_branch) {
        return Some(then_branch.to_string());
    }
    if then_branch == TRUE && else_branch == FALSE {
        return Some(condition.to_string());
    }
    if then_branch == FALSE && else_branch == TRUE {
        return Some(format!("(not {condition})"));
    }
    if let Some(positive) = negation_operand(condition) {
        return Some(format!("(ite {positive} {else_branch} {then_branch})"));
    }
    let nested_same_condition = |branch: &str| {
        split_application(branch, "ite").is_some_and(|operands| {
            operands.len() == 3 && same_printed_term(&operands[0], condition)
        })
    };
    if nested_same_condition(then_branch) || nested_same_condition(else_branch) {
        return None;
    }
    if then_branch == TRUE {
        return Some(format!("(or {condition} {else_branch})"));
    }
    if else_branch == FALSE {
        return Some(format!("(and {condition} {then_branch})"));
    }
    if then_branch == FALSE {
        return Some(format!("(and (not {condition}) {else_branch})"));
    }
    if else_branch == TRUE {
        return Some(format!("(or (not {condition}) {then_branch})"));
    }
    None
}

/// `implies_simplify`'s first matching pattern.
pub(super) fn implies_simplify(antecedent: &str, consequent: &str) -> Option<String> {
    if let (Some(a), Some(c)) = (negation_operand(antecedent), negation_operand(consequent)) {
        return Some(format!("(=> {c} {a})"));
    }
    if antecedent == FALSE || consequent == TRUE {
        return Some(TRUE.to_string());
    }
    if antecedent == TRUE {
        return Some(consequent.to_string());
    }
    if consequent == FALSE {
        return Some(format!("(not {antecedent})"));
    }
    if same_printed_term(antecedent, consequent) {
        return Some(TRUE.to_string());
    }
    let complementary = negation_operand(antecedent)
        .is_some_and(|inner| same_printed_term(&inner, consequent))
        || negation_operand(consequent).is_some_and(|inner| same_printed_term(&inner, antecedent));
    if complementary {
        return Some(consequent.to_string());
    }
    if split_application(antecedent, "=>")
        .is_some_and(|operands| operands.len() == 2 && same_printed_term(&operands[1], consequent))
    {
        // `(=> (=> a b) b)` -> `(or a b)`: a re-spelling this mirror leaves
        // alone. carcara would take this pattern, so nothing is emitted.
        return None;
    }
    None
}

/// The connectives the fold descends through and rewrites. Everything else
/// (theory atoms, uninterpreted applications, annotations) is a leaf.
pub(super) const FOLD_CONNECTIVES: [&str; 8] =
    ["not", "and", "or", "xor", "=", "distinct", "ite", "=>"];

/// The one-step rewrite of a node whose operands are already folded.
pub(super) fn top_rewrite(head: &str, operands: &[String]) -> Option<(FoldRule, String)> {
    match (head, operands) {
        ("not", [operand]) => not_simplify(operand).map(|text| (FoldRule::NotSimplify, text)),
        ("and", _) => and_or_simplify(operands, true).map(|text| (FoldRule::AndSimplify, text)),
        ("or", _) => and_or_simplify(operands, false).map(|text| (FoldRule::OrSimplify, text)),
        ("=", [left, right]) => equality_simplify(left, right),
        ("ite", [condition, then_branch, else_branch]) => {
            ite_simplify(condition, then_branch, else_branch)
                .map(|text| (FoldRule::IteSimplify, text))
        }
        ("=>", [antecedent, consequent]) => {
            implies_simplify(antecedent, consequent).map(|text| (FoldRule::ImpliesSimplify, text))
        }
        ("distinct", [left, right]) => {
            Some((FoldRule::DistinctElim, format!("(not (= {left} {right}))")))
        }
        ("xor", [left, right])
            if [TRUE, FALSE].contains(&left.as_str())
                || [TRUE, FALSE].contains(&right.as_str())
                || same_printed_term(left, right) =>
        {
            Some((
                FoldRule::ConnectiveDef,
                format!("(or (and (not {left}) {right}) (and {left} (not {right})))"),
            ))
        }
        _ => None,
    }
}

#[cfg(test)]
#[path = "mirror_admission_tests.rs"]
mod admission_tests;

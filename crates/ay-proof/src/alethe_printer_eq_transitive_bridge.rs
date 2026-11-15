// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Checked repair of an `eq_transitive` chain broken only by the SPELLING of
//! closed bit-vector terms.
//!
//! AY folds closed bit-vector terms while it elaborates the problem
//! (`(concat #x00 (concat c d))` becomes one 136-bit constant, `(bvadd 63 1)`
//! becomes `64`), then the authored-surface channel prints each assertion back
//! in the problem's own spelling so its `assume` matches the premise. A
//! transitivity chain AY derived over the folded terms can therefore print as
//! two links that meet at different spellings of one value:
//!
//! ```text
//! (not (= low0 (concat (_ bv0 8) (concat (_ bv9223372036854775811 64) (_ bv9 64)))))
//! (not (= high1 (_ bv170141183460469231787027535937012760585 136)))
//! (= low0 high1)
//! ```
//!
//! Pinned carcara answers `broken transitivity chain` for that text, so the
//! printer used to ship the step as a `hole`. This module instead proves each
//! missing link over the printed text and closes the chain with checked rules:
//!
//! ```text
//! (step t4.gb0 (cl (= (concat ..) (_ bv1701..585 136))) :rule evaluate)
//! (step t4.gb.et (cl (not (= low0 (concat ..))) (not (= (concat ..) (_ bv1701..585 136)))
//!                    (not (= high1 (_ bv1701..585 136))) (= low0 high1)) :rule eq_transitive)
//! (step t4 (cl <the clause exactly as printed>) :rule resolution :premises (t4.gb.et t4.gb0))
//! ```
//!
//! A link between two applications of the same plain function symbol is
//! proved argumentwise with `cong` (for `(select b (bvadd 63 1))` against
//! `(select b #x..40)` under `fld_len`/`fld_vec`), bottoming out in `evaluate`.
//!
//! The same planner joins an authored same-index READ-OVER-WRITE to the
//! element it reads with `arrays_idx` ([`read_over_write`]), and offers its
//! links to the printed-resolution pivot bridge ([`bridged_printed_equality`]).
//!
//! Every inference is independently re-checked by carcara; nothing here is
//! trusted. The planner only decides WHICH derivation to print, and it
//! declines (leaving the honest `hole`) unless:
//!
//! * both endpoints of an `evaluate` link are closed terms over the operators
//!   below and AY's own exact evaluation gives them the same value and width;
//! * a `cong` link joins two applications of the same plain symbol;
//! * the assembled chain passes [`printed_eq_transitive_chain_holds`], the
//!   replay of carcara's own greedy `find_chain`.
//!
//! The operator set is deliberately small. Pinned carcara 1.1.0 (git 9a352ee)
//! evaluates every SIGNED operation wrongly for a negative operand
//! (`Value::as_signed_bitvec` returns `2^w - v`, the magnitude), which also
//! breaks its `bvsub`, and its `(_ extract i j)` keeps one bit too few. An
//! `evaluate` step over any of those would be refused (or, worse, a wrong one
//! accepted), so they are not evaluated here. What remains — `concat`,
//! `bvadd`, `bvmul`, `bvand`, `bvor`, `bvxor`, `bvnot`, `bvneg` and
//! `(_ zero_extend k)` over literals — carcara computes modulo `2^w` exactly
//! as SMT-LIB defines it.

use super::{
    printed_eq_transitive_chain_holds, split_printed_equality, split_printed_negation,
    MAX_CHAIN_LITERALS, MAX_CHAIN_TERM_BYTES,
};
use crate::alethe_printer::surface_literal::equal_modulo_bitvec_literal_spelling;
use crate::alethe_printer::surface_tokens::split_smt_term_slices_bounded;
use crate::alethe_printer::{parse_printed_bitvec_literal, split_alethe_application_bounded};
pub(in crate::alethe_printer) use emit::bridged_printed_equality;
use emit::Emitter;
use num_bigint::BigUint;
use read_over_write::plan_read_over_write;
use std::fmt::Write as _;

#[path = "alethe_printer_eq_transitive_bridge_emit.rs"]
mod emit;
#[path = "alethe_printer_eq_transitive_bridge_row.rs"]
mod read_over_write;

/// Widest closed bit-vector value the planner evaluates.
const MAX_BRIDGE_WIDTH: u32 = 4096;
/// Planning work one repair may spend: one unit per visited node plus one per
/// 256 bytes of its text, so a pathological clause cannot rescan megabytes.
const MAX_BRIDGE_WORK: usize = 1 << 16;
/// Links one repair may add to a chain.
const MAX_BRIDGES: usize = 16;
/// Immediate fields (head plus arguments) of one application.
const MAX_APPLICATION_FIELDS: usize = 64;
/// Nesting depth the planner descends into one printed link, like the
/// printer's other text-level walkers.
const MAX_BRIDGE_DEPTH: usize = 64;

type Value = (BigUint, u32);

/// How two printed operands are proved equal.
enum Plan<'a> {
    /// carcara parses both to one term; no premise is needed.
    Same,
    /// Two closed bit-vector terms of one value and width.
    Eval {
        left: &'a str,
        right: &'a str,
        value: Value,
    },
    /// One plain function symbol applied to argumentwise-equal operands.
    Cong {
        left: &'a str,
        right: &'a str,
        args: Vec<Plan<'a>>,
    },
    /// `read` is `(select (store a i element) i)` and `other` is `element`
    /// up to `link` (`None`: one term to carcara's parser).
    ReadOverWrite {
        read: &'a str,
        element: &'a str,
        other: &'a str,
        link: Option<Box<Plan<'a>>>,
    },
}

/// One hop of the planned chain.
enum Link<'a> {
    Hypothesis(usize),
    Bridge(Plan<'a>),
}

/// The checked derivation of the printed `eq_transitive` clause `clause`
/// (`(cl ..)`, exactly as the step ships) for step `id`, or `None` when the
/// chain is not broken only by closed bit-vector spellings and same-index
/// reads over writes.
pub(super) fn bridged_eq_transitive(id: &str, clause: &str) -> Option<String> {
    let literals =
        split_alethe_application_bounded(clause, "cl", MAX_CHAIN_LITERALS, MAX_CHAIN_TERM_BYTES)
            .ok()?;
    let (goal, hypothesis_literals) = literals.split_last()?;
    let (goal_left, goal_right) = split_printed_equality(goal)?;
    let hypotheses = hypothesis_literals
        .iter()
        .map(|literal| split_printed_negation(literal).and_then(split_printed_equality))
        .collect::<Option<Vec<_>>>()?;
    let mut budget = MAX_BRIDGE_WORK;
    let path = plan_chain(goal_left, goal_right, &hypotheses, &mut budget)?;
    assemble(id, clause, goal, hypothesis_literals, &path)
}

/// carcara's greedy walk from `goal_left`, taking an exact hypothesis hop
/// whenever one exists and a bridged hop only when none does.
fn plan_chain<'a>(
    goal_left: &'a str,
    goal_right: &'a str,
    hypotheses: &[(&'a str, &'a str)],
    budget: &mut usize,
) -> Option<Vec<Link<'a>>> {
    let mut used = vec![false; hypotheses.len()];
    let mut path = Vec::new();
    let mut left = goal_left;
    let mut bridges = 0usize;
    for _ in 0..=hypotheses.len() {
        let used_hypothesis = path.iter().any(|link| matches!(link, Link::Hypothesis(_)));
        if equal_modulo_bitvec_literal_spelling(left, goal_right) {
            return (bridges > 0 && used_hypothesis).then_some(path);
        }
        if let Some((index, next)) = exact_hop(left, hypotheses, &used) {
            used[index] = true;
            path.push(Link::Hypothesis(index));
            left = next;
            continue;
        }
        if bridges == MAX_BRIDGES {
            return None;
        }
        if used_hypothesis {
            if let Some(plan) = plan_link(left, goal_right, budget) {
                path.push(Link::Bridge(plan));
                return Some(path);
            }
        }
        let (index, next, plan) = bridged_hop(left, hypotheses, &used, budget)?;
        used[index] = true;
        bridges += 1;
        path.push(Link::Bridge(plan));
        path.push(Link::Hypothesis(index));
        left = next;
    }
    None
}

fn exact_hop<'a>(
    left: &str,
    hypotheses: &[(&'a str, &'a str)],
    used: &[bool],
) -> Option<(usize, &'a str)> {
    hypotheses
        .iter()
        .enumerate()
        .filter(|(index, _)| !used[*index])
        .find_map(|(index, &(first, second))| {
            if equal_modulo_bitvec_literal_spelling(first, left) {
                Some((index, second))
            } else if equal_modulo_bitvec_literal_spelling(second, left) {
                Some((index, first))
            } else {
                None
            }
        })
}

fn bridged_hop<'a>(
    left: &'a str,
    hypotheses: &[(&'a str, &'a str)],
    used: &[bool],
    budget: &mut usize,
) -> Option<(usize, &'a str, Plan<'a>)> {
    for (index, &(first, second)) in hypotheses.iter().enumerate() {
        if used[index] {
            continue;
        }
        if let Some(plan) = plan_link(left, first, budget) {
            return Some((index, second, plan));
        }
        if let Some(plan) = plan_link(left, second, budget) {
            return Some((index, first, plan));
        }
    }
    None
}

/// A link that needs at least one checked step (never [`Plan::Same`]).
fn plan_link<'a>(left: &'a str, right: &'a str, budget: &mut usize) -> Option<Plan<'a>> {
    match plan_equality(left, right, 0, budget)? {
        Plan::Same => None,
        plan => Some(plan),
    }
}

fn plan_equality<'a>(
    left: &'a str,
    right: &'a str,
    depth: usize,
    budget: &mut usize,
) -> Option<Plan<'a>> {
    (depth <= MAX_BRIDGE_DEPTH).then_some(())?;
    spend(budget, left.len() + right.len())?;
    if equal_modulo_bitvec_literal_spelling(left, right) {
        return Some(Plan::Same);
    }
    if let (Some(value), Some(other)) = (
        closed_value(left, depth, budget),
        closed_value(right, depth, budget),
    ) {
        return (value == other).then_some(Plan::Eval { left, right, value });
    }
    plan_congruence(left, right, depth, budget)
        .or_else(|| plan_read_over_write(left, right, depth, budget))
}

/// `cong` over one plain head with the same arity, one sub-plan per operand.
fn plan_congruence<'a>(
    left: &'a str,
    right: &'a str,
    depth: usize,
    budget: &mut usize,
) -> Option<Plan<'a>> {
    let (head, left_args) = plain_application(left)?;
    let (right_head, right_args) = plain_application(right)?;
    if head != right_head || left_args.len() != right_args.len() {
        return None;
    }
    // A binary `=` whose operands do not pair in order is retried with the
    // right-hand operands swapped: pinned carcara's `cong` accepts either
    // orientation of an equality (`congruence.rs`, the `Operator::Equals` arm
    // tries all four), so `(= v2 (select (store a i v1) i))` meets the
    // canonical `(= v1 v2)` through `arrays_idx`. Only after the in-order
    // pairing failed, so every link proved before keeps its derivation.
    let in_order = plan_pairs(left_args.iter().zip(&right_args), depth, budget);
    let args = match (in_order, left_args.as_slice(), right_args.as_slice()) {
        (Some(args), _, _) => args,
        (None, [left_0, left_1], [right_0, right_1]) if head == "=" => {
            plan_pairs([(left_0, right_1), (left_1, right_0)], depth, budget)?
        }
        (None, _, _) => return None,
    };
    if args.iter().all(|arg| matches!(arg, Plan::Same)) {
        return None;
    }
    Some(Plan::Cong { left, right, args })
}

/// One sub-plan per operand pair, or `None` when any pair has none.
fn plan_pairs<'a, 'b>(
    pairs: impl IntoIterator<Item = (&'b &'a str, &'b &'a str)>,
    depth: usize,
    budget: &mut usize,
) -> Option<Vec<Plan<'a>>>
where
    'a: 'b,
{
    pairs
        .into_iter()
        .map(|(left, right)| plan_equality(left, right, depth + 1, budget))
        .collect()
}

fn spend(budget: &mut usize, bytes: usize) -> Option<()> {
    *budget = budget.checked_sub(1 + bytes / 256)?;
    Some(())
}

/// `(f a1 .. an)` for a plain, unindexed, unquoted function symbol `f`.
fn plain_application(text: &str) -> Option<(&str, Vec<&str>)> {
    let inner = text.strip_prefix('(')?.strip_suffix(')')?;
    let mut fields =
        split_smt_term_slices_bounded(inner, MAX_APPLICATION_FIELDS, MAX_CHAIN_TERM_BYTES).ok()?;
    if fields.len() < 2 {
        return None;
    }
    let head = fields.remove(0);
    let plain_symbol = head.chars().next().is_some_and(|first| {
        !matches!(first, '(' | '|' | '"' | ':' | '#') && !first.is_ascii_digit()
    });
    let binder_or_annotation = matches!(
        head,
        "_" | "!" | "as" | "let" | "forall" | "exists" | "choice" | "lambda" | "match" | "par"
    );
    (plain_symbol && !binder_or_annotation).then_some((head, fields))
}

/// AY's exact value of a closed bit-vector term over the supported operators.
fn closed_value(text: &str, depth: usize, budget: &mut usize) -> Option<Value> {
    (depth <= MAX_BRIDGE_DEPTH).then_some(())?;
    spend(budget, text.len())?;
    if let Some((value, width)) = parse_printed_bitvec_literal(text) {
        // `(_ bvN w)` must denote a value below `2^w`; anything else is not a
        // literal carcara and AY read the same way.
        let canonical = (1..=MAX_BRIDGE_WIDTH).contains(&width) && value.bits() <= u64::from(width);
        return canonical.then_some((value, width));
    }
    let inner = text.strip_prefix('(')?.strip_suffix(')')?;
    let fields =
        split_smt_term_slices_bounded(inner, MAX_APPLICATION_FIELDS, MAX_CHAIN_TERM_BYTES).ok()?;
    let (head, args) = fields.split_first()?;
    let values = args
        .iter()
        .map(|arg| closed_value(arg, depth + 1, budget))
        .collect::<Option<Vec<_>>>()?;
    evaluate_closed(head, &values)
}

fn evaluate_closed(head: &str, values: &[Value]) -> Option<Value> {
    let one = || BigUint::from(1u8);
    match (head, values) {
        ("concat", [_, _, ..]) => {
            let width = values
                .iter()
                .try_fold(0u32, |sum, (_, width)| sum.checked_add(*width))?;
            (width <= MAX_BRIDGE_WIDTH).then_some(())?;
            let value = values
                .iter()
                .fold(BigUint::default(), |acc, (value, width)| {
                    (acc << *width) | value
                });
            Some((value, width))
        }
        ("bvadd" | "bvmul" | "bvand" | "bvor" | "bvxor", [(first, width), rest @ ..])
            if !rest.is_empty() && rest.iter().all(|(_, other)| other == width) =>
        {
            let modulus = one() << *width;
            let value = rest
                .iter()
                .fold(first.clone(), |acc, (value, _)| match head {
                    "bvadd" => (acc + value) % &modulus,
                    "bvmul" => (acc * value) % &modulus,
                    "bvand" => acc & value,
                    "bvor" => acc | value,
                    _ => acc ^ value,
                });
            Some((value, *width))
        }
        ("bvnot", [(value, width)]) => Some((((one() << *width) - one()) ^ value, *width)),
        ("bvneg", [(value, width)]) => {
            let modulus = one() << *width;
            Some(((&modulus - value) % &modulus, *width))
        }
        (_, [(value, width)]) => {
            let extension = zero_extension(head)?;
            let width = width.checked_add(extension)?;
            (width <= MAX_BRIDGE_WIDTH).then_some((value.clone(), width))
        }
        _ => None,
    }
}

/// `k` of an indexed head spelled exactly `(_ zero_extend k)`.
fn zero_extension(head: &str) -> Option<u32> {
    let inner = head.strip_prefix('(')?.strip_suffix(')')?;
    match inner.split_whitespace().collect::<Vec<_>>().as_slice() {
        ["_", "zero_extend", count] => count.parse().ok(),
        _ => None,
    }
}

/// Print `path` as checked steps ending in step `id` with conclusion `clause`.
fn assemble(
    id: &str,
    clause: &str,
    goal: &str,
    hypothesis_literals: &[&str],
    path: &[Link<'_>],
) -> Option<String> {
    let mut emitter = Emitter {
        id,
        next: 0,
        out: String::new(),
    };
    let mut chain: Vec<String> = Vec::with_capacity(hypothesis_literals.len() + MAX_BRIDGES + 1);
    let mut bridge_steps = Vec::new();
    let mut used = vec![false; hypothesis_literals.len()];
    for link in path {
        match link {
            Link::Hypothesis(index) => {
                used[*index] = true;
                chain.push(hypothesis_literals[*index].to_string());
            }
            Link::Bridge(plan) => {
                let (step, left, right) = emitter.emit(plan)?;
                let equality = format!("(= {left} {right})");
                let literal = format!("(not {equality})");
                // A link that restates a clause literal (or repeats a link)
                // would give the closing resolution an ambiguous pivot.
                let restated = hypothesis_literals
                    .iter()
                    .copied()
                    .chain(std::iter::once(goal))
                    .chain(chain.iter().map(String::as_str))
                    .any(|existing| {
                        equal_modulo_bitvec_literal_spelling(existing, &literal)
                            || equal_modulo_bitvec_literal_spelling(existing, &equality)
                    });
                if restated {
                    return None;
                }
                chain.push(literal);
                bridge_steps.push(step);
            }
        }
    }
    chain.extend(
        hypothesis_literals
            .iter()
            .enumerate()
            .filter(|(index, _)| !used[*index])
            .map(|(_, literal)| (*literal).to_string()),
    );
    chain.push(goal.to_string());
    let borrowed: Vec<&str> = chain.iter().map(String::as_str).collect();
    if bridge_steps.is_empty() || !printed_eq_transitive_chain_holds(&borrowed) {
        return None;
    }
    let mut out = emitter.out;
    let _ = writeln!(
        out,
        "(step {id}.gb.et (cl {}) :rule eq_transitive)",
        chain.join(" ")
    );
    let _ = write!(
        out,
        "(step {id} {clause} :rule resolution :premises ({id}.gb.et {}))",
        bridge_steps.join(" ")
    );
    Some(out)
}

#[cfg(test)]
#[path = "alethe_printer_eq_transitive_bridge_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "alethe_printer_eq_transitive_bridge_row_tests.rs"]
mod read_over_write_tests;

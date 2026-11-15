// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Checked closed Boolean equalities left by constant BV conflicts.

use super::*;

#[derive(PartialEq, Eq)]
enum ClosedValue {
    Bool(bool),
    BitVec(num_bigint::BigUint, u32),
}

fn evaluate_closed(term: &str, depth: usize, remaining: &mut usize) -> Option<ClosedValue> {
    if depth > 16 {
        return None;
    }
    *remaining = remaining.checked_sub(1)?;
    match term {
        "true" => return Some(ClosedValue::Bool(true)),
        "false" => return Some(ClosedValue::Bool(false)),
        _ => {}
    }
    if let Some((value, width)) = parse_printed_bitvec_literal(term) {
        return (1..=128)
            .contains(&width)
            .then_some(ClosedValue::BitVec(value, width));
    }
    if let Some(args) = split_application(term, "not") {
        let [inner]: [String; 1] = args.try_into().ok()?;
        let ClosedValue::Bool(value) = evaluate_closed(&inner, depth + 1, remaining)? else {
            return None;
        };
        return Some(ClosedValue::Bool(!value));
    }
    let [left, right]: [String; 2] = split_application(term, "=")?.try_into().ok()?;
    let left = evaluate_closed(&left, depth + 1, remaining)?;
    let right = evaluate_closed(&right, depth + 1, remaining)?;
    match (&left, &right) {
        (ClosedValue::Bool(_), ClosedValue::Bool(_)) => {}
        (ClosedValue::BitVec(_, a), ClosedValue::BitVec(_, b)) if a == b => {}
        _ => return None,
    }
    Some(ClosedValue::Bool(left == right))
}

impl AlethePrinter<'_> {
    pub(super) fn lower_closed_boolean_clause(&self, id: ProofId, clause: &str) -> Option<String> {
        if clause.len() > 8192 || self.work_budget_exhausted() {
            return None;
        }
        self.charge(clause.len() as u64);
        let literals = split_application(clause, "cl")?;
        let mut remaining = 64;
        let output = match literals.as_slice() {
            [literal]
                if evaluate_closed(literal, 0, &mut remaining) == Some(ClosedValue::Bool(true)) =>
            {
                format!(
                    "(step {id}.closed (cl (= {literal} true)) :rule evaluate)\n\
                     (step {id}.positive (cl {literal} (not true)) :rule equiv2 :premises ({id}.closed))\n\
                     (step {id}.true (cl true) :rule true)\n\
                     (step {id} (cl {literal}) :rule resolution :premises ({id}.positive {id}.true))"
                )
            }
            [negative, literal]
                if *negative == format!("(not (not (not {literal})))")
                    && matches!(
                        evaluate_closed(literal, 0, &mut remaining),
                        Some(ClosedValue::Bool(_))
                    ) =>
            {
                format!("(step {id} {clause} :rule not_not)")
            }
            _ => return None,
        };
        self.charge(output.len() as u64);
        (!self.work_budget_exhausted()).then_some(output)
    }
}

#[cfg(test)]
mod tests;

// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared bounded parser for typed finite-array model values.

use ay_core::Sort;
use ay_model_check::{ArrayValue, ModelValue};

use super::super::rendered_dt_limits::{
    model_value_work, rendered_sexp_within_limits, MAX_RENDERED_DT_BYTES,
};

pub(in crate::executor::model) const MAX_TYPED_ARRAY_DEPTH: u32 = 32;
const MAX_TYPED_ARRAY_TOTAL_WORK: usize = 4 * MAX_RENDERED_DT_BYTES;

/// Shared allocation/work envelope for one typed-array reconstruction pass.
pub(in crate::executor::model) struct TypedArrayParseBudget {
    work: usize,
}

impl TypedArrayParseBudget {
    pub(in crate::executor::model) fn new() -> Self {
        Self { work: 0 }
    }

    pub(in crate::executor::model) fn charge_text(&mut self, text: &str) -> bool {
        rendered_sexp_within_limits(text) && self.charge(text.len())
    }

    pub(in crate::executor::model) fn charge_value(&mut self, value: &ModelValue) -> bool {
        model_value_work(value).is_some_and(|amount| self.charge(amount))
    }

    fn charge(&mut self, amount: usize) -> bool {
        match self.work.checked_add(amount) {
            Some(next) if next <= MAX_TYPED_ARRAY_TOTAL_WORK => {
                self.work = next;
                true
            }
            _ => false,
        }
    }
}

/// Parse the two finite-array forms emitted by AY's model printer. The caller
/// owns typed leaf parsing so this one structural parser can be reused by both
/// the independent array view and guarded datatype-field reconstruction.
pub(in crate::executor::model) fn parse_bounded_typed_array_text<F>(
    text: &str,
    expected_sort: &str,
    index_sort: &Sort,
    element_sort: &Sort,
    depth: u32,
    budget: &mut TypedArrayParseBudget,
    parse_leaf: &mut F,
) -> Option<ModelValue>
where
    F: FnMut(&str, &Sort, u32, &mut TypedArrayParseBudget) -> Option<ModelValue>,
{
    if depth > MAX_TYPED_ARRAY_DEPTH || !budget.charge_text(text) {
        return None;
    }
    let items = sexpr_items(text)?;
    match items.first()?.as_str() {
        "store" if items.len() == 4 => {
            let base = parse_bounded_typed_array_text(
                &items[1],
                expected_sort,
                index_sort,
                element_sort,
                depth + 1,
                budget,
                parse_leaf,
            )?;
            let ModelValue::Array(mut array) = base else {
                return None;
            };
            let key = parse_leaf(&items[2], index_sort, depth + 1, budget)?;
            let value = parse_leaf(&items[3], element_sort, depth + 1, budget)?;
            if !budget.charge_value(&key) || !budget.charge_value(&value) {
                return None;
            }
            array.store.push((key, value));
            Some(ModelValue::Array(array))
        }
        head if items.len() == 2 && head.starts_with('(') => {
            let qualifier = sexpr_items(head)?;
            if qualifier.len() != 3
                || qualifier[0] != "as"
                || qualifier[1] != "const"
                || canonical_sexpr(&qualifier[2])? != canonical_sexpr(expected_sort)?
            {
                return None;
            }
            let default = parse_leaf(&items[1], element_sort, depth + 1, budget)?;
            if !budget.charge_value(&default) {
                return None;
            }
            Some(ModelValue::Array(Box::new(ArrayValue {
                default,
                store: Vec::new(),
            })))
        }
        _ => None,
    }
}

/// Canonicalize one parsed s-expression before comparing a model qualifier to
/// the canonical sort renderer. This accepts harmless whitespace differences
/// but rejects adjacent forms, unbalanced input, and malformed quoted tokens.
fn canonical_sexpr(text: &str) -> Option<String> {
    let text = text.trim();
    if text.starts_with('(') {
        let items = sexpr_items(text)?;
        let items: Option<Vec<_>> = items.iter().map(|item| canonical_sexpr(item)).collect();
        return Some(format!("({})", items?.join(" ")));
    }
    let wrapped = format!("({text})");
    let mut items = sexpr_items(&wrapped)?;
    (items.len() == 1).then(|| items.remove(0))
}

/// Split one parenthesised s-expression into top-level items while respecting
/// nesting and SMT-LIB string/quoted-symbol delimiters.
pub(in crate::executor::model) fn sexpr_items(text: &str) -> Option<Vec<String>> {
    let body = text.trim().strip_prefix('(')?.strip_suffix(')')?;
    let mut items = Vec::new();
    let mut current = String::new();
    let mut depth = 0_i32;
    let mut in_string = false;
    let mut in_symbol = false;
    let mut chars = body.chars().peekable();
    while let Some(character) = chars.next() {
        if in_string {
            current.push(character);
            if character == '"' {
                if chars.peek() == Some(&'"') {
                    current.push(chars.next()?);
                } else {
                    in_string = false;
                }
            }
            continue;
        }
        if in_symbol {
            current.push(character);
            if character == '|' {
                in_symbol = false;
            }
            continue;
        }
        match character {
            '"' => {
                in_string = true;
                current.push(character);
            }
            '|' => {
                in_symbol = true;
                current.push(character);
            }
            '(' => {
                depth += 1;
                current.push(character);
            }
            ')' => {
                depth -= 1;
                if depth < 0 {
                    return None;
                }
                current.push(character);
            }
            character if character.is_whitespace() && depth == 0 => {
                if !current.is_empty() {
                    items.push(std::mem::take(&mut current));
                }
            }
            _ => current.push(character),
        }
    }
    if depth != 0 || in_string || in_symbol {
        return None;
    }
    if !current.is_empty() {
        items.push(current);
    }
    Some(items)
}

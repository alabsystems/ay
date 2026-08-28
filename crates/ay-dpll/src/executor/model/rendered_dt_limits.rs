// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Allocation and recursion preflights for rendered datatype values.

use ay_core::Sort;
use ay_model_check::ModelValue;

pub(super) const MAX_RENDERED_DT_BYTES: usize = 1024 * 1024;
pub(super) const MAX_RENDERED_DT_NODES: usize = 1024;
pub(super) const MAX_RENDERED_DT_DEPTH: usize = 32;
const MAX_RENDERED_DT_IDENTIFIER_BYTES: usize = 256;

pub(super) struct SchemaSourceBudget {
    bytes: usize,
    sort_nodes: usize,
}

impl SchemaSourceBudget {
    pub(super) fn new() -> Self {
        Self {
            bytes: 0,
            sort_nodes: 0,
        }
    }

    pub(super) fn charge_name(&mut self, amount: usize) -> bool {
        match self.bytes.checked_add(amount) {
            Some(next) if next <= MAX_RENDERED_DT_BYTES => {
                self.bytes = next;
                true
            }
            _ => false,
        }
    }

    pub(super) fn charge_identifier(&mut self, name: &str) -> bool {
        name.len() <= MAX_RENDERED_DT_IDENTIFIER_BYTES && self.charge_name(name.len())
    }

    /// Conservative clone/comparison work for the bounded descriptor seen so
    /// far. Each sort/schema node is charged at the same per-node envelope as
    /// opaque value construction, in addition to exact identifier bytes.
    pub(super) fn work(&self) -> Option<usize> {
        self.sort_nodes.checked_mul(272)?.checked_add(self.bytes)
    }

    /// Bound borrowed sort descriptors before any schema clone. Inline
    /// datatype descriptors can contain arbitrarily large trees and names.
    pub(super) fn charge_sort(&mut self, sort: &Sort) -> bool {
        let mut stack = vec![(sort, 0usize)];
        while let Some((sort, depth)) = stack.pop() {
            if depth > MAX_RENDERED_DT_DEPTH {
                return false;
            }
            self.sort_nodes = match self.sort_nodes.checked_add(1) {
                Some(next) if next <= MAX_RENDERED_DT_NODES => next,
                _ => return false,
            };
            match sort {
                Sort::Array(array) => {
                    if stack.len().checked_add(2).is_none_or(|pending| {
                        pending > MAX_RENDERED_DT_NODES.saturating_sub(self.sort_nodes)
                    }) {
                        return false;
                    }
                    stack.push((&array.index_sort, depth + 1));
                    stack.push((&array.element_sort, depth + 1));
                }
                Sort::Seq(element) => {
                    if stack.len() >= MAX_RENDERED_DT_NODES.saturating_sub(self.sort_nodes) {
                        return false;
                    }
                    stack.push((element, depth + 1));
                }
                Sort::Uninterpreted(name) | Sort::FiniteDomain(name, _) | Sort::TypeVar(name) => {
                    if !self.charge_identifier(name) {
                        return false;
                    }
                }
                Sort::Datatype(datatype) => {
                    if !self.charge_identifier(&datatype.name) {
                        return false;
                    }
                    for constructor in &datatype.constructors {
                        self.sort_nodes = match self.sort_nodes.checked_add(1) {
                            Some(next) if next <= MAX_RENDERED_DT_NODES => next,
                            _ => return false,
                        };
                        if !self.charge_identifier(&constructor.name) {
                            return false;
                        }
                        for field in &constructor.fields {
                            self.sort_nodes = match self.sort_nodes.checked_add(1) {
                                Some(next) if next <= MAX_RENDERED_DT_NODES => next,
                                _ => return false,
                            };
                            if !self.charge_identifier(&field.name)
                                || stack.len()
                                    >= MAX_RENDERED_DT_NODES.saturating_sub(self.sort_nodes)
                            {
                                return false;
                            }
                            stack.push((&field.sort, depth + 1));
                        }
                    }
                }
                _ => {}
            }
        }
        true
    }
}

/// Exact bounded node/payload work for aggregate callers.
pub(super) fn model_value_work(value: &ModelValue) -> Option<usize> {
    let mut stack = vec![(value, 0usize)];
    let mut nodes = 0usize;
    let mut bytes = 0usize;
    while let Some((value, depth)) = stack.pop() {
        if depth > MAX_RENDERED_DT_DEPTH {
            return None;
        }
        nodes += 1;
        if nodes > MAX_RENDERED_DT_NODES {
            return None;
        }
        let payload = match value {
            ModelValue::Bool(_) => 5,
            ModelValue::Int(value) => match usize::try_from(value.bits()) {
                Ok(bits) => bits.saturating_add(2),
                Err(_) => return None,
            },
            ModelValue::Real(value) => {
                let Ok(numerator) = usize::try_from(value.numer().bits()) else {
                    return None;
                };
                let Ok(denominator) = usize::try_from(value.denom().bits()) else {
                    return None;
                };
                numerator.saturating_add(denominator).saturating_add(3)
            }
            ModelValue::BitVec { width, value } => {
                match usize::try_from(u64::from(*width).max(value.bits())) {
                    Ok(bits) => bits.saturating_add(16),
                    Err(_) => return None,
                }
            }
            ModelValue::Str(value) | ModelValue::Uninterpreted(value) => value.len(),
            ModelValue::Datatype { ctor, args } => {
                if stack
                    .len()
                    .checked_add(args.len())
                    .is_none_or(|pending| pending > MAX_RENDERED_DT_NODES.saturating_sub(nodes))
                {
                    return None;
                }
                stack.extend(args.iter().map(|arg| (arg, depth + 1)));
                ctor.len().saturating_add(2)
            }
            ModelValue::Array(array) => {
                let Some(extra) = array
                    .store
                    .len()
                    .checked_mul(2)
                    .and_then(|entries| entries.checked_add(1))
                else {
                    return None;
                };
                if stack
                    .len()
                    .checked_add(extra)
                    .is_none_or(|pending| pending > MAX_RENDERED_DT_NODES.saturating_sub(nodes))
                {
                    return None;
                }
                stack.push((&array.default, depth + 1));
                for (index, cell) in &array.store {
                    stack.push((index, depth + 1));
                    stack.push((cell, depth + 1));
                }
                1
            }
            ModelValue::Seq(elements) => {
                if stack
                    .len()
                    .checked_add(elements.len())
                    .is_none_or(|pending| pending > MAX_RENDERED_DT_NODES.saturating_sub(nodes))
                {
                    return None;
                }
                stack.extend(elements.iter().map(|element| (element, depth + 1)));
                1
            }
            ModelValue::FloatingPoint { .. } | ModelValue::Algebraic(_) => return None,
        };
        bytes = match bytes.checked_add(payload) {
            Some(total) if total <= MAX_RENDERED_DT_BYTES => total,
            _ => return None,
        };
    }
    bytes.checked_add(nodes)
}

/// Iterative resource preflight before recursive S-expression parsing.
pub(super) fn rendered_sexp_within_limits(input: &str) -> bool {
    if input.is_empty() || input.len() > MAX_RENDERED_DT_BYTES {
        return false;
    }
    let bytes = input.as_bytes();
    let mut index = 0usize;
    let mut depth = 0usize;
    let mut nodes = 0usize;
    let mut in_bare_atom = false;
    while index < bytes.len() {
        match bytes[index] {
            byte if byte.is_ascii_whitespace() => {
                in_bare_atom = false;
                index += 1;
            }
            b'(' => {
                in_bare_atom = false;
                depth += 1;
                nodes += 1;
                if depth > MAX_RENDERED_DT_DEPTH || nodes > MAX_RENDERED_DT_NODES {
                    return false;
                }
                index += 1;
            }
            b')' => {
                in_bare_atom = false;
                if depth == 0 {
                    return false;
                }
                depth -= 1;
                index += 1;
            }
            b'"' => {
                if in_bare_atom {
                    return false;
                }
                nodes += 1;
                if nodes > MAX_RENDERED_DT_NODES {
                    return false;
                }
                index += 1;
                let mut closed = false;
                while index < bytes.len() {
                    if bytes[index] == b'"' {
                        if bytes.get(index + 1) == Some(&b'"') {
                            index += 2;
                            continue;
                        }
                        index += 1;
                        closed = true;
                        break;
                    }
                    index += 1;
                }
                if !closed {
                    return false;
                }
            }
            b'|' => {
                if in_bare_atom {
                    return false;
                }
                nodes += 1;
                if nodes > MAX_RENDERED_DT_NODES {
                    return false;
                }
                index += 1;
                let Some(end) = bytes[index..].iter().position(|&byte| byte == b'|') else {
                    return false;
                };
                index += end + 1;
            }
            _ => {
                if !in_bare_atom {
                    nodes += 1;
                    if nodes > MAX_RENDERED_DT_NODES {
                        return false;
                    }
                    in_bare_atom = true;
                }
                index += 1;
            }
        }
    }
    depth == 0 && nodes > 0
}

#[cfg(test)]
mod tests {
    use ay_model_check::ArrayValue;
    use num_bigint::BigInt;

    use super::*;

    #[test]
    fn aggregate_model_value_work_accepts_bounded_arrays_and_sequences() {
        let value = ModelValue::Datatype {
            ctor: "Box".to_string(),
            args: vec![ModelValue::Array(Box::new(ArrayValue {
                default: ModelValue::Seq(vec![ModelValue::Int(BigInt::from(0))]),
                store: vec![(
                    ModelValue::Int(BigInt::from(1)),
                    ModelValue::Seq(vec![ModelValue::Int(BigInt::from(2))]),
                )],
            }))],
        };

        assert!(
            model_value_work(&value).is_some(),
            "bounded Array/Seq fields are valid structured datatype payloads"
        );
    }

    #[test]
    fn aggregate_model_value_work_rejects_oversized_store() {
        let entries = (0..MAX_RENDERED_DT_NODES)
            .map(|index| {
                (
                    ModelValue::Int(BigInt::from(index)),
                    ModelValue::Int(BigInt::from(index)),
                )
            })
            .collect();
        let value = ModelValue::Array(Box::new(ArrayValue {
            default: ModelValue::Int(BigInt::from(0)),
            store: entries,
        }));

        assert_eq!(
            model_value_work(&value),
            None,
            "aggregate recovery must fail closed before an oversized walk"
        );
    }
}

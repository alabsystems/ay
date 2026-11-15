// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! An exact requirement trie for one alias class and semantic index value.
//! Names and values borrow already-retained entries; only the bounded trie
//! nodes and the final complete constructor/array value are allocated here.

use super::*;
use crate::residual::path::metadata;
use crate::residual::MAX_CLASSIFY_DEPTH;

mod arrays;

#[derive(Clone, Copy)]
enum Key<'a> {
    Field(&'a str),
    Index(&'a ModelValue),
}

enum Path<'a> {
    Fields(&'a [String]),
    Access(&'a [AccessStep]),
}

impl<'a> Path<'a> {
    fn split(self) -> Option<(Key<'a>, Self)> {
        match self {
            Self::Fields(path) => path
                .split_first()
                .map(|(name, rest)| (Key::Field(name), Self::Fields(rest))),
            Self::Access(path) => path.split_first().map(|(step, rest)| {
                let key = match step {
                    AccessStep::Field(name) => Key::Field(name),
                    AccessStep::Index(value) => Key::Index(value),
                };
                (key, Self::Access(rest))
            }),
        }
    }
}

#[derive(Default)]
struct Node<'a> {
    value: Option<&'a ModelValue>,
    children: Vec<(Key<'a>, Node<'a>)>,
}

pub(super) fn materialize(
    sort: &Sort,
    group: &[&Entry],
    resolve: &DtResolve<'_>,
    budget: &mut WitnessBudget,
) -> Option<ModelValue> {
    if !budget.spend_value_node() {
        return None;
    }
    let mut root = Node::default();
    for entry in group {
        let path = match &entry.slot {
            Slot::Whole => Path::Fields(&[]),
            Slot::Field(name) => Path::Fields(std::slice::from_ref(name)),
            Slot::Path(path) if (2..=MAX_CLASSIFY_DEPTH).contains(&path.len()) => {
                Path::Fields(path)
            }
            Slot::Path(_) => return None,
            Slot::Access(path) if (1..=MAX_CLASSIFY_DEPTH).contains(&path.len()) => {
                Path::Access(path)
            }
            Slot::Access(_) => return None,
        };
        root.insert(path, &entry.value, budget)?;
    }
    root.build(sort, resolve, budget, 0)
}

impl<'a> Node<'a> {
    fn child_index(&self, key: Key<'_>, budget: &mut WitnessBudget) -> Option<Option<usize>> {
        for (index, (candidate, _)) in self.children.iter().enumerate() {
            let matches = match (key, *candidate) {
                (Key::Field(name), Key::Field(candidate)) => {
                    if !budget.spend_value_nodes(name.len().min(candidate.len()).checked_add(1)?) {
                        return None;
                    }
                    name == candidate
                }
                (Key::Index(left), Key::Index(right)) => index_equal(left, right, budget)?,
                _ => return None,
            };
            if matches {
                return Some(Some(index));
            }
        }
        Some(None)
    }

    fn insert(
        &mut self,
        path: Path<'a>,
        value: &'a ModelValue,
        budget: &mut WitnessBudget,
    ) -> Option<()> {
        let Some((key, rest)) = path.split() else {
            if let Some(previous) = self.value {
                equal(previous, value, budget)?;
            } else {
                self.value = Some(value);
            }
            return Some(());
        };
        if !budget.spend_value_node() {
            return None;
        }
        let index = match self.child_index(key, budget)? {
            Some(index) => index,
            None => {
                if !budget.spend_value_node() {
                    return None;
                }
                self.children.try_reserve(1).ok()?;
                self.children.push((key, Node::default()));
                self.children.len() - 1
            }
        };
        self.children.get_mut(index)?.1.insert(rest, value, budget)
    }

    fn build(
        &self,
        sort: &Sort,
        resolve: &DtResolve<'_>,
        budget: &mut WitnessBudget,
        depth: usize,
    ) -> Option<ModelValue> {
        if depth > MAX_CLASSIFY_DEPTH || !budget.spend_value_node() {
            return None;
        }
        if let Some(value) = self.value {
            self.verify(sort, value, resolve, budget, depth)?;
            return budget.account_value(value).then(|| value.clone());
        }
        if self.children.is_empty() {
            return canonical_inhabitant(sort, resolve, &mut Vec::new(), budget, depth);
        }
        if let Sort::Array(array) = sort {
            return arrays::build(self, array, resolve, budget, depth);
        }
        let datatype = metadata::datatype(sort, resolve, &mut |n| budget.spend_value_nodes(n))?;
        for constructor in &datatype.constructors {
            if !self.fits(constructor, budget)? {
                continue;
            }
            if !budget.spend_value_nodes(constructor.fields.len())
                || !budget.spend_value_nodes(constructor.name.len())
            {
                return None;
            }
            let mut args = Vec::new();
            args.try_reserve(constructor.fields.len()).ok()?;
            let mut complete = true;
            for field in &constructor.fields {
                let child = self.child_index(Key::Field(&field.name), budget)?;
                let value = match child {
                    Some(index) => {
                        self.children
                            .get(index)?
                            .1
                            .build(&field.sort, resolve, budget, depth + 1)
                    }
                    None => canonical_inhabitant(
                        &field.sort,
                        resolve,
                        &mut Vec::new(),
                        budget,
                        depth + 1,
                    ),
                };
                let Some(value) = value else {
                    complete = false;
                    break;
                };
                args.push(value);
            }
            if complete {
                return Some(ModelValue::Datatype {
                    ctor: constructor.name.clone(),
                    args,
                });
            }
        }
        None
    }

    fn fits(
        &self,
        constructor: &ay_core::DatatypeConstructor,
        budget: &mut WitnessBudget,
    ) -> Option<bool> {
        for (key, _) in &self.children {
            let Key::Field(name) = key else {
                return Some(false);
            };
            if field_index(constructor, name, budget)?.is_none() {
                return Some(false);
            }
        }
        Some(true)
    }

    fn verify(
        &self,
        sort: &Sort,
        value: &ModelValue,
        resolve: &DtResolve<'_>,
        budget: &mut WitnessBudget,
        depth: usize,
    ) -> Option<()> {
        if depth > MAX_CLASSIFY_DEPTH || !budget.spend_value_node() {
            return None;
        }
        if let Some(expected) = self.value {
            equal(expected, value, budget)?;
        }
        if self.children.is_empty() {
            return Some(());
        }
        if let Sort::Array(array) = sort {
            return arrays::verify(self, array, value, resolve, budget, depth);
        }
        let datatype = metadata::datatype(sort, resolve, &mut |n| budget.spend_value_nodes(n))?;
        let ModelValue::Datatype { ctor, args } = value else {
            return None;
        };
        let mut found = None;
        for constructor in &datatype.constructors {
            if !budget.spend_value_nodes(ctor.len().min(constructor.name.len()).checked_add(1)?) {
                return None;
            }
            if constructor.name == *ctor {
                found = Some(constructor);
                break;
            }
        }
        let constructor = found?;
        if constructor.fields.len() != args.len() {
            return None;
        }
        for (key, node) in &self.children {
            let Key::Field(name) = key else {
                return None;
            };
            let index = field_index(constructor, name, budget)??;
            node.verify(
                &constructor.fields.get(index)?.sort,
                args.get(index)?,
                resolve,
                budget,
                depth + 1,
            )?;
        }
        Some(())
    }
}

fn field_index(
    constructor: &ay_core::DatatypeConstructor,
    name: &str,
    budget: &mut WitnessBudget,
) -> Option<Option<usize>> {
    for (index, field) in constructor.fields.iter().enumerate() {
        if !budget.spend_value_nodes(name.len().min(field.name.len()).checked_add(1)?) {
            return None;
        }
        if name == field.name {
            return Some(Some(index));
        }
    }
    Some(None)
}

fn equal(left: &ModelValue, right: &ModelValue, budget: &mut WitnessBudget) -> Option<()> {
    compare(left, right, budget)?.then_some(())
}

fn index_equal(left: &ModelValue, right: &ModelValue, budget: &mut WitnessBudget) -> Option<bool> {
    if !budget.compare_index() {
        return None;
    }
    compare(left, right, budget)
}

fn compare(left: &ModelValue, right: &ModelValue, budget: &mut WitnessBudget) -> Option<bool> {
    if std::ptr::eq(left, right) {
        return budget.spend_value_node().then_some(true);
    }
    // Admit both complete payloads before recursive comparisons. Constructors
    // and sequences compare corresponding children only: squaring unrelated
    // fields would exhaust the allowance on ordinary overlapping record pins.
    let before_left = budget.value_work;
    if !budget.account_value(left) {
        return None;
    }
    let left_size = budget.value_work.checked_sub(before_left)?;
    let before_right = budget.value_work;
    if !budget.account_value(right) {
        return None;
    }
    let right_size = budget.value_work.checked_sub(before_right)?;
    match (left, right) {
        (
            ModelValue::Datatype {
                ctor: left_ctor,
                args: left_args,
            },
            ModelValue::Datatype {
                ctor: right_ctor,
                args: right_args,
            },
        ) => {
            return if left_ctor != right_ctor {
                Some(false)
            } else {
                compare_children(left_args, right_args, budget)
            };
        }
        (ModelValue::Seq(left), ModelValue::Seq(right)) => {
            return compare_children(left, right, budget);
        }
        _ => {}
    }
    // Arrays can compare stores pairwise. Retain the full payload product
    // before that semantic operation and every other scalar/mixed-shape case.
    let work = left_size.checked_mul(right_size)?;
    if !budget.spend_value_nodes(work) {
        return None;
    }
    value_eq(left, right).ok()
}

fn compare_children(
    left: &[ModelValue],
    right: &[ModelValue],
    budget: &mut WitnessBudget,
) -> Option<bool> {
    if left.len() != right.len() {
        return Some(false);
    }
    for (left, right) in left.iter().zip(right) {
        if !compare(left, right, budget)? {
            return Some(false);
        }
    }
    Some(true)
}

#[cfg(test)]
mod tests;

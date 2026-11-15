// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{roots, Control, Substitution};
use crate::{ChcExpr, ChcProblem, ChcSort, ChcVar, HornClause};
use ay_core::kani_compat::{DetHashMap, DetHashSet};

pub(super) struct Census<'a, 'c> {
    names: DetHashSet<&'a str>,
    control: &'c Control,
    next: usize,
}

impl<'a, 'c> Census<'a, 'c> {
    pub(super) fn new(control: &'c Control) -> Self {
        Self {
            names: DetHashSet::default(),
            control,
            next: 0,
        }
    }

    fn name(&mut self, name: &'a str) -> Option<()> {
        // Also covers a later owned clone of a variable/sort name. The census
        // borrows; conservatively retaining this charge avoids a long sort
        // name bypassing the original memory ceiling during substitution.
        self.control
            .admit(name.len().checked_add(1)?, name.len().checked_add(64)?)?;
        if self.names.try_reserve(1).is_err() {
            return self.control.refuse();
        }
        self.names.insert(name);
        Some(())
    }

    fn sort(&mut self, root: &'a ChcSort) -> Option<()> {
        self.control.admit(1, 32)?;
        let mut stack = vec![(root, 0usize)];
        while let Some((sort, depth)) = stack.pop() {
            self.control.admit(1, 64)?;
            if depth >= crate::expr::MAX_EXPR_RECURSION_DEPTH {
                return self.control.refuse();
            }
            match sort {
                ChcSort::Array(key, value) => {
                    self.control.admit(2, 64)?;
                    if stack.try_reserve(2).is_err() {
                        return self.control.refuse();
                    }
                    stack.push((key, depth + 1));
                    stack.push((value, depth + 1));
                }
                ChcSort::Datatype { name, constructors } => {
                    self.name(name)?;
                    for constructor in constructors.iter() {
                        self.name(&constructor.name)?;
                        for selector in &constructor.selectors {
                            self.name(&selector.name)?;
                            self.control.admit(1, 32)?;
                            if stack.try_reserve(1).is_err() {
                                return self.control.refuse();
                            }
                            stack.push((&selector.sort, depth + 1));
                        }
                    }
                }
                ChcSort::Uninterpreted(name) => self.name(name)?,
                ChcSort::Bool | ChcSort::Int | ChcSort::Real | ChcSort::BitVec(_) => {}
            }
        }
        Some(())
    }

    pub(super) fn problem(&mut self, problem: &'a ChcProblem) -> Option<()> {
        self.control.poll()?;
        for predicate in problem.predicates() {
            self.name(&predicate.name)?;
            for sort in &predicate.arg_sorts {
                self.sort(sort)?;
            }
        }
        for (name, constructors) in problem.datatype_defs() {
            self.name(name)?;
            for (constructor, selectors) in constructors {
                self.name(constructor)?;
                for (selector, sort) in selectors {
                    self.name(selector)?;
                    self.sort(sort)?;
                }
            }
        }
        for name in problem.action_names() {
            self.name(name)?;
        }
        for clause in problem.source_clauses() {
            for root in roots(clause) {
                self.expression(root)?;
            }
        }
        // Retained pruned clauses have their own immutable declaration registry.
        // Iteration, not recursive normalization, keeps naming fully borrowed.
        if let Some(source) = problem.frozen_pruned_source_for_budget() {
            for clause in source.source_clauses() {
                for root in roots(clause) {
                    self.expression(root)?;
                }
            }
            for predicate in source.predicates() {
                self.name(&predicate.name)?;
                for sort in &predicate.arg_sorts {
                    self.sort(sort)?;
                }
            }
            for (name, constructors) in source.datatype_defs() {
                self.name(name)?;
                for (constructor, selectors) in constructors {
                    self.name(constructor)?;
                    for (selector, sort) in selectors {
                        self.name(selector)?;
                        self.sort(sort)?;
                    }
                }
            }
        }
        self.control.poll()
    }

    fn expression(&mut self, root: &'a ChcExpr) -> Option<()> {
        walk(root, self.control, |expression| {
            match expression {
                ChcExpr::Var(var) => {
                    self.name(&var.name)?;
                    self.sort(&var.sort)?;
                }
                ChcExpr::FuncApp(name, sort, _) => {
                    self.name(name)?;
                    self.sort(sort)?;
                }
                ChcExpr::PredicateApp(name, _, _) | ChcExpr::IsTesterMarker(name) => {
                    self.name(name)?;
                }
                ChcExpr::ConstArray(sort, _) | ChcExpr::ConstArrayMarker(sort) => {
                    self.sort(sort)?;
                }
                _ => {}
            }
            Some(())
        })
    }

    pub(super) fn substitution(&mut self, clause: &'a HornClause) -> Option<Substitution> {
        let mut variables: DetHashMap<&str, &ChcVar> = DetHashMap::default();
        let mut ordered = Vec::new();
        for root in roots(clause) {
            walk(root, self.control, |expression| {
                if let ChcExpr::Var(var) = expression {
                    self.control.admit(var.name.len().checked_add(1)?, 128)?;
                    if let Some(previous) = variables.get(var.name.as_str()) {
                        if previous.sort != var.sort {
                            return self.control.refuse();
                        }
                    } else {
                        if variables.try_reserve(1).is_err() || ordered.try_reserve(1).is_err() {
                            return self.control.refuse();
                        }
                        variables.insert(&var.name, var);
                        ordered.push(var);
                    }
                }
                Some(())
            })?;
        }
        let mut result = DetHashMap::default();
        for variable in ordered {
            // Debit every nested sort/name before the replacement owns a clone.
            self.sort(&variable.sort)?;
            let name = self.fresh()?;
            self.control.admit(
                variable.name.len().checked_add(1)?,
                variable.name.len().checked_add(192)?,
            )?;
            if result.try_reserve(1).is_err() {
                return self.control.refuse();
            }
            result.insert(
                variable.name.clone(),
                ChcExpr::var(ChcVar::new(name, variable.sort.clone())),
            );
        }
        self.control.poll()?;
        Some(result)
    }

    fn fresh(&mut self) -> Option<String> {
        loop {
            self.control.admit(64, 64)?;
            // Ordinary SMT-LIB symbols, never the elaborator's __ay_ identities.
            // Parsed names already normalize quoted/unquoted source spellings.
            let name = format!("ay!nullary!{}", self.next);
            let Some(next) = self.next.checked_add(1) else {
                return self.control.refuse();
            };
            self.next = next;
            if !self.names.contains(name.as_str()) {
                return Some(name);
            }
        }
    }
}

fn walk<'a>(
    root: &'a ChcExpr,
    control: &Control,
    mut visit: impl FnMut(&'a ChcExpr) -> Option<()>,
) -> Option<()> {
    control.admit(1, 64)?;
    let mut stack = vec![(root, 0usize)];
    let mut seen = DetHashSet::default();
    while let Some((node, depth)) = stack.pop() {
        control.admit(1, 64)?;
        if depth >= crate::expr::MAX_EXPR_RECURSION_DEPTH {
            return control.refuse();
        }
        if seen.try_reserve(1).is_err() {
            return control.refuse();
        }
        if !seen.insert(std::ptr::from_ref(node)) {
            continue;
        }
        visit(node)?;
        let children = crate::expr::dag::children(node);
        control.admit(children.len(), children.len().checked_mul(32)?)?;
        if stack.try_reserve(children.len()).is_err() {
            return control.refuse();
        }
        stack.extend(
            children
                .iter()
                .rev()
                .map(|child| (child.as_ref(), depth + 1)),
        );
    }
    control.poll()
}

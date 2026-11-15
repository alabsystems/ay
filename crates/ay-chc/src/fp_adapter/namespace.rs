// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Whole typed source namespace, including unused declarations and old queries.

use ay_core::original_query::WorkBudget;

use crate::{ChcExpr, ChcProblem, ChcSort, ClauseHead};

use super::source::{MAX_NAME, MAX_NODES};
use super::{FpAdapterError, FpInputBinding};

pub(super) const PREFIX: &str = "__ay_fp_bits_";
const MAX_RECORDS: usize = 32_768;
const MAX_DEPTH: usize = 64;

struct Census<'a, 'b> {
    records: usize,
    budget: &'a mut WorkBudget<'b>,
}

pub(super) fn validate(
    problem: &ChcProblem,
    bindings: &[FpInputBinding<'_>],
    budget: &mut WorkBudget<'_>,
) -> Result<(), FpAdapterError> {
    if bindings.len() > MAX_NODES {
        return Err(FpAdapterError::Unsupported("input population"));
    }
    // The bounded recursive walk borrows only; reserve its logical frame cost
    // before entering any source graph. There is no clone/hash/global env read.
    budget.admit(256, MAX_DEPTH * 512)?;
    let mut census = Census { records: 0, budget };
    for binding in bindings {
        census.name(&binding.target.name)?;
    }
    census.problem(problem, 0)
}

// Attachment checks its entire old body as well: a second independent FP
// encoding must not alias the reserved body-local auxiliary namespace.
pub(super) fn validate_body(
    body: &crate::ClauseBody,
    budget: &mut WorkBudget<'_>,
) -> Result<(), FpAdapterError> {
    budget.admit(256, MAX_DEPTH * 512)?;
    let mut census = Census { records: 0, budget };
    for (_, args) in &body.predicates {
        census.record(0)?;
        for arg in args {
            census.expr(arg, 1)?;
        }
    }
    if let Some(constraint) = &body.constraint {
        census.expr(constraint, 0)?;
    }
    Ok(())
}

impl Census<'_, '_> {
    fn record(&mut self, depth: usize) -> Result<(), FpAdapterError> {
        self.budget.charge(256)?;
        self.records += 1;
        if depth >= MAX_DEPTH || self.records > MAX_RECORDS {
            return Err(FpAdapterError::Unsupported("whole source namespace bounds"));
        }
        Ok(())
    }

    fn name(&mut self, name: &str) -> Result<(), FpAdapterError> {
        if name.len() > MAX_NAME {
            return Err(FpAdapterError::Unsupported("namespace name width"));
        }
        self.budget
            .charge(name.len().saturating_mul(16).saturating_add(256))?;
        if name.starts_with(PREFIX) {
            return Err(FpAdapterError::Invalid(
                "reserved auxiliary namespace collision",
            ));
        }
        Ok(())
    }

    fn problem(&mut self, problem: &ChcProblem, depth: usize) -> Result<(), FpAdapterError> {
        self.record(depth)?;
        for predicate in problem.predicates() {
            self.record(depth)?;
            self.name(&predicate.name)?;
            for sort in &predicate.arg_sorts {
                self.sort(sort, depth + 1)?;
            }
        }
        for (name, constructors) in problem.datatype_defs() {
            self.record(depth)?;
            self.name(name)?;
            for (constructor, selectors) in constructors {
                self.record(depth)?;
                self.name(constructor)?;
                for (selector, sort) in selectors {
                    self.name(selector)?;
                    self.sort(sort, depth + 1)?;
                }
            }
        }
        for clause in problem.source_clauses() {
            self.record(depth)?;
            for (_, args) in &clause.body.predicates {
                self.record(depth)?;
                for arg in args {
                    self.expr(arg, depth + 1)?;
                }
            }
            if let Some(constraint) = &clause.body.constraint {
                self.expr(constraint, depth + 1)?;
            }
            if let ClauseHead::Predicate(_, args) = &clause.head {
                for arg in args {
                    self.expr(arg, depth + 1)?;
                }
            }
        }
        if let Some(source) = problem.frozen_pruned_source_for_budget() {
            self.problem(source, depth + 1)?;
        }
        Ok(())
    }

    fn sort(&mut self, sort: &ChcSort, depth: usize) -> Result<(), FpAdapterError> {
        self.record(depth)?;
        match sort {
            ChcSort::Array(key, value) => {
                self.sort(key, depth + 1)?;
                self.sort(value, depth + 1)?;
            }
            ChcSort::Uninterpreted(name) => self.name(name)?,
            ChcSort::Datatype { name, constructors } => {
                self.name(name)?;
                for constructor in constructors.iter() {
                    self.record(depth)?;
                    self.name(&constructor.name)?;
                    for selector in &constructor.selectors {
                        self.name(&selector.name)?;
                        self.sort(&selector.sort, depth + 1)?;
                    }
                }
            }
            ChcSort::Bool | ChcSort::Int | ChcSort::Real | ChcSort::BitVec(_) => {}
        }
        Ok(())
    }

    fn expr(&mut self, expr: &ChcExpr, depth: usize) -> Result<(), FpAdapterError> {
        self.record(depth)?;
        match expr {
            ChcExpr::ArrayLambda(lambda) => {
                for formal in std::iter::once(lambda.binder()).chain(lambda.formals()) {
                    self.name(&formal.name)?;
                    self.sort(&formal.sort, depth + 1)?;
                }
                self.expr(lambda.body(), depth + 1)?;
                for value in lambda.captures() {
                    self.expr(value, depth + 1)?;
                }
            }
            ChcExpr::Var(var) => {
                self.name(&var.name)?;
                self.sort(&var.sort, depth + 1)?;
            }
            ChcExpr::Op(_, args) => {
                for arg in args {
                    self.expr(arg, depth + 1)?;
                }
            }
            ChcExpr::PredicateApp(name, _, args) => {
                self.name(name)?;
                for arg in args {
                    self.expr(arg, depth + 1)?;
                }
            }
            ChcExpr::FuncApp(name, sort, args) => {
                self.name(name)?;
                self.sort(sort, depth + 1)?;
                for arg in args {
                    self.expr(arg, depth + 1)?;
                }
            }
            ChcExpr::ConstArray(key, value) => {
                self.sort(key, depth + 1)?;
                self.expr(value, depth + 1)?;
            }
            ChcExpr::ConstArrayMarker(sort) => self.sort(sort, depth + 1)?,
            ChcExpr::IsTesterMarker(name) => self.name(name)?,
            ChcExpr::Bool(_) | ChcExpr::Int(_) | ChcExpr::Real(_, _) | ChcExpr::BitVec(_, _) => {}
        }
        Ok(())
    }
}

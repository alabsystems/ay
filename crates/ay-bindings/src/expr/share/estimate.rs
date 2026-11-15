// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Serialization-cost census aligned with lexical sharing regions.

use super::{node_id, Expr, SHARE_STACK_RED_ZONE, SHARE_STACK_SIZE};
use crate::constraint::Constraint;
use crate::expr::ExprValue;
use crate::program::AYProgram;
use std::collections::{HashMap, HashSet};

struct Estimate {
    cap: usize,
    quantified: HashMap<usize, usize>,
    plain: HashMap<usize, usize>,
}

impl Estimate {
    fn add(&self, left: usize, right: usize) -> usize {
        left.saturating_add(right).min(self.cap)
    }

    fn region(&mut self, root: &Expr) -> usize {
        let mut count = 0;
        self.visit_region(root, &mut HashSet::new(), &mut count);
        count
    }

    fn visit_region(&mut self, expr: &Expr, seen: &mut HashSet<usize>, count: &mut usize) {
        if *count >= self.cap {
            return;
        }
        stacker::maybe_grow(SHARE_STACK_RED_ZONE, SHARE_STACK_SIZE, || {
            if !seen.insert(node_id(expr)) {
                return;
            }
            if let Some(cost) = self.quantifier(expr) {
                *count = self.add(*count, cost);
                return;
            }
            *count = self.add(*count, 1);
            for child in expr.children() {
                if *count >= self.cap {
                    break;
                }
                self.visit_region(child, seen, count);
            }
        });
    }

    fn quantifier(&mut self, expr: &Expr) -> Option<usize> {
        let (body, triggers) = match expr.value.as_ref() {
            ExprValue::Forall { body, triggers, .. } | ExprValue::Exists { body, triggers, .. } => {
                (body, triggers)
            }
            _ => return None,
        };
        let id = node_id(expr);
        if let Some(cost) = self.quantified.get(&id) {
            return Some(*cost);
        }
        let body_cost = self.region(body);
        let mut cost = self.add(1, body_cost);
        for term in triggers.iter().flatten() {
            if cost >= self.cap {
                break;
            }
            // Patterns retain ordinary Display. Count their unfolded nodes,
            // with memoized saturating arithmetic, not a tree traversal.
            let pattern_cost = self.plain_tree(term);
            cost = self.add(cost, pattern_cost);
        }
        self.quantified.insert(id, cost);
        Some(cost)
    }

    fn plain_tree(&mut self, expr: &Expr) -> usize {
        if self.cap == 0 {
            return 0;
        }
        stacker::maybe_grow(SHARE_STACK_RED_ZONE, SHARE_STACK_SIZE, || {
            let id = node_id(expr);
            if let Some(cost) = self.plain.get(&id) {
                return *cost;
            }
            if let Some(cost) = self.quantifier(expr) {
                return cost;
            }
            let mut cost = 1;
            for child in expr.children() {
                if cost >= self.cap {
                    break;
                }
                let child_cost = self.plain_tree(child);
                cost = self.add(cost, child_cost);
            }
            self.plain.insert(id, cost);
            cost
        })
    }
}

// Each root is serialized independently by Constraint::Display: shared Arcs
// across commands, rule body/head, or separate get-value terms do not share lets.
fn constraint_exprs(command: &Constraint) -> Vec<&Expr> {
    match command {
        Constraint::Assert { expr, .. } | Constraint::SoftAssert { expr, .. } => vec![expr],
        Constraint::DefineFun { body, .. } => vec![body],
        Constraint::Rule {
            head: Some(head),
            body,
        } => vec![body, head],
        Constraint::Rule { head: None, body } => vec![body],
        Constraint::Query(expr) | Constraint::Maximize(expr) | Constraint::Minimize(expr) => {
            vec![expr]
        }
        Constraint::GetValue(exprs) => exprs.iter().collect(),
        _ => Vec::new(),
    }
}

impl AYProgram {
    /// Saturating serialization-cost estimate in scope-local distinct term nodes.
    ///
    /// Each separately serialized command expression and quantifier matrix is
    /// a fresh sharing region. A repeated whole quantifier counts once within
    /// its region, but the same Arc in two regions contributes to both. Pattern
    /// terms retain plain rendering and are counted as unfolded trees using
    /// memoized, saturating arithmetic. Returns early at `cap`.
    ///
    /// This is an admission heuristic, not a byte or process-memory bound:
    /// symbol/sort/literal widths, operator expansion, let syntax and the small
    /// unshared terms below the sharing threshold affect actual output size.
    #[must_use]
    pub fn serialized_node_estimate(&self, cap: usize) -> usize {
        let mut estimate = Estimate {
            cap,
            quantified: HashMap::new(),
            plain: HashMap::new(),
        };
        let mut total = 0;
        for command in self.commands() {
            // Unlike GetValue, this command deliberately uses plain Display.
            if let Constraint::CheckSatAssuming(terms) = command {
                for term in terms {
                    if total >= cap {
                        return cap;
                    }
                    let cost = estimate.plain_tree(term);
                    total = estimate.add(total, cost);
                }
                continue;
            }
            for root in constraint_exprs(command) {
                if total >= cap {
                    return cap;
                }
                let cost = estimate.region(root);
                total = estimate.add(total, cost);
            }
        }
        total
    }
}

#[cfg(test)]
mod tests;

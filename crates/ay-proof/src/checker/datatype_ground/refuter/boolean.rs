// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::{Symbol, TermData, TermId};

use super::{equality_sides, GroundRefuter, FALSE_NODE, TRUE_NODE};

impl GroundRefuter<'_> {
    pub(super) fn close_boolean_semantics(&mut self, changed: &mut bool) {
        for index in 0..self.universe.len() {
            let term = self.universe[index];
            self.close_not_semantics(term, changed);
            self.close_equality_semantics(term, changed);
            self.close_nary_boolean_semantics(term, changed);
            self.close_ite_semantics(term, changed);
        }
    }

    fn close_not_semantics(&mut self, term: TermId, changed: &mut bool) {
        let TermData::Not(inner) = self.terms.get(term) else {
            return;
        };
        let node = self.node(term);
        let inner_node = self.node(*inner);
        let (inner_root, node_root) = (self.find(inner_node), self.find(node));
        if inner_root == self.find(TRUE_NODE) {
            *changed |= self.union(node, FALSE_NODE);
        }
        if inner_root == self.find(FALSE_NODE) {
            *changed |= self.union(node, TRUE_NODE);
        }
        if node_root == self.find(TRUE_NODE) {
            *changed |= self.union(inner_node, FALSE_NODE);
        }
        if node_root == self.find(FALSE_NODE) {
            *changed |= self.union(inner_node, TRUE_NODE);
        }
    }

    fn close_equality_semantics(&mut self, term: TermId, changed: &mut bool) {
        let Some((first, second)) = equality_sides(self.terms, term) else {
            return;
        };
        let node = self.node(term);
        let (first_node, second_node) = (self.node(first), self.node(second));
        if self.find(first_node) == self.find(second_node) {
            *changed |= self.union(node, TRUE_NODE);
        }
        let root = self.find(node);
        if root == self.find(TRUE_NODE) {
            *changed |= self.union(first_node, second_node);
        }
        if root == self.find(FALSE_NODE) && self.eq_false_seen.insert(term) {
            self.diseqs.push((first_node, second_node));
            *changed = true;
        }
    }

    /// Propagate `and` and `or` facts in both truth-table directions.
    fn close_nary_boolean_semantics(&mut self, term: TermId, changed: &mut bool) {
        let TermData::App(Symbol::Named(name), args) = self.terms.get(term) else {
            return;
        };
        let is_and = name == "and";
        if (!is_and && name != "or") || args.is_empty() {
            return;
        }
        let children = args.clone();
        let node = self.node(term);

        // For `and`, the unit polarity is TRUE and the absorbing polarity is
        // FALSE; `or` is the dual. Root comparisons remain live because a
        // union within this rule can move them.
        let (unit_pole, absorb_pole) = if is_and {
            (TRUE_NODE, FALSE_NODE)
        } else {
            (FALSE_NODE, TRUE_NODE)
        };
        if self.find(node) == self.find(unit_pole) {
            for &child in &children {
                let child_node = self.node(child);
                *changed |= self.union(child_node, unit_pole);
            }
        }

        let mut all_unit = true;
        let mut absorbed = false;
        let mut undetermined = None;
        let mut multiple_undetermined = false;
        for &child in &children {
            let child_node = self.node(child);
            if self.find(child_node) == self.find(absorb_pole) {
                *changed |= self.union(node, absorb_pole);
                absorbed = true;
                all_unit = false;
                break;
            }
            if self.find(child_node) != self.find(unit_pole) {
                all_unit = false;
                if undetermined.replace(child).is_some() {
                    multiple_undetermined = true;
                }
            }
        }
        if all_unit {
            *changed |= self.union(node, unit_pole);
        } else if !absorbed && !multiple_undetermined && self.find(node) == self.find(absorb_pole) {
            if let Some(last) = undetermined {
                let last_node = self.node(last);
                *changed |= self.union(last_node, absorb_pole);
            }
        }
    }

    /// Select an ITE branch or infer its condition from a contradictory arm.
    fn close_ite_semantics(&mut self, term: TermId, changed: &mut bool) {
        let TermData::Ite(condition, then_branch, else_branch) = self.terms.get(term) else {
            return;
        };
        let (condition, then_branch, else_branch) = (*condition, *then_branch, *else_branch);
        let node = self.node(term);
        let condition_node = self.node(condition);
        let then_node = self.node(then_branch);
        let else_node = self.node(else_branch);
        if self.find(condition_node) == self.find(TRUE_NODE) {
            *changed |= self.union(node, then_node);
        }
        if self.find(condition_node) == self.find(FALSE_NODE) {
            *changed |= self.union(node, else_node);
        }
        if self.find(then_node) == self.find(else_node) {
            *changed |= self.union(node, then_node);
        }

        // If the ITE's value contradicts one arm, the other arm was selected.
        let node_true = self.find(node) == self.find(TRUE_NODE);
        let node_false = self.find(node) == self.find(FALSE_NODE);
        let then_true = self.find(then_node) == self.find(TRUE_NODE);
        let then_false = self.find(then_node) == self.find(FALSE_NODE);
        let else_true = self.find(else_node) == self.find(TRUE_NODE);
        let else_false = self.find(else_node) == self.find(FALSE_NODE);
        if (node_true && then_false) || (node_false && then_true) {
            *changed |= self.union(condition_node, FALSE_NODE);
        }
        if (node_true && else_false) || (node_false && else_true) {
            *changed |= self.union(condition_node, TRUE_NODE);
        }
    }
}

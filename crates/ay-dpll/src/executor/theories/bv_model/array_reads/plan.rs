// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

impl Recovery<'_> {
    pub(in crate::executor::theories::bv_model) fn plan(
        &mut self,
        root: TermId,
        dependencies: &mut HashSet<TermId>,
    ) -> Option<Plan> {
        let mut plan = Plan { reads: Vec::new() };
        self.visit(
            root,
            0,
            dependencies,
            &mut HashMap::default(),
            &mut HashSet::default(),
            &mut plan,
        )?;
        Some(plan)
    }

    fn visit(
        &mut self,
        term: TermId,
        depth: usize,
        dependencies: &mut HashSet<TermId>,
        done: &mut HashMap<TermId, bool>,
        active: &mut HashSet<TermId>,
        plan: &mut Plan,
    ) -> Option<bool> {
        self.spend(1)?;
        self.live(term)?;
        if let Some(&expanded) = done.get(&term) {
            return Some(expanded);
        }
        if depth >= MAX_DEPTH || !active.insert(term) {
            return None;
        }
        let terms = self.terms;
        let mut expanded = false;
        match terms.get(term) {
            TermData::Var(_, _) => {
                if let Some(&definition) = self.definitions.get(&term) {
                    self.live(definition)?;
                    if terms.sort(term) != terms.sort(definition) {
                        return None;
                    }
                    if matches!(terms.sort(term), Sort::Array(_)) {
                        self.visit(definition, depth + 1, dependencies, done, active, plan)?;
                        expanded = true;
                    } else {
                        dependencies.insert(term);
                    }
                }
            }
            TermData::Const(_) => {}
            TermData::App(_, args) => {
                self.spend(args.len())?;
                let mut receiver_expanded = false;
                for (index, &child) in args.iter().enumerate() {
                    let changed = self.visit(child, depth + 1, dependencies, done, active, plan)?;
                    if index == 0 {
                        receiver_expanded = changed;
                    }
                    expanded |= changed;
                }
                if receiver_expanded
                    && matches!(terms.get(term),
                    TermData::App(symbol, _) if symbol.name() == "select")
                {
                    // Raw metadata is authenticated at acquisition. Indexed
                    // lookalikes cannot fall through to a stale read cache.
                    plan.reads.push(term);
                }
            }
            TermData::Not(child) => {
                expanded = self.visit(*child, depth + 1, dependencies, done, active, plan)?;
            }
            TermData::Ite(condition, left, right) => {
                for child in [*condition, *left, *right] {
                    expanded |= self.visit(child, depth + 1, dependencies, done, active, plan)?;
                }
            }
            // No substitution across lexical scopes in this data-only helper.
            _ => return None,
        }
        active.remove(&term);
        done.insert(term, expanded);
        Some(expanded)
    }

    pub(super) fn mentions_substituted(
        &mut self,
        root: TermId,
        variables: &HashSet<TermId>,
    ) -> Option<bool> {
        let mut stack = vec![root];
        let mut visited = HashSet::default();
        let terms = self.terms;
        while let Some(term) = stack.pop() {
            self.spend(1)?;
            self.live(term)?;
            if !visited.insert(term) {
                continue;
            }
            match terms.get(term) {
                TermData::Var(_, _) if variables.contains(&term) => return Some(true),
                TermData::Var(_, _) | TermData::Const(_) => {}
                TermData::App(_, args) => {
                    self.spend(args.len())?;
                    stack.extend(args);
                }
                TermData::Not(child) => stack.push(*child),
                TermData::Ite(c, t, e) => stack.extend([*c, *t, *e]),
                _ => return None,
            }
        }
        Some(false)
    }
}

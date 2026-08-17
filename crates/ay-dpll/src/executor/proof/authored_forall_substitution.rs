// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Capture-safe producer hints shared by the authored quantifier lanes.

use std::collections::{HashMap, HashSet};

use super::*;

const MAX_SUBST_WORK: usize = 20_000;

struct StructuralSubstitution<'a> {
    binder_name: &'a str,
    value: TermId,
    value_names: HashSet<String>,
    work: usize,
    memo: HashMap<TermId, Option<TermId>>,
}

impl StructuralSubstitution<'_> {
    fn walk(&mut self, terms: &mut TermStore, term: TermId) -> Option<TermId> {
        if let Some(&cached) = self.memo.get(&term) {
            return cached;
        }
        self.work += 1;
        if self.work > MAX_SUBST_WORK {
            return None;
        }
        let sort = terms.sort(term).clone();
        let rebuilt = match terms.get(term).clone() {
            TermData::Var(name, _) if name == self.binder_name => {
                (terms.sort(self.value) == &sort).then_some(self.value)
            }
            TermData::Var(..) | TermData::Const(..) => Some(term),
            TermData::Not(inner) => {
                let inner = self.walk(terms, inner)?;
                Some(terms.mk_not_raw(inner))
            }
            TermData::Ite(condition, then_branch, else_branch) => {
                self.rebuild_ite(terms, condition, then_branch, else_branch)
            }
            TermData::App(symbol, args) => self.rebuild_app(terms, symbol, args, sort),
            TermData::Forall(bindings, body, triggers) => {
                self.rebuild_quantifier(terms, term, bindings, body, triggers, true)
            }
            TermData::Exists(bindings, body, triggers) => {
                self.rebuild_quantifier(terms, term, bindings, body, triggers, false)
            }
            TermData::Let(..) => None,
            _ => None,
        };
        self.memo.insert(term, rebuilt);
        rebuilt
    }

    fn rebuild_ite(
        &mut self,
        terms: &mut TermStore,
        condition: TermId,
        then_branch: TermId,
        else_branch: TermId,
    ) -> Option<TermId> {
        let condition = self.walk(terms, condition)?;
        let then_branch = self.walk(terms, then_branch)?;
        let else_branch = self.walk(terms, else_branch)?;
        Some(terms.mk_ite_raw(condition, then_branch, else_branch))
    }

    fn rebuild_app(
        &mut self,
        terms: &mut TermStore,
        symbol: Symbol,
        args: Vec<TermId>,
        sort: Sort,
    ) -> Option<TermId> {
        let rebuilt = args
            .into_iter()
            .map(|arg| self.walk(terms, arg))
            .collect::<Option<Vec<_>>>()?;
        Some(terms.mk_app(symbol, rebuilt, sort))
    }

    fn rebuild_quantifier(
        &mut self,
        terms: &mut TermStore,
        original: TermId,
        bindings: Vec<(String, Sort)>,
        body: TermId,
        triggers: Vec<Vec<TermId>>,
        is_forall: bool,
    ) -> Option<TermId> {
        if bindings.iter().any(|(name, _)| name == self.binder_name) {
            return Some(original);
        }
        if bindings
            .iter()
            .any(|(name, _)| self.value_names.contains(name))
        {
            return None;
        }
        let body = self.walk(terms, body)?;
        let triggers = triggers
            .into_iter()
            .map(|trigger| {
                trigger
                    .into_iter()
                    .map(|item| self.walk(terms, item))
                    .collect::<Option<Vec<_>>>()
            })
            .collect::<Option<Vec<_>>>()?;
        if is_forall {
            Some(terms.mk_forall_with_triggers(bindings, body, triggers))
        } else {
            Some(terms.mk_exists_with_triggers(bindings, body, triggers))
        }
    }
}

fn argument_var_names(terms: &TermStore, root: TermId) -> Option<HashSet<String>> {
    let mut names = HashSet::new();
    let mut seen = HashSet::new();
    let mut stack = vec![root];
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if seen.len() > MAX_SUBST_WORK {
            return None;
        }
        match terms.get(term) {
            TermData::Var(name, _) => {
                names.insert(name.clone());
            }
            TermData::Const(..) => {}
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(condition, then_branch, else_branch) => {
                stack.extend([*condition, *then_branch, *else_branch]);
            }
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Let(..) | TermData::Forall(..) | TermData::Exists(..) => return None,
            _ => return None,
        }
    }
    Some(names)
}

impl Executor {
    /// Producer-side hint: ground authored subterms of the requested sort.
    /// The walk stops at binders; the strict checker decides every proposal.
    pub(super) fn ground_instantiation_candidates(
        terms: &TermStore,
        authored: &[TermId],
        sort: &Sort,
        limit: usize,
    ) -> Vec<TermId> {
        const MAX_SCAN_WORK: usize = 20_000;
        let mut found = Vec::new();
        let mut seen = HashSet::new();
        let mut stack = authored.to_vec();
        while let Some(term) = stack.pop() {
            if !seen.insert(term) {
                continue;
            }
            if seen.len() > MAX_SCAN_WORK || found.len() >= limit {
                break;
            }
            if terms.sort(term) == sort {
                found.push(term);
            }
            match terms.get(term) {
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(condition, then_branch, else_branch) => {
                    stack.extend([*condition, *then_branch, *else_branch]);
                }
                _ => {}
            }
        }
        found
    }

    /// Build the literal raw substitution accepted by `forall_inst` without
    /// simplifying any rebuilt node. Nested binders are preserved only when
    /// the replacement cannot be captured; `let` remains unsupported.
    pub(super) fn substitute_single_binder_structurally(
        terms: &mut TermStore,
        body: TermId,
        binder_name: &str,
        value: TermId,
    ) -> Option<TermId> {
        let mut substitution = StructuralSubstitution {
            binder_name,
            value,
            value_names: argument_var_names(terms, value)?,
            work: 0,
            memo: HashMap::new(),
        };
        let instance = substitution.walk(terms, body)?;
        (terms.sort(instance) == &Sort::Bool).then_some(instance)
    }
}

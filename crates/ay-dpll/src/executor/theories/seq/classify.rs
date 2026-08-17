// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Fail-closed classification of terms on sequence routes.

use super::super::super::Executor;
use super::scan::SUPPORTED_SEQ_OPS;
use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::{Symbol, TermData, TermId};

impl Executor {
    /// Check whether any assertion contains a `seq.len` application.
    pub(super) fn assertions_contain_seq_len(&self) -> bool {
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        let mut visited = HashSet::default();
        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }
            match self.ctx.terms.get(term) {
                TermData::App(Symbol::Named(name), args) => {
                    if name == "seq.len" {
                        return true;
                    }
                    stack.extend(args.iter().copied());
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => stack.extend([*c, *t, *e]),
                _ => {}
            }
        }
        false
    }

    pub(super) fn assertions_contain_native_seq_ops(&self) -> bool {
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        let mut visited = HashSet::default();
        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }
            match self.ctx.terms.get(term) {
                TermData::App(Symbol::Named(name), args) => {
                    if name.starts_with("seq.") {
                        return true;
                    }
                    stack.extend(args.iter().copied());
                }
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Let(bindings, body) => {
                    stack.extend(bindings.iter().map(|(_, binding)| *binding));
                    stack.push(*body);
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => stack.extend([*c, *t, *e]),
                TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                    stack.push(*body);
                    stack.extend(triggers.iter().flatten().copied());
                }
                _ => {}
            }
        }
        false
    }

    /// Check whether live assertions contain active datatype operations.
    pub(in crate::executor) fn assertions_contain_datatype_terms(&self) -> bool {
        self.terms_contain_datatype_terms(&self.ctx.assertions)
    }

    pub(in crate::executor) fn terms_contain_datatype_terms(&self, roots: &[TermId]) -> bool {
        let mut stack: Vec<TermId> = roots.to_vec();
        let mut visited = HashSet::default();
        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }
            match self.ctx.terms.get(term) {
                TermData::App(sym, args) => {
                    if self.is_datatype_symbol_name(sym.name()) {
                        return true;
                    }
                    stack.extend(args.iter().copied());
                }
                TermData::Var(name, _) if self.ctx.is_constructor(name).is_some() => return true,
                TermData::Let(bindings, body) => {
                    stack.extend(bindings.iter().map(|(_, binding)| *binding));
                    stack.push(*body);
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => stack.extend([*c, *t, *e]),
                TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                    stack.push(*body);
                    stack.extend(triggers.iter().flatten().copied());
                }
                _ => {}
            }
        }
        false
    }

    fn is_datatype_symbol_name(&self, name: &str) -> bool {
        if self.ctx.is_constructor(name).is_some()
            || name
                .strip_prefix("is-")
                .is_some_and(|ctor| self.ctx.is_constructor(ctor).is_some())
        {
            return true;
        }
        self.ctx
            .ctor_selectors_iter()
            .any(|(_, selectors)| selectors.iter().any(|selector| selector == name))
    }

    /// Detect unsupported sequence operations and sequence-sorted ITE inputs.
    pub(in crate::executor) fn assertions_contain_unsupported_seq_ops(&self) -> bool {
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        let mut visited = HashSet::default();
        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }
            match self.ctx.terms.get(term) {
                TermData::App(Symbol::Named(name), args) => {
                    if name.starts_with("seq.")
                        && (!SUPPORTED_SEQ_OPS.contains(&name.as_str())
                            || args.iter().any(|&arg| {
                                matches!(self.ctx.terms.get(arg), TermData::Ite(..))
                                    && self.ctx.terms.sort(arg).is_seq()
                            }))
                    {
                        return true;
                    }
                    stack.extend(args.iter().copied());
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => stack.extend([*c, *t, *e]),
                _ => {}
            }
        }
        false
    }
}

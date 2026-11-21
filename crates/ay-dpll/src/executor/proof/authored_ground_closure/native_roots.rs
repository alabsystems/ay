// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Native API rows retain their exact authored term, rather than an SMT AST.
//! The placeholder is a row marker, never a new premise or a symbol lookup.

use super::*;

pub(super) fn is_native_row(surface: &FrontendTerm) -> bool {
    matches!(
        crate::executor::proof_surface_syntax::strip_frontend_annotations(surface),
        FrontendTerm::Symbol(name) if name == crate::executor::NATIVE_API_ASSERTION_PLACEHOLDER
    )
}

impl Executor {
    pub(super) fn native_ground_closure_roots(
        &self,
        parsed: &[FrontendTerm],
        scope: &[TermId],
    ) -> Option<Vec<TermId>> {
        // Preserve the old SMT-row bound. Only repeated native rows may use
        // the larger bounded row window; their distinct root bound is 64.
        if parsed.len() > MAX_AUTHORED_ROOTS && !parsed.iter().all(is_native_row) {
            return None;
        }
        if !parsed.iter().any(is_native_row) {
            return Some(Vec::new());
        }
        let authored = self
            .ctx
            .concrete_authored_assertion_terms_aligned_bounded(MAX_NATIVE_AUTHORED_ROWS)?;
        if authored.len() != parsed.len() {
            return None;
        }
        let mut roots = Vec::new();
        for (row, root) in parsed.iter().zip(authored) {
            if !is_native_row(row) || self.mentions_source_macro(row) {
                continue;
            }
            if self.ctx.terms.sort(root) != &Sort::Bool
                || !scope.contains(&root)
                || !self.is_bounded_native_ground_root(root)
            {
                continue;
            }
            if !roots.contains(&root) {
                if roots.len() >= MAX_AUTHORED_ROOTS {
                    return None;
                }
                roots.push(root);
            }
        }
        Some(roots)
    }

    fn is_bounded_native_ground_root(&self, root: TermId) -> bool {
        let mut pending = vec![root];
        let mut work = MAX_NODES;
        while let Some(term) = pending.pop() {
            let Some(remaining) = work.checked_sub(1) else {
                return false;
            };
            work = remaining;
            let children: &[TermId] = match self.ctx.terms.get(term) {
                TermData::Forall(..) | TermData::Exists(..) | TermData::Let(..) => return false,
                TermData::App(_, args) => args,
                TermData::Not(inner) => std::slice::from_ref(inner),
                TermData::Ite(c, t, e) => {
                    if pending.len() + 3 > work {
                        return false;
                    }
                    pending.extend([*c, *t, *e]);
                    continue;
                }
                _ => &[],
            };
            if pending.len() + children.len() > work {
                return false;
            }
            pending.extend(children.iter().copied());
        }
        true
    }
}

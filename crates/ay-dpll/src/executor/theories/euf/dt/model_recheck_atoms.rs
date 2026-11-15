// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The equalities the post-`Sat` D0 model recheck merges
//! ([`Executor::dt_model_egraph_recheck`]).
//!
//! Only GROUND datatype equalities are facts of the decoded model. The eager
//! datatype axioms range over every datatype-sorted term in the store, including
//! ones inside a quantifier body, so the SAT layer can hold a variable for an
//! atom such as `(= self (Cons a_6 b_7))` whose `a_6`/`b_7` are a quantifier's
//! binders. A clash lemma derived from such an atom is theory-valid, but the
//! recheck appends it to the assertions, where it asserts the binders FREE:
//! the binder/free-constant identity that Option C of
//! the development design notes removes at
//! its source, and that the E-matching ground-index canary (LI-1/LI-2) rejects.
//! Leaving such an atom out can only MISS a conflict — fail-open for that atom,
//! exactly as for an atom the SAT layer never saw — and a genuine clash of the
//! ground model is still found among its ground atoms.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Symbol, TermData};
use ay_core::{Sort, TermId, TermStore};

use super::super::super::super::Executor;

impl Executor {
    /// Every binder-free datatype-sorted equality that is asserted as a
    /// top-level unit or TRUE in the SAT model, in ascending `TermId` order.
    pub(super) fn dt_model_true_ground_equalities(
        &self,
        sat_model: &[bool],
        term_to_var: &HashMap<TermId, u32>,
    ) -> Vec<TermId> {
        // Datatype sort names (internal, possibly instance-mangled).
        let dt_names: HashSet<String> = self
            .ctx
            .datatype_iter()
            .map(|(name, _)| name.to_string())
            .collect();
        let is_dt_sort = |sort: &Sort| match sort {
            Sort::Datatype(dt) => dt_names.contains(&dt.name),
            Sort::Uninterpreted(name) => dt_names.contains(name),
            _ => false,
        };
        let binds_a_binder = terms_mentioning_a_binder(&self.ctx.terms);

        // Asserted top-level units are true in every accepted model; everything
        // else reads the SAT assignment (this is where the axiom-(C)
        // instantiation equalities `t = C(sel_1 t, ...)` the bit-blast core
        // decided live). An atom the SAT layer never saw is skipped — fewer
        // merges can only MISS a conflict (fail-open for that atom; the
        // always-on gates remain the backstop), never invent one.
        let asserted: HashSet<TermId> = self.ctx.assertions.iter().copied().collect();
        let mut true_eqs: Vec<TermId> = Vec::new();
        for (raw, &mentions_binder) in binds_a_binder.iter().enumerate() {
            let tid = TermId(raw as u32);
            let TermData::App(Symbol::Named(sym), args) = self.ctx.terms.get(tid) else {
                continue;
            };
            if sym.as_str() != "="
                || args.len() != 2
                || !is_dt_sort(self.ctx.terms.sort(args[0]))
                || mentions_binder
            {
                continue;
            }
            let truth = if asserted.contains(&tid) {
                Some(true)
            } else {
                self.term_value(sat_model, term_to_var, tid)
            };
            if truth == Some(true) {
                true_eqs.push(tid);
            }
        }
        true_eqs
    }
}

/// For every term of the store, whether it mentions a variable some quantifier
/// in the store binds (by name, the binding discipline). One pass in `TermId`
/// order: interning creates every child before its parent, and a child that is
/// NOT older than its parent — never produced by the interner — is counted as
/// mentioning a binder, the conservative answer for this filter.
fn terms_mentioning_a_binder(terms: &TermStore) -> Vec<bool> {
    let mut binders: HashSet<&str> = HashSet::default();
    for id in terms.term_ids() {
        if let TermData::Forall(vars, _, _) | TermData::Exists(vars, _, _) = terms.get(id) {
            binders.extend(vars.iter().map(|(name, _)| name.as_str()));
        }
    }
    let mut mentions: Vec<bool> = Vec::with_capacity(terms.len());
    for raw in 0..terms.len() {
        let child = |id: &TermId| mentions.get(id.0 as usize).is_none_or(|&m| m);
        let mentions_binder = match terms.get(TermId(raw as u32)) {
            TermData::Var(name, _) => binders.contains(name.as_str()),
            TermData::Const(_) => false,
            TermData::App(_, args) => args.iter().any(child),
            TermData::Not(inner) => child(inner),
            TermData::Ite(c, t, e) => [c, t, e].into_iter().any(child),
            TermData::Let(bindings, body) => {
                bindings.iter().any(|(_, value)| child(value)) || child(body)
            }
            TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => child(body),
            _ => true,
        };
        mentions.push(mentions_binder);
    }
    mentions
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The recheck's filter: `(= self b)` under `forall b` is not a model
    /// fact, `(= self nil)` is — and the verdict is per term, not per root.
    #[test]
    fn only_terms_reaching_a_binder_spelling_are_marked() {
        let mut terms = TermStore::new();
        let list = Sort::Uninterpreted("List".to_string());
        let receiver = terms.mk_var("self", list.clone());
        let nil = terms.mk_var("nil", list.clone());
        let bound = terms.mk_fresh_var("b", list.clone());
        let TermData::Var(bound_name, _) = terms.get(bound).clone() else {
            unreachable!("mk_fresh_var mints a Var");
        };
        let under_binder = terms.mk_eq(receiver, bound);
        let quantifier = terms.mk_forall(vec![(bound_name, list)], under_binder);
        let ground = terms.mk_eq(receiver, nil);

        let marks = terms_mentioning_a_binder(&terms);
        assert_eq!(marks.len(), terms.len());
        for (term, expected) in [
            (receiver, false),
            (nil, false),
            (ground, false),
            (bound, true),
            (under_binder, true),
            (quantifier, true),
        ] {
            assert_eq!(marks[term.0 as usize], expected, "term {term:?}");
        }
    }
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Recursive workers copied from the pre-patch source, with renamed workers.
//! Used solely for shallow exact-ID and interner-order parity controls.

use super::super::*;

pub(super) fn simplify(store: &mut TermStore, term: TermId) -> TermId {
    let mut cache = crate::kani_compat::det_hash_map_new();
    store.postorder_oracle_simplify_inner(term, &mut cache)
}

pub(super) fn substitute(
    store: &mut TermStore,
    term: TermId,
    from: &[TermId],
    to: &[TermId],
) -> TermId {
    if from.is_empty() || to.is_empty() {
        return term;
    }
    let mut cache = crate::kani_compat::det_hash_map_new();
    store.postorder_oracle_substitute_inner(term, from, to, &mut cache)
}

impl TermStore {
    fn postorder_oracle_simplify_inner(
        &mut self,
        term: TermId,
        cache: &mut crate::kani_compat::DetHashMap<TermId, TermId>,
    ) -> TermId {
        if let Some(&cached) = cache.get(&term) {
            return cached;
        }

        let result = match self.get(term).clone() {
            TermData::Const(_) | TermData::Var(_, _) => term,
            TermData::App(sym, args) => {
                // Rebuild children first, then re-apply the folding constructor for
                // this operator. Even if no child changed, run it through
                // `rebuild_app` so a constant application that escaped eager
                // folding (e.g. a raw parser-built `(+ 2 3)`) collapses.
                let new_args: Vec<TermId> = args
                    .iter()
                    .map(|&arg| self.postorder_oracle_simplify_inner(arg, cache))
                    .collect();
                self.rebuild_app(&sym, new_args, term)
            }
            TermData::Not(inner) => {
                let new_inner = self.postorder_oracle_simplify_inner(inner, cache);
                self.mk_not(new_inner)
            }
            TermData::Ite(c, t, e) => {
                let nc = self.postorder_oracle_simplify_inner(c, cache);
                let nt = self.postorder_oracle_simplify_inner(t, cache);
                let ne = self.postorder_oracle_simplify_inner(e, cache);
                self.mk_ite(nc, nt, ne)
            }
            TermData::Let(bindings, body) => {
                let new_bindings: Vec<(String, TermId)> = bindings
                    .iter()
                    .map(|(name, val)| {
                        (
                            name.clone(),
                            self.postorder_oracle_simplify_inner(*val, cache),
                        )
                    })
                    .collect();
                let new_body = self.postorder_oracle_simplify_inner(body, cache);
                if new_bindings == bindings && new_body == body {
                    term
                } else {
                    let sort = self.sort(term).clone();
                    self.intern(TermData::Let(new_bindings, new_body), sort)
                }
            }
            TermData::Forall(vars, body, triggers) => {
                let new_body = self.postorder_oracle_simplify_inner(body, cache);
                if new_body == body {
                    term
                } else {
                    let sort = self.sort(term).clone();
                    let rebuilt = self.intern(TermData::Forall(vars, new_body, triggers), sort);
                    self.copy_quantifier_metadata(term, rebuilt);
                    rebuilt
                }
            }
            TermData::Exists(vars, body, triggers) => {
                let new_body = self.postorder_oracle_simplify_inner(body, cache);
                if new_body == body {
                    term
                } else {
                    let sort = self.sort(term).clone();
                    let rebuilt = self.intern(TermData::Exists(vars, new_body, triggers), sort);
                    self.copy_quantifier_metadata(term, rebuilt);
                    rebuilt
                }
            }
        };

        cache.insert(term, result);
        result
    }

    // Direct hit: replace WITHOUT recursing into the replacement
    // (simultaneous semantics). Checked first so a top-level match wins.
    // `zip` honors only the common prefix, so unequal `from`/`to` lengths
    // need no pre-truncation.
    fn postorder_oracle_substitute_inner(
        &mut self,
        term: TermId,
        from: &[TermId],
        to: &[TermId],
        cache: &mut crate::kani_compat::DetHashMap<TermId, TermId>,
    ) -> TermId {
        for (&f, &t) in from.iter().zip(to.iter()) {
            if term == f {
                return t;
            }
        }
        if let Some(&cached) = cache.get(&term) {
            return cached;
        }

        let result = match self.get(term).clone() {
            TermData::Const(_) | TermData::Var(_, _) => term,
            TermData::App(sym, args) => {
                let mut changed = false;
                let new_args: Vec<TermId> = args
                    .iter()
                    .map(|&arg| {
                        let new_arg = self.postorder_oracle_substitute_inner(arg, from, to, cache);
                        changed |= new_arg != arg;
                        new_arg
                    })
                    .collect();
                if changed {
                    self.rebuild_app(&sym, new_args, term)
                } else {
                    term
                }
            }
            TermData::Not(inner) => {
                let new_inner = self.postorder_oracle_substitute_inner(inner, from, to, cache);
                if new_inner != inner {
                    self.mk_not(new_inner)
                } else {
                    term
                }
            }
            TermData::Ite(c, t, e) => {
                let nc = self.postorder_oracle_substitute_inner(c, from, to, cache);
                let nt = self.postorder_oracle_substitute_inner(t, from, to, cache);
                let ne = self.postorder_oracle_substitute_inner(e, from, to, cache);
                if nc != c || nt != t || ne != e {
                    self.mk_ite(nc, nt, ne)
                } else {
                    term
                }
            }
            TermData::Let(bindings, body) => {
                self.postorder_oracle_substitute_let(term, bindings, body, (from, to), cache)
            }
            TermData::Forall(vars, body, triggers) => {
                let new_body = self.postorder_oracle_substitute_inner(body, from, to, cache);
                if new_body != body {
                    let sort = self.sort(term).clone();
                    let rebuilt = self.intern(TermData::Forall(vars, new_body, triggers), sort);
                    self.copy_quantifier_metadata(term, rebuilt);
                    rebuilt
                } else {
                    term
                }
            }
            TermData::Exists(vars, body, triggers) => {
                let new_body = self.postorder_oracle_substitute_inner(body, from, to, cache);
                if new_body != body {
                    let sort = self.sort(term).clone();
                    let rebuilt = self.intern(TermData::Exists(vars, new_body, triggers), sort);
                    self.copy_quantifier_metadata(term, rebuilt);
                    rebuilt
                } else {
                    term
                }
            }
        };

        cache.insert(term, result);
        result
    }

    fn postorder_oracle_substitute_let(
        &mut self,
        term: TermId,
        bindings: Vec<(String, TermId)>,
        body: TermId,
        substitution: (&[TermId], &[TermId]),
        cache: &mut crate::kani_compat::DetHashMap<TermId, TermId>,
    ) -> TermId {
        let (from, to) = substitution;
        let mut changed = false;
        let new_bindings: Vec<(String, TermId)> = bindings
            .iter()
            .map(|(name, val)| {
                let new_val = self.postorder_oracle_substitute_inner(*val, from, to, cache);
                changed |= new_val != *val;
                (name.clone(), new_val)
            })
            .collect();
        let new_body = self.postorder_oracle_substitute_inner(body, from, to, cache);
        changed |= new_body != body;
        if changed {
            let sort = self.sort(term).clone();
            self.intern(TermData::Let(new_bindings, new_body), sort)
        } else {
            term
        }
    }
}

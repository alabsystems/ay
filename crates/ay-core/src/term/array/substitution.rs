// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Lexical alpha-renaming for the single-variable substitution primitive.

use super::*;

fn replacement_matches(
    terms: &TermStore,
    root: TermId,
    matches: impl Fn(TermId, &TermData) -> bool,
) -> (bool, bool) {
    let mut pending = vec![root];
    let mut available = true;
    let mut visited = crate::kani_compat::det_hash_set_new();
    while let Some(term) = pending.pop() {
        // Quantifier hint metadata can carry sentinel IDs. It contributes no
        // logical variables and must remain intact when it is unavailable.
        if terms.entry_stamp(term).is_none() {
            available = false;
            continue;
        }
        if !visited.insert(term) {
            continue;
        }
        let data = terms.get(term);
        if matches(term, data) {
            return (true, available);
        }
        match data {
            TermData::Const(_) | TermData::Var(_, _) => {}
            TermData::App(_, args) => pending.extend(args),
            TermData::Not(inner) => pending.push(*inner),
            TermData::Ite(a, b, c) => pending.extend([*a, *b, *c]),
            TermData::Let(bindings, body) => {
                pending.extend(bindings.iter().map(|(_, value)| *value));
                pending.push(*body);
            }
            TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                pending.push(*body);
                pending.extend(triggers.iter().flatten().copied());
                pending.extend(terms.quantifier_no_patterns(term));
            }
        }
    }
    (false, available)
}

pub(super) fn annotation_is_available(terms: &TermStore, root: TermId) -> bool {
    replacement_matches(terms, root, |_, _| false).1
}

pub(super) fn replacement_contains_term(terms: &TermStore, root: TermId, needle: TermId) -> bool {
    replacement_matches(terms, root, |term, _| term == needle).0
}

pub(super) fn replacement_contains_name(terms: &TermStore, root: TermId, name: &str) -> bool {
    replacement_matches(terms, root, |_, data| match data {
        TermData::Var(candidate, _) => candidate == name,
        TermData::Let(bindings, _) => bindings.iter().any(|(bound, _)| bound == name),
        TermData::Forall(bindings, _, _) | TermData::Exists(bindings, _, _) => {
            bindings.iter().any(|(bound, _)| bound == name)
        }
        _ => false,
    })
    .0
}

impl TermStore {
    pub(super) fn fresh_substitution_binder(
        &mut self,
        prefix: &str,
        sort: &Sort,
        roots: &[TermId],
    ) -> TermId {
        loop {
            let fresh = self.mk_fresh_var(prefix, sort.clone());
            let TermData::Var(name, _) = self.get(fresh) else {
                unreachable!("fresh bound variable");
            };
            // Unused SMT binder names need not be in the variable-name table.
            if roots
                .iter()
                .all(|&root| !replacement_contains_name(self, root, name))
            {
                return fresh;
            }
        }
    }

    pub(super) fn rebuild_substituted_quantifier(
        &mut self,
        original: TermId,
        mut bindings: Vec<(String, Sort)>,
        mut body: TermId,
        mut triggers: Vec<Vec<TermId>>,
        mut no_patterns: Vec<TermId>,
    ) -> TermId {
        let same_structure = match self.get(original) {
            TermData::Forall(old, old_body, old_triggers)
            | TermData::Exists(old, old_body, old_triggers) => {
                old == &bindings && *old_body == body && old_triggers == &triggers
            }
            _ => return original,
        };
        if same_structure {
            if self.quantifier_no_patterns(original) == no_patterns {
                return original;
            }
            // Metadata is keyed by interned term identity. Give changed
            // annotations an alpha-equivalent root before updating them.
            let mut roots = vec![original, body];
            roots.extend(triggers.iter().flatten());
            roots.extend(&no_patterns);
            let Some((bound_name, bound_sort)) = bindings.first_mut() else {
                // The native quantifier API requires a nonempty binder list.
                return original;
            };
            let local =
                self.fresh_substitution_binder("__ay_hint_substitution_bound", bound_sort, &roots);
            body = self.rename_bound_name(body, bound_name, bound_sort, local);
            for trigger in triggers.iter_mut().flatten() {
                *trigger = self.rename_bound_hint(*trigger, bound_name, bound_sort, local);
            }
            for pattern in &mut no_patterns {
                *pattern = self.rename_bound_hint(*pattern, bound_name, bound_sort, local);
            }
            let TermData::Var(local_name, _) = self.get(local) else {
                unreachable!("fresh bound variable");
            };
            *bound_name = local_name.clone();
        }
        let rebuilt = match self.get(original) {
            TermData::Forall(..) => self.mk_forall_with_triggers(bindings, body, triggers),
            _ => self.mk_exists_with_triggers(bindings, body, triggers),
        };
        self.copy_quantifier_metadata(original, rebuilt);
        if self.quantifier_no_patterns(rebuilt) != no_patterns {
            self.set_quantifier_no_patterns(rebuilt, no_patterns);
        }
        rebuilt
    }

    pub(super) fn rename_bound_hint(
        &mut self,
        term: TermId,
        name: &str,
        sort: &Sort,
        fresh: TermId,
    ) -> TermId {
        if annotation_is_available(self, term) {
            self.rename_bound_name(term, name, sort, fresh)
        } else {
            term
        }
    }

    fn rename_bound_hint_inner(
        &mut self,
        term: TermId,
        name: &str,
        sort: &Sort,
        fresh: TermId,
        excluded: &crate::kani_compat::DetHashSet<TermId>,
        cache: &mut crate::kani_compat::DetHashMap<TermId, TermId>,
    ) -> TermId {
        if annotation_is_available(self, term) {
            self.rename_bound_name_inner(term, name, sort, fresh, excluded, cache)
        } else {
            term
        }
    }

    /// Rename every occurrence owned by the surrounding SMT name binder.
    /// Exact lambda-bound IDs remain local even when they share this name.
    pub(super) fn rename_bound_name(
        &mut self,
        term: TermId,
        name: &str,
        sort: &Sort,
        fresh: TermId,
    ) -> TermId {
        let excluded = crate::kani_compat::det_hash_set_new();
        let mut cache = crate::kani_compat::det_hash_map_new();
        self.rename_bound_name_inner(term, name, sort, fresh, &excluded, &mut cache)
    }

    fn rename_bound_name_inner(
        &mut self,
        term: TermId,
        name: &str,
        sort: &Sort,
        fresh: TermId,
        excluded: &crate::kani_compat::DetHashSet<TermId>,
        cache: &mut crate::kani_compat::DetHashMap<TermId, TermId>,
    ) -> TermId {
        if self.entry_stamp(term).is_none() {
            return term;
        }
        if let Some(&cached) = cache.get(&term) {
            return cached;
        }
        let rewritten = match self.get(term).clone() {
            TermData::Const(_) => term,
            TermData::Var(candidate, _)
                if candidate == name && self.sort(term) == sort && !excluded.contains(&term) =>
            {
                fresh
            }
            TermData::Var(_, _) => term,
            TermData::App(Symbol::Named(symbol), args)
                if symbol == "lambda-array" && args.len() == 2 =>
            {
                let [binder, body] = [args[0], args[1]];
                let shadowing = matches!(self.get(binder), TermData::Var(candidate, _)
                    if candidate == name && self.sort(binder) == sort);
                let body = if shadowing {
                    let mut nested = excluded.clone();
                    nested.insert(binder);
                    // The same DAG node can be free outside this exact lambda.
                    let mut nested_cache = crate::kani_compat::det_hash_map_new();
                    self.rename_bound_name_inner(
                        body,
                        name,
                        sort,
                        fresh,
                        &nested,
                        &mut nested_cache,
                    )
                } else {
                    self.rename_bound_name_inner(body, name, sort, fresh, excluded, cache)
                };
                if body == args[1] {
                    term
                } else {
                    self.mk_lambda_array(binder, body)
                }
            }
            TermData::App(symbol, args) => {
                let rewritten: Vec<_> = args
                    .iter()
                    .map(|&arg| {
                        self.rename_bound_name_inner(arg, name, sort, fresh, excluded, cache)
                    })
                    .collect();
                if rewritten == args {
                    term
                } else {
                    self.rebuild_app(&symbol, rewritten, term)
                }
            }
            TermData::Not(inner) => {
                let new = self.rename_bound_name_inner(inner, name, sort, fresh, excluded, cache);
                if new == inner {
                    term
                } else {
                    self.mk_not(new)
                }
            }
            TermData::Ite(condition, then_term, else_term) => {
                let new_condition =
                    self.rename_bound_name_inner(condition, name, sort, fresh, excluded, cache);
                let new_then =
                    self.rename_bound_name_inner(then_term, name, sort, fresh, excluded, cache);
                let new_else =
                    self.rename_bound_name_inner(else_term, name, sort, fresh, excluded, cache);
                if (new_condition, new_then, new_else) == (condition, then_term, else_term) {
                    term
                } else {
                    self.mk_ite(new_condition, new_then, new_else)
                }
            }
            TermData::Let(bindings, body) => {
                let body = if bindings.iter().any(|(bound, _)| bound == name) {
                    body
                } else {
                    self.rename_bound_name_inner(body, name, sort, fresh, excluded, cache)
                };
                let bindings: Vec<_> = bindings
                    .into_iter()
                    .map(|(bound, value)| {
                        (
                            bound,
                            self.rename_bound_name_inner(value, name, sort, fresh, excluded, cache),
                        )
                    })
                    .collect();
                self.mk_let(bindings, body)
            }
            TermData::Forall(bindings, body, mut triggers)
            | TermData::Exists(bindings, body, mut triggers) => {
                if bindings.iter().any(|(bound, _)| bound == name) {
                    term
                } else {
                    let original_body = body;
                    let original_triggers = triggers.clone();
                    let body =
                        self.rename_bound_name_inner(body, name, sort, fresh, excluded, cache);
                    for trigger in triggers.iter_mut().flatten() {
                        *trigger = self
                            .rename_bound_hint_inner(*trigger, name, sort, fresh, excluded, cache);
                    }
                    let original_no_patterns = self.quantifier_no_patterns(term).to_vec();
                    let mut no_patterns = original_no_patterns.clone();
                    for pattern in &mut no_patterns {
                        *pattern = self
                            .rename_bound_hint_inner(*pattern, name, sort, fresh, excluded, cache);
                    }
                    if body == original_body
                        && triggers == original_triggers
                        && no_patterns == original_no_patterns
                    {
                        term
                    } else {
                        self.rebuild_substituted_quantifier(
                            term,
                            bindings,
                            body,
                            triggers,
                            no_patterns,
                        )
                    }
                }
            }
        };
        cache.insert(term, rewritten);
        rewritten
    }
}

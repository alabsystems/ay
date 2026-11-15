// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The term walks behind native binder separation (`binder_separation.rs`):
//! the spellings a twin must avoid, and the capture-avoiding renaming of one
//! binder's free occurrences to its twin.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::TermData;
use ay_core::{Sort, TermId, TermStore};

use super::HashSet;

/// The spelling of a `Var` node (empty for any other node, which no caller
/// passes: binders are validated as `Var`s first).
pub(super) fn var_name(terms: &TermStore, var: TermId) -> String {
    match terms.get(var) {
        TermData::Var(name, _) => name.clone(),
        _ => String::new(),
    }
}

/// Every spelling a twin must avoid: the binder list's names and every variable
/// or binder name reachable from `body` and `triggers`. `None` for a term kind
/// the walk does not know, which leaves the binder unseparated.
pub(super) fn names_in_scope(
    terms: &TermStore,
    var_ids: &[TermId],
    body: TermId,
    triggers: &[Vec<TermId>],
) -> Option<HashSet<String>> {
    let mut names: HashSet<String> = var_ids.iter().map(|&v| var_name(terms, v)).collect();
    let mut seen: HashSet<TermId> = HashSet::default();
    let mut stack: Vec<TermId> = vec![body];
    stack.extend(triggers.iter().flatten().copied());
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        match terms.get(term) {
            TermData::Var(name, _) => {
                names.insert(name.clone());
            }
            TermData::Const(_) => {}
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, t, e) => stack.extend([*c, *t, *e]),
            TermData::Let(bindings, inner) => {
                names.extend(bindings.iter().map(|(name, _)| name.clone()));
                stack.extend(bindings.iter().map(|(_, value)| *value));
                stack.push(*inner);
            }
            TermData::Forall(vars, inner, nested) | TermData::Exists(vars, inner, nested) => {
                names.extend(vars.iter().map(|(name, _)| name.clone()));
                stack.push(*inner);
                stack.extend(nested.iter().flatten().copied());
                stack.extend(terms.quantifier_no_patterns(term).iter().copied());
            }
            _ => return None,
        }
    }
    Some(names)
}

/// Capture-avoiding renaming of the free occurrences of one binder `from` (whose
/// spelling is `from_name`) to `to`, a variable whose spelling occurs nowhere
/// in the renamed term.
pub(super) struct Rename<'a> {
    pub(super) from: TermId,
    pub(super) from_name: &'a str,
    pub(super) to: TermId,
}

impl Rename<'_> {
    /// `None` for a term kind the walk does not know. A nested binder of the
    /// same spelling shadows `from`, so its scope is left untouched; nested
    /// triggers and no-patterns are renamed with their quantifier's body.
    pub(super) fn apply(
        &self,
        terms: &mut TermStore,
        term: TermId,
        cache: &mut HashMap<TermId, TermId>,
    ) -> Option<TermId> {
        if term == self.from {
            return Some(self.to);
        }
        if let Some(&done) = cache.get(&term) {
            return Some(done);
        }
        let renamed = match terms.get(term).clone() {
            TermData::Const(_) | TermData::Var(_, _) => term,
            TermData::App(symbol, args) => {
                let new_args = self.apply_all(terms, &args, cache)?;
                if new_args == args {
                    term
                } else {
                    terms.rebuild_app(&symbol, new_args, term)
                }
            }
            TermData::Not(inner) => {
                let new_inner = self.apply(terms, inner, cache)?;
                if new_inner == inner {
                    term
                } else {
                    terms.mk_not(new_inner)
                }
            }
            TermData::Ite(c, t, e) => {
                let new = self.apply_all(terms, &[c, t, e], cache)?;
                if new == [c, t, e] {
                    term
                } else {
                    terms.mk_ite(new[0], new[1], new[2])
                }
            }
            TermData::Let(bindings, inner) => {
                let values: Vec<TermId> = bindings.iter().map(|(_, value)| *value).collect();
                let new_values = self.apply_all(terms, &values, cache)?;
                let shadowed = bindings.iter().any(|(name, _)| name == self.from_name);
                let new_inner = if shadowed {
                    inner
                } else {
                    self.apply(terms, inner, cache)?
                };
                if new_values == values && new_inner == inner {
                    term
                } else {
                    let new_bindings = bindings
                        .into_iter()
                        .zip(new_values)
                        .map(|((name, _), value)| (name, value))
                        .collect();
                    terms.mk_let(new_bindings, new_inner)
                }
            }
            TermData::Forall(vars, inner, nested) | TermData::Exists(vars, inner, nested) => {
                if vars.iter().any(|(name, _)| name == self.from_name) {
                    term
                } else {
                    self.apply_quantifier(terms, term, vars, inner, nested, cache)?
                }
            }
            _ => return None,
        };
        cache.insert(term, renamed);
        Some(renamed)
    }

    fn apply_all(
        &self,
        terms: &mut TermStore,
        items: &[TermId],
        cache: &mut HashMap<TermId, TermId>,
    ) -> Option<Vec<TermId>> {
        items
            .iter()
            .map(|&item| self.apply(terms, item, cache))
            .collect()
    }

    /// Rebuild a nested, non-shadowing quantifier with its body, triggers and
    /// no-patterns renamed, carrying its metadata over.
    fn apply_quantifier(
        &self,
        terms: &mut TermStore,
        term: TermId,
        vars: Vec<(String, Sort)>,
        inner: TermId,
        nested: Vec<Vec<TermId>>,
        cache: &mut HashMap<TermId, TermId>,
    ) -> Option<TermId> {
        let new_inner = self.apply(terms, inner, cache)?;
        let new_nested = nested
            .iter()
            .map(|multi| self.apply_all(terms, multi, cache))
            .collect::<Option<Vec<_>>>()?;
        let no_patterns = terms.quantifier_no_patterns(term).to_vec();
        let new_no_patterns = self.apply_all(terms, &no_patterns, cache)?;
        if new_inner == inner && new_nested == nested && new_no_patterns == no_patterns {
            return Some(term);
        }
        let rebuilt = if matches!(terms.get(term), TermData::Forall(..)) {
            terms.mk_forall_with_triggers(vars, new_inner, new_nested)
        } else {
            terms.mk_exists_with_triggers(vars, new_inner, new_nested)
        };
        terms.copy_quantifier_metadata(term, rebuilt);
        if new_no_patterns != no_patterns {
            terms.set_quantifier_no_patterns(rebuilt, new_no_patterns);
        }
        Some(rebuilt)
    }
}

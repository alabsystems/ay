// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Ground occurrences in the asserted term DAG.
//!
//! A `TermId` can occur both beneath a binder and outside it (notably through
//! the Z3-compatible C API, which preserves the caller's bound-constant AST).
//! Groundness is therefore a property of `(TermId, binder scope)`, not of the
//! id alone. The assertion roots, rather than every arena entry, define which
//! occurrences can supply ground candidates.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermData;
use ay_core::{Sort, TermId, TermStore};

use super::{EMATCH_STACK_RED_ZONE, EMATCH_STACK_SIZE};

type ScopeId = u32;

/// Persistent within a monotonically growing assertion round group. Reset it
/// when assertions can be retracted; the memo and accumulators are inseparable.
#[derive(Clone, Default)]
pub(super) struct GroundOccurrences {
    scope_ids: HashMap<Vec<String>, ScopeId>,
    ground_cache: HashMap<(u32, ScopeId), bool>,
    /// A term is admitted if *any asserted occurrence* is ground.
    pub(super) ground_ids: HashSet<u32>,
    /// Bound Var ids still serve as a conservative fallback for EUF model
    /// entries absent from the asserted occurrence walk.
    pub(super) bound_var_ids: HashSet<u32>,
    /// Ground Bool arguments at an uninterpreted-function application site.
    pub(super) bool_uf_args: HashSet<u32>,
    new_ground_apps: Vec<TermId>,
}

impl GroundOccurrences {
    /// Visit only asserted roots, starting each at the empty binder scope.
    pub(super) fn visit_assertions(&mut self, terms: &TermStore, assertions: &[TermId]) {
        for &root in assertions {
            let mut bound_names = HashSet::default();
            self.visit(terms, root, &mut bound_names, 0);
            debug_assert!(bound_names.is_empty());
        }
    }

    /// Drain Apps that acquired their first ground occurrence since the last
    /// drain. A second occurrence or round must not duplicate an index entry.
    pub(super) fn take_new_ground_apps(&mut self) -> Vec<TermId> {
        std::mem::take(&mut self.new_ground_apps)
    }

    fn scope_id(&mut self, bound_names: &HashSet<String>) -> ScopeId {
        if bound_names.is_empty() {
            return 0;
        }
        let mut names: Vec<String> = bound_names.iter().cloned().collect();
        names.sort_unstable();
        if let Some(&id) = self.scope_ids.get(&names) {
            return id;
        }
        let id = self.scope_ids.len() as ScopeId + 1;
        self.scope_ids.insert(names, id);
        id
    }

    fn visit(
        &mut self,
        terms: &TermStore,
        term: TermId,
        bound_names: &mut HashSet<String>,
        scope: ScopeId,
    ) -> bool {
        if let Some(&ground) = self.ground_cache.get(&(term.0, scope)) {
            return ground;
        }
        let ground = stacker::maybe_grow(EMATCH_STACK_RED_ZONE, EMATCH_STACK_SIZE, || {
            match terms.get(term) {
                TermData::Const(_) => true,
                TermData::Var(name, _) => {
                    // Match the solver's existing name-binding semantics. The
                    // frontend may suffix a binder's spelling for uniqueness.
                    let base_name = name.trim_end_matches(|c: char| c == '_' || c.is_ascii_digit());
                    let bound = bound_names.contains(name) || bound_names.contains(base_name);
                    if bound {
                        self.bound_var_ids.insert(term.0);
                    }
                    !bound
                }
                TermData::App(sym, args) => {
                    let uf = !crate::features::is_builtin_symbol_name(sym.name());
                    let mut all_ground = true;
                    for &arg in args {
                        let arg_ground = self.visit(terms, arg, bound_names, scope);
                        if uf
                            && arg_ground
                            && matches!(terms.sort(arg), Sort::Bool)
                            && !matches!(terms.get(arg), TermData::Const(_))
                        {
                            self.bool_uf_args.insert(arg.0);
                        }
                        // Visit every child even if an earlier one is bound:
                        // later children can supply independent ground terms.
                        all_ground &= arg_ground;
                    }
                    if all_ground && self.ground_ids.insert(term.0) {
                        self.new_ground_apps.push(term);
                    }
                    all_ground
                }
                TermData::Not(inner) => self.visit(terms, *inner, bound_names, scope),
                TermData::Ite(c, t, e) => {
                    let c_ground = self.visit(terms, *c, bound_names, scope);
                    let t_ground = self.visit(terms, *t, bound_names, scope);
                    let e_ground = self.visit(terms, *e, bound_names, scope);
                    c_ground && t_ground && e_ground
                }
                TermData::Let(bindings, body) => {
                    let mut all_ground = true;
                    for (_, value) in bindings {
                        all_ground &= self.visit(terms, *value, bound_names, scope);
                    }
                    let body_ground = self.visit(terms, *body, bound_names, scope);
                    all_ground && body_ground
                }
                TermData::Forall(vars, body, _) | TermData::Exists(vars, body, _) => {
                    let mut added = Vec::new();
                    for (name, _) in vars {
                        if bound_names.insert(name.clone()) {
                            added.push(name.clone());
                        }
                    }
                    let inner_scope = self.scope_id(bound_names);
                    self.visit(terms, *body, bound_names, inner_scope);
                    for name in &added {
                        bound_names.remove(name);
                    }
                    false
                }
                // Future variants cannot be assumed ground.
                _ => false,
            }
        });
        if ground {
            self.ground_ids.insert(term.0);
        }
        self.ground_cache.insert((term.0, scope), ground);
        ground
    }
}

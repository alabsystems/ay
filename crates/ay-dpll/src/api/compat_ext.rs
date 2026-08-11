// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Engine-backed helpers for the Z3-compatible C API (`ay-ffi`).
//!
//! Additive `impl Solver` methods that expose existing `ay-core`/`ay-dpll`
//! machinery — term traversal/rebuild, `TermArena` array/lambda/map builders,
//! recognized-builtin named applications, and the `qe-light` equality-
//! elimination core — through the native [`Solver`] surface so the FFI layer
//! (`z3_compat::engine_ext`) can build the corresponding `Z3_*` terms without
//! reaching into private IR internals.
//!
//! Every builder here is either a thin wrapper over an existing, semantically
//! identical `TermArena` primitive or a faithful traversal/rebuild over
//! [`TermData`]; none introduces a new "decide" path, so none can make AY emit
//! a wrong verdict.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::{Symbol, TermData};
use ay_core::{Sort, TermId};

use crate::preprocess::{PreprocessingPass, QeLight};

use super::types::{FuncDecl, SolverError, Term};
use super::Solver;

/// Aggregate work envelope for validating preserved binders during one
/// `update_term` call.  A caller-controlled replacement may be a large DAG and
/// the source binder may contain many variables, so the cap is shared across
/// every body/trigger scan rather than resetting for each root.
const UPDATE_TERM_BINDER_WORK_LIMIT: usize = 100_000;

impl Solver {
    // =========================================================================
    // Term predicates / traversal (Z3_is_ground)
    // =========================================================================

    /// Return `true` iff `t` is *ground*: it contains no free (quantifier-bound)
    /// variable occurrence.
    ///
    /// AY stores BOTH declared constants and quantifier-bound variables as
    /// [`TermData::Var`]. The two are distinguished by registration: a
    /// `declare_const` variable is recorded in `Solver::var_sorts` (it is a
    /// ground 0-arity constant, matching Z3 where declared constants are
    /// ground), whereas a fresh quantifier-bound variable is NOT. So a `Var` is
    /// treated as ground exactly when its [`TermId`] is registered in
    /// `var_sorts`; an unregistered `Var` marks the enclosing term non-ground.
    ///
    /// The walk descends `App` arguments, `Not`/`Ite` children, `Let` bindings
    /// and bodies, and quantifier bodies, memoizing over the hash-consed DAG so
    /// each distinct subterm is visited once. Backs the Z3-compat
    /// `Z3_is_ground` FFI entry point.
    #[must_use]
    pub fn is_ground(&self, t: Term) -> bool {
        let Ok(id) = self.resolve_term("is_ground", t) else {
            return false;
        };
        let mut cache: HashMap<TermId, bool> = HashMap::default();
        self.is_ground_rec(id, &mut cache)
    }

    fn is_ground_rec(&self, id: TermId, cache: &mut HashMap<TermId, bool>) -> bool {
        if let Some(&cached) = cache.get(&id) {
            return cached;
        }
        let result = match self.terms().get(id).clone() {
            // A declared constant (registered) is ground; an unregistered
            // (quantifier-bound) variable is not.
            TermData::Var(_, _) => self.var_sorts.contains_key(&id),
            TermData::Const(_) => true,
            TermData::App(_, args) => args.iter().all(|&a| self.is_ground_rec(a, cache)),
            TermData::Not(inner) => self.is_ground_rec(inner, cache),
            TermData::Ite(c, th, e) => {
                self.is_ground_rec(c, cache)
                    && self.is_ground_rec(th, cache)
                    && self.is_ground_rec(e, cache)
            }
            TermData::Let(bindings, body) => {
                bindings.iter().all(|(_, v)| self.is_ground_rec(*v, cache))
                    && self.is_ground_rec(body, cache)
            }
            TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
                self.is_ground_rec(body, cache)
            }
            // `TermData` is `#[non_exhaustive]`: an unknown future node kind has
            // no variable we can observe, so treat it conservatively as ground.
            _ => true,
        };
        cache.insert(id, result);
        result
    }

    // =========================================================================
    // Variable / function / positional substitution
    // =========================================================================

    /// Replace each de Bruijn bound variable of index `i` (AY's named `Var`
    /// node `__db<i>`, as produced by `Z3_mk_bound`) with `to[i]` in `term`.
    ///
    /// [`Solver::substitute`] keys on `Term` identity and so cannot address the
    /// positional `__db<i>` vars; this resolves each `__db<i>` to its interned
    /// [`TermId`] (by name) and performs the same simultaneous, id-keyed
    /// substitution. Indices whose `__db<i>` var was never interned are skipped
    /// (they cannot occur in `term`). With no resolvable target the input is
    /// returned unchanged. Backs the Z3-compat `Z3_substitute_vars` FFI entry.
    #[must_use]
    pub fn substitute_vars(&mut self, term: Term, to: &[Term]) -> Term {
        let term_id = self.require_term("substitute_vars", term);
        let replacement_ids = self.require_terms("substitute_vars", to);
        if to.is_empty() {
            return term;
        }
        let mut from_ids: Vec<TermId> = Vec::with_capacity(to.len());
        let mut to_ids: Vec<TermId> = Vec::with_capacity(to.len());
        for (i, &replacement_id) in replacement_ids.iter().enumerate() {
            if let Some(var_id) = self.terms().lookup(&format!("__db{i}")) {
                from_ids.push(var_id);
                to_ids.push(replacement_id);
            }
        }
        if from_ids.is_empty() {
            return term;
        }
        let result = self.terms_mut().substitute(term_id, &from_ids, &to_ids);
        self.wrap_term(result)
    }

    /// Resolve the de Bruijn-encoded bound variables of an n-ary binder body
    /// into the given named variables, re-anchoring surviving indices.
    ///
    /// The Z3 de Bruijn C API (`Z3_mk_bound` + `Z3_mk_lambda`/quantifiers)
    /// hands AY a `body` whose bound occurrences are the positional vars
    /// `__db{k}`. For a binder introducing `vars = [x0 .. x{n-1}]` (decl
    /// order), Z3's convention is index 0 = innermost = LAST decl, so
    /// `__db{k}` with `k < n` resolves to `vars[n-1-k]`. Indices `k >= n`
    /// refer to *enclosing* (not-yet-constructed) binders; they are shifted
    /// down to `__db{k-n}` so that, from OUTSIDE this binder, every surviving
    /// `__db` index counts only the binders still missing. This anchoring is
    /// what keeps eager beta-reduction (`select` over a lambda array,
    /// `TermStore::mk_select`) sound without any traversal-time shifting: a
    /// reduced body's surviving `__db{k}` still refers to the k-th missing
    /// enclosing binder. Without this resolution the `__db{k}` vars leak into
    /// the built term as free variables — an open term and wrong values (e.g.
    /// `select((lambda x. x+1), 41)` "simplifying" to `(+ __db0 1)`).
    ///
    /// Substitution is simultaneous (`TermStore::substitute`), so the
    /// `__db1 -> __db0` shift cannot collide with a `__db0 -> x` resolution.
    /// Bodies with no `__db` occurrence (the named-variable path) are
    /// returned unchanged.
    #[must_use]
    pub fn bind_de_bruijn(&mut self, vars: &[Term], body: Term) -> Term {
        let var_ids = self.require_terms("bind_de_bruijn", vars);
        let body_id = self.require_term("bind_de_bruijn", body);
        let n = vars.len();
        if n == 0 {
            return body;
        }
        // Collect the distinct `__db{k}` vars occurring in `body`.
        let mut seen: HashMap<TermId, ()> = HashMap::default();
        let mut occ: Vec<(usize, TermId)> = Vec::new();
        self.collect_db_vars(body_id, &mut seen, &mut occ);
        if occ.is_empty() {
            return body;
        }
        let mut from_ids: Vec<TermId> = Vec::with_capacity(occ.len());
        let mut to_ids: Vec<TermId> = Vec::with_capacity(occ.len());
        for (k, id) in occ {
            from_ids.push(id);
            if k < n {
                to_ids.push(var_ids[n - 1 - k]);
            } else {
                let sort = self.terms().sort(id).clone();
                let shifted = self.declare_const(&format!("__db{}", k - n), sort);
                to_ids.push(shifted.id());
            }
        }
        let result = self.terms_mut().substitute(body_id, &from_ids, &to_ids);
        self.wrap_term(result)
    }

    /// Collect the distinct `__db{k}` positional vars occurring in `term`
    /// (post-order DAG walk, memoized via `seen`). Helper for
    /// [`Self::bind_de_bruijn`].
    fn collect_db_vars(
        &self,
        term: TermId,
        seen: &mut HashMap<TermId, ()>,
        out: &mut Vec<(usize, TermId)>,
    ) {
        if seen.insert(term, ()).is_some() {
            return;
        }
        match self.terms().get(term) {
            TermData::Var(name, _) => {
                if let Some(k) = name
                    .strip_prefix("__db")
                    .and_then(|s| s.parse::<usize>().ok())
                {
                    out.push((k, term));
                }
            }
            TermData::Const(_) => {}
            TermData::App(_, args) => {
                for &a in args.clone().iter() {
                    self.collect_db_vars(a, seen, out);
                }
            }
            TermData::Not(inner) => self.collect_db_vars(*inner, seen, out),
            TermData::Ite(c, t, e) => {
                let (c, t, e) = (*c, *t, *e);
                self.collect_db_vars(c, seen, out);
                self.collect_db_vars(t, seen, out);
                self.collect_db_vars(e, seen, out);
            }
            TermData::Let(bindings, body) => {
                let (bindings, body) = (bindings.clone(), *body);
                for (_, b) in &bindings {
                    self.collect_db_vars(*b, seen, out);
                }
                self.collect_db_vars(body, seen, out);
            }
            TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
                self.collect_db_vars(*body, seen, out);
            }
            // Future TermData variants: no `__db` vars to collect.
            _ => {}
        }
    }

    /// Macro/beta-expand each application of `from[i]` in `term` by substituting
    /// the actual call arguments into the parameterized template `to[i]`.
    ///
    /// Each template `to[i]` is a body over the de Bruijn parameters
    /// `__db0 .. __db{k-1}` (`k = from[i].arity()`). Wherever `term` contains
    /// `App(from[i], a0..a{k-1})`, that node is replaced by
    /// `to[i][__db0 := a0, ..]` — a *one-shot* expansion: the substituted
    /// arguments are the (already rewritten) actuals, and the inlined template
    /// is NOT re-scanned for further `from` matches. Distinct from inline
    /// `define-fun` expansion (this keys on the caller's own decls). Backs the
    /// Z3-compat `Z3_substitute_funs` FFI entry point.
    #[must_use]
    pub fn substitute_funs(&mut self, term: Term, from: &[FuncDecl], to: &[Term]) -> Term {
        let term_id = self.require_term("substitute_funs", term);
        let template_ids = self.require_terms("substitute_funs", to);
        let n = from.len().min(to.len());
        if n == 0 {
            return term;
        }
        // Exact core identity -> (template term, arity). Authenticated
        // declaration handles must still denote their live declaration;
        // synthetic handles may select true operators, but never acquire
        // authority merely because their spelling matches a user declaration.
        let mut fun_map: HashMap<String, (TermId, usize)> = HashMap::default();
        for i in 0..n {
            let declaration_is_current =
                from[i].identity.is_some() && self.function_handle_is_current(&from[i]);
            let synthetic_operator_is_safe = from[i].identity.is_none()
                && !self.core_name_requires_authenticated_handle(&from[i].core_name);
            if declaration_is_current || synthetic_operator_is_safe {
                fun_map.insert(
                    from[i].core_name.clone(),
                    (template_ids[i], from[i].domain.len()),
                );
            }
        }
        let mut cache: HashMap<TermId, TermId> = HashMap::default();
        let result = self.subst_funs_rec(term_id, &fun_map, &mut cache);
        self.wrap_term(result)
    }

    fn subst_funs_rec(
        &mut self,
        term: TermId,
        fun_map: &HashMap<String, (TermId, usize)>,
        cache: &mut HashMap<TermId, TermId>,
    ) -> TermId {
        if let Some(&cached) = cache.get(&term) {
            return cached;
        }
        let result = match self.terms().get(term).clone() {
            TermData::Const(_) | TermData::Var(_, _) => term,
            TermData::App(symbol, args) => {
                // Rewrite arguments bottom-up first.
                let new_args: Vec<TermId> = args
                    .iter()
                    .map(|&arg| self.subst_funs_rec(arg, fun_map, cache))
                    .collect();
                // If this application matches one of the `from` decls (by exact
                // core identity and arity), inline its template with the
                // rewritten actuals.
                let matched = match &symbol {
                    Symbol::Named(name) => fun_map
                        .get(name)
                        .filter(|&&(_, arity)| arity == new_args.len())
                        .copied(),
                    Symbol::Indexed(_, _) => None,
                    // Future Symbol variants: never treat as a macro match.
                    _ => None,
                };
                if let Some((template, _)) = matched {
                    // Beta-substitute __db0..__db{k-1} := new_args into template.
                    let mut from_ids: Vec<TermId> = Vec::with_capacity(new_args.len());
                    let mut to_ids: Vec<TermId> = Vec::with_capacity(new_args.len());
                    for (j, &arg) in new_args.iter().enumerate() {
                        if let Some(db) = self.terms().lookup(&format!("__db{j}")) {
                            from_ids.push(db);
                            to_ids.push(arg);
                        }
                    }
                    self.terms_mut().substitute(template, &from_ids, &to_ids)
                } else if new_args == args {
                    term
                } else {
                    let sort = self.terms().sort(term).clone();
                    self.terms_mut().mk_app(symbol, new_args, sort)
                }
            }
            TermData::Not(inner) => {
                let ni = self.subst_funs_rec(inner, fun_map, cache);
                if ni == inner {
                    term
                } else {
                    self.terms_mut().mk_not(ni)
                }
            }
            TermData::Ite(c, t, e) => {
                let nc = self.subst_funs_rec(c, fun_map, cache);
                let nt = self.subst_funs_rec(t, fun_map, cache);
                let ne = self.subst_funs_rec(e, fun_map, cache);
                if nc == c && nt == t && ne == e {
                    term
                } else {
                    self.terms_mut().mk_ite(nc, nt, ne)
                }
            }
            TermData::Let(bindings, body) => {
                let new_bindings: Vec<(String, TermId)> = bindings
                    .iter()
                    .map(|(name, v)| (name.clone(), self.subst_funs_rec(*v, fun_map, cache)))
                    .collect();
                let new_body = self.subst_funs_rec(body, fun_map, cache);
                if new_bindings == bindings && new_body == body {
                    term
                } else {
                    self.terms_mut().mk_let(new_bindings, new_body)
                }
            }
            TermData::Forall(vars, body, triggers) => {
                let new_body = self.subst_funs_rec(body, fun_map, cache);
                if new_body == body {
                    term
                } else {
                    self.terms_mut()
                        .mk_forall_with_triggers(vars, new_body, triggers)
                }
            }
            TermData::Exists(vars, body, triggers) => {
                let new_body = self.subst_funs_rec(body, fun_map, cache);
                if new_body == body {
                    term
                } else {
                    self.terms_mut()
                        .mk_exists_with_triggers(vars, new_body, triggers)
                }
            }
            // Future node kinds: leave unchanged (faithful identity).
            _ => term,
        };
        cache.insert(term, result);
        result
    }

    /// Rebuild `term` keeping its operator / quantifier binder but replacing its
    /// immediate children with `args`, mirroring the child order of
    /// [`Solver::term_children`].
    ///
    /// Returns `None` when the checked rebuild fails (the FFI reports the error
    /// and returns the input). Positional (not identity-keyed) so children that
    /// happen to be equal are still each replaced by the corresponding `args`
    /// entry. Backs the Z3-compat `Z3_update_term` FFI entry point.
    ///
    /// Child order (matching `term_children`):
    /// - `App(f, xs)` → `xs`
    /// - `Not(x)` → `[x]`; `Ite(c, t, e)` → `[c, t, e]`
    /// - `Let(bs, body)` → binding values then `body`
    /// - `Forall|Exists(_, body, _)` → `[body]`
    /// - `Var` / `Const` → `[]`
    #[must_use]
    pub fn update_term(&mut self, term: Term, args: &[Term]) -> Option<Term> {
        self.try_update_term(term, args).ok()
    }

    /// Return whether an opaque native-API term handle names an entry in this
    /// solver's term store.
    ///
    /// This is intentionally a narrow validity query: compatibility layers
    /// can authenticate an encoded handle before calling APIs that otherwise
    /// index the store. It does not inspect the term or mutate solver state.
    #[must_use]
    pub fn is_valid_term(&self, term: Term) -> bool {
        self.resolve_term("is_valid_term", term).is_ok()
    }

    /// Check that occurrences captured by a preserved named binder retain the
    /// sort declared by that binder.  Nested binders with the same name shadow
    /// the preserved binder; `let` values remain in the outer scope while its
    /// body is shadowed.
    fn validate_update_bound_name(
        &self,
        root: TermId,
        bound_name: &str,
        expected_sort: &Sort,
        work: &mut usize,
    ) -> Result<(), SolverError> {
        let mut seen: HashMap<(TermId, bool), ()> = HashMap::default();
        let mut pending = vec![(root, false)];

        while let Some((current, shadowed)) = pending.pop() {
            if seen.insert((current, shadowed), ()).is_some() {
                continue;
            }
            *work = work.saturating_add(1);
            if *work > UPDATE_TERM_BINDER_WORK_LIMIT {
                return Err(SolverError::InvalidArgument {
                    operation: "update_term",
                    message: format!(
                        "binder validation exceeds the {UPDATE_TERM_BINDER_WORK_LIMIT}-node work limit"
                    ),
                });
            }

            match self.terms().get(current) {
                TermData::Var(name, _) => {
                    if !shadowed
                        && name == bound_name
                        && self.terms().sort(current) != expected_sort
                    {
                        return Err(SolverError::InvalidArgument {
                            operation: "update_term",
                            message: format!(
                                "bound variable `{bound_name}` is declared as {expected_sort} but occurs as {} in a replacement",
                                self.terms().sort(current)
                            ),
                        });
                    }
                }
                TermData::Const(_) => {}
                TermData::App(_, children) => {
                    pending.extend(children.iter().copied().map(|child| (child, shadowed)));
                }
                TermData::Not(inner) => pending.push((*inner, shadowed)),
                TermData::Ite(condition, then_value, else_value) => {
                    pending.push((*condition, shadowed));
                    pending.push((*then_value, shadowed));
                    pending.push((*else_value, shadowed));
                }
                TermData::Let(bindings, body) => {
                    pending.extend(bindings.iter().map(|(_, value)| (*value, shadowed)));
                    let body_shadowed =
                        shadowed || bindings.iter().any(|(name, _)| name == bound_name);
                    pending.push((*body, body_shadowed));
                }
                TermData::Forall(vars, body, triggers) | TermData::Exists(vars, body, triggers) => {
                    let nested_shadowed =
                        shadowed || vars.iter().any(|(name, _)| name == bound_name);
                    pending.push((*body, nested_shadowed));
                    for trigger in triggers {
                        pending.extend(trigger.iter().copied().map(|term| (term, nested_shadowed)));
                    }
                }
                // `TermData` is non-exhaustive.  Updating through an unknown
                // node could hide an ill-sorted occurrence, so fail closed.
                _ => {
                    return Err(SolverError::InvalidArgument {
                        operation: "update_term",
                        message:
                            "replacement contains a term kind unsupported by binder validation"
                                .to_string(),
                    });
                }
            }
        }
        Ok(())
    }

    /// Checked variant of [`Self::update_term`].
    ///
    /// This validates every opaque handle before indexing the term store and
    /// requires each replacement to have exactly the sort of the child in the
    /// same position. The positional sort check is security-relevant for
    /// applications: rebuilding an existing privileged operator such as
    /// `select` with arbitrary child sorts would bypass its normal checked
    /// constructor while retaining the privileged symbol and result sort.
    /// Validation completes before the term store is mutated.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::InvalidArgument`] for an out-of-range handle, an
    /// argument-count mismatch, a term kind whose child layout is unknown, or
    /// a replacement that would give a preserved named binder an occurrence of
    /// the wrong sort.
    /// Returns [`SolverError::SortMismatch`] when a replacement's sort differs
    /// from the corresponding original child sort.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_update_term(&mut self, term: Term, args: &[Term]) -> Result<Term, SolverError> {
        let term_id = self.resolve_term("update_term", term)?;
        let ids = self.resolve_terms("update_term", args)?;

        let data = self.terms().get(term_id).clone();
        let old_children: Vec<TermId> = match &data {
            TermData::Var(_, _) | TermData::Const(_) => Vec::new(),
            TermData::App(_, old_args) => old_args.clone(),
            TermData::Not(inner) => vec![*inner],
            TermData::Ite(condition, then_value, else_value) => {
                vec![*condition, *then_value, *else_value]
            }
            TermData::Let(bindings, body) => {
                let mut children: Vec<TermId> = bindings.iter().map(|(_, value)| *value).collect();
                children.push(*body);
                children
            }
            TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => vec![*body],
            _ => {
                return Err(SolverError::InvalidArgument {
                    operation: "update_term",
                    message: "term kind has no supported child layout".to_string(),
                });
            }
        };

        if args.len() != old_children.len() {
            return Err(SolverError::InvalidArgument {
                operation: "update_term",
                message: format!(
                    "term expects {} immediate children, got {}",
                    old_children.len(),
                    args.len()
                ),
            });
        }
        for (&old_child, &replacement_id) in old_children.iter().zip(&ids) {
            let expected_sort = self.terms().sort(old_child);
            let actual_sort = self.terms().sort(replacement_id);
            if actual_sort != expected_sort {
                return Err(SolverError::SortMismatch {
                    operation: "update_term",
                    expected: "the sort of the corresponding original child",
                    got: vec![actual_sort.clone()],
                });
            }
        }

        let mut binder_work = 0usize;
        match &data {
            TermData::Let(bindings, _) => {
                // `let` binding values are outside the scope of the names; only
                // the trailing replacement body is captured by the preserved
                // binders.  Its immediate result sort alone is insufficient:
                // it may contain a same-named variable of another sort.
                let body = ids[bindings.len()];
                for (position, (name, _)) in bindings.iter().enumerate() {
                    let expected_sort = self.terms().sort(ids[position]);
                    self.validate_update_bound_name(body, name, expected_sort, &mut binder_work)?;
                }
            }
            TermData::Forall(vars, _, triggers) | TermData::Exists(vars, _, triggers) => {
                for (name, sort) in vars {
                    self.validate_update_bound_name(ids[0], name, sort, &mut binder_work)?;
                    // Triggers are preserved rather than supplied as immediate
                    // children, but they are still in the binder's scope and
                    // must satisfy the same invariant before reconstruction.
                    for trigger in triggers {
                        for &pattern in trigger {
                            self.validate_update_bound_name(pattern, name, sort, &mut binder_work)?;
                        }
                    }
                }
            }
            _ => {}
        }
        let new = match data {
            TermData::Var(_, _) | TermData::Const(_) => term,
            TermData::App(symbol, old_args) => {
                if ids == old_args {
                    term
                } else {
                    let sort = self.terms().sort(term_id).clone();
                    let result = self.terms_mut().mk_app(symbol, ids, sort);
                    self.wrap_term(result)
                }
            }
            TermData::Not(_) => self.try_not(args[0])?,
            TermData::Ite(_, _, _) => self.try_ite(args[0], args[1], args[2])?,
            TermData::Let(bindings, _) => {
                let new_bindings: Vec<(String, TermId)> = bindings
                    .iter()
                    .zip(ids.iter())
                    .map(|((name, _), &v)| (name.clone(), v))
                    .collect();
                // The child-count check guarantees one trailing body ID.
                let body = ids[bindings.len()];
                let result = self.terms_mut().mk_let(new_bindings, body);
                self.wrap_term(result)
            }
            TermData::Forall(vars, _, triggers) => {
                let result = self
                    .terms_mut()
                    .mk_forall_with_triggers(vars, ids[0], triggers);
                self.wrap_term(result)
            }
            TermData::Exists(vars, _, triggers) => {
                let result = self
                    .terms_mut()
                    .mk_exists_with_triggers(vars, ids[0], triggers);
                self.wrap_term(result)
            }
            // Future node kinds remain fail-closed even if the validation and
            // rebuild matches are changed independently.
            _ => {
                return Err(SolverError::InvalidArgument {
                    operation: "update_term",
                    message: "term kind has no supported rebuild".to_string(),
                });
            }
        };
        Ok(new)
    }

    // =========================================================================
    // Array / set primitives (expose ay-core TermArena builders)
    // =========================================================================

    /// Build `(default a)` — the else-case value of array `a`. Result sort is
    /// `a`'s element sort. Exposes `TermArena::mk_array_default`, which folds
    /// constant arrays, array maps, and binder-independent lambdas. A dependent
    /// lambda default remains opaque, matching Z3 5.0.0's observable behavior.
    /// Store defaults are intentionally preserved for the solver: a unit carrier
    /// yields the stored value, a finite carrier smaller than 2^14 uses selects
    /// at a shared epsilon, and a large/infinite carrier preserves the base
    /// default. Backs `Z3_mk_array_default`.
    #[must_use]
    pub fn array_default(&mut self, array: Term) -> Term {
        let array_id = self.require_term("array_default", array);
        let result = self.terms_mut().mk_array_default(array_id);
        self.wrap_term(result)
    }

    /// Build `(as-array f)` for the unary function named `func_name` with the
    /// given `array_sort` = `(Array dom range)`. `select(as-array f, i) = f(i)`.
    /// Exposes `TermArena::mk_as_array`. Backs `Z3_mk_as_array`.
    #[must_use]
    pub fn as_array(&mut self, func_name: &str, array_sort: Sort) -> Term {
        let result = self.terms_mut().mk_as_array(func_name, array_sort);
        self.wrap_term(result)
    }

    /// Build the single-variable lambda array `(lambda ((x T)) body)` with
    /// bound variable `var` and `body`, i.e. an array with
    /// `select(arr, i) = body[x := i]`. Multi-variable lambdas are curried in
    /// the FFI layer. Exposes `TermArena::mk_lambda_array`. Backs `Z3_mk_lambda`
    /// / `Z3_mk_lambda_const`.
    #[must_use]
    pub fn lambda_array(&mut self, var: Term, body: Term) -> Term {
        let var_id = self.require_term("lambda_array", var);
        let body_id = self.require_term("lambda_array", body);
        let result = self.terms_mut().mk_lambda_array(var_id, body_id);
        self.wrap_term(result)
    }

    /// Build `((_ map f) a0 .. a{n-1})` — pointwise application of the function
    /// named `func_name` over arrays `arrays`, with the given `result_sort`
    /// (`(Array index range_of_f)`). `select(map f (a..), i) = f(select(a, i)..)`.
    /// Exposes `TermArena::mk_array_map`. Backs `Z3_mk_map` and, via Bool
    /// combinators over `(Array elem Bool)`, the pointwise set operations
    /// (`Z3_mk_set_union` = `map or`, `_intersect` = `map and`,
    /// `_complement`/`_difference` = `map not`).
    #[must_use]
    pub fn array_map(&mut self, func_name: &str, arrays: &[Term], result_sort: Sort) -> Term {
        let array_ids = self.require_terms("array_map", arrays);
        let result = self
            .terms_mut()
            .mk_array_map(func_name, array_ids, result_sort);
        self.wrap_term(result)
    }

    // =========================================================================
    // Recognized-builtin named applications (sequences / strings)
    // =========================================================================

    /// Intern a recognized-builtin application `App(Symbol::named(token), args)`
    /// at `result_sort`, without any structural simplification. `token` must be
    /// a token the executor recognizes (see the callers below); building the
    /// term is sound regardless of whether the executor can DECIDE it (an
    /// undecided theory atom yields `unknown`, never a wrong answer).
    fn named_builtin_app(&mut self, token: &str, args: Vec<Term>, result_sort: Sort) -> Term {
        let arg_ids = self.require_terms("named_builtin_app", &args);
        let result = self
            .terms_mut()
            .mk_app(Symbol::named(token), arg_ids, result_sort);
        self.wrap_term(result)
    }

    /// Set-cardinality predicate `(set.has_size s k)` → Bool: holds iff the
    /// Boolean array `s` (a set as its characteristic function) has exactly
    /// `k` elements mapped to true. Backs `Z3_mk_set_has_size` for element
    /// domains the FFI cannot finitely expand (Int, Real, uninterpreted, wide
    /// BV): the term is REAL and prints as its SMT-LIB application, and the
    /// executor's fail-closed cardinality gate (see
    /// `assertions_contain_set_has_size`) makes any solve over it an honest
    /// `unknown` (`UnknownReason::Incomplete`) — never a wrong SAT/UNSAT from
    /// treating cardinality as an uninterpreted predicate.
    #[must_use]
    pub fn set_has_size(&mut self, s: Term, k: Term) -> Term {
        self.named_builtin_app("set.has_size", vec![s, k], Sort::Bool)
    }

    /// Lexicographic string `<=`: `(str.<= a b)` → Bool. Backs `Z3_mk_str_le`.
    #[must_use]
    pub fn str_le(&mut self, a: Term, b: Term) -> Term {
        self.named_builtin_app("str.<=", vec![a, b], Sort::Bool)
    }

    /// Lexicographic string `<`: `(str.< a b)` → Bool. Backs `Z3_mk_str_lt`.
    #[must_use]
    pub fn str_lt(&mut self, a: Term, b: Term) -> Term {
        self.named_builtin_app("str.<", vec![a, b], Sort::Bool)
    }

    /// Int codepoint → single-char string: `(str.from_code a)` → String.
    /// Backs `Z3_mk_string_from_code`.
    #[must_use]
    pub fn string_from_code(&mut self, a: Term) -> Term {
        self.named_builtin_app("str.from_code", vec![a], Sort::String)
    }

    /// Single-char string → Int codepoint (`-1` if not length 1):
    /// `(str.to_code a)` → Int. Backs `Z3_mk_string_to_code`.
    #[must_use]
    pub fn string_to_code(&mut self, a: Term) -> Term {
        self.named_builtin_app("str.to_code", vec![a], Sort::Int)
    }

    /// Last index of `substr` in `s`: `(seq.last_indexof s substr)` → Int.
    /// Backs `Z3_mk_seq_last_index`.
    #[must_use]
    pub fn seq_last_index(&mut self, s: Term, substr: Term) -> Term {
        self.named_builtin_app("seq.last_indexof", vec![s, substr], Sort::Int)
    }

    /// Replace the first regex match of `re` in `s` with `dst`:
    /// `(str.replace_re s re dst)` → String. Backs `Z3_mk_seq_replace_re`.
    #[must_use]
    pub fn seq_replace_re(&mut self, s: Term, re: Term, dst: Term) -> Term {
        self.named_builtin_app("str.replace_re", vec![s, re, dst], Sort::String)
    }

    /// Replace ALL regex matches of `re` in `s` with `dst`:
    /// `(str.replace_re_all s re dst)` → String. Backs `Z3_mk_seq_replace_re_all`.
    #[must_use]
    pub fn seq_replace_re_all(&mut self, s: Term, re: Term, dst: Term) -> Term {
        self.named_builtin_app("str.replace_re_all", vec![s, re, dst], Sort::String)
    }

    // =========================================================================
    // Higher-order sequence combinators (seq.map / seq.mapi / seq.foldl /
    // seq.foldli)
    //
    // These build the REAL SMT-LIB named applications at the caller-supplied
    // result sort (the FFI computes it from the function's array sort, matching
    // Z3). SOLVING (#ho-seq): the seq theory's `unfold_ho_seq_ops` pass
    // (executor/theories/seq/ho_unfold.rs) DECIDES goals whose combinators are
    // finitely unfoldable (structurally-known or length-pinned sequence
    // arguments, or a map equated to a structurally-known sequence) by
    // rewriting them to element-wise `select` applications. The tokens stay
    // deliberately OUTSIDE the seq theory's `SUPPORTED_SEQ_OPS` allowlist, so
    // anything the unfolder cannot bound returns an honest `unknown`
    // (`UnknownReason::Incomplete`) — never a wrong SAT/UNSAT from treating
    // the combinator as an uninterpreted function (#6026).
    // =========================================================================

    /// Map `f` (an `Array E R` function-as-array) over sequence `s`:
    /// `(seq.map f s)` → `(Seq R)`. Backs `Z3_mk_seq_map`.
    #[must_use]
    pub fn seq_map(&mut self, f: Term, s: Term, result_sort: Sort) -> Term {
        self.named_builtin_app("seq.map", vec![f, s], result_sort)
    }

    /// Indexed map of `f` (an `Array Int E R` curried function-as-array) over
    /// `s` starting at index `i`: `(seq.mapi f i s)` → `(Seq R)`. Backs
    /// `Z3_mk_seq_mapi`.
    #[must_use]
    pub fn seq_mapi(&mut self, f: Term, i: Term, s: Term, result_sort: Sort) -> Term {
        self.named_builtin_app("seq.mapi", vec![f, i, s], result_sort)
    }

    /// Left fold of `f` (an `Array A E A` curried function-as-array) over `s`
    /// from accumulator `a`: `(seq.foldl f a s)` → sort of `a`. Backs
    /// `Z3_mk_seq_foldl`.
    #[must_use]
    pub fn seq_foldl(&mut self, f: Term, a: Term, s: Term, result_sort: Sort) -> Term {
        self.named_builtin_app("seq.foldl", vec![f, a, s], result_sort)
    }

    /// Indexed left fold of `f` over `s` from index `i` and accumulator `a`:
    /// `(seq.foldli f i a s)` → sort of `a`. Backs `Z3_mk_seq_foldli`.
    #[must_use]
    pub fn seq_foldli(&mut self, f: Term, i: Term, a: Term, s: Term, result_sort: Sort) -> Term {
        self.named_builtin_app("seq.foldli", vec![f, i, a, s], result_sort)
    }

    /// Intern a quantifier-pattern grouping node `(pattern t1 t2 ...)` over the
    /// trigger terms, at sort Bool — the exact representation Z3 itself uses
    /// for a (multi-)trigger pattern AST (an application of an internal decl
    /// named `pattern` with Bool range). Backs `Z3_pattern_to_ast` for
    /// multi-trigger patterns.
    ///
    /// The node is INERT: patterns are instantiation hints; this term is only
    /// ever produced for introspection and is never asserted or consulted by
    /// the solver, so it cannot affect any verdict.
    #[must_use]
    pub fn pattern_term(&mut self, triggers: &[Term]) -> Term {
        self.named_builtin_app("pattern", triggers.to_vec(), Sort::Bool)
    }

    // =========================================================================
    // Light quantifier elimination (Z3_qe_lite)
    // =========================================================================

    /// Best-effort light quantifier elimination of `vars` from `body`.
    ///
    /// Treats each `var` as existentially quantified and eliminates it when it
    /// falls in the sound `qe-light` (Cooper) fragment — a single `Int` variable
    /// in a linear-integer matrix whose solved-form equality/inequalities Cooper
    /// can discharge — by reusing the [`QeLight`] preprocessing pass on a
    /// locally-wrapped `(exists ((var Int)) current)`. Each successful step is
    /// equivalence-preserving (Cooper self-checks before returning), so the
    /// result satisfies `∃vars. body ≡ ∃(remaining). result`.
    ///
    /// A variable outside the fragment (non-`Int`, non-linear, disjunctive, or
    /// not a bare `Var`) is simply LEFT in place — the identity fallback, which
    /// is always logically valid because `qe_lite` is best-effort by contract.
    /// Backs the Z3-compat `Z3_qe_lite` FFI entry point.
    #[must_use]
    pub fn qe_lite(&mut self, body: Term, vars: &[Term]) -> Term {
        let mut current = self.require_term("qe_lite", body);
        let var_ids = self.require_terms("qe_lite", vars);
        for var_id in var_ids {
            // Only a genuine (unfolded) Var node can be a bound variable.
            let TermData::Var(name, _) = self.terms().get(var_id).clone() else {
                continue;
            };
            let sort = self.terms().sort(var_id).clone();
            // QeLight (Cooper) eliminates exactly one Int-sorted existential.
            if sort != Sort::Int {
                continue;
            }
            // Only a Bool matrix can be wrapped in an existential.
            if *self.terms().sort(current) != Sort::Bool {
                continue;
            }
            // Wrap `(exists ((name Int)) current)` over the SAME Var identity
            // occurring in `current`, so QeLight recovers the bound variable.
            let exists = self.terms_mut().mk_exists(vec![(name, sort)], current);
            let mut assertions = vec![exists];
            QeLight::new().apply(self.terms_mut(), &mut assertions);
            let rewritten = assertions[0];
            // A change means QeLight replaced the top `exists` with its verified
            // quantifier-free equivalent; adopt it. Otherwise keep `current`
            // open (the var REMAINS free — sound identity).
            if rewritten != exists {
                current = rewritten;
            }
        }
        self.wrap_term(current)
    }
}

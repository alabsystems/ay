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

use super::types::{FuncDecl, Term};
use super::Solver;

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
        let mut cache: HashMap<TermId, bool> = HashMap::default();
        self.is_ground_rec(t.0, &mut cache)
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
        if to.is_empty() {
            return term;
        }
        let mut from_ids: Vec<TermId> = Vec::with_capacity(to.len());
        let mut to_ids: Vec<TermId> = Vec::with_capacity(to.len());
        for (i, replacement) in to.iter().enumerate() {
            if let Some(var_id) = self.terms().lookup(&format!("__db{i}")) {
                from_ids.push(var_id);
                to_ids.push(replacement.0);
            }
        }
        if from_ids.is_empty() {
            return term;
        }
        Term(self.terms_mut().substitute(term.0, &from_ids, &to_ids))
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
        let n = vars.len();
        if n == 0 {
            return body;
        }
        // Collect the distinct `__db{k}` vars occurring in `body`.
        let mut seen: HashMap<TermId, ()> = HashMap::default();
        let mut occ: Vec<(usize, TermId)> = Vec::new();
        self.collect_db_vars(body.0, &mut seen, &mut occ);
        if occ.is_empty() {
            return body;
        }
        let mut from_ids: Vec<TermId> = Vec::with_capacity(occ.len());
        let mut to_ids: Vec<TermId> = Vec::with_capacity(occ.len());
        for (k, id) in occ {
            from_ids.push(id);
            if k < n {
                to_ids.push(vars[n - 1 - k].0);
            } else {
                let sort = self.terms().sort(id).clone();
                let shifted = self.declare_const(&format!("__db{}", k - n), sort);
                to_ids.push(shifted.0);
            }
        }
        Term(self.terms_mut().substitute(body.0, &from_ids, &to_ids))
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
        let n = from.len().min(to.len());
        if n == 0 {
            return term;
        }
        // name -> (template term, arity)
        let mut fun_map: HashMap<String, (TermId, usize)> = HashMap::default();
        for i in 0..n {
            fun_map.insert(from[i].name.clone(), (to[i].0, from[i].domain.len()));
        }
        let mut cache: HashMap<TermId, TermId> = HashMap::default();
        Term(self.subst_funs_rec(term.0, &fun_map, &mut cache))
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
                // If this application matches one of the `from` decls (by name
                // and arity), inline its template with the rewritten actuals.
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
    /// Returns `None` when `args.len()` does not match `term`'s child count
    /// (the FFI reports the arg-count mismatch and returns the input). Positional
    /// (not identity-keyed) so children that happen to be equal are still each
    /// replaced by the corresponding `args` entry. Backs the Z3-compat
    /// `Z3_update_term` FFI entry point.
    ///
    /// Child order (matching `term_children`):
    /// - `App(f, xs)` → `xs`
    /// - `Not(x)` → `[x]`; `Ite(c, t, e)` → `[c, t, e]`
    /// - `Let(bs, body)` → binding values then `body`
    /// - `Forall|Exists(_, body, _)` → `[body]`
    /// - `Var` / `Const` → `[]`
    #[must_use]
    pub fn update_term(&mut self, term: Term, args: &[Term]) -> Option<Term> {
        let ids: Vec<TermId> = args.iter().map(|t| t.0).collect();
        let new = match self.terms().get(term.0).clone() {
            TermData::Var(_, _) | TermData::Const(_) => {
                if !ids.is_empty() {
                    return None;
                }
                term.0
            }
            TermData::App(symbol, old_args) => {
                if ids.len() != old_args.len() {
                    return None;
                }
                if ids == old_args {
                    term.0
                } else {
                    let sort = self.terms().sort(term.0).clone();
                    self.terms_mut().mk_app(symbol, ids, sort)
                }
            }
            TermData::Not(_) => {
                if ids.len() != 1 {
                    return None;
                }
                self.terms_mut().mk_not(ids[0])
            }
            TermData::Ite(_, _, _) => {
                if ids.len() != 3 {
                    return None;
                }
                self.terms_mut().mk_ite(ids[0], ids[1], ids[2])
            }
            TermData::Let(bindings, _) => {
                if ids.len() != bindings.len() + 1 {
                    return None;
                }
                let new_bindings: Vec<(String, TermId)> = bindings
                    .iter()
                    .zip(ids.iter())
                    .map(|((name, _), &v)| (name.clone(), v))
                    .collect();
                // Length was checked == bindings.len() + 1, so `ids` is non-empty.
                let &body = ids.last()?;
                self.terms_mut().mk_let(new_bindings, body)
            }
            TermData::Forall(vars, _, triggers) => {
                if ids.len() != 1 {
                    return None;
                }
                self.terms_mut()
                    .mk_forall_with_triggers(vars, ids[0], triggers)
            }
            TermData::Exists(vars, _, triggers) => {
                if ids.len() != 1 {
                    return None;
                }
                self.terms_mut()
                    .mk_exists_with_triggers(vars, ids[0], triggers)
            }
            // Future node kinds: no known child layout — refuse rather than guess.
            _ => return None,
        };
        Some(Term(new))
    }

    // =========================================================================
    // Array / set primitives (expose ay-core TermArena builders)
    // =========================================================================

    /// Build `(default a)` — the else-case value of array `a`. Result sort is
    /// `a`'s element sort. Exposes `TermArena::mk_array_default` (which folds
    /// `default(const v) = v`, `default(lambda x. body) = body`,
    /// `default(store a i v) = default(a)`). Backs `Z3_mk_array_default`.
    #[must_use]
    pub fn array_default(&mut self, array: Term) -> Term {
        Term(self.terms_mut().mk_array_default(array.0))
    }

    /// Build `(as-array f)` for the unary function named `func_name` with the
    /// given `array_sort` = `(Array dom range)`. `select(as-array f, i) = f(i)`.
    /// Exposes `TermArena::mk_as_array`. Backs `Z3_mk_as_array`.
    #[must_use]
    pub fn as_array(&mut self, func_name: &str, array_sort: Sort) -> Term {
        Term(self.terms_mut().mk_as_array(func_name, array_sort))
    }

    /// Build the single-variable lambda array `(lambda ((x T)) body)` with
    /// bound variable `var` and `body`, i.e. an array with
    /// `select(arr, i) = body[x := i]`. Multi-variable lambdas are curried in
    /// the FFI layer. Exposes `TermArena::mk_lambda_array`. Backs `Z3_mk_lambda`
    /// / `Z3_mk_lambda_const`.
    #[must_use]
    pub fn lambda_array(&mut self, var: Term, body: Term) -> Term {
        Term(self.terms_mut().mk_lambda_array(var.0, body.0))
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
        let array_ids: Vec<TermId> = arrays.iter().map(|t| t.0).collect();
        Term(
            self.terms_mut()
                .mk_array_map(func_name, array_ids, result_sort),
        )
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
        let arg_ids: Vec<TermId> = args.iter().map(|t| t.0).collect();
        Term(
            self.terms_mut()
                .mk_app(Symbol::named(token), arg_ids, result_sort),
        )
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
        let mut current = body.0;
        for &var in vars {
            // Only a genuine (unfolded) Var node can be a bound variable.
            let TermData::Var(name, _) = self.terms().get(var.0).clone() else {
                continue;
            };
            let sort = self.terms().sort(var.0).clone();
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
        Term(current)
    }
}

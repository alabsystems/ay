// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;

use crate::command::{Command, Term as ParsedTerm};
use ay_core::{Sort, TermId};

use super::{
    is_reserved_symbol, CommandResult, Context, ElaborateError, Objective, ObjectiveDirection,
    OptionValue, Result, ScopeFrame, SoftAssertion, SymbolInfo,
};

/// Builtin sort names supplied by enabled SMT theories.
///
/// User aliases/declarations with these names would either shadow a theory
/// carrier or be silently ignored by the builtin match in `sorts.rs`.
const BUILTIN_THEORY_SORT_NAMES: &[&str] = &[
    "Bool",
    "RoundingMode",
    "Float16",
    "Float32",
    "Float64",
    "Float128",
    // Z3 5.0.0's one-parameter finite-set sort constructor.
    "FiniteSet",
];

/// A compact `(push N)` command must not amplify a few input bytes into an
/// effectively unbounded loop and allocation.  This still permits far deeper
/// incremental use than practical solver workloads while bounding one
/// context's empty-frame storage.
const MAX_INCREMENTAL_SCOPE_DEPTH: usize = 1 << 16;

pub(super) fn is_builtin_theory_sort(name: &str) -> bool {
    BUILTIN_THEORY_SORT_NAMES.contains(&name)
}

impl Context {
    /// Reject a sort declaration/definition before it can overwrite any live
    /// sort binding.  Sort aliases and datatype carriers share one SMT-LIB
    /// namespace even though their implementation metadata lives in four
    /// maps.
    fn ensure_sort_name_available(&self, name: &str) -> Result<()> {
        // Z3 5.0.0's no-logic signature includes the legacy lowercase `bool`
        // alias and its proof-object carrier. Selecting any logic removes
        // both, at which point the names may be declared as ordinary user
        // sorts.
        if is_builtin_theory_sort(name)
            || (self.logic.is_none() && matches!(name, "bool" | "Proof"))
        {
            return Err(ElaborateError::ReservedSymbol(name.to_string()));
        }
        if self.sort_defs.contains_key(name)
            || self.parametric_sort_defs.contains_key(name)
            || self.datatypes.contains_key(name)
            || self.parametric_datatypes.contains_key(name)
            || self.sort_parameters.contains(name)
        {
            return Err(ElaborateError::SortRedeclaration(name.to_string()));
        }
        Ok(())
    }

    /// Add an assertion
    pub(crate) fn assert(&mut self, term: &ParsedTerm) -> Result<()> {
        // #quantprod-g3: a pure definitional forall over a never-yet-used
        // declared function adopts it as a macro (fail-closed; see the
        // method). On adoption the elaboration below expands every
        // `f`-application, turning this assertion into the reflexive
        // tautology while `(get-model)` gains the definitional entry.
        let adopted = if self.elaborating_polymorphic_instance {
            None
        } else {
            self.try_adopt_definitional_forall(term)
        };
        #[cfg(test)]
        if adopted.is_some() && std::mem::take(&mut self.fail_next_assert_after_macro_adoption) {
            if let Some(name) = adopted.as_deref() {
                self.rollback_adopted_macro(name);
            }
            return Err(ElaborateError::Unsupported(
                "test-injected failure after macro adoption".to_string(),
            ));
        }
        let elaborated = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            self.elaborate_term(term, &HashMap::default())
        }));
        let id = match elaborated {
            Ok(Ok(id)) => id,
            Ok(Err(error)) => {
                if let Some(name) = adopted.as_deref() {
                    self.rollback_adopted_macro(name);
                }
                return Err(error);
            }
            Err(payload) => {
                if let Some(name) = adopted.as_deref() {
                    self.rollback_adopted_macro(name);
                }
                std::panic::resume_unwind(payload);
            }
        };
        let sort = self.terms.sort(id).clone();
        if sort != Sort::Bool {
            if let Some(name) = adopted.as_deref() {
                self.rollback_adopted_macro(name);
            }
            return Err(ElaborateError::SortMismatch {
                expected: "Bool".to_string(),
                actual: format!("{sort:?}"),
            });
        }
        let public_metadata = match self.validate_public_assertion(term, id) {
            Ok(metadata) => metadata,
            Err(error) => {
                if let Some(name) = adopted.as_deref() {
                    self.rollback_adopted_macro(name);
                }
                return Err(error);
            }
        };
        // Retain the original parsed AST only under the retention policy and
        // while the parallel assertion stacks remain prefix-aligned.
        if self.retain_parsed_assertions && self.assertions_parsed.len() == self.assertions.len() {
            self.assertions_parsed.push(term.clone());
        }
        self.assertions.push(id);
        self.assertion_finite_set_metadata.push(public_metadata);
        Ok(())
    }

    /// Push a scope
    pub(crate) fn push(&mut self) {
        self.scopes.push(ScopeFrame {
            symbols: HashMap::default(),
            assertion_count: self.assertions.len(),
            objective_count: self.objectives.len(),
            soft_constraint_count: self.soft_constraints.len(),
            named_terms: Vec::new(),
            datatypes: Vec::new(),
            constructors: Vec::new(),
            sort_defs: Vec::new(),
            fun_defs: Vec::new(),
            parametric_datatypes: Vec::new(),
            polymorphic_assertion_count: self.polymorphic_assertions.len(),
            authored_assertion_count: self.authored_assertions.len(),
            polymorphic_declarations: Vec::new(),
        });
    }

    /// Pop a scope. Returns `true` on success, `false` on underflow (no scopes).
    pub(crate) fn pop(&mut self) -> bool {
        if let Some(frame) = self.scopes.pop() {
            // Restore the exact outer binding state. A scoped overload shares
            // its surface name with an outer declaration, so deleting by name
            // would incorrectly destroy the surviving declaration on pop.
            for state in frame.symbols.into_values() {
                if let Some(primary) = state.primary {
                    self.symbols.insert(state.name.clone(), primary);
                } else {
                    self.symbols.remove(&state.name);
                }
                if let Some(overloads) = state.overloads {
                    self.overloaded_symbols
                        .insert(state.name.clone(), overloads);
                } else {
                    self.overloaded_symbols.remove(&state.name);
                }
                if state.was_internal {
                    self.internal_symbols.insert(state.name);
                } else {
                    self.internal_symbols.remove(&state.name);
                }
            }
            // Remove assertions from this scope
            self.assertions.truncate(frame.assertion_count);
            self.assertion_finite_set_metadata
                .truncate(frame.assertion_count);
            self.assertions_parsed.truncate(frame.assertion_count);
            // Remove objectives from this scope
            self.objectives.truncate(frame.objective_count);
            self.objective_finite_set_metadata
                .truncate(frame.objective_count);
            // Remove soft constraints from this scope
            self.soft_constraints.truncate(frame.soft_constraint_count);
            self.soft_finite_set_metadata
                .truncate(frame.soft_constraint_count);
            // Remove named terms defined in this scope
            for name in frame.named_terms {
                self.named_terms.remove(&name);
            }
            // Remove datatypes defined in this scope
            for name in frame.datatypes {
                self.datatypes.remove(&name);
                self.monomorphic_datatype_decs.remove(&name);
                // Parametric instance metadata is keyed by the same mangled name.
                self.parametric_instance_args.remove(&name);
            }
            // Remove constructors defined in this scope
            for name in frame.constructors {
                self.constructors.remove(&name);
                self.ctor_selectors.remove(&name);
                self.ctor_selector_info.remove(&name);
                self.nullary_ctor_terms.remove(&name);
            }
            // Remove sort definitions defined in this scope (both monomorphic
            // synonyms and parameterized templates are tracked here; removing an
            // absent key from either map is a harmless no-op).
            for name in frame.sort_defs {
                self.sort_defs.remove(&name);
                self.public_sort_defs.remove(&name);
                self.parametric_sort_defs.remove(&name);
            }
            // Remove function definitions defined in this scope (#8621)
            for name in frame.fun_defs {
                self.fun_defs.remove(&name);
                self.recursive_fun_names.remove(&name);
            }
            // Remove parametric datatype templates defined in this scope.
            for name in frame.parametric_datatypes {
                self.parametric_datatypes.remove(&name);
            }
            self.polymorphic_assertions
                .truncate(frame.polymorphic_assertion_count);
            self.authored_assertions
                .truncate(frame.authored_assertion_count);
            if !frame.polymorphic_declarations.is_empty() {
                self.polymorphic_declarations.retain(|declaration| {
                    !frame
                        .polymorphic_declarations
                        .iter()
                        .any(|name| name == &declaration.name)
                });
            }
            true
        } else {
            false
        }
    }

    /// Truncate the hard assertion stack (and the aligned parsed-assertion
    /// stack) back to `len`.
    ///
    /// Used by the executor's MaxSMT solve to revert the temporary relaxation
    /// clauses it appended at the current scope level once the solve completes.
    pub fn truncate_assertions(&mut self, len: usize) {
        self.assertions.truncate(len);
        self.assertion_finite_set_metadata.truncate(len);
        self.assertions_parsed.truncate(len);
    }

    /// Remove a set of declared symbols by name (e.g. internal relaxation /
    /// cardinality-counter variables introduced by the MaxSMT solve).
    ///
    /// Mirrors the symbol cleanup `pop()` performs for scoped declarations,
    /// without requiring a scope frame. Only intended for internal `__ay_*`
    /// symbols the solver created itself.
    pub fn remove_symbols(&mut self, names: &[String]) {
        for name in names {
            self.symbols.remove(name);
            self.overloaded_symbols.remove(name);
            self.internal_symbols.remove(name);
        }
    }

    /// True when `name` is a SOLVER-INTERNAL symbol registration (e.g. a fresh
    /// field constant from the eager single-constructor datatype elimination),
    /// not a user declaration. `(get-model)` must not print such symbols; a
    /// user (re)declaration of the same name clears the flag
    /// (#mv-internal-symbol-suppression).
    pub fn is_internal_symbol(&self, name: &str) -> bool {
        self.internal_symbols.contains(name)
    }

    /// Iterate over all declared symbol signatures. An overloaded surface name
    /// appears once per signature; non-overloaded names appear once.
    pub fn symbol_iter(&self) -> impl Iterator<Item = (&String, &SymbolInfo)> {
        self.symbols
            .iter()
            .filter(|(name, _)| !self.overloaded_symbols.contains_key(*name))
            .chain(
                self.overloaded_symbols
                    .iter()
                    .flat_map(|(name, infos)| infos.iter().map(move |info| (name, info))),
            )
    }

    /// Core term/model identity for one declared signature. Public renderers
    /// should continue to print `surface_name`; solver tables and occurrence
    /// sets must key by this identity or distinct overloads conflate.
    pub fn symbol_identity_name<'a>(&self, surface_name: &'a str, info: &'a SymbolInfo) -> &'a str {
        info.internal_name.as_deref().unwrap_or(surface_name)
    }

    /// Return the public surface name when `identity` denotes one signature of
    /// an overloaded declaration. Serializers use this to add the result-sort
    /// ascription required to select the same signature when replayed.
    pub fn overloaded_surface_name<'a>(&'a self, identity: &'a str) -> Option<&'a str> {
        let surface_name = self.dt_surface_name(identity).unwrap_or(identity);
        self.overloaded_symbols
            .get(surface_name)
            .is_some_and(|infos| {
                infos
                    .iter()
                    .any(|info| self.symbol_identity_name(surface_name, info) == identity)
            })
            .then_some(surface_name)
    }

    /// True when `name` was bound by a problem-level `define-fun` /
    /// `define-fun-rec` / `define-funs-rec`.
    ///
    /// Such a symbol's interpretation is FIXED by the problem text, so
    /// `(get-model)` must not re-emit it: the model-validation grammar treats a
    /// second `define-fun` of the same name as a definition conflict, and any
    /// solver-side "value" for it is at best redundant and at worst wrong
    /// (defined applications are macro-expanded at elaboration, so no internal
    /// model entry is ever keyed by the defined name).
    pub fn is_defined_fun(&self, name: &str) -> bool {
        self.fun_defs.contains_key(name)
    }

    /// #quantprod-g3: the adopted definitional-macro interpretation of a
    /// DECLARED function, if any: `(elaborated params, elaborated body)`.
    /// Unlike a problem-level `define-fun` (which `(get-model)` must omit),
    /// an adopted declared function still needs a model entry — this is it.
    pub fn adopted_macro_interp(&self, name: &str) -> Option<&(Vec<(String, Sort)>, TermId)> {
        self.adopted_macro_interps.get(name)
    }

    /// Register the model interpretation for a pure definitional macro that
    /// was recognized by the native Rust API after term construction.
    ///
    /// The native API owns expansion of later applications, so this method
    /// deliberately installs only the interpretation used by model emission.
    /// It repeats the context-side soundness checks: the declaration must be a
    /// single, ordinary user function with the exact signature; no earlier
    /// constraint may mention it; and the body must be non-recursive.
    ///
    /// `existing_uses_are_pinned` is the ONE narrow exemption from the
    /// "no earlier constraint may mention it" check, and only the native API
    /// may pass `true`.  That guard is there because an earlier raw
    /// application would otherwise stay a disconnected uninterpreted symbol
    /// once the defining `forall` is discharged.  The native adopter can
    /// instead enumerate EVERY raw application in its term arena and replace
    /// the `forall` with those applications' own definitional instances; when
    /// it has done so, each earlier use is fixed at exactly the value this
    /// interpretation gives it, so the interpretation is consistent with every
    /// remaining occurrence and nothing is disconnected.  The parsed-SMT path
    /// has no such enumeration and always passes `false`.  Every other check
    /// below applies unchanged in both modes.
    #[doc(hidden)]
    pub fn try_register_native_adopted_macro_interp(
        &mut self,
        name: &str,
        params: &[(String, Sort)],
        body: TermId,
        existing_uses_are_pinned: bool,
    ) -> bool {
        if !self.scopes.is_empty()
            || self.fun_defs.contains_key(name)
            || self.recursive_fun_names.contains(name)
            || self.is_datatype_member_name(name)
            || self.overloaded_symbols.contains_key(name)
            || self.adopted_macro_interps.contains_key(name)
            || (!existing_uses_are_pinned && self.constraints_mention_symbol(name))
            || self.term_mentions_symbol(body, name)
        {
            return false;
        }
        let Some(info) = self.symbols.get(name) else {
            return false;
        };
        if info.arg_sorts.len() != params.len()
            || info
                .arg_sorts
                .iter()
                .zip(params.iter())
                .any(|(declared, (_, actual))| declared != actual)
            || self.terms.sort(body) != &info.sort
        {
            return false;
        }
        self.adopted_macro_interps
            .insert(name.to_string(), (params.to_vec(), body));
        true
    }

    /// #quantprod-g3: is `name` referenced by any EXISTING constraint — a
    /// hard assertion, soft assertion, or objective? Elaborated terms have
    /// macros expanded, so indirect uses through `define-fun` bodies are
    /// seen. Consulted only at (rare) adoption attempts, so ordinary asserts
    /// pay nothing.
    fn constraints_mention_symbol(&self, name: &str) -> bool {
        self.assertions
            .iter()
            .copied()
            .chain(self.soft_constraints.iter().map(|s| s.term))
            .chain(self.objectives.iter().map(|o| o.term))
            .any(|t| self.term_mentions_symbol(t, name))
    }

    /// #quantprod-g3: does `body`'s DAG reference symbol `name` anywhere
    /// (application head or variable/constant leaf)? Used to refuse a
    /// recursive "definition" — fail-closed on any occurrence.
    fn term_mentions_symbol(&self, term: TermId, name: &str) -> bool {
        let mut seen = ay_core::kani_compat::DetHashSet::default();
        let mut stack = vec![term];
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            match self.terms.get(t) {
                ay_core::TermData::App(sym, args) => {
                    if matches!(sym, ay_core::term::Symbol::Named(n) if n == name) {
                        return true;
                    }
                    stack.extend(args.iter().copied());
                }
                ay_core::TermData::Var(n, _) if n == name => return true,
                ay_core::TermData::Not(inner) => stack.push(*inner),
                ay_core::TermData::Ite(c, a, b) => {
                    stack.push(*c);
                    stack.push(*a);
                    stack.push(*b);
                }
                ay_core::TermData::Let(bindings, body) => {
                    for (_, v) in bindings {
                        stack.push(*v);
                    }
                    stack.push(*body);
                }
                ay_core::TermData::Forall(_, body, _) | ay_core::TermData::Exists(_, body, _) => {
                    stack.push(*body)
                }
                _ => {}
            }
        }
        false
    }

    /// #quantprod-g3: adopt `(assert (forall X. (= (f X) body)))` as the
    /// macro `f := λX. body` when that is provably a pure DEFINITION.
    ///
    /// z3's macro-finder equivalent. When every occurrence of `f` in the
    /// problem goes through this forall's expansion, `f = λX. body` holds in
    /// EVERY model of the constraint and conversely `λX. body` satisfies the
    /// constraint by reflexivity — so registering the macro and letting the
    /// (re-)elaboration expand every application preserves satisfiability in
    /// BOTH polarities, decides problems the quantifier engines fail closed
    /// on (`forall x. (= (f x) (* x x))` is UFNIA), and yields the z3-parity
    /// model entry. Fail-closed adoption conditions, each refusal keeping
    /// the byte-identical status quo:
    ///
    /// * outermost scope only (a `pop` could otherwise drop the justifying
    ///   assertion while the macro persisted);
    /// * plain un-annotated `forall` whose body is `(= (f x1 … xk) rhs)`
    ///   with the binder list applied exactly, in order, binder names
    ///   distinct, and exactly ONE side an `f`-application;
    /// * `f` user-declared, arity and binder sorts matching the declaration,
    ///   not already defined/recursive/datatype-internal, and NOT referenced
    ///   by any existing assertion/soft-assertion/objective (a raw pre-macro
    ///   occurrence would constrain a DIFFERENT, disconnected `f`);
    /// * the elaborated `rhs` does not mention `f` (directly or through an
    ///   expanded macro — the walk runs on the elaborated DAG) and has
    ///   exactly the declared result sort.
    ///
    /// On adoption the caller re-elaborates the assertion, which the fresh
    /// macro turns into the reflexive tautology — the constraint stays on
    /// the stack with its meaning discharged by construction.
    fn try_adopt_definitional_forall(&mut self, term: &ParsedTerm) -> Option<String> {
        use crate::command::Term as PT;
        if !self.scopes.is_empty() {
            return None;
        }
        let PT::Forall(pvars, pbody) = term else {
            return None;
        };
        if pvars.is_empty() {
            return None;
        }
        // Distinct binder names (duplicate binders make the "applied exactly
        // in order" reading ambiguous).
        for i in 0..pvars.len() {
            for j in (i + 1)..pvars.len() {
                if pvars[i].0 == pvars[j].0 {
                    return None;
                }
            }
        }
        let PT::App(eq, pargs) = pbody.as_ref() else {
            return None;
        };
        if eq != "=" || pargs.len() != 2 {
            return None;
        }
        // The `f`-application side at the parsed level: `(f x1 … xk)` with
        // the binders in order.
        //
        // Head candidacy is restricted to USER-DECLARED symbols.  A theory
        // builtin (`+`, `bvadd`, `select`, …) is already totally interpreted,
        // so it can never be the symbol a definition defines; without this
        // restriction `forall a b. (= (add a b) (+ a b))` — the RHS being the
        // binders applied exactly, in order — made BOTH sides look like heads
        // and the disambiguation below refused a definition that is in fact
        // unambiguous.  This can only NARROW candidacy, so it removes no
        // adoption: an undeclared head was already rejected below by
        // `self.symbols.get(&fname)?`.  Two user-declared heads
        // (`f(a,b) = g(a,b)`) stay genuinely ambiguous and keep refusing.
        let declared = &self.symbols;
        let side_f = |t: &PT| -> Option<String> {
            let PT::App(f, args) = t else {
                return None;
            };
            if !declared.contains_key(f) {
                return None;
            }
            if args.len() != pvars.len() {
                return None;
            }
            for (a, (v, _)) in args.iter().zip(pvars.iter()) {
                let PT::Symbol(s) = a else {
                    return None;
                };
                if s != v {
                    return None;
                }
            }
            Some(f.clone())
        };
        let (fname, parsed_rhs) = match (side_f(&pargs[0]), side_f(&pargs[1])) {
            (Some(f), None) => (f, pargs[1].clone()),
            (None, Some(f)) => (f, pargs[0].clone()),
            _ => return None,
        };
        if self.fun_defs.contains_key(&fname)
            || self.recursive_fun_names.contains(&fname)
            || self.is_datatype_member_name(&fname)
            // An OVERLOADED symbol could keep a raw second-arity use alive
            // outside the macro expansion — refuse (fail-closed).
            || self.overloaded_symbols.contains_key(&fname)
        {
            return None;
        }
        let info = self.symbols.get(&fname)?;
        if info.arg_sorts.len() != pvars.len() {
            return None;
        }
        // A pre-adoption raw occurrence of `f` in any existing constraint
        // would stay a disconnected uninterpreted symbol while later
        // occurrences expand — refuse (wrong-verdict source).
        if self.constraints_mention_symbol(&fname) {
            return None;
        }
        let ret_sort = info.sort.clone();
        let arg_sorts = info.arg_sorts.clone();
        // Binder sorts must equal the declared argument sorts exactly.
        let mut params: Vec<(String, Sort)> = Vec::with_capacity(pvars.len());
        for ((vname, vsort), decl) in pvars.iter().zip(arg_sorts.iter()) {
            let Ok(s) = self.elaborate_sort(vsort) else {
                return None;
            };
            if s != *decl {
                return None;
            }
            params.push((vname.clone(), s));
        }
        // Validate on the ELABORATED forall (macro not yet registered): the
        // same structural shape must hold after elaboration, the definition
        // body must be `f`-free, and its sort must be the declared result
        // sort. Elaboration errors refuse adoption; the caller's normal
        // elaboration then surfaces the same error.
        let Ok(eid) = self.elaborate_term(term, &HashMap::default()) else {
            return None;
        };
        let ay_core::TermData::Forall(evars, ebody, _) = self.terms.get(eid).clone() else {
            return None;
        };
        if evars.len() != params.len() {
            return None;
        }
        let ay_core::TermData::App(esym, eargs) = self.terms.get(ebody).clone() else {
            return None;
        };
        if !matches!(&esym, ay_core::term::Symbol::Named(n) if n == "=") || eargs.len() != 2 {
            return None;
        }
        let is_f_app = |t: TermId| -> bool {
            let ay_core::TermData::App(sym, fargs) = self.terms.get(t) else {
                return false;
            };
            if !matches!(sym, ay_core::term::Symbol::Named(n) if *n == fname)
                || fargs.len() != evars.len()
            {
                return false;
            }
            fargs.iter().zip(evars.iter()).all(|(&a, (vn, _))| {
                matches!(self.terms.get(a), ay_core::TermData::Var(n, _) if n == vn)
            })
        };
        let def_body = match (is_f_app(eargs[0]), is_f_app(eargs[1])) {
            (true, false) => eargs[1],
            (false, true) => eargs[0],
            _ => return None,
        };
        if self.term_mentions_symbol(def_body, &fname) {
            return None;
        }
        if *self.terms.sort(def_body) != ret_sort {
            return None;
        }
        // Adopt: future (re-)elaborations expand every `f`-application.
        self.fun_defs
            .insert(fname.clone(), (params, ret_sort, parsed_rhs));
        self.adopted_macro_interps
            .insert(fname.clone(), (evars, def_body));
        Some(fname)
    }

    fn rollback_adopted_macro(&mut self, name: &str) {
        self.fun_defs.remove(name);
        self.adopted_macro_interps.remove(name);
    }

    #[cfg(test)]
    pub(crate) fn fail_next_assert_after_macro_adoption(&mut self) {
        self.fail_next_assert_after_macro_adoption = true;
    }

    /// True when `name` was bound by `define-fun-rec` / `define-funs-rec` (a
    /// recursive function), as opposed to a plain `define-fun` macro. z3
    /// overloads a `declare-*` against such a name instead of rejecting it; AY
    /// cannot represent that overload, so the CLI fail-closes such a case to
    /// `unknown` rather than answer on a misresolved binding. (#P0.3)
    pub fn is_recursive_fun(&self, name: &str) -> bool {
        self.recursive_fun_names.contains(name)
    }

    /// Whether a user-visible declaration/definition already occupies `name`.
    /// The CLI queries this before an accepted `define-*` overload: definitions
    /// remain name-keyed in [`Context::fun_defs`], so retaining a definitive
    /// verdict after such an overload would misrepresent z3's per-signature
    /// binding semantics.
    pub fn has_symbol_binding(&self, name: &str) -> bool {
        self.symbols.contains_key(name)
            || self.overloaded_symbols.contains_key(name)
            || self.fun_defs.contains_key(name)
    }

    /// Register a symbol directly (for native API use)
    ///
    /// This is used by the native Rust API to register constants created
    /// via `mk_var` so they appear in models.
    pub fn register_symbol(&mut self, name: String, term: TermId, sort: Sort) {
        let public_sort = super::PublicSort::from_engine(&sort);
        let info = SymbolInfo {
            term: Some(term),
            sort,
            arg_sorts: vec![],
            public_sort,
            public_arg_sorts: vec![],
            internal_name: None,
        };
        if self.global_declarations_enabled() {
            self.propagate_global_symbol_replacement_to_snapshots(&name, &info);
        } else {
            self.track_scoped_symbol(&name);
        }
        self.symbols.insert(name, info);
    }

    /// Register a native constant independently of the current SMT-LIB
    /// assertion scope, without changing `:global-declarations`.
    #[doc(hidden)]
    pub fn register_native_global_symbol(&mut self, name: String, term: TermId, sort: Sort) {
        self.with_native_global_declaration_tracking(|ctx| {
            ctx.register_symbol(name, term, sort);
        });
    }

    /// Register a trusted surface-name alias for a native function identity.
    ///
    /// API adapters sometimes represent declaration identity with a private
    /// internal name while exposing a caller-visible name to SMT-LIB parsing.
    /// The alias participates in ordinary signature-based overload resolution,
    /// but applications are built with `internal_name`, so two public names or
    /// overloads cannot collapse onto the same core `App` symbol.
    pub fn register_native_function_alias(
        &mut self,
        surface_name: String,
        internal_name: String,
        arg_sorts: Vec<Sort>,
        ret_sort: Sort,
    ) -> Result<bool> {
        let public_arg_sorts = arg_sorts
            .iter()
            .map(super::PublicSort::from_engine)
            .collect();
        let public_sort = super::PublicSort::from_engine(&ret_sort);
        self.register_native_function_alias_inner(
            surface_name,
            internal_name,
            arg_sorts,
            ret_sort,
            public_arg_sorts,
            public_sort,
            false,
        )
    }

    /// Register a trusted native function alias with an exact public signature.
    ///
    /// Z3 5.0.0 API adapters use this when a declaration mentions
    /// [`super::PublicSort::FiniteSet`]. Its engine signature is derived by
    /// lowering that public signature, while the distinct public identity is
    /// retained for subsequent textual parsing.
    pub fn register_native_public_function_alias(
        &mut self,
        surface_name: String,
        internal_name: String,
        public_arg_sorts: Vec<super::PublicSort>,
        public_sort: super::PublicSort,
    ) -> Result<bool> {
        let arg_sorts = public_arg_sorts
            .iter()
            .map(|sort| {
                sort.engine_sort().ok_or_else(|| {
                    ElaborateError::Unsupported(format!(
                        "native alias '{surface_name}' has an unresolved public argument sort"
                    ))
                })
            })
            .collect::<Result<Vec<_>>>()?;
        let ret_sort = public_sort.engine_sort().ok_or_else(|| {
            ElaborateError::Unsupported(format!(
                "native alias '{surface_name}' has an unresolved public result sort"
            ))
        })?;
        self.register_native_function_alias_inner(
            surface_name,
            internal_name,
            arg_sorts,
            ret_sort,
            public_arg_sorts,
            public_sort,
            true,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn register_native_function_alias_inner(
        &mut self,
        surface_name: String,
        internal_name: String,
        arg_sorts: Vec<Sort>,
        ret_sort: Sort,
        public_arg_sorts: Vec<super::PublicSort>,
        public_sort: super::PublicSort,
        replace_public_identity: bool,
    ) -> Result<bool> {
        let is_same_engine_alias = |info: &SymbolInfo| {
            info.internal_name.as_deref().unwrap_or(&surface_name) == internal_name
                && info.arg_sorts == arg_sorts
                && info.sort == ret_sort
        };
        // Exact re-registration is an identity operation, including for a
        // trusted alias of a datatype member. Check it before the collision
        // gates: after first registration, metadata intentionally classifies a
        // custom recognizer alias as a datatype-member surface name.
        if let Some(info) = self
            .overloaded_symbols
            .get_mut(&surface_name)
            .and_then(|aliases| aliases.iter_mut().find(|info| is_same_engine_alias(info)))
        {
            if replace_public_identity {
                let changed =
                    info.public_arg_sorts != public_arg_sorts || info.public_sort != public_sort;
                info.public_arg_sorts = public_arg_sorts.clone();
                info.public_sort = public_sort.clone();
                if let Some(primary) = self
                    .symbols
                    .get_mut(&surface_name)
                    .filter(|primary| is_same_engine_alias(primary))
                {
                    primary.public_arg_sorts = public_arg_sorts;
                    primary.public_sort = public_sort;
                }
                return Ok(changed);
            }
            return Ok(false);
        }
        if let Some(info) = self
            .symbols
            .get_mut(&surface_name)
            .filter(|info| is_same_engine_alias(info))
        {
            if replace_public_identity {
                let changed =
                    info.public_arg_sorts != public_arg_sorts || info.public_sort != public_sort;
                info.public_arg_sorts = public_arg_sorts;
                info.public_sort = public_sort;
                return Ok(changed);
            }
            return Ok(false);
        }
        if replace_public_identity {
            let lowered_signature_collides = self
                .symbols
                .get(&surface_name)
                .is_some_and(|info| info.arg_sorts == arg_sorts && info.sort == ret_sort)
                || self
                    .overloaded_symbols
                    .get(&surface_name)
                    .is_some_and(|aliases| {
                        aliases
                            .iter()
                            .any(|info| info.arg_sorts == arg_sorts && info.sort == ret_sort)
                    });
            if lowered_signature_collides {
                // The engine cannot select two declarations distinguished only
                // by FiniteSet-vs-Array public identity. Reject instead of
                // silently routing an application to an arbitrary alias.
                return Err(ElaborateError::UnrepresentableOverload(surface_name));
            }
        }
        // Reserved structural operators are safe only through their dedicated
        // builders. A textual alias could be intercepted by a specialized
        // elaboration path before ordinary function resolution.
        if is_reserved_symbol(&surface_name) {
            return Err(ElaborateError::ReservedSymbol(surface_name));
        }
        if self.is_datatype_member_name(&surface_name) {
            return Err(ElaborateError::DatatypeMemberCollision(surface_name));
        }
        self.track_internal_surface(internal_name.clone(), surface_name.clone());
        self.register_overloadable_symbol(
            surface_name,
            SymbolInfo {
                term: None,
                sort: ret_sort,
                arg_sorts,
                public_sort,
                public_arg_sorts,
                internal_name: Some(internal_name),
            },
        );
        Ok(true)
    }

    /// Register a native function alias independently of the current SMT-LIB
    /// assertion scope, without changing `:global-declarations`.
    #[doc(hidden)]
    pub fn register_native_global_function_alias(
        &mut self,
        surface_name: String,
        internal_name: String,
        arg_sorts: Vec<Sort>,
        ret_sort: Sort,
    ) -> Result<bool> {
        self.with_native_global_declaration_tracking(|ctx| {
            ctx.register_native_function_alias(surface_name, internal_name, arg_sorts, ret_sort)
        })
    }

    /// Register a native alias with an exact public signature independently of
    /// the current SMT-LIB assertion scope.
    #[doc(hidden)]
    pub fn register_native_global_public_function_alias(
        &mut self,
        surface_name: String,
        internal_name: String,
        public_arg_sorts: Vec<super::PublicSort>,
        public_sort: super::PublicSort,
    ) -> Result<bool> {
        self.with_native_global_declaration_tracking(|ctx| {
            ctx.register_native_public_function_alias(
                surface_name,
                internal_name,
                public_arg_sorts,
                public_sort,
            )
        })
    }

    pub(super) fn register_overloadable_symbol(&mut self, name: String, info: SymbolInfo) {
        if self.global_declarations_enabled() {
            self.propagate_global_overload_to_snapshots(&name, &info);
        } else {
            self.track_scoped_symbol(&name);
        }
        if let Some(existing) = self.symbols.get(&name).cloned() {
            self.overloaded_symbols
                .entry(name.clone())
                .or_insert_with(|| vec![existing])
                .push(info.clone());
        } else if let Some(overloads) = self.overloaded_symbols.get_mut(&name) {
            overloads.push(info.clone());
        }

        self.symbols.insert(name.clone(), info);
    }

    fn propagate_global_symbol_replacement_to_snapshots(&mut self, name: &str, info: &SymbolInfo) {
        for frame in &mut self.scopes {
            if let Some(state) = frame.symbols.get_mut(name) {
                state.primary = Some(info.clone());
                state.overloads = None;
                state.was_internal = false;
            }
        }
    }

    fn propagate_global_overload_to_snapshots(&mut self, name: &str, info: &SymbolInfo) {
        for frame in &mut self.scopes {
            if let Some(state) = frame.symbols.get_mut(name) {
                if let Some(existing) = state.primary.clone() {
                    state
                        .overloads
                        .get_or_insert_with(|| vec![existing])
                        .push(info.clone());
                } else if let Some(overloads) = state.overloads.as_mut() {
                    overloads.push(info.clone());
                }
                state.primary = Some(info.clone());
                state.was_internal = false;
            }
        }
    }

    pub(crate) fn with_native_global_declaration_tracking<T>(
        &mut self,
        operation: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let prior = std::mem::replace(&mut self.native_global_declaration, true);
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| operation(self)));
        self.native_global_declaration = prior;
        match result {
            Ok(value) => value,
            Err(payload) => std::panic::resume_unwind(payload),
        }
    }

    /// Allocate a private core identity for an incoming ordinary declaration
    /// when its surface name is already occupied. The first declaration keeps
    /// the surface identity for compatibility; every later overload is
    /// disjoint even when only its result sort differs.
    pub(super) fn ordinary_declaration_internal_name(&mut self, name: &str) -> Option<String> {
        if !self.symbols.contains_key(name) && !self.overloaded_symbols.contains_key(name) {
            return None;
        }
        loop {
            let candidate = format!(
                "{}overload_{}",
                super::INTERNAL_SYMBOL_PREFIX,
                self.next_overload_identity
            );
            self.next_overload_identity = self.next_overload_identity.wrapping_add(1);
            let already_used = self.symbols.contains_key(&candidate)
                || self.overloaded_symbols.contains_key(&candidate)
                || self.dt_internal_surface.contains_key(&candidate);
            if !already_used {
                self.track_internal_surface(candidate.clone(), name.to_string());
                return Some(candidate);
            }
        }
    }

    /// The internal symbol name to use when BUILDING an application of `name`
    /// to `args`: the instance-mangled name for a parametric-datatype
    /// constructor/selector/tester (so the term is name-disjoint per instance),
    /// or the surface `name` unchanged for monomorphic datatypes / non-datatype
    /// symbols. `overload` is the already-computed overload resolution (if any),
    /// reused so this does not re-resolve.
    pub(super) fn datatype_internal_name(
        &self,
        name: &str,
        args: &[TermId],
        overload: Option<&SymbolInfo>,
    ) -> String {
        if let Some(info) = overload {
            return info
                .internal_name
                .clone()
                .unwrap_or_else(|| name.to_string());
        }
        // Single registered instance (in `symbols`, not yet overloaded): use its
        // internal name when its argument sorts match this application.
        if let Some(info) = self.symbols.get(name) {
            if let Some(internal) = &info.internal_name {
                if info.arg_sorts.len() == args.len()
                    && info
                        .arg_sorts
                        .iter()
                        .zip(args.iter())
                        .all(|(expected, arg)| expected == self.terms.sort(*arg))
                {
                    return internal.clone();
                }
            }
        }
        name.to_string()
    }

    pub(super) fn resolve_overloaded_symbol(
        &self,
        name: &str,
        args: &[TermId],
    ) -> Result<Option<SymbolInfo>> {
        let Some(candidates) = self.overloaded_symbols.get(name) else {
            return Ok(None);
        };

        let signature_matches = |info: &&SymbolInfo, allow_int_to_real: bool| {
            info.arg_sorts.len() == args.len()
                && info
                    .arg_sorts
                    .iter()
                    .zip(args.iter())
                    .all(|(expected, arg)| {
                        let actual = self.terms.sort(*arg);
                        expected == actual
                            || (allow_int_to_real
                                && expected == &Sort::Real
                                && actual == &Sort::Int)
                    })
        };

        // Prefer an exact overload over one that needs the SMT-LIB Int-to-Real
        // coercion. For example, `f(Int)` wins over `f(Real)` at an Int term.
        let mut matches = candidates
            .iter()
            .filter(|info| signature_matches(info, false));

        if let Some(first) = matches.next().cloned() {
            if matches.next().is_some() {
                return Err(ElaborateError::Unsupported(format!(
                    "ambiguous overloaded symbol '{name}'"
                )));
            }
            return Ok(Some(first));
        }

        let mut matches = candidates
            .iter()
            .filter(|info| signature_matches(info, self.int_real_coercions()));
        let Some(first) = matches.next().cloned() else {
            return Ok(None);
        };

        if matches.next().is_some() {
            return Err(ElaborateError::Unsupported(format!(
                "ambiguous overloaded symbol '{name}'"
            )));
        }

        Ok(Some(first))
    }

    fn symbol_candidates(&self, name: &str) -> Option<&[SymbolInfo]> {
        self.overloaded_symbols
            .get(name)
            .map(Vec::as_slice)
            .or_else(|| self.symbols.get(name).map(std::slice::from_ref))
    }

    /// Resolve a bare identifier to one nullary declaration.
    ///
    /// SMT-LIB permits declarations that differ only in result sort. Without
    /// an expected-sort-directed elaborator a bare use of two such constants is
    /// ambiguous; selecting the most recently registered entry is unsound.
    /// Likewise, a non-nullary function name is not a value by itself.
    pub(super) fn resolve_bare_declared_symbol(&self, name: &str) -> Result<Option<SymbolInfo>> {
        let Some(candidates) = self.symbol_candidates(name) else {
            return Ok(None);
        };
        let mut matches = candidates.iter().filter(|info| info.arg_sorts.is_empty());
        let Some(first) = matches.next().cloned() else {
            return Err(ElaborateError::InvalidConstant(format!(
                "function '{name}' requires arguments"
            )));
        };
        if matches.next().is_some() {
            return Err(ElaborateError::Unsupported(format!(
                "ambiguous nullary symbol '{name}'"
            )));
        }
        Ok(Some(first))
    }

    /// Resolve an indexed higher-order reference such as `(_ as-array f)` by
    /// arity when no operand supplies the function's domain sorts.
    pub(super) fn resolve_declared_symbol_with_arity(
        &self,
        name: &str,
        arity: usize,
    ) -> Result<Option<SymbolInfo>> {
        let Some(candidates) = self.symbol_candidates(name) else {
            return Ok(None);
        };
        let mut matches = candidates
            .iter()
            .filter(|info| info.arg_sorts.len() == arity);
        let Some(first) = matches.next().cloned() else {
            return Ok(None);
        };
        if matches.next().is_some() {
            return Err(ElaborateError::Unsupported(format!(
                "ambiguous {arity}-argument symbol '{name}'"
            )));
        }
        Ok(Some(first))
    }

    /// Resolve `(_ map f)` against the exact element sorts of its array
    /// operands. Coercive matches are deliberately excluded: the array-map
    /// term/rewrite layer cannot materialize pointwise Int-to-Real coercions.
    pub(super) fn resolve_declared_symbol_for_domain(
        &self,
        name: &str,
        actual_sorts: &[Sort],
    ) -> Result<Option<SymbolInfo>> {
        let Some(candidates) = self.symbol_candidates(name) else {
            return Ok(None);
        };
        let mut matches = candidates
            .iter()
            .filter(|info| info.arg_sorts == actual_sorts);
        let Some(first) = matches.next().cloned() else {
            return Ok(None);
        };
        if matches.next().is_some() {
            return Err(ElaborateError::Unsupported(format!(
                "ambiguous overloaded symbol '{name}' for array-map domain"
            )));
        }
        Ok(Some(first))
    }

    /// Resolve a qualified identifier `((as name Result) args...)` against its
    /// complete declared signature.  The result ascription participates in
    /// overload selection; arguments must match exactly or through SMT-LIB's
    /// sole implicit application coercion, Int to Real.  Selecting by the
    /// result sort alone would admit ill-sorted applications, while selecting
    /// the last declaration would conflate overloaded identities.
    pub(super) fn resolve_qualified_declared_symbol(
        &self,
        name: &str,
        result_sort: &Sort,
        args: &[TermId],
    ) -> Result<Option<SymbolInfo>> {
        let Some(candidates) = self.symbol_candidates(name) else {
            return Ok(None);
        };

        let signature_matches = |info: &&SymbolInfo, allow_int_to_real: bool| {
            &info.sort == result_sort
                && info.arg_sorts.len() == args.len()
                && info
                    .arg_sorts
                    .iter()
                    .zip(args.iter())
                    .all(|(expected, arg)| {
                        let actual = self.terms.sort(*arg);
                        expected == actual
                            || (allow_int_to_real
                                && expected == &Sort::Real
                                && actual == &Sort::Int)
                    })
        };

        let mut exact = candidates
            .iter()
            .filter(|info| signature_matches(info, false));
        if let Some(first) = exact.next().cloned() {
            if exact.next().is_some() {
                return Err(ElaborateError::Unsupported(format!(
                    "ambiguous qualified symbol '(as {name} {result_sort})'"
                )));
            }
            return Ok(Some(first));
        }

        let mut coercive = candidates
            .iter()
            .filter(|info| signature_matches(info, self.int_real_coercions()));
        let Some(first) = coercive.next().cloned() else {
            return Ok(None);
        };
        if coercive.next().is_some() {
            return Err(ElaborateError::Unsupported(format!(
                "ambiguous qualified symbol '(as {name} {result_sort})'"
            )));
        }
        Ok(Some(first))
    }

    /// Process a command
    pub fn process_command(&mut self, cmd: &Command) -> Result<Option<CommandResult>> {
        self.validate_command_execution_mode(cmd)?;
        self.validate_command_against_declared_logic(cmd)?;
        if matches!(
            cmd,
            Command::SetLogic(_)
                | Command::DeclareSort(..)
                | Command::DeclareSortParameter(..)
                | Command::DefineSort(..)
                | Command::DeclareDatatype(..)
                | Command::DeclareDatatypes(..)
                | Command::DeclareFun(..)
                | Command::DeclareConst(..)
                | Command::DefineFun(..)
                | Command::DefineFunRec(..)
                | Command::DefineFunsRec(..)
                | Command::Assert(..)
                | Command::AssertSoft { .. }
                | Command::Push(..)
                | Command::Pop(..)
                | Command::Reset
                | Command::ResetAssertions
                | Command::CheckSat
                | Command::CheckSatAssuming(..)
                | Command::Maximize(..)
                | Command::Minimize(..)
        ) {
            self.clear_materialized_polymorphic_assertions();
        }
        match cmd {
            Command::SetLogic(logic) => {
                self.validate_logic_sort_parameter_conflicts(logic)?;
                self.logic = Some(logic.clone());
                // This one came from the command stream, so a LATER one in the
                // same stream is z3's "already been set" error.
                self.logic_set_by_command = true;
                self.refresh_polymorphic_declarations()?;
                Ok(None)
            }
            Command::DeclareConst(name, sort) => {
                if self.rank_sort_parameters(&[], sort).is_empty() {
                    self.declare_const(name, sort)?;
                    self.refresh_polymorphic_declarations()?;
                } else {
                    self.declare_polymorphic_fun(name, &[], sort)?;
                }
                Ok(None)
            }
            Command::DeclareFun(name, arg_sorts, ret_sort) => {
                if self.rank_sort_parameters(arg_sorts, ret_sort).is_empty() {
                    self.declare_fun(name, arg_sorts, ret_sort)?;
                    self.refresh_polymorphic_declarations()?;
                } else {
                    self.declare_polymorphic_fun(name, arg_sorts, ret_sort)?;
                }
                Ok(None)
            }
            Command::DefineFun(name, params, ret_sort, body) => {
                if self
                    .function_definition_sort_parameters(params, ret_sort, body)
                    .is_empty()
                {
                    self.define_fun(name, params, ret_sort, body)?;
                } else {
                    self.define_function_with_sort_parameters(name, params, ret_sort, body)?;
                }
                Ok(None)
            }
            Command::DefineFunRec(name, params, ret_sort, body) => {
                if self
                    .function_definition_sort_parameters(params, ret_sort, body)
                    .is_empty()
                {
                    // Register the symbol first so the body can reference it.
                    self.define_fun_rec(name, params, ret_sort, body)?;
                } else {
                    self.define_recursive_function_with_sort_parameters(
                        name, params, ret_sort, body,
                    )?;
                }
                Ok(None)
            }
            Command::DefineFunsRec(declarations, bodies) => {
                let polymorphic =
                    declarations
                        .iter()
                        .zip(bodies)
                        .any(|((_name, params, ret_sort), body)| {
                            !self
                                .function_definition_sort_parameters(params, ret_sort, body)
                                .is_empty()
                        });
                if polymorphic {
                    self.define_recursive_functions_with_sort_parameters(declarations, bodies)?;
                } else {
                    // Register all symbols first so the bodies can reference peers.
                    self.define_funs_rec(declarations, bodies)?;
                }
                Ok(None)
            }
            Command::DeclareVar(_, _)
            | Command::SynthFun(_, _, _, _)
            | Command::SynthInv(_, _, _)
            | Command::SygusConstraint(_)
            | Command::InvConstraint(_, _, _, _)
            | Command::CheckSynth => Err(ElaborateError::Unsupported(
                "SyGuS commands are parsed but not executable yet".to_string(),
            )),
            // Z3 fixedpoint (CHC) commands are not executed by the DPLL(T)
            // elaborator. A genuine fixedpoint script is detected and routed to
            // the ay-chc engine before reaching this path; reaching here means a
            // fixedpoint construct appeared in a non-fixedpoint context, which
            // we soundly reject as unsupported rather than mis-evaluate.
            Command::DeclareRel(_, _) | Command::Rule(_) | Command::Query(_) => {
                Err(ElaborateError::Unsupported(
                    "fixedpoint commands (declare-rel/rule/query) are handled by the CHC engine, \
                     not the DPLL(T) solver"
                        .to_string(),
                ))
            }
            Command::Assert(term) => {
                self.assert_authored(term)?;
                Ok(None)
            }
            Command::AssertSoft {
                term,
                weight,
                id: group,
            } => {
                // A soft assertion elaborates like a normal assert, but it is
                // recorded separately and is NOT pushed onto the hard assertion
                // stack — the solver may leave it violated. It must still be a
                // Bool, mirroring the hard-assert sort contract.
                let term_id = self.elaborate_term(term, &HashMap::default())?;
                let sort = self.terms.sort(term_id);
                if *sort != Sort::Bool {
                    return Err(ElaborateError::SortMismatch {
                        expected: "Bool".to_string(),
                        actual: format!("{sort:?}"),
                    });
                }
                let public_metadata = self.validate_public_assertion(term, term_id)?;
                self.add_soft_constraint(SoftAssertion {
                    term: term_id,
                    weight: *weight,
                    id: group.clone(),
                });
                if let Some(metadata) = self.soft_finite_set_metadata.last_mut() {
                    *metadata = public_metadata;
                }
                Ok(None)
            }
            Command::Maximize(term) => {
                let id = self.elaborate_term(term, &HashMap::default())?;
                let public_metadata = self.validate_public_assertion(term, id)?;
                self.objectives.push(Objective {
                    direction: ObjectiveDirection::Maximize,
                    term: id,
                });
                self.objective_finite_set_metadata.push(public_metadata);
                Ok(None)
            }
            Command::Minimize(term) => {
                let id = self.elaborate_term(term, &HashMap::default())?;
                let public_metadata = self.validate_public_assertion(term, id)?;
                self.objectives.push(Objective {
                    direction: ObjectiveDirection::Minimize,
                    term: id,
                });
                self.objective_finite_set_metadata.push(public_metadata);
                Ok(None)
            }
            Command::Push(n) => {
                // Recorded BEFORE the preflight: a rejected push still tells a
                // diagnostic consumer that this is not a single-shot query.
                self.scope_commands_used = true;
                let count = usize::try_from(*n).map_err(|_| {
                    ElaborateError::Unsupported("push count does not fit this target".to_string())
                })?;
                let Some(new_depth) = self.scopes.len().checked_add(count) else {
                    return Err(ElaborateError::Unsupported(
                        "incremental scope depth overflow".to_string(),
                    ));
                };
                if new_depth > MAX_INCREMENTAL_SCOPE_DEPTH {
                    return Err(ElaborateError::Unsupported(format!(
                        "incremental scope depth {new_depth} exceeds the supported maximum \
                         {MAX_INCREMENTAL_SCOPE_DEPTH}"
                    )));
                }
                // Reserve before changing the depth so allocation failure is
                // reported without leaving a partially pushed prefix.
                self.scopes.try_reserve(count).map_err(|_| {
                    ElaborateError::Unsupported(
                        "unable to allocate incremental scope frames".to_string(),
                    )
                })?;
                for _ in 0..count {
                    self.push();
                }
                Ok(None)
            }
            Command::Pop(n) => {
                self.scope_commands_used = true;
                let count = usize::try_from(*n).map_err(|_| ElaborateError::ScopeUnderflow)?;
                // Preflight the whole request.  Popping a valid prefix and
                // then reporting underflow would leave assertions,
                // declarations, and objectives partially rolled back.
                if count > self.scopes.len() {
                    return Err(ElaborateError::ScopeUnderflow);
                }
                for _ in 0..count {
                    let popped = self.pop();
                    debug_assert!(popped, "pop count was preflighted against scope depth");
                }
                Ok(None)
            }
            Command::CheckSat => {
                self.materialize_polymorphic_assertions()?;
                self.check_sat_commands = self.check_sat_commands.saturating_add(1);
                Ok(Some(CommandResult::CheckSat))
            }
            Command::CheckSatAssuming(terms) => {
                // The assumptions are NOT part of `assertions_parsed`, so a
                // surface-syntax consumer cannot see the full query. Treated
                // exactly like a scope command: not a single-shot query.
                self.check_sat_commands = self.check_sat_commands.saturating_add(1);
                self.scope_commands_used = true;
                self.materialize_polymorphic_assertions()?;
                if terms
                    .iter()
                    .any(|term| !self.term_sort_parameters(term).is_empty())
                {
                    self.polymorphic_instantiation_complete = false;
                    return Ok(Some(CommandResult::CheckSatAssuming(Vec::new())));
                }
                // Elaborate each assumption term to get its TermId
                let term_ids: Vec<TermId> = terms
                    .iter()
                    .map(|term| {
                        let id = self.elaborate_term(term, &HashMap::default())?;
                        self.validate_public_term(term)?;
                        Ok(id)
                    })
                    .collect::<Result<Vec<_>>>()?;
                Ok(Some(CommandResult::CheckSatAssuming(term_ids)))
            }
            Command::GetModel => Ok(Some(CommandResult::GetModel)),
            Command::GetObjectives => Ok(Some(CommandResult::GetObjectives)),
            Command::GetObjectiveCertificates => Ok(Some(CommandResult::GetObjectiveCertificates)),
            Command::GetValue(terms) => {
                // Elaborate each term to its TermId while preserving the original
                // SMT-LIB text for the verbatim `(get-value ...)` key echo.
                let pairs: Vec<(String, TermId)> = terms
                    .iter()
                    .map(|(text, t)| {
                        let id = self.elaborate_term(t, &HashMap::default())?;
                        self.validate_public_term(t)?;
                        Ok((text.clone(), id))
                    })
                    .collect::<Result<Vec<_>>>()?;
                Ok(Some(CommandResult::GetValue(pairs)))
            }
            Command::Eval(term) => {
                // (eval t) is Z3 shorthand for get-value of one term: elaborate
                // the term and let the executor print just its model value.
                let term_id = self.elaborate_term(term, &HashMap::default())?;
                self.validate_public_term(term)?;
                Ok(Some(CommandResult::Eval(term_id)))
            }
            Command::GetConsequences(assumptions, variables) => {
                let assumption_ids: Vec<TermId> = assumptions
                    .iter()
                    .map(|term| {
                        let id = self.elaborate_term(term, &HashMap::default())?;
                        self.validate_public_term(term)?;
                        Ok(id)
                    })
                    .collect::<Result<Vec<_>>>()?;
                let variable_ids: Vec<TermId> = variables
                    .iter()
                    .map(|term| {
                        let id = self.elaborate_term(term, &HashMap::default())?;
                        self.validate_public_term(term)?;
                        Ok(id)
                    })
                    .collect::<Result<Vec<_>>>()?;
                Ok(Some(CommandResult::GetConsequences(
                    assumption_ids,
                    variable_ids,
                )))
            }
            Command::GetAbduct(name, goal) => {
                let goal_id = self.elaborate_term(goal, &HashMap::default())?;
                self.validate_public_term(goal)?;
                Ok(Some(CommandResult::GetAbduct(name.clone(), goal_id)))
            }
            Command::GetInfo(keyword) => Ok(Some(CommandResult::GetInfo(keyword.clone()))),
            Command::GetOption(keyword) => Ok(Some(CommandResult::GetOption(keyword.clone()))),
            Command::Labels => Ok(Some(CommandResult::Labels)),
            Command::GetAssertions => Ok(Some(CommandResult::GetAssertions)),
            Command::SetOption(keyword, value) => {
                self.set_option(keyword, value);
                Ok(None)
            }
            Command::SetOptionAttribute(keyword) => Err(ElaborateError::Unsupported(format!(
                "valueless solver option {keyword}"
            ))),
            Command::Exit => Ok(Some(CommandResult::Exit)),
            Command::Reset => {
                // Preserve the host-configured parsed-assertion retention
                // policy across `(reset)` — it reflects the session's proof
                // configuration (e.g. `--no-proof`), not per-script state.
                let retain_parsed = self.retain_parsed_assertions;
                let finite_set_typing_mode = self.finite_set_typing_mode;
                let strict_logic_compliance = self.strict_logic_compliance;
                *self = Self::new();
                self.retain_parsed_assertions = retain_parsed;
                self.finite_set_typing_mode = finite_set_typing_mode;
                self.strict_logic_compliance = strict_logic_compliance;
                Ok(None)
            }
            Command::ResetAssertions => {
                if self.strict_logic_compliance {
                    // SMT-LIB 2.7 removes every assertion level beyond the
                    // first. Popping the frames (instead of merely clearing
                    // the vector) also retires declarations and definitions
                    // introduced in those levels when
                    // :global-declarations is false.
                    while self.pop() {}
                } else {
                    // Z3 5.0.0 keeps its public assertion-stack level across
                    // reset-assertions. Preserve the historical executor
                    // behavior used by --z3-mode: discard the materialized
                    // frames while the CLI retains the public level and
                    // simulates later pops.
                    self.scopes.clear();
                }
                self.assertions.clear();
                self.assertion_finite_set_metadata.clear();
                self.assertions_parsed.clear();
                self.objectives.clear();
                self.objective_finite_set_metadata.clear();
                self.soft_constraints.clear();
                self.soft_finite_set_metadata.clear();
                // Named formulas are assertion provenance. Keeping them after
                // their assertions and scope frames are gone can make a later
                // syntactically identical assertion inherit a stale core label.
                self.named_terms.clear();
                // #quantprod-g3: an adopted definitional macro is justified
                // ONLY by its (now removed) assertion — un-adopt it, or later
                // asserts would keep expanding an unconstrained `f`. Plain
                // `define-fun` macros persist as before.
                for name in self.adopted_macro_interps.keys() {
                    self.fun_defs.remove(name.as_str());
                }
                self.adopted_macro_interps.clear();
                self.polymorphic_assertions
                    .retain(|assertion| assertion.persistent_definition);
                self.authored_assertions.clear();
                self.materialized_polymorphic_assertions = 0;
                self.polymorphic_instantiation_complete = true;
                Ok(None)
            }
            // Declare/define sort are stored but don't produce output
            Command::DeclareSort(name, arity) => {
                // `RoundingMode` and Float16/32/64/128 are builtin FP sorts.
                // In particular, RM literals (`RNE` … `roundTowardZero`)
                // elaborate to `Sort::Uninterpreted("RoundingMode")`, and the
                // executor's finite-domain pass keys on that sort name. A user
                // redeclaration would either conflate that fixed domain or be
                // silently ignored by the abbreviation matcher; z3 rejects all
                // of them as already defined. (#P0.2 symbolic RoundingMode)
                self.ensure_sort_name_available(name)?;
                // A non-zero-arity uninterpreted sort constructor needs an
                // identity that includes its instantiated arguments.  The
                // core currently has no faithful representation for that;
                // treating it as a monomorphic `Uninterpreted(name)` silently
                // accepts ill-sorted scripts, so fail closed.
                if *arity != 0 {
                    return Err(ElaborateError::Unsupported(format!(
                        "non-zero-arity declare-sort '{name}' (arity {arity})"
                    )));
                }
                // Store as uninterpreted sort
                let sort = Sort::Uninterpreted(name.clone());
                self.sort_defs.insert(name.clone(), sort.clone());
                self.public_sort_defs
                    .insert(name.clone(), super::PublicSort::Core(sort));
                self.track_scoped_sort_def(name.clone());
                self.refresh_polymorphic_declarations()?;
                Ok(None)
            }
            Command::DeclareSortParameter(name) => {
                self.declare_sort_parameter(name)?;
                Ok(None)
            }
            Command::DefineSort(name, params, sort) => {
                self.ensure_sort_name_available(name)?;
                let mut unique_params = ay_core::kani_compat::DetHashSet::default();
                if let Some(duplicate) = params
                    .iter()
                    .find(|param| !unique_params.insert(param.as_str()))
                {
                    return Err(ElaborateError::InvalidConstant(format!(
                        "duplicate define-sort parameter: {duplicate}"
                    )));
                }
                self.validate_define_sort_parameters(params, sort)?;
                if params.is_empty() {
                    // Monomorphic synonym: eagerly elaborate and store the sort.
                    let public_sort = self.elaborate_public_sort(sort)?;
                    let elaborated = self.elaborate_sort(sort)?;
                    self.sort_defs.insert(name.clone(), elaborated);
                    self.public_sort_defs.insert(name.clone(), public_sort);
                } else {
                    // Parameterized synonym: keep the body as a template so each
                    // ground use `(Name A1 .. An)` substitutes the type parameters
                    // and elaborates the body. Storing an eagerly-elaborated body
                    // would bind the parameters to `Uninterpreted("T")`. (z3 parity)
                    self.parametric_sort_defs
                        .insert(name.clone(), (params.clone(), sort.clone()));
                }
                self.track_scoped_sort_def(name.clone());
                self.refresh_polymorphic_declarations()?;
                Ok(None)
            }
            Command::DeclareDatatype(name, datatype_dec) => {
                if is_builtin_theory_sort(name) {
                    return Err(ElaborateError::ReservedSymbol(name.clone()));
                }
                self.declare_datatype(name, datatype_dec)?;
                self.refresh_polymorphic_declarations()?;
                Ok(None)
            }
            Command::DeclareDatatypes(sort_decs, datatype_decs) => {
                if let Some(sort_dec) = sort_decs
                    .iter()
                    .find(|sort_dec| is_builtin_theory_sort(&sort_dec.name))
                {
                    return Err(ElaborateError::ReservedSymbol(sort_dec.name.clone()));
                }
                self.declare_datatypes(sort_decs, datatype_decs)?;
                self.refresh_polymorphic_declarations()?;
                Ok(None)
            }
            // SetInfo is acknowledged but not required to produce output
            Command::SetInfo(_, _) | Command::SetInfoAttribute(_) => Ok(None),
            // Echo returns the message to be printed (handled by executor)
            Command::Echo(msg) => Ok(Some(CommandResult::Echo(msg.clone()))),
            Command::GetAssignment => Ok(Some(CommandResult::GetAssignment)),
            Command::GetUnsatCore => Ok(Some(CommandResult::GetUnsatCore)),
            Command::GetUnsatCoreWithFarkas => Ok(Some(CommandResult::GetUnsatCoreWithFarkas)),
            Command::GetUnsatAssumptions => Ok(Some(CommandResult::GetUnsatAssumptions)),
            Command::GetProof => Ok(Some(CommandResult::GetProof)),
            Command::Display(term, source) => {
                let _ = self.elaborate_term(term, &HashMap::default())?;
                self.validate_public_term(term)?;
                Ok(Some(CommandResult::Display(source.clone())))
            }
            Command::DebugSet(name, term, source) => {
                let _ = self.elaborate_term(term, &HashMap::default())?;
                self.validate_public_term(term)?;
                self.z3_debug_exprs.insert(name.clone(), source.clone());
                Ok(None)
            }
            Command::DebugPpVar(name) => {
                let source = self.z3_debug_exprs.get(name).cloned().ok_or_else(|| {
                    ElaborateError::Unsupported(format!("unknown global variable {name}"))
                })?;
                Ok(Some(CommandResult::Display(source)))
            }
            Command::Simplify(term) => {
                let term_id = self.elaborate_term(term, &HashMap::default())?;
                self.validate_public_term(term)?;
                Ok(Some(CommandResult::Simplify(term_id)))
            }
            // `(apply <tactic>)`: no term elaboration is needed — the tactic
            // names no terms; the executor runs it over the already-elaborated
            // assertions. The tactic is forwarded verbatim to the executor.
            Command::Apply(tactic) => Ok(Some(CommandResult::Apply(tactic.clone()))),
            // Craig interpolation (get-interpolant / compute-interpolant) is a
            // Z3/SeaHorn/KLEE extension computed by the ay-chc Farkas/Craig
            // machinery, which the DPLL(T) executor cannot reach. The CLI
            // intercepts these commands before reaching the executor; reaching
            // here (e.g. native API / FFI use) is soundly reported as
            // unsupported rather than producing a wrong interpolant.
            Command::GetInterpolant(_, _) | Command::ComputeInterpolant(_, _) => {
                Err(ElaborateError::Unsupported(
                    "get-interpolant/compute-interpolant are handled by the CHC interpolation \
                     engine via the CLI, not the DPLL(T) executor"
                        .to_string(),
                ))
            }
        }
    }

    /// Process one native-API declaration as global to assertion scopes while
    /// leaving both spellings of the public global-declarations option exactly
    /// unchanged. Callers still own executor-level result invalidation.
    #[doc(hidden)]
    pub fn execute_native_global_declaration(
        &mut self,
        cmd: &Command,
    ) -> Result<Option<CommandResult>> {
        if !matches!(
            cmd,
            Command::DeclareSort(..)
                | Command::DeclareSortParameter(..)
                | Command::DefineSort(..)
                | Command::DeclareDatatype(..)
                | Command::DeclareDatatypes(..)
                | Command::DeclareFun(..)
                | Command::DeclareConst(..)
                | Command::DefineFun(..)
                | Command::DefineFunRec(..)
                | Command::DefineFunsRec(..)
        ) {
            return Err(ElaborateError::Unsupported(
                "native global-declaration execution accepts only declaration commands".to_string(),
            ));
        }
        self.with_native_global_declaration_tracking(|ctx| ctx.process_command(cmd))
    }

    /// Set a solver option
    fn set_option(&mut self, keyword: &str, value: &crate::sexp::SExpr) {
        use crate::sexp::SExpr;
        let key = keyword.trim_start_matches(':').to_string();
        let opt_value = match value {
            SExpr::True => OptionValue::Bool(true),
            SExpr::False => OptionValue::Bool(false),
            SExpr::Numeral(n) => OptionValue::Numeral(n.clone()),
            SExpr::String(s) | SExpr::Symbol(s) => OptionValue::String(s.clone()),
            _ => return, // Ignore unsupported value types
        };
        // Proofs explicitly requested mid-session: parsed-assertion retention
        // must be back ON so proof export can align surface syntax for every
        // assertion from this point (SMT-LIB scripts set :produce-proofs before
        // any assert, so the stacks are normally still empty and stay fully
        // aligned; a nonstandard late enable is handled by the prefix-alignment
        // guard at the push sites).
        if key == "produce-proofs" && matches!(opt_value, OptionValue::Bool(true)) {
            self.retain_parsed_assertions = true;
        }
        if key == "numeral-as-real" {
            if let OptionValue::Bool(enabled) = &opt_value {
                self.numeral_as_real = *enabled;
            }
        }
        if key == "int-real-coercions" {
            if let OptionValue::Bool(enabled) = &opt_value {
                self.int_real_coercions = *enabled;
            }
        }
        if key == "global-declarations" || key == "global-decls" {
            self.options
                .insert("global-declarations".to_string(), opt_value.clone());
            self.options.insert("global-decls".to_string(), opt_value);
        } else {
            self.options.insert(key, opt_value);
        }
    }

    /// Get an option value
    pub fn get_option(&self, keyword: &str) -> Option<&OptionValue> {
        let key = keyword.trim_start_matches(':');
        self.options.get(key)
    }

    pub(super) fn numeral_as_real(&self) -> bool {
        self.numeral_as_real
    }

    pub(super) fn int_real_coercions(&self) -> bool {
        self.int_real_coercions
    }

    /// Iterate over named terms (for get-assignment)
    pub fn named_terms_iter(&self) -> impl Iterator<Item = (&str, TermId)> {
        self.named_terms.iter().map(|(k, v)| (k.as_str(), *v))
    }

    /// Register a named term for get-assignment and get-unsat-core.
    ///
    /// Tracks in the current scope so the name is removed on pop().
    pub fn register_named_term(&mut self, name: String, term_id: TermId) {
        self.named_terms.insert(name.clone(), term_id);
        if let Some(scope) = self.scopes.last_mut() {
            scope.named_terms.push(name);
        }
    }

    /// Iterate over declared datatypes: (dt_name, constructor_names)
    ///
    /// Returns an iterator over all datatype definitions with their constructor names.
    /// Used by theory solvers (e.g., DtSolver) to register datatype information.
    pub fn datatype_iter(&self) -> impl Iterator<Item = (&str, &[String])> {
        self.datatypes
            .iter()
            .map(|(name, ctors)| (name.as_str(), ctors.as_slice()))
    }

    /// Check if a symbol name is a datatype constructor
    ///
    /// Returns Some((dt_name, ctor_name)) if the symbol is a constructor,
    /// None otherwise. Used by theory solvers to identify constructor applications.
    pub fn is_constructor(&self, name: &str) -> Option<(String, String)> {
        self.constructors.get(name).cloned()
    }

    /// Get the selector names for a constructor symbol.
    ///
    /// Returns selector names in the order they appear in the datatype declaration.
    /// Used by DT theory solver to generate selector axioms.
    pub fn constructor_selectors(&self, ctor_name: &str) -> Option<&[String]> {
        self.ctor_selectors.get(ctor_name).map(Vec::as_slice)
    }

    /// Get selector metadata for a constructor in declaration order.
    pub fn constructor_selector_info(&self, ctor_name: &str) -> Option<&[(String, Sort)]> {
        self.ctor_selector_info.get(ctor_name).map(Vec::as_slice)
    }

    /// Per-instance selector metadata for `ctor_name` (the INTERNAL, possibly
    /// instance-mangled constructor name).
    ///
    /// Parametric datatypes monomorphize to instances whose
    /// constructors/selectors carry INSTANCE-MANGLED internal names (e.g.
    /// `mk@Pair!{Int}!{Int}`), so the by-name [`Self::ctor_selector_info`] map is
    /// already instance-disjoint and exact. The `dt_name` argument is retained
    /// for call-site clarity (it equals the instance whose mangled `ctor_name`
    /// this is) but the lookup keys solely on the unique internal name.
    pub fn constructor_selector_info_in(
        &self,
        _dt_name: &str,
        ctor_name: &str,
    ) -> Option<Vec<(String, Sort)>> {
        self.ctor_selector_info.get(ctor_name).cloned()
    }

    /// The bound term of the NULLARY constructor `ctor_name` **of the datatype
    /// `dt_name`**.
    ///
    /// Two datatypes may share a constructor name (SMT-LIB 2.6 §4.2.3 ad-hoc
    /// overloading; §3.6.4's `(as f σ)` exists to disambiguate it), and each
    /// nullary constructor is bound to its own distinct term. `self.symbols`
    /// keeps only the last-registered signature, so looking the name up bare
    /// returns the most recently declared datatype's inhabitant regardless of
    /// which datatype was asked for. Select by result sort instead — that is
    /// exactly the ascription's own resolution rule — and only fall back to the
    /// bare entry when the name is not overloaded at all.
    pub(super) fn nullary_ctor_term_in(&self, dt_name: &str, ctor_name: &str) -> Option<TermId> {
        let wanted = Sort::Uninterpreted(dt_name.to_string());
        let candidates = self.symbol_candidates(ctor_name)?;
        let mut matches = candidates
            .iter()
            .filter(|info| info.arg_sorts.is_empty() && info.sort == wanted);
        let first = matches.next()?;
        // Two nullary constructors of the SAME datatype cannot share a name, so
        // an ambiguity here means the tables are inconsistent: decline rather
        // than pick one (the caller then leaves the constant a free datatype
        // variable, which is always sound).
        if matches.next().is_some() {
            return None;
        }
        first.term
    }

    /// Iterate over all constructor -> selector mappings.
    ///
    /// Returns (constructor_name, selector_names) pairs. Used by the DT theory
    /// solver to identify selector applications when propagating axioms through
    /// variable indirection (#1740).
    pub fn ctor_selectors_iter(&self) -> impl Iterator<Item = (&String, &Vec<String>)> {
        self.ctor_selectors.iter()
    }

    /// Get the return sort of a declared symbol.
    ///
    /// Returns the return sort for function/constructor/selector symbols.
    /// Used by DT theory solver to build selector application terms.
    pub fn symbol_sort(&self, name: &str) -> Option<&Sort> {
        self.symbols.get(name).map(|info| &info.sort)
    }

    /// Get full symbol information for a declared symbol.
    ///
    /// Returns the [`SymbolInfo`] for a symbol, including its return sort
    /// and argument sorts. Used by the API layer to validate datatype
    /// constructor/selector/tester usage.
    pub fn symbol_info(&self, name: &str) -> Option<&SymbolInfo> {
        self.symbols.get(name)
    }

    /// Resolve one core term identity to its exact declaration signature.
    /// Unlike [`Self::symbol_info`], this accepts private overload/datatype
    /// identities and never substitutes the most recently declared signature.
    pub fn symbol_info_by_identity(&self, identity: &str) -> Option<&SymbolInfo> {
        let surface_name = self.dt_surface_name(identity).unwrap_or(identity);
        self.symbol_candidates(surface_name)?
            .iter()
            .find(|info| self.symbol_identity_name(surface_name, info) == identity)
    }
}

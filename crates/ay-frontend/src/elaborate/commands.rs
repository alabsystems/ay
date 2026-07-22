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

/// Builtin simple sort names supplied by the SMT-LIB FloatingPoint theory.
/// User aliases/declarations with these names would either shadow
/// `RoundingMode`'s fixed five-element semantics or be silently ignored by the
/// FP abbreviation match in `sorts.rs`.
const BUILTIN_FP_SIMPLE_SORT_NAMES: &[&str] =
    &["RoundingMode", "Float16", "Float32", "Float64", "Float128"];

fn is_builtin_fp_simple_sort(name: &str) -> bool {
    BUILTIN_FP_SIMPLE_SORT_NAMES.contains(&name)
}

impl Context {
    /// Add an assertion
    pub(crate) fn assert(&mut self, term: &ParsedTerm) -> Result<()> {
        // #quantprod-g3: a pure definitional forall over a never-yet-used
        // declared function adopts it as a macro (fail-closed; see the
        // method). On adoption the elaboration below expands every
        // `f`-application, turning this assertion into the reflexive
        // tautology while `(get-model)` gains the definitional entry.
        self.try_adopt_definitional_forall(term);
        let id = self.elaborate_term(term, &HashMap::default())?;
        let sort = self.terms.sort(id);
        if *sort != Sort::Bool {
            return Err(ElaborateError::SortMismatch {
                expected: "Bool".to_string(),
                actual: format!("{sort:?}"),
            });
        }
        // Retain the original parsed AST only under the retention policy and
        // while the parallel assertion stacks remain prefix-aligned.
        if self.retain_parsed_assertions && self.assertions_parsed.len() == self.assertions.len() {
            self.assertions_parsed.push(term.clone());
        }
        self.assertions.push(id);
        Ok(())
    }

    /// Push a scope
    pub(crate) fn push(&mut self) {
        self.scopes.push(ScopeFrame {
            symbols: Vec::new(),
            assertion_count: self.assertions.len(),
            objective_count: self.objectives.len(),
            soft_constraint_count: self.soft_constraints.len(),
            named_terms: Vec::new(),
            datatypes: Vec::new(),
            constructors: Vec::new(),
            sort_defs: Vec::new(),
            fun_defs: Vec::new(),
            parametric_datatypes: Vec::new(),
        });
    }

    /// Pop a scope. Returns `true` on success, `false` on underflow (no scopes).
    pub(crate) fn pop(&mut self) -> bool {
        if let Some(frame) = self.scopes.pop() {
            // Remove symbols defined in this scope
            for name in frame.symbols {
                self.symbols.remove(&name);
                self.overloaded_symbols.remove(&name);
                self.internal_symbols.remove(&name);
            }
            // Remove assertions from this scope
            self.assertions.truncate(frame.assertion_count);
            self.assertions_parsed.truncate(frame.assertion_count);
            // Remove objectives from this scope
            self.objectives.truncate(frame.objective_count);
            // Remove soft constraints from this scope
            self.soft_constraints.truncate(frame.soft_constraint_count);
            // Remove named terms defined in this scope
            for name in frame.named_terms {
                self.named_terms.remove(&name);
            }
            // Remove datatypes defined in this scope
            for name in frame.datatypes {
                self.datatypes.remove(&name);
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

    /// Iterate over all declared symbols
    pub fn symbol_iter(&self) -> impl Iterator<Item = (&String, &SymbolInfo)> {
        self.symbols.iter()
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
    fn try_adopt_definitional_forall(&mut self, term: &ParsedTerm) {
        use crate::command::Term as PT;
        if !self.scopes.is_empty() {
            return;
        }
        let PT::Forall(pvars, pbody) = term else {
            return;
        };
        if pvars.is_empty() {
            return;
        }
        // Distinct binder names (duplicate binders make the "applied exactly
        // in order" reading ambiguous).
        for i in 0..pvars.len() {
            for j in (i + 1)..pvars.len() {
                if pvars[i].0 == pvars[j].0 {
                    return;
                }
            }
        }
        let PT::App(eq, pargs) = pbody.as_ref() else {
            return;
        };
        if eq != "=" || pargs.len() != 2 {
            return;
        }
        // The `f`-application side at the parsed level: `(f x1 … xk)` with
        // the binders in order.
        let side_f = |t: &PT| -> Option<String> {
            let PT::App(f, args) = t else {
                return None;
            };
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
            _ => return,
        };
        if self.fun_defs.contains_key(&fname)
            || self.recursive_fun_names.contains(&fname)
            || self.is_datatype_member_name(&fname)
            // An OVERLOADED symbol could keep a raw second-arity use alive
            // outside the macro expansion — refuse (fail-closed).
            || self.overloaded_symbols.contains_key(&fname)
        {
            return;
        }
        let Some(info) = self.symbols.get(&fname) else {
            return;
        };
        if info.arg_sorts.len() != pvars.len() {
            return;
        }
        // A pre-adoption raw occurrence of `f` in any existing constraint
        // would stay a disconnected uninterpreted symbol while later
        // occurrences expand — refuse (wrong-verdict source).
        if self.constraints_mention_symbol(&fname) {
            return;
        }
        let ret_sort = info.sort.clone();
        let arg_sorts = info.arg_sorts.clone();
        // Binder sorts must equal the declared argument sorts exactly.
        let mut params: Vec<(String, Sort)> = Vec::with_capacity(pvars.len());
        for ((vname, vsort), decl) in pvars.iter().zip(arg_sorts.iter()) {
            let Ok(s) = self.elaborate_sort(vsort) else {
                return;
            };
            if s != *decl {
                return;
            }
            params.push((vname.clone(), s));
        }
        // Validate on the ELABORATED forall (macro not yet registered): the
        // same structural shape must hold after elaboration, the definition
        // body must be `f`-free, and its sort must be the declared result
        // sort. Elaboration errors refuse adoption; the caller's normal
        // elaboration then surfaces the same error.
        let Ok(eid) = self.elaborate_term(term, &HashMap::default()) else {
            return;
        };
        let ay_core::TermData::Forall(evars, ebody, _) = self.terms.get(eid).clone() else {
            return;
        };
        if evars.len() != params.len() {
            return;
        }
        let ay_core::TermData::App(esym, eargs) = self.terms.get(ebody).clone() else {
            return;
        };
        if !matches!(&esym, ay_core::term::Symbol::Named(n) if n == "=") || eargs.len() != 2 {
            return;
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
            _ => return,
        };
        if self.term_mentions_symbol(def_body, &fname) {
            return;
        }
        if *self.terms.sort(def_body) != ret_sort {
            return;
        }
        // Adopt: future (re-)elaborations expand every `f`-application.
        self.fun_defs.insert(fname.clone(), (params, parsed_rhs));
        self.adopted_macro_interps.insert(fname, (evars, def_body));
    }

    /// True when `name` was bound by `define-fun-rec` / `define-funs-rec` (a
    /// recursive function), as opposed to a plain `define-fun` macro. z3
    /// overloads a `declare-*` against such a name instead of rejecting it; AY
    /// cannot represent that overload, so the CLI fail-closes such a case to
    /// `unknown` rather than answer on a misresolved binding. (#P0.3)
    pub fn is_recursive_fun(&self, name: &str) -> bool {
        self.recursive_fun_names.contains(name)
    }

    /// Register a symbol directly (for native API use)
    ///
    /// This is used by the native Rust API to register constants created
    /// via `mk_var` so they appear in models.
    pub fn register_symbol(&mut self, name: String, term: TermId, sort: Sort) {
        self.symbols.insert(
            name.clone(),
            SymbolInfo {
                term: Some(term),
                sort,
                arg_sorts: vec![],
                internal_name: None,
            },
        );
        self.track_scoped_symbol(name);
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
    ) -> Result<()> {
        // Reserved structural operators are safe only through their dedicated
        // builders. A textual alias could be intercepted by a specialized
        // elaboration path before ordinary function resolution.
        if is_reserved_symbol(&surface_name) {
            return Err(ElaborateError::ReservedSymbol(surface_name));
        }
        if self.is_datatype_member_name(&surface_name) {
            return Err(ElaborateError::DatatypeMemberCollision(surface_name));
        }
        let is_same_alias = |info: &SymbolInfo| {
            info.internal_name.as_deref() == Some(internal_name.as_str())
                && info.arg_sorts == arg_sorts
                && info.sort == ret_sort
        };
        if self.symbols.get(&surface_name).is_some_and(is_same_alias)
            || self
                .overloaded_symbols
                .get(&surface_name)
                .is_some_and(|aliases| aliases.iter().any(is_same_alias))
        {
            return Ok(());
        }
        self.register_overloadable_symbol(
            surface_name,
            SymbolInfo {
                term: None,
                sort: ret_sort,
                arg_sorts,
                internal_name: Some(internal_name),
            },
        );
        Ok(())
    }

    pub(super) fn register_overloadable_symbol(&mut self, name: String, info: SymbolInfo) {
        if let Some(existing) = self.symbols.get(&name).cloned() {
            self.overloaded_symbols
                .entry(name.clone())
                .or_insert_with(|| vec![existing])
                .push(info.clone());
        } else if let Some(overloads) = self.overloaded_symbols.get_mut(&name) {
            overloads.push(info.clone());
        }

        self.symbols.insert(name.clone(), info);
        self.track_scoped_symbol(name);
    }

    /// Resolve a nullary overloaded symbol (e.g. a parametric datatype's
    /// nullary constructor `nil`) to the bound term whose result sort matches
    /// `sort`. Used by `(as <name> <sort>)` so distinct datatype instantiations
    /// that share a constructor name resolve to the correct instance.
    pub(super) fn nullary_overload_with_sort(&self, name: &str, sort: &Sort) -> Option<TermId> {
        let candidates = self.overloaded_symbols.get(name)?;
        for info in candidates {
            if info.arg_sorts.is_empty() {
                if let Some(term) = info.term {
                    if self.terms.sort(term) == sort {
                        return Some(term);
                    }
                }
            }
        }
        None
    }

    /// The instance-internal (mangled) name of constructor `name` whose RESULT
    /// sort equals `result_sort` — used to resolve an `(as <ctor> <instance>)`
    /// ascription to the correct parametric instance. `None` for monomorphic
    /// constructors / non-datatype symbols (no mangling).
    pub(super) fn ctor_internal_for_result_sort(
        &self,
        name: &str,
        result_sort: &Sort,
    ) -> Option<String> {
        let matches = |info: &SymbolInfo| {
            if &info.sort == result_sort {
                info.internal_name.clone()
            } else {
                None
            }
        };
        if let Some(candidates) = self.overloaded_symbols.get(name) {
            if let Some(internal) = candidates.iter().find_map(matches) {
                return Some(internal);
            }
        }
        self.symbols.get(name).and_then(matches)
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

        let mut matches = candidates.iter().filter(|info| {
            info.arg_sorts.len() == args.len()
                && info
                    .arg_sorts
                    .iter()
                    .zip(args.iter())
                    .all(|(expected, arg)| expected == self.terms.sort(*arg))
        });

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

    /// Process a command
    pub fn process_command(&mut self, cmd: &Command) -> Result<Option<CommandResult>> {
        match cmd {
            Command::SetLogic(logic) => {
                self.logic = Some(logic.clone());
                Ok(None)
            }
            Command::DeclareConst(name, sort) => {
                self.declare_const(name, sort)?;
                Ok(None)
            }
            Command::DeclareFun(name, arg_sorts, ret_sort) => {
                self.declare_fun(name, arg_sorts, ret_sort)?;
                Ok(None)
            }
            Command::DefineFun(name, params, ret_sort, body) => {
                self.define_fun(name, params, ret_sort, body)?;
                Ok(None)
            }
            Command::DefineFunRec(name, params, ret_sort, body) => {
                // For recursive functions, register the symbol first so the body can reference it
                self.define_fun_rec(name, params, ret_sort, body)?;
                Ok(None)
            }
            Command::DefineFunsRec(declarations, bodies) => {
                // For mutually recursive functions, register all symbols first
                self.define_funs_rec(declarations, bodies)?;
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
                self.assert(term)?;
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
                self.add_soft_constraint(SoftAssertion {
                    term: term_id,
                    weight: *weight,
                    id: group.clone(),
                });
                Ok(None)
            }
            Command::Maximize(term) => {
                let id = self.elaborate_term(term, &HashMap::default())?;
                self.objectives.push(Objective {
                    direction: ObjectiveDirection::Maximize,
                    term: id,
                });
                Ok(None)
            }
            Command::Minimize(term) => {
                let id = self.elaborate_term(term, &HashMap::default())?;
                self.objectives.push(Objective {
                    direction: ObjectiveDirection::Minimize,
                    term: id,
                });
                Ok(None)
            }
            Command::Push(n) => {
                for _ in 0..*n {
                    self.push();
                }
                Ok(None)
            }
            Command::Pop(n) => {
                for _ in 0..*n {
                    if !self.pop() {
                        return Err(ElaborateError::ScopeUnderflow);
                    }
                }
                Ok(None)
            }
            Command::CheckSat => Ok(Some(CommandResult::CheckSat)),
            Command::CheckSatAssuming(terms) => {
                // Elaborate each assumption term to get its TermId
                let term_ids: Vec<TermId> = terms
                    .iter()
                    .map(|t| self.elaborate_term(t, &HashMap::default()))
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
                        self.elaborate_term(t, &HashMap::default())
                            .map(|id| (text.clone(), id))
                    })
                    .collect::<Result<Vec<_>>>()?;
                Ok(Some(CommandResult::GetValue(pairs)))
            }
            Command::Eval(term) => {
                // (eval t) is Z3 shorthand for get-value of one term: elaborate
                // the term and let the executor print just its model value.
                let term_id = self.elaborate_term(term, &HashMap::default())?;
                Ok(Some(CommandResult::Eval(term_id)))
            }
            Command::GetConsequences(assumptions, variables) => {
                let assumption_ids: Vec<TermId> = assumptions
                    .iter()
                    .map(|t| self.elaborate_term(t, &HashMap::default()))
                    .collect::<Result<Vec<_>>>()?;
                let variable_ids: Vec<TermId> = variables
                    .iter()
                    .map(|t| self.elaborate_term(t, &HashMap::default()))
                    .collect::<Result<Vec<_>>>()?;
                Ok(Some(CommandResult::GetConsequences(
                    assumption_ids,
                    variable_ids,
                )))
            }
            Command::GetAbduct(name, goal) => {
                let goal_id = self.elaborate_term(goal, &HashMap::default())?;
                Ok(Some(CommandResult::GetAbduct(name.clone(), goal_id)))
            }
            Command::GetInfo(keyword) => Ok(Some(CommandResult::GetInfo(keyword.clone()))),
            Command::GetOption(keyword) => Ok(Some(CommandResult::GetOption(keyword.clone()))),
            Command::GetAssertions => Ok(Some(CommandResult::GetAssertions)),
            Command::SetOption(keyword, value) => {
                self.set_option(keyword, value);
                Ok(None)
            }
            Command::Exit => Ok(Some(CommandResult::Exit)),
            Command::Reset => {
                // Preserve the host-configured parsed-assertion retention
                // policy across `(reset)` — it reflects the session's proof
                // configuration (e.g. `--no-proof`), not per-script state.
                let retain_parsed = self.retain_parsed_assertions;
                *self = Self::new();
                self.retain_parsed_assertions = retain_parsed;
                Ok(None)
            }
            Command::ResetAssertions => {
                self.assertions.clear();
                self.assertions_parsed.clear();
                self.objectives.clear();
                self.soft_constraints.clear();
                self.scopes.clear();
                // #quantprod-g3: an adopted definitional macro is justified
                // ONLY by its (now removed) assertion — un-adopt it, or later
                // asserts would keep expanding an unconstrained `f`. Plain
                // `define-fun` macros persist as before.
                for name in self.adopted_macro_interps.keys() {
                    self.fun_defs.remove(name.as_str());
                }
                self.adopted_macro_interps.clear();
                Ok(None)
            }
            // Declare/define sort are stored but don't produce output
            Command::DeclareSort(name, _arity) => {
                // `RoundingMode` and Float16/32/64/128 are builtin FP sorts.
                // In particular, RM literals (`RNE` … `roundTowardZero`)
                // elaborate to `Sort::Uninterpreted("RoundingMode")`, and the
                // executor's finite-domain pass keys on that sort name. A user
                // redeclaration would either conflate that fixed domain or be
                // silently ignored by the abbreviation matcher; z3 rejects all
                // of them as already defined. (#P0.2 symbolic RoundingMode)
                if is_builtin_fp_simple_sort(name) {
                    return Err(ElaborateError::ReservedSymbol(name.clone()));
                }
                // Store as uninterpreted sort
                self.sort_defs
                    .insert(name.clone(), Sort::Uninterpreted(name.clone()));
                self.track_scoped_sort_def(name.clone());
                Ok(None)
            }
            Command::DefineSort(name, params, sort) => {
                if is_builtin_fp_simple_sort(name) {
                    return Err(ElaborateError::ReservedSymbol(name.clone()));
                }
                if params.is_empty() {
                    // Monomorphic synonym: eagerly elaborate and store the sort.
                    let elaborated = self.elaborate_sort(sort)?;
                    self.sort_defs.insert(name.clone(), elaborated);
                } else {
                    // Parameterized synonym: keep the body as a template so each
                    // ground use `(Name A1 .. An)` substitutes the type parameters
                    // and elaborates the body. Storing an eagerly-elaborated body
                    // would bind the parameters to `Uninterpreted("T")`. (z3 parity)
                    self.parametric_sort_defs
                        .insert(name.clone(), (params.clone(), sort.clone()));
                }
                self.track_scoped_sort_def(name.clone());
                Ok(None)
            }
            Command::DeclareDatatype(name, datatype_dec) => {
                if is_builtin_fp_simple_sort(name) {
                    return Err(ElaborateError::ReservedSymbol(name.clone()));
                }
                self.declare_datatype(name, datatype_dec)?;
                Ok(None)
            }
            Command::DeclareDatatypes(sort_decs, datatype_decs) => {
                if let Some(sort_dec) = sort_decs
                    .iter()
                    .find(|sort_dec| is_builtin_fp_simple_sort(&sort_dec.name))
                {
                    return Err(ElaborateError::ReservedSymbol(sort_dec.name.clone()));
                }
                self.declare_datatypes(sort_decs, datatype_decs)?;
                Ok(None)
            }
            // SetInfo is acknowledged but not required to produce output
            Command::SetInfo(_, _) => Ok(None),
            // Echo returns the message to be printed (handled by executor)
            Command::Echo(msg) => Ok(Some(CommandResult::Echo(msg.clone()))),
            Command::GetAssignment => Ok(Some(CommandResult::GetAssignment)),
            Command::GetUnsatCore => Ok(Some(CommandResult::GetUnsatCore)),
            Command::GetUnsatCoreWithFarkas => Ok(Some(CommandResult::GetUnsatCoreWithFarkas)),
            Command::GetUnsatAssumptions => Ok(Some(CommandResult::GetUnsatAssumptions)),
            Command::GetProof => Ok(Some(CommandResult::GetProof)),
            Command::Simplify(term) => {
                let term_id = self.elaborate_term(term, &HashMap::default())?;
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
}

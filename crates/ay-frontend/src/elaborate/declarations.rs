// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::command::{self, Term as ParsedTerm};
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{Sort, Symbol, TermId};

use super::{is_reserved_symbol, Context, ElaborateError, Result, SymbolInfo};

/// How an incoming command introduces a name, for z3-parity redefinition
/// collision detection ([`Context::redefinition_error`]). z3 treats plain
/// macros (`define-fun`), recursive functions (`define-fun-rec` /
/// `define-funs-rec`), and uninterpreted declarations (`declare-const` /
/// `declare-fun`) with different collision/overload rules. (#P0.3)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IntroKind {
    /// `declare-const` / `declare-fun` — an uninterpreted declaration.
    Declare,
    /// `define-fun` — a plain macro (named expression).
    Macro,
    /// `define-fun-rec` / `define-funs-rec` — a recursive function.
    Recursive,
}

impl Context {
    fn reject_redefinition(
        &self,
        kind: IntroKind,
        name: &str,
        arg_sorts: &[command::Sort],
        ret_sort: &command::Sort,
    ) -> Result<()> {
        if let Some(message) = self.redefinition_error(kind, name, arg_sorts, ret_sort) {
            return Err(ElaborateError::Redefinition(message));
        }
        Ok(())
    }

    fn reject_unrepresentable_overload(&self, kind: IntroKind, name: &str) -> Result<()> {
        // Ordinary declarations have opaque per-signature identities and can
        // coexist. Definitions remain name-keyed in `fun_defs`: any accepted
        // overload on either side would make application expansion select one
        // body solely by spelling and conflate the other signature.
        let conflicts = match kind {
            IntroKind::Declare => self.fun_defs.contains_key(name),
            IntroKind::Macro | IntroKind::Recursive => self.has_symbol_binding(name),
        };
        if conflicts {
            return Err(ElaborateError::UnrepresentableOverload(name.to_string()));
        }
        Ok(())
    }

    fn validate_defined_function_body(
        &mut self,
        params: &[(String, Sort)],
        result_sort: &Sort,
        body: &ParsedTerm,
    ) -> Result<()> {
        let mut env = HashMap::default();
        for (name, sort) in params {
            env.insert(name.clone(), self.terms.mk_var(name, sort.clone()));
        }
        let body_term = self.elaborate_term(body, &env)?;
        let actual = self.terms.sort(body_term);
        if actual == result_sort || (actual == &Sort::Int && result_sort == &Sort::Real) {
            return Ok(());
        }
        Err(ElaborateError::SortMismatch {
            expected: result_sort.to_string(),
            actual: actual.to_string(),
        })
    }

    /// Declare a constant
    pub(crate) fn declare_const(&mut self, name: &str, sort: &command::Sort) -> Result<()> {
        self.reject_redefinition(IntroKind::Declare, name, &[], sort)?;
        if is_reserved_symbol(name) {
            return Err(ElaborateError::ReservedSymbol(name.to_string()));
        }
        // #reserved-ops dynamic gate: a datatype member name would be
        // conflated with the builtin constructor/selector/tester operation.
        if self.is_datatype_member_name(name) {
            return Err(ElaborateError::DatatypeMemberCollision(name.to_string()));
        }
        self.reject_unrepresentable_overload(IntroKind::Declare, name)?;
        let sort = self.elaborate_sort(sort)?;
        let internal_name = self.ordinary_declaration_internal_name(name);
        let term_name = internal_name.as_deref().unwrap_or(name);
        let term = self.mk_declared_const_term(term_name, &sort);
        self.register_overloadable_symbol(
            name.to_string(),
            SymbolInfo {
                term: Some(term),
                sort,
                arg_sorts: vec![],
                internal_name,
            },
        );
        // A USER declaration always wins over a colliding solver-internal
        // registration: it must never be model-suppressed
        // (#mv-internal-symbol-suppression).
        self.internal_symbols.remove(name);
        Ok(())
    }

    /// Build the elaborated term to bind to a freshly declared constant `name`
    /// of `sort`, performing eager datatype elimination for non-recursive
    /// single-constructor datatypes.
    ///
    /// A single-constructor datatype `D = C(f_0: T_0, ..., f_{n-1}: T_{n-1})` is
    /// isomorphic to the tuple `(T_0, ..., T_{n-1})`: every value of `D` is
    /// `C(x_0, ..., x_{n-1})` for unique field values. So binding the constant to
    /// `C(v!f_0, ..., v!f_{n-1})` over fresh field constants — rather than an
    /// opaque variable — is BOTH sound and complete. The payoff is decidability
    /// without invoking a datatype decision procedure:
    ///   * `sel_i(v)` becomes `sel_i(C(...))`, folded to `v!f_i` by the
    ///     selector-over-constructor reduction in `elaborate_app`;
    ///   * `v = w` becomes `C(...) = C(...)`, decomposed by constructor
    ///     injectivity into field equalities.
    ///
    /// Both then discharge using only the underlying scalar/UF theories. This is
    /// the standard datatype-elimination preprocessing for finite, non-recursive
    /// product types (closure environments, structs, tuples) and is what makes
    /// BMC closure-environment goals — selectors over havoc'd single-constructor
    /// variables — DECIDABLE rather than `unknown`.
    ///
    /// Multi-constructor, recursive, or zero-field datatypes fall back to an
    /// opaque fresh variable (the prior behaviour); this is always sound, only
    /// potentially incomplete, exactly as before.
    pub(super) fn mk_declared_const_term(&mut self, name: &str, sort: &Sort) -> TermId {
        let mut visiting: Vec<String> = Vec::new();
        self.build_const_term(name, sort, &mut visiting)
    }

    /// Recursive worker for [`mk_declared_const_term`]. Builds (and, for the
    /// fresh field constants it introduces, registers) the term for a constant
    /// `name` of `sort`. The caller registers the top-level `name` symbol; this
    /// registers only the introduced field symbols so they are solvable and
    /// appear in models. `visiting` holds the datatype names currently being
    /// expanded, guarding against (mutually) recursive single-constructor types.
    fn build_const_term(&mut self, name: &str, sort: &Sort, visiting: &mut Vec<String>) -> TermId {
        if let Sort::Uninterpreted(dt_name) = sort {
            if !visiting.iter().any(|v| v == dt_name) {
                // Only single-constructor datatypes are product types we can
                // eliminate. `ctor_selector_info` gives the field (selector, sort)
                // list in positional order.
                let single_ctor = self.datatypes.get(dt_name).and_then(|ctors| {
                    if ctors.len() == 1 {
                        Some(ctors[0].clone())
                    } else {
                        None
                    }
                });
                if let Some(ctor_name) = single_ctor {
                    // Resolve the field sorts for THIS specific datatype instance.
                    // The by-name `ctor_selector_info` map keeps only the
                    // last-registered instance, so for a constructor shared across
                    // parametric instantiations (e.g. `mk` of `(Pair Int Int)` and
                    // `(Pair Int Bool)`) it would eliminate the constant with the
                    // wrong instance's field sorts — corrupting selector sorts
                    // (wrong-UNSAT) and instance identity (wrong-SAT). (#param-dt)
                    if let Some(field_info) = self.constructor_selector_info_in(dt_name, &ctor_name)
                    {
                        if field_info.is_empty() {
                            // Zero-field single constructor (e.g. `Unit`): the
                            // datatype has EXACTLY ONE inhabitant, so bind the
                            // const directly to that nullary constructor term
                            // (stored as a Var, #1745) rather than leaving it a
                            // free datatype variable. A free zero-field DT var
                            // otherwise drives the exhaustiveness/constructor axiom
                            // passes, which — alongside an eliminated multi-field
                            // datatype — push the combined solver to `unknown` on
                            // otherwise-SAT problems. Sound + complete: every value
                            // of the sort IS that constructor.
                            if let Some(term) =
                                self.symbols.get(&ctor_name).and_then(|info| info.term)
                            {
                                return term;
                            }
                        } else {
                            visiting.push(dt_name.clone());
                            let mut field_terms = Vec::with_capacity(field_info.len());
                            for (sel_name, field_sort) in &field_info {
                                let field_name = format!("{name}!{sel_name}");
                                let field_term =
                                    self.build_const_term(&field_name, field_sort, visiting);
                                // Register the field so it is collected as a
                                // solvable variable and resolvable in get-value.
                                self.track_scoped_symbol(&field_name);
                                self.symbols.insert(
                                    field_name.clone(),
                                    SymbolInfo {
                                        term: Some(field_term),
                                        sort: field_sort.clone(),
                                        arg_sorts: vec![],
                                        internal_name: None,
                                    },
                                );
                                // Solver-internal, NOT user-declared: `(get-model)`
                                // must not print it (#mv-internal-symbol-suppression).
                                self.internal_symbols.insert(field_name.clone());
                                field_terms.push(field_term);
                            }
                            visiting.pop();
                            return self.terms.mk_app(
                                Symbol::named(&ctor_name),
                                field_terms,
                                sort.clone(),
                            );
                        }
                    }
                }
            }
        }
        // Default: opaque fresh variable (unchanged behaviour).
        self.terms.mk_fresh_named_var(name, sort.clone())
    }

    /// Declare a function
    pub(crate) fn declare_fun(
        &mut self,
        name: &str,
        arg_sorts: &[command::Sort],
        ret_sort: &command::Sort,
    ) -> Result<()> {
        self.reject_redefinition(IntroKind::Declare, name, arg_sorts, ret_sort)?;
        // Declaration-activated collection predicates (`set.subset`,
        // `map.dom`, `map.subset`, `multiset.subset`) are the SOLE exception
        // to the reserved-name gate, and only HERE (declare-fun) and only at
        // their native collection signature: that declaration is the
        // documented activation route for the native set/map/multiset solvers
        // (deductive-checks's encoder declares exactly these via the programmatic
        // `try_declare_fun` API, which funnels through this method). Any other
        // signature is rejected fail-closed below — before the signature gate,
        // `(declare-fun set.subset (Int Int) Bool)` + `(not (set.subset 0 0))`
        // reached the native subset rule and answered a definitive `unsat` via
        // ground-identity reflexivity on a forged symbol.
        let declaration_activated = super::is_declaration_activated_op_name(name);
        if !declaration_activated && is_reserved_symbol(name) {
            return Err(ElaborateError::ReservedSymbol(name.to_string()));
        }
        // #reserved-ops dynamic gate: a datatype member name would be
        // conflated with the builtin constructor/selector/tester operation
        // (confirmed wrong-UNSAT class: post-hoc `declare-fun is-Cons`/`hd`).
        // The programmatic ay-dpll API pre-empts this error for an
        // IDENTICAL-signature redeclaration by adopting the registered member
        // instead (see `Solver::try_declare_fun`); the SMT-LIB text path
        // always rejects.
        if self.is_datatype_member_name(name) {
            return Err(ElaborateError::DatatypeMemberCollision(name.to_string()));
        }
        self.reject_unrepresentable_overload(IntroKind::Declare, name)?;
        let mut elaborated_arg_sorts: Vec<Sort> = Vec::with_capacity(arg_sorts.len());
        for s in arg_sorts {
            elaborated_arg_sorts.push(self.elaborate_sort(s)?);
        }
        let arg_sorts = elaborated_arg_sorts;
        let ret_sort = self.elaborate_sort(ret_sort)?;
        if declaration_activated
            && !super::declaration_activated_signature_ok(name, &arg_sorts, &ret_sort)
        {
            return Err(ElaborateError::Unsupported(format!(
                "'{name}' is a declaration-activated builtin collection predicate; it may only \
                 be declared at its native collection signature ((Array ...) (Array ...) -> Bool \
                 for the subset predicates, (Array ...) -> (Array ...) for map.dom), got \
                 ({arg_sorts:?}) -> {ret_sort:?}"
            )));
        }

        let internal_name = self.ordinary_declaration_internal_name(name);

        // If no arguments, it's a constant — apply the same eager single-
        // constructor datatype elimination as declare-const.
        let term = if arg_sorts.is_empty() {
            Some(self.mk_declared_const_term(internal_name.as_deref().unwrap_or(name), &ret_sort))
        } else {
            None
        };

        // Commit the sticky shadow marker only after every fallible sort and
        // signature check succeeds. A rejected declaration must not disable
        // builtin `to_real` reasoning for the rest of the session.
        if name == "to_real" {
            self.terms.mark_to_real_shadowed();
        }

        self.register_overloadable_symbol(
            name.to_string(),
            SymbolInfo {
                term,
                sort: ret_sort,
                arg_sorts,
                internal_name,
            },
        );
        // A USER declaration always wins over a colliding solver-internal
        // registration (#mv-internal-symbol-suppression).
        self.internal_symbols.remove(name);
        Ok(())
    }

    /// z3 4.15.4 redefinition collision, exact error text or `None` when the
    /// command is legally accepted (fresh name, or an overload z3 permits).
    ///
    /// `new_kind` is how the INCOMING command introduces `name`; the existing
    /// binding's kind is read from context. z3's accept/reject matrix (all
    /// measured against 4.15.4) unifies to two rules:
    ///
    /// 1. **Suppression:** a `declare-*` and a `define-fun-rec`/`define-funs-rec`
    ///    on opposite sides never collide (recfun lives in z3's `recfun` plugin
    ///    namespace) — so `(declare-const g Int)(define-fun-rec g () Int 1)` and
    ///    its reverse are both accepted.
    /// 2. **Match rule:** otherwise they collide when the argument DOMAINS match;
    ///    the result sort is part of the key EXCEPT when the existing binding is
    ///    a plain `define-fun` macro (a named expression keyed by name+domain
    ///    only), where the result sort is ignored.
    ///
    /// The message wording (four distinct z3 forms) is selected from the
    /// `(new_kind, old_kind)` pair. The returned string is the message BODY
    /// (no `line/column` prefix — the CLI adds position). (#P0.3)
    pub fn redefinition_error(
        &self,
        new_kind: IntroKind,
        name: &str,
        arg_sorts: &[command::Sort],
        ret_sort: &command::Sort,
    ) -> Option<String> {
        // Fast path: only a redeclaration of an already-known name can collide.
        if !self.symbols.contains_key(name) && !self.overloaded_symbols.contains_key(name) {
            return None;
        }
        // Names with dedicated gates keep their specific errors — don't pre-empt.
        if is_reserved_symbol(name)
            || self.is_datatype_member_name(name)
            || super::is_declaration_activated_op_name(name)
        {
            return None;
        }

        // Classify the EXISTING binding. `recursive_fun_names` ⊆ `fun_defs`.
        let old_kind = if self.recursive_fun_names.contains(name) {
            IntroKind::Recursive
        } else if self.fun_defs.contains_key(name) {
            IntroKind::Macro
        } else {
            IntroKind::Declare
        };

        // Rule 1 — recfun/declare cross pairs never collide (either order).
        let cross_recfun_declare = |a: IntroKind, b: IntroKind| {
            matches!(a, IntroKind::Recursive) && matches!(b, IntroKind::Declare)
        };
        if cross_recfun_declare(new_kind, old_kind) || cross_recfun_declare(old_kind, new_kind) {
            return None;
        }

        // Redefinition probing is observational: lazy sort/datatype expansion
        // must not mutate the live context before the command is accepted.
        let mut probe = self.datatype_sort_preflight_context();
        let mut elaborated_arg_sorts: Vec<Sort> = Vec::with_capacity(arg_sorts.len());
        for s in arg_sorts {
            elaborated_arg_sorts.push(probe.elaborate_sort(s).ok()?);
        }
        let elaborated_ret_sort = probe.elaborate_sort(ret_sort).ok()?;

        // Rule 2 — match rule. A plain macro on the existing side ignores the
        // result sort; everything else keys on the full signature.
        let collides = if matches!(old_kind, IntroKind::Macro) {
            self.has_symbol_with_domain(name, &elaborated_arg_sorts)
        } else {
            self.has_symbol_with_signature(name, &elaborated_arg_sorts, &elaborated_ret_sort)
        };
        if !collides {
            return None;
        }

        Some(match (new_kind, old_kind) {
            (IntroKind::Macro, IntroKind::Macro) => "named expression already defined".to_string(),
            (IntroKind::Macro, _) => format!(
                "invalid named expression, declaration already defined with this name {name}"
            ),
            (_, IntroKind::Macro) => format!(
                "invalid declaration, named expression already defined with this name {name}"
            ),
            (_, _) => {
                let kind = if arg_sorts.is_empty() {
                    "constant"
                } else {
                    "function"
                };
                format!(
                    "invalid declaration, {kind} '{name}' (with the given signature) already declared"
                )
            }
        })
    }

    /// Define a function
    pub(crate) fn define_fun(
        &mut self,
        name: &str,
        params: &[(String, command::Sort)],
        ret_sort: &command::Sort,
        body: &ParsedTerm,
    ) -> Result<()> {
        let parsed_arg_sorts: Vec<_> = params.iter().map(|(_, sort)| sort.clone()).collect();
        self.reject_redefinition(IntroKind::Macro, name, &parsed_arg_sorts, ret_sort)?;
        if is_reserved_symbol(name) {
            return Err(ElaborateError::ReservedSymbol(name.to_string()));
        }
        // #reserved-ops dynamic gate (see `declare_fun`).
        if self.is_datatype_member_name(name) {
            return Err(ElaborateError::DatatypeMemberCollision(name.to_string()));
        }
        self.reject_unrepresentable_overload(IntroKind::Macro, name)?;
        let mut params_vec: Vec<(String, Sort)> = Vec::with_capacity(params.len());
        for (n, s) in params {
            params_vec.push((n.clone(), self.elaborate_sort(s)?));
        }
        let params = params_vec;
        let ret_sort = self.elaborate_sort(ret_sort)?;

        self.validate_defined_function_body(&params, &ret_sort, body)?;

        // Store the definition for expansion
        self.fun_defs.insert(
            name.to_string(),
            (params.clone(), ret_sort.clone(), body.clone()),
        );

        // Also add to symbol table
        let arg_sorts: Vec<Sort> = params.iter().map(|(_, s)| s.clone()).collect();
        self.track_scoped_symbol(name);
        self.symbols.insert(
            name.to_string(),
            SymbolInfo {
                term: None,
                sort: ret_sort,
                arg_sorts,
                internal_name: None,
            },
        );
        // Track in current scope for pop() cleanup (#8621).
        self.track_scoped_fun_def(name.to_string());
        Ok(())
    }

    /// Define a recursive function
    ///
    /// For recursive functions, the function can reference itself in its body.
    /// We add to the symbol table first to enable self-reference during expansion.
    pub(crate) fn define_fun_rec(
        &mut self,
        name: &str,
        params: &[(String, command::Sort)],
        ret_sort: &command::Sort,
        body: &ParsedTerm,
    ) -> Result<()> {
        let parsed_arg_sorts: Vec<_> = params.iter().map(|(_, sort)| sort.clone()).collect();
        self.reject_redefinition(IntroKind::Recursive, name, &parsed_arg_sorts, ret_sort)?;
        if is_reserved_symbol(name) {
            return Err(ElaborateError::ReservedSymbol(name.to_string()));
        }
        // #reserved-ops dynamic gate (see `declare_fun`).
        if self.is_datatype_member_name(name) {
            return Err(ElaborateError::DatatypeMemberCollision(name.to_string()));
        }
        self.reject_unrepresentable_overload(IntroKind::Recursive, name)?;
        let mut params_vec: Vec<(String, Sort)> = Vec::with_capacity(params.len());
        for (n, s) in params {
            params_vec.push((n.clone(), self.elaborate_sort(s)?));
        }
        let params = params_vec;
        let ret_sort = self.elaborate_sort(ret_sort)?;

        // For recursive functions, add to symbol table first so body can reference the function
        let arg_sorts: Vec<Sort> = params.iter().map(|(_, s)| s.clone()).collect();
        let scope_symbols_before = self.scopes.last().map(|frame| frame.symbols.clone());
        self.track_scoped_symbol(name);
        let previous_symbol = self.symbols.insert(
            name.to_string(),
            SymbolInfo {
                term: None,
                sort: ret_sort.clone(),
                arg_sorts,
                internal_name: None,
            },
        );

        if let Err(error) = self.validate_defined_function_body(&params, &ret_sort, body) {
            if let Some(previous) = previous_symbol {
                self.symbols.insert(name.to_string(), previous);
            } else {
                self.symbols.remove(name);
            }
            if let (Some(frame), Some(symbols)) = (self.scopes.last_mut(), scope_symbols_before) {
                frame.symbols = symbols;
            }
            return Err(error);
        }

        // Store the definition for expansion
        self.fun_defs
            .insert(name.to_string(), (params, ret_sort, body.clone()));
        // Mark as a recursive-function declaration (distinct from a plain macro)
        // for z3-parity redefinition collision (#P0.3).
        self.recursive_fun_names.insert(name.to_string());

        // Track in current scope for pop() cleanup (#8621).
        self.track_scoped_fun_def(name.to_string());

        Ok(())
    }

    /// Define mutually recursive functions
    ///
    /// For mutually recursive functions, all function signatures are registered
    /// first so the bodies can reference each other.
    pub(crate) fn define_funs_rec(
        &mut self,
        declarations: &[command::FuncDeclaration],
        bodies: &[ParsedTerm],
    ) -> Result<()> {
        if declarations.len() != bodies.len() {
            return Err(ElaborateError::InvalidConstant(format!(
                "define-funs-rec has {} declarations but {} bodies",
                declarations.len(),
                bodies.len()
            )));
        }

        // Validate all function names first
        let mut names = HashSet::default();
        for (name, _params, _ret_sort) in declarations {
            if !names.insert(name.clone()) {
                return Err(ElaborateError::InvalidConstant(format!(
                    "define-funs-rec contains duplicate function name '{name}'"
                )));
            }
            if is_reserved_symbol(name) {
                return Err(ElaborateError::ReservedSymbol(name.clone()));
            }
            // #reserved-ops dynamic gate (see `declare_fun`).
            if self.is_datatype_member_name(name) {
                return Err(ElaborateError::DatatypeMemberCollision(name.clone()));
            }
        }

        // Enforce the same collision rules for every caller of Context, not
        // just the CLI wrapper. Probe the whole batch before registering any
        // mutually recursive signature.
        for (name, params, ret_sort) in declarations {
            let parsed_arg_sorts: Vec<_> = params.iter().map(|(_, sort)| sort.clone()).collect();
            self.reject_redefinition(IntroKind::Recursive, name, &parsed_arg_sorts, ret_sort)?;
            self.reject_unrepresentable_overload(IntroKind::Recursive, name)?;
        }

        // Elaborated declarations with internal Sort type
        type ElaboratedDecl = (String, Vec<(String, Sort)>, Sort);

        // Prove every sort can elaborate before the live symbol table changes.
        // The narrow probe absorbs lazy parametric-sort/datatype instantiation,
        // so a bad later declaration cannot leave earlier signatures behind.
        let mut preflight = self.datatype_sort_preflight_context();
        for (_name, params, ret_sort) in declarations {
            for (_param_name, sort) in params {
                preflight.elaborate_sort(sort)?;
            }
            preflight.elaborate_sort(ret_sort)?;
        }

        // Elaborate all live signatures before registering the first one. The
        // preflight above makes this deterministic/fallible phase atomic.
        let mut elaborated_decls: Vec<ElaboratedDecl> = Vec::new();
        for (name, params, ret_sort) in declarations {
            let mut params_vec: Vec<(String, Sort)> = Vec::with_capacity(params.len());
            for (n, s) in params {
                params_vec.push((n.clone(), self.elaborate_sort(s)?));
            }
            let params = params_vec;
            let ret_sort = self.elaborate_sort(ret_sort)?;

            elaborated_decls.push((name.clone(), params, ret_sort));
        }

        // First commit phase: register all signatures so mutually recursive
        // bodies resolve every peer. Preserve the exact state needed to undo a
        // later body-validation error, including the current scope's lazy
        // symbol snapshots.
        let scope_symbols_before = self.scopes.last().map(|frame| frame.symbols.clone());
        let mut previous_symbols: Vec<(String, Option<SymbolInfo>)> = Vec::new();
        for (name, params, ret_sort) in &elaborated_decls {
            let arg_sorts: Vec<Sort> = params.iter().map(|(_, sort)| sort.clone()).collect();
            self.track_scoped_symbol(name);
            let previous = self.symbols.insert(
                name.clone(),
                SymbolInfo {
                    term: None,
                    sort: ret_sort.clone(),
                    arg_sorts,
                    internal_name: None,
                },
            );
            previous_symbols.push((name.clone(), previous));
        }

        let validation = elaborated_decls.iter().zip(bodies.iter()).try_for_each(
            |((_name, params, ret_sort), body)| {
                self.validate_defined_function_body(params, ret_sort, body)
            },
        );
        if let Err(error) = validation {
            for (name, previous) in previous_symbols.into_iter().rev() {
                if let Some(previous) = previous {
                    self.symbols.insert(name, previous);
                } else {
                    self.symbols.remove(&name);
                }
            }
            if let (Some(frame), Some(symbols)) = (self.scopes.last_mut(), scope_symbols_before) {
                frame.symbols = symbols;
            }
            return Err(error);
        }

        // Second pass: store all function definitions
        for ((name, params, ret_sort), body) in elaborated_decls.into_iter().zip(bodies.iter()) {
            self.fun_defs
                .insert(name.clone(), (params, ret_sort, body.clone()));
            // Mark as recursive-function declarations for z3-parity redefinition
            // collision (#P0.3).
            self.recursive_fun_names.insert(name.clone());
            // Track in current scope for pop() cleanup (#8621).
            self.track_scoped_fun_def(name.clone());
        }

        Ok(())
    }
}

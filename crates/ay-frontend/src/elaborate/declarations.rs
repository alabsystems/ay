// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::command::{self, Term as ParsedTerm};
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
    /// Declare a constant
    pub(crate) fn declare_const(&mut self, name: &str, sort: &command::Sort) -> Result<()> {
        if is_reserved_symbol(name) {
            return Err(ElaborateError::ReservedSymbol(name.to_string()));
        }
        // #reserved-ops dynamic gate: a datatype member name would be
        // conflated with the builtin constructor/selector/tester operation.
        if self.is_datatype_member_name(name) {
            return Err(ElaborateError::DatatypeMemberCollision(name.to_string()));
        }
        let sort = self.elaborate_sort(sort)?;
        let term = self.mk_declared_const_term(name, &sort);
        self.symbols.insert(
            name.to_string(),
            SymbolInfo {
                term: Some(term),
                sort,
                arg_sorts: vec![],
                internal_name: None,
            },
        );
        // A USER declaration always wins over a colliding solver-internal
        // registration: it must never be model-suppressed
        // (#mv-internal-symbol-suppression).
        self.internal_symbols.remove(name);
        self.track_scoped_symbol(name.to_string());
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
                                self.track_scoped_symbol(field_name);
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
        // A user declaration of `to_real` (deliberately declarable — a valid
        // `(_ map f)` target) shadows the builtin: its applications are
        // byte-identical to the builtin's in the term store, so the
        // to_real-integrality rewrites must stand down for the rest of the
        // session (sticky, fail-closed). Covers both SMT-LIB text and the
        // programmatic `try_declare_fun` path (which funnels through this
        // method via Command::DeclareFun). (#to-real-bridge)
        if name == "to_real" {
            self.terms.mark_to_real_shadowed();
        }
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

        // If no arguments, it's a constant — apply the same eager single-
        // constructor datatype elimination as declare-const.
        let term = if arg_sorts.is_empty() {
            Some(self.mk_declared_const_term(name, &ret_sort))
        } else {
            None
        };

        self.symbols.insert(
            name.to_string(),
            SymbolInfo {
                term,
                sort: ret_sort,
                arg_sorts,
                internal_name: None,
            },
        );
        // A USER declaration always wins over a colliding solver-internal
        // registration (#mv-internal-symbol-suppression).
        self.internal_symbols.remove(name);
        self.track_scoped_symbol(name.to_string());
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
        &mut self,
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

        let mut elaborated_arg_sorts: Vec<Sort> = Vec::with_capacity(arg_sorts.len());
        for s in arg_sorts {
            elaborated_arg_sorts.push(self.elaborate_sort(s).ok()?);
        }
        let elaborated_ret_sort = self.elaborate_sort(ret_sort).ok()?;

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
        if is_reserved_symbol(name) {
            return Err(ElaborateError::ReservedSymbol(name.to_string()));
        }
        // #reserved-ops dynamic gate (see `declare_fun`).
        if self.is_datatype_member_name(name) {
            return Err(ElaborateError::DatatypeMemberCollision(name.to_string()));
        }
        let mut params_vec: Vec<(String, Sort)> = Vec::with_capacity(params.len());
        for (n, s) in params {
            params_vec.push((n.clone(), self.elaborate_sort(s)?));
        }
        let params = params_vec;
        let ret_sort = self.elaborate_sort(ret_sort)?;

        // Store the definition for expansion
        self.fun_defs
            .insert(name.to_string(), (params.clone(), body.clone()));

        // Also add to symbol table
        let arg_sorts: Vec<Sort> = params.iter().map(|(_, s)| s.clone()).collect();
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
        self.track_scoped_symbol(name.to_string());
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
        if is_reserved_symbol(name) {
            return Err(ElaborateError::ReservedSymbol(name.to_string()));
        }
        // #reserved-ops dynamic gate (see `declare_fun`).
        if self.is_datatype_member_name(name) {
            return Err(ElaborateError::DatatypeMemberCollision(name.to_string()));
        }
        let mut params_vec: Vec<(String, Sort)> = Vec::with_capacity(params.len());
        for (n, s) in params {
            params_vec.push((n.clone(), self.elaborate_sort(s)?));
        }
        let params = params_vec;
        let ret_sort = self.elaborate_sort(ret_sort)?;

        // For recursive functions, add to symbol table first so body can reference the function
        let arg_sorts: Vec<Sort> = params.iter().map(|(_, s)| s.clone()).collect();
        self.symbols.insert(
            name.to_string(),
            SymbolInfo {
                term: None,
                sort: ret_sort,
                arg_sorts,
                internal_name: None,
            },
        );

        // Store the definition for expansion
        self.fun_defs
            .insert(name.to_string(), (params, body.clone()));
        // Mark as a recursive-function declaration (distinct from a plain macro)
        // for z3-parity redefinition collision (#P0.3).
        self.recursive_fun_names.insert(name.to_string());

        // Track in current scope for pop() cleanup (#8621).
        self.track_scoped_fun_def(name.to_string());
        self.track_scoped_symbol(name.to_string());

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
        // Validate all function names first
        for (name, _params, _ret_sort) in declarations {
            if is_reserved_symbol(name) {
                return Err(ElaborateError::ReservedSymbol(name.clone()));
            }
            // #reserved-ops dynamic gate (see `declare_fun`).
            if self.is_datatype_member_name(name) {
                return Err(ElaborateError::DatatypeMemberCollision(name.clone()));
            }
        }

        // Elaborated declarations with internal Sort type
        type ElaboratedDecl = (String, Vec<(String, Sort)>, Sort);

        // First pass: register all function signatures in the symbol table
        let mut elaborated_decls: Vec<ElaboratedDecl> = Vec::new();

        for (name, params, ret_sort) in declarations {
            let mut params_vec: Vec<(String, Sort)> = Vec::with_capacity(params.len());
            for (n, s) in params {
                params_vec.push((n.clone(), self.elaborate_sort(s)?));
            }
            let params = params_vec;
            let ret_sort = self.elaborate_sort(ret_sort)?;

            let arg_sorts: Vec<Sort> = params.iter().map(|(_, s)| s.clone()).collect();
            self.symbols.insert(
                name.clone(),
                SymbolInfo {
                    term: None,
                    sort: ret_sort.clone(),
                    arg_sorts,
                    internal_name: None,
                },
            );

            elaborated_decls.push((name.clone(), params, ret_sort));
        }

        // Second pass: store all function definitions
        for ((name, params, _ret_sort), body) in elaborated_decls.into_iter().zip(bodies.iter()) {
            self.fun_defs.insert(name.clone(), (params, body.clone()));
            // Mark as recursive-function declarations for z3-parity redefinition
            // collision (#P0.3).
            self.recursive_fun_names.insert(name.clone());
            // Track in current scope for pop() cleanup (#8621).
            self.track_scoped_fun_def(name.clone());
            self.track_scoped_symbol(name);
        }

        Ok(())
    }
}

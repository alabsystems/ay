// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Term introspection for the AY Solver API.
//!
//! Provides methods to decompose terms back into their operator and arguments.
//! Used by the Z3-compatible FFI layer for `Z3_get_app_num_args`, etc.

use ay_core::term::{Symbol, TermData};
use ay_core::Sort;

use super::types::Term;
use super::{Solver, SolverError};

mod fallible;

/// Describes the kind of a term node.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum TermKind {
    /// Function application (named or indexed operator)
    App {
        /// Operator name (e.g. "+", "and", "f")
        name: String,
        /// Number of arguments
        num_args: usize,
    },
    /// Variable reference
    Var {
        /// Variable name
        name: String,
    },
    /// Constant value (numeral, boolean, bitvector literal)
    Const,
    /// Negation (single child)
    Not,
    /// If-then-else (3 children: cond, then, else)
    Ite,
    /// Universal quantifier
    Forall,
    /// Existential quantifier
    Exists,
    /// Let binding
    Let,
}

impl Solver {
    /// Format a term as SMT-LIB text using this solver's term store.
    ///
    /// Use `Term::to_string` or `std::fmt::Display` on `Term` for a stable
    /// opaque handle. Use this method when you need the term's reconstructed
    /// expression, including variables, constants, applications, lets, and
    /// quantifiers.
    /// Bounded field-numeral rendering refusal returns an SMT-LIB error response.
    ///
    /// # Panics
    ///
    /// Panics if `term` was not created by this solver or is otherwise stale.
    #[must_use]
    pub fn format_term(&self, term: Term) -> String {
        let id = self.require_term("format_term", term);
        if self.executor.terms().finite_field_presence(id) == Some(false) {
            self.executor.format_term(id)
        } else {
            self.executor
                .checked_evaluation_output(|| self.executor.format_term(id))
        }
    }

    /// Format a term as SMT-LIB text, or `None` if `term` does not index a
    /// live node in this solver's term store or bounded rendering refuses.
    ///
    /// Unlike [`format_term`](Self::format_term), which panics on a stale or
    /// foreign handle, this bounds-checks the handle first and returns `None`
    /// instead of panicking. Used by the Z3-compatible FFI
    /// (`Z3_ast_to_string`), where a foreign/stale `Z3_ast` must yield a null
    /// string rather than unwind a panic across the C boundary.
    #[must_use]
    pub fn format_term_checked(&self, term: Term) -> Option<String> {
        self.format_term_checked_with_bindings(term, |_| false)
    }

    /// Format a term while avoiding both native bindings and the caller's
    /// additional public declaration namespace when spelling field numerals.
    /// Foreign/stale handles and bounded rendering refusal return `None`.
    pub fn format_term_checked_with_bindings(
        &self,
        term: Term,
        mut occupied: impl FnMut(&str) -> bool,
    ) -> Option<String> {
        let id = self.resolve_term("format_term_checked", term).ok()?;
        let needs_check = self.executor.terms().finite_field_presence(id) != Some(false);
        if needs_check {
            self.executor.check_evaluation_read().ok()?;
        }
        let text = self.executor.format_term_in_namespace(id, &mut occupied);
        if needs_check {
            self.executor.check_evaluation_read().ok()?;
        }
        Some(text)
    }

    /// Serialize the current assertion stack as a self-contained SMT-LIB2
    /// script (declarations + named assertions + `(check-sat)`). Parse the
    /// result into a fresh [`Solver`] and call [`Solver::check_sat`] to
    /// reproduce a batch (non-incremental) solve of the identical query.
    /// (#transpose)
    #[must_use]
    pub fn to_smtlib2(&self) -> String {
        self.executor.to_smtlib2()
    }

    /// Surface names of the declared symbols (constants and function heads)
    /// that occur in the DAGs under `roots`, as `get-model` prints them.
    ///
    /// A model printed by this solver lists every symbol declared on it. The
    /// Z3 C API runs several logical solvers over one engine, so it restricts
    /// each handle's published model to the symbols of that handle's goal with
    /// this set. Matching covers both the surface name and the internal
    /// identity of an overloaded or builtin-colliding declaration. Only FREE
    /// occurrences count: a variable bound by an enclosing quantifier, `let`
    /// or lambda (`lambda-array`) is not a symbol of the goal, even when the API built it from a
    /// declared constant of the same name (the Z3 C API's `Z3_mk_forall_const`
    /// binds named constants), so `exists q0. q0 < 0` does not list `q0`.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError`](super::types::SolverError) if a root is not a
    /// live term of this solver.
    pub fn declared_symbols_in(
        &self,
        roots: &[Term],
    ) -> Result<std::collections::BTreeSet<String>, super::types::SolverError> {
        let terms = self.terms();
        // Binder scopes: (enclosing scope, names bound here). Scope 0 is the
        // top level; a binder's body is walked in a fresh child scope, and a
        // term is visited once per scope it occurs in.
        let mut scopes: Vec<(usize, Vec<&str>)> = vec![(0, Vec::new())];
        fn is_bound(scopes: &[(usize, Vec<&str>)], mut scope: usize, name: &str) -> bool {
            while scope != 0 {
                let (parent, names) = &scopes[scope];
                if names.iter().any(|bound| *bound == name) {
                    return true;
                }
                scope = *parent;
            }
            false
        }
        let mut pending: Vec<(ay_core::TermId, usize)> = self
            .resolve_terms("declared_symbols_in", roots)?
            .into_iter()
            .map(|id| (id, 0))
            .collect();
        let mut seen: ay_core::kani_compat::DetHashSet<(ay_core::TermId, usize)> =
            ay_core::kani_compat::det_hash_set_new();
        let mut occurring: ay_core::kani_compat::DetHashSet<&str> =
            ay_core::kani_compat::det_hash_set_new();
        while let Some((id, scope)) = pending.pop() {
            if !seen.insert((id, scope)) {
                continue;
            }
            match terms.get(id) {
                TermData::Var(name, _) => {
                    if !is_bound(&scopes, scope, name) {
                        occurring.insert(name.as_str());
                    }
                }
                TermData::App(symbol, _) => {
                    // A lambda binds its variable (the Z3 API's
                    // `Z3_mk_lambda_const` binds the caller's own constant):
                    // the variable is not an occurrence, and the body is
                    // walked with it bound.
                    if let Some((var, body)) = terms.get_lambda_array(id) {
                        if let TermData::Var(name, _) = terms.get(var) {
                            scopes.push((scope, vec![name.as_str()]));
                            pending.push((body, scopes.len() - 1));
                            continue;
                        }
                    }
                    occurring.insert(symbol.name());
                }
                TermData::Forall(vars, body, triggers) | TermData::Exists(vars, body, triggers) => {
                    scopes.push((scope, vars.iter().map(|(name, _)| name.as_str()).collect()));
                    let inner = scopes.len() - 1;
                    pending.push((*body, inner));
                    pending.extend(triggers.iter().flatten().map(|&t| (t, inner)));
                    continue;
                }
                TermData::Let(bindings, body) => {
                    pending.extend(bindings.iter().map(|&(_, value)| (value, scope)));
                    scopes.push((
                        scope,
                        bindings.iter().map(|(name, _)| name.as_str()).collect(),
                    ));
                    pending.push((*body, scopes.len() - 1));
                    continue;
                }
                _ => {}
            }
            pending.extend(terms.children(id).into_iter().map(|child| (child, scope)));
        }
        let context = self.executor.context();
        Ok(context
            .symbol_iter()
            .filter(|(surface, info)| {
                occurring.contains(surface.as_str())
                    || occurring.contains(context.symbol_identity_name(surface, info))
            })
            .map(|(surface, _)| surface.clone())
            .collect())
    }

    /// Serialize the given assertion list in Z3's `Z3_solver_to_string` /
    /// z3py `Solver.sexpr()` shape: one `(declare-fun ...)` line per declared
    /// symbol followed by one `(assert ...)` line per assertion, with no
    /// script wrapper. This is a faithful dump of the passed assertions (never
    /// fabricated). Backs the Z3-compat `Z3_solver_to_string` FFI entry point,
    /// which holds its live assertions on the per-solver handle rather than on
    /// the executor's internal stack.
    #[must_use]
    pub fn assertions_sexpr(&self, assertions: &[Term]) -> String {
        let ids = self.require_terms("assertions_sexpr", assertions);
        self.executor.assertions_sexpr_for(&ids)
    }

    /// Serialize assertions while avoiding an adapter's additional public
    /// declaration namespace. Invalid handles or bounded rendering refusal
    /// return `None`, without publishing a partial assertion dump.
    pub fn assertions_sexpr_with_bindings(
        &self,
        assertions: &[Term],
        mut occupied: impl FnMut(&str) -> bool,
    ) -> Option<String> {
        let ids = self
            .resolve_terms("assertions_sexpr_with_bindings", assertions)
            .ok()?;
        let needs_check = ids
            .iter()
            .any(|&id| self.terms().finite_field_presence(id) != Some(false));
        if needs_check {
            self.executor.check_evaluation_read().ok()?;
        }
        let text = self
            .executor
            .assertions_sexpr_in_namespace(&ids, &mut occupied);
        if needs_check {
            self.executor.check_evaluation_read().ok()?;
        }
        Some(text)
    }

    /// Get the kind of a term, including operator info for applications.
    #[must_use]
    pub fn term_kind(&self, term: Term) -> TermKind {
        let id = self.require_term("term_kind", term);
        match self.terms().get(id) {
            TermData::App(sym, args) => {
                let name = match sym {
                    Symbol::Named(n) => n.to_string(),
                    Symbol::Indexed(n, indices) => {
                        format!(
                            "(_ {n} {})",
                            indices
                                .iter()
                                .map(ToString::to_string)
                                .collect::<Vec<_>>()
                                .join(" ")
                        )
                    }
                    // All current Symbol variants handled above (#5692).
                    other => unreachable!("unhandled Symbol variant in term_kind(): {other:?}"),
                };
                TermKind::App {
                    name,
                    num_args: args.len(),
                }
            }
            TermData::Var(name, _) => TermKind::Var { name: name.clone() },
            TermData::Const(_) => TermKind::Const,
            TermData::Not(_) => TermKind::Not,
            TermData::Ite(_, _, _) => TermKind::Ite,
            TermData::Forall(_, _, _) => TermKind::Forall,
            TermData::Exists(_, _, _) => TermKind::Exists,
            TermData::Let(_, _) => TermKind::Let,
            // All current TermData variants are handled above.
            // This arm is required by #[non_exhaustive] and catches future variants.
            other => unreachable!("unhandled TermData variant in term_kind(): {other:?}"),
        }
    }

    /// Get the children (arguments) of a term.
    ///
    /// - `App(f, [a, b])` → `[a, b]`
    /// - `Not(x)` → `[x]`
    /// - `Ite(c, t, e)` → `[c, t, e]`
    /// - `Var`, `Const` → `[]`
    #[must_use]
    pub fn term_children(&self, term: Term) -> Vec<Term> {
        let id = self.require_term("term_children", term);
        self.terms()
            .children(id)
            .into_iter()
            .map(|child| self.wrap_term(child))
            .collect()
    }

    /// Immediate public children, counted without allocating either the native
    /// ID vector or its larger public-handle conversion. Like term_children,
    /// quantifier patterns are not public application children.
    pub fn try_term_child_count(&self, term: Term) -> Result<usize, SolverError> {
        let id = self.resolve_term("term child count", term)?;
        Ok(match self.terms().get(id) {
            TermData::Const(_) | TermData::Var(..) => 0,
            TermData::App(_, arguments) => arguments.len(),
            // A Vec cannot occupy usize::MAX entries; its allocation is
            // bounded by isize::MAX, so this extra body slot cannot overflow.
            TermData::Let(bindings, _) => bindings.len() + 1,
            TermData::Not(_) | TermData::Forall(..) | TermData::Exists(..) => 1,
            TermData::Ite(..) => 3,
            _ => {
                return Err(SolverError::TacticFailed(
                    "unsupported immediate-child shape".into(),
                ))
            }
        })
    }

    /// Compare the exact ordered immediate children without materializing a
    /// copy. This observes DATA only; callers that need original admission
    /// first call try_term_child_count and prepay that work through their
    /// retained operation BEFORE calling this comparison. No owner is minted.
    pub fn try_term_children_match(
        &self,
        term: Term,
        expected: &[Term],
    ) -> Result<(usize, bool), SolverError> {
        let count = self.try_term_child_count(term)?;
        if count != expected.len() {
            return Ok((count, false));
        }
        let id = self.resolve_term("term children comparison", term)?;
        let mut position = 0;
        let mut same = true;
        let mut compare = |child| {
            same &= expected[position] == self.wrap_term(child);
            position += 1;
        };
        match self.terms().get(id) {
            TermData::Const(_) | TermData::Var(..) => {}
            TermData::App(_, arguments) => {
                for &child in arguments {
                    compare(child);
                }
            }
            TermData::Let(bindings, body) => {
                for (_, child) in bindings {
                    compare(*child);
                }
                compare(*body);
            }
            TermData::Not(child)
            | TermData::Forall(_, child, _)
            | TermData::Exists(_, child, _) => compare(*child),
            TermData::Ite(condition, yes, no) => {
                compare(*condition);
                compare(*yes);
                compare(*no);
            }
            _ => {
                return Err(SolverError::TacticFailed(
                    "unsupported immediate-child shape".into(),
                ))
            }
        }
        Ok((count, same))
    }

    /// Get the sort (type) of a term.
    ///
    /// Works for all sort kinds: Bool, Int, Real, BitVec, FloatingPoint, Array,
    /// String, Datatype, Uninterpreted, etc.
    ///
    /// # Panics
    ///
    /// Panics when `term` is not a live handle of this solver. Use
    /// [`Self::try_term_sort`] for a fallible version.
    #[must_use]
    pub fn term_sort(&self, term: Term) -> Sort {
        let id = self.require_term("term_sort", term);
        self.sort_of_live_term(id)
    }

    /// The sort of an authenticated term: the one lookup `term_sort` and
    /// `try_term_sort` share.
    fn sort_of_live_term(&self, id: ay_core::TermId) -> Sort {
        self.var_sorts
            .get(&id)
            .cloned()
            .unwrap_or_else(|| self.terms().sort(id).clone())
    }

    /// Get the sort of a term.
    ///
    /// This is an alias for [`term_sort`](Self::term_sort), provided for
    /// convenience when calling code reads more naturally as `solver.sort_of(t)`.
    #[must_use]
    pub fn sort_of(&self, term: Term) -> Sort {
        self.term_sort(term)
    }

    /// Get bound variable names and sorts from a quantifier term.
    ///
    /// Returns `None` if the term is not a quantifier.
    #[must_use]
    pub fn quantifier_bound_vars(&self, term: Term) -> Option<Vec<(String, Sort)>> {
        let id = self.resolve_term("quantifier_bound_vars", term).ok()?;
        match self.terms().get(id) {
            TermData::Forall(vars, _, _) | TermData::Exists(vars, _, _) => Some(vars.clone()),
            _ => None,
        }
    }

    /// Get trigger patterns from a quantifier term.
    ///
    /// Returns `None` if the term is not a quantifier.
    /// Each inner `Vec<Term>` is a multi-pattern (conjunction).
    /// The outer `Vec` contains alternative trigger sets (disjunction).
    #[must_use]
    pub fn quantifier_triggers(&self, term: Term) -> Option<Vec<Vec<Term>>> {
        let id = self.resolve_term("quantifier_triggers", term).ok()?;
        match self.terms().get(id) {
            TermData::Forall(_, _, triggers) | TermData::Exists(_, _, triggers) => Some(
                triggers
                    .iter()
                    .map(|ts| ts.iter().map(|&t| self.wrap_term(t)).collect())
                    .collect(),
            ),
            _ => None,
        }
    }

    /// Simultaneously replace each `from[i]` subterm of `term` with `to[i]`.
    ///
    /// Matching is by hash-consed term identity; substitution is simultaneous
    /// (a `from` match is replaced without recursing into the replacement).
    /// `from` and `to` are expected to have equal length; only the common
    /// prefix is honored if they differ. The result is interned and eagerly
    /// simplified, so e.g. substituting `x -> 5` in `(+ x 1)` yields `6`.
    ///
    /// Backs the Z3-compat `Z3_substitute` FFI entry point. Sort compatibility
    /// of each `from[i]`/`to[i]` pair is the caller's responsibility (the FFI
    /// layer reports `Z3_SORT_ERROR` for mismatches before calling this).
    #[must_use]
    pub fn substitute(&mut self, term: Term, from: &[Term], to: &[Term]) -> Term {
        let term_id = self.require_term("substitute", term);
        let from_ids = self.require_terms("substitute", from);
        let to_ids = self.require_terms("substitute", to);
        let result = self.terms_mut().substitute(term_id, &from_ids, &to_ids);
        self.wrap_term(result)
    }

    /// Return a simplified term that is logically equivalent to `term`.
    ///
    /// Rebuilds the term bottom-up through AY's simplifying constructors, which
    /// re-applies eager constant-folding and identity simplification to every
    /// node. FP constructors preserve their application shape; this explicit
    /// operation also applies the exact FP word-level rewriter used by solving.
    /// It folds constant/identity subexpressions not folded at build time
    /// (including raw parser-built or consumer-assembled terms):
    /// `(+ 2 3)` folds to `5`, `(and true p)` to `p`, `(+ x 0)` to `x`,
    /// `(ite true a b)` to `a`, `(select (store a i v) i)` to `v`, etc.
    ///
    /// The result is **logically equivalent** to the input — every step is a
    /// semantics-preserving simplification. Backs the Z3-compat `Z3_simplify`
    /// FFI entry point.
    #[must_use]
    pub fn simplify(&mut self, term: Term) -> Term {
        let id = self.require_term("simplify", term);
        let result = self.terms_mut().simplify(id);
        // Use the same exact FP rewrites as the solving pipeline. Constructors
        // retain their application shape until explicit simplification; NaN's
        // unspecified IEEE encoding remains symbolic.
        let fp_result = ay_fp::rewriter::FpRewriter::new().rewrite(self.terms_mut(), result);
        let result = if fp_result == result {
            result
        } else {
            // An FP fold can expose a constant BV/Boolean parent.
            self.terms_mut().simplify(fp_result)
        };
        self.wrap_term(result)
    }
}

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
use super::Solver;

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
    ///
    /// # Panics
    ///
    /// Panics if `term` was not created by this solver or is otherwise stale.
    #[must_use]
    pub fn format_term(&self, term: Term) -> String {
        self.executor.format_term(term.0)
    }

    /// Format a term as SMT-LIB text, or `None` if `term` does not index a
    /// live node in this solver's term store.
    ///
    /// Unlike [`format_term`](Self::format_term), which panics on a stale or
    /// foreign handle, this bounds-checks the handle first and returns `None`
    /// instead of panicking. Used by the Z3-compatible FFI
    /// (`Z3_ast_to_string`), where a foreign/stale `Z3_ast` must yield a null
    /// string rather than unwind a panic across the C boundary.
    #[must_use]
    pub fn format_term_checked(&self, term: Term) -> Option<String> {
        if term.0.index() >= self.terms().len() {
            return None;
        }
        Some(self.executor.format_term(term.0))
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

    /// Serialize the given assertion list in Z3's `Z3_solver_to_string` /
    /// z3py `Solver.sexpr()` shape: one `(declare-fun ...)` line per declared
    /// symbol followed by one `(assert ...)` line per assertion, with no
    /// script wrapper. This is a faithful dump of the passed assertions (never
    /// fabricated). Backs the Z3-compat `Z3_solver_to_string` FFI entry point,
    /// which holds its live assertions on the per-solver handle rather than on
    /// the executor's internal stack.
    #[must_use]
    pub fn assertions_sexpr(&self, assertions: &[Term]) -> String {
        let ids: Vec<ay_core::TermId> = assertions.iter().map(|t| t.id()).collect();
        self.executor.assertions_sexpr_for(&ids)
    }

    /// Get the kind of a term, including operator info for applications.
    #[must_use]
    pub fn term_kind(&self, term: Term) -> TermKind {
        match self.terms().get(term.0) {
            TermData::App(sym, args) => {
                let name = match sym {
                    Symbol::Named(n) => n.clone(),
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
        self.terms()
            .children(term.0)
            .into_iter()
            .map(Term)
            .collect()
    }

    /// Get the sort (type) of a term.
    ///
    /// Works for all sort kinds: Bool, Int, Real, BitVec, FloatingPoint, Array,
    /// String, Datatype, Uninterpreted, etc.
    #[must_use]
    pub fn term_sort(&self, term: Term) -> Sort {
        self.var_sorts
            .get(&term.0)
            .cloned()
            .unwrap_or_else(|| self.terms().sort(term.0).clone())
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
        match self.terms().get(term.0) {
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
        match self.terms().get(term.0) {
            TermData::Forall(_, _, triggers) | TermData::Exists(_, _, triggers) => Some(
                triggers
                    .iter()
                    .map(|ts| ts.iter().map(|&t| Term(t)).collect())
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
        let from_ids: Vec<_> = from.iter().map(|t| t.0).collect();
        let to_ids: Vec<_> = to.iter().map(|t| t.0).collect();
        Term(self.terms_mut().substitute(term.0, &from_ids, &to_ids))
    }

    /// Return a simplified term that is logically equivalent to `term`.
    ///
    /// Rebuilds the term bottom-up through AY's simplifying constructors, which
    /// re-applies eager constant-folding and identity simplification to every
    /// node. AY folds eagerly at construction, so terms built through the `mk_*`
    /// API are already a fixpoint (the result is the same interned term). The
    /// value-add is for terms whose constant/identity subexpressions were not
    /// folded at build time (e.g. raw parser-built or consumer-assembled terms):
    /// `(+ 2 3)` folds to `5`, `(and true p)` to `p`, `(+ x 0)` to `x`,
    /// `(ite true a b)` to `a`, `(select (store a i v) i)` to `v`, etc.
    ///
    /// The result is **logically equivalent** to the input — every step is a
    /// semantics-preserving simplification. Backs the Z3-compat `Z3_simplify`
    /// FFI entry point.
    #[must_use]
    pub fn simplify(&mut self, term: Term) -> Term {
        Term(self.terms_mut().simplify(term.0))
    }
}

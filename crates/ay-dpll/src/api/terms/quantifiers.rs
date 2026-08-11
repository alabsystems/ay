// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[allow(clippy::panic, deprecated)]
impl Solver {
    /// Create a universally quantified formula: `(forall ((x S) ...) body)`.
    ///
    /// `vars` must be variable terms (see [`Self::fresh_var`] and [`Self::declare_const`]).
    ///
    /// # Panics
    /// Panics if any element of `vars` is not a variable term, or if `vars` contains duplicates.
    /// Use [`Self::try_forall`] for a fallible version.
    pub fn forall(&mut self, vars: &[Term], body: Term) -> Term {
        self.try_forall(vars, body)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a universally quantified formula: `(forall ((x S) ...) body)`.
    ///
    /// Fallible version of [`forall`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if `body` is not a Bool.
    ///
    /// Returns [`SolverError::InvalidArgument`] if:
    /// - Any element of `vars` is not a variable term
    /// - `vars` contains duplicate variables
    ///
    /// [`forall`]: Solver::forall
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_forall(&mut self, vars: &[Term], body: Term) -> Result<Term, SolverError> {
        let body_id = self.resolve_term("forall", body)?;
        let var_ids = vars
            .iter()
            .copied()
            .map(|var| self.resolve_term("forall", var))
            .collect::<Result<Vec<_>, _>>()?;
        let body_sort = self.terms().sort(body_id).clone();
        if body_sort != Sort::Bool {
            return Err(SolverError::SortMismatch {
                operation: "forall",
                expected: "Bool",
                got: vec![body_sort],
            });
        }

        let mut seen = HashSet::default();
        let mut core_vars = Vec::with_capacity(vars.len());
        for &var_id in &var_ids {
            let name = match self.terms().get(var_id) {
                TermData::Var(name, _) => name.clone(),
                other => {
                    return Err(SolverError::InvalidArgument {
                        operation: "forall",
                        message: format!("expected variable term, got {other:?}"),
                    });
                }
            };

            if !seen.insert(var_id) {
                return Err(SolverError::InvalidArgument {
                    operation: "forall",
                    message: format!("duplicate bound variable: {name}"),
                });
            }

            let sort = self.terms().sort(var_id).clone();
            core_vars.push((name, sort));
        }
        let result = self.terms_mut().mk_forall(core_vars, body_id);
        Ok(self.wrap_term(result))
    }

    /// Mark a `forall` term as "E-matching only" — excluded from MBQI/CEGQI
    /// synthesis instantiation, discharged only by E-matching on a ground
    /// trigger. Used for the Hilbert-`choose` witness axiom so deductive-checks matches
    /// Verus's trigger-only semantics (a transparent predicate with no
    /// established ground witness must NOT let the chosen value be
    /// synthesis-instantiated). No-op unless `term` is a `Forall`. See
    /// [`ay_core::TermStore::mark_no_mbqi`]. Sound/conservative: skipping
    /// instantiation can only lose proofs, never produce a wrong-UNSAT.
    pub fn mark_no_mbqi(&mut self, term: Term) {
        if let Ok(id) = self.resolve_term("mark_no_mbqi", term) {
            self.terms_mut().mark_no_mbqi(id);
        }
    }

    /// Attach a `:qid` (quantifier identifier) to a `Forall`/`Exists` `term`.
    /// No-op unless `term` is a quantifier. Pure instantiation-hint metadata: it
    /// never changes the asserted formula's semantics or any sat/unsat verdict.
    /// Read back with [`Self::quantifier_id`]. See [`ay_core::TermStore::set_quantifier_id`].
    pub fn set_quantifier_id(&mut self, term: Term, qid: &str) {
        if let Ok(id) = self.resolve_term("set_quantifier_id", term) {
            self.terms_mut().set_quantifier_id(id, qid.to_string());
        }
    }

    /// The `:qid` attached to `term`, if any (see [`Self::set_quantifier_id`]).
    #[must_use]
    pub fn quantifier_id(&self, term: Term) -> Option<String> {
        let id = self.resolve_term("quantifier_id", term).ok()?;
        self.terms().quantifier_id(id).map(str::to_string)
    }

    /// Attach a `:skolemid` to a `Forall`/`Exists` `term`. No-op unless `term`
    /// is a quantifier. Metadata only. Read back with [`Self::skolem_id`].
    pub fn set_skolem_id(&mut self, term: Term, skid: &str) {
        if let Ok(id) = self.resolve_term("set_skolem_id", term) {
            self.terms_mut().set_skolem_id(id, skid.to_string());
        }
    }

    /// The `:skolemid` attached to `term`, if any (see [`Self::set_skolem_id`]).
    #[must_use]
    pub fn skolem_id(&self, term: Term) -> Option<String> {
        let id = self.resolve_term("skolem_id", term).ok()?;
        self.terms().skolem_id(id).map(str::to_string)
    }

    /// Try to create a constant-bounded integer universal quantifier.
    ///
    /// This builds the canonical SMT shape:
    /// `(forall ((i Int)) (=> (and (<= lower i) (< i upper)) body))`.
    /// The solver's finite-domain preprocessor recognizes this form for small
    /// ranges, which is the EXTERNAL_CODEGEN memory-proof pattern for array-range checks.
    ///
    /// Empty ranges are valid and return `true` after validating `var` and
    /// `body`.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if `var` is not `Int` or `body`
    /// is not `Bool`.
    ///
    /// Returns [`SolverError::InvalidArgument`] if `var` is not a variable term.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_forall_int_range(
        &mut self,
        var: Term,
        lower_inclusive: i64,
        upper_exclusive: i64,
        body: Term,
    ) -> Result<Term, SolverError> {
        self.try_forall_int_range_bigint(
            var,
            &BigInt::from(lower_inclusive),
            &BigInt::from(upper_exclusive),
            body,
        )
    }

    /// Try to create a constant-bounded integer universal quantifier with
    /// arbitrary-precision bounds.
    ///
    /// Ranges outside the finite-domain expansion budget remain valid
    /// quantified formulas; they simply fall back to the normal quantifier
    /// pipeline during solving.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if `var` is not `Int` or `body`
    /// is not `Bool`.
    ///
    /// Returns [`SolverError::InvalidArgument`] if `var` is not a variable term.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_forall_int_range_bigint(
        &mut self,
        var: Term,
        lower_inclusive: &BigInt,
        upper_exclusive: &BigInt,
        body: Term,
    ) -> Result<Term, SolverError> {
        let var_id = self.resolve_term("forall_int_range", var)?;
        let body_id = self.resolve_term("forall_int_range", body)?;
        let var_sort = self.terms().sort(var_id).clone();
        if var_sort != Sort::Int {
            return Err(SolverError::SortMismatch {
                operation: "forall_int_range",
                expected: "Int bound variable",
                got: vec![var_sort],
            });
        }

        let body_sort = self.terms().sort(body_id).clone();
        if body_sort != Sort::Bool {
            return Err(SolverError::SortMismatch {
                operation: "forall_int_range",
                expected: "Bool",
                got: vec![body_sort],
            });
        }

        if !matches!(self.terms().get(var_id), TermData::Var(_, _)) {
            return Err(SolverError::InvalidArgument {
                operation: "forall_int_range",
                message: "expected variable term".to_string(),
            });
        }

        if lower_inclusive >= upper_exclusive {
            return Ok(self.bool_const(true));
        }

        let lower = self.int_const_bigint(lower_inclusive);
        let upper = self.int_const_bigint(upper_exclusive);
        let lower_le_var = self.try_le(lower, var)?;
        let var_lt_upper = self.try_lt(var, upper)?;
        let guard = self.try_and(lower_le_var, var_lt_upper)?;
        let guarded_body = self.try_implies(guard, body)?;
        self.try_forall(&[var], guarded_body)
    }

    /// Create a universally quantified formula with trigger patterns.
    ///
    /// Triggers guide E-matching instantiation. Each inner slice is a multi-trigger
    /// (all patterns must match for instantiation). Multiple outer elements are
    /// alternative trigger sets.
    ///
    /// # Panics
    /// Panics on invalid bound variables or triggers. Use [`Self::try_forall_with_triggers`]
    /// for a fallible version.
    pub fn forall_with_triggers(
        &mut self,
        vars: &[Term],
        body: Term,
        triggers: &[&[Term]],
    ) -> Term {
        self.try_forall_with_triggers(vars, body, triggers)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a universally quantified formula with trigger patterns.
    ///
    /// # Errors
    /// Returns [`SolverError::SortMismatch`] if `body` is not a Bool.
    ///
    /// Returns [`SolverError::InvalidArgument`] if:
    /// - Any element of `vars` is not a variable term
    /// - `vars` contains duplicate variables
    ///
    /// Returns [`SolverError::InvalidTrigger`] if any trigger application does not
    /// contain at least one bound variable.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_forall_with_triggers(
        &mut self,
        vars: &[Term],
        body: Term,
        triggers: &[&[Term]],
    ) -> Result<Term, SolverError> {
        let body_id = self.resolve_term("forall_with_triggers", body)?;
        let var_ids = vars
            .iter()
            .copied()
            .map(|var| self.resolve_term("forall_with_triggers", var))
            .collect::<Result<Vec<_>, _>>()?;
        let trigger_ids = triggers
            .iter()
            .map(|multi| {
                multi
                    .iter()
                    .copied()
                    .map(|term| self.resolve_term("forall_with_triggers", term))
                    .collect::<Result<Vec<_>, _>>()
            })
            .collect::<Result<Vec<_>, _>>()?;
        let body_sort = self.terms().sort(body_id).clone();
        if body_sort != Sort::Bool {
            return Err(SolverError::SortMismatch {
                operation: "forall_with_triggers",
                expected: "Bool",
                got: vec![body_sort],
            });
        }

        let mut seen = HashSet::default();
        let mut bound_names: HashSet<String> = HashSet::default();
        let mut core_vars = Vec::with_capacity(vars.len());
        for &var_id in &var_ids {
            let name = match self.terms().get(var_id) {
                TermData::Var(name, _) => name.clone(),
                other => {
                    return Err(SolverError::InvalidArgument {
                        operation: "forall_with_triggers",
                        message: format!("expected variable term, got {other:?}"),
                    });
                }
            };

            if !seen.insert(var_id) {
                return Err(SolverError::InvalidArgument {
                    operation: "forall_with_triggers",
                    message: format!("duplicate bound variable: {name}"),
                });
            }

            let sort = self.terms().sort(var_id).clone();
            bound_names.insert(name.clone());
            core_vars.push((name, sort));
        }

        let mut core_triggers: Vec<Vec<TermId>> = Vec::new();
        for multi in trigger_ids {
            let mut multi_terms: Vec<TermId> = Vec::new();
            for term_id in multi {
                let TermData::App(_, _) = self.terms().get(term_id) else {
                    continue;
                };
                if !contains_bound_var(self.terms(), term_id, &bound_names) {
                    return Err(SolverError::InvalidTrigger {
                        operation: "forall_with_triggers",
                        message: "trigger must contain at least one bound variable".to_string(),
                    });
                }
                multi_terms.push(term_id);
            }
            if !multi_terms.is_empty() {
                core_triggers.push(multi_terms);
            }
        }

        let result = self
            .terms_mut()
            .mk_forall_with_triggers(core_vars, body_id, core_triggers);
        Ok(self.wrap_term(result))
    }

    /// Create an existentially quantified formula: `(exists ((x S) ...) body)`.
    ///
    /// `vars` must be variable terms (see [`Self::fresh_var`] and [`Self::declare_const`]).
    ///
    /// # Panics
    /// Panics if any element of `vars` is not a variable term, or if `vars` contains duplicates.
    /// Use [`Self::try_exists`] for a fallible version.
    pub fn exists(&mut self, vars: &[Term], body: Term) -> Term {
        self.try_exists(vars, body)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create an existentially quantified formula: `(exists ((x S) ...) body)`.
    ///
    /// Fallible version of [`exists`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if `body` is not a Bool.
    ///
    /// Returns [`SolverError::InvalidArgument`] if:
    /// - Any element of `vars` is not a variable term
    /// - `vars` contains duplicate variables
    ///
    /// [`exists`]: Solver::exists
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_exists(&mut self, vars: &[Term], body: Term) -> Result<Term, SolverError> {
        let body_id = self.resolve_term("exists", body)?;
        let var_ids = vars
            .iter()
            .copied()
            .map(|var| self.resolve_term("exists", var))
            .collect::<Result<Vec<_>, _>>()?;
        let body_sort = self.terms().sort(body_id).clone();
        if body_sort != Sort::Bool {
            return Err(SolverError::SortMismatch {
                operation: "exists",
                expected: "Bool",
                got: vec![body_sort],
            });
        }

        let mut seen = HashSet::default();
        let mut core_vars = Vec::with_capacity(vars.len());
        for &var_id in &var_ids {
            let name = match self.terms().get(var_id) {
                TermData::Var(name, _) => name.clone(),
                other => {
                    return Err(SolverError::InvalidArgument {
                        operation: "exists",
                        message: format!("expected variable term, got {other:?}"),
                    });
                }
            };

            if !seen.insert(var_id) {
                return Err(SolverError::InvalidArgument {
                    operation: "exists",
                    message: format!("duplicate bound variable: {name}"),
                });
            }

            let sort = self.terms().sort(var_id).clone();
            core_vars.push((name, sort));
        }
        let result = self.terms_mut().mk_exists(core_vars, body_id);
        Ok(self.wrap_term(result))
    }

    /// Create an existentially quantified formula with trigger patterns.
    ///
    /// Triggers guide E-matching instantiation. Each inner slice is a multi-trigger
    /// (all patterns must match for instantiation). Multiple outer elements are
    /// alternative trigger sets.
    ///
    /// # Panics
    /// Panics on invalid bound variables or triggers. Use [`Self::try_exists_with_triggers`]
    /// for a fallible version.
    pub fn exists_with_triggers(
        &mut self,
        vars: &[Term],
        body: Term,
        triggers: &[&[Term]],
    ) -> Term {
        self.try_exists_with_triggers(vars, body, triggers)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create an existentially quantified formula with trigger patterns.
    ///
    /// # Errors
    /// Returns [`SolverError::SortMismatch`] if `body` is not a Bool.
    ///
    /// Returns [`SolverError::InvalidArgument`] if:
    /// - Any element of `vars` is not a variable term
    /// - `vars` contains duplicate variables
    ///
    /// Returns [`SolverError::InvalidTrigger`] if any trigger application does not
    /// contain at least one bound variable.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_exists_with_triggers(
        &mut self,
        vars: &[Term],
        body: Term,
        triggers: &[&[Term]],
    ) -> Result<Term, SolverError> {
        let body_id = self.resolve_term("exists_with_triggers", body)?;
        let var_ids = vars
            .iter()
            .copied()
            .map(|var| self.resolve_term("exists_with_triggers", var))
            .collect::<Result<Vec<_>, _>>()?;
        let trigger_ids = triggers
            .iter()
            .map(|multi| {
                multi
                    .iter()
                    .copied()
                    .map(|term| self.resolve_term("exists_with_triggers", term))
                    .collect::<Result<Vec<_>, _>>()
            })
            .collect::<Result<Vec<_>, _>>()?;
        let body_sort = self.terms().sort(body_id).clone();
        if body_sort != Sort::Bool {
            return Err(SolverError::SortMismatch {
                operation: "exists_with_triggers",
                expected: "Bool",
                got: vec![body_sort],
            });
        }

        let mut seen = HashSet::default();
        let mut bound_names: HashSet<String> = HashSet::default();
        let mut core_vars = Vec::with_capacity(vars.len());
        for &var_id in &var_ids {
            let name = match self.terms().get(var_id) {
                TermData::Var(name, _) => name.clone(),
                other => {
                    return Err(SolverError::InvalidArgument {
                        operation: "exists_with_triggers",
                        message: format!("expected variable term, got {other:?}"),
                    });
                }
            };

            if !seen.insert(var_id) {
                return Err(SolverError::InvalidArgument {
                    operation: "exists_with_triggers",
                    message: format!("duplicate bound variable: {name}"),
                });
            }

            bound_names.insert(name.clone());
            let sort = self.terms().sort(var_id).clone();
            core_vars.push((name, sort));
        }

        let mut core_triggers: Vec<Vec<TermId>> = Vec::new();
        for multi in trigger_ids {
            let mut multi_terms: Vec<TermId> = Vec::new();
            for term_id in multi {
                let TermData::App(_, _) = self.terms().get(term_id) else {
                    continue;
                };
                if !contains_bound_var(self.terms(), term_id, &bound_names) {
                    return Err(SolverError::InvalidTrigger {
                        operation: "exists_with_triggers",
                        message: "trigger must contain at least one bound variable".to_string(),
                    });
                }
                multi_terms.push(term_id);
            }
            if !multi_terms.is_empty() {
                core_triggers.push(multi_terms);
            }
        }

        let result = self
            .terms_mut()
            .mk_exists_with_triggers(core_vars, body_id, core_triggers);
        Ok(self.wrap_term(result))
    }
}

fn contains_bound_var(terms: &TermStore, term: TermId, bound_names: &HashSet<String>) -> bool {
    match terms.get(term) {
        TermData::Var(name, _) => bound_names.contains(name),
        TermData::App(_, args) => args
            .iter()
            .any(|&arg| contains_bound_var(terms, arg, bound_names)),
        TermData::Not(inner) => contains_bound_var(terms, *inner, bound_names),
        TermData::Ite(c, t, e) => {
            contains_bound_var(terms, *c, bound_names)
                || contains_bound_var(terms, *t, bound_names)
                || contains_bound_var(terms, *e, bound_names)
        }
        TermData::Let(_, _) | TermData::Forall(..) | TermData::Exists(..) => false,
        TermData::Const(_) => false,
        other => unreachable!("unhandled TermData variant in contains_bound_var(): {other:?}"),
    }
}

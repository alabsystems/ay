// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Assertion stack management: assert, push, pop, scopes, reset.

mod adoption_support;
mod native_power;
#[cfg(test)]
mod source_origin_tests;

use ay_core::term::Symbol;
use ay_core::{Sort, TermData, TermId};
use ay_frontend::command::Term as ParsedTerm;
use ay_frontend::Command;

use crate::api::types::{FuncDeclIdentity, NativeReplayEventKind, SolverError, Term};
use crate::api::{Solver, SolverCacheToken};
use crate::executor::NATIVE_API_ASSERTION_PLACEHOLDER;

impl Solver {
    /// Assert a constraint (must be a Boolean term)
    ///
    /// # Panics
    /// Panics if `term` is not Bool sort. Use [`Self::try_assert_term`] for a fallible version.
    #[allow(clippy::panic)]
    pub fn assert_term(&mut self, term: Term) {
        self.try_assert_term(term).unwrap_or_else(|e| panic!("{e}"));
    }

    /// Try to assert a constraint (must be a Boolean term).
    ///
    /// Fallible version of [`assert_term`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if `term` is not a Bool sort.
    ///
    /// [`assert_term`]: Solver::assert_term
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_assert_term(&mut self, term: Term) -> Result<(), SolverError> {
        self.assert_native_term(
            term,
            ParsedTerm::Symbol(NATIVE_API_ASSERTION_PLACEHOLDER.to_string()),
        )
    }

    pub(super) fn assert_native_term(
        &mut self,
        term: Term,
        source: ParsedTerm,
    ) -> Result<(), SolverError> {
        let term_id = self.resolve_term("assert_term", term)?;
        if let Some(message) = self
            .executor
            .array_ext_witness_registration_error(&[term_id])
        {
            return Err(SolverError::InvalidArgument {
                operation: "assert_term",
                message,
            });
        }
        let sort = self.terms().sort(term_id).clone();
        if sort != Sort::Bool {
            return Err(SolverError::SortMismatch {
                operation: "assert_term",
                expected: "Bool",
                got: vec![sort],
            });
        }

        self.executor.note_api_assertion_mutation();

        // Match the parsed-SMT macro finder at the native API boundary.  A
        // pure top-level `forall X. f(X) = body` over a fresh declared UF is
        // an exact definition: later native applications can be expanded by
        // construction, while model output emits the lambda body.  Every
        // refusal below keeps the original quantified assertion unchanged.
        // A native `^` reaches the engine with the elaborator's semantics:
        // literal positive integer exponents unfold to products, anything else
        // stays for the executor's capability gate (`native_power`).
        let lowered = self.lower_native_integer_powers(term_id);
        let asserted_term = self
            .try_adopt_native_definitional_forall(lowered)
            .map_or(lowered, |adoption| adoption.replacement);

        // Keep assertions_parsed aligned with assertions for proof-rewrite
        // invariants when assertions are added via the native API path.
        let ctx = self.executor.context_mut_internal();
        ctx.add_native_assertion_with_parsed(asserted_term, source);
        self.record_native_replay_event(NativeReplayEventKind::Assert {
            term: term_id,
            name: None,
        });
        Ok(())
    }

    /// Assert a named constraint for unsat core attribution.
    ///
    /// Equivalent to `(assert (! term :named name))` in SMT-LIB.
    /// After an UNSAT result, call [`try_get_unsat_core`] to get the subset
    /// of names that contributed to unsatisfiability.
    ///
    /// This is the stable consumer workflow for vacuity detection:
    /// 1. Enable cores with [`set_produce_unsat_cores`](Self::set_produce_unsat_cores).
    /// 2. Name each top-level assertion group (for example
    ///    `preconditions`, `encoding_axioms`, `negated_postcondition`).
    /// 3. Solve and inspect [`try_get_unsat_core`](Self::try_get_unsat_core).
    /// 4. If `negated_postcondition` is absent from the core, the UNSAT proof
    ///    is vacuous with respect to the postcondition.
    ///
    /// Assertion names should be unique within the currently active solver
    /// scope. Reusing a name overwrites the earlier core-reporting entry for
    /// that name.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if `term` is not a Bool sort.
    ///
    /// [`try_get_unsat_core`]: Solver::try_get_unsat_core
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_assert_named(&mut self, term: Term, name: &str) -> Result<(), SolverError> {
        let term_id = self.resolve_term("assert_named", term)?;
        if let Some(message) = self
            .executor
            .array_ext_witness_registration_error(&[term_id])
        {
            return Err(SolverError::InvalidArgument {
                operation: "assert_named",
                message,
            });
        }
        let sort = self.terms().sort(term_id).clone();
        if sort != Sort::Bool {
            return Err(SolverError::SortMismatch {
                operation: "assert_named",
                expected: "Bool",
                got: vec![sort],
            });
        }

        self.executor.note_api_assertion_mutation();

        // #defmacro-named-preuse: a core label is metadata, not meaning, so a
        // named definitional forall is exactly as adoptable as an anonymous
        // one (`try_assert_term`). The label follows the assertion that
        // actually lands on the stack — the discharged replacement — so the
        // named-core redirect assumes the replacement, never the raw
        // quantifier it discharged; and the label is recorded against the
        // adopted head so a harvested core over the expanded assertions
        // still reports the definition it depends on.
        let lowered = self.lower_native_integer_powers(term_id);
        let adoption = self.try_adopt_native_definitional_forall(lowered);
        let asserted_term = adoption
            .as_ref()
            .map_or(lowered, |adoption| adoption.replacement);

        let ctx = self.executor.context_mut_internal();
        // A native assertion's optional core name is metadata, not surface
        // syntax.  Reuse the anonymous native sentinel so strict proof
        // reconstruction derives from the exact asserted term instead of
        // trying to elaborate a fabricated `__ay_named_*` variable.
        ctx.add_native_assertion_with_parsed(
            asserted_term,
            ParsedTerm::Symbol(NATIVE_API_ASSERTION_PLACEHOLDER.to_string()),
        );
        ctx.register_named_term(name.to_string(), asserted_term);
        if let Some(adoption) = &adoption {
            ctx.note_adopted_definition_label(&adoption.head, name.to_string());
        }
        self.record_native_replay_event(NativeReplayEventKind::Assert {
            term: term_id,
            name: Some(name.to_string()),
        });
        Ok(())
    }

    /// `term` with every native `^` whose exponent is a literal positive
    /// integer unfolded into a product, exactly as the assertion boundary
    /// lowers it. A ground power then folds under [`Self::simplify`] (the Z3
    /// C API's `Z3_model_eval` relies on this: `2^3` evaluates to `8`).
    ///
    /// # Panics
    ///
    /// Panics if `term` is not a live term of this solver.
    pub fn lower_native_powers(&mut self, term: Term) -> Term {
        let id = self.require_term("lower_native_powers", term);
        let lowered = self.lower_native_integer_powers(id);
        self.wrap_term(lowered)
    }

    /// Push a new scope for incremental solving
    ///
    /// # Panics
    ///
    /// Panics if the executor fails to push a scope. Use [`try_push`] for a
    /// fallible version that returns an error instead.
    ///
    /// [`try_push`]: Solver::try_push
    #[allow(clippy::panic)]
    pub fn push(&mut self) {
        self.try_push()
            .unwrap_or_else(|e| panic!("Failed to push scope: {e}"));
    }

    /// Try to push a new scope for incremental solving.
    ///
    /// Fallible version of [`push`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns an error if the executor fails to push a scope.
    ///
    /// [`push`]: Solver::push
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_push(&mut self) -> Result<(), SolverError> {
        self.executor.execute(&Command::Push(1))?;
        self.scope_level += 1;
        self.record_native_replay_event(NativeReplayEventKind::Push);
        Ok(())
    }

    /// Pop the most recent scope
    ///
    /// # Panics
    ///
    /// Panics if there are no scopes to pop or if the executor fails.
    /// Use [`try_pop`] for a fallible version that returns an error instead.
    ///
    /// [`try_pop`]: Solver::try_pop
    #[allow(clippy::panic)]
    pub fn pop(&mut self) {
        self.try_pop()
            .unwrap_or_else(|e| panic!("Failed to pop scope: {e}"));
    }

    /// Try to pop the most recent scope.
    ///
    /// Fallible version of [`pop`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns an error if there are no scopes to pop or if the executor fails.
    ///
    /// [`pop`]: Solver::pop
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_pop(&mut self) -> Result<(), SolverError> {
        if self.scope_level == 0 {
            return Err(SolverError::ExecutorError(crate::ExecutorError::Elaborate(
                ay_frontend::ElaborateError::ScopeUnderflow,
            )));
        }
        self.executor.execute(&Command::Pop(1))?;
        self.scope_level -= 1;
        self.record_native_replay_event(NativeReplayEventKind::Pop);
        Ok(())
    }

    /// Return the number of backtracking scopes (push/pop levels).
    #[must_use]
    pub fn num_scopes(&self) -> u32 {
        self.scope_level
    }

    /// Return the current set of asserted terms.
    #[must_use]
    pub fn assertions(&self) -> Vec<Term> {
        self.assertions_iter().collect()
    }

    /// Borrow the current asserted terms without allocating a vector.
    ///
    /// Order, duplicates and active scopes match [`Self::assertions`]. Each
    /// item carries the same current arena/entry authentication as other native
    /// term handles. The exact length can be checked before reserving storage.
    #[must_use]
    pub fn assertions_iter(&self) -> impl ExactSizeIterator<Item = Term> + '_ {
        self.executor
            .context()
            .assertions
            .iter()
            .map(|&id| self.wrap_term(id))
    }

    /// Reset the solver, clearing all assertions
    ///
    /// # Panics
    ///
    /// Panics if the executor fails to reset. Use [`try_reset`] for a
    /// fallible version that returns an error instead.
    ///
    /// [`try_reset`]: Solver::try_reset
    #[allow(clippy::panic)]
    pub fn reset(&mut self) {
        self.try_reset()
            .unwrap_or_else(|e| panic!("Failed to reset solver: {e}"));
    }

    /// Try to reset the solver, clearing all assertions.
    ///
    /// Fallible version of [`reset`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns an error if the executor fails to reset.
    ///
    /// [`reset`]: Solver::reset
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_reset(&mut self) -> Result<(), SolverError> {
        self.executor.execute(&Command::Reset)?;
        self.term_arena = crate::api::types::TermArenaStamp::fresh();
        // A full reset discards the term/declaration arena. Rotate the cache
        // generation and invalidate every clone of the old token before callers
        // can inspect state holding old handles.
        self.cache_token.invalidate();
        self.cache_token = SolverCacheToken::new();
        self.scope_level = 0;
        self.var_names.clear();
        self.adopted_tactic_declarations.clear();
        self.var_terms_by_name.clear();
        self.var_sorts.clear();
        self.last_assumptions = None;
        self.last_unknown_reason = None;
        self.last_executor_error = None;
        self.last_artifact_export_failure = None;
        self.last_model_extraction_failure = None;
        self.soft_constraints.clear();
        self.optimization_sequence.clear();
        self.defined_funs.clear();
        self.native_fun_signatures.clear();
        self.core_tracker = crate::api::types::CoreEvolutionTracker::new();
        self.native_replay_events.clear();
        self.record_native_replay_event(NativeReplayEventKind::Reset);
        Ok(())
    }

    /// Reset all assertions and scopes, preserving logic and declarations.
    ///
    /// Unlike [`try_reset`] which clears everything (logic, declarations,
    /// assertions), this preserves the current logic and all declared
    /// constants/functions. Only assertions and scope levels are cleared.
    ///
    /// Equivalent to `(reset-assertions)` in SMT-LIB 2.6 section 4.2.2.
    ///
    /// # Errors
    ///
    /// Returns an error if the executor fails to reset assertions.
    ///
    /// [`try_reset`]: Solver::try_reset
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_reset_assertions(&mut self) -> Result<(), SolverError> {
        self.executor.execute(&Command::ResetAssertions)?;
        self.scope_level = 0;
        // Preserve explicit API-level definitions.  Definitions adopted from
        // asserted foralls lose their justification here and must disappear,
        // matching the frontend context's adopted-macro reset.
        self.defined_funs
            .retain(|_, definition| !definition.assertion_derived);
        self.last_assumptions = None;
        self.last_unknown_reason = None;
        self.last_executor_error = None;
        self.last_artifact_export_failure = None;
        self.last_model_extraction_failure = None;
        self.soft_constraints.clear();
        self.optimization_sequence.clear();
        self.core_tracker = crate::api::types::CoreEvolutionTracker::new();
        self.record_native_replay_event(NativeReplayEventKind::ResetAssertions);
        Ok(())
    }

    /// Whether a definition adopted from an asserted definitional `forall` is
    /// installed. While one is, [`Self::try_apply`] expands every new
    /// application of its head at construction; an embedder that shares one
    /// solver between several assertion sets (the Z3 C API's solver handles)
    /// must not leave such a definition installed past the solve it served,
    /// or terms built for another assertion set arrive pre-expanded.
    /// [`Self::try_reset_assertions`] removes them.
    #[must_use]
    pub fn has_assertion_derived_definitions(&self) -> bool {
        self.defined_funs
            .values()
            .any(|definition| definition.assertion_derived)
    }

    /// Adopt a native, already-elaborated definitional forall as an exact
    /// macro, returning the assertion that replaces the discharged `forall`.
    ///
    /// This is deliberately stricter than syntactic recognition alone.  Raw
    /// applications of the defined symbol that were built BEFORE the definition
    /// arrived are the hazard for a handle-based API: a caller can retain any
    /// prebuilt term and assert it after adoption, bypassing expansion in
    /// `try_apply`, so discharging the `forall` would strand them as a
    /// disconnected uninterpreted symbol.  Every such application is therefore
    /// PINNED to its own definitional instance in the returned assertion, and
    /// any application that cannot be pinned exactly (a variable argument, a
    /// mismatched arity/sort, a quantified definition body) REFUSES the whole
    /// adoption.  With no earlier application the replacement is the reflexive
    /// tautology, exactly as before.
    fn try_adopt_native_definitional_forall(
        &mut self,
        assertion: TermId,
    ) -> Option<NativeDefinitionalAdoption> {
        if self.scope_level != 0 {
            return None;
        }
        if !self.adoption_suppressed_funs.is_empty()
            && self.definitional_head_is_adoption_suppressed(assertion)
        {
            return None;
        }
        let TermData::Forall(vars, body, _) = self.terms().get(assertion).clone() else {
            return None;
        };
        if vars.is_empty() {
            return None;
        }
        for i in 0..vars.len() {
            for j in (i + 1)..vars.len() {
                if vars[i].0 == vars[j].0 {
                    return None;
                }
            }
        }
        let TermData::App(Symbol::Named(eq), sides) = self.terms().get(body).clone() else {
            return None;
        };
        if eq != "=" || sides.len() != 2 {
            return None;
        }

        let (core_name, param_terms, head, definition_body) = match (
            self.exact_native_definitional_head(sides[0], &vars),
            self.exact_native_definitional_head(sides[1], &vars),
        ) {
            (Some((name, params, head)), None) => (name, params, head, sides[1]),
            (None, Some((name, params, head))) => (name, params, head, sides[0]),
            _ => return None,
        };
        let (name, registration) = self
            .native_fun_signatures
            .iter()
            .find(|(_, registration)| registration.core_name == core_name)?;
        // The frontend model-interpretation hook intentionally supports only
        // declarations whose public and core names coincide. A builtin-name
        // collision has a private identity and therefore remains an ordinary
        // UF instead of being unsafely adopted through a spelling-keyed path.
        if registration.core_name != *name || self.defined_funs.contains_key(name) {
            return None;
        }
        let domain = &registration.domain;
        let range = &registration.range;
        let core_domain: Vec<Sort> = domain
            .iter()
            .map(|sort| self.lower_live_sort(sort))
            .collect();
        let core_range = self.lower_live_sort(range);
        let declaration_identity = registration.identity.clone();
        if domain.len() != vars.len()
            || core_domain
                .iter()
                .zip(vars.iter())
                .any(|(declared, (_, bound))| *declared != *bound)
            || core_range != *self.terms().sort(definition_body)
        {
            return None;
        }

        // Native Terms are persistent handles, so a raw application of `f`
        // built BEFORE the definition arrived cannot be expanded retroactively:
        // the caller may already have asserted it, or may assert a retained
        // handle later, bypassing expansion in `try_apply`.  Adopting while
        // such a term exists would strand it as a disconnected uninterpreted
        // symbol — the definition would be discharged while those occurrences
        // stayed unconstrained.
        //
        // Collect them instead of refusing outright, and PIN each to the value
        // the definition gives it (below).  That keeps the adoption exactly as
        // strong as the `forall` it discharges: the arena scan is COMPLETE
        // (every raw application of `f` that exists), the set is CLOSED (after
        // adoption `try_apply` expands, so no new raw application can be
        // built), and each pin is read from the definition body itself, never
        // invented.  Any occurrence that cannot be pinned keeps the original
        // REFUSAL:
        //
        //   * an argument mentioning a bound variable — the enclosing
        //     quantifier's OTHER instances would be raw applications at points
        //     no pin covers;
        //   * an arity or argument-sort mismatch (an overloaded second use);
        //   * more occurrences than `RAW_APPLICATION_PIN_CAP`.
        //   * a PREDICATE (Bool-ranged) definition: the pin is a Bool/Bool
        //     equality that strict UNSAT certification cannot currently
        //     reconstruct (`EufCongruentPred: predicate symbols differ`), so a
        //     genuinely provable UNSAT would be rejected and demoted to
        //     Unknown.  Refusing keeps the pre-pinning verdict exactly.
        let range_is_bool = range.as_term_sort() == Sort::Bool;
        // A declared constant and a quantifier binder are both `Var` nodes in
        // the arena, so "mentions a bound variable" is decided by NAME against
        // every binder any quantifier in the arena introduces (collected
        // below): a `Var` whose name no binder ever bound is a free constant,
        // and `f(i)` over a declared `i` is a ground application the pin
        // covers exactly. A constant that shares its spelling with some
        // binder is treated as bound — fail-closed, refusing the adoption —
        // because the two cannot be told apart term-by-term
        // (#defmacro-named-preuse: deductive-checks's `out = f(i)` before the
        // definition of `f`, with `i` a declared constant).
        let binder_names = arena_binder_names(self);
        let mut stale_applications: Vec<(TermId, Vec<TermId>)> = Vec::new();
        for id in self.terms().term_ids() {
            if id == head {
                continue;
            }
            let TermData::App(Symbol::Named(other), args) = self.terms().get(id) else {
                continue;
            };
            if other != &core_name {
                continue;
            }
            let args = args.clone();
            if args.len() != vars.len() {
                return None;
            }
            for (arg, (_, bound)) in args.iter().zip(vars.iter()) {
                if self.terms().sort(*arg) != bound {
                    return None;
                }
                if term_mentions_binder_var(self, *arg, &binder_names) {
                    return None;
                }
            }
            if range_is_bool {
                return None;
            }
            stale_applications.push((id, args));
        }
        if stale_applications.len() > RAW_APPLICATION_PIN_CAP {
            return None;
        }
        // Pinning substitutes the binder terms into the definition body by
        // TERM IDENTITY.  A quantifier inside that body could re-bind the same
        // identity, so the substitution would capture.  No pin, no exposure —
        // refuse rather than reason about it.
        if !stale_applications.is_empty() && term_contains_quantifier(self, definition_body) {
            return None;
        }

        let params: Vec<(String, Sort)> = vars.clone();
        if !self
            .executor
            .context_mut_internal()
            // Claim the pinned-uses exemption ONLY when there is something to
            // exempt.  With no pre-definition application the original
            // "no earlier constraint may mention it" check runs unchanged.
            .try_register_native_adopted_macro_interp(
                name,
                &params,
                definition_body,
                !stale_applications.is_empty(),
            )
        {
            return None;
        }
        let head = name.clone();
        self.defined_funs.insert(
            head.clone(),
            super::super::DefinedFun {
                params: params
                    .iter()
                    .zip(param_terms.iter().copied())
                    .map(|((name, _), term)| (name.clone(), term))
                    .collect(),
                body: definition_body,
                return_sort: core_range,
                assertion_derived: true,
                identity: FuncDeclIdentity::Frontend(declaration_identity),
            },
        );

        // Replace the discharged `forall` with the ground pins for the raw
        // applications that predated it.  With no such application this is the
        // reflexive tautology, byte-identical to the previous behaviour.  Each
        // pin is the definition INSTANTIATED at that application's own
        // arguments — an exact consequence of the assertion being replaced, so
        // the swap can only weaken, never strengthen (no UNSAT can be created);
        // and because the scan above is complete and closed, any model of the
        // pins extends to a model of the original `forall` by reading `f` off
        // the definition body everywhere else, so no SAT is created either.
        let mut replacement = self.wrap_term(self.terms().true_term());
        for (raw, args) in stale_applications {
            let subst: ay_core::kani_compat::DetHashMap<TermId, TermId> =
                param_terms.iter().copied().zip(args).collect();
            let expanded = self.substitute_defined_fun_body(definition_body, &subst);
            let pin = self.eq(self.wrap_term(raw), self.wrap_term(expanded));
            replacement = self.and(replacement, pin);
        }
        Some(NativeDefinitionalAdoption {
            head,
            replacement: replacement.id(),
        })
    }
}

/// A native definitional forall adopted as a macro: the caller-visible head
/// name and the assertion that replaces the discharged `forall` on the stack.
struct NativeDefinitionalAdoption {
    head: String,
    replacement: TermId,
}

/// The most raw pre-definition applications of one symbol that adoption will
/// pin.  Beyond this the adoption REFUSES (status quo), bounding the extra
/// ground equations a single assertion can introduce.
const RAW_APPLICATION_PIN_CAP: usize = 256;

/// Does `term`'s DAG contain a quantifier anywhere?  Fail-closed default: an
/// unrecognized node counts as one.
fn term_contains_quantifier(solver: &Solver, term: TermId) -> bool {
    let mut seen = ay_core::kani_compat::DetHashSet::default();
    let mut stack = vec![term];
    while let Some(current) = stack.pop() {
        if !seen.insert(current) {
            continue;
        }
        match solver.terms().get(current) {
            TermData::Forall(_, _, _) | TermData::Exists(_, _, _) => return true,
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, t, e) => stack.extend([*c, *t, *e]),
            TermData::Let(bindings, body) => {
                stack.extend(bindings.iter().map(|(_, value)| *value));
                stack.push(*body);
            }
            TermData::Const(_) | TermData::Var(_, _) => {}
            _ => return true,
        }
    }
    false
}

/// Every binder name any `forall`/`exists` in the arena introduces. One walk
/// over the arena's top-level nodes: a quantifier node carries its own binder
/// list, so no descent is needed.
fn arena_binder_names(solver: &Solver) -> ay_core::kani_compat::DetHashSet<String> {
    let mut names = ay_core::kani_compat::DetHashSet::default();
    for id in solver.terms().term_ids() {
        if let TermData::Forall(vars, _, _) | TermData::Exists(vars, _, _) = solver.terms().get(id)
        {
            names.extend(vars.iter().map(|(name, _)| name.clone()));
        }
    }
    names
}

/// Does `term`'s DAG mention a variable some quantifier binds (by name)?  A raw
/// application with such an argument cannot be pinned: instantiating its
/// enclosing quantifier yields applications at points no pin covers.  A `Var`
/// no binder ever bound is a declared constant and pins exactly.
fn term_mentions_binder_var(
    solver: &Solver,
    term: TermId,
    binder_names: &ay_core::kani_compat::DetHashSet<String>,
) -> bool {
    let mut seen = ay_core::kani_compat::DetHashSet::default();
    let mut stack = vec![term];
    while let Some(current) = stack.pop() {
        if !seen.insert(current) {
            continue;
        }
        match solver.terms().get(current) {
            TermData::Var(name, _) => {
                if binder_names.contains(name) {
                    return true;
                }
            }
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, t, e) => stack.extend([*c, *t, *e]),
            TermData::Let(bindings, body) => {
                stack.extend(bindings.iter().map(|(_, value)| *value));
                stack.push(*body);
            }
            TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                stack.push(*body);
                stack.extend(triggers.iter().flatten().copied());
            }
            TermData::Const(_) => {}
            _ => return true,
        }
    }
    false
}

#[cfg(test)]
#[path = "assertions/native_bv_source_surface_tests.rs"]
mod native_bv_source_surface_tests;

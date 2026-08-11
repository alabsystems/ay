// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Arithmetic optimization objectives: `maximize` / `minimize`.
//!
//! This is the native-API surface for AY's executor-level objective optimizer
//! (`(maximize ...)` / `(minimize ...)`). An objective is a numeric (Int / Real
//! / BitVec) term to drive to its extreme subject to the hard assertions.
//!
//! ## Usage
//!
//! ```
//! use ay_dpll::api::{Logic, Solver, Sort};
//! use num_rational::BigRational;
//! use num_traits::FromPrimitive;
//!
//! let mut solver = Solver::try_new(Logic::QfLia).unwrap();
//! let x = solver.declare_const("x", Sort::Int);
//! let zero = solver.int_const(0);
//! let ten = solver.int_const(10);
//! // 0 <= x <= 10
//! let lo = solver.try_ge(x, zero).unwrap();
//! let hi = solver.try_le(x, ten).unwrap();
//! solver.try_assert_term(lo).unwrap();
//! solver.try_assert_term(hi).unwrap();
//! let obj = solver.maximize(x);
//! assert!(solver.optimize_check().is_sat());
//! assert_eq!(
//!     solver.get_objective_value(obj).unwrap().as_finite().cloned(),
//!     Some(BigRational::from_i64(10).unwrap())
//! );
//! ```
//!
//! ## Relationship to MaxSMT (soft constraints)
//!
//! Objectives and soft constraints (`assert_soft`) are SEPARATE optimization
//! mechanisms. [`optimize_check`](Solver::optimize_check) optimizes registered
//! ARITHMETIC objectives; [`check_sat_max`](Solver::check_sat_max) optimizes a
//! pure API-owned soft set. AY does not yet jointly optimize both classes, so
//! `optimize_check` fails closed with `Unknown(Unsupported)` whenever API softs
//! are registered instead of silently discarding them.

use ay_core::time::Instant;
use ay_core::Sort;
use ay_frontend::{Command, Objective, ObjectiveDirection};

use crate::api::types::{
    NativeReplayEventKind, ObjectiveValue, SolveResult, SolverError, Term, VerifiedSolveResult,
};
use crate::api::Solver;
use crate::executor::optimization::ObjectiveOutcome;

impl Solver {
    /// Register a `maximize` objective on the term `term`.
    ///
    /// Returns the objective's index (its position in declaration order), which
    /// later identifies it for [`get_objective_value`](Self::get_objective_value).
    /// The term must be numeric (Int / Real / BitVec); a non-numeric sort is
    /// accepted here but rejected at [`optimize_check`](Self::optimize_check)
    /// time, mirroring the SMT-LIB `(maximize ...)` flow.
    pub fn maximize(&mut self, term: Term) -> usize {
        self.try_maximize(term)
            .unwrap_or_else(|error| panic!("{error}"))
    }

    /// Fallible variant of [`maximize`](Self::maximize).
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_maximize(&mut self, term: Term) -> Result<usize, SolverError> {
        self.register_objective(term, ObjectiveDirection::Maximize)
    }

    /// Register a `minimize` objective on the term `term`.
    ///
    /// Returns the objective's index. See [`maximize`](Self::maximize).
    pub fn minimize(&mut self, term: Term) -> usize {
        self.try_minimize(term)
            .unwrap_or_else(|error| panic!("{error}"))
    }

    /// Fallible variant of [`minimize`](Self::minimize).
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_minimize(&mut self, term: Term) -> Result<usize, SolverError> {
        self.register_objective(term, ObjectiveDirection::Minimize)
    }

    /// Shared registration: push an objective onto the executor context and
    /// return its index (the new declaration-order position).
    fn register_objective(
        &mut self,
        term: Term,
        direction: ObjectiveDirection,
    ) -> Result<usize, SolverError> {
        if let Some(message) = self
            .executor
            .array_ext_witness_registration_error(&[term.0])
        {
            return Err(SolverError::InvalidArgument {
                operation: "register_objective",
                message,
            });
        }
        self.executor.note_api_optimization_mutation();
        let ctx = self.executor.context_mut();
        let idx = ctx.objectives().len();
        ctx.add_objective(Objective {
            direction,
            term: term.0,
        });
        Ok(idx)
    }

    /// Return the number of registered optimization objectives.
    #[must_use]
    pub fn num_objectives(&self) -> usize {
        self.executor.context().objectives().len()
    }

    /// Solve, optimizing the registered objectives.
    ///
    /// When objectives are registered this runs the executor's objective
    /// optimizer (lexicographic by default; `box` / `pareto` via the
    /// `opt.priority` option), exactly as a `(check-sat)` would for a script that
    /// contains `(maximize ...)` / `(minimize ...)`. When NO objectives are
    /// registered this is equivalent to [`check_sat`](Self::check_sat).
    ///
    /// After a SAT result, read each objective's optimum with
    /// [`get_objective_value`](Self::get_objective_value).
    ///
    /// Returns a [`VerifiedSolveResult`]: `Sat` if the hard constraints are
    /// satisfiable (and the optima are available), `Unsat` if not, `Unknown`
    /// otherwise.
    pub fn optimize_check(&mut self) -> VerifiedSolveResult {
        // Retire the preceding public result before command elaboration can
        // fail, while retaining only Pareto's intentional enumeration state.
        self.clear_last_solve_state(true, true);
        self.record_native_replay_event(NativeReplayEventKind::CheckSat);

        if !self.soft_constraints.is_empty() {
            // The executor context does not contain API-owned softs, so entering
            // its objective optimizer here would silently ignore them and make
            // the returned model value look like a joint optimum.
            self.executor
                .replace_last_result_with_unknown(crate::UnknownReason::Unsupported);
            self.last_unknown_reason = Some(crate::UnknownReason::Unsupported);
            return self.finish_verified_result(SolveResult::Unknown);
        }

        let deadline = self.timeout.map(|duration| Instant::now() + duration);
        if let Some(early) = self.preflight_check(deadline) {
            return early;
        }

        // Optimization performs many nested feasibility checks, so the native
        // API must install the same interrupt/deadline/memory and clause-budget
        // envelope as `check_sat` around the ENTIRE executor command. The
        // executor's own timeout alone does not carry Solver-level controls.
        self.install_solve_controls(deadline);

        // Drive the executor's `(check-sat)` dispatch, which routes to
        // `optimize_check_sat` because objectives are non-empty. This reuses the
        // SAME optimizer the SMT-LIB front end uses, so the optima here are
        // exactly the optima a `(check-sat)` + `(get-objectives)` would report.
        let exec_result = self.executor.execute(&Command::CheckSat);
        self.executor.clear_solve_controls();
        if let Err(e) = exec_result {
            self.record_executor_failure_unknown(&e);
            return self.finish_verified_result(SolveResult::Unknown);
        }

        let result = self
            .executor
            .last_result()
            .cloned()
            .unwrap_or(SolveResult::Unknown);
        if result == SolveResult::Unknown && self.last_unknown_reason.is_none() {
            self.classify_unknown_reason(deadline);
        }
        self.finish_verified_result(result)
    }

    /// Get the optimum value of objective `idx` after [`optimize_check`](Self::optimize_check).
    ///
    /// Returns `None` if `idx` is out of range, or if no scalar optimum is
    /// available (e.g. the last solve was not SAT, the objective could not be
    /// evaluated, its optimum is finite but UNATTAINED (`v + k·ε`,
    /// #opt-epsilon), or it follows a lexicographic predecessor with no
    /// attainable optimum).
    /// A finite optimum is returned as [`ObjectiveValue::Finite`]; an unbounded
    /// objective as [`ObjectiveValue::PosInfinity`] (maximize) /
    /// [`ObjectiveValue::NegInfinity`] (minimize).
    ///
    /// SOUNDNESS: the value is read from the SAME executor state that
    /// `(get-objectives)` formats, so it can never disagree with the SMT-LIB
    /// report; AY never fabricates an optimum.
    #[must_use]
    pub fn get_objective_value(&self, idx: usize) -> Option<ObjectiveValue> {
        self.executor.context().objectives().get(idx)?;
        match self.executor.objective_optimum(idx) {
            ObjectiveOutcome::Finite(r) => Some(ObjectiveValue::Finite(r)),
            // An UNATTAINED optimum (`v + k·ε`, #opt-epsilon) has no scalar
            // the native API could return without lying (the finite part is
            // NOT attained; z3py exposes an epsilon expression object here).
            // Phase A: honestly unavailable at this surface — strictly better
            // than the pre-#opt-epsilon whole-query `unknown`, never a
            // fabricated scalar. z3py-style epsilon exposure is a noted
            // follow-up.
            ObjectiveOutcome::Epsilon { .. } => None,
            ObjectiveOutcome::PosInfinity => Some(ObjectiveValue::PosInfinity),
            ObjectiveOutcome::NegInfinity => Some(ObjectiveValue::NegInfinity),
            ObjectiveOutcome::Unavailable => None,
        }
    }

    /// The sort of objective `idx`'s term, or `None` if `idx` is out of range.
    ///
    /// Useful for FFI callers that must build the optimum numeral in the right
    /// sort (Int vs Real vs BitVec).
    #[must_use]
    pub fn objective_sort(&self, idx: usize) -> Option<Sort> {
        let ctx = self.executor.context();
        let obj = ctx.objectives().get(idx)?;
        Some(ctx.terms.sort(obj.term).clone())
    }

    /// The objective term (the `(maximize ...)` / `(minimize ...)` argument) of
    /// objective `idx`, or `None` if `idx` is out of range.
    ///
    /// Returns the objective expression EXACTLY as registered — the raw term the
    /// caller handed to [`maximize`](Self::maximize) / [`minimize`](Self::minimize)
    /// (or that a parsed `(maximize ...)` produced). Used by the FFI
    /// `Z3_optimize_get_objectives` to surface the objective expressions.
    #[must_use]
    pub fn objective_term(&self, idx: usize) -> Option<Term> {
        let obj = self.executor.context().objectives().get(idx)?;
        Some(Term(obj.term))
    }

    /// The direction (`Maximize` / `Minimize`) of objective `idx`, or `None` if
    /// `idx` is out of range.
    #[must_use]
    pub fn objective_direction(&self, idx: usize) -> Option<ObjectiveDirection> {
        self.executor
            .context()
            .objectives()
            .get(idx)
            .map(|o| o.direction)
    }
}

#[cfg(test)]
mod tests {
    use crate::api::{Logic, ObjectiveValue, Solver};
    use ay_core::Sort;
    use num_rational::BigRational;
    use num_traits::FromPrimitive;

    fn rat(n: i64) -> BigRational {
        BigRational::from_i64(n).unwrap()
    }

    /// `(maximize x)` under `0 <= x <= 10` → optimum 10.
    #[test]
    fn maximize_int_bounded() {
        let mut s = Solver::try_new(Logic::QfLia).unwrap();
        let x = s.declare_const("x", Sort::Int);
        let zero = s.int_const(0);
        let ten = s.int_const(10);
        let lo = s.try_ge(x, zero).unwrap();
        let hi = s.try_le(x, ten).unwrap();
        s.try_assert_term(lo).unwrap();
        s.try_assert_term(hi).unwrap();
        let obj = s.maximize(x);
        assert_eq!(obj, 0);
        assert_eq!(s.num_objectives(), 1);
        assert!(s.optimize_check().is_sat());
        assert_eq!(
            s.get_objective_value(obj),
            Some(ObjectiveValue::Finite(rat(10)))
        );
    }

    /// `(minimize x)` under `3 <= x <= 100` → optimum 3.
    #[test]
    fn minimize_int_bounded() {
        let mut s = Solver::try_new(Logic::QfLia).unwrap();
        let x = s.declare_const("x", Sort::Int);
        let three = s.int_const(3);
        let hundred = s.int_const(100);
        let lo = s.try_ge(x, three).unwrap();
        let hi = s.try_le(x, hundred).unwrap();
        s.try_assert_term(lo).unwrap();
        s.try_assert_term(hi).unwrap();
        let obj = s.minimize(x);
        assert!(s.optimize_check().is_sat());
        assert_eq!(
            s.get_objective_value(obj),
            Some(ObjectiveValue::Finite(rat(3)))
        );
    }

    /// Two-objective lexicographic: maximize x then maximize y under
    /// `x + y <= 10, 0 <= x, 0 <= y`. Lex maximizes x first (=10) which forces
    /// y = 0.
    #[test]
    fn lex_two_objectives() {
        let mut s = Solver::try_new(Logic::QfLia).unwrap();
        let x = s.declare_const("x", Sort::Int);
        let y = s.declare_const("y", Sort::Int);
        let zero = s.int_const(0);
        let ten = s.int_const(10);
        let xy = s.try_add(x, y).unwrap();
        let sum_le = s.try_le(xy, ten).unwrap();
        let x_nn = s.try_ge(x, zero).unwrap();
        let y_nn = s.try_ge(y, zero).unwrap();
        s.try_assert_term(sum_le).unwrap();
        s.try_assert_term(x_nn).unwrap();
        s.try_assert_term(y_nn).unwrap();
        let ox = s.maximize(x);
        let oy = s.maximize(y);
        assert!(s.optimize_check().is_sat());
        assert_eq!(
            s.get_objective_value(ox),
            Some(ObjectiveValue::Finite(rat(10)))
        );
        assert_eq!(
            s.get_objective_value(oy),
            Some(ObjectiveValue::Finite(rat(0)))
        );
    }

    /// Lexicographic optimum commits are internal to one optimization query.
    /// They must not survive as hard assertions and constrain the next query.
    #[test]
    fn lex_two_objective_commits_do_not_leak_into_followup_solve() {
        let mut s = Solver::try_new(Logic::QfLia).unwrap();
        let x = s.declare_const("x", Sort::Int);
        let y = s.declare_const("y", Sort::Int);
        let zero = s.int_const(0);
        let ten = s.int_const(10);
        let bounds = [
            s.try_ge(x, zero).unwrap(),
            s.try_le(x, ten).unwrap(),
            s.try_ge(y, zero).unwrap(),
            s.try_le(y, ten).unwrap(),
        ];
        for bound in bounds {
            s.try_assert_term(bound).unwrap();
        }
        let original_assertions = s.assertions();
        let ox = s.maximize(x);
        let oy = s.maximize(y);

        let first = s.optimize_check();
        assert!(first.is_sat());
        assert!(first.was_model_validated());
        assert_eq!(s.assertions(), original_assertions);
        assert_eq!(
            s.get_objective_value(ox),
            Some(ObjectiveValue::Finite(rat(10)))
        );
        assert_eq!(
            s.get_objective_value(oy),
            Some(ObjectiveValue::Finite(rat(10)))
        );

        // The new hard constraint changes x's optimum. A leaked `x >= 10`
        // commit from the first solve would make this query falsely UNSAT.
        let x_is_zero = s.try_eq(x, zero).unwrap();
        s.try_assert_term(x_is_zero).unwrap();
        assert_eq!(s.assertions().len(), original_assertions.len() + 1);

        let second = s.optimize_check();
        assert!(second.is_sat());
        assert!(second.was_model_validated());
        assert_eq!(s.assertions().len(), original_assertions.len() + 1);
        assert_eq!(
            s.get_objective_value(ox),
            Some(ObjectiveValue::Finite(rat(0)))
        );
        assert_eq!(
            s.get_objective_value(oy),
            Some(ObjectiveValue::Finite(rat(10)))
        );
    }

    /// Unbounded Real maximize (only a lower bound on x) → +oo.
    ///
    /// AY detects unboundedness via the audited LRA simplex optimizer and
    /// reports `oo` (SAT). INT objectives take the same lane (LP relaxation +
    /// Meyer's theorem, #unbounded-oo); that case is covered by
    /// [`unbounded_int_is_pos_infinity`].
    #[test]
    fn unbounded_real_maximize_is_pos_infinity() {
        let mut s = Solver::try_new(Logic::QfLra).unwrap();
        let x = s.declare_const("x", Sort::Real);
        let zero_r = s.rational_const(0, 1);
        let lo = s.try_ge(x, zero_r).unwrap();
        s.try_assert_term(lo).unwrap();
        let obj = s.maximize(x);
        let r = s.optimize_check();
        assert!(r.is_sat(), "expected SAT, got {:?}", r.result());
        assert_eq!(
            s.get_objective_value(obj),
            Some(ObjectiveValue::PosInfinity)
        );
    }

    /// Unbounded INT maximize → SAT + +oo (#unbounded-oo), matching z3 and
    /// the Real twin above. The LP-relaxation probe proves unboundedness
    /// (faithful pure-conjunction polyhedron + integer-feasible point +
    /// rational recession ray, Meyer's theorem); a finite optimum is still
    /// NEVER fabricated — anything unprovable stays Unknown.
    #[test]
    fn unbounded_int_is_pos_infinity() {
        let mut s = Solver::try_new(Logic::QfLia).unwrap();
        let x = s.declare_const("x", Sort::Int);
        let zero = s.int_const(0);
        let lo = s.try_ge(x, zero).unwrap();
        s.try_assert_term(lo).unwrap();
        let obj = s.maximize(x);
        let r = s.optimize_check();
        assert!(r.is_sat(), "expected SAT, got {:?}", r.result());
        assert_eq!(
            s.get_objective_value(obj),
            Some(ObjectiveValue::PosInfinity)
        );
    }

    /// Out-of-range index → None.
    #[test]
    fn objective_value_out_of_range() {
        let mut s = Solver::try_new(Logic::QfLia).unwrap();
        let x = s.declare_const("x", Sort::Int);
        let zero = s.int_const(0);
        let ten = s.int_const(10);
        let lo = s.try_ge(x, zero).unwrap();
        let hi = s.try_le(x, ten).unwrap();
        s.try_assert_term(lo).unwrap();
        s.try_assert_term(hi).unwrap();
        let _ = s.maximize(x);
        assert!(s.optimize_check().is_sat());
        assert_eq!(s.get_objective_value(5), None);
    }

    /// Real minimize over `x >= 5/2` → optimum 5/2 (exact fraction).
    #[test]
    fn minimize_real_fraction() {
        let mut s = Solver::try_new(Logic::QfLra).unwrap();
        let x = s.declare_const("x", Sort::Real);
        let half5 = s.rational_const(5, 2);
        let lo = s.try_ge(x, half5).unwrap();
        s.try_assert_term(lo).unwrap();
        let obj = s.minimize(x);
        assert!(s.optimize_check().is_sat());
        assert_eq!(
            s.get_objective_value(obj),
            Some(ObjectiveValue::Finite(BigRational::new(
                num_bigint::BigInt::from(5),
                num_bigint::BigInt::from(2)
            )))
        );
    }

    /// `objective_sort` reports the registered objective's sort.
    #[test]
    fn objective_sort_reports_sort() {
        let mut s = Solver::try_new(Logic::QfLia).unwrap();
        let x = s.declare_const("x", Sort::Int);
        let obj = s.maximize(x);
        assert_eq!(s.objective_sort(obj), Some(Sort::Int));
        assert_eq!(s.objective_sort(1), None);
    }

    /// Registering an objective changes the decision problem. A feasibility
    /// model from an earlier plain check is not an optimum and must become
    /// unavailable immediately, before the first optimizing query.
    #[test]
    fn objective_registration_retires_stale_feasibility_model_and_value() {
        let mut s = Solver::try_new(Logic::QfLia).unwrap();
        let x = s.declare_const("x", Sort::Int);
        let zero = s.int_const(0);
        let ten = s.int_const(10);
        let lo = s.try_ge(x, zero).unwrap();
        let hi = s.try_le(x, ten).unwrap();
        s.try_assert_term(lo).unwrap();
        s.try_assert_term(hi).unwrap();

        assert!(s.check_sat().is_sat());
        assert!(s.model().is_some());

        let objective = s.maximize(x);
        assert!(s.executor.last_result().is_none());
        assert!(s.model().is_none());
        assert_eq!(s.get_objective_value(objective), None);
        assert!(s.executor.take_sat_certificate().is_none());
    }

    /// A native plain `check_sat` is intentionally a feasibility query even
    /// when objectives are registered. Its arbitrary satisfying value must
    /// never be exposed as an optimum, either before the first optimization or
    /// after a previously admitted optimization.
    #[test]
    fn plain_check_never_publishes_or_republishes_objective_values() {
        let mut s = Solver::try_new(Logic::QfLia).unwrap();
        let x = s.declare_const("x", Sort::Int);
        let zero = s.int_const(0);
        let ten = s.int_const(10);
        for bound in [s.try_ge(x, zero).unwrap(), s.try_le(x, ten).unwrap()] {
            s.try_assert_term(bound).unwrap();
        }
        let objective = s.maximize(x);

        assert!(s.check_sat().is_sat());
        assert!(s.model().is_some());
        assert_eq!(s.get_objective_value(objective), None);

        assert!(s.optimize_check().is_sat());
        assert_eq!(
            s.get_objective_value(objective),
            Some(ObjectiveValue::Finite(rat(10)))
        );

        assert!(s.check_sat().is_sat());
        assert!(s.model().is_some());
        assert_eq!(s.get_objective_value(objective), None);
    }

    /// A finite lex optimum belongs to the final emitted model. Simulate a
    /// post-emission repair that changes the objective and ensure the exact
    /// accounting gate revokes the SAT certificate, model, and value.
    #[test]
    fn post_emission_objective_drift_is_honest_unknown() {
        let mut s = Solver::try_new(Logic::QfLia).unwrap();
        let x = s.declare_const("x", Sort::Int);
        let zero = s.int_const(0);
        let ten = s.int_const(10);
        for bound in [s.try_ge(x, zero).unwrap(), s.try_le(x, ten).unwrap()] {
            s.try_assert_term(bound).unwrap();
        }
        let objective = s.maximize(x);
        s.executor
            .force_optimization_post_emit_objective_flip_for_test();

        let result = s.optimize_check();
        assert!(result.is_unknown());
        assert_eq!(
            s.unknown_reason(),
            Some(crate::UnknownReason::InternalError)
        );
        assert!(s.model().is_none());
        assert_eq!(s.get_objective_value(objective), None);
        assert!(s.executor.take_sat_certificate().is_none());
        assert!(s.executor.finite_objective_values.is_empty());
        assert!(s.executor.objective_certificates.is_empty());
    }

    /// Pareto enumeration is keyed to the complete objective list. Adding an
    /// objective must reset it without pretending the hard assertion stack was
    /// mutated or switching to incremental assertion mode.
    #[test]
    fn objective_registration_resets_pareto_without_incremental_side_effect() {
        let mut s = Solver::try_new(Logic::QfLia).unwrap();
        s.set_option(":opt.priority", "pareto");
        let x = s.declare_const("x", Sort::Int);
        let y = s.declare_const("y", Sort::Int);
        let zero = s.int_const(0);
        let one = s.int_const(1);
        for term in [
            s.try_ge(x, zero).unwrap(),
            s.try_le(x, one).unwrap(),
            s.try_ge(y, zero).unwrap(),
            s.try_le(y, one).unwrap(),
        ] {
            s.try_assert_term(term).unwrap();
        }
        s.maximize(x);
        assert!(s.optimize_check().is_sat());
        assert!(s.executor.pareto_state.is_some());
        let incremental_before = s.executor.incremental_mode;

        let y_objective = s.maximize(y);
        assert!(s.executor.pareto_state.is_none());
        assert!(s.executor.last_result().is_none());
        assert_eq!(s.get_objective_value(y_objective), None);
        assert_eq!(s.executor.incremental_mode, incremental_before);
    }

    /// Objective handles identify declarations, not terms. In box mode the two
    /// declarations below have different independent optima even though their
    /// term is identical. A term-keyed outcome cache aliases them to one value.
    #[test]
    fn duplicate_term_box_objectives_keep_distinct_native_values() {
        let mut s = Solver::try_new(Logic::QfLia).unwrap();
        s.set_option(":opt.priority", "box");
        let x = s.declare_const("x", Sort::Int);
        let zero = s.int_const(0);
        let ten = s.int_const(10);
        let lo = s.try_ge(x, zero).unwrap();
        let hi = s.try_le(x, ten).unwrap();
        s.try_assert_term(lo).unwrap();
        s.try_assert_term(hi).unwrap();

        let maximize_x = s.maximize(x);
        let minimize_x = s.minimize(x);
        let first = s.optimize_check();
        assert!(first.is_sat());
        assert!(first.was_model_validated());
        assert_eq!(
            s.get_objective_value(maximize_x),
            Some(ObjectiveValue::Finite(rat(10)))
        );
        assert_eq!(
            s.get_objective_value(minimize_x),
            Some(ObjectiveValue::Finite(rat(0)))
        );

        // Mutation retires both indexed outcomes; a re-solve publishes a fresh
        // pair and cannot retain either value from the preceding problem.
        let four = s.int_const(4);
        let x_is_four = s.try_eq(x, four).unwrap();
        s.try_assert_term(x_is_four).unwrap();
        assert_eq!(s.get_objective_value(maximize_x), None);
        assert_eq!(s.get_objective_value(minimize_x), None);
        assert!(s.optimize_check().is_sat());
        assert_eq!(
            s.get_objective_value(maximize_x),
            Some(ObjectiveValue::Finite(rat(4)))
        );
        assert_eq!(
            s.get_objective_value(minimize_x),
            Some(ObjectiveValue::Finite(rat(4)))
        );
    }

    /// Duplicate unbounded objectives must retain their own direction. A
    /// term-keyed map overwrites `+oo` with `-oo` for both handles.
    #[test]
    fn duplicate_term_box_objectives_keep_distinct_infinities() {
        let mut s = Solver::try_new(Logic::QfLra).unwrap();
        s.set_option(":opt.priority", "box");
        let x = s.declare_const("x", Sort::Real);
        let maximize_x = s.maximize(x);
        let minimize_x = s.minimize(x);

        let result = s.optimize_check();
        assert!(result.is_sat(), "expected SAT, got {:?}", result.result());
        assert!(result.was_model_validated());
        assert_eq!(
            s.get_objective_value(maximize_x),
            Some(ObjectiveValue::PosInfinity)
        );
        assert_eq!(
            s.get_objective_value(minimize_x),
            Some(ObjectiveValue::NegInfinity)
        );
    }

    /// In lex mode an unbounded prefix has no attainable value under which a
    /// later objective can be optimized. Z3 exposes an interval for the suffix;
    /// AY's scalar API reports it as unavailable instead of inventing an
    /// independent `-oo` result for the second declaration.
    #[test]
    fn unbounded_lex_prefix_makes_later_objectives_unavailable() {
        let mut s = Solver::try_new(Logic::QfLra).unwrap();
        let x = s.declare_const("x", Sort::Real);
        let maximize_x = s.maximize(x);
        let minimize_x = s.minimize(x);

        let first = s.optimize_check();
        assert!(first.is_sat(), "expected SAT, got {:?}", first.result());
        assert!(first.was_model_validated());
        assert_eq!(
            s.get_objective_value(maximize_x),
            Some(ObjectiveValue::PosInfinity)
        );
        assert_eq!(s.get_objective_value(minimize_x), None);

        // Tightening the problem retires the unavailable marker. With x <= 5,
        // lex maximize pins x=5 and the later minimize has the exact value 5.
        let five = s.rational_const(5, 1);
        let upper = s.try_le(x, five).unwrap();
        s.try_assert_term(upper).unwrap();
        assert_eq!(s.get_objective_value(maximize_x), None);
        assert_eq!(s.get_objective_value(minimize_x), None);
        let second = s.optimize_check();
        assert!(second.is_sat());
        assert_eq!(
            s.get_objective_value(maximize_x),
            Some(ObjectiveValue::Finite(rat(5)))
        );
        assert_eq!(
            s.get_objective_value(minimize_x),
            Some(ObjectiveValue::Finite(rat(5)))
        );
    }
}

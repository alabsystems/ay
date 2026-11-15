// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Existing tactic options are restrictions/configuration, never grants.
//! Contracts: Z3 5.3.3 api_tactic.cpp, tactical.cpp, rewriter_params.hpp.

use super::tactics::{Tactic, TacticFailure};
use ay_core::original_query::CountedAdmissionError;
use ay_core::term::TermConstructionAdmission;
use std::cell::Cell;
use std::sync::Mutex;
use std::time::Instant;

/// Type retained from the real parameter setter/parser, not inferred from a
/// symbol's printed spelling (the symbol `true` is not a Boolean parameter).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TacticParameterValue {
    Bool(bool),
    UInt(u32),
    Unsupported,
}

/// The supported simplifier settings. Explicit UINT_MAX is retained so a later
/// update can remove a local setting without ever widening the original owner.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct TacticParameters {
    pub(crate) polynomial: super::polynomial_parameters::PolynomialParameters,
    pub(crate) max_steps: Option<u32>,
    pub(crate) max_memory: Option<u32>,
    pub(crate) elim_and: Option<bool>,
    pub(crate) max_power_expansion: Option<u32>,
}
impl TacticParameters {
    pub fn set(&mut self, name: &str, value: TacticParameterValue) -> Result<(), TacticFailure> {
        if super::polynomial_parameters::PolynomialParameters::recognizes(name) {
            return self.polynomial.set(name, value);
        }
        match (name.strip_prefix("rewriter.").unwrap_or(name), value) {
            ("max_steps", TacticParameterValue::UInt(n)) => self.max_steps = Some(n),
            ("max_memory", TacticParameterValue::UInt(n)) => self.max_memory = Some(n),
            ("elim_and", TacticParameterValue::Bool(value)) => self.elim_and = Some(value),
            _ => {
                return Err(TacticFailure::new(
                    "unsupported tactic parameter name or type",
                ))
            }
        }
        Ok(())
    }
    pub(crate) fn is_empty(self) -> bool {
        self == Self::default()
    }
    /// Stored using-params options override later updates, as upstream append.
    pub(crate) fn over(self, earlier: Self) -> Self {
        Self {
            polynomial: self.polynomial.over(earlier.polynomial),
            max_steps: self.max_steps.or(earlier.max_steps),
            max_memory: self.max_memory.or(earlier.max_memory),
            elim_and: self.elim_and.or(earlier.elim_and),
            max_power_expansion: self.max_power_expansion.or(earlier.max_power_expansion),
        }
    }
    /// Carry an embedding's actual global sequence-rewriter setting. Z3's
    /// local tactic descriptor set omits this module parameter, so `set`
    /// intentionally rejects it. This supplies configuration, never admission.
    pub fn with_global_sequence_power(mut self, maximum: u32) -> Self {
        self.max_power_expansion = Some(maximum);
        self
    }
    pub fn with_global_polynomial(mut self, global: super::PolynomialParameters) -> Self {
        self.polynomial = self.polynomial.over(global);
        self
    }
}

/// Shared C tactic identity. Configuration updates hold no lock across an
/// original-owner callback. The expression itself is immutable.
#[derive(Debug)]
pub struct TacticInstance {
    pub(crate) body: Tactic,
    configured: Mutex<TacticParameters>,
}
impl TacticInstance {
    pub fn new(body: Tactic) -> Self {
        Self {
            body,
            configured: Mutex::new(TacticParameters::default()),
        }
    }
    pub(crate) fn configured(&self) -> Result<TacticParameters, TacticFailure> {
        self.configured
            .lock()
            .map(|p| *p)
            .map_err(|_| TacticFailure::new("tactic configuration owner unavailable"))
    }
    pub(crate) fn install(&self, params: TacticParameters) -> Result<(), TacticFailure> {
        let mut current = self
            .configured
            .lock()
            .map_err(|_| TacticFailure::new("tactic configuration owner unavailable"))?;
        *current = params;
        Ok(())
    }
}

thread_local! {static CURRENT:Cell<TacticParameters>=Cell::new(TacticParameters::default());}
pub(super) struct Installed(TacticParameters);
impl Drop for Installed {
    fn drop(&mut self) {
        CURRENT.with(|p| p.set(self.0));
    }
}
pub(super) fn current() -> TacticParameters {
    CURRENT.with(Cell::get)
}
pub(super) fn install(params: TacticParameters) -> Installed {
    Installed(CURRENT.with(|p| {
        let old = p.get();
        p.set(params.over(old));
        old
    }))
}

/// A local checkpoint limit. Every successful debit still goes to the SAME
/// original owner. Local refusal cannot revive or hide an original refusal.
/// Memory checks current native pressure plus the next prepaid allocation.
/// The original owner's cumulative storage accounting remains unchanged.
/// This is a checkpoint restriction, not a kernel reservation.
pub(super) struct Restricted<'a> {
    original: &'a dyn TermConstructionAdmission,
    end: Option<Instant>,
    memory: Option<usize>,
    refused: Cell<Option<CountedAdmissionError>>,
}
impl<'a> Restricted<'a> {
    pub(super) fn new(
        original: &'a dyn TermConstructionAdmission,
        end: Option<Instant>,
        memory: Option<u32>,
    ) -> Result<Self, TacticFailure> {
        let memory = match memory.filter(|v| *v != u32::MAX) {
            Some(mib) => Some(
                usize::try_from(mib)
                    .ok()
                    .and_then(|m| m.checked_mul(1 << 20))
                    .ok_or_else(|| TacticFailure::new("tactic memory limit overflow"))?,
            ),
            None => None,
        };
        Ok(Self {
            original,
            end,
            memory,
            refused: Cell::new(None),
        })
    }
    fn local(&self, error: CountedAdmissionError) -> CountedAdmissionError {
        if let Some(first) = self.refused.get() {
            first
        } else {
            self.refused.set(Some(error));
            error
        }
    }
    pub(super) fn settle<T>(&self, result: Result<T, TacticFailure>) -> Result<T, TacticFailure> {
        self.original
            .check()
            .map_err(|_| TacticFailure::new("original tactic owner stopped"))?;
        if let Err(failure) = &result {
            if failure.local_limit.is_some() {
                return result;
            }
        }
        if self.refused.get().is_none() && result.is_ok() {
            if self.check().is_err() {
                self.original
                    .check()
                    .map_err(|_| TacticFailure::new("original tactic owner stopped"))?;
                if self.refused.get().is_none() {
                    return Err(TacticFailure::new("original tactic checkpoint refused"));
                }
            }
        }
        if let Some(reason) = self.refused.get() {
            let kind = if matches!(
                reason,
                CountedAdmissionError::Memory | CountedAdmissionError::StorageExhausted
            ) {
                crate::api::TacticLimitKind::Memory
            } else {
                crate::api::TacticLimitKind::Deadline
            };
            return Err(TacticFailure::limited(kind));
        }
        result
    }
    pub(super) fn expired(&self) -> bool {
        self.end.is_some_and(|e| Instant::now() >= e)
    }
}
impl TermConstructionAdmission for Restricted<'_> {
    fn admit(&self, work: usize, bytes: usize) -> Result<(), CountedAdmissionError> {
        self.original.check()?;
        if let Some(first) = self.refused.get() {
            return Err(first);
        }
        if self.expired() {
            return Err(self.local(CountedAdmissionError::WorkExhausted));
        }
        if let Some(limit) = self.memory {
            let observed = ay_sys::current_memory_pressure_bytes();
            if observed == 0
                || observed
                    .checked_add(bytes)
                    .is_none_or(|total| total > limit)
            {
                return Err(self.local(CountedAdmissionError::Memory));
            }
        }
        self.original.admit(work, bytes)?;
        if self.expired() {
            return Err(self.local(CountedAdmissionError::WorkExhausted));
        }
        if let Some(limit) = self.memory {
            let observed = ay_sys::current_memory_pressure_bytes();
            if observed == 0
                || observed
                    .checked_add(bytes)
                    .is_none_or(|total| total > limit)
            {
                return Err(self.local(CountedAdmissionError::Memory));
            }
        }
        Ok(())
    }
    fn refuse(&self, error: CountedAdmissionError) -> CountedAdmissionError {
        if let Some(first) = self.refused.get() {
            first
        } else {
            self.original.refuse(error)
        }
    }
}

/// Rewrite steps have their own documented native unit; metadata and copies
/// are additionally paid to the original owner and never hidden by this cap.
pub(super) struct Steps {
    used: usize,
    limit: Option<usize>,
}
impl Steps {
    pub(super) fn new(limit: Option<u32>) -> Self {
        Self {
            used: 0,
            limit: limit.filter(|v| *v != u32::MAX).map(|v| v as usize),
        }
    }
    pub(super) fn visit(
        &mut self,
        owner: &dyn TermConstructionAdmission,
    ) -> Result<(), TacticFailure> {
        owner
            .check()
            .map_err(|_| TacticFailure::new("original tactic owner stopped"))?;
        let next = self
            .used
            .checked_add(1)
            .ok_or_else(|| TacticFailure::new("tactic rewrite step overflow"))?;
        if self.limit.is_some_and(|limit| next > limit) {
            return Err(TacticFailure::limited(crate::api::TacticLimitKind::Work));
        }
        owner
            .admit(1, 0)
            .map_err(|_| TacticFailure::new("original tactic owner stopped"))?;
        self.used = next;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::api::Goal;
    use ay_core::original_query::{CountedAdmission, FiniteAdmissionGrant};
    use ay_core::{Sort, Symbol, TermData, TermId, TermStore};
    use std::sync::Arc;

    fn original() -> CountedAdmission {
        CountedAdmission::new(
            FiniteAdmissionGrant::new(1 << 20, 16 << 20),
            None,
            Arc::new(|| false),
        )
        .unwrap()
    }
    fn expression() -> (TermStore, [TermId; 3], TermId) {
        let mut terms = TermStore::new();
        let vars = [
            terms.mk_var("p", Sort::Bool),
            terms.mk_var("q", Sort::Bool),
            terms.mk_var("r", Sort::Bool),
        ];
        let and = terms.mk_app(Symbol::Named("and".into()), &vars[..2], Sort::Bool);
        let root = terms.mk_app(Symbol::Named("or".into()), [and, vars[2]], Sort::Bool);
        (terms, vars, root)
    }
    struct View {
        vars: [TermId; 3],
        mask: u8,
    }
    impl ay_model_check::ModelView for View {
        fn leaf_value(&self, id: TermId) -> Option<ay_model_check::ModelValue> {
            self.vars
                .iter()
                .position(|v| *v == id)
                .map(|n| ay_model_check::ModelValue::Bool(self.mask & (1 << n) != 0))
        }
    }
    fn params(name: &str, value: TacticParameterValue) -> TacticParameters {
        let mut result = TacticParameters::default();
        result.set(name, value).unwrap();
        result
    }

    #[test]
    fn tactic_parameters_elim_and_changes_real_nested_formula_and_preserves_every_model() {
        let (mut terms, vars, root) = expression();
        let tactic = Tactic::WithParams(
            Box::new(Tactic::Simplify),
            params("elim_and", TacticParameterValue::Bool(true)),
        );
        let result = tactic
            .apply_goals_admitted(&mut terms, Goal::root(vec![root]), &original())
            .unwrap();
        assert_eq!(result.len(), 1);
        assert_eq!(result[0].formulas.len(), 1);
        let rewritten = result[0].formulas[0];
        assert_ne!(rewritten, root);
        let mut todo = vec![rewritten];
        while let Some(id) = todo.pop() {
            match terms.get(id) {
                TermData::App(Symbol::Named(name), args) => {
                    assert_ne!(name, "and");
                    todo.extend(args);
                }
                TermData::Not(child) => todo.push(*child),
                _ => {}
            }
        }
        for mask in 0..8 {
            let view = View { vars, mask };
            let eval = ay_model_check::Evaluator::new(&terms, &view);
            let before = eval.evaluate(root);
            let after = eval.evaluate(rewritten);
            assert!(
                matches!((&before,&after),(ay_model_check::EvalOutcome::Value(ay_model_check::ModelValue::Bool(a)),ay_model_check::EvalOutcome::Value(ay_model_check::ModelValue::Bool(b))) if a==b),
                "{mask}: {before:?} {after:?}"
            );
        }
    }

    #[test]
    fn tactic_parameters_zero_steps_refuses_without_term_growth_and_or_else_can_recover() {
        let (mut terms, _, root) = expression();
        let stamp = terms.snapshot_stamp();
        let owner = original();
        let zero = Tactic::WithParams(
            Box::new(Tactic::Simplify),
            params("max_steps", TacticParameterValue::UInt(0)),
        );
        assert!(zero
            .apply_goals_admitted(&mut terms, Goal::root(vec![root]), &owner)
            .is_err());
        assert_eq!(stamp, terms.snapshot_stamp());
        assert!(owner.check().is_ok());
        let recovered = zero
            .or_else(Tactic::Skip)
            .apply_goals_admitted(&mut terms, Goal::root(vec![root]), &owner)
            .unwrap();
        assert_eq!(recovered[0].formulas, vec![root]);
    }

    #[test]
    fn tactic_parameters_shared_update_persists_and_stored_settings_override_later_updates() {
        let (mut terms, _, root) = expression();
        let shared = Tactic::Shared(Arc::new(TacticInstance::new(Tactic::Simplify)));
        let owner = original();
        shared
            .update_parameters(params("max_steps", TacticParameterValue::UInt(0)), &owner)
            .unwrap();
        assert!(shared
            .apply_goals_admitted(&mut terms, Goal::root(vec![root]), &original())
            .is_err());
        let stored = Tactic::WithParams(
            Box::new(shared.clone()),
            params("max_steps", TacticParameterValue::UInt(u32::MAX)),
        );
        stored
            .update_parameters(params("max_steps", TacticParameterValue::UInt(0)), &owner)
            .unwrap();
        assert!(stored
            .apply_goals_admitted(&mut terms, Goal::root(vec![root]), &owner)
            .is_ok());
        assert!(shared
            .apply_goals_admitted(&mut terms, Goal::root(vec![root]), &original())
            .is_ok());
    }

    #[test]
    fn tactic_parameters_reject_wrong_types_unknown_keys_and_unsupported_primitive() {
        assert!(TacticParameters::default()
            .set("elim_and", TacticParameterValue::Unsupported)
            .is_err());
        assert!(TacticParameters::default()
            .set("max_steps", TacticParameterValue::Bool(true))
            .is_err());
        assert!(TacticParameters::default()
            .set("unknown_directive", TacticParameterValue::UInt(1))
            .is_err());
        let owner = original();
        assert!(Tactic::FieldToBv
            .validate_parameters(params("max_steps", TacticParameterValue::UInt(1)), &owner)
            .is_err());
    }

    #[test]
    fn tactic_parameters_local_expiry_and_memory_refusal_never_clear_an_original_stop() {
        let owner = original();
        let expired = Restricted::new(&owner, Some(Instant::now()), None).unwrap();
        assert!(expired.check().is_err());
        assert!(owner.check().is_ok());
        let memory = Restricted::new(&owner, None, Some(0)).unwrap();
        assert!(memory.admit(1, 1).is_err());
        assert!(owner.check().is_ok());
        owner.refuse(CountedAdmissionError::WorkExhausted);
        for ms in [0, u32::MAX] {
            let mut terms = TermStore::new();
            let root = terms.mk_bool(true);
            assert!(Tactic::TryFor(Box::new(Tactic::Skip), ms)
                .apply_goals_admitted(&mut terms, Goal::root(vec![root]), &owner)
                .is_err());
        }
        assert!(owner.check().is_err());
    }

    #[test]
    fn tactic_parameters_zero_and_max_timer_are_disabled_without_hiding_parent_restrictions() {
        let owner = original();
        let mut terms = TermStore::new();
        let root = terms.mk_bool(true);
        for ms in [0, u32::MAX] {
            assert!(Tactic::TryFor(Box::new(Tactic::Skip), ms)
                .apply_goals_admitted(&mut terms, Goal::root(vec![root]), &owner)
                .is_ok());
        }
    }
}

#[cfg(test)]
mod typed_limit_tests {
    use super::*;
    use crate::api::{Goal, Logic, Solver, SolverError, TacticLimitKind};
    use ay_core::original_query::{CountedAdmission, FiniteAdmissionGrant};
    use ay_core::{Sort, Symbol, TermStore};
    use std::sync::Arc;
    fn original() -> CountedAdmission {
        CountedAdmission::new(
            FiniteAdmissionGrant::new(1 << 20, 16 << 20),
            None,
            Arc::new(|| false),
        )
        .unwrap()
    }
    #[test]
    fn tactic_parameters_local_causes_survive_api_conversion_without_poisoning_original() {
        let mut solver = Solver::new(Logic::All);
        let p = solver.bool_var("local_p");
        let q = solver.bool_var("local_q");
        let root = solver.and(p, q);
        let mut params = TacticParameters::default();
        params
            .set("max_steps", TacticParameterValue::UInt(0))
            .unwrap();
        let error = solver
            .apply_tactic_subgoals_converted(
                &Tactic::WithParams(Box::new(Tactic::Simplify), params),
                &[root],
                0,
                None,
            )
            .unwrap_err();
        assert!(matches!(
            error,
            SolverError::TacticLimit(TacticLimitKind::Work)
        ));
        assert!(solver
            .apply_tactic_subgoals_converted(&Tactic::Skip, &[root], 0, None)
            .is_ok());
        let owner = original();
        let expired = Restricted::new(&owner, Some(Instant::now()), None).unwrap();
        assert!(expired.check().is_err());
        assert!(matches!(
            expired
                .settle::<()>(Err(TacticFailure::new("body failed")))
                .unwrap_err()
                .into_solver_error(),
            SolverError::TacticLimit(TacticLimitKind::Deadline)
        ));
        assert!(owner.check().is_ok());
        let memory = Restricted::new(&owner, None, Some(0)).unwrap();
        assert!(memory.check().is_err());
        assert!(matches!(
            memory
                .settle::<()>(Err(TacticFailure::new("body failed")))
                .unwrap_err()
                .into_solver_error(),
            SolverError::TacticLimit(TacticLimitKind::Memory)
        ));
        owner.refuse(CountedAdmissionError::WorkExhausted);
        assert!(expired
            .settle::<()>(Ok(()))
            .unwrap_err()
            .local_limit
            .is_none());
    }
    #[test]
    fn tactic_parameters_timeout_overflow_is_refused_without_truncation() {
        let ast = ay_frontend::ApplyTactic::TryFor(
            Box::new(ay_frontend::ApplyTactic::Skip),
            u64::from(u32::MAX) + 1,
        );
        let owner = original();
        assert!(Tactic::prepare_apply(&ast, &owner).is_err());
        let mut terms = TermStore::new();
        let p = terms.mk_var("p", Sort::Bool);
        assert!(Tactic::from_apply(&ast)
            .apply_goals_admitted(&mut terms, Goal::root(vec![p]), &owner)
            .is_err());
    }
    #[test]
    fn tactic_parameters_prepared_controls_are_real_and_original_counter_is_shared() {
        let owner = original();
        let ast = ay_frontend::ApplyTactic::UsingParams(
            Box::new(ay_frontend::ApplyTactic::Simplify),
            vec![("max_steps".into(), ay_frontend::ParamValue::Int(0))],
        );
        let prepared = Tactic::prepare_apply(&ast, &owner).unwrap();
        let mut terms = TermStore::new();
        let p = terms.mk_var("p", Sort::Bool);
        let q = terms.mk_var("q", Sort::Bool);
        let root = terms.mk_app(Symbol::Named("or".into()), [p, q], Sort::Bool);
        let failure = prepared
            .get()
            .unwrap()
            .apply_goals_admitted(&mut terms, Goal::root(vec![root]), &owner)
            .unwrap_err();
        assert_eq!(failure.local_limit, Some(TacticLimitKind::Work));
        assert!(owner.check().is_ok());
        owner.refuse(CountedAdmissionError::WorkExhausted);
        assert!(Tactic::prepare_apply(&ast, &owner).is_err());
    }
}

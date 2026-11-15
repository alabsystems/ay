// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Direct expression simplification under an already retained request.
use super::{
    field_to_bv::Borrowed,
    tactic_bool_rewrite::ConjunctionMode,
    tactic_parameters::{Restricted, Steps},
    tactics::{TacticFailure, TacticOperation},
};
use crate::api::{Solver, SolverError, TacticParameterValue as V, TacticParameters, Term};
use ay_core::term::{CountedTermBuilder, TermConstructionAdmission};
use ay_core::{Sort, TermId};
use ay_model_check::ModelValue;
use num_bigint::BigUint;

/// Supported direct-rewriter configuration. These are restrictions/options,
/// never a replacement for the existing operation's source or resource owner.
#[derive(Clone, Copy, Debug, Default)]
pub struct SimplifyParameters {
    rewrite: TacticParameters,
    timeout_ms: Option<u32>,
}
impl SimplifyParameters {
    /// Direct Z3_simplify_ex reads known values by their actual stored type;
    /// unlike the tactic API, a wrong type falls back to the default.
    pub fn set(&mut self, name: &str, value: V) -> Result<(), SolverError> {
        if super::polynomial_parameters::PolynomialParameters::recognizes(name) {
            // Like upstream params_ref getters, an incorrectly typed known
            // direct-rewriter parameter leaves the default intact.
            let _ = self.rewrite.polynomial.set(name, value);
            return Ok(());
        }
        match (name, value) {
            ("max_power_expansion", V::UInt(n)) => self.rewrite.max_power_expansion = Some(n),
            ("max_steps", V::UInt(n)) => self.rewrite.max_steps = Some(n),
            ("max_memory", V::UInt(n)) => self.rewrite.max_memory = Some(n),
            ("elim_and", V::Bool(v)) => self.rewrite.elim_and = Some(v),
            ("timeout", V::UInt(n)) => self.timeout_ms = Some(n),
            ("ctrl_c", V::Bool(false)) => {} // Cannot disable original cancellation.
            ("ctrl_c", V::Bool(true)) => {
                return Err(SolverError::TacticFailed(
                    "direct ctrl_c installation is unsupported".into(),
                ))
            }
            ("max_power_expansion" | "max_steps" | "max_memory" | "timeout", _)
            | ("elim_and" | "ctrl_c", _) => {}
            _ => {
                return Err(SolverError::TacticFailed(
                    "unsupported direct simplifier parameter".into(),
                ))
            }
        }
        Ok(())
    }
    /// A local setting overrides the actual global module value.
    pub fn with_global_sequence_power(mut self, maximum: u32) -> Self {
        self.rewrite.max_power_expansion.get_or_insert(maximum);
        self
    }
    pub fn with_global_polynomial(mut self, global: super::PolynomialParameters) -> Self {
        self.rewrite = self.rewrite.with_global_polynomial(global);
        self
    }
}

impl Solver {
    /// Preserve a public arithmetic application's observable input structure.
    /// The same ordinary constructor request owns its metadata and typed
    /// native construction; this does not begin a solve or evaluation grant.
    pub fn try_arithmetic_application_in_operation(
        &mut self,
        operation: &TacticOperation,
        op: ay_core::term::CountedRingBuiltin,
        arguments: &[Term],
    ) -> Result<Term, SolverError> {
        if !operation.validate(self) {
            return Err(SolverError::TacticFailed(
                "arithmetic constructor source refused".into(),
            ));
        }
        let owner = operation.admission();
        let mut ids = Vec::new();
        ay_core::term::reserve_counted(&mut ids, arguments.len(), owner)
            .map_err(|e| SolverError::TacticFailed(e.to_string()))?;
        owner
            .admit(arguments.len(), 0)
            .map_err(|e| SolverError::TacticFailed(e.to_string()))?;
        if !operation.validate(self) {
            return Err(SolverError::TacticFailed(
                "arithmetic constructor source refused".into(),
            ));
        }
        for &argument in arguments {
            ids.push(self.resolve_term("arithmetic application", argument)?);
        }
        let borrowed = Borrowed(owner);
        let mut builder = CountedTermBuilder::with_admission(self.terms_mut(), &borrowed)
            .map_err(|e| SolverError::TacticFailed(e.to_string()))?;
        let result = builder
            .ring_apply(op, &ids)
            .map_err(|e| SolverError::TacticFailed(e.to_string()))?;
        builder
            .finish()
            .map_err(|e| SolverError::TacticFailed(e.to_string()))?;
        if !operation.validate(self) {
            return Err(SolverError::TacticFailed(
                "arithmetic constructor publication refused".into(),
            ));
        }
        Ok(self.wrap_term(result))
    }

    /// Borrow and compare the live engine sort before adapter publication;
    /// neither sort is cloned and the original source fences bookend controls.
    pub fn term_has_sort_in_operation(
        &self,
        operation: &TacticOperation,
        term: Term,
        expected: &Sort,
    ) -> Result<bool, SolverError> {
        let source = self.resolve_term("simplify sort", term)?;
        if !operation.validate(self) {
            return Err(SolverError::TacticFailed(
                "sort owner/source refused".into(),
            ));
        }
        let owner = operation.admission();
        for sort in [self.terms().sort(source), expected] {
            ay_core::TermStore::inspect_sort_with_progress(sort, &mut |work, bytes| {
                work.checked_add(bytes)
                    .is_some_and(|n| owner.admit(n, 0).is_ok())
            })
            .map_err(|_| SolverError::TacticFailed("sort inspection refused".into()))?;
        }
        let equal = self.terms().sort(source) == expected;
        if !operation.validate(self) {
            return Err(SolverError::TacticFailed("sort publication refused".into()));
        }
        Ok(equal)
    }

    /// Reuse the exact caller operation through parsing, construction and AST
    /// publication. No solver/check attempt or model/proof authority is made.
    pub fn simplify_in_operation(
        &mut self,
        operation: &TacticOperation,
        source: Term,
        parameters: SimplifyParameters,
    ) -> Result<Term, SolverError> {
        if !operation.validate(self) {
            return Err(SolverError::TacticFailed(
                "direct simplifier source/owner changed".into(),
            ));
        }
        let source = self.resolve_term("simplify", source)?;
        let end = operation.sublimit_end(parameters.timeout_ms)?;
        let result = (|| -> Result<TermId, TacticFailure> {
            let restricted =
                Restricted::new(operation.admission(), end, parameters.rewrite.max_memory)?;
            let mut steps = Steps::new(parameters.rewrite.max_steps);
            let rewritten = (|| {
                let roots = super::tactic_polynomial::rewrite_with_sequences(
                    self.terms_mut(),
                    &[source],
                    parameters.rewrite.max_power_expansion.unwrap_or(2),
                    parameters.rewrite.polynomial,
                    &mut steps,
                    &restricted,
                )?;
                let source = *roots
                    .first()
                    .ok_or_else(|| TacticFailure::new("empty direct rewrite"))?;
                super::tactic_propagate_values::simplify_term(
                    self.terms_mut(),
                    source,
                    if parameters.rewrite.elim_and == Some(true) {
                        ConjunctionMode::Eliminate
                    } else {
                        ConjunctionMode::Retain
                    },
                    &mut steps,
                    &restricted,
                )
            })();
            restricted.settle(rewritten)
        })()
        .map_err(TacticFailure::into_solver_error)?;
        if !operation.validate(self) {
            return Err(SolverError::TacticFailed(
                "direct simplifier publication refused".into(),
            ));
        }
        Ok(self.wrap_term(result))
    }
}

pub(super) fn fp_literal(
    builder: &mut CountedTermBuilder<'_, '_, Borrowed<'_>>,
    source: TermId,
    value: &ModelValue,
    owner: &dyn TermConstructionAdmission,
) -> Result<Option<TermId>, TacticFailure> {
    let fail = || TacticFailure::new("direct floating-point literal construction refused");
    let (sign, eb, sb) = match value {
        ModelValue::FloatingPoint {
            sign,
            exponent_bits,
            significand_bits,
            ..
        }
        | ModelValue::FloatingPointExact {
            sign,
            exponent_bits,
            significand_bits,
            ..
        } => (*sign, *exponent_bits, *significand_bits),
        _ => return Ok(None),
    };
    if builder.terms().sort(source) != &Sort::FloatingPoint(eb, sb) || eb < 2 || sb < 2 {
        return Err(fail());
    }
    // Actual native scalar conversion buffers, not the declared FP width.
    let (conversions, bytes) = match value {
        ModelValue::FloatingPoint { .. } => (
            3,
            std::mem::size_of::<u128>() + 2 * std::mem::size_of::<u64>(),
        ),
        _ => (1, std::mem::size_of::<u64>()), // Exact fields stay borrowed.
    };
    owner.admit(conversions, bytes).map_err(|_| fail())?;
    let sign_value = BigUint::from(u8::from(sign));
    let sign = builder
        .bitvector_unsigned(&sign_value, 1)
        .map_err(|_| fail())?;
    let (exponent, fraction) = match value {
        ModelValue::FloatingPoint {
            exponent,
            significand,
            ..
        } => {
            let e = BigUint::from(*exponent);
            let f = BigUint::from(*significand);
            let e = builder.bitvector_unsigned(&e, eb).map_err(|_| fail())?;
            let f = builder.bitvector_unsigned(&f, sb - 1).map_err(|_| fail())?;
            (e, f)
        }
        ModelValue::FloatingPointExact {
            exponent,
            significand,
            ..
        } => {
            let e = builder
                .bitvector_unsigned(exponent, eb)
                .map_err(|_| fail())?;
            let f = builder
                .bitvector_unsigned(significand, sb - 1)
                .map_err(|_| fail())?;
            (e, f)
        }
        _ => return Err(fail()),
    };
    let result = builder
        .floating_point_fields(sign, exponent, fraction)
        .map_err(|_| fail())?;
    owner.check().map_err(|_| fail())?;
    Ok(Some(result))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::api::Logic;
    use ay_core::{Constant, Symbol, TermData};

    #[test]
    fn arithmetic_constructor_preserves_structure_and_the_same_stopped_owner() {
        let mut solver = Solver::new(Logic::All);
        let x = solver.declare_const("constructor_x", Sort::Int);
        let one = solver.int_const(1);
        let operation = solver.begin_tactic_operation().unwrap();
        let sum = solver
            .try_arithmetic_application_in_operation(
                &operation,
                ay_core::term::CountedRingBuiltin::Add,
                &[x, one],
            )
            .unwrap();
        assert!(
            matches!(solver.terms().get(sum.id()), TermData::App(Symbol::Named(h), a)
            if h == "+" && a == &[x.id(), one.id()])
        );
        solver.interrupt();
        let stamp = solver.terms().snapshot_stamp();
        assert!(solver
            .try_arithmetic_application_in_operation(
                &operation,
                ay_core::term::CountedRingBuiltin::Multiply,
                &[sum, sum]
            )
            .is_err());
        solver.clear_interrupt();
        assert!(solver
            .try_arithmetic_application_in_operation(
                &operation,
                ay_core::term::CountedRingBuiltin::Multiply,
                &[sum, sum]
            )
            .is_err());
        assert_eq!(solver.terms().snapshot_stamp(), stamp);
        drop(operation);
        let operation = solver.begin_tactic_operation().unwrap();
        assert!(solver
            .try_arithmetic_application_in_operation(
                &operation,
                ay_core::term::CountedRingBuiltin::Multiply,
                &[sum, sum]
            )
            .is_ok());
    }

    #[test]
    fn borrowed_immediate_children_preserve_order_foreign_identity_and_large_forwarded_arity() {
        let mut solver = Solver::new(Logic::All);
        let x = solver.declare_const("child_x", Sort::Int);
        let y = solver.declare_const("child_y", Sort::Int);
        let operation = solver.begin_tactic_operation().unwrap();
        let sum = solver
            .try_arithmetic_application_in_operation(
                &operation,
                ay_core::term::CountedRingBuiltin::Add,
                &[x, y],
            )
            .unwrap();
        assert_eq!(solver.try_term_child_count(sum).unwrap(), 2);
        assert_eq!(
            solver.try_term_children_match(sum, &[x, y]).unwrap(),
            (2, true)
        );
        assert_eq!(
            solver.try_term_children_match(sum, &[y, x]).unwrap(),
            (2, false)
        );
        let mut foreign = Solver::new(Logic::All);
        let other = foreign.declare_const("child_x", Sort::Int);
        assert_eq!(
            solver.try_term_children_match(sum, &[other, y]).unwrap(),
            (2, false)
        );
        let source = solver.terms_mut().mk_app_structural(
            Symbol::named("many_children"),
            vec![x.id(); 128],
            Sort::Complex,
        );
        let source = solver.wrap_term(source);
        assert_eq!(solver.try_term_child_count(source).unwrap(), 128);
        assert_eq!(
            solver.try_term_children_match(source, &[x]).unwrap(),
            (128, false)
        );
        assert_eq!(
            solver
                .try_term_children_match(source, &vec![x; 128])
                .unwrap(),
            (128, true)
        );
    }

    #[test]
    fn direct_simplifier_raw_closed_arithmetic_and_fp_use_owned_folding() {
        let mut solver = Solver::new(Logic::All);
        let terms = solver.terms_mut();
        let two = terms.mk_int(2.into());
        let three = terms.mk_int(3.into());
        let raw = terms.mk_app_structural(Symbol::named("+"), [two, three], Sort::Int);
        let raw = solver.wrap_term(raw);
        let operation = solver.begin_tactic_operation().unwrap();
        let result = solver
            .simplify_in_operation(&operation, raw, SimplifyParameters::default())
            .unwrap();
        assert!(
            matches!(solver.terms().get(result.id()), TermData::Const(Constant::Int(v)) if v == &num_bigint::BigInt::from(5))
        );
        drop(operation);

        let one = solver.try_fp_const_from_bits(0x3f800000, 8, 24).unwrap();
        let terms = solver.terms_mut();
        let rm = terms.mk_app_structural(
            Symbol::named("RNE"),
            [],
            Sort::Uninterpreted("RoundingMode".into()),
        );
        let raw = terms.mk_app_structural(
            Symbol::named("fp.add"),
            [rm, one.id(), one.id()],
            Sort::FloatingPoint(8, 24),
        );
        let raw = solver.wrap_term(raw);
        let operation = solver.begin_tactic_operation().unwrap();
        let result = solver
            .simplify_in_operation(&operation, raw, SimplifyParameters::default())
            .unwrap();
        let value = ay_model_check::evaluate_term(
            solver.terms(),
            &super::super::tactic_propagate_values::Closed(operation.admission()),
            result.id(),
        );
        assert!(
            matches!(
                value,
                ay_model_check::EvalOutcome::Value(ModelValue::FloatingPoint {
                    sign: false,
                    exponent: 128,
                    significand: 0,
                    exponent_bits: 8,
                    significand_bits: 24
                })
            ),
            "{value:?}"
        );
    }

    #[test]
    fn direct_simplifier_ieee_conversion_folds_only_concrete_builtin_values() {
        let mut solver = Solver::new(Logic::All);
        let one = solver.try_fp_const_from_bits(0x3f800000, 8, 24).unwrap();
        let raw = solver.try_fp_to_ieee_bv(one).unwrap();
        let operation = solver.begin_tactic_operation().unwrap();
        let folded = solver
            .simplify_in_operation(&operation, raw, SimplifyParameters::default())
            .unwrap();
        assert!(matches!(solver.terms().get(folded.id()),
            TermData::Const(Constant::BitVec { value, .. })
                if value == &num_bigint::BigInt::from(0x3f800000u32)));
        drop(operation);

        // The same spelling becomes opaque when it denotes an authored UF.
        solver
            .terms_mut()
            .register_declared_function("fp.to_ieee_bv");
        let operation = solver.begin_tactic_operation().unwrap();
        let opaque = solver
            .simplify_in_operation(&operation, raw, SimplifyParameters::default())
            .unwrap();
        assert!(matches!(
            solver.terms().get(opaque.id()),
            TermData::App(_, _)
        ));
    }

    #[test]
    fn direct_simplifier_original_stop_is_sticky_and_new_request_recovers() {
        let mut solver = Solver::new(Logic::All);
        let yes = solver.bool_const(true);
        let operation = solver.begin_tactic_operation().unwrap();
        let stamp = solver.terms().snapshot_stamp();
        solver.interrupt();
        assert!(solver
            .simplify_in_operation(&operation, yes, SimplifyParameters::default())
            .is_err());
        solver.clear_interrupt();
        assert!(solver
            .simplify_in_operation(&operation, yes, SimplifyParameters::default())
            .is_err());
        assert_eq!(solver.terms().snapshot_stamp(), stamp);
        drop(operation);
        let operation = solver.begin_tactic_operation().unwrap();
        assert_eq!(
            solver
                .simplify_in_operation(&operation, yes, SimplifyParameters::default())
                .unwrap(),
            yes
        );
    }

    #[test]
    fn direct_simplifier_same_owner_work_refusal_and_foreign_scope_refuse() {
        let mut solver = Solver::new(Logic::All);
        let yes = solver.bool_const(true);
        let operation = solver.begin_tactic_operation().unwrap();
        assert!(operation.admission().admit(usize::MAX, 0).is_err());
        assert!(solver
            .simplify_in_operation(&operation, yes, SimplifyParameters::default())
            .is_err());
        drop(operation);
        let other = Solver::new(Logic::All);
        let foreign = other.begin_tactic_operation().unwrap();
        assert!(solver
            .simplify_in_operation(&foreign, yes, SimplifyParameters::default())
            .is_err());
    }

    #[test]
    fn direct_simplifier_local_limits_are_typed_and_do_not_revive_originals() {
        let mut solver = Solver::new(Logic::All);
        let yes = solver.bool_const(true);
        let operation = solver.begin_tactic_operation().unwrap();
        let mut parameters = SimplifyParameters::default();
        parameters.set("max_steps", V::UInt(0)).unwrap();
        assert!(matches!(
            solver.simplify_in_operation(&operation, yes, parameters),
            Err(SolverError::TacticLimit(crate::api::TacticLimitKind::Work))
        ));
        assert!(operation.admission().check().is_ok());
        assert!(solver
            .simplify_in_operation(&operation, yes, SimplifyParameters::default())
            .is_ok());
        let mut parameters = SimplifyParameters::default();
        parameters.set("max_memory", V::UInt(0)).unwrap();
        assert!(matches!(
            solver.simplify_in_operation(&operation, yes, parameters),
            Err(SolverError::TacticLimit(
                crate::api::TacticLimitKind::Memory
            ))
        ));
    }
}

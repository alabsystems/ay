// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Admission before rendering one complete, typed pending-array DATA value.

use super::*;
use crate::executor::model::recovery_admission::RecoveryAdmission;
use crate::executor::model::rendered_dt_limits::SchemaSourceBudget;
use ay_model_check::ModelValue;

#[derive(Clone, Copy, PartialEq, Eq)]
enum RenderProfile {
    Pending,
    Retained,
}

trait RenderOwner {
    fn pay(&self, work: usize, bytes: usize) -> bool;
    fn profile(&self) -> RenderProfile;
}
impl RenderOwner for RecoveryAdmission {
    fn pay(&self, work: usize, bytes: usize) -> bool {
        RecoveryAdmission::pay(self, work, bytes)
    }
    fn profile(&self) -> RenderProfile {
        RenderProfile::Pending
    }
}
struct OriginalRead<'a>(
    &'a Executor,
    &'a dyn ay_core::term::TermConstructionAdmission,
);
impl RenderOwner for OriginalRead<'_> {
    fn pay(&self, work: usize, bytes: usize) -> bool {
        super::super::super::evaluation_copies::active()
            && super::super::super::evaluation_copies::validate(self.0)
            && self.1.admit(work, bytes).is_ok()
            && super::super::super::evaluation_copies::validate(self.0)
    }
    fn profile(&self) -> RenderProfile {
        RenderProfile::Retained
    }
}

fn checked_add(left: usize, right: usize) -> Result<usize, QueryError> {
    left.checked_add(right).ok_or(QueryError::Exhausted)
}

fn charge(owner: &dyn RenderOwner, units: usize, bytes: usize) -> Result<(), QueryError> {
    owner
        .pay(units, bytes)
        .then_some(())
        .ok_or(QueryError::Exhausted)
}

fn allocate(owner: &dyn RenderOwner, bytes: usize) -> Result<(), QueryError> {
    charge(owner, bytes, bytes)
}

/// Bound the actual recursive formatter's strings, including its repeated
/// array-store prefix copies and datatype parts/join/result buffers. This
/// borrowed walk finishes before any formatting occurs. Schema visits join
/// the SAME active recovery ledger before touching nested descriptors.
fn rendered_bound(
    exec: &Executor,
    value: &ModelValue,
    sort: &Sort,
    depth: usize,
    schema: &mut SchemaSourceBudget,
    owner: &dyn RenderOwner,
) -> Result<usize, QueryError> {
    if depth > 32 {
        return Err(QueryError::Invalid("pending value depth"));
    }
    charge(owner, 1, 0)?;
    if !schema.charge_sort(sort) {
        return Err(QueryError::Exhausted);
    }
    match (value, sort) {
        (ModelValue::Bool(value), Sort::Bool) => {
            let bytes = if *value { 4 } else { 5 };
            allocate(owner, bytes)?;
            Ok(bytes)
        }
        (ModelValue::Int(value), Sort::Int | Sort::Real) => {
            let bytes = checked_add(
                usize::try_from(value.bits()).map_err(|_| QueryError::Exhausted)?,
                5,
            )?;
            allocate(owner, bytes.checked_mul(3).ok_or(QueryError::Exhausted)?)?;
            Ok(bytes)
        }
        (ModelValue::Real(value), Sort::Real) if value.denom().sign() == num_bigint::Sign::Plus => {
            let bits = value
                .numer()
                .bits()
                .checked_add(value.denom().bits())
                .ok_or(QueryError::Exhausted)?;
            let bytes = checked_add(
                usize::try_from(bits).map_err(|_| QueryError::Exhausted)?,
                16,
            )?;
            allocate(owner, bytes.checked_mul(3).ok_or(QueryError::Exhausted)?)?;
            Ok(bytes)
        }
        (ModelValue::BitVec { width, value }, Sort::BitVec(expected))
            if *width > 0
                && *width == expected.width
                && value.sign() != num_bigint::Sign::Minus
                && value.bits() <= u64::from(*width) =>
        {
            // One binary digit per bit is an upper bound for the existing
            // binary/hex formatter. No giant width can reach its allocation
            // before the original aggregate grant accepts this bound.
            let bytes = checked_add(*width as usize, 32)?;
            allocate(owner, bytes.checked_mul(2).ok_or(QueryError::Exhausted)?)?;
            Ok(bytes)
        }
        (ModelValue::Str(value), Sort::String) if owner.profile() == RenderProfile::Retained => {
            let bytes = checked_add(value.len().checked_mul(6).ok_or(QueryError::Exhausted)?, 2)?;
            allocate(owner, bytes)?;
            Ok(bytes)
        }
        (
            ModelValue::FloatingPoint {
                exponent_bits,
                significand_bits,
                ..
            }
            | ModelValue::FloatingPointExact {
                exponent_bits,
                significand_bits,
                ..
            },
            Sort::FloatingPoint(eb, sb),
        ) if owner.profile() == RenderProfile::Retained
            && exponent_bits == eb
            && significand_bits == sb =>
        {
            let bytes = usize::try_from(eb.checked_add(*sb).ok_or(QueryError::Exhausted)?)
                .map_err(|_| QueryError::Exhausted)?
                .checked_mul(2)
                .and_then(|n| n.checked_add(128))
                .ok_or(QueryError::Exhausted)?;
            allocate(owner, bytes.checked_mul(3).ok_or(QueryError::Exhausted)?)?;
            Ok(bytes)
        }
        (ModelValue::Array(array), Sort::Array(array_sort)) => {
            charge(owner, array.store.len(), 0)?;
            let mut descriptor = SchemaSourceBudget::new();
            if !descriptor.charge_sort(sort) {
                return Err(QueryError::Exhausted);
            }
            let sort_bytes = descriptor.work().ok_or(QueryError::Exhausted)?;
            let default = rendered_bound(
                exec,
                &array.default,
                &array_sort.element_sort,
                depth + 1,
                schema,
                owner,
            )?;
            let mut bytes = checked_add(checked_add(sort_bytes, default)?, 32)?;
            allocate(owner, checked_add(sort_bytes, bytes)?)?;
            for (index, value) in &array.store {
                let index = rendered_bound(
                    exec,
                    index,
                    &array_sort.index_sort,
                    depth + 1,
                    schema,
                    owner,
                )?;
                let value = rendered_bound(
                    exec,
                    value,
                    &array_sort.element_sort,
                    depth + 1,
                    schema,
                    owner,
                )?;
                bytes = checked_add(checked_add(checked_add(bytes, index)?, value)?, 16)?;
                allocate(owner, bytes)?;
            }
            Ok(bytes)
        }
        (ModelValue::Datatype { ctor, args }, _) => {
            if !schema.charge_identifier(ctor) {
                return Err(QueryError::Exhausted);
            }
            let Some(info) = exec.ctx.exact_datatype_member_info(ctor) else {
                return Err(QueryError::Invalid("pending constructor is not declared"));
            };
            if info.declaration_kind() != DeclarationKind::DatatypeConstructor
                || !exec.ctx.is_live_datatype_member_identity(ctor)
                || !schema.charge_sort(&info.sort)
                || &info.sort != sort
            {
                return Err(QueryError::Invalid("pending constructor owner"));
            }
            let Some(fields) = exec.ctx.constructor_selector_info(ctor) else {
                return Err(QueryError::Invalid("pending constructor fields"));
            };
            if args.len() != fields.len() || args.len() != info.arg_sorts.len() {
                return Err(QueryError::Invalid("pending constructor arity"));
            }
            charge(
                owner,
                args.len(),
                args.len()
                    .checked_mul(size_of::<String>())
                    .ok_or(QueryError::Exhausted)?,
            )?;
            let surface = exec.dt_surface(ctor);
            if !schema.charge_identifier(surface) {
                return Err(QueryError::Exhausted);
            }
            let mut children = 0;
            for ((arg, (field, field_sort)), argument_sort) in
                args.iter().zip(fields).zip(&info.arg_sorts)
            {
                if !schema.charge_identifier(field)
                    || !schema.charge_sort(argument_sort)
                    || argument_sort != field_sort
                {
                    return Err(QueryError::Invalid("pending constructor field signature"));
                }
                children = checked_add(
                    children,
                    rendered_bound(exec, arg, field_sort, depth + 1, schema, owner)?,
                )?;
            }
            if args.is_empty() {
                allocate(owner, surface.len())?;
                return Ok(surface.len());
            }
            let joined = checked_add(children, args.len() - 1)?;
            let result = checked_add(checked_add(surface.len(), joined)?, 3)?;
            allocate(
                owner,
                checked_add(checked_add(surface.len(), joined)?, result)?,
            )?;
            Ok(result)
        }
        // Unknown/opaque/unavailable payloads are not complete DATA. This
        // protocol also does not render FP, algebraic, sequence or string
        // values; it never substitutes a canonical inhabitant for them.
        _ => Err(QueryError::Invalid(
            "unsupported or incomplete pending value",
        )),
    }
}

impl Executor {
    /// Reuse the native typed formatter's PRE-allocation bound under the
    /// actual retained read/copy owner. No new timer or allowance is created.
    pub(in crate::executor::model) fn retained_array_render_value(
        &self,
        value: &ModelValue,
        sort: &Sort,
        admission: &dyn ay_core::term::TermConstructionAdmission,
    ) -> Result<String, QueryError> {
        let owner = OriginalRead(self, admission);
        charge(&owner, 0, 0)?;
        let bound = rendered_bound(self, value, sort, 0, &mut SchemaSourceBudget::new(), &owner)?;
        charge(&owner, 0, 0)?;
        let text = self
            .format_gate_model_value(value, sort)
            .ok_or(QueryError::Invalid("retained value renderer refused"))?;
        if text.len() > bound {
            return Err(QueryError::Invalid("retained renderer bound"));
        }
        charge(&owner, 0, 0)?;
        Ok(text)
    }
    pub(in crate::executor::model) fn pending_array_render_value(
        &self,
        value: &ModelValue,
        sort: &Sort,
    ) -> Result<String, QueryError> {
        let owner = RecoveryAdmission::current_for(self).ok_or(QueryError::Invalid(
            "pending renderer has no original resource owner",
        ))?;
        // Formatting cannot borrow an unrelated caller ledger. Every payload,
        // copy and temporary allocation is charged to this exact query owner.
        charge(&owner, 0, 0)?;
        let mut schema = SchemaSourceBudget::new();
        let bound = rendered_bound(self, value, sort, 0, &mut schema, &owner)?;
        let rendered = self
            .format_gate_model_value(value, sort)
            .ok_or(QueryError::Invalid(
                "pending typed value cannot be rendered",
            ))?;
        if rendered.len() > bound {
            return Err(QueryError::Invalid(
                "pending renderer exceeded its admitted bound",
            ));
        }
        charge(&owner, 0, 0)?;
        Ok(rendered)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_model_check::ArrayValue;
    use std::sync::Arc;

    fn fixture() -> (Executor, String, Sort, ModelValue) {
        let mut exec = Executor::new();
        let commands = ay_frontend::parse(
            "(declare-datatype Row ((row (tag (_ BitVec 8)) (data (Array Int Bool)))))",
        )
        .unwrap();
        assert_eq!(exec.execute_all(&commands).unwrap(), [] as [String; 0]);
        let info = exec.ctx.exact_datatype_member_info("row").unwrap();
        let ctor = exec.ctx.symbol_identity_name("row", info).to_string();
        let sort = info.sort.clone();
        let value = ModelValue::Datatype {
            ctor: ctor.clone(),
            args: vec![
                ModelValue::bitvec(9.into(), 8),
                ModelValue::Array(Box::new(ArrayValue {
                    default: ModelValue::Bool(false),
                    store: vec![(ModelValue::Int(33.into()), ModelValue::Bool(true))],
                })),
            ],
        };
        (exec, ctor, sort, value)
    }

    #[test]
    fn complete_nested_values_render_only_with_the_exact_original_resource_owner() {
        let (exec, _, sort, value) = fixture();
        assert!(exec.pending_array_render_value(&value, &sort).is_err());
        let _stop = ay_core::resource::enter_check_stop(Arc::new(|| false));
        let scope = RecoveryScope::enter(&exec, MAX_WORK as usize, MAX_COPY_BYTES).unwrap();
        let owner = scope.admission();
        let rendered = exec.pending_array_render_value(&value, &sort).unwrap();
        assert_eq!(
            rendered,
            "(row #x09 (store ((as const (Array Int Bool)) false) 33 true))"
        );
        assert!(!rendered.contains("ay.value-unavailable"));
        let other = Executor::new();
        assert!(other
            .pending_array_render_value(&ModelValue::Bool(false), &Sort::Bool)
            .is_err());
        assert!(owner.pay(0, 0));
    }

    #[test]
    fn incomplete_wrong_owner_and_wrong_field_values_are_not_renderable_data() {
        let (exec, ctor, sort, _) = fixture();
        let _stop = ay_core::resource::enter_check_stop(Arc::new(|| false));
        let scope = RecoveryScope::enter(&exec, MAX_WORK as usize, MAX_COPY_BYTES).unwrap();
        let owner = scope.admission();
        for value in [
            ModelValue::Uninterpreted("(_ ay.value-unavailable t216)".into()),
            ModelValue::Datatype {
                ctor: "fake-row".into(),
                args: vec![],
            },
            ModelValue::Datatype {
                ctor,
                args: vec![ModelValue::Int(9.into()), ModelValue::Bool(false)],
            },
            ModelValue::Bool(false),
        ] {
            assert!(exec.pending_array_render_value(&value, &sort).is_err());
        }
        assert!(
            owner.pay(0, 0),
            "a semantic DATA refusal does not fabricate a stop"
        );
    }

    #[test]
    fn huge_width_is_refused_before_formatting_and_does_not_reopen_the_shared_grant() {
        let exec = Executor::new();
        let _stop = ay_core::resource::enter_check_stop(Arc::new(|| false));
        let scope = RecoveryScope::enter(&exec, 1024, 1024).unwrap();
        let owner = scope.admission();
        let value = ModelValue::BitVec {
            width: u32::MAX,
            value: 0.into(),
        };
        assert!(exec
            .pending_array_render_value(&value, &Sort::bitvec(u32::MAX))
            .is_err());
        assert!(!owner.pay(0, 0));
        assert!(exec
            .pending_array_render_value(&ModelValue::Bool(true), &Sort::Bool)
            .is_err());
    }

    #[test]
    fn an_unrelated_plain_work_budget_cannot_pay_the_original_owners_format_cost() {
        let exec = Executor::new();
        let value = ModelValue::Int(BigInt::from(1u8) << 4096usize);
        let _stop = ay_core::resource::enter_check_stop(Arc::new(|| false));
        let scope = RecoveryScope::enter(&exec, 1024, 1024).unwrap();
        let owner = scope.admission();
        let mut checkpoint = || std::ops::ControlFlow::Continue(());
        let mut unrelated = WorkBudget::new(MAX_WORK, &mut checkpoint);
        unrelated.admit(0, 1024 * 1024).unwrap();
        assert!(exec.pending_array_render_value(&value, &Sort::Int).is_err());
        assert!(
            !owner.pay(0, 0),
            "the real shared owner, rather than this plain budget, refuses"
        );
        assert!(unrelated.charge(1).is_ok());
    }
}

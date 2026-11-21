// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Sequence reads retain fixed in-bounds semantics and explicitly chosen,
//! single-valued out-of-bounds interpretations. An evaluation failure never
//! establishes the out-of-bounds condition.

use super::*;
use num_traits::ToPrimitive;

impl Evaluator<'_> {
    pub(super) fn charge_sequence_work(&self, amount: usize) -> EvalResult<()> {
        if self.admission_callback_active.get() {
            return Err(self.reentrant_admission_error());
        }
        let result = {
            self.admission_callback_active.set(true);
            let _guard = AdmissionCallbackGuard(&self.admission_callback_active);
            self.charge_functional_work(amount)
        };
        if let Some(reason) = self.prior_admission_refusal() {
            return Err(reason);
        }
        result
    }

    pub(super) fn sequence_instance_sorts_equal(
        &self,
        left: &Sort,
        right: &Sort,
    ) -> EvalResult<bool> {
        // Polymorphic empty sequences need distinct function instances. Admit
        // borrowed raw sorts before structural comparison; never use display
        // text or a fresh name to identify the native type.
        let mut nodes = 0usize;
        self.admit_sequence_instance_sort(left, 0, &mut nodes)?;
        self.admit_sequence_instance_sort(right, 0, &mut nodes)?;
        Ok(left == right)
    }

    fn admit_sequence_instance_sort(
        &self,
        sort: &Sort,
        depth: usize,
        nodes: &mut usize,
    ) -> EvalResult<()> {
        if depth >= 64 || *nodes >= 4096 {
            return Err(EvalError::resource(
                EvalResource::Depth,
                "sequence instance sort exceeds its bounded shape",
            ));
        }
        *nodes += 1;
        self.charge_sequence_work(1)?;
        match sort {
            Sort::Array(array) => {
                self.admit_sequence_instance_sort(&array.index_sort, depth + 1, nodes)?;
                self.admit_sequence_instance_sort(&array.element_sort, depth + 1, nodes)
            }
            Sort::Seq(element) => self.admit_sequence_instance_sort(element, depth + 1, nodes),
            Sort::Uninterpreted(name) | Sort::TypeVar(name) | Sort::FiniteDomain(name, _) => {
                self.charge_sequence_work(name.len())
            }
            Sort::Datatype(datatype) => {
                self.charge_sequence_work(
                    datatype
                        .name
                        .len()
                        .saturating_add(datatype.constructors.len()),
                )?;
                for constructor in &datatype.constructors {
                    self.charge_sequence_work(
                        constructor
                            .name
                            .len()
                            .saturating_add(constructor.fields.len()),
                    )?;
                    for field in &constructor.fields {
                        self.charge_sequence_work(field.name.len())?;
                        self.admit_sequence_instance_sort(&field.sort, depth + 1, nodes)?;
                    }
                }
                Ok(())
            }
            Sort::Bool
            | Sort::Int
            | Sort::Real
            | Sort::BitVec(_)
            | Sort::String
            | Sort::RegLan
            | Sort::FloatingPoint(..)
            | Sort::Char
            | Sort::Complex
            | Sort::FiniteField(_) => Ok(()),
            _ => Err("unsupported sequence instance sort".into()),
        }
    }

    pub(super) fn eval_sequence_nth(
        &self,
        term: TermId,
        args: &[TermId],
        depth: usize,
    ) -> EvalResult<ModelValue> {
        let [sequence, index] = exactly(args)?;
        if self.terms.entry_stamp(sequence).is_none() || self.terms.entry_stamp(index).is_none() {
            return Err("seq.nth has an invalid operand handle".into());
        }
        let Sort::Seq(element) = self.terms.sort(sequence) else {
            return Err("seq.nth requires a sequence operand".into());
        };
        if self.terms.sort(index) != &Sort::Int || self.terms.sort(term) != element.as_ref() {
            return Err("seq.nth operand/result signature mismatch".into());
        }
        let values = self.eval_all(args, depth)?;
        let [ModelValue::Seq(sequence_value), ModelValue::Int(index_value)] = values.as_slice()
        else {
            return Err(
                "seq.nth requires independently evaluated sequence and integer values".into(),
            );
        };
        self.ensure_value_inhabits_sort(&values[0], self.terms.sort(sequence))?;
        if let Some(value) = index_value
            .to_usize()
            .and_then(|index| sequence_value.get(index))
        {
            self.ensure_value_inhabits_sort(value, element)?;
            return self.clone_value(value);
        }
        // Negative and non-usize indices are outside every materialized finite
        // sequence. This exact branch may choose a value of the element sort,
        // using the existing value-keyed graph and context-dependence refusal.
        self.admit_sequence_instance_sort(element, 0, &mut 0usize)?;
        self.eval_uninterpreted_app_checked(
            term,
            "seq.nth",
            args,
            depth,
            "seq.nth index is outside the independently evaluated finite sequence".into(),
            Some(ProvenUnconstrainedKind::SeqNthOutOfBounds),
            |value| self.ensure_value_inhabits_sort(value, element),
        )
    }
}

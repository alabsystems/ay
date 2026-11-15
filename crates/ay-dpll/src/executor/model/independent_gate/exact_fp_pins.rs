// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact model DATA construction under the retained original model owner.
//! The caller supplies source/leaf validation and the post-cleanup fence.

use ay_core::term::{CountedBuiltin, CountedTermBuilder, CountedTermError};
use ay_core::{Sort, TermId, TermStore};
use ay_frontend::SourceContextStamp;
use ay_model_check::ModelValue;

use super::super::functional_arrays::PinAdmission;
use super::{Executor, IndependentModelView};

const MAX_DEPTH: usize = 256;

#[cfg(test)]
mod tests;

/// A construction frame retains the existing model ledger and source identity.
/// It neither seals a model nor creates a new allowance or confirmation epoch.
pub(super) struct Frame {
    owner: PinAdmission,
    source: SourceContextStamp,
    binding: Binding,
}

enum Binding {
    RetainedModel,
    CurrentRead,
}

impl Frame {
    pub(super) fn capture(exec: &Executor) -> Result<Option<Self>, ()> {
        let Some(model) = exec.last_model.as_ref() else {
            return Ok(None);
        };
        let retained_query = match &model.construction_owner {
            Some(owner) => {
                if !owner.validate_data_source(exec) {
                    return Err(());
                }
                match owner.query_binding_matches(exec) {
                    Ok(matches) => matches,
                    Err(_) => {
                        owner.latch_original_constructor_stop(exec);
                        return Err(());
                    }
                }
            }
            None => false,
        };
        let (owner, binding) = if retained_query {
            (PinAdmission::capture(exec, model), Binding::RetainedModel)
        } else {
            // Old model carriers may lack a retained construction ledger.
            // Bound classification by the actual current read in that case;
            // this fallback NEVER enables Exact pin construction.
            (
                PinAdmission::capture_current_read(exec),
                Binding::CurrentRead,
            )
        };
        let owner = owner.map_err(|_| ())?;
        let source = exec.ctx.source_context_stamp();
        let valid = model.validate_functional_array_source(exec).is_ok()
            && IndependentModelView::new(exec, model)
                .canonical_theory_bindings_are_coherent_with_progress(&mut |work| {
                    owner.pay(work, 0).is_ok()
                });
        if !valid {
            let _ = owner.finish(exec.ctx.terms.true_memory_bytes());
            return Err(());
        }
        Ok(Some(Self {
            owner,
            source,
            binding,
        }))
    }

    pub(super) fn owner(&self) -> &PinAdmission {
        &self.owner
    }

    pub(super) fn model_owner(&self) -> Option<&PinAdmission> {
        match self.binding {
            Binding::RetainedModel => Some(&self.owner),
            Binding::CurrentRead => None,
        }
    }

    /// Caller-owned row/value/traversal scratch must have dropped first.
    pub(super) fn finish(self, exec: &Executor) -> bool {
        let valid = self.source == exec.ctx.source_context_stamp()
            && exec.last_model.as_ref().is_some_and(|model| {
                (match self.binding {
                    Binding::RetainedModel => {
                        self.owner.matches_model(model) && model.validate_construction_owner(exec)
                    }
                    Binding::CurrentRead => {
                        self.owner.matches_current_read(exec)
                            && model
                                .construction_owner
                                .as_ref()
                                .is_none_or(|owner| owner.validate_data_source(exec))
                    }
                }) && model.validate_functional_array_source(exec).is_ok()
                    && IndependentModelView::new(exec, model)
                        .canonical_theory_bindings_are_coherent_with_progress(&mut |work| {
                            self.owner.pay(work, 0).is_ok()
                        })
            });
        let finished = self.owner.finish(exec.ctx.terms.true_memory_bytes());
        valid && finished.is_ok()
    }
}

/// Detect exact fields without copying any payload or inventing a read grant.
pub(super) fn contains_exact(value: &ModelValue, owner: &PinAdmission) -> Option<bool> {
    fn visit(value: &ModelValue, owner: &PinAdmission, depth: usize) -> Option<bool> {
        owner.pay(1, 0).ok()?;
        if depth > MAX_DEPTH {
            return None;
        }
        match value {
            ModelValue::FloatingPointExact { .. } => Some(true),
            ModelValue::Array(array) => {
                if visit(&array.default, owner, depth + 1)? {
                    return Some(true);
                }
                for (index, value) in &array.store {
                    if visit(index, owner, depth + 1)? || visit(value, owner, depth + 1)? {
                        return Some(true);
                    }
                }
                Some(false)
            }
            _ => Some(false),
        }
    }
    visit(value, owner, 0)
}

pub(super) fn literal(
    terms: &mut TermStore,
    value: &ModelValue,
    sort: &Sort,
    owner: &PinAdmission,
) -> Option<TermId> {
    if let Sort::FloatingPoint(eb, sb) = sort {
        namespace(*eb, *sb).ok()?;
        let (value_eb, value_sb) = match value {
            ModelValue::FloatingPointExact {
                exponent_bits,
                significand_bits,
                ..
            }
            | ModelValue::FloatingPoint {
                exponent_bits,
                significand_bits,
                ..
            } => (*exponent_bits, *significand_bits),
            _ => return None,
        };
        if (value_eb, value_sb) != (*eb, *sb) {
            return None;
        }
    }
    let mut builder = CountedTermBuilder::with_admission(terms, owner).ok()?;
    let result = construct(&mut builder, value, sort, owner, 0);
    // Constructor temporaries have dropped before index disposal and its
    // original-owner poll. The caller's final source/capacity fence comes last.
    let finished = builder.finish();
    finished.ok()?;
    result.ok()
}

fn namespace(eb: u32, sb: u32) -> Result<(), CountedTermError> {
    if !(2..=ay_fp::MAX_ENCODING_EXPONENT_BITS).contains(&eb)
        || !(2..=ay_fp::MAX_ENCODING_SIGNIFICAND_BITS).contains(&sb)
    {
        return Err(CountedTermError::InvalidInput);
    }
    Ok(())
}

fn construct(
    builder: &mut CountedTermBuilder<'_, '_, PinAdmission>,
    value: &ModelValue,
    sort: &Sort,
    owner: &PinAdmission,
    depth: usize,
) -> Result<TermId, CountedTermError> {
    use ay_core::term::TermConstructionAdmission;
    owner.admit(1, 0)?;
    if depth > MAX_DEPTH {
        return Err(CountedTermError::Unsupported);
    }
    match (value, sort) {
        (ModelValue::Bool(value), Sort::Bool) => builder.boolean(*value),
        (ModelValue::BitVec { width, value }, Sort::BitVec(expected))
            if *width == expected.width =>
        {
            builder.bitvector(value, *width)
        }
        (
            ModelValue::FloatingPointExact {
                sign,
                exponent,
                significand,
                exponent_bits,
                significand_bits,
            },
            Sort::FloatingPoint(eb, sb),
        ) if (exponent_bits, significand_bits) == (eb, sb) => {
            namespace(*eb, *sb)?;
            // Only the fixed one-bit sign temporary is created here. Both
            // variable-sized fields remain borrowed until their builder debit.
            owner.admit(64, 64)?;
            let sign = builder.bitvector(&num_bigint::BigInt::from(u8::from(*sign)), 1)?;
            let exponent = builder.bitvector_unsigned(exponent, *eb)?;
            let fraction = builder.bitvector_unsigned(significand, *sb - 1)?;
            builder.floating_point_fields(sign, exponent, fraction)
        }
        (
            ModelValue::FloatingPoint {
                sign,
                exponent,
                significand,
                exponent_bits,
                significand_bits,
            },
            Sort::FloatingPoint(eb, sb),
        ) if (exponent_bits, significand_bits) == (eb, sb) => {
            namespace(*eb, *sb)?;
            // The legacy carrier has at most 128 stored fraction bits. A
            // malformed wide legacy value must not acquire Exact semantics.
            if *sb > u128::BITS + 1 {
                return Err(CountedTermError::InvalidInput);
            }
            owner.admit(256, 256)?;
            let sign = builder.bitvector(&num_bigint::BigInt::from(u8::from(*sign)), 1)?;
            let exponent = builder.bitvector(&num_bigint::BigInt::from(*exponent), *eb)?;
            let fraction = builder.bitvector(&num_bigint::BigInt::from(*significand), *sb - 1)?;
            builder.floating_point_fields(sign, exponent, fraction)
        }
        (ModelValue::Array(array), Sort::Array(array_sort)) => {
            let default = construct(
                builder,
                &array.default,
                &array_sort.element_sort,
                owner,
                depth + 1,
            )?;
            let mut term = builder.constant_array(&array_sort.index_sort, default)?;
            // Preserve oldest-first/newest-wins semantics without cloning the
            // model's store list or falling back to an unmetered constructor.
            for (index, value) in &array.store {
                let index = construct(builder, index, &array_sort.index_sort, owner, depth + 1)?;
                let value = construct(builder, value, &array_sort.element_sort, owner, depth + 1)?;
                term = builder.apply(CountedBuiltin::Store, &[term, index, value])?;
            }
            Ok(term)
        }
        _ => Err(CountedTermError::Unsupported),
    }
}

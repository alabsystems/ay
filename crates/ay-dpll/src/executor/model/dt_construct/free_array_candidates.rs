// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded pairwise-distinct finite-function candidates for free DT fields.

use ay_core::Sort;
use ay_model_check::{ArrayValue, ModelValue};
use num_bigint::BigInt;
use num_rational::BigRational;

use super::DtBuilder;

/// The class constructor already caps requested candidates much more tightly,
/// but this independent bound makes the enumerator total under direct reuse.
const MAX_FREE_ARRAY_VARIANTS: usize = 4 * 1024;

impl DtBuilder<'_> {
    fn supports_free_array_variants(&self, sort: &Sort) -> bool {
        let Sort::Array(array) = sort else {
            return false;
        };
        scalar_at(&array.index_sort, 0).is_some()
            && scalar_at(&array.element_sort, 0).is_some()
            && scalar_at(&array.element_sort, 1).is_some()
    }

    /// Pick the first representable field whose selector is absent from this
    /// class. A later exact reconstruction may overwrite every observed field;
    /// varying one of those would create only syntactically fresh candidates
    /// that collapse to the same final datatype value. Both callers must first
    /// charge the exact `fields * sel_apps` envelope through
    /// `charge_field_scans`; naming that contract prevents a future native-DT
    /// caller from silently bypassing the unconditional budget.
    pub(super) fn precharged_free_array_variation_fields(
        &self,
        root: usize,
        fields: &[(String, Sort)],
    ) -> Vec<usize> {
        let Some(required_terms) = self.datatype_array_required_terms.as_ref() else {
            return Vec::new();
        };
        fields
            .iter()
            .enumerate()
            .filter_map(|(index, (selector, sort))| {
                (self.supports_free_array_variants(sort)
                    && !self
                        .sel_apps
                        .iter()
                        .any(|(application, candidate, argument)| {
                            candidate == selector
                                && required_terms.contains(application)
                                && self.index.get(argument).is_some_and(|&term| {
                                    self.class_of.get(term).copied() == Some(root)
                                })
                        }))
                .then_some(index)
            })
            .collect()
    }

    /// Pick a scalar field whose candidate will survive committed-selector
    /// installation. `apply_committed_fields` overwrites every observed scalar
    /// field after candidate generation; varying such a field forever would
    /// collapse every candidate to the same value and mask a later free array
    /// field. The caller precharges the full field-by-selector scan.
    pub(super) fn precharged_free_scalar_variation_fields(
        &self,
        root: usize,
        fields: &[(String, Sort)],
    ) -> Vec<usize> {
        let Some(required_terms) = self.datatype_array_required_terms.as_ref() else {
            return Vec::new();
        };
        fields
            .iter()
            .enumerate()
            .filter_map(|(index, (selector, sort))| {
                let variable = matches!(
                    sort,
                    Sort::Bool | Sort::Int | Sort::Real | Sort::String | Sort::BitVec(_)
                );
                let overwritten =
                    self.sel_apps
                        .iter()
                        .any(|(application, candidate, argument)| {
                            required_terms.contains(application)
                                && candidate == selector
                                && self.index.get(argument).is_some_and(|&term| {
                                    self.class_of.get(term).copied() == Some(root)
                                })
                        });
                (variable && !overwritten).then_some(index)
            })
            .collect()
    }

    /// Keep a sole-constructor inference on the free-candidate path only when
    /// an existing datatype disequality actually needs another value and one
    /// selector-unobserved field has a constructive scalar or finite-function
    /// family. Explicit authored constructor applications never call this
    /// helper. A positive tester may call it because the tester fixes the
    /// constructor tag, not otherwise-unobserved field values.
    pub(super) fn inferred_constructor_needs_free_choice(
        &mut self,
        root: usize,
        ctor: &str,
    ) -> bool {
        if !self
            .diseq
            .get(&root)
            .is_some_and(|neighbors| !neighbors.is_empty())
        {
            return false;
        }
        let Some(fields) = self.exec.ctx.constructor_selector_info(ctor) else {
            return false;
        };
        if !self
            .work_budget
            .charge_field_scans(fields.len(), self.sel_apps.len(), 0)
        {
            return false;
        }
        !self
            .precharged_free_scalar_variation_fields(root, fields)
            .is_empty()
            || !self
                .precharged_free_array_variation_fields(root, fields)
                .is_empty()
    }

    /// Return variant zero immediately after the constructor's base candidate.
    /// Constants vary first. A finite element domain then continues with one
    /// non-default point at each exact index, which is extensionally distinct
    /// from every constant whenever the index domain has at least two values.
    pub(super) fn variable_array_fields_candidate(
        &self,
        ctor: &str,
        fields: &[(String, Sort)],
        variable_fields: &[usize],
        ordinal: usize,
    ) -> Option<ModelValue> {
        let mut remainder = ordinal;
        let mut args = fields
            .iter()
            .map(|(_, sort)| self.base_default(sort, &mut Vec::new()))
            .collect::<Option<Vec<_>>>()?;
        for &index in variable_fields {
            let Sort::Array(array_sort) = &fields.get(index)?.1 else {
                return None;
            };
            let variants = finite_function_variant_count(array_sort)?;
            let radix = variants.checked_add(1)?;
            let digit = remainder % radix;
            remainder /= radix;
            if digit != 0 {
                *args.get_mut(index)? = ModelValue::Array(Box::new(finite_function_variant(
                    array_sort,
                    digit.checked_sub(1)?,
                )?));
            }
        }
        if remainder != 0 {
            return None;
        }
        Some(ModelValue::Datatype {
            ctor: ctor.to_string(),
            args,
        })
    }

    pub(super) fn free_array_field_product(
        &self,
        fields: &[(String, Sort)],
        variable_fields: &[usize],
    ) -> Option<usize> {
        variable_fields.iter().try_fold(1usize, |product, &index| {
            let Sort::Array(array_sort) = &fields.get(index)?.1 else {
                return None;
            };
            product.checked_mul(finite_function_variant_count(array_sort)?.checked_add(1)?)
        })
    }
}

fn finite_function_variant_count(sort: &ay_core::ArraySort) -> Option<usize> {
    let constants = nondefault_scalar_count(&sort.element_sort)?;
    if constants >= MAX_FREE_ARRAY_VARIANTS {
        return Some(MAX_FREE_ARRAY_VARIANTS);
    }
    if scalar_at(&sort.element_sort, 1).is_none() {
        return Some(constants);
    }
    let indices = scalar_domain_count(&sort.index_sort, MAX_FREE_ARRAY_VARIANTS)?;
    let points = (indices >= 2).then_some(indices).unwrap_or(0);
    constants
        .checked_add(points)
        .map(|count| count.min(MAX_FREE_ARRAY_VARIANTS))
}

fn scalar_domain_count(sort: &Sort, limit: usize) -> Option<usize> {
    match sort {
        Sort::Bool => Some(2.min(limit)),
        Sort::BitVec(bitvec) if bitvec.width >= usize::BITS => Some(limit),
        Sort::BitVec(bitvec) => Some((1usize.checked_shl(bitvec.width)?).min(limit)),
        Sort::Int | Sort::Real | Sort::String => Some(limit),
        _ => None,
    }
}

fn finite_function_variant(sort: &ay_core::ArraySort, variant: usize) -> Option<ArrayValue> {
    if variant >= finite_function_variant_count(sort)? {
        return None;
    }
    let base = scalar_at(&sort.element_sort, 0)?;
    let constant_variants = nondefault_scalar_count(&sort.element_sort)?;
    if variant < constant_variants {
        return Some(ArrayValue {
            default: scalar_at(&sort.element_sort, variant.checked_add(1)?)?,
            store: Vec::new(),
        });
    }

    // On a singleton index domain, this point function equals `const e1`.
    // Requiring a second exact index rules out that only possible alias.
    scalar_at(&sort.index_sort, 1)?;
    let index_ordinal = variant.checked_sub(constant_variants)?;
    let key = scalar_at(&sort.index_sort, index_ordinal)?;
    let nondefault = scalar_at(&sort.element_sort, 1)?;
    Some(ArrayValue {
        default: base,
        store: vec![(key, nondefault)],
    })
}

/// Number of non-base scalar constants exposed by the bounded family. `None`
/// means this scalar sort is outside the exact finite-function fragment.
fn nondefault_scalar_count(sort: &Sort) -> Option<usize> {
    match sort {
        Sort::Bool => Some(1),
        Sort::BitVec(bitvec) => {
            if bitvec.width == 0 {
                return Some(0);
            }
            let count = if bitvec.width >= usize::BITS {
                MAX_FREE_ARRAY_VARIANTS
            } else {
                (1usize << bitvec.width)
                    .saturating_sub(1)
                    .min(MAX_FREE_ARRAY_VARIANTS)
            };
            Some(count)
        }
        Sort::Int | Sort::Real | Sort::String => Some(MAX_FREE_ARRAY_VARIANTS),
        _ => None,
    }
}

/// Deterministic, injective scalar enumeration over the bounded ordinals used
/// above. Finite Bool/BV domains return `None` exactly at exhaustion.
fn scalar_at(sort: &Sort, ordinal: usize) -> Option<ModelValue> {
    let ordinal = u64::try_from(ordinal).ok()?;
    match sort {
        Sort::Bool => match ordinal {
            0 => Some(ModelValue::Bool(false)),
            1 => Some(ModelValue::Bool(true)),
            _ => None,
        },
        Sort::Int => Some(ModelValue::Int(BigInt::from(ordinal))),
        Sort::Real => Some(ModelValue::Real(BigRational::from_integer(BigInt::from(
            ordinal,
        )))),
        Sort::String => Some(ModelValue::Str(if ordinal == 0 {
            String::new()
        } else {
            format!("v{ordinal}")
        })),
        Sort::BitVec(bitvec) => {
            if bitvec.width < u64::BITS && ordinal >= (1_u64 << bitvec.width) {
                return None;
            }
            Some(ModelValue::bitvec(BigInt::from(ordinal), bitvec.width))
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeSet;

    fn bool_at(array: &ArrayValue, key: &ModelValue) -> bool {
        let value = array
            .store
            .iter()
            .rev()
            .find(|(candidate, _)| {
                super::super::dt_canonical_string(candidate)
                    == super::super::dt_canonical_string(key)
            })
            .map_or(&array.default, |(_, value)| value);
        matches!(value, ModelValue::Bool(true))
    }

    fn finite_bool_signatures(sort: &ay_core::ArraySort, keys: &[ModelValue]) -> Vec<Vec<bool>> {
        let base = ArrayValue {
            default: ModelValue::Bool(false),
            store: Vec::new(),
        };
        std::iter::once(base)
            .chain(
                (0..MAX_FREE_ARRAY_VARIANTS)
                    .map_while(|variant| finite_function_variant(sort, variant)),
            )
            .map(|array| keys.iter().map(|key| bool_at(&array, key)).collect())
            .collect()
    }

    #[test]
    fn bool_index_family_is_exactly_four_functions() {
        let sort = ay_core::ArraySort::new(Sort::Bool, Sort::Bool);
        let signatures =
            finite_bool_signatures(&sort, &[ModelValue::Bool(false), ModelValue::Bool(true)]);
        assert_eq!(signatures.len(), 4);
        assert_eq!(signatures.iter().cloned().collect::<BTreeSet<_>>().len(), 4);
    }

    #[test]
    fn zero_width_bv_index_does_not_duplicate_constant() {
        let sort = ay_core::ArraySort::new(Sort::bitvec(0), Sort::Bool);
        assert!(finite_function_variant(&sort, 0).is_some());
        assert!(finite_function_variant(&sort, 1).is_none());
    }

    #[test]
    fn bv1_index_family_is_exactly_four_functions() {
        let sort = ay_core::ArraySort::new(Sort::bitvec(1), Sort::Bool);
        let signatures = finite_bool_signatures(
            &sort,
            &[
                ModelValue::bitvec(BigInt::from(0), 1),
                ModelValue::bitvec(BigInt::from(1), 1),
            ],
        );
        assert_eq!(signatures.len(), 4);
        assert_eq!(signatures.iter().cloned().collect::<BTreeSet<_>>().len(), 4);
    }

    #[test]
    fn wide_bv_index_family_is_bounded_without_shift_wrap() {
        let sort = ay_core::ArraySort::new(Sort::bitvec(128), Sort::Bool);
        assert!(finite_function_variant(&sort, MAX_FREE_ARRAY_VARIANTS - 1).is_some());
        assert!(finite_function_variant(&sort, MAX_FREE_ARRAY_VARIANTS).is_none());
    }

    #[test]
    fn int_bool_family_starts_with_const_then_unique_points() {
        let sort = ay_core::ArraySort::new(Sort::Int, Sort::Bool);
        let first = finite_function_variant(&sort, 0).expect("const true");
        let second = finite_function_variant(&sort, 1).expect("point at zero");
        let third = finite_function_variant(&sort, 2).expect("point at one");
        assert!(first.store.is_empty());
        assert_ne!(
            super::super::dt_canonical_string(&ModelValue::Array(Box::new(first))),
            super::super::dt_canonical_string(&ModelValue::Array(Box::new(second.clone())))
        );
        assert_ne!(
            super::super::dt_canonical_string(&ModelValue::Array(Box::new(second))),
            super::super::dt_canonical_string(&ModelValue::Array(Box::new(third)))
        );
    }
}

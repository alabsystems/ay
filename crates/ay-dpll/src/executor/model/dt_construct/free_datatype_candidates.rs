// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded candidate construction for free datatype classes.

use ay_core::Sort;
use ay_model_check::ModelValue;
use num_bigint::BigInt;
use num_rational::BigRational;

use super::freshness::FreeDatatypeFreshness;
use super::{dt_canonical_string, exact_datatype_sort_name, DtBuilder};

impl DtBuilder<'_> {
    /// Construct a FREE class: the well-founded default, distinct from every
    /// already-constructed disequality neighbour and avoiding excluded root
    /// constructors.
    pub(super) fn construct_free(
        &mut self,
        root: usize,
        excluded: &[String],
        path: &mut Vec<usize>,
        fuel: u32,
    ) -> Option<ModelValue> {
        let sort_name = self.class_sort_name(root)?;
        let mut used = FreeDatatypeFreshness::new();
        if let Some(neighbors) = self.diseq.get(&root) {
            for nb in neighbors.clone() {
                if let Some(Some(v)) = self.values.get(&nb) {
                    if !self.work_budget.charge_render(v) {
                        return None;
                    }
                    let canonical = dt_canonical_string(v);
                    if !self.work_budget.charge_bytes(canonical.len()) {
                        return None;
                    }
                    used.record(v, &canonical)?;
                }
            }
        }
        let budget = used.len() + 16;
        for k in 0..budget {
            if !self.work_budget.charge_candidate(k) {
                return None;
            }
            let cand = self.free_candidate(root, &sort_name, k, excluded)?;
            // Honor pinned fields (#dt-pin-selector). `free_candidate` fills a
            // constructor's scalar fields with base defaults; when a member of
            // this class has a selector application `(sel member)` the raw model
            // COMMITTED a value to (an asserted `(= (sel member) v)`), that field
            // is pinned and the base default would falsify the assertion. This
            // is exactly the case where distinctness forces a free class onto a
            // non-base constructor (`x=nil` taken, so `y` must be `cons ..`): the
            // pinned `hd` must be honored, not defaulted to 0 (GAP-2).
            // Datatype fields observed through a datatype-sorted selector
            // application recurse into that application's class, so a nested
            // chain (`(hd (tl x)) = 3` under a `cons` candidate for `x`'s
            // class) projects the same value the inner class pins
            // (#dt-free-selector-funcong).
            let cand = self.finish_constructed_datatype(root, cand, path, fuel)?;
            if self.work_budget.exhausted() {
                return None;
            }
            if !self.work_budget.charge_render(&cand) {
                return None;
            }
            let canonical = dt_canonical_string(&cand);
            if used.is_fresh(&cand, &canonical)? {
                return Some(cand);
            }
        }
        None
    }

    /// The k-th candidate value of datatype `dt_name` (deterministic,
    /// pairwise-distinct enumeration), skipping excluded root constructors.
    fn free_candidate(
        &mut self,
        root: usize,
        dt_name: &str,
        k: usize,
        excluded: &[String],
    ) -> Option<ModelValue> {
        let ctors = self.exec.ctx.datatype_constructors(dt_name)?;
        if !self
            .work_budget
            .charge_constructor_filter(ctors.len(), excluded.len())
        {
            return None;
        }
        let allowed: Vec<&String> = ctors.iter().filter(|c| !excluded.contains(c)).collect();
        if allowed.is_empty() {
            return None;
        }
        // Prefer well-founded ordering: nullary constructors first.
        let mut nullary: Vec<&String> = Vec::new();
        let mut non_nullary: Vec<&String> = Vec::new();
        for c in &allowed {
            if self
                .exec
                .ctx
                .constructor_selector_info(c)
                .map_or(true, |f| f.is_empty())
            {
                nullary.push(c);
            } else {
                non_nullary.push(c);
            }
        }
        if k < nullary.len() {
            return Some(ModelValue::Datatype {
                ctor: nullary[k].clone(),
                args: Vec::new(),
            });
        }
        let mut j = k - nullary.len();
        // A constructor can be perfectly inhabitable without carrying one of
        // the variation sources below.  In particular, an array/sequence field
        // has a canonical extensional default even though this completion lane
        // deliberately does not invent distinct array/sequence values.  Give
        // every such constructor its one exact base candidate before declaring
        // the finite enumeration exhausted.  Different constructors remain
        // pairwise-distinct by constructor identity; a second class requiring
        // another value of the same constructor still fails closed.
        for c in &non_nullary {
            let fields = self.exec.ctx.constructor_selector_info(c)?;
            let args = fields
                .iter()
                .map(|(_, field_sort)| self.base_default(field_sort, &mut Vec::new()))
                .collect::<Option<Vec<_>>>();
            let Some(args) = args else {
                continue;
            };
            if j == 0 {
                return Some(ModelValue::Datatype {
                    ctor: (*c).clone(),
                    args,
                });
            }
            j -= 1;
        }
        // Variation constructor: prefer one with a directly-recursive field
        // (unbounded depth chain), else one with a variable scalar field.
        let mut visited = Vec::new();
        for c in &non_nullary {
            let fields = self.exec.ctx.constructor_selector_info(c)?;
            // Directly-recursive field?
            if let Some(rec_idx) = fields
                .iter()
                .position(|(_, fs)| exact_datatype_sort_name(fs) == Some(dt_name))
            {
                let base =
                    self.base_default(&Sort::Uninterpreted(dt_name.to_string()), &mut visited)?;
                let mut chain = base;
                for _ in 0..=j {
                    let mut args = Vec::with_capacity(fields.len());
                    for (i, (_, fs)) in fields.iter().enumerate() {
                        if i == rec_idx {
                            args.push(chain.clone());
                        } else {
                            args.push(self.base_default(fs, &mut Vec::new())?);
                        }
                    }
                    chain = ModelValue::Datatype {
                        ctor: (*c).clone(),
                        args,
                    };
                }
                return Some(chain);
            }
            if !self
                .work_budget
                .charge_field_scans(fields.len(), self.sel_apps.len(), 0)
            {
                return None;
            }
            // Variable scalar fields? Skip fields that committed selector
            // installation will overwrite, or they hide every later source of
            // real variation (notably the Vec/Slice data array after equal
            // ptr/len/cap fields). Any unbounded scalar is sufficient by
            // itself. Otherwise enumerate the full finite Bool/BV product,
            // excluding its all-default value (already emitted above), before
            // falling through to the array family.
            let scalar_fields = self.precharged_free_scalar_variation_fields(root, fields);
            if let Some(&var_idx) = scalar_fields
                .iter()
                .find(|&&index| matches!(fields[index].1, Sort::Int | Sort::Real | Sort::String))
            {
                return self.variable_scalar_candidate(c, fields, var_idx, j.checked_add(1)?);
            }
            let finite_fields: Vec<usize> = scalar_fields
                .into_iter()
                .filter(|&index| matches!(fields[index].1, Sort::Bool | Sort::BitVec(_)))
                .collect();
            if !finite_fields.is_empty() {
                let ordinal = j.checked_add(1)?;
                if let Some(candidate) =
                    self.variable_finite_scalar_candidate(c, fields, &finite_fields, ordinal)
                {
                    return Some(candidate);
                }
                let scalar_variants = self
                    .finite_scalar_product(&finite_fields, fields)?
                    .checked_sub(1)?;
                j = j.checked_sub(scalar_variants)?;
            }
            // Variable finite-function field? The base constant array was
            // emitted above; this bounded family supplies pairwise-distinct
            // exact arrays without inventing an opaque carrier.
            let array_fields = self.precharged_free_array_variation_fields(root, fields);
            if !array_fields.is_empty() {
                let ordinal = j.checked_add(1)?;
                if let Some(candidate) =
                    self.variable_array_fields_candidate(c, fields, &array_fields, ordinal)
                {
                    return Some(candidate);
                }
                let array_variants = self
                    .free_array_field_product(fields, &array_fields)?
                    .checked_sub(1)?;
                j = j.checked_sub(array_variants)?;
            }
        }
        // Finite enumeration exhausted.
        None
    }

    fn variable_scalar_candidate(
        &self,
        ctor: &str,
        fields: &[(String, Sort)],
        var_idx: usize,
        variant: usize,
    ) -> Option<ModelValue> {
        let (_, sort) = &fields[var_idx];
        let varied = match sort {
            Sort::Int => ModelValue::Int(BigInt::from(variant as u64)),
            Sort::Real => ModelValue::Real(BigRational::from(BigInt::from(variant as u64))),
            Sort::String => ModelValue::Str(format!("v{variant}")),
            Sort::BitVec(bv) => {
                // Only 2^width distinct values exist.
                if bv.width < 63 && (variant as u64) >= (1u64 << bv.width) {
                    return None;
                }
                ModelValue::bitvec(BigInt::from(variant as u64), bv.width)
            }
            _ => return None,
        };
        let mut args = Vec::with_capacity(fields.len());
        for (index, (_, field_sort)) in fields.iter().enumerate() {
            if index == var_idx {
                args.push(varied.clone());
            } else {
                args.push(self.base_default(field_sort, &mut Vec::new())?);
            }
        }
        Some(ModelValue::Datatype {
            ctor: ctor.to_string(),
            args,
        })
    }

    /// Mixed-radix enumeration of all finite selector-unobserved scalar
    /// fields. `ordinal == 0` is the base value emitted separately; callers
    /// start at one. A product larger than `usize` still accepts every bounded
    /// ordinal this constructor loop can request without computing the product.
    fn variable_finite_scalar_candidate(
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
            let sort = &fields.get(index)?.1;
            let value = match sort {
                Sort::Bool => {
                    let digit = remainder % 2;
                    remainder /= 2;
                    ModelValue::Bool(digit != 0)
                }
                Sort::BitVec(bitvec) if bitvec.width >= usize::BITS => {
                    let digit = remainder;
                    remainder = 0;
                    ModelValue::bitvec(BigInt::from(u64::try_from(digit).ok()?), bitvec.width)
                }
                Sort::BitVec(bitvec) => {
                    let radix = 1usize.checked_shl(bitvec.width)?;
                    let digit = remainder % radix;
                    remainder /= radix;
                    ModelValue::bitvec(BigInt::from(u64::try_from(digit).ok()?), bitvec.width)
                }
                _ => return None,
            };
            *args.get_mut(index)? = value;
        }
        if remainder != 0 {
            return None;
        }
        Some(ModelValue::Datatype {
            ctor: ctor.to_string(),
            args,
        })
    }

    fn finite_scalar_product(
        &self,
        variable_fields: &[usize],
        fields: &[(String, Sort)],
    ) -> Option<usize> {
        variable_fields.iter().try_fold(1usize, |product, &index| {
            let radix = match &fields.get(index)?.1 {
                Sort::Bool => 2,
                Sort::BitVec(bitvec) => 1usize.checked_shl(bitvec.width)?,
                _ => return None,
            };
            product.checked_mul(radix)
        })
    }
}

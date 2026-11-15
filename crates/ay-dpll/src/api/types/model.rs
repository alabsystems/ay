// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model and verified model types.

use ay_core::kani_compat::DetHashMap as HashMap;

use num_bigint::BigInt;
use num_rational::BigRational;

use super::ModelValue;

/// A satisfying model mapping variables to values
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Model {
    pub(crate) int_values: HashMap<String, BigInt>,
    pub(crate) real_values: HashMap<String, BigRational>,
    pub(crate) bool_values: HashMap<String, bool>,
    pub(crate) bv_values: HashMap<String, (BigInt, u32)>,
    pub(crate) string_values: HashMap<String, String>,
    pub(crate) fp_values: HashMap<String, ModelValue>,
    pub(crate) field_values: HashMap<String, ModelValue>,
    pub(crate) seq_values: HashMap<String, ModelValue>,
    pub(crate) array_values: HashMap<String, ModelValue>,
    pub(crate) datatype_values: HashMap<String, ModelValue>,
    pub(crate) uninterpreted_values: HashMap<String, String>,
}

impl Model {
    /// Construct an empty model with no variable assignments.
    ///
    /// AY's [`Model`] value maps are crate-private, so an out-of-crate consumer
    /// (notably the Z3-compat FFI's `Z3_mk_model`, which returns a caller-owned
    /// model to be populated with `Z3_add_const_interp` / `Z3_add_func_interp`)
    /// cannot build one directly. This exposes the empty constructor.
    #[must_use]
    pub fn empty() -> Self {
        Self {
            int_values: HashMap::default(),
            real_values: HashMap::default(),
            bool_values: HashMap::default(),
            bv_values: HashMap::default(),
            string_values: HashMap::default(),
            fp_values: HashMap::default(),
            field_values: HashMap::default(),
            seq_values: HashMap::default(),
            array_values: HashMap::default(),
            datatype_values: HashMap::default(),
            uninterpreted_values: HashMap::default(),
        }
    }

    /// Keep only the assignments whose name satisfies `keep`.
    ///
    /// Restriction never changes a retained value, so a restricted model still
    /// satisfies every formula that mentions only retained names. The Z3 C API
    /// uses this to publish, for one solver handle, exactly the symbols of that
    /// handle's goal: the engine that produced the model is shared by every
    /// handle of a context and prints every symbol declared on it.
    pub fn retain_names(&mut self, keep: impl Fn(&str) -> bool) {
        self.int_values.retain(|name, _| keep(name));
        self.real_values.retain(|name, _| keep(name));
        self.bool_values.retain(|name, _| keep(name));
        self.bv_values.retain(|name, _| keep(name));
        self.string_values.retain(|name, _| keep(name));
        self.fp_values.retain(|name, _| keep(name));
        self.field_values.retain(|name, _| keep(name));
        self.seq_values.retain(|name, _| keep(name));
        self.array_values.retain(|name, _| keep(name));
        self.datatype_values.retain(|name, _| keep(name));
        self.uninterpreted_values.retain(|name, _| keep(name));
    }

    /// Rename assignments: `rename(name)` is the new name, or `None` to keep
    /// it. Values are unchanged. The Z3 C API uses this to carry a model into
    /// another context, whose declarations have identities of their own.
    pub fn rename_names(&mut self, rename: impl Fn(&str) -> Option<String>) {
        fn renamed<V>(map: &mut HashMap<String, V>, rename: &impl Fn(&str) -> Option<String>) {
            let old = std::mem::take(map);
            for (name, value) in old {
                let name = rename(&name).unwrap_or(name);
                map.insert(name, value);
            }
        }
        renamed(&mut self.int_values, &rename);
        renamed(&mut self.real_values, &rename);
        renamed(&mut self.bool_values, &rename);
        renamed(&mut self.bv_values, &rename);
        renamed(&mut self.string_values, &rename);
        renamed(&mut self.fp_values, &rename);
        renamed(&mut self.field_values, &rename);
        renamed(&mut self.seq_values, &rename);
        renamed(&mut self.array_values, &rename);
        renamed(&mut self.datatype_values, &rename);
        renamed(&mut self.uninterpreted_values, &rename);
    }

    /// Integer variable's exact arbitrary-precision value.
    pub fn int_val(&self, name: &str) -> Option<&BigInt> {
        self.int_values.get(name)
    }

    /// Deprecated: use [`int_val`](Self::int_val) instead.
    pub fn get_int(&self, name: &str) -> Option<&BigInt> {
        self.int_val(name)
    }

    /// Integer variable's value as i64 (returns None on overflow).
    pub fn int_val_i64(&self, name: &str) -> Option<i64> {
        use num_traits::ToPrimitive;
        self.int_values.get(name).and_then(ToPrimitive::to_i64)
    }

    /// Real variable's exact arbitrary-precision rational value.
    pub fn real_val(&self, name: &str) -> Option<&BigRational> {
        self.real_values.get(name)
    }

    /// Real variable's value as f64 (precision loss for exact rationals).
    pub fn real_val_f64(&self, name: &str) -> Option<f64> {
        use num_traits::ToPrimitive;
        self.real_values.get(name).and_then(ToPrimitive::to_f64)
    }

    /// Boolean variable's value.
    pub fn bool_val(&self, name: &str) -> Option<bool> {
        self.bool_values.get(name).copied()
    }

    /// Bitvector variable's value as (value, width).
    pub fn bv_val(&self, name: &str) -> Option<(BigInt, u32)> {
        self.bv_values.get(name).cloned()
    }

    /// String variable's value.
    pub fn string_val(&self, name: &str) -> Option<&str> {
        self.string_values.get(name).map(String::as_str)
    }

    /// Deprecated: use [`string_val`](Self::string_val) instead.
    pub fn get_string(&self, name: &str) -> Option<&str> {
        self.string_val(name)
    }

    /// Floating-point variable's value as a [`ModelValue`].
    pub fn fp_val(&self, name: &str) -> Option<&ModelValue> {
        self.fp_values.get(name)
    }

    /// Prime-field variable's exact value, including field identity.
    pub fn finite_field_val(&self, name: &str) -> Option<&ModelValue> {
        self.field_values.get(name)
    }

    /// Sequence variable's value as a [`ModelValue`].
    pub fn seq_val(&self, name: &str) -> Option<&ModelValue> {
        self.seq_values.get(name)
    }

    /// Array variable's value as a [`ModelValue`].
    pub fn array_val(&self, name: &str) -> Option<&ModelValue> {
        self.array_values.get(name)
    }

    /// Datatype variable's value as a [`ModelValue`].
    pub fn datatype_val(&self, name: &str) -> Option<&ModelValue> {
        self.datatype_values.get(name)
    }

    /// Uninterpreted sort variable's value (symbolic element name).
    pub fn uninterpreted_val(&self, name: &str) -> Option<&str> {
        self.uninterpreted_values.get(name).map(String::as_str)
    }

    /// Returns an iterator over all integer variable names and values
    pub fn iter_ints(&self) -> impl Iterator<Item = (&str, &BigInt)> {
        self.int_values.iter().map(|(k, v)| (k.as_str(), v))
    }

    /// Returns an iterator over all real variable names and values
    pub fn iter_reals(&self) -> impl Iterator<Item = (&str, &BigRational)> {
        self.real_values.iter().map(|(k, v)| (k.as_str(), v))
    }

    /// Returns an iterator over all boolean variable names and values
    pub fn iter_bools(&self) -> impl Iterator<Item = (&str, bool)> {
        self.bool_values.iter().map(|(k, v)| (k.as_str(), *v))
    }

    /// Returns an iterator over all bitvector variable names and values
    pub fn iter_bvs(&self) -> impl Iterator<Item = (&str, &(BigInt, u32))> {
        self.bv_values.iter().map(|(k, v)| (k.as_str(), v))
    }

    /// Returns an iterator over all string variable names and values
    pub fn iter_strings(&self) -> impl Iterator<Item = (&str, &str)> {
        self.string_values
            .iter()
            .map(|(k, v)| (k.as_str(), v.as_str()))
    }

    /// Returns an iterator over all floating-point variable names and values
    pub fn iter_fps(&self) -> impl Iterator<Item = (&str, &ModelValue)> {
        self.fp_values.iter().map(|(k, v)| (k.as_str(), v))
    }

    /// Iterate exact prime-field model values.
    pub fn iter_finite_fields(&self) -> impl Iterator<Item = (&str, &ModelValue)> {
        self.field_values.iter().map(|(k, v)| (k.as_str(), v))
    }

    /// Returns an iterator over all sequence variable names and values
    pub fn iter_seqs(&self) -> impl Iterator<Item = (&str, &ModelValue)> {
        self.seq_values.iter().map(|(k, v)| (k.as_str(), v))
    }

    /// Returns an iterator over all array variable names and values
    pub fn iter_arrays(&self) -> impl Iterator<Item = (&str, &ModelValue)> {
        self.array_values.iter().map(|(k, v)| (k.as_str(), v))
    }

    /// Returns an iterator over all datatype variable names and values
    pub fn iter_datatypes(&self) -> impl Iterator<Item = (&str, &ModelValue)> {
        self.datatype_values.iter().map(|(k, v)| (k.as_str(), v))
    }

    /// Returns an iterator over all uninterpreted sort variable names and values
    pub fn iter_uninterpreteds(&self) -> impl Iterator<Item = (&str, &str)> {
        self.uninterpreted_values
            .iter()
            .map(|(k, v)| (k.as_str(), v.as_str()))
    }

    /// Returns an iterator over all variable names and values as unified [`ModelValue`]s.
    ///
    /// Iterates across all sort maps in a fixed order: Bool, Int, Real, BitVec,
    /// String, FloatingPoint, Seq, Array, Datatype, Uninterpreted.
    pub fn iter_all(&self) -> impl Iterator<Item = (&str, ModelValue)> {
        self.iter_bools()
            .map(|(name, value)| (name, ModelValue::Bool(value)))
            .chain(
                self.iter_ints()
                    .map(|(name, value)| (name, ModelValue::Int(value.clone()))),
            )
            .chain(
                self.iter_reals()
                    .map(|(name, value)| (name, ModelValue::Real(value.clone()))),
            )
            .chain(self.iter_bvs().map(|(name, (value, width))| {
                (
                    name,
                    ModelValue::BitVec {
                        value: value.clone(),
                        width: *width,
                    },
                )
            }))
            .chain(
                self.iter_strings()
                    .map(|(name, value)| (name, ModelValue::String(value.to_string()))),
            )
            .chain(self.iter_fps().map(|(name, value)| (name, value.clone())))
            .chain(
                self.iter_finite_fields()
                    .map(|(name, value)| (name, value.clone())),
            )
            .chain(self.iter_seqs().map(|(name, value)| (name, value.clone())))
            .chain(
                self.iter_arrays()
                    .map(|(name, value)| (name, value.clone())),
            )
            .chain(
                self.iter_datatypes()
                    .map(|(name, value)| (name, value.clone())),
            )
            .chain(
                self.iter_uninterpreteds()
                    .map(|(name, value)| (name, ModelValue::Uninterpreted(value.to_string()))),
            )
    }

    /// Returns an iterator over all variable names and values.
    ///
    /// Alias for [`iter_all`](Self::iter_all).
    pub fn iter(&self) -> impl Iterator<Item = (&str, ModelValue)> {
        self.iter_all()
    }

    /// Returns an iterator over all variable names in the model.
    ///
    /// Uses the same sort order as [`iter_all`](Self::iter_all).
    pub fn names(&self) -> impl Iterator<Item = &str> {
        self.bool_values
            .keys()
            .map(String::as_str)
            .chain(self.int_values.keys().map(String::as_str))
            .chain(self.real_values.keys().map(String::as_str))
            .chain(self.bv_values.keys().map(String::as_str))
            .chain(self.string_values.keys().map(String::as_str))
            .chain(self.fp_values.keys().map(String::as_str))
            .chain(self.field_values.keys().map(String::as_str))
            .chain(self.seq_values.keys().map(String::as_str))
            .chain(self.array_values.keys().map(String::as_str))
            .chain(self.datatype_values.keys().map(String::as_str))
            .chain(self.uninterpreted_values.keys().map(String::as_str))
    }

    /// Returns true if the model is empty (no variable assignments)
    pub fn is_empty(&self) -> bool {
        self.int_values.is_empty()
            && self.real_values.is_empty()
            && self.bool_values.is_empty()
            && self.bv_values.is_empty()
            && self.string_values.is_empty()
            && self.fp_values.is_empty()
            && self.field_values.is_empty()
            && self.seq_values.is_empty()
            && self.array_values.is_empty()
            && self.datatype_values.is_empty()
            && self.uninterpreted_values.is_empty()
    }

    /// Look up a variable by name across all sort maps, returning its value as a [`ModelValue`].
    ///
    /// This searches booleans, integers, reals, bitvectors, strings, floating-point,
    /// sequences, arrays, datatypes, and uninterpreted sorts in that order.
    pub fn value_by_name(&self, name: &str) -> Option<ModelValue> {
        if let Some(v) = self.bool_values.get(name) {
            return Some(ModelValue::Bool(*v));
        }
        if let Some(v) = self.int_values.get(name) {
            return Some(ModelValue::Int(v.clone()));
        }
        if let Some(v) = self.real_values.get(name) {
            return Some(ModelValue::Real(v.clone()));
        }
        if let Some((value, width)) = self.bv_values.get(name) {
            return Some(ModelValue::BitVec {
                value: value.clone(),
                width: *width,
            });
        }
        if let Some(v) = self.string_values.get(name) {
            return Some(ModelValue::String(v.clone()));
        }
        if let Some(v) = self.field_values.get(name) {
            return Some(v.clone());
        }
        if let Some(v) = self.fp_values.get(name) {
            return Some(v.clone());
        }
        if let Some(v) = self.seq_values.get(name) {
            return Some(v.clone());
        }
        if let Some(v) = self.array_values.get(name) {
            return Some(v.clone());
        }
        if let Some(v) = self.datatype_values.get(name) {
            return Some(v.clone());
        }
        if let Some(v) = self.uninterpreted_values.get(name) {
            return Some(ModelValue::Uninterpreted(v.clone()));
        }
        None
    }

    /// Returns the total number of variable assignments in the model
    #[must_use]
    pub fn len(&self) -> usize {
        self.int_values.len()
            + self.real_values.len()
            + self.bool_values.len()
            + self.bv_values.len()
            + self.string_values.len()
            + self.fp_values.len()
            + self.field_values.len()
            + self.seq_values.len()
            + self.array_values.len()
            + self.datatype_values.len()
            + self.uninterpreted_values.len()
    }
}

/// A verified model that can only be constructed within ay-dpll from a
/// validated solver state.
///
/// Guarantees that the enclosed model was extracted from a solver that
/// returned `Sat` through the verified solve pipeline. Can only be constructed
/// within the `ay-dpll` crate via `from_validated`.
///
/// Part of #5748: structural verification invariant Phase 3.
#[derive(Debug, Clone, PartialEq, Eq)]
#[must_use = "verified models should not be discarded"]
pub struct VerifiedModel {
    model: Model,
}

impl VerifiedModel {
    /// Wrap a validated model.
    ///
    /// Only callable within ay-dpll. The caller MUST have verified that
    /// the model came from a Sat result in the executor's validated pipeline.
    pub(crate) fn from_validated(model: Model) -> Self {
        Self { model }
    }

    /// Get the underlying model.
    #[inline]
    pub fn model(&self) -> &Model {
        &self.model
    }

    /// Consume and return the inner model.
    #[inline]
    pub fn into_inner(self) -> Model {
        self.model
    }
}

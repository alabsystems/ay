//! Mapping of variables to values.

use std::fmt::Display;

use crate::{prelude::*, substitution::Substitutable};

/// Data structure to store mapping from [`VarIdx`] to [`VarType`].
#[derive(Debug, Default, Clone)]
pub struct Assignment<V> {
    pub assignment: Vec<V>,
}

impl<V> Assignment<V>
where
    V: VarType,
{
    /// Initialize a new [`Assignment`] with specific `size` where all entries are set to the default value of [`VarType`].
    #[inline]
    pub fn with_size(size: usize) -> Self {
        Assignment::<V> {
            assignment: vec![Default::default(); size],
        }
    }

    /// Resizes the [`Assignment`] to the given `new_len`.
    ///
    /// If `new_len` is smaller than the current `len` of `Assignment`, the [`Assignment`] is truncated to `new_len`. If `new_len` is larger than the current `len` of [`Assignment`], then [`Assignment`] is increased up to `new_len` and filled with the default values for [`VarType`], but the entries up to the current length are left unchanged.
    #[inline]
    pub fn resize(&mut self, new_len: usize) {
        self.assignment.resize(new_len, Default::default());
    }

    /// Set variable at index `idx` to `value`.
    #[inline]
    pub fn set_value(&mut self, idx: VarIdx, value: V::Value) {
        self.assignment[idx].set_value(value);
    }

    /// Get the value of the variable at index `idx`.
    #[inline]
    pub fn get_value(&self, idx: VarIdx) -> V::Value {
        self.assignment[idx].get_value()
    }

    /// Set a value by using a [`Lit`]. Hence, if [`Lit`] is negated, then the value assigned to its variable is negated.
    #[inline]
    pub fn set_lit_value(&mut self, lit: Lit, value: V::Value) {
        if lit.is_negated() {
            self.assignment[lit.get_var()].set_value(value.negate());
        } else {
            self.assignment[lit.get_var()].set_value(value);
        }
    }

    /// Set a value by literal. Hence, if the literal is negated, then value assigned to its variable is negated.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the [`Assignment`] has a large enough size, so that the variable index of `lit` is at most that size.
    ///
    /// Using a `lit` with variable index of at least the size of [`Assignment`] is undefined behaviour.
    #[inline]
    pub unsafe fn set_lit_value_unchecked(&mut self, lit: Lit, value: V::Value) {
        debug_assert!(lit.get_var() < self.assignment.len());
        if lit.is_negated() {
            unsafe {
                self.assignment
                    .get_unchecked_mut(lit.get_var())
                    .set_value(value.negate())
            };
        } else {
            unsafe {
                self.assignment
                    .get_unchecked_mut(lit.get_var())
                    .set_value(value)
            };
        }
    }

    /// Get the value of a [`Lit`]. Hence, if [`Lit`] is negated, then value assigned to its variable is negated.
    #[inline]
    pub fn get_lit_value(&self, lit: Lit) -> V::Value {
        if let Some(value) = self.assignment.get(lit.get_var()) {
            if lit.is_negated() {
                value.get_value().negate()
            } else {
                value.get_value()
            }
        } else {
            V::Value::default()
        }
    }

    /// Same as `get_lit_value` but without bounds check.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the [`Assignment`] has a large enough size, so that the variable index of `lit` is less than that size.
    ///
    /// Using a `lit` with variable index of at least the size of [`Assignment`] is undefined behaviour.
    #[inline]
    pub unsafe fn get_lit_value_unchecked(&self, lit: Lit) -> V::Value {
        debug_assert!(lit.get_var() < self.assignment.len());
        let value = unsafe { self.assignment.get_unchecked(lit.get_var()).get_value() };
        if lit.is_negated() {
            value.negate()
        } else {
            value
        }
    }

    /// Reset the [`Assignment`] to its default values.
    #[inline]
    pub fn reset(&mut self) {
        self.assignment.fill(Default::default());
    }

    /// Returns the number of variables in the [`Assignment`] no matter their value.
    #[inline]
    pub fn len(&self) -> usize {
        self.assignment.len()
    }

    /// Returns `true` if the assignment is empty, i.e., it contains no variables, neither unassigned nor assigned.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.assignment.is_empty()
    }
}

impl Assignment<BooleanVar> {
    /// Construct an [`Assignment`] from a [`Vec<Lit>`] with a given capacity.
    ///
    /// Returns `Some(assignment)` if the `literals` are consistent, i.e., [`Vec<Lit>`] does not contain a literal and its negation. If `literals` is not consistent, then [`None`] is returned.
    #[inline]
    pub fn from(literals: &Vec<Lit>, capacity: usize) -> Option<Self> {
        let mut assignment = Assignment::with_size(capacity);
        for &lit in literals {
            if unsafe { assignment.get_lit_value_unchecked(lit) } == BoolValue::Assigned(false) {
                return None;
            }
            unsafe { assignment.set_lit_value_unchecked(lit, BoolValue::Assigned(true)) };
        }
        Some(assignment)
    }

    /// Test if the variable is unassigned.
    ///
    /// Returns `true` if the variable matches `BoolValue::Unassigned`.
    #[inline]
    pub fn is_unassigned(&self, var: VarIdx) -> bool {
        matches!(self.assignment[var].get_value(), BoolValue::Unassigned)
    }

    /// Test if the variable is unassigned.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the [`Assignment`] has a large enough size, so that the variable index of `lit` is less than that size.
    ///
    /// Using a `lit` with variable index of at least the size of [`Assignment`] is undefined behaviour.
    #[inline]
    pub unsafe fn is_unassigned_unchecked(&self, lit: Lit) -> bool {
        debug_assert!(lit.get_var() < self.assignment.len());
        matches!(
            unsafe { self.assignment.get_unchecked(lit.get_var()).get_value() },
            BoolValue::Unassigned
        )
    }

    /// Test if the variable is assigned to some value.
    ///
    /// Returns `true` if the variable matches `BoolValue::Assigned(_)`.
    #[inline]
    pub fn is_assigned(&self, var: VarIdx) -> bool {
        matches!(self.assignment[var].get_value(), BoolValue::Assigned(_))
    }
}

impl ToPrettyString for Assignment<BooleanVar> {
    fn to_pretty_string<V: VarNameLookup>(&self, var_names: &V) -> String {
        let mut output = String::with_capacity(8 * self.len());
        for (idx, var) in self.assignment.iter().enumerate() {
            match var.get_value() {
                BoolValue::Assigned(true) => {
                    output.push_str(var_names.get_name(idx));
                    output.push(' ');
                }
                BoolValue::Assigned(false) => {
                    output.push('~');
                    output.push_str(var_names.get_name(idx));
                    output.push(' ');
                }
                BoolValue::Unassigned => {}
            }
        }
        output.pop();
        output
    }
}

impl Substitutable for Assignment<BooleanVar> {
    fn get_lit(&self, lit: Lit) -> Option<SubstitutionValue> {
        match unsafe { self.get_lit_value_unchecked(lit) } {
            BoolValue::Unassigned => None,
            BoolValue::Assigned(true) => Some(SubstitutionValue::TRUE),
            BoolValue::Assigned(false) => Some(SubstitutionValue::FALSE),
        }
    }
}

impl Display for Assignment<BooleanVar> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (idx, var) in self.assignment.iter().enumerate() {
            match var.get_value() {
                BoolValue::Unassigned => writeln!(f, "{}: -", idx + 1)?,
                BoolValue::Assigned(val) => writeln!(f, "{}: {}", idx + 1, val)?,
            }
        }
        Ok(())
    }
}

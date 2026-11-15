//! A mapping from variables to literals or truth values.

use std::collections::BTreeMap;

use crate::prelude::*;

/// The internal representation of a substitution.
type SubstitutionData = usize;

/// A [`SubstitutionValue`] is an element in the range of the substitution. Hence, a [`SubstitutionValue`] is either a literal or a truth value.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct SubstitutionValue {
    data: SubstitutionData,
}

/// Cut off value when to change from sparse to dense representation of substitutions
const SPARSE_CUTOFF: usize = 32;

impl SubstitutionValue {
    /// Truth value representing false.
    pub const FALSE: SubstitutionValue = SubstitutionValue {
        data: SubstitutionData::MAX - 1,
    };
    /// Truth value representing true.
    pub const TRUE: SubstitutionValue = SubstitutionValue {
        data: SubstitutionData::MAX,
    };

    /// Construct a [`SubstitutionValue`] mapping to [`Lit`].
    #[inline]
    pub fn lit(lit: Lit) -> Self {
        SubstitutionValue {
            data: lit.get_lit_data(),
        }
    }

    /// Get the [`Lit`] of the [`SubstitutionValue`].
    #[inline]
    pub fn get_lit(self) -> Lit {
        Lit::from_raw_data(self.data)
    }

    /// Negate the [`SubstitutionValue`].
    ///
    /// If the [`SubstitutionValue`] is a truth value, then true is changed to false and vice versa. If [`SubstitutionValue`] is a literal, then the literal is negated.
    #[inline]
    pub fn into_negation(&self) -> Self {
        SubstitutionValue {
            data: self.data ^ 1,
        }
    }
}

pub trait Substitutable {
    /// Get the [`SubstitutionValue`] that `lit` is mapped to.
    ///
    /// This means that if `lit` is negated, then the [`SubstitutionValue`] for its variable is negated.
    fn get_lit(&self, lit: Lit) -> Option<SubstitutionValue>;
}

/// A [`Substitution`] maps variables to literals or truth values.
#[derive(Debug, Clone, Default)]
pub struct Substitution {
    /// Sparse representation uses a map from [`VarIdx`] to [`SubstitutionValue`].
    sparse_map: BTreeMap<VarIdx, SubstitutionValue>,
    /// Dense representation uses a [`Vec<Option<SubstitutionValue>>`] in which we can index with [`VarIdx`]. The purpose of the option is to have a common default value, which should improve performance for resetting it.
    dense_map: Vec<Option<SubstitutionValue>>,
    /// The support of the [`Substitution`] are the variables not mapped to themselves by the [`Substitution`].
    support: Vec<VarIdx>,
}

impl Substitution {
    /// Get a substitution with a specific `size`.
    ///
    /// The `size` is the intended capacity of the [`Substitution`] that should be allocated.
    #[inline]
    pub fn with_size(size: usize) -> Self {
        if size > SPARSE_CUTOFF {
            Substitution {
                sparse_map: BTreeMap::new(),
                dense_map: vec![None; size],
                support: Vec::with_capacity(size),
            }
        } else {
            Substitution {
                sparse_map: BTreeMap::new(),
                dense_map: vec![],
                support: Vec::with_capacity(size),
            }
        }
    }

    /// Set `var` to map to `value`.
    ///
    /// This function takes care to switch from sparse to dense representation if the support gets to large.
    #[inline]
    pub fn set(&mut self, var: VarIdx, value: SubstitutionValue) -> bool {
        let already_set = if self.dense_map.is_empty() {
            // We are using sparse representation.
            if self.support.len() < SPARSE_CUTOFF {
                self.sparse_map.insert(var, value).is_some()
            } else {
                for (&var, &value) in self.sparse_map.iter() {
                    if var >= self.dense_map.len() {
                        self.dense_map.resize(1 + var, None);
                    }
                    unsafe {
                        *self.dense_map.get_unchecked_mut(var) = Some(value);
                    }
                }
                // Grow vector if it is too small.
                if var >= self.dense_map.len() {
                    self.dense_map.resize(1 + var, None);
                }
                unsafe {
                    self.dense_map
                        .get_unchecked_mut(var)
                        .replace(value)
                        .is_some()
                }
            }
        } else {
            // Grow vector if it is too small.
            if var >= self.dense_map.len() {
                self.dense_map.resize(1 + var, None);
            }
            unsafe {
                self.dense_map
                    .get_unchecked_mut(var)
                    .replace(value)
                    .is_some()
            }
        };
        if !already_set {
            self.support.push(var);
        }
        already_set
    }

    /// Get the [`SubstitutionValue`] that `var` maps to.
    #[inline]
    pub fn get(&self, var: VarIdx) -> Option<SubstitutionValue> {
        // If the dense map is empty, then we are using sparse mapping.
        if self.dense_map.is_empty() {
            self.sparse_map.get(&var).copied()
        } else {
            match self.dense_map.get(var) {
                Some(value) => *value,
                None => None,
            }
        }
    }

    /// Get size of the support of the [`Substitution`], i.e., how many variables are not mapped to itself by the [`Substitution`].
    #[inline]
    pub fn len(&self) -> usize {
        self.support.len()
    }

    /// Check if the support of the [`Substitution`] is empty, i.e., all variables map to themselves in the [`Substitution`].
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.support.is_empty()
    }

    /// Get an iterator over the support of the [`Substitution`], i.e., the variables not mapped to themself by the [`Substitution`].
    #[inline]
    pub fn syntactic_support(&self) -> impl Iterator<Item = &VarIdx> {
        self.support.iter()
    }
}

impl Substitutable for Substitution {
    #[inline]
    fn get_lit(&self, lit: Lit) -> Option<SubstitutionValue> {
        if lit.is_negated() {
            self.get(lit.get_var()).map(|sub| sub.into_negation())
        } else {
            self.get(lit.get_var())
        }
    }
}

impl ToPrettyString for Substitution {
    fn to_pretty_string<V: VarNameLookup>(&self, var_names: &V) -> String {
        let mut out = String::new();
        for from in self.support.iter() {
            out.push(' ');
            out.push_str(var_names.get_name(*from));
            out.push_str(" -> ");
            match self.get(*from).unwrap() {
                SubstitutionValue::TRUE => out.push('1'),
                SubstitutionValue::FALSE => out.push('0'),
                lit => out.push_str(&lit.get_lit().to_pretty_string(var_names)),
            }
        }
        out
    }
}

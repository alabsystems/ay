//! Implementation of [`VarType`] for Boolean variables.

use crate::{prelude::Negate, var_type::VarType};

/// A [`BooleanVar`] is a variable which takes boolean variables. The [`BooleanVar`] implements the [`VarType`] trait.
#[derive(Debug, Clone, Default)]
pub struct BooleanVar {
    value: BoolValue,
}

/// A Boolean value that is either `Unassigned`, `Assigned(true)`, or `Assigned(false)`.
#[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
pub enum BoolValue {
    Unassigned,
    Assigned(bool),
}

impl VarType for BooleanVar {
    type Value = BoolValue;

    #[inline]
    fn new() -> Self
    where
        Self: Sized,
    {
        BooleanVar {
            value: BoolValue::Unassigned,
        }
    }

    #[inline]
    fn set_value(&mut self, value: Self::Value) {
        self.value = value;
    }

    #[inline]
    fn get_value(&self) -> Self::Value {
        self.value
    }
}

impl Negate for BoolValue {
    #[inline]
    fn negate(self) -> Self {
        match self {
            Self::Unassigned => Self::Unassigned,
            Self::Assigned(value) => Self::Assigned(!value),
        }
    }
}

impl Default for BoolValue {
    #[inline]
    fn default() -> Self {
        Self::Unassigned
    }
}

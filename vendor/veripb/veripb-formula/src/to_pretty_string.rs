//! Trait for formatting strings using the correct variable name.

use crate::prelude::VarNameLookup;

/// Formatting strings using correct variables name mapping.
pub trait ToPrettyString {
    /// Format to a string using the correct variable names.
    fn to_pretty_string<V: VarNameLookup>(&self, var_names: &V) -> String;
}

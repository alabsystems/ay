//! Processor for VeriPB rules.

use veripb_formula::prelude::VarNameRecorder;
use veripb_rules::VeriPBRule;

use crate::error::ParserError;

/// Error type returned by a [`ProofProcessor`].
pub trait ProofProcessorError: From<ParserError> + std::error::Error {}

impl<T> ProofProcessorError for T where T: From<ParserError> + std::error::Error {}

/// Trait for processing VeriPB proof rules.
///
/// The interacts with and forwards parsed rules to the [`ProofProcessor`]. The [`ProofProcessor`] has to track of a mapping from variable names to variable indices through the [`VarNameRecorder`] trait.
pub trait ProofProcessor: VarNameRecorder {
    type Error: ProofProcessorError;

    /// The parsed VeriPB proof version number.
    fn process_version(&mut self, major: i64, minor: i64);

    /// Record a variable name and perform semantic checks on the usage of the variable. This function returns the variable index of the variable.
    fn process_var_name(
        &mut self,
        line: usize,
        name: &str,
        is_aux_var: bool,
    ) -> Result<usize, Self::Error>;

    /// Process a VeriPB proof rule.
    fn process_rule(&mut self, line: usize, rule: VeriPBRule) -> Result<(), Self::Error>;

    /// Returns whether the rule on (0-based) proof file line `line` should be
    /// traced. This lets the parser decide whether to print the proof file
    /// source lines for a rule before handing it over for processing.
    fn should_trace(&self, line: usize) -> bool;

    /// Returns the ID of the constraint most recently returned by a rule.
    /// Usually this is latest derived constraint, but for the `e` (equals) rule
    /// it's the ID of the constraint which was found to be equal to given one.
    fn last_returned_constraint_id(&mut self) -> Option<isize>;
}

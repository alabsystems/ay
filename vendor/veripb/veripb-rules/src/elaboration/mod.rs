//! Elaboration: rewrites a checked proof into a fully-explicit proof in the kernel format.
//! This will then be checkable by the CakePB formally verified checker.

use std::rc::Rc;

use thiserror::Error;
use veripb_formula::prelude::{DBConstraint, VarNameLookup};

pub mod elaborator;
pub mod rules;
pub mod write_helpers;

pub use elaborator::Elaborator;

/// Placeholder for elaboration errors.
#[derive(Debug, Error, PartialEq)]
pub enum ElaborationError {}

/// Read access to constraints by their database index.
pub trait ConstraintLookup {
    type Error: std::error::Error;

    /// Get a constraint at the absolute constraint ID `index`.
    ///
    /// If there is no constraint with the constraint ID `index`, then this function should return an error.
    fn get_entry_usize(&self, index: usize) -> Result<&Rc<DBConstraint>, Self::Error>;
}

/// Lookup over a single constraint: ignores the index and returns it directly.
impl ConstraintLookup for Rc<DBConstraint> {
    type Error = std::convert::Infallible;
    fn get_entry_usize(&self, _index: usize) -> Result<&Rc<DBConstraint>, Self::Error> {
        Ok(self)
    }
}

/// A rule that can write its own elaborated form. The default writes nothing.
pub trait Elaboratable {
    /// Write rule through the [`Elaborator`] to the file opened in the [`Elaborator`]. Some rules in VeriPB require elaboration before checking a rule is ended, which might require to write a proof through functions available in the [`write_helpers`] module. In thins case this function might write nothing.
    fn elaborate<C: ConstraintLookup, V: VarNameLookup>(
        &self,
        _elaborator: &mut Elaborator,
        _database: &C,
        _var_name_lookup: &V,
    ) -> Result<(), ElaborationError> {
        Ok(())
    }
}

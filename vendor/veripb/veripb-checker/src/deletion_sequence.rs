//! Data structure for deleting multiple constraints.

use crate::{
    context::Context, database::Database, error::CheckingError, rules::deletion::DeletionChecker,
};
use colored::Colorize;
use itertools::Itertools;

/// Trait for deleting multiple constriaints.
pub trait DeletionSequence {
    /// Get an [`Iterator`] of the constraint IDs that are deleted.
    fn get_deleted_ids(&self) -> impl Iterator<Item = &usize>;

    /// Write the deleted constraint IDs to a [`String`].
    #[inline]
    fn trace_deletions(&self, database: &Database) -> String {
        self.get_deleted_ids()
            .map(|&id| {
                if database
                    .get_entry_usize(id)
                    .expect("constraint should still exist")
                    .is_core_constraint_id(id)
                {
                    id.to_string().bright_green()
                } else {
                    id.to_string().yellow()
                }
            })
            .join(", ")
    }

    /// Delete the constraint IDs from the [`Database`].
    #[inline]
    fn delete_constraints(
        &self,
        database: &mut Database,
        context: &mut Context,
    ) -> Result<(), CheckingError> {
        self.get_deleted_ids()
            .try_for_each(|&constraint_id| database.delete_constraint(context, constraint_id))
    }
}

impl DeletionSequence for Vec<usize> {
    #[inline]
    fn get_deleted_ids(&self) -> impl Iterator<Item = &usize> {
        self.iter()
    }
}

/// Enum for for variant implementing deletion sequence trait.
pub enum DeletionSequenceEnum<'a> {
    /// Deleted constraints are stored inside the VeriPB deletion rule.
    Deletion(&'a DeletionChecker),
    /// Deleted constraint IDs are stored in a vector.
    Vec(Vec<usize>),
}

impl DeletionSequenceEnum<'_> {
    /// Print the constraint IDs in the deletion sequence.
    #[inline]
    pub fn trace_deletions(&self, database: &Database) -> String {
        match self {
            DeletionSequenceEnum::Deletion(del) => del.trace_deletions(database),
            DeletionSequenceEnum::Vec(vec) => vec.trace_deletions(database),
        }
    }

    /// Delete the constraints in the sequence in the `database`.
    #[inline]
    pub fn delete_constraints(
        &self,
        database: &mut Database,
        context: &mut Context,
    ) -> Result<(), CheckingError> {
        match self {
            DeletionSequenceEnum::Deletion(del) => del.delete_constraints(database, context),
            DeletionSequenceEnum::Vec(vec) => vec.delete_constraints(database, context),
        }
    }
}

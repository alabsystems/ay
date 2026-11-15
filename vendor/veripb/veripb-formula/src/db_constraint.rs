//! Wrapper for [`PBConstraint`] with header metadata.

use std::{cell::RefCell, collections::BTreeMap, hash::Hasher, ptr};

use malachite_bigint::BigInt;

use crate::{pb_constraint::PBConstraintEnum, prelude::*, substitution::Substitutable};

/// Header for [`DBConstraint`] in the database that contains metadata of the constraint.
#[derive(Debug, Default)]
pub struct DBHeader {
    /// The IDs of the constraint, where the constraint is in the derived set.
    pub derived_ids: Vec<usize>,
    /// The IDs of the constraint, where the constraint is in the core set.
    pub core_ids: Vec<usize>,
    /// If the constraint has been added to the occurrence list.
    pub is_in_occurrences: bool,
    /// If the constraint is the representative for its value in `unique_constraints`.
    pub is_in_unique: bool,
    /// Map from original constraint ID to elaborated constraint ID.
    pub in_to_out_id: BTreeMap<usize, usize>,
    /// Count how many valid IDs the constraint has.
    pub valid_id_counter: isize,
    /// If the constraint has been marked by output check.
    pub is_in_output_formula: bool,
    /// If the constraint might be used as a reason inside a saved trail.
    pub is_saved_reason: bool,
    /// How many propagation sets the constraint is attached to
    pub attached_propagator_count: usize,
}

impl DBHeader {
    /// Check if the header contains an ID in [`core_ids`](DBHeader::core_ids).
    #[inline]
    pub fn is_core_constraint(&self) -> bool {
        !self.core_ids.is_empty()
    }

    /// Check if `id` is contained in [`core_ids`](DBHeader::core_ids) of the header.
    #[inline]
    pub fn is_core_constraint_id(&self, id: usize) -> bool {
        self.core_ids.contains(&id)
    }
}

/// An entry in the constraint database.
///
/// The entry consists of a `header` for metadata of the constraint and the `constraint` itself.
#[derive(Debug)]
pub struct DBConstraint {
    pub header: RefCell<DBHeader>,
    pub constraint: PBConstraintEnum,
}

impl DBConstraint {
    /// Add an `constraint_id` to the [`DBConstraint`].
    ///
    /// It the parameter `add_to_core` is set to `true`, then the constraint ID is added to the [`core_ids`](DBHeader::core_ids), and otherwise it is added to the [`derived_ids`](DBHeader::derived_ids)
    #[inline]
    pub fn add_id(&self, constraint_id: usize, add_to_core: bool) {
        let mut header = self.header.borrow_mut();
        if add_to_core {
            header.core_ids.push(constraint_id);
        } else {
            header.derived_ids.push(constraint_id);
        }
        header.valid_id_counter += 1;
    }

    /// Remove `constraint_id` from the [`DBConstraint`].
    ///
    /// This function removes the ID from both the core and the derived set.
    #[inline]
    pub fn remove_id(&self, constraint_id: usize) {
        let mut header = self.header.borrow_mut();
        if let Some(idx) = header.core_ids.iter().position(|&x| x == constraint_id) {
            header.core_ids.swap_remove(idx);
        } else if let Some(idx) = header.derived_ids.iter().position(|&x| x == constraint_id) {
            header.derived_ids.swap_remove(idx);
        } else {
            unreachable!()
        }
        header.in_to_out_id.remove(&constraint_id);
    }

    /// Get actual deleted constraint IDs from the core and the derived set when deleting by constraint ID.
    ///
    /// This function returns the pair of [`Vec<VarIdx>`], where the first element is the IDs deleted from the core set and the second element is the IDs deleted from the derived set.
    #[inline]
    pub fn get_del_by_id(&self, constraint_id: usize) -> (Vec<usize>, Vec<usize>) {
        let mut header = self.header.borrow_mut();
        header.valid_id_counter -= 1;

        // Check if all IDs are deleted.
        if header.valid_id_counter <= 0 {
            (header.core_ids.clone(), header.derived_ids.clone())
        } else if header.core_ids.contains(&constraint_id) {
            (vec![constraint_id], vec![])
        } else {
            (vec![], vec![constraint_id])
        }
    }

    /// Get the actual deleted constraint IDs from the core and the derived set when deleting by constraint specification.
    ///
    /// This function returns the pair of [`Vec<VarIdx>`], where the first element is the IDs deleted from the core set and the second element is the IDs deleted from the derived set.
    #[inline]
    pub fn get_del_by_spec(&self) -> (Vec<usize>, Vec<usize>) {
        let mut header = self.header.borrow_mut();
        header.valid_id_counter -= 1;

        if header.valid_id_counter <= 0 {
            (header.core_ids.clone(), header.derived_ids.clone())
        } else {
            (vec![], vec![])
        }
    }

    /// Move the `constraint_id` of the constraint from the derived set to the core set.
    #[inline]
    pub fn move_id_to_core(&self, constraint_id: usize) {
        let mut header = self.header.borrow_mut();

        if let Some(pos) = header
            .derived_ids
            .iter()
            .position(|&id| id == constraint_id)
        {
            header.derived_ids.swap_remove(pos);
            header.core_ids.push(constraint_id);
        }
    }

    /// Check if this constraint has any constraint IDs.
    ///
    /// This function return `true` if and only if there are no constraints for this constraint saved.
    ///
    /// If the parameter `only_core` is `true`, then we only check if there are IDs in the core set.
    #[inline]
    pub fn all_constraint_ids_empty(&self, only_core: bool) -> bool {
        let header = self.header.borrow();
        if only_core {
            header.core_ids.is_empty()
        } else {
            header.core_ids.is_empty() && header.derived_ids.is_empty()
        }
    }

    /// Get some ID for the constraint.
    ///
    /// If the constraint has a core constraint ID, then it will preferably return that. If the constraint does not have a ID, then the dummy ID `0` will be returned.
    #[inline]
    pub fn get_some_id(&self) -> usize {
        let header = self.header.borrow();
        if !header.core_ids.is_empty() {
            header.core_ids[0]
        } else if !header.derived_ids.is_empty() {
            header.derived_ids[0]
        } else {
            0
        }
    }

    /// Copy the constraint IDs and from this constraint to `other` constraint.
    #[inline]
    pub fn copy_ids(&self, other: &DBConstraint) {
        let mut header = self.header.borrow_mut();
        let other_header = other.header.borrow();
        header.core_ids = other_header.core_ids.clone();
        header.derived_ids = other_header.derived_ids.clone();
        header.in_to_out_id = other_header.in_to_out_id.clone();
    }

    /// Add the constraint IDs from `other` constraint to this constraint.
    #[inline]
    pub fn append_ids(&self, other: DBConstraint) {
        let mut header = self.header.borrow_mut();
        let mut other_header = other.header.borrow_mut();
        header.core_ids.append(&mut other_header.core_ids);
        header.derived_ids.append(&mut other_header.derived_ids);
        header.in_to_out_id.append(&mut other_header.in_to_out_id);
    }

    /// Set to output constraint ID of `orig_id` to `out_id`.
    #[inline]
    pub fn set_out_id(&self, orig_id: usize, out_id: usize) {
        self.header
            .borrow_mut()
            .in_to_out_id
            .insert(orig_id, out_id);
    }

    /// Get the output constraint ID from ID `orig_id`.
    #[inline]
    pub fn get_out_id(&self, orig_id: usize) -> Option<usize> {
        self.header.borrow().in_to_out_id.get(&orig_id).cloned()
    }

    /// Check if the constraint is in the core set.
    #[inline]
    pub fn is_core_constraint(&self) -> bool {
        self.header.borrow().is_core_constraint()
    }

    /// Check if the constraint is a core constraint and not marked as being in the output formula.
    #[inline]
    pub fn is_core_and_not_in_output_constraint(&self) -> bool {
        let header = self.header.borrow();
        header.is_core_constraint() && !header.is_in_output_formula
    }

    /// Check if the the constraint ID `id` of the constraint which is in the core IDs.
    #[inline]
    pub fn is_core_constraint_id(&self, id: usize) -> bool {
        self.header.borrow().is_core_constraint_id(id)
    }

    /// Check if the constraint is (ordinarily) syntactically implied.
    ///
    /// This function calls [`implies()`](PBConstraintEnum::implies()) of the [`PBConstraint`].
    #[inline]
    pub fn implies(&self, target: &DBConstraint) -> bool {
        self.constraint.implies(&target.constraint)
    }

    /// Get the negation of this constraint.
    ///
    /// This function calls [`negate()`](PBConstraintEnum::negate()) of the [`PBConstraint`].
    #[inline]
    pub fn negate(&self) -> DBConstraint {
        self.constraint.negate().into()
    }

    /// Get the constraint substituted with the `substitution`.
    ///
    /// This function calls [`substitute()`](PBConstraintEnum::substitute()) of the [`PBConstraint`].
    #[inline]
    pub fn substitute(&self, substitution: &impl Substitutable) -> DBConstraint {
        self.constraint.substitute(substitution).into()
    }

    /// Get the maximum coefficient of the constraint.
    ///
    /// This function calls [`get_max_coeff()`](PBConstraintEnum::get_max_coeff()) of the [`PBConstraint`].
    #[inline]
    pub fn get_max_coeff(&self) -> BigInt {
        self.constraint.get_max_coeff()
    }

    /// Check if the constraint is a contradiction, i.e., the constraint is always falsified.
    ///
    /// This function calls [`is_contradicting()`](PBConstraintEnum::is_contradicting()) of the [`PBConstraint`].
    #[inline]
    pub fn is_contradicting(&self) -> bool {
        self.constraint.is_contradicting()
    }

    /// Check if the constraint is trivial, i.e., the constraint is always satisfied.
    ///
    /// This function calls [`is_trivial()`](PBConstraintEnum::is_trivial()) of the [`PBConstraint`].
    #[inline]
    pub fn is_trivial(&self) -> bool {
        self.constraint.is_trivial()
    }

    /// Check if the constraint is satisfied by the given `assignment`.
    ///
    /// This function calls [`is_satisfied()`](PBConstraintEnum::is_satisfied()) of the [`PBConstraint`].
    #[inline]
    pub fn is_satisfied(&self, assignment: &Assignment<BooleanVar>) -> bool {
        self.constraint.is_satisfied(assignment)
    }

    /// Check if the constraint is falsified by the given `assignment`.
    ///
    /// This function calls [`is_falsified()`](PBConstraintEnum::is_falsified()) of the [`PBConstraint`].
    #[inline]
    pub fn is_falsified(&self, assignment: &Assignment<BooleanVar>) -> bool {
        self.constraint.is_falsified(assignment)
    }

    /// Calculate the propagations of the constraint with respect to the given `assignment`.
    ///
    /// This function calls [`propagate()`](PBConstraintEnum::propagate()) of the [`PBConstraint`].
    #[inline]
    pub fn propagate(
        &self,
        assignment: &mut Assignment<BooleanVar>,
    ) -> ConstraintPropagationResult {
        self.constraint.propagate(assignment)
    }

    /// Trace the propagations of the constraint with respect to the given `assignment`.
    ///
    /// This function calls [`traced_propagate()`](PBConstraintEnum::traced_propagate()) of the [`PBConstraint`].
    #[inline]
    pub fn traced_propagate(&self, assignment: &mut Assignment<BooleanVar>) -> Vec<Lit> {
        self.constraint.traced_propagate(assignment)
    }

    #[inline]
    pub fn get_reification(&self, var: VarIdx, direction: ReificationDir) -> PBConstraintEnum {
        self.constraint.get_reification(var, direction)
    }
}

/// **ATTENTION:** The equivalence check is only with respect to the [`PBConstraintEnum`] and the [`DBHeader`] is ignored.
impl PartialEq for DBConstraint {
    fn eq(&self, other: &Self) -> bool {
        ptr::eq(self, other) || self.constraint == other.constraint
    }
}

/// **ATTENTION:** The equivalence check is only with respect to the [`PBConstraintEnum`] and the [`DBHeader`] is ignored.
impl PartialEq<PBConstraintEnum> for DBConstraint {
    fn eq(&self, other: &PBConstraintEnum) -> bool {
        self.constraint == *other
    }
}

impl Eq for DBConstraint {}

/// **ATTENTION:** The hash is calculated only with respect to the [`PBConstraintEnum`] and the [`DBHeader`] is ignored.
impl std::hash::Hash for DBConstraint {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.constraint.hash(state);
    }
}

impl From<PBConstraintEnum> for DBConstraint {
    fn from(value: PBConstraintEnum) -> Self {
        DBConstraint {
            header: RefCell::new(DBHeader::default()),
            constraint: value,
        }
    }
}

impl From<Clause> for DBConstraint {
    fn from(value: Clause) -> Self {
        DBConstraint {
            header: RefCell::new(DBHeader::default()),
            constraint: value.into(),
        }
    }
}

impl From<Cardinality> for DBConstraint {
    fn from(value: Cardinality) -> Self {
        DBConstraint {
            header: RefCell::new(DBHeader::default()),
            constraint: value.into(),
        }
    }
}

impl<N> From<GeneralPBConstraint<N>> for DBConstraint
where
    N: Int,
    PBConstraintEnum: From<GeneralPBConstraint<N>>,
{
    fn from(value: GeneralPBConstraint<N>) -> Self {
        DBConstraint {
            header: RefCell::new(DBHeader::default()),
            constraint: value.into(),
        }
    }
}

impl ToPrettyString for DBConstraint {
    fn to_pretty_string<V: VarNameLookup>(&self, var_names: &V) -> String {
        self.constraint.to_pretty_string(var_names)
    }
}

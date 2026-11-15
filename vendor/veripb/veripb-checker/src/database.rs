//! Storage of pseudo-Boolean constraints in the [`ForwardsChecker`](crate::checker::ForwardsChecker).

use std::{cell::RefCell, ops::Range, rc::Rc};

use ahash::{HashSet, RandomState};
use by_address::ByAddress;
use veripb_formula::prelude::*;
use veripb_propagator::propagation_engine::{
    CORE_CLAUSES_CARD, CORE_GENERAL, DERIVED_CLAUSES_CARD, DERIVED_GENERAL, PropagationEngine,
};
use veripb_rules::elaboration::ConstraintLookup;

use crate::{context::Context, error::CheckingError, occurrence_list::OccurrenceList};

const IGNORE_DATABASE_PROOFGOAL_THRESHOLD: f64 = 0.05;

/// A database proof obligation that proofgoal *generation* discharged, and the
/// reason it did.
///
/// `add_non_obvious_proofgoals` drops an obligation for one of three reasons,
/// and each is an acceptance shape the kernel bridge re-judges elsewhere: a
/// trivially-true substituted constraint (`consume_trivial`), an original
/// constraint that syntactically implies its own substituted image
/// (`consume_implication`), and a substituted constraint that equals a usable
/// database constraint (`consume_db_lookup`). Naming the reason lets
/// `kernel_bridge::consume_autodischarge` route each drop back through the
/// same entry point the corresponding *explicit* proofgoal would take, so a
/// discharge that happens during goal generation is re-derived rather than
/// trusted. Only collected under `--kernel-verify`.
#[derive(Debug)]
pub enum AutoDischarge {
    /// The substituted constraint is trivially true (source, substituted).
    ///
    /// The SOURCE is carried even though discharging needs only the image.
    /// `red` has to pair each database slot the witness moves with the goal
    /// that covers it, and a goal's slot is recovered from the source's live
    /// ids -- the substituted constraint alone has a fresh header and no ids
    /// at all, so a slot discharged this way was invisible and the whole step
    /// had to be refused.
    Trivial(Rc<DBConstraint>, Rc<DBConstraint>),
    /// The original constraint implies its substituted image (source, target).
    Implied(Rc<DBConstraint>, Rc<DBConstraint>),
    /// A database constraint equals the substituted one
    /// (source, goal, found). `source` is the slot the goal is ABOUT; `found`
    /// is the unrelated database constraint that happens to equal it.
    DbLookup(Rc<DBConstraint>, Rc<DBConstraint>, Rc<DBConstraint>),
}

/// Remove the constraint from the core propagator and add it to the derived propagator.
#[inline]
pub fn move_to_derived_propagator(
    prop_engine: &mut PropagationEngine,
    constraint: &Rc<DBConstraint>,
) -> Result<(), CheckingError> {
    prop_engine.detach_checker(true, constraint, prop_engine.only_core_trail)?;
    prop_engine.attach_checker(false, constraint)?;
    Ok(())
}

/// Storage for constraints.
#[derive(Debug, Default)]
pub struct Database {
    /// Constraint ID indexed vector to directly get a constraint from its index.
    pub entries: Vec<Option<Rc<DBConstraint>>>,
    /// Hash map of unique constraints identified by the constraint of the entry.
    pub unique_constraints: HashSet<Rc<DBConstraint>>,
    /// An occurrence list mapping from literals to constraints. This list is kept in sync with the `unique_constraints`.
    occurrences: OccurrenceList,
    /// Only constraint IDs that are less than `next_unique_index_id` have been added to `unique_constraints`.
    next_unique_index_id: usize,
    /// Only constraint IDs that are less than `next_occurrences_index_id` have been added to `occurrences`.
    next_occurrences_index_id: usize,
    /// Only constraint IDs that are less than `next_propagation_index_id` have been added to the propagation engine.
    pub(crate) next_propagation_index_id: usize,
    /// Only constraint IDs that are at least `first_derived_id_lower_bound` may be in the derived set.
    first_derived_id_lower_bound: usize,
    /// The maximum size of the database to elaborate all database proofgoals even if they are autoproven.
    ignore_database_proofgoal_size: usize,
}

impl Database {
    /// Construct a new empty database with dummy entry at position 0.
    pub fn new() -> Self {
        Database {
            entries: vec![None],
            // The same fixed-seed state `from_formula` uses twelve lines
            // below, and for the same reason -- but this constructor got it
            // through `..Default::default()`, i.e. `ahash::RandomState`'s
            // runtime-seeded default, which a workspace-wide sweep for
            // randomly-seeded containers missed precisely because there is no
            // named constructor call to grep for. This is the constructor for
            // the order and `spec` sub-databases, and `check_implication`
            // iterates `unique_constraints` and returns the *first* implying
            // constraint, whose id an `ia` stores and the elaborator writes as
            // a hint. Measured: a `spec` block with two `red`s and a hintless
            // `ia` elaborated to `: 2` on 24 of 40 runs and `: 4` on the other
            // 16. Both artifacts re-check, so this was a determinism defect
            // and not a wrong verdict -- but an artifact that is not a
            // function of its input cannot be reproduced or hash-pinned.
            unique_constraints: HashSet::with_hasher(RandomState::with_seeds(42, 42, 42, 42)),
            ..Default::default()
        }
    }

    /// Initialize a database from the a `Formula`.
    pub fn from_formula(constraints: Vec<PBConstraintEnum>) -> Self {
        let mut entries = Vec::with_capacity(constraints.len() + 1);
        entries.push(None);
        let unique_constraints = HashSet::with_capacity_and_hasher(
            constraints.len(),
            RandomState::with_seeds(42, 42, 42, 42),
        );
        let occurrences = OccurrenceList::default();
        for constraint in constraints {
            let db_constraint = Rc::new(DBConstraint {
                header: RefCell::new(DBHeader::default()),
                constraint,
            });
            db_constraint.add_id(entries.len(), true);
            entries.push(Some(db_constraint));
        }
        let first_non_indexed_constraint_id = entries.len();
        let ignore_database_proofgoal_size =
            (IGNORE_DATABASE_PROOFGOAL_THRESHOLD * (entries.len() as f64)) as usize;

        Database {
            entries,
            unique_constraints,
            occurrences,
            next_unique_index_id: 1,
            next_occurrences_index_id: 1,
            next_propagation_index_id: 1,
            first_derived_id_lower_bound: first_non_indexed_constraint_id,
            ignore_database_proofgoal_size,
        }
    }

    /// Lazily adds a constraint to the database.
    ///
    /// If the constraint is already in the database, then it will be added lazily again.
    #[inline]
    pub fn add_constraint(&mut self, constraint: Rc<DBConstraint>, add_to_core: bool) {
        constraint.add_id(self.len(), add_to_core);
        self.entries.push(Some(constraint));
    }

    /// Remove a constraint from the unique-constraint and occurrences indices if it has
    /// been added to them.
    pub fn deindex_removed_constraint(&mut self, constraint: &Rc<DBConstraint>) {
        let mut header = constraint.header.borrow_mut();
        if header.is_in_unique {
            self.unique_constraints.remove(constraint.as_ref());
            header.is_in_unique = false;
        }

        if header.is_in_occurrences {
            self.occurrences.remove(constraint);
            header.is_in_occurrences = false;
        }
    }

    /// Re-index a constraint into whichever indices are already caught up to `len`
    /// (an index still behind will pick it up on its next `update_*`). Inverse of
    /// [`Database::deindex_removed_constraint`], will be used for the trimmer.
    pub fn reindex_reinserted_constraint(
        &mut self,
        constraint: &Rc<DBConstraint>,
        prop_engine: &mut PropagationEngine,
    ) -> Result<(), CheckingError> {
        let len = self.len();
        let mut header = constraint.header.borrow_mut();
        if self.next_unique_index_id == len
            && !header.is_in_unique
            && self.unique_constraints.insert(Rc::clone(constraint))
        {
            header.is_in_unique = true;
        }
        if self.next_occurrences_index_id == len && !header.is_in_occurrences {
            self.occurrences.add(constraint);
        }
        if self.next_propagation_index_id == len && header.attached_propagator_count == 0 {
            let add_to_core = constraint.is_core_constraint();
            prop_engine.attach_checker(add_to_core, constraint)?;
        }
        Ok(())
    }

    /// Check that the given id can be removed from the Database and `.take()` the entry if so.
    pub fn take_deletable_entry(&mut self, id: usize) -> Result<Rc<DBConstraint>, CheckingError> {
        match self.entries.get_mut(id) {
            None => Err(CheckingError::deletion(
                id,
                &format!(
                    "there are only {} constraints in the database",
                    self.entries.len()
                ),
            )),
            Some(None) => Err(CheckingError::deletion(
                id,
                "the constraint has already been deleted",
            )),
            Some(entry) => Ok(entry.take().expect("already checked None")),
        }
    }

    /// Delete a constraint from the database by their ID.
    ///
    /// Also deletes the constraint from indexing structures if it was added to them.
    #[inline]
    pub fn delete_constraint(
        &mut self,
        context: &mut Context,
        constraint_id: usize,
    ) -> Result<(), CheckingError> {
        let db_constraint = self.take_deletable_entry(constraint_id)?;
        let was_core = db_constraint.is_core_constraint();
        db_constraint.remove_id(constraint_id);
        // Did this constraint leave the CORE set? Either the whole entry went,
        // or it kept a derived id and lost its core one. Both are a deletion
        // from the core database the backward invariant `VeriPbCore.DbBack`
        // is stated over, and both need `dbBack_delete_checked`'s obligation.
        let left_core = was_core
            && (db_constraint.all_constraint_ids_empty(false)
                || !db_constraint.is_core_constraint());
        if db_constraint.all_constraint_ids_empty(false) {
            self.deindex_removed_constraint(&db_constraint);
            context
                .propagation_engine
                .detach_checker(was_core, &db_constraint, true)?;
        } else if was_core && !db_constraint.is_core_constraint() {
            move_to_derived_propagator(&mut context.propagation_engine, &db_constraint)?;
        }
        if left_core {
            crate::kernel_bridge::shadow_record_core_deletion(context, constraint_id);
        }
        // Mirror the deletion in the kernel shadow database
        // (`VeriPbCore.DbOk.delete`). Every deletion path in the checker
        // funnels through here, and `take_deletable_entry` above has already
        // rejected an out-of-range or already-deleted id, so the mirror only
        // runs once the entry really is gone -- an early return above leaves
        // the shadow untouched, matching the live database.
        crate::kernel_bridge::shadow_record_deleted(context, constraint_id);
        Ok(())
    }

    /// Indexes all constraints that are not yet indexed in `unique_constraints`.
    ///
    /// In case a duplicate constraint is detected, then the duplicate constraint is merged into the first occurrence.
    /// In particular, this also removes duplicate constraints from `occurrences` and the propagation engine.
    ///
    /// Must be called before:
    /// - using `Database::unique_constraints` directly
    /// - calling `Database::lookup()`
    /// - calling `Database::get_proofgoals()`
    pub fn update_unique_index(
        &mut self,
        prop_engine: &mut PropagationEngine,
    ) -> Result<(), CheckingError> {
        for constraint_id in self.next_unique_index_id..self.len() {
            // First check that the constraint ID is not deleted.
            if let Some(Some(constraint)) = self.entries.get(constraint_id) {
                // Skip a constraint with no live id (needed for
                // trimming, where survivor constraints persist in the
                // database even after being removed).
                if constraint.all_constraint_ids_empty(false) {
                    continue;
                }
                let is_core_constraint = constraint.is_core_constraint();
                if self.unique_constraints.insert(constraint.clone()) {
                    constraint.header.borrow_mut().is_in_unique = true;
                } else {
                    // Merge this constraint with the existing constraint.
                    let entry = self.unique_constraints.get(constraint).unwrap();
                    let is_original_core_constraint = entry.is_core_constraint();
                    entry.add_id(constraint_id, is_core_constraint);
                    if let Some(out_id) = constraint.get_out_id(constraint_id) {
                        entry.set_out_id(constraint_id, out_id);
                    }
                    constraint.remove_id(constraint_id);
                    // Remove from occurrence list if the duplicate constraint was added.
                    //
                    // This branch needs the occurrence index to have run *ahead* of the unique
                    // index -- upstream now keys it on the `is_in_occurrences` header flag rather
                    // than on `constraint_id < next_occurrences_index_id`, which is the same
                    // condition stated precisely: the flag is set only by `OccurrenceList::add`,
                    // i.e. only for ids the occurrence index has already passed. It is one-way
                    // either way: `update_occurrences_index` only ever visits ids at or above
                    // `next_occurrences_index_id`, so anything taken out here for an
                    // id below that frontier is never put back. `OccurrenceList` is keyed by
                    // address, so what must come out is the duplicate allocation and never the
                    // survivor -- after the assignment below, `entry` is the constraint living at
                    // `constraint_id`, and it has to stay findable or every `red`/`dom` proof
                    // obligation it should generate is lost without a trace.
                    //
                    // Two shapes would do exactly that, and neither is refuted by anything above:
                    // the two `Rc`s being one allocation (`unique_constraints` is keyed
                    // structurally, so `get` can hand back the very constraint we are merging),
                    // and `entry` not being indexed at all, which nothing would now repair.
                    // Measured by instrumenting this function and running
                    // `cargo test --test integration -- --test-threads=1` over the corpus as it
                    // stood at 441 derivations (867 trials: check and elaborate mode, less the
                    // 15 ignored): the duplicate merge below ran 263 times and this branch was
                    // entered 0 times, because not one of the 4182 `update_unique_index` calls
                    // saw the occurrence index ahead of it. `Database::var_occurs` does leave it
                    // ahead -- on 6 of those 441 derivations, by as much as 97 ids -- but each
                    // of those runs ends before the unique index catches up.
                    //
                    // The corpus has grown since (449 derivations at the time of writing), so
                    // those counts are a snapshot, not a live figure. The conclusion does not
                    // depend on re-measuring them: the branch returning an error means any
                    // instance that reaches it fails the suite, so a green corpus *is* the
                    // standing evidence that it stays unreached. That is the point of refusing
                    // loudly -- a scheduling accident is not an invariant, and the alternative
                    // was a missing obligation and a wrong verdict, discovered by nobody.
                    //
                    // The flag is read and cleared through separate short borrows rather than
                    // one `borrow_mut` held across the body: the refusal below has to inspect
                    // `entry`'s header too, and in the `Rc::ptr_eq` case that is the very same
                    // `RefCell`.
                    if constraint.header.borrow().is_in_occurrences {
                        if Rc::ptr_eq(entry, constraint) || !entry.header.borrow().is_in_occurrences
                        {
                            return Err(CheckingError::OccurrenceIndexEviction(constraint_id));
                        }
                        self.occurrences.remove(constraint);
                        constraint.header.borrow_mut().is_in_occurrences = false;
                    }

                    // Remove from propagator if it was added.
                    if constraint_id < self.next_propagation_index_id {
                        prop_engine.detach_checker(is_core_constraint, constraint, true)?;
                    }
                    // In case the original constraint is only in the derived set
                    // and the new is in the core set, then move it to the core.
                    let is_original_in_propagator =
                        entry.header.borrow().attached_propagator_count > 0;
                    if is_original_in_propagator
                        && !is_original_core_constraint
                        && is_core_constraint
                    {
                        prop_engine.move_constraint_checker(false, true, entry)?;
                    }
                    // Overwrite the duplicate constraint such that they both IDs point to the same constraint.
                    //
                    // The kernel shadow database needs no update here: this
                    // branch only fires when `entry == constraint` under
                    // `DBConstraint`'s equality, which is structural on the
                    // constraint itself, so the id keeps describing the same
                    // constraint and its slot stays correct.
                    self.entries[constraint_id] = Some(Rc::clone(entry));
                }
            }
        }
        self.next_unique_index_id = self.len();
        Ok(())
    }

    /// Indexes all constraints that are not yet indexed in `occurrences`. Will be automatically called before occurrences are needed.
    pub fn update_occurrences_index(&mut self) {
        for constraint_id in self.next_occurrences_index_id..self.len() {
            // First check that the constraint ID is not deleted.
            if let Some(Some(constraint)) = self.entries.get(constraint_id) {
                // Skip a constraint with no live id (needed for trimming).
                if constraint.all_constraint_ids_empty(false) {
                    continue;
                }
                if !constraint.header.borrow().is_in_occurrences {
                    self.occurrences.add(constraint);
                }
            }
        }
        self.next_occurrences_index_id = self.len();
    }

    /// Indexes all constraints that are not yet added to the propagation engine.
    ///
    /// Must be called before:
    /// - calling `PropagationEngine::reverse_unit_propagation_check()`
    /// - calling `PropagationEngine::propagate_solution()`
    pub fn update_propagation_index(
        &mut self,
        prop_engine: &mut PropagationEngine,
    ) -> Result<(), CheckingError> {
        for constraint_id in self.next_propagation_index_id..self.len() {
            // First check that the constraint ID is not deleted.
            if let Some(Some(constraint)) = self.entries.get(constraint_id) {
                // Skip a constraint with no live id (needed for trimming).
                let attach = {
                    let header = constraint.header.borrow();
                    header.attached_propagator_count == 0
                        && !(header.core_ids.is_empty() && header.derived_ids.is_empty())
                };
                if attach {
                    let add_to_core = constraint.is_core_constraint();
                    prop_engine.attach_checker(add_to_core, constraint)?;
                }
            }
        }
        self.next_propagation_index_id = self.len();
        Ok(())
    }

    /// Check if `constraint` is contained in the `Database` and return a reference to the constraint in the database if it exists.
    #[inline]
    pub fn lookup(&self, constraint: &Rc<DBConstraint>) -> Option<&Rc<DBConstraint>> {
        debug_assert!(self.len() == self.next_unique_index_id);
        self.unique_constraints.get(constraint)
    }

    /// Check if the database contain a contradiction.
    #[inline]
    pub fn contains_contradiction(&self) -> Option<usize> {
        for constraint in self.unique_constraints.iter() {
            if constraint.is_contradicting() {
                return Some(constraint.get_some_id());
            }
        }
        for constraint_id in self.next_unique_index_id..self.len() {
            if let Some(Some(constraint)) = self.entries.get(constraint_id)
                && constraint.is_contradicting()
            {
                return Some(constraint_id);
            }
        }
        None
    }

    /// Normalize a constraint ID using the current number of constraints into an absolute constraint ID.
    #[inline]
    pub fn normalize_id(&self, index: isize) -> isize {
        if index < 0 {
            self.len() as isize + index
        } else {
            index
        }
    }

    /// Get the constraint at a specific absolute or relative `index` in the database.
    ///
    /// This function returns an error if there is no constraint stored at the `index`.
    #[inline]
    pub fn get_entry(&self, index: isize) -> Result<&Rc<DBConstraint>, CheckingError> {
        let entry = if index < 0 {
            match self
                .entries
                .get(((self.entries.len() as isize) + index) as usize)
            {
                Some(entry) => entry,
                None => {
                    return Err(CheckingError::out_of_bounds(
                        index,
                        -(self.entries.len() as isize) + 1,
                        (self.entries.len() as isize) - 1,
                    ));
                }
            }
        } else {
            match self.entries.get(index as usize) {
                Some(entry) => entry,
                None => {
                    return Err(CheckingError::out_of_bounds(
                        index,
                        -(self.entries.len() as isize),
                        (self.entries.len() as isize) - 1,
                    ));
                }
            }
        };

        match entry {
            Some(constraint) => Ok(constraint),
            None => Err(CheckingError::access_deleted(index)),
        }
    }

    /// Get the constraint at a specific absolute `index` in the database.
    ///
    /// This function returns an error if there is no constraint stored at the `index`.
    #[inline]
    pub fn get_entry_usize(&self, index: usize) -> Result<&Rc<DBConstraint>, CheckingError> {
        let entry = match self.entries.get(index) {
            Some(entry) => entry,
            None => {
                return Err(CheckingError::out_of_bounds(
                    index as isize,
                    -(self.entries.len() as isize),
                    (self.entries.len() as isize) - 1,
                ));
            }
        };

        match entry {
            Some(constraint) => Ok(constraint),
            None => Err(CheckingError::access_deleted(index as isize)),
        }
    }

    /// Get the constraint at a specific absolute `index` in the database.
    ///
    /// This functions returns [`None`] if the constraint has already been deleted.
    #[inline]
    pub fn get_entry_optionally_deleted_usize(
        &self,
        index: usize,
    ) -> Result<Option<&Rc<DBConstraint>>, CheckingError> {
        let entry = match self.entries.get(index) {
            Some(entry) => entry,
            None => {
                return Err(CheckingError::out_of_bounds(
                    index as isize,
                    -(self.entries.len() as isize),
                    (self.entries.len() as isize) - 1,
                ));
            }
        };

        match entry {
            Some(constraint) => Ok(Some(constraint)),
            None => Ok(None),
        }
    }

    /// Check if the constraint at the `index` is not deleted.
    #[inline]
    pub fn is_undeleted(&self, index: usize) -> Result<bool, CheckingError> {
        if let Some(entry) = self.entries.get(index) {
            return Ok(entry.is_some());
        }
        Err(CheckingError::out_of_bounds(
            index as isize,
            -(self.entries.len() as isize),
            (self.entries.len() as isize) - 1,
        ))
    }

    /// Move the constraint ID to the core set and add it to the core propagator if it is not already in the core.
    #[inline]
    pub fn move_to_core(
        &self,
        prop_engine: &mut PropagationEngine,
        index: usize,
    ) -> Result<(), CheckingError> {
        // Find the constraint and get its header.
        let constraint = self.get_entry_usize(index)?;

        // If the constraint was not in the core propagator before, it is moved there.
        if !constraint.is_core_constraint()
            && constraint.header.borrow().attached_propagator_count > 0
        {
            prop_engine.move_constraint_checker(false, true, constraint)?;
        }

        // Remove ID from derived set and add it to the core set of IDs.
        constraint.move_id_to_core(index);

        Ok(())
    }

    /// Move all constraints to the core set and add them to the core propagator.
    pub fn move_to_core_all(
        &mut self,
        prop_engine: &mut PropagationEngine,
    ) -> Result<(), CheckingError> {
        // Move all constraints in database to core set.

        for constraint_id in self.first_derived_id_lower_bound..self.len() {
            if let Some(Some(constraint)) = self.entries.get(constraint_id) {
                let header = &mut *constraint.header.borrow_mut();
                header.core_ids.append(&mut header.derived_ids);
            }
        }
        self.first_derived_id_lower_bound = self.len();

        // Move all constraints in the derived propagation set to the core propagation set.
        prop_engine.move_all_constraints(DERIVED_CLAUSES_CARD, CORE_CLAUSES_CARD)?;
        prop_engine.move_all_constraints(DERIVED_GENERAL, CORE_GENERAL)?;

        Ok(())
    }

    /// Check if all constraints in the database are in the core set. No constraint is moved by this operation.
    pub fn all_constraints_in_core(&mut self) -> bool {
        // We make use of the fact that constraints can only be moved from the derived to the core set. So once we checked if a constraint is in the core set, then it will stay there or it will be deleted.
        for constraint in self.entries[self.first_derived_id_lower_bound..]
            .iter()
            .flatten()
        {
            if !constraint.header.borrow().derived_ids.is_empty() {
                return false;
            }
        }
        // Store last constraint ID as start point for next check.
        self.first_derived_id_lower_bound = self.len();

        true
    }

    /// Get the variables actually used by the constraints in the database.
    #[inline]
    pub fn get_used_vars(&mut self) -> Vec<VarIdx> {
        self.update_occurrences_index();
        self.occurrences.get_used_vars()
    }

    /// Whether any live constraint in the database mentions `var`, in either
    /// polarity.
    ///
    /// Uses the same occurrence index proofgoal generation relies on, so a
    /// constraint this misses is a constraint no `red`/`dom` would have turned
    /// into a proof obligation either.
    #[inline]
    pub fn var_occurs(&mut self, var: VarIdx) -> bool {
        self.update_occurrences_index();
        [false, true].into_iter().any(|negated| {
            self.occurrences
                .get_constraints_for_lit(Lit::from_var(var, negated))
                .is_some_and(|constraints| !constraints.is_empty())
        })
    }

    /// Add constraints to `unique_substituted_constraints` that contain the literal `lit`.
    ///
    /// This function only adds constraints that are not obviously implied by the database already.
    ///
    /// With `record_autodischarges` set (that is, under `--kernel-verify`),
    /// every obligation dropped here is pushed onto `autodischarged` together
    /// with the reason it was dropped, so the caller can hand it to
    /// `kernel_bridge::consume_autodischarge`. The if/else-if chain names the
    /// same three conditions the single `if` tested and in the same order, so
    /// the set of goals kept is unchanged: a goal is dropped iff it is
    /// trivial, or implied by its original, or (autoproving not excluded)
    /// matched by a usable database constraint.
    // Seven of the eight are the independent switches the two callers set
    // differently; bundling them into a parameter struct would only move the
    // same eight names one level out. Same deliberate exception as
    // `veripb_rules::elaboration::write_helpers`.
    #[allow(clippy::too_many_arguments)]
    #[inline]
    fn add_non_obvious_proofgoals(
        &self,
        substitution: &Substitution,
        unique_touched_constraint: HashSet<&ByAddress<Rc<DBConstraint>>>,
        add_derived_goals: bool,
        exclude_database_autoproving: bool,
        only_core_subproof: bool,
        record_autodischarges: bool,
        autodischarged: &mut Vec<AutoDischarge>,
    ) -> HashSet<Rc<DBConstraint>> {
        let mut unique_substituted_constraints =
            HashSet::with_hasher(RandomState::with_seeds(42, 42, 42, 42));
        // Iterate in *constraint-id* order, not hash order.
        //
        // `unique_touched_constraint` is a `HashSet` keyed by `ByAddress`, so
        // its iteration order is the order of allocator addresses -- which vary
        // from run to run under ASLR, with a fixed hasher seed or without one.
        // The *set* of proofgoals is unaffected, but the order they are
        // generated in is not, and that order reaches the artifact: it decides
        // propagation order, hence the RUP hints an elaborated proof records.
        // Measured before this: `rup_php65` elaborated to a different file on
        // every run -- six distinct hashes over three runs of each of two
        // binaries -- differing only in hint permutations, all re-checking to
        // the same verdict.
        //
        // That is not a wrong verdict, but a checker whose output is not a
        // function of its input cannot be reproduced, and worse, cannot be
        // tested reliably: a defect that shows up under one iteration order and
        // not another is flaky rather than absent, and the differential tests
        // in this tree would find it only by luck.
        let mut ordered: Vec<_> = unique_touched_constraint.into_iter().collect();
        ordered.sort_unstable_by_key(|constraint| constraint.get_some_id());
        for constraint in ordered {
            if add_derived_goals || constraint.is_core_constraint() {
                let substituted_constraint = Rc::new(constraint.substitute(substitution));
                // The following conditions have to consider a proofgoal non-obvious:
                // 1. The proofgoal is not trivial (... >= 1)
                // 2. The original constraint does not imply the proofgoal.
                // 3. No other database constraint is syntactially equivalent to the proofgoal. This is ignored, if:
                //     1. `exclude_database_autoproving` is true.
                //     2. We can only use core constraints for the subrpoof and the database constraint is not in the core set.
                let discharged = if substituted_constraint.is_trivial() {
                    Some(AutoDischarge::Trivial(
                        Rc::clone(constraint),
                        Rc::clone(&substituted_constraint),
                    ))
                } else if constraint.implies(&substituted_constraint) {
                    Some(AutoDischarge::Implied(
                        Rc::clone(constraint),
                        Rc::clone(&substituted_constraint),
                    ))
                } else if exclude_database_autoproving {
                    None
                } else {
                    match self.lookup(&substituted_constraint) {
                        Some(found) if !only_core_subproof || found.is_core_constraint() => {
                            Some(AutoDischarge::DbLookup(
                                Rc::clone(constraint),
                                Rc::clone(&substituted_constraint),
                                Rc::clone(found),
                            ))
                        }
                        _ => None,
                    }
                };
                match discharged {
                    Some(discharged) => {
                        if record_autodischarges {
                            autodischarged.push(discharged);
                        }
                    }
                    None => {
                        // Copy ids from the original constraint.
                        substituted_constraint.copy_ids(constraint);
                        // Check if constraint is already contained in unique substituted constraints.
                        if let Some(prev_entry) =
                            unique_substituted_constraints.replace(substituted_constraint)
                        {
                            let entry = unique_substituted_constraints.get(&prev_entry).unwrap();
                            entry.append_ids(Rc::into_inner(prev_entry).unwrap());
                        }
                    }
                }
            }
        }
        unique_substituted_constraints
    }

    /// Get the proofgoals from the formula for strengthening rules with respect to the substitution.
    ///
    /// Proofgoals that are trivial, implied by the original constraint, or that can be found in the database are not added as proofgoals.
    ///
    /// The second component lists those auto-discharged obligations when
    /// `record_autodischarges` is set; the caller must feed it to
    /// `kernel_bridge::consume_autodischarge` so the discharges are re-judged
    /// by the kernel instead of being trusted. With the flag off the vector
    /// stays empty and, `Vec::new` not allocating, the recording is free.
    #[inline]
    pub fn get_proofgoals(
        &mut self,
        substitution: &Substitution,
        add_derived_goals: bool,
        exclude_database_autoproving: bool,
        only_core_subproof: bool,
        record_autodischarges: bool,
    ) -> (HashSet<Rc<DBConstraint>>, Vec<AutoDischarge>) {
        debug_assert_eq!(self.len(), self.next_unique_index_id);

        self.update_occurrences_index();
        let mut unique_touched_constraints =
            HashSet::with_hasher(RandomState::with_seeds(42, 42, 42, 42));
        for &var_idx in substitution.syntactic_support() {
            // Constraints where the literal is mapped to true do not need to be considered as a proofgoal.
            match substitution.get(var_idx).unwrap() {
                SubstitutionValue::TRUE => {
                    if let Some(occurrences) = self
                        .occurrences
                        .get_constraints_for_lit(Lit::from_var(var_idx, true))
                    {
                        unique_touched_constraints.extend(occurrences.iter());
                    }
                }
                SubstitutionValue::FALSE => {
                    if let Some(occurrences) = self
                        .occurrences
                        .get_constraints_for_lit(Lit::from_var(var_idx, false))
                    {
                        unique_touched_constraints.extend(occurrences.iter());
                    }
                }
                _ => {
                    if let Some(occurrences) = self
                        .occurrences
                        .get_constraints_for_lit(Lit::from_var(var_idx, false))
                    {
                        unique_touched_constraints.extend(occurrences.iter());
                    }
                    if let Some(occurrences) = self
                        .occurrences
                        .get_constraints_for_lit(Lit::from_var(var_idx, true))
                    {
                        unique_touched_constraints.extend(occurrences.iter());
                    }
                }
            }
        }

        let mut autodischarged = Vec::new();
        if record_autodischarges {
            self.record_witness_satisfied_discharges(
                substitution,
                &unique_touched_constraints,
                add_derived_goals,
                &mut autodischarged,
            );
        }

        let exclude_database_autoproving = exclude_database_autoproving
            && unique_touched_constraints.len() < self.ignore_database_proofgoal_size;

        let goals = self.add_non_obvious_proofgoals(
            substitution,
            unique_touched_constraints,
            add_derived_goals,
            exclude_database_autoproving,
            only_core_subproof,
            record_autodischarges,
            &mut autodischarged,
        );
        (goals, autodischarged)
    }

    /// The obligations the loop above deliberately does *not* collect, for
    /// `--kernel-verify` to re-judge.
    ///
    /// When the witness maps a variable to `TRUE`, constraints containing that
    /// variable *positively* are skipped ("constraints where the literal is
    /// mapped to true do not need to be considered as a proofgoal"), and
    /// likewise for `FALSE` and the negated occurrences. That is sound —
    /// substituting a satisfied literal drops its term and lowers the degree
    /// by its coefficient, so `C` implies `C|w` — but it is an *implication
    /// argument*, and it is the fourth place a database proof obligation gets
    /// discharged without anything re-deriving it. Under `--kernel-verify`
    /// each such constraint is substituted and handed over as
    /// `AutoDischarge::Implied(C, C|w)`, so it goes through the same proved
    /// chain as an explicit `DBImplies` proofgoal.
    ///
    /// Constraints already collected as genuine goals are subtracted: one can
    /// be satisfied on one substituted variable and genuinely touched on
    /// another, and for that one the weakening argument does not apply — a
    /// real goal is generated instead. Derived constraints carry no obligation
    /// at all when only core goals are being generated, matching the filter in
    /// [`Self::add_non_obvious_proofgoals`].
    ///
    /// This costs one `substitute()` per satisfied constraint, so it is gated
    /// on the flag rather than done unconditionally.
    fn record_witness_satisfied_discharges(
        &self,
        substitution: &Substitution,
        unique_touched_constraints: &HashSet<&ByAddress<Rc<DBConstraint>>>,
        add_derived_goals: bool,
        autodischarged: &mut Vec<AutoDischarge>,
    ) {
        let mut seen: HashSet<&ByAddress<Rc<DBConstraint>>> =
            HashSet::with_hasher(RandomState::with_seeds(42, 42, 42, 42));
        // Scratch buffer for the id-order sort below, reused across the loop
        // so the ordering costs one amortized allocation for the whole call
        // rather than one per substituted variable.
        let mut ordered: Vec<&ByAddress<Rc<DBConstraint>>> = Vec::new();
        for &var_idx in substitution.syntactic_support() {
            // The literal the witness *satisfies*: the opposite polarity of
            // the one the loop above collects.
            let satisfied = match substitution.get(var_idx).unwrap() {
                SubstitutionValue::TRUE => Lit::from_var(var_idx, false),
                SubstitutionValue::FALSE => Lit::from_var(var_idx, true),
                // A variable mapped to another literal satisfies nothing
                // syntactically; both polarities are collected as goals.
                _ => continue,
            };
            let Some(occurrences) = self.occurrences.get_constraints_for_lit(satisfied) else {
                continue;
            };
            // Iterate in *constraint-id* order, for the same reason
            // `add_non_obvious_proofgoals` does: the occurrence list is a
            // `HashSet` keyed by `ByAddress`, so its iteration order is the
            // order of allocator addresses, which vary from run to run under
            // ASLR whatever the hasher seed. The *set* of discharges is
            // unaffected and so are the `--kernel-verify` counters they feed,
            // which only count; what moved was the order they reach
            // `kernel_bridge::consume_autodischarge` in, and hence which one a
            // kernel divergence would be reported against first. That is a
            // refusal whose reason is not a function of its input, on one of
            // the least travelled paths in the checker. Sorted here rather
            // than left to chance, so that a divergence is reproducible.
            ordered.clear();
            ordered.extend(occurrences.iter());
            ordered.sort_unstable_by_key(|constraint| constraint.get_some_id());
            for constraint in ordered.iter().copied() {
                if unique_touched_constraints.contains(constraint) || !seen.insert(constraint) {
                    continue;
                }
                if !(add_derived_goals || constraint.is_core_constraint()) {
                    continue;
                }
                let substituted = Rc::new(constraint.substitute(substitution));
                autodischarged.push(AutoDischarge::Implied(Rc::clone(constraint), substituted));
            }
        }
    }

    /// Get an iterator over the constraint IDs for the constraints that have not been deleted in the given `range` in the order of the constraint IDs.
    #[inline]
    pub fn get_undeleted(
        &self,
        range: Range<usize>,
    ) -> impl '_ + Iterator<Item = Result<usize, CheckingError>> {
        range
            .into_iter()
            .filter_map(|id| match self.is_undeleted(id) {
                Ok(true) => Some(Ok(id)),
                Ok(false) => None,
                Err(err) => Some(Err(err)),
            })
    }

    /// Get an iterator over the constraint entries in the database that have not been deleted starting from the first constraint that has not been added to the unique constraints. The constraints are in order of the constraint ID.
    #[inline]
    pub fn get_undeleted_non_unique_indexed(&self) -> impl '_ + Iterator<Item = &Rc<DBConstraint>> {
        self.entries[self.next_unique_index_id..self.len()]
            .iter()
            .flatten()
    }

    /// The length of the database is the number of entries including deleted constraint and duplicates.
    #[inline]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Returns `true` if there are no entries in the database including deleted constraints.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// The size of the database is the number of non-deleted (`Some(constraint)`) entries in the database.
    #[inline]
    pub fn size(&self) -> usize {
        self.entries.iter().flatten().count()
    }
}

impl ConstraintLookup for Database {
    type Error = CheckingError;

    fn get_entry_usize(&self, index: usize) -> Result<&Rc<DBConstraint>, Self::Error> {
        self.get_entry_usize(index)
    }
}

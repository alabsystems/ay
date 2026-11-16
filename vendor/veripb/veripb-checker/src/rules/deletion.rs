use std::rc::Rc;

use colored::Colorize;
use itertools::Itertools;
use veripb_formula::prelude::*;
use veripb_propagator::propagation_engine::PropagationEngine;
use veripb_rules::{
    Deletion, DeletionOption, DeletionOrigin,
    elaboration::{ConstraintLookup, Elaboratable, ElaborationError, Elaborator},
};

use super::Checkable;

use crate::{
    context::REQUIRED_RUP_STREAK,
    deletion_sequence::{DeletionSequence, DeletionSequenceEnum},
    prelude::*,
    rules::ScopeId,
};

#[derive(Debug)]
pub struct DeletionChecker {
    inner: Deletion,
    core_ids: Vec<usize>,
    derived_ids: Vec<usize>,
}

impl DeletionChecker {
    pub fn new(inner: Deletion) -> Self {
        Self {
            inner,
            core_ids: Vec::new(),
            derived_ids: Vec::new(),
        }
    }

    /// Get the actual deletions due to this deletion command.
    ///
    /// This is required, as we allow deletion by specification and deletion by ID in the same proof. Hence, we follow the following convention for deletions.
    ///
    /// - If a constraint is deleted by specification and there are more valid constraint IDs for this constraints than the number of times this constraint has been deleted by specification, then all constraint IDs stay valid. Otherwise, all constraint IDs become invalid and the constraint is deleted.
    /// - If a constraint is deleted by ID, then this ID is no longer valid for this constraint. If this causes that the number of valid IDs is at least the number deletions by specification, then all constraint IDs become invalid and the constraint is deleted.
    ///
    /// This function returns `true`, if at least one constraint ID that is actually deleted is in the core set.
    #[inline]
    fn get_actual_deletions(
        &mut self,
        context: &mut Context,
        database: &mut Database,
    ) -> Result<(), CheckingError> {
        (self.core_ids, self.derived_ids) = resolve_actual_deletions(
            &self.inner.identifier,
            &mut context.level_ids,
            &mut context.propagation_engine,
            database,
        )?;
        Ok(())
    }

    /// Check if deletion from core and deletion from derived set only deletes constraints from their respective set.
    #[inline]
    fn check_deletion_origin(&self) -> Result<(), CheckingError> {
        validate_deletion_origin(&self.inner.origin, &self.core_ids, &self.derived_ids)
    }

    /// Unchecked deletion can be used if all of the following conditions are met:
    /// (0. No explicit subproof is specified, but this might only be a temporary condition.)
    /// 1. If an order is loaded or strengthening-to-core is enabled, then check if all constraints are in the core set of constraints.
    #[inline]
    fn check_unchecked_deletion(
        &self,
        database: &mut Database,
        context: &mut Context,
    ) -> Result<(), CheckingError> {
        if self.inner.has_subproof {
            return Err(CheckingError::UncheckedWithSubproof);
        }

        if (context.active_order.is_some() || context.is_strengthening_to_core)
            && !database.all_constraints_in_core()
        {
            return Err(CheckingError::UncheckedDeletionDangerous);
        }

        Ok(())
    }

    /// Checked deletion check. We need to construct the proof goals and use heuristics similar to redundance-based strengthening.
    #[inline]
    fn check_checked_deletion(
        &mut self,
        constraint_id: usize,
        database: &mut Database,
        context: &mut Context,
    ) -> Result<Vec<Rc<DBConstraint>>, CheckingError> {
        context.check_witness(&self.inner.witness)?;

        let deleted_constraint = database.get_entry_usize(constraint_id)?.clone();
        let out_id = deleted_constraint.get_out_id(constraint_id);

        // Taken before the deletion so a discharge below is credited to the
        // core deletion it actually belongs to. See
        // `kernel_bridge::shadow_note_core_deletion_discharged`.
        let core_deletions_before = crate::kernel_bridge::shadow_core_deletions(context);

        // Remove constraint from database and from propagator.
        database.delete_constraint(context, constraint_id)?;

        // Maybe the deletion is actually just implied by RUP. We only do this check if we had enough success autoproving the subproof at top-level without using the witness.
        if !self.inner.has_subproof
            && (context.rup_streak >= REQUIRED_RUP_STREAK || self.inner.witness.is_empty())
        {
            // Check if constraint is in DB.
            database.update_unique_index(&mut context.propagation_engine)?;
            if let Some(constraint) = database.lookup(&deleted_constraint)
                && constraint.is_core_constraint()
            {
                // Both `consume_*` entry points below record a SKIP and
                // return `Ok` when the kernel could not re-derive the step, so
                // calling them is not evidence that it did. The counter going
                // up is. Credit the deletion only then -- otherwise a run
                // whose kernel re-derivation stood down would have its
                // obligation credited on the checker's say-so, which is the
                // exact substitution this whole development refuses.
                let verified_before = context.kernel_stats.db_lookup_verified;
                crate::kernel_bridge::consume_db_lookup(
                    context,
                    &deleted_constraint.constraint,
                    &constraint.constraint,
                )?;
                // `VeriPbCore.dbBack_delete_checked` discharged: the deleted
                // constraint is still a core slot under another id, so
                // `holdsAllO_get` gives `Holds b c` from
                // `HoldsAllO b (setNone i CO)` with nothing else assumed.
                if context.kernel_stats.db_lookup_verified > verified_before {
                    crate::kernel_bridge::shadow_note_core_deletion_discharged(
                        context,
                        core_deletions_before,
                    );
                }
                if context.trace_enabled {
                    println!("* constraint is in DB already")
                }
                if let Some(elaborator) = context.elaborator.as_mut() {
                    elaborator
                        .write_existing_constraint_checked_deletion(out_id.unwrap(), constraint);
                }
                return Ok(vec![]);
            }
            // Check if constraint is RUP.

            context.propagation_engine.collect_kernel_certificate = context.config.kernel_verify;
            database.update_propagation_index(&mut context.propagation_engine)?;
            if context
                .propagation_engine
                .reverse_unit_propagation_check(
                    &context.var_names,
                    &[],
                    Some(&deleted_constraint),
                    true,
                    context.elaborator.is_some(),
                    false,
                )?
                .is_conflict()
            {
                // Same rule as the lookup path above: the skip-and-continue
                // shape of `consume_rup_conflict` means only the counter
                // advancing proves the kernel re-derived this RUP.
                let verified_before = context.kernel_stats.rup_verified;
                crate::kernel_bridge::consume_rup_conflict(
                    context,
                    database,
                    Some(&deleted_constraint.constraint),
                )?;
                // `VeriPbCore.dbBack_delete_checked` discharged: the RUP ran
                // with `only_core = true` and AFTER `delete_constraint`, so
                // the database it refuted `~c` against is exactly
                // `setNone i CO` -- the obligation, not a weaker one over the
                // whole database.
                if context.kernel_stats.rup_verified > verified_before {
                    crate::kernel_bridge::shadow_note_core_deletion_discharged(
                        context,
                        core_deletions_before,
                    );
                }
                if context.trace_enabled {
                    println!("* constraint is RUP *")
                }
                if let Some(elaborator) = context.elaborator.as_mut() {
                    elaborator.write_rup_checked_deletion(
                        out_id.unwrap(),
                        &context.propagation_engine.rup_hints,
                    );
                }
                return Ok(vec![]);
            }
            context.rup_streak = std::num::Saturating(0);
        }

        // NO SKIP. The kernel models this step, and models it as the simplest
        // one it has: `VeriPbCore.DbOkF.delete`, which is UNCONDITIONAL.
        //
        // That looks too easy beside the witness machinery this rule runs, so
        // it is worth saying exactly why the two do not need to agree. VeriPB
        // requires a witness here because `delc` removes a constraint from the
        // CORE, and the core is what its later reasoning treats as the current
        // formula -- weaken that and a bound already proved may stop holding.
        // The kernel's invariant is not stated over the current database at
        // all: `DbFull` quantifies over models of `F`, the formula on disk,
        // which no rule can change. Deleting from the database only makes a
        // companion EASIER to find and the database HARDER to refute, so the
        // verdict can only get weaker, never wrong.
        //
        // The subproof's own goals are still discharged and still kernel
        // re-judged; what is gone is a `skip` that reported a modelled step as
        // unmodelled.

        let mut subproof_context = SubproofContext::new(database.len());
        // Paired with the deleted constraint's own goal below, which is the
        // second conjunct of `dbBackSat_delete_red`'s `hgoal`.
        let mut red_goal_slots: Vec<(usize, veripb_formula::prelude::PBConstraintEnum)> =
            Vec::new();

        // We need to elaborate the delc rule line here, as autoproving might generate extra lines.
        if let Some(elaborator) = &mut context.elaborator {
            elaborator.write_delc_subproof_header(
                out_id.unwrap(),
                Some(&self.inner.witness),
                Some(&context.var_names),
            );
        }

        if context.is_strengthening_to_core {
            subproof_context.proof_by_contradiction_subproof = true;
        }
        if !context.is_strengthening_to_core || context.major_version == Some(2) {
            // Generate the proofgoals, starting with the constraint to be introduced.
            let deleted_goal = Rc::new(deleted_constraint.substitute(&self.inner.witness));
            red_goal_slots.push((constraint_id, deleted_goal.constraint.clone()));
            subproof_context.add_single_proofgoal(deleted_goal, Some(ScopeId::LessEqual));
            if context.trace_enabled {
                println!("  ** proofgoal from satisfying deleted constraint **");
                subproof_context.trace_internal_proofgoal_back(&context.var_names);
            }

            // Proofgoals from order.
            if let Some(active_order) = &mut context.active_order {
                for proofgoal in active_order.get_proofgoals(&self.inner.witness) {
                    subproof_context.add_internal_proofgoal(proofgoal);
                }
                if context.trace_enabled {
                    println!("  ** proofgoals from order **");
                    for id in 2..subproof_context.internal_proofgoal_len() {
                        subproof_context.trace_internal_proofgoal(id, &context.var_names);
                    }
                }
            }

            // Proofgoal from the objective.
            if let Some(objective) = &context.objective {
                subproof_context.add_single_proofgoal(
                    objective.get_proofgoal(&self.inner.witness),
                    Some(ScopeId::LessEqual),
                );
                if context.trace_enabled {
                    println!("  ** proofgoal from objective **");
                    subproof_context.trace_internal_proofgoal_back(&context.var_names);
                }
            }

            // Get core database proofgoals.
            subproof_context.declare_database_obligations(Some(ScopeId::LessEqual));
            database.update_unique_index(&mut context.propagation_engine)?;
            let (goals, autodischarged) = database.get_proofgoals(
                &self.inner.witness,
                false,
                context.elaborator.is_some(),
                true,
                context.config.kernel_verify,
            );
            // The goal-to-slot pairing `dbBackSat_delete_red` needs, built the
            // same way `red` builds its own: CORE ids only, because `CO` holds
            // derived constraints as `none` and they raise no obligation --
            // which is exactly why these goals were asked for with
            // `add_derived_goals = false`.
            let note = |source: &Rc<DBConstraint>,
                            image: &Rc<DBConstraint>,
                            out: &mut Vec<(usize, veripb_formula::prelude::PBConstraintEnum)>| {
                let header = source.header.borrow();
                for &id in header.core_ids.iter() {
                    out.push((id, image.constraint.clone()));
                }
            };
            // Obligations proofgoal generation discharged by itself are
            // re-judged through the same entry points their explicit
            // counterparts use.
            for discharged in &autodischarged {
                use crate::database::AutoDischarge;
                match discharged {
                    AutoDischarge::Trivial(source, image)
                    | AutoDischarge::Implied(source, image)
                    | AutoDischarge::DbLookup(source, image, _) => {
                        note(source, image, &mut red_goal_slots)
                    }
                }
                crate::kernel_bridge::consume_autodischarge(context, discharged)?;
            }
            for constraint in goals {
                note(&constraint, &constraint, &mut red_goal_slots);
                subproof_context.add_database_proofgoal(
                    constraint,
                    false,
                    Some(ScopeId::LessEqual),
                );
            }
            if context.trace_enabled {
                subproof_context.trace_database_proofgoals(&context.var_names);
            }
        }

        let negated = Rc::new(deleted_constraint.negate());

        if self.inner.has_subproof {
            subproof_context.additional_hint = Some(database.len());
            context.inside_strengthening_subproof = true;
            subproof_context.witness = std::mem::take(&mut self.inner.witness);
            context
                .subcontexts
                .push(Subcontext::Subproof(subproof_context));
            Ok(vec![negated])
        } else {
            if let Some(elaborator) = context.elaborator.as_mut() {
                negated.set_out_id(0, elaborator.inc_id());
            }

            // An unchanged skip census across `finalize` is what says every
            // goal was KERNEL-discharged rather than merely accepted -- the
            // same test `red`'s `qed` applies, and the same reason: the
            // `consume_*` entry points record a skip and return `Ok` when the
            // kernel cannot re-derive a step.
            let skips_before = context.kernel_stats.total_skips();
            subproof_context
                .finalize(context, database, &[negated])
                .map_err(|e| match e {
                    CheckingError::AutoprovingFailed(goal_id) => {
                        CheckingError::CheckedDeletionAutoprovingFailed(goal_id, out_id)
                    }
                    e => e,
                })?;
            let discharged_cleanly = context.kernel_stats.total_skips() == skips_before;
            crate::kernel_bridge::offer_red_deletion(
                context,
                database,
                &self.inner.witness,
                &deleted_constraint.constraint,
                constraint_id,
                &red_goal_slots,
                discharged_cleanly,
                core_deletions_before,
            );
            Ok(vec![])
        }
    }
}

/// Resolve a deletion command to the concrete (core, derived) constraint ids it deletes.
///
/// We allow deletion by specification and deletion by ID in the same proof, following this
/// convention:
/// - If a constraint is deleted by specification and there are more valid constraint IDs than the
///   number of times it has been deleted by specification, all IDs stay valid; otherwise all IDs
///   become invalid and the constraint is deleted.
/// - If a constraint is deleted by ID, that ID is no longer valid; if this brings the valid-ID
///   count to at most the deletions-by-specification count, all IDs become invalid.
pub fn resolve_actual_deletions(
    identifier: &DeletionOption,
    level_ids: &mut [Vec<usize>],
    propagation_engine: &mut PropagationEngine,
    database: &mut Database,
) -> Result<(Vec<usize>, Vec<usize>), CheckingError> {
    let mut core_ids = Vec::new();
    let mut derived_ids = Vec::new();
    match identifier {
        DeletionOption::Id(constraint_ids) => {
            for &id in constraint_ids {
                let index = database.normalize_id(id) as usize;
                let (core, derived) = database.get_entry_usize(index)?.get_del_by_id(index);
                core_ids.extend(core);
                derived_ids.extend(derived);
            }
        }
        DeletionOption::Range((start, end)) => {
            let start_index = database.normalize_id(*start) as usize;
            let end_index = database.normalize_id(*end) as usize;
            for index_result in database.get_undeleted(start_index..end_index) {
                let index = index_result?;
                let (core, derived) = database.get_entry_usize(index)?.get_del_by_id(index);
                core_ids.extend(core);
                derived_ids.extend(derived);
            }
        }
        DeletionOption::Spec(constraint) => {
            database.update_unique_index(propagation_engine)?;
            match database.lookup(constraint) {
                Some(db_constraint) => {
                    let (core, derived) = db_constraint.get_del_by_spec();
                    core_ids.extend(core);
                    derived_ids.extend(derived);
                }
                None => return Err(CheckingError::not_found(constraint, false)),
            }
        }
        DeletionOption::Wipe(level) => {
            let number_levels = level_ids.len();
            // `level_ids` only grows when a `wiplvl`/level rule reaches that
            // level, so a `del wipe` naming a higher one indexes past the end.
            // Slicing there aborts the process (the release profile is
            // `panic = "abort"`), which is a crash on ordinary proof text
            // rather than a diagnosis.
            if *level > number_levels {
                return Err(CheckingError::WipeLevelOutOfRange(
                    *level,
                    number_levels.saturating_sub(1),
                ));
            }
            for ids in &mut level_ids[*level..number_levels] {
                for index in ids.drain(..) {
                    if let Some(constraint) = database.get_entry_optionally_deleted_usize(index)? {
                        let (core, derived) = constraint.get_del_by_id(index);
                        core_ids.extend(core);
                        derived_ids.extend(derived);
                    }
                }
            }
        }
    }
    // Remove duplicates from the actually deleted IDs.
    core_ids.sort_unstable();
    core_ids.dedup();
    derived_ids.sort_unstable();
    derived_ids.dedup();
    Ok((core_ids, derived_ids))
}

/// Enforce a deletion command's origin: a `Core` command must delete no derived ids, and a
/// `Derived` command must delete no core ids.
pub fn validate_deletion_origin(
    origin: &DeletionOrigin,
    core_ids: &[usize],
    derived_ids: &[usize],
) -> Result<(), CheckingError> {
    match origin {
        DeletionOrigin::Core => {
            if let Some(&id) = derived_ids.first() {
                return Err(CheckingError::DeletionFromCoreDeletesDerived(id));
            }
        }
        DeletionOrigin::Derived => {
            if let Some(&id) = core_ids.first() {
                return Err(CheckingError::DeletionFromDerivedDeletesCore(id));
            }
        }
        DeletionOrigin::Unknown => {}
    }
    Ok(())
}

impl Checkable for DeletionChecker {
    #[inline]
    fn kernel_slot_taint(&self) -> &'static str {
        // Checked deletion introduces the negated deleted constraint as the
        // premise of its subproof; the deletion-witness meta-step that
        // licenses it is outside the proved kernel.
        "checked-deletion-premise"
    }

    fn compute(
        &mut self,
        context: &mut Context,
        database: &mut Database,
    ) -> Result<Vec<Rc<DBConstraint>>, CheckingError> {
        // Get what constraints and IDs are actually deleted by this rule.
        self.get_actual_deletions(context, database)?;
        // Get which deleted IDs are from the core and which are from the derived set.
        self.check_deletion_origin()?;

        // Check preconditions:
        // If there is a subproof, then there should be exactly one core constraint.
        if self.inner.has_subproof && self.core_ids.len() != 1 {
            return Err(CheckingError::DeletionSubproofNotOneCoreConstraint);
        }
        // If there are more than one core constraint, then the witness must be empty.
        if self.core_ids.len() > 1 && !self.inner.witness.is_empty() {
            return Err(CheckingError::DeletionMultipleCoreWithWitness);
        }
        // If strengthening to core is enabled, then checked deletion cannot use a witness.
        //
        // `proof_format_overview.md` used to give this condition as "an order
        // is loaded *or* strengthening-to-core is enabled"; only the second
        // half belongs here, and the asymmetry is deliberate. Under
        // strengthening-to-core `check_checked_deletion` takes the
        // proof-by-contradiction branch and generates no substituted
        // proofgoals at all, so a witness would be accepted without anything
        // ever checking it -- hence the refusal. Under a loaded order it does
        // generate them, and among them the order's own: it calls
        // `ActiveOrder::get_proofgoals` on exactly the same line `red` does,
        // so the witness owes `O(z|w, z)` and cannot worsen the order.
        // Refusing a witness here as well would reject sound proofs; see
        // `tests/instances/{correct,incorrect}/version{2,3}/checked_deletion_witness_*`
        // for the minimal pair that differs only in whether the witness
        // worsens the order.
        if context.is_strengthening_to_core
            && !self.core_ids.is_empty()
            && !self.inner.witness.is_empty()
        {
            return Err(CheckingError::DeletionWithWitnessWhileStrengtheningToCore);
        }

        // We should check for a checked deletion if
        if context.strong_solution_guarantees
            || self.inner.has_subproof
            || context.active_order.is_some()
            || context.is_strengthening_to_core
        {
            context.only_core = true;
            while let Some(id) = self.core_ids.pop() {
                if context.trace_enabled {
                    println!("  Checked deletion of ID: {}", id.to_string().yellow());
                }
                if self.inner.has_subproof {
                    return self.check_checked_deletion(id, database, context);
                } else {
                    if let Some(elaborator) = &mut context.elaborator {
                        elaborator.enable_buffered_proof();
                    }
                    match self.check_checked_deletion(id, database, context) {
                        Ok(_) => {
                            if let Some(elaborator) = &mut context.elaborator {
                                elaborator.write_buffered_proof();
                            }
                        }
                        Err(CheckingError::CheckedDeletionAutoprovingFailed(goal_id, out_id)) => {
                            if context.config.force_checked_deletion {
                                return Err(CheckingError::ForceCheckedDeletionFailed(goal_id));
                            }
                            if context.strong_solution_guarantees {
                                log::warn!(
                                    "Switching from stronger to weaker guarantee using unchecked deletion. This means that any solution after this deletion is not necessarily a solution for the original problem."
                                );
                                // Remember that the downgrade was not requested
                                // by the user: the guarantee this run can give
                                // is weaker than the one it was asked for, which
                                // has to be visible in the verdict and the exit
                                // code and not only in this warning on stderr.
                                context.unchecked_deletion_fallback = true;
                            }
                            if let Some(elaborator) = &mut context.elaborator {
                                elaborator.forget_buffered_proof();
                                elaborator.write_unchecked_deletion(out_id.unwrap());
                                warn_elaborated_deletion_obligation(&[out_id.unwrap()]);
                            }
                            context.strong_solution_guarantees = false;
                            self.check_unchecked_deletion(database, context)?;
                            break;
                        }
                        e => return e,
                    }
                }
            }
            context.only_core = false;
        } else if !self.core_ids.is_empty() {
            self.check_unchecked_deletion(database, context)?;
        }

        Ok(vec![])
    }

    fn get_deleted(
        &self,
        _database: &Database,
    ) -> Result<Option<DeletionSequenceEnum<'_>>, CheckingError> {
        Ok(Some(DeletionSequenceEnum::Deletion(self)))
    }
}

impl From<Deletion> for DeletionChecker {
    fn from(inner: Deletion) -> Self {
        Self::new(inner)
    }
}

impl DeletionSequence for DeletionChecker {
    #[inline]
    fn get_deleted_ids(&self) -> impl Iterator<Item = &usize> {
        self.core_ids.iter().chain(self.derived_ids.iter())
    }
}

impl Elaboratable for DeletionChecker {
    fn elaborate<C: ConstraintLookup, V: VarNameLookup>(
        &self,
        elaborator: &mut Elaborator,
        database: &C,
        _var_names: &V,
    ) -> Result<(), ElaborationError> {
        if !self.derived_ids.is_empty() {
            elaborator.write_derived_deletions(&self.derived_ids, database);
        }

        if !self.core_ids.is_empty() {
            elaborator.write_core_deletions_no_subproof(&self.core_ids, database);
            let out_ids: Vec<usize> = self
                .core_ids
                .iter()
                .filter_map(|&index| {
                    database
                        .get_entry_usize(index)
                        .ok()
                        .and_then(|constraint| constraint.get_out_id(index))
                })
                .collect();
            warn_elaborated_deletion_obligation(&out_ids);
        }

        Ok(())
    }
}

/// Say out loud that the elaborated proof states a deletion obligation this run
/// did not discharge.
///
/// The kernel proof format has no rule for an *unchecked* core deletion — a
/// bare `delc <id>;` is a checked core deletion whose obligation is left to the
/// consumer (see
/// [`Elaborator::write_unchecked_deletion`](veripb_rules::elaboration::Elaborator::write_unchecked_deletion)).
/// That is what keeps the artifact honest, but it also means the downgrade
/// itself cannot be written into the artifact, so it is reported here instead:
/// the consumer of this proof will do work this run skipped, and its verdict
/// may consequently be stronger (or the proof may be refused) where this run
/// only claimed the weaker guarantee.
fn warn_elaborated_deletion_obligation(out_ids: &[usize]) {
    if out_ids.is_empty() {
        return;
    }
    let ids = out_ids.iter().map(usize::to_string).join(" ");
    log::warn!(
        "Elaborating a core deletion whose check was not discharged: the elaborated proof \
         writes `delc {ids};`, which is a *checked* core deletion, because the proof format \
         has no unchecked one. Whoever checks the elaborated proof must therefore discharge \
         that obligation or lower its guarantee as this run did, and may reach a different \
         verdict from this run's."
    );
}

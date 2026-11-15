use std::{ops::Range, rc::Rc};

use veripb_formula::prelude::*;
use veripb_propagator::propagation_engine::PropagationEngine;
use veripb_rules::{
    EndSubproof,
    elaboration::{ConstraintLookup, Elaboratable, ElaborationError, Elaborator},
};

use crate::{
    deletion_sequence::DeletionSequenceEnum, order_context::OrderPhase, prelude::*,
    proofgoal_context::ProofgoalContext,
};

#[derive(Debug)]
pub struct EndSubproofChecker {
    inner: EndSubproof,
    is_elaborated: bool,
    subproof_id_range: Range<usize>,
    replacement_database: Option<Box<Database>>,
    replacement_prop_engine: Option<Box<PropagationEngine>>,
    qed_subcontext: bool,
    add_to_core: bool,
}

impl EndSubproofChecker {
    pub fn new(inner: EndSubproof) -> Self {
        Self {
            inner,
            is_elaborated: false,
            subproof_id_range: 0..0,
            replacement_database: None,
            replacement_prop_engine: None,
            qed_subcontext: false,
            add_to_core: false,
        }
    }

    /// End a subproof subcontext.
    #[inline]
    fn end_subproof(
        &mut self,
        context: &mut Context,
        database: &mut Database,
        subproof_context: SubproofContext,
    ) -> Result<Vec<Rc<DBConstraint>>, CheckingError> {
        self.subproof_id_range = subproof_context.subproof_start_id..database.len();
        // The `red` justification for the one constraint this `qed` stores,
        // read BEFORE `finalize` consumes the context.
        //
        // The witness is CLONED, never taken: `use_toplevel_rup_check` reads
        // its length to decide whether the top-level RUP shortcut runs, so
        // moving it out would change which proofs are ACCEPTED -- a
        // verification detail silently altering the checker's verdict.
        let is_dom = subproof_context.offers_dom_justification;
        let red_offer = (context.config.kernel_verify
            && (subproof_context.offers_red_justification || is_dom)
            && subproof_context.to_add.len() == 1)
            .then(|| {
                (
                    subproof_context.witness.clone(),
                    subproof_context.to_add[0].clone(),
                    subproof_context.red_goal_slots.clone(),
                    subproof_context.red_derived_slots.clone(),
                )
            });
        let had_objective_update = subproof_context.objective_update.is_some();
        // Snapshot across the discharges below: an unchanged skip census is
        // what says every goal was KERNEL-justified, not merely accepted.
        let skips_before = context.kernel_stats.total_skips();
        let result = if let Some(hint) = &mut self.inner.optional_hint {
            *hint = database.normalize_id(*hint);
            if !database.get_entry_usize(*hint as usize)?.is_contradicting() {
                return Err(CheckingError::HintNoContradiction(*hint));
            }
            // This contradiction decides the subproof, and the subproof's
            // constraints are deleted at `qed`, so it must be kernel
            // re-judged here — conclusion-time re-judging can never cover it.
            crate::kernel_bridge::kernel_check_contradiction_id(context, database, *hint)?;
            subproof_context.finalize_unchecked(context)
        } else {
            // `finalize` will already elaborate the `qed` and write the final `qed` for the subproof.
            self.is_elaborated = true;
            // Need to check that all remaining proofgoals can be proven.
            subproof_context.finalize(context, database, &[])
        };

        // After the goals are discharged, and after every bridge call
        // `finalize` makes -- all of which are DISCHARGE forms that offer
        // nothing -- so the pending queue holds exactly this contribution when
        // `shadow_record_added` consumes it for the single constraint
        // `finalize_unchecked` returns. The subproof's own slots are still in
        // the shadow here (deletion happens after the add), which is required
        // rather than incidental: the theorem is instantiated at the database
        // as it stands when the constraint is appended.
        // An `obju` subproof carries its update here; its two equality goals
        // discharged inside `finalize` above, so an unchanged skip census is
        // what says the agreement `DbOkF.improve` needs was KERNEL-established.
        if result.is_ok() && context.config.kernel_verify && had_objective_update {
            let verified = context.kernel_stats.total_skips() == skips_before;
            crate::kernel_bridge::note_objective_update(context, verified);
        }
        if result.is_ok() {
            if let Some((witness, constraint, goal_slots, derived_slots)) = red_offer {
                let discharged_cleanly = context.kernel_stats.total_skips() == skips_before;
                let offer = if is_dom {
                    crate::kernel_bridge::offer_dom
                } else {
                    crate::kernel_bridge::offer_red
                };
                offer(
                    context,
                    &witness,
                    &constraint.constraint,
                    &goal_slots,
                    discharged_cleanly,
                    &derived_slots,
                );
            }
        }

        // If the subcontext below is not a `Subproof` or `Proofgoal`, then we definitely end the only core subproof.
        match context.subcontexts.last() {
            Some(Subcontext::Proofgoal(_)) | Some(Subcontext::Subproof(_)) => (),
            _ => context.only_core = false,
        }

        result
    }

    /// End a proofgoal subcontext.
    #[inline]
    fn end_proofgoal(
        &mut self,
        context: &mut Context,
        database: &mut Database,
        proofgoal_context: ProofgoalContext,
    ) -> Result<Vec<Rc<DBConstraint>>, CheckingError> {
        self.subproof_id_range = proofgoal_context.subproof_start_id..database.len();
        if let Some(hint) = &mut self.inner.optional_hint {
            *hint = database.normalize_id(*hint);
            if !database.get_entry_usize(*hint as usize)?.is_contradicting() {
                return Err(CheckingError::HintNoContradiction(*hint));
            }
            // This contradiction discharges the proofgoal; re-judge it
            // through the kernel here — the subproof-range constraints are
            // gone by conclusion time.
            crate::kernel_bridge::kernel_check_contradiction_id(context, database, *hint)?;
            // Fix that version 2.0 `red` steps with empty witness are elaborated to `pbc` correctly.
            // The guard is `discharges_pbc_contradiction`, not merely
            // `proof_by_contradiction_subproof`: the premises must be entailed
            // by the enclosing database, or the contradiction was bought with
            // an extra assumption. See `crate::rules::ProofgoalChecker`.
            if proofgoal_context.discharges_pbc_contradiction
                && let Some(Subcontext::Subproof(subsubcontext)) = context.subcontexts.last_mut()
            {
                self.is_elaborated = true;
                subsubcontext.contradiction_proven = true;
                if context.elaborator.is_some() {
                    subsubcontext.contradiction_output_id = database
                        .get_entry_usize(*hint as usize)?
                        .get_out_id(*hint as usize)
                        .expect("Constraint should have output ID.");
                }
            }
            Ok(vec![])
        } else {
            // Need to check that contradiction has been derived.
            if database
                .get_entry_usize(database.len() - 1)?
                .is_contradicting()
            {
                self.inner.optional_hint = Some(database.len() as isize - 1);
            } else if let Some(id) = database.contains_contradiction() {
                self.inner.optional_hint = Some(id as isize);
            } else {
                return Err(CheckingError::ProofgoalEndContradicitionNotObvious);
            }
            // One call covers both hintless resolutions above (last
            // constraint and database scan): the found contradiction decides
            // the proofgoal, so it is kernel re-judged where it fires.
            crate::kernel_bridge::kernel_check_contradiction_id(
                context,
                database,
                self.inner.optional_hint.unwrap(),
            )?;
            // Fix that version 2.0 `red` steps with empty witness are elaborated to `pbc` correctly.
            // Same stronger guard as in the hinted branch above.
            if proofgoal_context.discharges_pbc_contradiction
                && let Some(Subcontext::Subproof(subsubcontext)) = context.subcontexts.last_mut()
            {
                let hint = self.inner.optional_hint.unwrap() as usize;
                self.is_elaborated = true;
                subsubcontext.contradiction_proven = true;
                if context.elaborator.is_some() {
                    subsubcontext.contradiction_output_id = database
                        .get_entry_usize(hint)?
                        .get_out_id(hint)
                        .expect("Constraint should have output ID.");
                }
            }
            Ok(vec![])
        }
    }
}

impl From<EndSubproof> for EndSubproofChecker {
    fn from(inner: EndSubproof) -> Self {
        Self::new(inner)
    }
}

impl Checkable for EndSubproofChecker {
    fn compute(
        &mut self,
        context: &mut Context,
        database: &mut Database,
    ) -> Result<Vec<Rc<DBConstraint>>, CheckingError> {
        if let Some(subcontext) = context.subcontexts.pop() {
            match subcontext {
                Subcontext::Subproof(mut subproof_context) => {
                    if subproof_context.current_scope.is_some() {
                        subproof_context.current_scope = None;
                        self.subproof_id_range = subproof_context.scope_start_id..database.len();
                        context
                            .subcontexts
                            .push(Subcontext::Subproof(subproof_context));
                        return Ok(vec![]);
                    }
                    self.qed_subcontext = true;
                    self.add_to_core = subproof_context.add_to_core;
                    self.end_subproof(context, database, subproof_context)
                }
                Subcontext::Proofgoal(proofgoal_context) => {
                    self.qed_subcontext = true;
                    self.end_proofgoal(context, database, proofgoal_context)
                }
                Subcontext::Order(mut order_context) => {
                    if self.inner.optional_hint.is_some() {
                        return Err(CheckingError::EndNoHintAllowed);
                    }
                    if order_context.inside_vars {
                        order_context.inside_vars = false;
                        if !order_context.left_vars_defined {
                            return Err(CheckingError::LeftVarsUndefined);
                        }
                        if !order_context.right_vars_defined {
                            return Err(CheckingError::RightVarsUndefined);
                        }
                        // `left` and `right` name the two sides of the same
                        // relation, so the lists must be the same length.
                        // `OrderRightVariablesRule` checks this when `right` is
                        // parsed, which is enough for version 3.0 (its grammar
                        // admits each list once, in order), but the version 2.0
                        // parser dispatches line by line and happily accepts a
                        // second, longer `left` afterwards. Everything
                        // downstream then zips the two lists with `izip!` and
                        // silently truncates.
                        if !order_context
                            .constructed_order
                            .check_symmetric_left_and_right_variables()
                        {
                            return Err(CheckingError::AsymmetricOrderVariables);
                        }
                        if !order_context.aux_vars_defined {
                            if context.major_version >= Some(3) {
                                if let Some(elaborator) = context.elaborator.as_mut() {
                                    elaborator.write_empty_aux();
                                }
                            } else {
                                return Err(CheckingError::AuxVarsUndefined);
                            }
                        }

                        order_context.phase = OrderPhase::Variables;
                        context.subcontexts.push(Subcontext::Order(order_context));
                        return Ok(vec![]);
                    }
                    if order_context.inside_def {
                        order_context.inside_def = false;
                        order_context.phase = OrderPhase::Definition;
                        context.subcontexts.push(Subcontext::Order(order_context));
                        return Ok(vec![]);
                    }

                    // The order's own `end`. `def` is mandatory: without it the
                    // definition is empty, every side condition below holds
                    // vacuously, and the resulting "order" relates nothing --
                    // which `load_order` would then accept. The version-3
                    // grammar makes `def` mandatory; this is the same
                    // requirement, where the version-2 dialect also meets it.
                    if order_context.phase < OrderPhase::Definition {
                        return Err(CheckingError::OrderBlockOutOfSequence {
                            block: "end",
                            expected: order_context.phase.expected_next(),
                        });
                    }

                    // Check if reflexivity and transitivity have been proven.
                    if !order_context.reflexivity_proven
                        && !order_context.autoprove_reflexivity(context)?
                    {
                        return Err(CheckingError::ReflexivityProofFailed);
                    }
                    if !order_context.transitivity_proven && !order_context.autoprove_transitivity()
                    {
                        return Err(CheckingError::TransitivityProofFailed);
                    }

                    // The kernel DOES model the order now, and needs exactly
                    // ONE property of it: TRANSITIVITY
                    // (`VeriPbCore.dbOkF_dom_from_preorder`). Reflexivity is
                    // not required and irreflexivity is not assumed -- a `dom`
                    // step discharges the STRICT part of the preorder, and the
                    // strict part of a transitive relation is irreflexive for
                    // free.
                    //
                    // Transitivity comes from a real subproof: `autoprove_
                    // transitivity` always declines, so there is no path that
                    // sets it without one. Those goals discharge through the
                    // ordinary path, so an unchanged skip census across the
                    // whole definition block is what says the kernel
                    // established it rather than the checker merely accepting
                    // it. Anything the kernel could not justify -- inside the
                    // transitivity proof or anywhere else in the block --
                    // leaves the order unverified, and every `dom` that loads
                    // it is then refused.
                    if context.config.kernel_verify {
                        let verified = context.kernel_stats.total_skips()
                            == order_context.kernel_skips_at_open;
                        crate::kernel_bridge::note_order_definition(
                            context,
                            &order_context.name,
                            verified,
                        );
                        if !verified {
                            context.kernel_stats.skip("order-definition-unmodelled");
                        }
                    }

                    // Restore database.
                    self.replacement_database = Some(order_context.stored_database);
                    self.replacement_prop_engine = Some(order_context.stored_prop_engine);

                    // Add successfully proven order to context.
                    context
                        .orders
                        .insert(order_context.name, order_context.constructed_order);

                    // Recover old context state.
                    if let Some(elaborator) = context.elaborator.as_mut() {
                        elaborator.current_id = order_context.stored_elaborator_id;
                    }
                    context.active_order = *order_context.stored_active_order;

                    Ok(vec![])
                }
                Subcontext::Reflexivity(reflexivity_context) => {
                    // Check if a proof for reflexivity has been provided.
                    if !reflexivity_context.is_proven {
                        return Err(CheckingError::ReflexivityProofMissing);
                    }
                    let order_context = match context.subcontexts.last_mut().unwrap() {
                        Subcontext::Order(order_context) => order_context,
                        _ => unreachable!(),
                    };
                    order_context.reflexivity_proven = true;
                    order_context.phase = OrderPhase::Reflexivity;
                    Ok(vec![])
                }
                Subcontext::Transitivity(mut transitivity_context) => {
                    if transitivity_context.inside_vars {
                        transitivity_context.inside_vars = false;
                        context
                            .subcontexts
                            .push(Subcontext::Transitivity(transitivity_context));
                        return Ok(vec![]);
                    }
                    // Check if a proof for transitivity has been provided.
                    if !transitivity_context.is_proven {
                        return Err(CheckingError::TransitivityProofMissing);
                    }
                    let order_context = match context.subcontexts.last_mut().unwrap() {
                        Subcontext::Order(order_context) => order_context,
                        _ => unreachable!(),
                    };
                    order_context.transitivity_proven = true;
                    order_context.phase = OrderPhase::Transitivity;
                    Ok(vec![])
                }
                Subcontext::Specification(spec_context) => {
                    let order_context = match context.subcontexts.last_mut().unwrap() {
                        Subcontext::Order(order_context) => order_context,
                        _ => unreachable!(),
                    };

                    for constraint in database.entries.iter().flatten() {
                        order_context
                            .constructed_order
                            .specification
                            .push(constraint.clone());
                    }

                    order_context.phase = OrderPhase::Specification;

                    // Restore database.
                    self.replacement_database = Some(spec_context.stored_database);
                    self.replacement_prop_engine = Some(spec_context.stored_prop_engine);
                    if let Some(elaborator) = context.elaborator.as_mut() {
                        elaborator.current_id = spec_context.stored_elaborator_id;
                    }

                    Ok(vec![])
                }
            }
        } else {
            Err(CheckingError::NoOpenSubcontext)
        }
    }

    #[inline]
    fn get_deleted<'a>(
        &'a self,
        database: &Database,
    ) -> Result<Option<DeletionSequenceEnum<'a>>, CheckingError> {
        let mut deleted_ids = Vec::new();
        database
            .get_undeleted(self.subproof_id_range.clone())
            .try_for_each(|result_index| {
                let index = result_index?;
                let constraint = database.get_entry_usize(index).unwrap();
                let mut constraint_ids = constraint.get_del_by_id(index);
                deleted_ids.append(&mut constraint_ids.0);
                deleted_ids.append(&mut constraint_ids.1);
                Result::<_, CheckingError>::Ok(())
            })?;
        // Remove duplicates from deleted constraint IDs.
        deleted_ids.sort_unstable();
        deleted_ids.dedup();
        Ok(Some(DeletionSequenceEnum::Vec(deleted_ids)))
    }

    #[inline]
    fn is_subproof_friendly(&self) -> bool {
        true
    }

    #[inline]
    fn add_constraints_to_core(&self, _context: &Context) -> bool {
        self.add_to_core
    }

    #[inline]
    fn swaps_database(&self) -> bool {
        self.replacement_database.is_some()
    }

    #[inline]
    fn get_new_database(&mut self) -> (Database, PropagationEngine) {
        (
            *std::mem::take(&mut self.replacement_database).unwrap(),
            *std::mem::take(&mut self.replacement_prop_engine).unwrap(),
        )
    }

    /// The only database this rule ever swaps in is one a `def_order` /
    /// `spec` stored on the way in, so this is exactly the matching pop of
    /// the kernel shadow's stack (see `crate::kernel_bridge`). The
    /// sub-database being dropped here needs no mirroring: its slots are
    /// discarded with it.
    #[inline]
    fn handle_old_database(
        &mut self,
        context: &mut Context,
        _database: Database,
        _prop_engine: PropagationEngine,
    ) {
        crate::kernel_bridge::shadow_restore(context);
    }

    #[inline]
    fn kernel_slot_taint(&self) -> &'static str {
        // A constraint stored at `qed` by DOMINANCE, checked deletion or
        // proof-by-contradiction. Redundance no longer lands here: it sets
        // `offers_red_justification` and its slot is justified above.
        "strengthening-subproof-unmodelled"
    }
}

impl Elaboratable for EndSubproofChecker {
    fn elaborate<C: ConstraintLookup, V: VarNameLookup>(
        &self,
        elaborator: &mut Elaborator,
        database: &C,
        _var_lookup: &V,
    ) -> Result<(), ElaborationError> {
        if self.is_elaborated {
            return Ok(());
        }
        elaborator.write_subcontext_end(self.qed_subcontext, self.inner.optional_hint, database);
        Ok(())
    }
}

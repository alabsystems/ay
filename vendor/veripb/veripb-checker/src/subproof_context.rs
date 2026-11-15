/// [`Subcontext`] for a top-level subproof.
use std::{collections::BTreeMap, rc::Rc};

use colored::Colorize;
use veripb_formula::prelude::*;
use veripb_rules::{ObjectiveUpdateType, ProofgoalID};

use crate::{context::AUTOPROVING, prelude::*, rules::ScopeId};

/// The proofgoal elaboration threshold ratio controls if proofgoals that are equal to a constraint in the database are elaborated or not. The ratio we compare to is the number of proofgoals divided by the number of constraint in the formula.
///
/// # Why is this needed?
/// CakePB supports autoproving for proofgoals where the constraint is already in the database, but the initialization of the data structure required for this is slow and only pays off if there are many proof goals. Through experimentation it was determined that `0.05` is a good ratio for this.
const PROOFGOAL_ELABORATION_THRESHOLD: f64 = 0.05;

/// Marks a subproof whose rule turns every database constraint into a proof
/// obligation, and records how those obligations are restricted.
///
/// An obligation that proofgoal *generation* auto-discharged (trivial, implied
/// by the original constraint, or found in the database) is still real — the
/// proof may discharge it explicitly instead — so the goal is rebuilt on
/// demand by [`SubproofContext::pop_database_goal`]. It must be rebuilt
/// exactly as generation would have built it, including the scope it may be
/// proven in: `scope geq` introduces the *strictly improving* specification
/// premises, which are not available to the "not worsening" obligations that
/// database goals belong to.
#[derive(Debug, Clone, Copy)]
struct DatabaseObligations {
    scope_restriction: Option<ScopeId>,
}

/// Top-level subproof [`Subcontext`] storing information that is only needed inside that subproof and what should be changed after the subproof is completed.
#[derive(Debug, Default)]
pub struct SubproofContext {
    /// Constraints to be added after the subproof has been completed.
    pub to_add: Vec<Rc<DBConstraint>>,
    /// Add the constraints in the `to_add` vector to the core set.
    pub add_to_core: bool,
    /// Proofgoals from the database that should be proven in the subproof.
    database_proofgoals: BTreeMap<usize, Proofgoal>,
    /// Whether the rule that opened this subproof turns *every* database
    /// constraint into a proof obligation (the strengthening rules do:
    /// `red`, `dom`, checked `del`).
    ///
    /// [`Self::pop_database_goal`] reconstructs an obligation that proofgoal
    /// generation auto-discharged, which is legitimate only when the rule
    /// generated database obligations at all. Rules whose obligation set is
    /// fixed and internal — `pbc`, `pres_add`/`pres_rm`, `obju`, and checked
    /// deletion under strengthening-to-core — owe nothing per database
    /// constraint, and for them a `proofgoal <id>` must be rejected rather
    /// than answered with a freshly invented, self-discharging goal.
    database_obligations: Option<DatabaseObligations>,
    /// Internal proofgoals that should be proven in the subproof. Internal proofgoals are identified by an `#`.
    internal_proofgoals: Vec<Option<Proofgoal>>,
    /// Objective that should be set after the subproof is completed. This can update
    pub objective_update: Option<PBObjective>,
    /// The type of the objective update.
    pub objective_update_type: ObjectiveUpdateType,
    /// The additional premise is usually the negated constraint.
    pub additional_hint: Option<usize>,
    /// Whether [`Self::finalize`] should write the `qed` that closes this
    /// block in the elaborated proof.
    ///
    /// Normally one `SubproofContext` is one block, so `finalize` closing it is
    /// right. `dom` under an order with a non-empty `spec` is the exception:
    /// it finalizes *two* contexts — the `leq` scope and the strict `geq` one —
    /// against a single `dom` header, because both scopes owe goals. Each
    /// `finalize` wrote a `qed`, so the block was closed twice against one
    /// `inc_indent`: the second `dec_indent` underflowed. Under this fork's
    /// `overflow-checks` that aborts (a proof that verifies without `-e`
    /// crashed with it); upstream wraps to `usize::MAX` and writes a
    /// structurally corrupt proof — the `dom` closed after the first `qed` and
    /// `proofgoal #2` stranded at top level — while still reporting success.
    ///
    /// Setting this on the first of the pair makes the two contexts emit one
    /// block between them, which is what the elaborated `dom` is. It affects
    /// the elaborator only; no checking decision reads it.
    ///
    /// Spelled as *suppress* rather than *emit* so that `#[derive(Default)]`
    /// gives the safe value: `false`, meaning every block closes itself unless
    /// a caller deliberately says otherwise. An `emit_closing_qed` field would
    /// default to `false` and silently swallow every `qed` in the file.
    pub suppress_closing_qed: bool,
    /// Flag if proof by contradiction subproof.
    pub proof_by_contradiction_subproof: bool,
    /// Start constraint ID of the subproof.
    pub subproof_start_id: usize,
    /// Current scope the subproof is in.
    pub current_scope: Option<ScopeId>,
    /// Starting constraint ID for the scope.
    pub scope_start_id: usize,
    /// Witness used for this subproof.
    pub witness: Substitution,
    /// The database slots this subproof's `red` generated a proofgoal for,
    /// each paired with the substituted constraint that goal is.
    ///
    /// Computed where the goals are GENERATED, in the `red` rule, and carried
    /// here because the offer happens at the `qed` -- by which point
    /// `get_proofgoals`' output is long gone. Empty for every other rule.
    pub red_goal_slots: Vec<(usize, veripb_formula::prelude::PBConstraintEnum)>,
    /// Slot ids the database held as DERIVED when this subproof's `red` ran.
    /// Carried for the same reason as [`Self::red_goal_slots`]: the offer
    /// happens at the `qed`, after the information is gone.
    pub red_derived_slots: Vec<usize>,
    /// As [`Self::offers_red_justification`], but for DOMINANCE. Kept apart
    /// because the two are different legs of `VeriPbCore.DbOkF` with different
    /// hypotheses -- `dom` additionally needs the loaded order's transitivity
    /// to have been kernel-established -- and because the census counts them
    /// separately.
    pub offers_dom_justification: bool,
    /// The `qed` closing this subproof must offer a `red` justification
    /// (`VeriPbCore.DbOkF.red`) for the single constraint in [`Self::to_add`],
    /// instead of leaving it a named hole.
    ///
    /// ONLY redundance-based strengthening may set this. `dom`, checked
    /// deletion and proof-by-contradiction all store a witness here too and
    /// none of them is an instance of that theorem -- so the FLAG, not the
    /// presence of a witness, is what routes the offer. Getting that wrong
    /// would hand a `red` justification to a rule the kernel says nothing
    /// about, which is silent unsound accounting rather than a visible hole.
    pub offers_red_justification: bool,
    /// A nested proofgoal has established the contradiction this
    /// proof-by-contradiction subproof owes.
    ///
    /// Only [`ProofgoalContext::discharges_pbc_contradiction`] may set this,
    /// and only for a goal whose counterexample premises are entailed by the
    /// negated conclusion already in the database — see
    /// [`crate::rules::ProofgoalChecker`]. [`Self::finalize`] treats the flag
    /// as licence to skip every remaining obligation *and* the top-level RUP
    /// check, so setting it from anything weaker (for instance "some proofgoal
    /// inside a `pbc` was discharged") makes the checker refute tautologies.
    pub contradiction_proven: bool,
    /// Contradiction output hint.
    pub contradiction_output_id: usize,
}

impl SubproofContext {
    /// Constructs a new subproof context with internal proofgoals containing dummy 0th element.
    #[inline]
    pub fn new(start_id: usize) -> Self {
        SubproofContext {
            internal_proofgoals: vec![None],
            subproof_start_id: start_id,
            ..Default::default()
        }
    }

    /// Add a single constraint internal proofgoal to the subproof context.
    #[inline]
    pub fn add_single_proofgoal(
        &mut self,
        constraint: Rc<DBConstraint>,
        scope_restriction: Option<ScopeId>,
    ) {
        self.internal_proofgoals
            .push(Some(Proofgoal::mk_single_constraint(
                constraint,
                scope_restriction,
                false,
            )));
    }

    /// Add a proofgoal as an internal proofgoal.
    #[inline]
    pub fn add_internal_proofgoal(&mut self, proofgoal: Proofgoal) {
        self.internal_proofgoals.push(Some(proofgoal));
    }

    /// Add dummy internal proofgoals to increment the IDs.
    pub fn resize_internal(&mut self, new_size: usize) {
        self.internal_proofgoals.resize_with(new_size, || None);
    }

    /// Add a multi constraint internal proofgoal to the subproof context.
    #[inline]
    pub fn add_multi_proofgoal(
        &mut self,
        constraints: Vec<Rc<DBConstraint>>,
        scope_restriction: Option<ScopeId>,
    ) {
        self.internal_proofgoals
            .push(Some(Proofgoal::mk_multi_constraint(
                constraints,
                scope_restriction,
            )));
    }

    /// Declare that this subproof owes an obligation for every database
    /// constraint, restricted to `scope_restriction`.
    ///
    /// Must be called by every rule that hands database proofgoals to this
    /// context, *including* when generation happened to auto-discharge all of
    /// them and [`Self::add_database_proofgoal`] is therefore never reached:
    /// what this records is that the obligations exist, not that any survived.
    #[inline]
    pub fn declare_database_obligations(&mut self, scope_restriction: Option<ScopeId>) {
        self.database_obligations = Some(DatabaseObligations { scope_restriction });
    }

    /// Add a single constraint proofgoal from the database to the subproof context.
    ///
    /// The constraint is added in such a way that it can be easily referenced by the constraint ID of any duplicate of the constraint. However, when the proofgoal is proven, this fact should directly propagate to the other duplicates.
    #[inline]
    pub fn add_database_proofgoal(
        &mut self,
        constraint: Rc<DBConstraint>,
        add_derived_goals: bool,
        scope_restriction: Option<ScopeId>,
    ) {
        debug_assert!(
            self.database_obligations.is_some(),
            "database proofgoals added without declaring database obligations"
        );
        for &id in constraint.header.borrow().core_ids.iter() {
            self.database_proofgoals.insert(
                id,
                Proofgoal::mk_single_constraint(constraint.clone(), scope_restriction, false),
            );
        }
        if add_derived_goals {
            for &id in constraint.header.borrow().derived_ids.iter() {
                self.database_proofgoals.insert(
                    id,
                    Proofgoal::mk_single_constraint(constraint.clone(), scope_restriction, false),
                );
            }
        }
    }

    /// Get an internal proof goal.
    #[inline]
    pub fn pop_internal_goal(&mut self, index: usize) -> Result<Proofgoal, CheckingError> {
        if let Some(optional_goal) = self.internal_proofgoals.get_mut(index) {
            if let Some(goal) = optional_goal.take() {
                if let Some(scope) = self.current_scope
                    && !goal.is_in_scope(scope)
                {
                    return Err(CheckingError::ProofgoalNotInScope(
                        ProofgoalID::Internal(index),
                        scope,
                    ));
                }
                return Ok(goal);
            }
            return Err(CheckingError::InternalProofgoalAlreadyProven(index));
        }
        Err(CheckingError::InternalProofgoalNotExisting(index))
    }

    /// Get a database proofgoal.
    ///
    /// A goal that generation kept is handed over directly. A goal generation
    /// auto-discharged is rebuilt from the database constraint under this
    /// subproof's witness — but only for a subproof that owes database
    /// obligations in the first place. Without that guard the reconstruction
    /// invents an obligation out of nothing: for a `pbc` (or a checked
    /// deletion under strengthening-to-core) it hands back the database
    /// constraint itself, whose counterexample premise contradicts the very
    /// database it is proven against, so `proofgoal <any id>` is discharged by
    /// two lines and — before the fix in [`crate::rules::ProofgoalChecker`] —
    /// was taken as proof of the whole subproof's contradiction.
    #[inline]
    pub fn pop_database_goal(
        &mut self,
        index: usize,
        database: &Database,
    ) -> Result<Proofgoal, CheckingError> {
        if let Some(goal) = self.database_proofgoals.remove(&index) {
            if let Some(scope) = self.current_scope
                && !goal.is_in_scope(scope)
            {
                return Err(CheckingError::ProofgoalNotInScope(
                    ProofgoalID::Database(index as isize),
                    scope,
                ));
            }
            Ok(goal)
        } else if let Some(obligations) = self.database_obligations {
            let constraint = database.get_entry_usize(index)?;
            let substituted = Rc::new(constraint.substitute(&self.witness));
            // Same bookkeeping generation does, so the elaborator can name the
            // goal by the output ID of the constraint it came from.
            substituted.copy_ids(constraint);
            let goal =
                Proofgoal::mk_single_constraint(substituted, obligations.scope_restriction, false);
            if let Some(scope) = self.current_scope
                && !goal.is_in_scope(scope)
            {
                return Err(CheckingError::ProofgoalNotInScope(
                    ProofgoalID::Database(index as isize),
                    scope,
                ));
            }
            Ok(goal)
        } else {
            Err(CheckingError::DatabaseProofgoalNotExisting(index))
        }
    }

    /// Prints the last added internal proofgoal.
    #[inline]
    pub fn trace_internal_proofgoal_back(&self, var_names: &VarNameManager) {
        self.trace_internal_proofgoal(self.internal_proofgoals.len() - 1, var_names);
    }

    /// Prints the internal proofgoal with the given `id`.
    #[inline]
    pub fn trace_internal_proofgoal(&self, id: usize, var_names: &VarNameManager) {
        if let Some(Some(proofgoal)) = self.internal_proofgoals.get(id) {
            let id_string = String::from("#") + id.to_string().as_str();
            proofgoal.trace(id_string.as_str(), var_names)
        }
    }

    /// Print all the internal proofgoals.
    #[inline]
    pub fn trace_all_internal_proofgoals(&self, var_names: &VarNameManager) {
        for (goal_id, goal) in self.internal_proofgoals.iter().enumerate() {
            let id_string = String::from("#") + goal_id.to_string().as_str();
            if let Some(proofgoal) = goal {
                proofgoal.trace(id_string.as_str(), var_names)
            }
        }
    }

    /// Print the proofgoals from the database according to their constraint ID.
    #[inline]
    pub fn trace_database_proofgoals(&self, var_names: &VarNameManager) {
        if self.database_proofgoals.is_empty() {
            return;
        }
        println!("  ** proofgoal from formula **");
        for (goal_id, proofgoal) in self.database_proofgoals.iter() {
            println!(
                "  proofgoal {}: {}",
                goal_id.to_string().bright_green(),
                proofgoal
                    .unwrapped_conclusion()
                    .to_pretty_string(var_names)
                    .blue()
            );
        }
    }

    /// Finalizes the subproof by checking for unproven proofgoals and autoproving them if possible.
    ///
    /// This function can be used to conclude a top-level subproof (i.e., not a proofgoal subproof). It tries to autoprove the remaining proofgoals. If all proofgoals are proven, then this function updates the objective and return the constraints to be added after the subproof is successful.
    ///
    /// This function consumes the `SubproofContext`, as it is no longer required and saves reallocating memory for the output constraints that should be added.
    pub fn finalize(
        mut self,
        context: &mut Context,
        database: &mut Database,
        additional_premises: &[Rc<DBConstraint>],
    ) -> Result<Vec<Rc<DBConstraint>>, CheckingError> {
        if context.trace_enabled {
            println!("  autoproving remaining proofgoals:")
        }

        // Check if all proofgoals have been proven.
        if !self.proof_by_contradiction_subproof
            && self.internal_proofgoals.iter().all(|g| g.is_none())
            && self.database_proofgoals.is_empty()
        {
            if let Some(elaborator) = context.elaborator.as_mut() {
                if !self.suppress_closing_qed {
                    elaborator.write_qed();
                }
            }
            return self.finalize_unchecked(context);
        } else if self.contradiction_proven {
            // `DB /\ ~C |- false` was shown by a nested proofgoal, so every
            // remaining obligation holds vacuously. The flag is only ever set
            // for a goal whose premises `~C` already entails; see
            // [`Self::contradiction_proven`].
            if let Some(elaborator) = context.elaborator.as_mut() {
                if !self.suppress_closing_qed {
                    elaborator.write_qed_with_id(self.contradiction_output_id);
                }
            }
            return self.finalize_unchecked(context);
        }

        // Check if we can derive contradiction in the top-level subproof. Hence, all proofgoals can use this contradiction to show the proofgoals.
        let hint = if additional_premises.is_empty() {
            if self.use_toplevel_rup_check() || self.proof_by_contradiction_subproof {
                context.propagation_engine.collect_kernel_certificate =
                    context.config.kernel_verify;
                database.update_propagation_index(&mut context.propagation_engine)?;
                if context
                    .propagation_engine
                    .reverse_unit_propagation_check(
                        &context.var_names,
                        &[],
                        None,
                        context.only_core,
                        context.elaborator.is_some(),
                        self.proof_by_contradiction_subproof && context.config.trace_failed,
                    )?
                    .is_conflict()
                {
                    crate::kernel_bridge::consume_rup_conflict(context, database, None)?;
                    if context.trace_enabled {
                        println!(
                            "  * database with subproof constraints is propagating to conflict"
                        );
                    }
                    context.rup_streak += 1;
                    if let Some(elaborator) = context.elaborator.as_mut() {
                        elaborator.write_rup_contradiction_subproof_tail(
                            false,
                            &context.propagation_engine.rup_hints,
                        );
                    }
                    return self.finalize_unchecked(context);
                }
            }
            if let Some(premise) = self.additional_hint {
                Some(database.get_entry_usize(premise)?.clone())
            } else {
                None
            }
        } else {
            if self.use_toplevel_rup_check() || self.proof_by_contradiction_subproof {
                context.propagation_engine.collect_kernel_certificate =
                    context.config.kernel_verify;
                database.update_propagation_index(&mut context.propagation_engine)?;
                if context
                    .propagation_engine
                    .reverse_unit_propagation_check(
                        &context.var_names,
                        additional_premises,
                        None,
                        context.only_core,
                        context.elaborator.is_some(),
                        self.proof_by_contradiction_subproof && context.config.trace_failed,
                    )?
                    .is_conflict()
                {
                    crate::kernel_bridge::consume_rup_conflict(context, database, None)?;
                    if context.trace_enabled {
                        println!("  * database with subproof premises is propagating to conflict");
                    }
                    context.rup_streak += 1;
                    if let Some(elaborator) = context.elaborator.as_mut() {
                        elaborator.write_rup_contradiction_subproof_tail(
                            false,
                            &context.propagation_engine.rup_hints,
                        );
                    }
                    return self.finalize_unchecked(context);
                }
            }

            // Add additional premises to the propagation engine for the autoproving.
            for constraint in additional_premises {
                context.propagation_engine.attach(AUTOPROVING, constraint)?;
            }
            context.propagation_engine.enable_front(AUTOPROVING);

            // Take the first constraint as hint, as this is the negated constraint for redundance- and dominance-based strengthening.
            Some(additional_premises[0].clone())
        };

        if self.proof_by_contradiction_subproof {
            return Err(CheckingError::ProofByContradictionNotRUP);
        }

        // Check remaining internal proofgoals.
        for (id, proofgoal) in self.internal_proofgoals.iter_mut().enumerate() {
            if let Some(proofgoal) = proofgoal {
                let technique = proofgoal
                    .autoprove(context, database, &hint, ProofgoalID::Internal(id), true)
                    .inspect_err(|_| {
                        if !additional_premises.is_empty() {
                            context.propagation_engine.disable(AUTOPROVING);
                            context.propagation_engine.clear_set(AUTOPROVING);
                        }
                    })?;
                if context.trace_enabled {
                    proofgoal.trace_autoproven(
                        ("#".to_string() + id.to_string().as_str()).purple(),
                        technique,
                    );
                }
            }
        }

        let elaborate_database_proofgoals = (self.database_proofgoals.len() as f64
            / database.len() as f64)
            <= PROOFGOAL_ELABORATION_THRESHOLD;
        // Check remaining database proofgoals.
        while let Some((id, mut proofgoal)) = self.database_proofgoals.pop_first() {
            let technique = proofgoal
                .autoprove(
                    context,
                    database,
                    &hint,
                    ProofgoalID::Database(id as isize),
                    elaborate_database_proofgoals,
                )
                .inspect_err(|_| {
                    if !additional_premises.is_empty() {
                        context.propagation_engine.disable(AUTOPROVING);
                        context.propagation_engine.clear_set(AUTOPROVING);
                    }
                })?;
            if context.trace_enabled {
                proofgoal.trace_autoproven(id.to_string().bright_green(), technique);
            }
        }

        if let Some(elaborator) = context.elaborator.as_mut() {
            if !self.suppress_closing_qed {
                elaborator.write_qed();
            }
        }

        if !additional_premises.is_empty() {
            context.propagation_engine.disable(AUTOPROVING);
            context.propagation_engine.clear_set(AUTOPROVING);
        }

        self.finalize_unchecked(context)
    }

    /// Finalize the subproof without checking for unproven proofgoals.
    ///
    /// This function updates the objective and return the constraints to be added after the subproof is successful.
    #[inline]
    pub fn finalize_unchecked(
        self,
        context: &mut Context,
    ) -> Result<Vec<Rc<DBConstraint>>, CheckingError> {
        // Change the objective if it should be updated.
        if let Some(objective_update) = self.objective_update {
            context.update_objective(objective_update, self.objective_update_type);
        }

        // Add the derived constraints.
        Ok(self.to_add)
    }

    /// The maximum ID for an internal proofgoal.
    #[inline]
    pub fn internal_proofgoal_len(&self) -> usize {
        self.internal_proofgoals.len()
    }

    /// The number of database proofgoals.
    #[inline]
    pub fn database_proofgoals_len(&self) -> usize {
        self.database_proofgoals.len()
    }

    /// Heuristic to check if we should use the top-level RUP check to detect if all proofgoals follow by one RUP check without using the proofgoals at all.
    /// Usually this is the case for redundance-based strengthening steps that could be RUP steps.
    /// Such steps occur in proofs produced by SAT solvers directly translated from the RAT rule.
    ///
    /// Such RAT steps always have a witness of length 1, so we require that the witness has length at most 1.
    /// In addition, we require that there is at least one internal proofgoal (which are offset by one) and at least three database proofgoals.
    #[inline]
    fn use_toplevel_rup_check(&self) -> bool {
        self.internal_proofgoal_len() >= 2
            && self.database_proofgoals.len() >= 3
            && self.witness.len() <= 1
    }
}

use std::{num::Saturating, rc::Rc};

use veripb_formula::prelude::*;
use veripb_rules::RedundanceBasedStrengtheningRule;

use crate::{context::REQUIRED_RUP_STREAK, prelude::*};

use super::ScopeId;

impl Checkable for RedundanceBasedStrengtheningRule {
    fn compute(
        &mut self,
        context: &mut Context,
        database: &mut Database,
    ) -> Result<Vec<Rc<DBConstraint>>, CheckingError> {
        context.check_witness(&self.witness)?;

        let subcontexts = context.subcontexts.as_slice().last_chunk::<2usize>();
        if let Some(
            [
                Subcontext::Order(order_context),
                Subcontext::Specification(_),
            ],
        ) = subcontexts
        {
            let contains_variable_out_of_order = match &self.constraint.constraint {
                PBConstraintEnum::Clause(clause) => clause.get_lits().any(|lit| {
                    !order_context
                        .constructed_order
                        .is_order_variable(lit.get_var())
                }),
                PBConstraintEnum::Cardinality(cardinality) => cardinality.get_lits().any(|lit| {
                    !order_context
                        .constructed_order
                        .is_order_variable(lit.get_var())
                }),
                PBConstraintEnum::GeneralPBI64(constraint) => constraint.get_lits().any(|lit| {
                    !order_context
                        .constructed_order
                        .is_order_variable(lit.get_var())
                }),
                PBConstraintEnum::GeneralPBI128(constraint) => constraint.get_lits().any(|lit| {
                    !order_context
                        .constructed_order
                        .is_order_variable(lit.get_var())
                }),
                PBConstraintEnum::GeneralPBBigInt(constraint) => constraint.get_lits().any(|lit| {
                    !order_context
                        .constructed_order
                        .is_order_variable(lit.get_var())
                }),
            };
            if contains_variable_out_of_order {
                Err(CheckingError::UndeclaredVariablesInOrder)?
            } else if self
                .witness
                .syntactic_support()
                .any(|var| !order_context.constructed_order.is_auxiliary_variable(*var))
            {
                Err(CheckingError::SpecWitnessMapsNonAuxVariable)?
            }
        }

        // Maybe the strengthening statements in the proof are actually just RUP constraints. We only do this check if we had enough success autoproving the subproof at top-level without using the witness.
        if !self.has_subproof
            && (self.witness.is_empty() || context.rup_streak >= REQUIRED_RUP_STREAK)
        {
            // Check if constraint is RUP.
            context.propagation_engine.collect_kernel_certificate = context.config.kernel_verify;
            database.update_propagation_index(&mut context.propagation_engine)?;
            if context
                .propagation_engine
                .reverse_unit_propagation_check(
                    &context.var_names,
                    &[],
                    Some(&self.constraint),
                    context.only_core,
                    context.elaborator.is_some(),
                    false,
                )?
                .is_conflict()
            {
                // The `red` constraint is stored here, so this acceptance
                // also feeds the shadow database: a RUP-shortcut `red` is an
                // ordinary entailed derivation, not a witness meta-step.
                crate::kernel_bridge::consume_rup_derivation(
                    context,
                    database,
                    &self.constraint.constraint,
                )?;
                if context.trace_enabled {
                    println!("* constraint is RUP *")
                }
                if let Some(elaborator) = context.elaborator.as_mut() {
                    elaborator.write_rup_step(
                        &self.constraint.constraint,
                        &context.propagation_engine.rup_hints,
                        &context.var_names,
                    );
                }
                return Ok(vec![self.constraint.clone()]);
            }
            // Check if constraint is in DB.
            database.update_unique_index(&mut context.propagation_engine)?;
            if let Some(constraint) = database.lookup(&self.constraint)
                && (!context.only_core || constraint.is_core_constraint())
            {
                // As above: a `red` that is discharged by "this constraint is
                // already in the database" stores a copy of an entailed
                // constraint, so its slot is the found id's slot.
                let constraint = constraint.clone();
                crate::kernel_bridge::consume_db_lookup_derivation(
                    context,
                    database,
                    &self.constraint.constraint,
                    &constraint,
                )?;
                if context.trace_enabled {
                    println!("* constraint is in DB already")
                }
                if let Some(elaborator) = context.elaborator.as_mut() {
                    elaborator.write_pol_single_id(
                        constraint.get_out_id(constraint.get_some_id()).unwrap(),
                    );
                }

                return Ok(vec![self.constraint.clone()]);
            }
            context.rup_streak = Saturating(0);
        }

        // From here on the acceptance rests on the redundance meta-step —
        // witness substitution, proofgoal generation, and "discharging these
        // substituted goals licenses adding the constraint" — which the
        // proved kernel does not model (the development design notes section 5, item
        // 5). The individual goal discharges below are kernel-checked; the
        // license itself is counted here so the summary never claims full
        // coverage for a witnessed `red` (or v2 proof-by-contradiction)
        // acceptance.
        // Past both shortcuts, so the constraint about to be stored is
        // witnessed: satisfiability-preserving, NOT input-entailed. `output
        // DERIVABLE` must refuse after this.
        context.witnessed_strengthening_used = true;

        // The acceptance rests on the redundance meta-step. The kernel DOES
        // now model it (`VeriPbCore.dbOkR_red_of_goals`), but the
        // justification cannot be offered HERE: the offer queue is consumed in
        // the order constraints are stored, and the subproof branch below
        // stores the NEGATED constraint first. Offering early made the
        // shadow read this rule's justification into the negation's slot --
        // measured as `shadow-slot-mismatch x378` on one corpus instance. The
        // offer is made where the constraint is actually added, after the
        // goals have been discharged.

        let mut subproof_context = SubproofContext::new(database.len());
        // Only the explicit-subproof branch consumes this: it is handed to
        // `EndSubproofChecker`, which stores the constraints the `qed` adds.
        // The constraint *this* rule returns is placed by
        // `Checkable::add_constraints_to_core` below, which covers the
        // subproof-less branch and both shortcut returns above. Do not fold
        // the two back together: dropping the trait override is exactly the
        // defect that let a bare `red` land in the derived set under
        // strengthening-to-core.
        let mut add_to_core = false;
        // We need to elaborate the red rule line here, as autoproving might generate extra lines. In version 2, redundance-based strengthening with an empty witness is treated as proof by contradiction.
        if context.major_version <= Some(2) && self.witness.is_empty() {
            subproof_context.proof_by_contradiction_subproof = true;
            if let Some(elaborator) = context.elaborator.as_mut() {
                elaborator.write_pbc_header(&self.constraint, &context.var_names);
            }
        } else {
            add_to_core = context.is_strengthening_to_core;
            if let Some(elaborator) = context.elaborator.as_mut() {
                elaborator.write_red_header(&self.constraint, &self.witness, &context.var_names);
            }
        }

        // Generate the proofgoals, starting with the constraint to be introduced.
        subproof_context.add_single_proofgoal(
            Rc::new(self.constraint.substitute(&self.witness)),
            Some(ScopeId::LessEqual),
        );
        if context.trace_enabled {
            println!("  ** proofgoal from satisfying added constraint **");
            subproof_context.trace_internal_proofgoal_back(&context.var_names);
        }

        // Proofgoals from order.
        if let Some(active_order) = &mut context.active_order {
            for proofgoal in active_order.get_proofgoals(&self.witness) {
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
                objective.get_proofgoal(&self.witness),
                Some(ScopeId::LessEqual),
            );
            if context.trace_enabled {
                println!("  ** proofgoal from objective **");
                subproof_context.trace_internal_proofgoal_back(&context.var_names);
            }
        }

        // Get database proofgoals.
        subproof_context.declare_database_obligations(Some(ScopeId::LessEqual));
        database.update_unique_index(&mut context.propagation_engine)?;
        let (goals, autodischarged) = database.get_proofgoals(
            &self.witness,
            !context.is_strengthening_to_core,
            context.elaborator.is_some(),
            context.only_core,
            context.config.kernel_verify,
        );
        // The SLOT each goal is about, paired with the substituted constraint
        // that goal is. `copy_ids` carries the source constraint's live ids
        // onto its substituted image, and a live id IS a shadow slot index --
        // so this recovers, without trusting the occurrences index, exactly
        // which slots received an obligation.
        //
        // ALL THREE auto-discharge forms carry their source, so every one
        // pairs. `Trivial` and `DbLookup` did not until the enum was widened
        // to hold it: their payload is the substituted constraint, which has a
        // fresh header and no ids, so a slot discharged that way was invisible
        // here and the whole step was refused.
        let add_derived = !context.is_strengthening_to_core;
        let derived_slots = crate::kernel_bridge::derived_slot_ids(database, add_derived);
        let mut goal_slots: Vec<(usize, veripb_formula::prelude::PBConstraintEnum)> = Vec::new();
        let note =
            |source: &Rc<DBConstraint>,
             image: &Rc<DBConstraint>,
             out: &mut Vec<(usize, veripb_formula::prelude::PBConstraintEnum)>| {
                let header = source.header.borrow();
                for &id in header.core_ids.iter() {
                    out.push((id, image.constraint.clone()));
                }
                if add_derived {
                    for &id in header.derived_ids.iter() {
                        out.push((id, image.constraint.clone()));
                    }
                }
            };
        // Obligations proofgoal generation discharged by itself are re-judged
        // through the same entry points their explicit counterparts use.
        for discharged in &autodischarged {
            use crate::database::AutoDischarge;
            match discharged {
                AutoDischarge::Trivial(source, image)
                | AutoDischarge::Implied(source, image)
                | AutoDischarge::DbLookup(source, image, _) => note(source, image, &mut goal_slots),
            }
            crate::kernel_bridge::consume_autodischarge(context, discharged)?;
        }
        for constraint in goals {
            note(&constraint, &constraint, &mut goal_slots);
            subproof_context.add_database_proofgoal(
                constraint,
                add_derived,
                Some(ScopeId::LessEqual),
            );
        }
        if context.trace_enabled {
            subproof_context.trace_database_proofgoals(&context.var_names);
        }

        let negated = Rc::new(self.constraint.negate());

        if self.has_subproof {
            subproof_context.additional_hint = Some(database.len());
            subproof_context.to_add.push(self.constraint.clone());
            context.inside_strengthening_subproof = true;
            // This branch stores the NEGATION here and its own constraint at
            // the `qed`, so the offer is made THERE -- against the database
            // the theorem is instantiated at. Offering here would be consumed
            // by `negated` below, which is exactly the `shadow-slot-mismatch`
            // defect measured earlier on this rule. The negation keeps its own
            // hole from `kernel_slot_taint`, which is correct: it IS an
            // assumption, discharged by the subproof rather than justified.
            subproof_context.offers_red_justification = true;
            subproof_context.red_goal_slots = std::mem::take(&mut goal_slots);
            subproof_context.red_derived_slots = derived_slots.clone();
            subproof_context.witness = std::mem::take(&mut self.witness);
            subproof_context.add_to_core = add_to_core;
            context
                .subcontexts
                .push(Subcontext::Subproof(subproof_context));
            Ok(vec![negated])
        } else {
            if let Some(elaborator) = context.elaborator.as_mut() {
                negated.set_out_id(0, elaborator.inc_id());
            }

            // Snapshot across the discharges: an unchanged skip census is what
            // says every goal was KERNEL-justified, not merely accepted.
            let skips_before = context.kernel_stats.total_skips();
            subproof_context.finalize(context, database, &[negated])?;
            let discharged_cleanly = context.kernel_stats.total_skips() == skips_before;
            // Every proofgoal has now been discharged, and each reached the
            // bridge through the same path its explicit counterpart uses --
            // so anything the kernel could not justify has already been
            // counted as a skip. What remains for
            // `VeriPbCore.dbOkR_red_of_goals` is the `substDB w DB = DB`
            // premise, which `offer_red` establishes by COMPUTING the
            // substitution for every stored slot rather than inferring it
            // from the absence of a proofgoal.
            if context.config.kernel_verify {
                crate::kernel_bridge::offer_red(
                    context,
                    &self.witness,
                    &self.constraint.constraint,
                    &goal_slots,
                    discharged_cleanly,
                    &derived_slots,
                );
            }
            Ok(vec![self.constraint.clone()])
        }
    }

    #[inline]
    fn kernel_slot_taint(&self) -> &'static str {
        // The NEGATED constraint this rule stores when it opens a subproof.
        // It is an ASSUMPTION the subproof discharges, not something the
        // kernel failed to justify -- the rule's own constraint is offered and
        // justified separately. Named for what it is: a census that calls a
        // premise `-unmodelled` reads as a gap and overstates the real one.
        "red-negation-premise"
    }

    #[inline]
    fn is_subproof_friendly(&self) -> bool {
        self.witness.is_empty()
    }

    /// Strengthening-to-core promises that *every* constraint a strengthening
    /// rule introduces goes into the core set, and `compute` above relies on
    /// that promise when it passes `add_derived_goals = false` to
    /// [`Database::get_proofgoals`]: derived constraints are then dropped from
    /// the proof obligations of every later `red`/`dom`/`delc`, which is only
    /// sound while the derived set holds nothing but constraints entailed by
    /// the core set. Without this override a `red` written without an explicit
    /// subproof stored its (merely satisfiability-preserving) constraint into
    /// the derived set, so the next `red` never had to preserve it and two
    /// contradictory witnesses refuted a satisfiable formula.
    ///
    /// Unconditional on purpose. On the explicit-subproof branch the value
    /// only routes the negated hypothesis into core for the subproof's
    /// lifetime, which is harmless — no core-restricted check is reachable
    /// there — and on the two shortcut returns (`red` discharged as RUP or by
    /// a database lookup) the stored constraint is entailed, so placing it in
    /// core is conservative. [`DominanceBasedStrengtheningRule`] has had the
    /// identical override all along.
    #[inline]
    fn add_constraints_to_core(&self, context: &Context) -> bool {
        context.is_strengthening_to_core
    }
}

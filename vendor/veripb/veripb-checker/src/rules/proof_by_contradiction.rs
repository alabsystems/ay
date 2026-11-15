use std::rc::Rc;

use veripb_formula::prelude::*;
use veripb_rules::ProofByContradiction;

use crate::prelude::*;

impl Checkable for ProofByContradiction {
    fn compute(
        &mut self,
        context: &mut Context,
        database: &mut Database,
    ) -> Result<Vec<Rc<DBConstraint>>, CheckingError> {
        // Maybe we can quickly autoprove that the constraint is implied.
        if !self.has_subproof {
            // Check if constraint is in DB.
            database.update_unique_index(&mut context.propagation_engine)?;
            if let Some(constraint) = database.lookup(&self.constraint)
                && (!context.only_core || constraint.is_core_constraint())
            {
                crate::kernel_bridge::consume_db_lookup(
                    context,
                    &self.constraint.constraint,
                    &constraint.constraint,
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
        }

        // Proof by contradiction IS `red` with an EMPTY witness, and the
        // kernel models it as such. With `w` empty, `substC w D` is `D` for
        // every slot, so `dbOkR_red_of_goals`' premise reduces to
        // "`HoldsAllO b DB` and `not Holds b c` imply `Holds b c`" -- which can
        // hold only vacuously, i.e. only when no model of the database
        // falsifies `c`. That is exactly what the subproof's contradiction
        // establishes, and it is why this rule needs no witness reasoning of
        // its own: the licence is the same theorem `red` uses.

        // We need to elaborate the red rule line here, as autoproving might generate extra lines.
        if let Some(elaborator) = context.elaborator.as_mut() {
            elaborator.write_pbc_header(&self.constraint, &context.var_names);
        }

        if context.trace_enabled {
            println!("  ** contradiction has to be shown in subproof **");
        }

        let negated = Rc::new(self.constraint.negate());
        let mut subproof_context = SubproofContext::new(database.len());
        subproof_context.proof_by_contradiction_subproof = true;

        // `pbc` generates no database proofgoals at all, so nothing is
        // paired and derived slots are dropped on the same licence.
        let derived_slots = crate::kernel_bridge::derived_slot_ids(database, false);
        if self.has_subproof {
            subproof_context.additional_hint = Some(database.len());
            subproof_context.to_add.push(self.constraint.clone());
            // Offered at the `qed`, where the contradiction is discharged --
            // this branch stores the NEGATION here, and an offer made now
            // would be consumed by it. `subproof_context.witness` is left at
            // its default, which IS the empty witness this rule needs.
            subproof_context.offers_red_justification = true;
            subproof_context.red_derived_slots = derived_slots;

            context
                .subcontexts
                .push(Subcontext::Subproof(subproof_context));
            Ok(vec![negated])
        } else {
            if let Some(elaborator) = context.elaborator.as_mut() {
                negated.set_out_id(0, elaborator.inc_id());
            }

            let skips_before = context.kernel_stats.total_skips();
            subproof_context.finalize(context, database, &[negated])?;
            if context.config.kernel_verify {
                let discharged_cleanly = context.kernel_stats.total_skips() == skips_before;
                crate::kernel_bridge::offer_red(
                    context,
                    &Substitution::default(),
                    &self.constraint.constraint,
                    &[],
                    discharged_cleanly,
                    &derived_slots,
                );
            }
            Ok(vec![self.constraint.clone()])
        }
    }

    #[inline]
    fn kernel_slot_taint(&self) -> &'static str {
        // As in `red`: the NEGATED constraint, an assumption this rule's own
        // subproof discharges. The constraint it adds is offered separately.
        "pbc-negation-premise"
    }

    #[inline]
    fn is_subproof_friendly(&self) -> bool {
        true
    }
}

use std::rc::Rc;

use veripb_formula::prelude::*;
use veripb_rules::{
    ProofgoalID, ProofgoalRule,
    elaboration::{ConstraintLookup, Elaboratable, ElaborationError, Elaborator},
};

use crate::{prelude::*, proofgoal_context::ProofgoalContext};

/// Decide whether discharging a proofgoal with these counterexample premises
/// also discharges the enclosing proof-by-contradiction subproof.
///
/// A proof-by-contradiction subproof owes `DB /\ ~C |- false`, where `~C` is
/// the negated conclusion the rule pushed into the database and recorded as
/// `additional_hint`. A proofgoal subproof establishes
/// `DB /\ ~C /\ premises |- false`. The two coincide exactly when `premises`
/// add nothing to `DB /\ ~C`; the cheap and sufficient witness for that is
/// that `~C` itself syntactically implies every premise, which is precisely
/// the situation the flag was introduced for — a version 2.0 `red` with an
/// empty witness, whose goal `#1` is `C` and whose counterexample premise is
/// therefore `~C` again.
///
/// Getting this wrong is a wrong-verdict defect, not a missed optimisation:
/// the caller in `end subproof` stores the answer, and
/// [`SubproofContext::finalize`](crate::SubproofContext::finalize) treats a
/// proven contradiction as licence to skip *every* remaining obligation and
/// the top-level RUP check. Setting it for an arbitrary discharged goal — as
/// this code did before, for any goal at all inside a `pbc` — refutes a
/// tautology in three lines.
/// Answering "no" is always safe — the subproof then has to close the ordinary
/// way — so a missing or already-deleted negated conclusion is reported as "no"
/// rather than raised as an error.
fn discharges_pbc_contradiction(
    subproof_context: &SubproofContext,
    database: &Database,
    premises: &[Rc<DBConstraint>],
) -> bool {
    if !subproof_context.proof_by_contradiction_subproof {
        return false;
    }
    let Some(negated_conclusion) = subproof_context
        .additional_hint
        .and_then(|hint| database.get_entry_usize(hint).ok())
    else {
        return false;
    };
    premises
        .iter()
        .all(|premise| negated_conclusion.implies(premise))
}

#[derive(Debug)]
pub struct ProofgoalChecker {
    inner: ProofgoalRule,
    pbc_out_id_from_hint: Option<(usize, usize)>,
}
impl ProofgoalChecker {
    fn new(inner: ProofgoalRule) -> Self {
        Self {
            inner,
            pbc_out_id_from_hint: None,
        }
    }
}

impl Checkable for ProofgoalChecker {
    #[inline]
    fn kernel_slot_taint(&self) -> &'static str {
        // A proofgoal introduces its premises as assumptions for the goal's
        // subproof; the meta-step that discharges them (redundance,
        // dominance, objective update) is what the kernel does not model.
        "proofgoal-premise"
    }

    fn compute(
        &mut self,
        context: &mut Context,
        database: &mut Database,
    ) -> Result<Vec<Rc<DBConstraint>>, CheckingError> {
        if let Some(Subcontext::Subproof(subproof_context)) = context.subcontexts.last_mut() {
            let proofgoal = match &mut self.inner.proofgoal_id {
                ProofgoalID::Internal(index) => subproof_context.pop_internal_goal(*index)?,
                ProofgoalID::Database(index) => {
                    *index = database.normalize_id(*index);
                    subproof_context.pop_database_goal(*index as usize, database)?
                }
            };
            let constraints = proofgoal.into_counterexample();
            let mut proofgoal_context = ProofgoalContext::new(database.len());
            proofgoal_context.discharges_pbc_contradiction =
                discharges_pbc_contradiction(subproof_context, database, &constraints);
            context
                .subcontexts
                .push(Subcontext::Proofgoal(proofgoal_context));

            if context.elaborator.is_none() {
                return Ok(constraints);
            }

            let Some(Subcontext::Subproof(subproof_context)) =
                context.subcontexts.get(context.subcontexts.len() - 2)
            else {
                return Ok(constraints);
            };

            if !subproof_context.proof_by_contradiction_subproof {
                return Ok(constraints);
            }

            let hint = subproof_context.additional_hint.unwrap();
            let counterexample_id = database.len() + constraints.len() - 1;
            self.pbc_out_id_from_hint = Some((counterexample_id, hint));

            Ok(constraints)
        } else {
            Err(CheckingError::ProofgoalOutsideSubproof)
        }
    }

    #[inline]
    fn is_subproof_friendly(&self) -> bool {
        true
    }
}

impl From<ProofgoalRule> for ProofgoalChecker {
    fn from(inner: ProofgoalRule) -> Self {
        Self::new(inner)
    }
}

impl Elaboratable for ProofgoalChecker {
    fn elaborate<C: ConstraintLookup, V: VarNameLookup>(
        &self,
        elaborator: &mut Elaborator,
        database: &C,
        _var_lookup: &V,
    ) -> Result<(), ElaborationError> {
        let Some((counterexample_id, hint)) = self.pbc_out_id_from_hint else {
            elaborator.write_proofgoal(&self.inner.proofgoal_id, Some(database));
            return Ok(());
        };

        elaborator.dec_id();
        let hint_out_id = database
            .get_entry_usize(hint)
            .expect("Proof by contradiction should have additional hint")
            .get_out_id(hint)
            .expect("Constraint should have output ID.");
        database
            .get_entry_usize(counterexample_id)
            .expect("Counterexample constraint should be in the database")
            .set_out_id(counterexample_id, hint_out_id);
        Ok(())
    }
}

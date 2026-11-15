use std::rc::Rc;

use malachite_bigint::BigInt;
use veripb_formula::pb_constraint::constraint_from_terms;
use veripb_formula::prelude::*;
use veripb_rules::AssertionRule;

use crate::prelude::*;

impl Checkable for AssertionRule {
    #[inline]
    fn compute(
        &mut self,
        context: &mut Context,
        _database: &mut Database,
    ) -> Result<Vec<Rc<DBConstraint>>, CheckingError> {
        context.assertion_used = true;
        // An assertion is an axiom-by-fiat: the constraint enters the database
        // with no proof obligation at all, so in general there is nothing the
        // kernel could re-derive, and the summary must count it -- otherwise a
        // run whose database contains unproved constraints would still claim
        // nothing lay outside the proved fragment. `assertion_used` qualifies
        // the verdict (`s UNDER ASSERTIONS ...`) either way, and this does not
        // touch that.
        //
        // ONE shape is not an assumption, though. `VeriPbCore.improveC` says
        // "objective strictly below `v`", and `DbOkB.improve` admits it on
        // `Int.le v bound` alone -- it does NOT require that a solution
        // achieving `v` was exhibited, because refuting `F` together with
        // `obj < v` proves `obj >= v` over `F` regardless. An `a` storing
        // exactly that constraint is therefore a sound bounds step with a
        // kernel theorem behind it, and recognising it is not a special case
        // for these instances: it is the general fact that this particular
        // assertion asserts nothing.
        //
        // The candidate handed over is `improveC` at `v = 0`, built with the
        // SAME constructors an improving `sol` uses; the bridge reads the real
        // `v` off the degree difference and refuses anything whose terms do
        // not match.
        if context.config.kernel_verify {
            match improving_candidate_at_zero(context) {
                Some(cand0) => crate::kernel_bridge::offer_assertion_bound(
                    context,
                    &self.constraint.constraint,
                    &cand0,
                ),
                None => context.kernel_stats.skip("assertion-unverified"),
            }
        }
        Ok(vec![self.constraint.clone()])
    }

    #[inline]
    fn kernel_slot_taint(&self) -> &'static str {
        // Nothing entails an axiom-by-fiat, so its shadow slot is a hole.
        "assertion-unverified"
    }

    fn is_subproof_friendly(&self) -> bool {
        true
    }
}

/// `VeriPbCore.improveC` for the run's objective at `v = 0`: the negated
/// objective at degree `1 + constant`.
///
/// Built with the same constructors `SolutionRuleOutput::Improving` uses, so
/// the two are directly comparable. `None` when the run has no objective, in
/// which case no assertion can be an objective bound.
fn improving_candidate_at_zero(context: &Context) -> Option<PBConstraintEnum> {
    let objective = context.objective.as_ref()?;
    let mut negated_terms: Vec<_> = objective.terms.values().cloned().collect();
    for term in negated_terms.iter_mut() {
        term.coeff = -term.coeff.clone();
    }
    Some(
        constraint_from_terms(negated_terms, BigInt::from(1) + &objective.constant)
            .into_smallest_type(),
    )
}

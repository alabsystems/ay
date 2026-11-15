// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! [`SemanticChargeClass::QuantifierProgressMetered`] and
//! [`SemanticChargeClass::EquivPosIdentityShape`] — the precharges of the
//! steps an authored quantifier EXPANSION chain is made of.
//!
//! A refutation of a deeply alternating quantified problem walks every
//! authored quantifier from the outside in: `forall_inst` instantiates a
//! universal, `sko_forall`/`sko_ex` (`AletheRule::Skolem`) Skolemizes an
//! existential and `equiv_pos1`/`equiv_pos2` turns that equality into the
//! clause resolution uses. Each of those steps carries the WHOLE remaining
//! quantified body as its payload, so under the `General` model each one
//! precharged `payload.work * payload.unfolded_work`.
//!
//! MEASURED (`ay --z3-mode -T:20 --probe-strict-check`, QSAT route's
//! expansion replay on `2010-Monniaux-QE/mjollnir2/formula_199`, a correct
//! `unsat`): one `forall_inst` precharged 15_897_820 from
//! `payload(work=10_126, unfolded_work=1_570)`, one `Skolem` 15_762_453, one
//! `equiv_pos2` 31_608_837; twelve alternations later the walk refused with
//! `budget: work 333978893+31803193 of 350000000`, after 41 steps whose real
//! validation is a few thousand metered node visits each. The verdict stayed
//! `unknown` for a proof the checker accepts.
//!
//! * `forall_inst` and `Skolem`: their validators
//!   (`checker::quantifier::validate_forall_inst_with_progress`,
//!   `validate_sko_forall_with_progress`) debit EVERY primitive they perform —
//!   each term read, name and sort comparison, table probe, stack push and
//!   blocked-set clone — through the strict walk's own progress callback
//!   (`QuantifierMeter::charge`), and stop at `SKOLEM_TERM_WORK_LIMIT` node
//!   visits. The `General` product was a second, estimated bill for work the
//!   envelope is already debited for as it happens — the same double charge
//!   `TrustKindProgressMetered` retired for `Generic` lemmas. What remains
//!   unmetered is linear (the clause scan and the derived-clause clone), and
//!   one copy of `work + unfolded_work` covers it.
//! * `equiv_pos1`/`equiv_pos2` in the EMITTED identity shape
//!   ([`crate::checker::boolean_equiv_pos_shape::equiv_pos_is_emitted_identity_shape`]):
//!   the validator is a fixed program of about thirty reads (the derivation
//!   is on that predicate). Any other shape keeps `General`, because the rule
//!   in general reaches the unmemoized De Morgan recursion of
//!   `matches_negation_of_term`.
//!
//! Both charges are capped by [`replaced_general_product`], so each is a
//! TIGHTENING at every payload: no proof that fits a caller's envelope today
//! can stop fitting it. Byte limbs are unchanged.

use super::semantic_charge::replaced_general_product;
use super::*;

/// Work factor of [`SemanticChargeClass::EquivPosIdentityShape`], applied to
/// the step's DAG payload `work`. The validator's fixed program is about thirty
/// primitives (see the shape predicate); `payload.work >= 3` on every
/// admitted step (the payload walk debits one unit per clause literal), so
/// `32 * work + 32 >= 128` dominates it with room to spare, and the charge
/// still grows with the step's real payload.
pub(super) const EQUIV_POS_IDENTITY_WORK_FACTOR: usize = 32;

/// The `Skolem` reservation the `General` model kept on top of its product
/// (`private_validator_charge`); kept here so this class never charges less
/// than that floor.
const SKOLEM_PRIVATE_CHARGE: (usize, usize) = (100_000, 8 * 1024 * 1024);

/// The class of a quantifier-expansion step, or `None` for every other step.
pub(super) fn quantifier_expansion_class(
    step: &ProofStep,
    terms: &TermStore,
) -> Option<SemanticChargeClass> {
    let ProofStep::Step { rule, clause, .. } = step else {
        return None;
    };
    match rule {
        AletheRule::ForallInst | AletheRule::Skolem => {
            Some(SemanticChargeClass::QuantifierProgressMetered)
        }
        AletheRule::EquivPos1 | AletheRule::EquivPos2 => {
            let positive = matches!(rule, AletheRule::EquivPos2);
            crate::checker::boolean_equiv_pos_shape::equiv_pos_is_emitted_identity_shape(
                terms, clause, positive,
            )
            .then_some(SemanticChargeClass::EquivPosIdentityShape)
        }
        _ => None,
    }
}

/// Charge of [`SemanticChargeClass::QuantifierProgressMetered`]: the linear
/// unmetered remainder, capped by the `General` product it replaces, never
/// below the `Skolem` reservation the old model kept.
pub(super) fn quantifier_progress_charge(
    step: &ProofStep,
    payload: PayloadStats,
) -> Result<(usize, usize), ProofCheckError> {
    let structural = checked_add_usize(payload.work, payload.unfolded_work)?;
    let work = structural.min(replaced_general_product(payload, 1));
    let floor = match step {
        ProofStep::Step {
            rule: AletheRule::Skolem,
            ..
        } => SKOLEM_PRIVATE_CHARGE,
        _ => (0, 0),
    };
    Ok((work.max(floor.0), payload.bytes.max(floor.1)))
}

/// Charge of [`SemanticChargeClass::EquivPosIdentityShape`].
pub(super) fn equiv_pos_identity_charge(
    payload: PayloadStats,
) -> Result<(usize, usize), ProofCheckError> {
    let modelled = checked_mul_usize(payload.work, EQUIV_POS_IDENTITY_WORK_FACTOR)?;
    let modelled = checked_add_usize(modelled, EQUIV_POS_IDENTITY_WORK_FACTOR)?;
    Ok((
        modelled.min(replaced_general_product(payload, 1)),
        payload.bytes,
    ))
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact and fail-closed precharges for strict semantic validators.

use super::*;

/// Resolution has its own exact set-work meter; array schemas are quadratic in
/// the unfolded step payload.
fn class_specific_semantic_charge(
    step: &ProofStep,
    payload: PayloadStats,
    class: SemanticChargeClass,
) -> Result<Option<(usize, usize)>, ProofCheckError> {
    let charge = match class {
        SemanticChargeClass::ResolutionRoute => (0, 0),
        SemanticChargeClass::BoundedAssignmentEval => bounded_assignment_eval_charge(payload)?,
        SemanticChargeClass::UnorderedClauseMatch => unordered_clause_match_charge(step, payload)?,
        SemanticChargeClass::EufIdentityRoute => (
            checked_mul_usize(payload.work, EUF_IDENTITY_WORK_FACTOR)?,
            checked_mul_usize(payload.bytes, EUF_IDENTITY_BYTE_FACTOR)?,
        ),
        SemanticChargeClass::DatatypeEnumPigeonhole => (
            checked_mul_usize(payload.work.max(payload.unfolded_work), 8)?,
            payload.bytes,
        ),
        SemanticChargeClass::ArrayClauseSchema => {
            let square = checked_mul_usize(payload.unfolded_work, payload.unfolded_work)?;
            let linear = checked_add_usize(payload.unfolded_work, payload.work)?;
            (
                checked_mul_usize(checked_add_usize(square, linear)?, ARRAY_SCHEMA_WORK_FACTOR)?,
                checked_add_usize(
                    checked_mul_usize(payload.bytes, 4)?,
                    checked_mul_usize(payload.unfolded_work, ARRAY_SCHEMA_ENTRY_BYTES)?,
                )?,
            )
        }
        SemanticChargeClass::General | SemanticChargeClass::ProgressFarkas => return Ok(None),
    };
    Ok(Some(charge))
}

/// The `General` product a tightening class replaces, saturated rather than
/// checked.
///
/// Every tightening class caps its own model with this value, which makes the
/// class a TIGHTENING by construction: it can only ever charge less than the
/// estimate it replaces, so no proof that fits a caller's envelope today can
/// stop fitting it. Saturation is the conservative direction here — the cap
/// only ever grows — and it keeps a payload near `usize::MAX` from turning a
/// cheaper, perfectly representable charge into a refusal.
fn replaced_general_product(payload: PayloadStats, scale: usize) -> usize {
    let named = payload.work.saturating_mul(payload.unfolded_work);
    let paired = payload.unfolded_work.saturating_mul(payload.unfolded_work);
    named.max(paired).saturating_mul(scale)
}

/// Exact worst case of [`crate::checker::validate_bool_tautology`].
///
/// The validator does three things and nothing else:
///
///  1. one `Sort` check per clause literal — `O(clause_len) <= O(work)`;
///  2. for a UNIT clause, the structural packed-clausification recognizer. It
///     builds one `TermId` set over the unit's top-level disjuncts and then asks
///     only O(1) set questions per disjunct and per member of a negated
///     join — `O(unfolded_work)` since every node it touches is a distinct
///     unfolded occurrence (this is why the recognizer indexes its disjuncts
///     instead of rescanning them; the `Vec` scans it replaced were quadratic
///     and would not fit under this charge);
///  3. otherwise `validate_bounded_clause_semantics`: one DAG walk to collect
///     bounded variables (`O(work)`), then at most
///     [`BOUNDED_EVAL_ASSIGNMENTS`] assignments, each walking every literal's
///     TREE once (`unfolded_work` nodes) and resolving each `Var` node by a
///     linear scan of an environment holding at most
///     `MAX_BOUNDED_ASSIGNMENT_BITS` entries.
///
/// Step 3 dominates, at
/// `BOUNDED_EVAL_ASSIGNMENTS * unfolded_work * min(unfolded_work, BOUNDED_EVAL_ENV_WIDTH)`.
///
/// The `min` is the whole point. The `General` product uses `unfolded_work` for
/// BOTH factors, but the second factor is the ENVIRONMENT width, which
/// saturates at `BOUNDED_EVAL_ENV_WIDTH`. Below that width the two agree; above
/// it the charge grows LINEARLY instead of quadratically, so a wide packed unit
/// stops being refused before its validator has run.
///
/// The result is capped by [`replaced_general_product`], so at every payload
/// this charge is at most what the estimate it replaces would have taken.
///
/// Bytes are deliberately unchanged from the `General`/private-path model
/// (`256 * payload.bytes`): the byte limb was never the binding one for this
/// family, and leaving it alone keeps this a pure work-side tightening.
fn bounded_assignment_eval_charge(
    payload: PayloadStats,
) -> Result<(usize, usize), ProofCheckError> {
    let env_factor = payload.unfolded_work.min(BOUNDED_EVAL_ENV_WIDTH);
    let evaluation = checked_mul_usize(
        checked_mul_usize(payload.unfolded_work, env_factor)?,
        BOUNDED_EVAL_ASSIGNMENTS,
    )?;
    // The literal sort checks, the variable-collection DAG walk and the
    // structural recognizer are each linear in the payload; one extra copy of
    // `work + unfolded_work` covers all three together.
    let structural = checked_add_usize(payload.work, payload.unfolded_work)?;
    let modelled = checked_add_usize(evaluation, structural)?;
    Ok((
        modelled.min(replaced_general_product(payload, BOUNDED_EVAL_ASSIGNMENTS)),
        checked_mul_usize(payload.bytes, BOUNDED_EVAL_ASSIGNMENTS)?,
    ))
}

/// Exact worst case of [`crate::checker::validate_or_clausification`].
///
/// The rule decomposes `(assume (or l1 .. ln))` into `(cl l1 .. ln)`. Its
/// validator does O(1) premise/shape checks, decodes the premise's `or`
/// application, and calls `clause_matches_unordered`, which compares raw
/// `TermId`s pairwise and NEVER descends into a literal: at most
/// `clause_len^2` comparisons over a `clause_len`-entry match bitmap.
///
/// `clause_len <= unfolded_work` for any step (every literal contributes at
/// least one unfolded node), so `clause_len^2 <= unfolded_work^2`; the result is
/// additionally capped by [`replaced_general_product`], making this a tightening
/// of the `General` product at every payload.
fn unordered_clause_match_charge(
    step: &ProofStep,
    payload: PayloadStats,
) -> Result<(usize, usize), ProofCheckError> {
    let clause_len = match step {
        ProofStep::Step { clause, .. } => clause.len(),
        _ => payload.unfolded_work,
    };
    let pairwise = checked_mul_usize(clause_len, clause_len)?;
    let modelled = checked_add_usize(pairwise, clause_len)?;
    Ok((
        modelled.min(replaced_general_product(payload, 1)),
        payload.bytes,
    ))
}

fn string_ground_validator_charge(
    payload: PayloadStats,
) -> Result<(usize, usize), ProofCheckError> {
    let decoded_and_cloned = checked_mul_usize(payload.bytes, 16)?;
    let table_overhead = checked_mul_usize(crate::checker::STRING_EVAL_WORK_LIMIT, 96)?;
    let char_allocation = checked_mul_usize(
        crate::checker::STRING_CHAR_ALLOCATION_LIMIT,
        size_of::<char>(),
    )?;
    let numeric_allocation =
        checked_add_usize(crate::checker::STRING_NUMERIC_BIT_ALLOCATION_LIMIT, 7)? / 8;
    let work = checked_add_usize(
        checked_add_usize(
            crate::checker::STRING_EVAL_WORK_LIMIT,
            crate::checker::STRING_CHAR_ALLOCATION_LIMIT,
        )?,
        crate::checker::STRING_NUMERIC_WORK_LIMIT,
    )?;
    let bytes = checked_add_usize(
        checked_add_usize(
            checked_add_usize(table_overhead, char_allocation)?,
            numeric_allocation,
        )?,
        decoded_and_cloned,
    )?;
    Ok((work, bytes))
}

fn private_validator_charge(
    step: &ProofStep,
    payload: PayloadStats,
    base_work: usize,
    class: SemanticChargeClass,
) -> Result<(usize, usize), ProofCheckError> {
    let charge = match step {
        ProofStep::Step {
            rule: AletheRule::Skolem,
            ..
        } => (100_000, 8 * 1024 * 1024),
        ProofStep::Step {
            rule: AletheRule::Evaluate,
            ..
        } => (100_000, 1024 * 1024),
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::StringGroundEval,
            ..
        } => string_ground_validator_charge(payload)?,
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::RegexIntersectEmpty,
            ..
        } => (10_600_000, 256 * 1024 * 1024),
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::NraIntervalUnsat | TheoryLemmaKind::NraUnivariateUnsat,
            ..
        } => (8_300_000, 128 * 1024 * 1024),
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::Generic,
            ..
        } => {
            // Equality-span extraction/elimination debits its actual rational,
            // DAG, and worst-case structural monomial work through the
            // borrowed progress callback.
            (0, 0)
        }
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::FpForwardError,
            ..
        } => (1_000_000, 16 * 1024 * 1024),
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::FpGroundEval,
            ..
        } => (
            crate::checker::FP_GROUND_WORK_LIMIT,
            checked_mul_usize(payload.bytes, 1 << 16)?,
        ),
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::FpClassification { .. },
            ..
        } => scale_validator_charge(base_work, payload.bytes, 1 << 16)?,
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::OrderIteTautology,
            ..
        } => scale_validator_charge(base_work, payload.bytes, payload.order_assignments)?,
        // `BoolTautology` is NOT here: it owns
        // `SemanticChargeClass::BoundedAssignmentEval`, which charges the
        // evaluator's exact worst case. The BV kinds keep the conservative
        // product because they can also enter the separately budgeted
        // proof-producing bit-blast replay.
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::BvBitBlast | TheoryLemmaKind::BvBitBlastGate { .. },
            ..
        } => scale_validator_charge(base_work, payload.bytes, 1 << 8)?,
        ProofStep::TheoryLemma {
            kind:
                TheoryLemmaKind::ArrayDefaultConst
                | TheoryLemmaKind::ArrayExtensionality
                | TheoryLemmaKind::ArrayFiniteExtensionality
                | TheoryLemmaKind::ArrayFiniteSelectExpansion,
            ..
        } => (100_000, checked_mul_usize(payload.bytes, 2)?),
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::SetCardMemberCount,
            ..
        } => (
            checked_mul_usize(payload.work, payload.unfolded_work)?,
            checked_mul_usize(payload.bytes, 512)?,
        ),
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::LraFarkas | TheoryLemmaKind::LiaGeneric,
            ..
        } => farkas_meter::polynomial_charge(payload, class)?,
        _ => (0, 0),
    };
    Ok(charge)
}

fn scale_validator_charge(
    work: usize,
    bytes: usize,
    factor: usize,
) -> Result<(usize, usize), ProofCheckError> {
    Ok((
        checked_mul_usize(work, factor)?,
        checked_mul_usize(bytes, factor)?,
    ))
}

pub(super) fn semantic_validator_charge(
    step: &ProofStep,
    payload: PayloadStats,
    class: SemanticChargeClass,
) -> Result<(usize, usize), ProofCheckError> {
    if let Some(charge) = class_specific_semantic_charge(step, payload, class)? {
        return Ok(charge);
    }
    let named = checked_mul_usize(payload.work, payload.unfolded_work)?;
    let paired = checked_mul_usize(payload.unfolded_work, payload.unfolded_work)?;
    let base_work = named.max(paired);
    let private = private_validator_charge(step, payload, base_work, class)?;
    Ok((base_work.max(private.0), payload.bytes.max(private.1)))
}

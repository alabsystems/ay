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
        SemanticChargeClass::BvBitBlastReplay => {
            // validate_bv_bitblast_controlled first scans Bool sorts and the
            // reachable DAG for BV content, then runs the same bounded
            // evaluator as BoolTautology. Its possible proof-producing replay
            // was already reserved by validate_expensive_bv_budget; charging
            // a second, payload-squared replay estimate can reject a proof
            // before that bounded checker is entered.
            let (evaluation, bytes) = bounded_assignment_eval_charge(payload)?;
            let structural = checked_mul_usize(payload.work, 4)?;
            (
                checked_add_usize(evaluation, structural)?
                    .min(replaced_general_product(payload, 1 << 8)),
                bytes,
            )
        }
        // The sort checks, the BV-membership scan and the classification walk
        // that refuses: the replay arm's structural limb, and the payload's
        // own bytes.
        SemanticChargeClass::BvBitBlastWithoutEvaluation => {
            (checked_mul_usize(payload.work, 4)?, payload.bytes)
        }
        SemanticChargeClass::BoundedAssignmentEval => bounded_assignment_eval_charge(payload)?,
        SemanticChargeClass::ClosedBvConstantRelation => {
            let (work, old_bytes) = bounded_assignment_eval_charge(payload)?;
            // The exact fragment's fixed scratch bound is derived beside its
            // syntax gate. This never changes work, semantic validation or the
            // caller's budget, and never exceeds the previous byte charge.
            let bytes = checked_add_usize(checked_mul_usize(payload.bytes, 4)?, 4096)?;
            (work, old_bytes.min(bytes))
        }
        SemanticChargeClass::UnorderedClauseMatch => unordered_clause_match_charge(step, payload)?,
        SemanticChargeClass::EufIdentityRoute => (
            checked_mul_usize(payload.work, EUF_IDENTITY_WORK_FACTOR)?,
            checked_mul_usize(payload.bytes, EUF_IDENTITY_BYTE_FACTOR)?,
        ),
        SemanticChargeClass::ClauseIdentityRoute => clause_identity_route_charge(payload)?,
        SemanticChargeClass::AndNegIdentityShape => {
            // Shared 32*DAG-work+32 price: the classifier and validator each
            // perform one immediate-ID/Bool-sort scan. Payload work includes
            // at least both the n+1 clause slots and n source-argument slots,
            // so this bounds both scans without a tree-unfolding product.
            and_pos_charge::and_pos_shallow_match_charge(payload)?
        }
        SemanticChargeClass::AndPosShallowMatch => {
            and_pos_charge::and_pos_shallow_match_charge(payload)?
        }
        SemanticChargeClass::QuantifierProgressMetered => {
            quantifier_charge::quantifier_progress_charge(step, payload)?
        }
        SemanticChargeClass::EquivPosIdentityShape => {
            quantifier_charge::equiv_pos_identity_charge(payload)?
        }
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
        SemanticChargeClass::TrustKindProgressMetered => trust_kind_progress_charge(payload)?,
        SemanticChargeClass::ArrayRowShape => array_row_shape_charge(payload)?,
        SemanticChargeClass::ArrayExtensionalityShape => {
            array_extensionality_shape_charge(payload)?
        }
        SemanticChargeClass::General | SemanticChargeClass::ProgressFarkas => return Ok(None),
    };
    Ok(Some(charge))
}

/// Slot reads per literal that bound `validate_array_select_store`
/// ([`SemanticChargeClass::ArrayRowShape`]).
///
/// Counted from the validator, for a clause of `L` literals: two non-Bool
/// scans (`2L` sort reads), one `flatten_clause_literals` (`1` read plus a
/// clone of the flattened literals), then the three matchers. Each matcher is
/// a fixed program per literal — `matches_row1_conditional` is the widest at
/// `equality_sides` (2) + `row1_eq_parts` (two `select_store_parts` at 9 each
/// plus 2 comparisons) + `find` (2) + `matches_not_equality_pair` (4) + one
/// sort read = 29 — and the three together stay under 64 reads per literal,
/// including the two-literal length guards that make every wider clause fail
/// after the scans. A flattened literal that came from a unit `or` is an
/// argument of that `or`, i.e. a DAG node the base payload walk debited as
/// one unit of `payload.work`, so `payload.work` bounds the literal count on
/// both routes.
pub(super) const ARRAY_ROW_SHAPE_WORK_FACTOR: usize = 64;

/// Slot reads per reachable DAG node that bound the chain route of
/// `validate_array_extensionality`
/// ([`SemanticChargeClass::ArrayExtensionalityShape`]).
///
/// `extensionality_chain_parts` tries two literal orderings; each costs
/// `equality_sides` (2) + three sort reads + `negated_equality_sides` (3),
/// then `select_chain_to_array_pair` at two `well_sorted_select_parts` (5
/// reads each) + two sort reads + four comparisons per peeled level, and then
/// `validate_extensionality_binding` per level: one `terms.get`, one
/// registry lookup keyed by the witness name, three comparisons. Every level
/// is a distinct `select` node of the literal, so levels are bounded by
/// `payload.work`, and `16 + 58 * levels <= 64 * payload.work + 64`. The
/// folded-read fallback is NOT in this factor: it debits its own consumption
/// through the progress callback (see [`FOLDED_READ_UNIT_WORK`]).
pub(super) const ARRAY_EXTENSIONALITY_SHAPE_WORK_FACTOR: usize = 64;

/// Work debited per folded-read budget unit the extensionality fallback
/// consumes (`crate::checker::array_axiom::FoldedReadWorkBudget::consume`).
///
/// One unit is one memoized `FoldedReadMatcher::matches_target` node: a memo
/// probe and insert keyed by a four-tuple, two `Sort` clones, a handful of
/// sort/slot reads, and a `decode_store_fold` walk bounded by the matcher's
/// `FOLD_BOUND` of 64 store levels. 256 covers all of it with headroom; the
/// whole-proof cap of `FOLDED_REGISTRY_WORK_LIMIT` (100_000) units bounds
/// the total at 25.6M, well inside any caller envelope.
pub(crate) const FOLDED_READ_UNIT_WORK: usize = 256;

/// Exact model for [`SemanticChargeClass::ArrayRowShape`]: a constant number
/// of slot reads per literal, and the flatten clone's bytes (already inside
/// `payload.bytes`, which the base walk debits per pushed literal and per
/// reachable node).
///
/// Capped by [`replaced_general_product`] so it is a TIGHTENING at every
/// payload; the byte limb is unchanged (the private model contributed nothing
/// for this kind), so this cannot newly refuse on bytes.
fn array_row_shape_charge(payload: PayloadStats) -> Result<(usize, usize), ProofCheckError> {
    let reads = checked_mul_usize(payload.work, ARRAY_ROW_SHAPE_WORK_FACTOR)?;
    // A `work = 0` payload must still pay for the constant-time guards.
    let modelled = checked_add_usize(reads, ARRAY_ROW_SHAPE_WORK_FACTOR)?;
    Ok((
        modelled.min(replaced_general_product(payload, 1)),
        payload.bytes,
    ))
}

/// Exact model for [`SemanticChargeClass::ArrayExtensionalityShape`]: the
/// chain route's reads, plus the `(array_a, array_b, witness)` binding vector
/// (three `TermId`s per peeled level) on the byte side.
///
/// Work is capped by [`replaced_general_product`]; bytes are capped by the
/// `2 * payload.bytes` the replaced private model charged. Both limbs are
/// therefore tightenings, and the fallback's consumption arrives through the
/// progress callback on top.
fn array_extensionality_shape_charge(
    payload: PayloadStats,
) -> Result<(usize, usize), ProofCheckError> {
    let reads = checked_mul_usize(payload.work, ARRAY_EXTENSIONALITY_SHAPE_WORK_FACTOR)?;
    let modelled = checked_add_usize(reads, ARRAY_EXTENSIONALITY_SHAPE_WORK_FACTOR)?;
    let binding_bytes = checked_mul_usize(payload.work, 3 * size_of::<TermId>())?;
    let bytes = checked_add_usize(payload.bytes, binding_bytes)?;
    let replaced_bytes = payload.bytes.saturating_mul(2);
    Ok((
        modelled.min(replaced_general_product(payload, 1)),
        bytes.min(replaced_bytes),
    ))
}

/// Exact worst case of the three syntax-only clause-identity validators —
/// [`crate::checker::reordering::validate_reordering`],
/// [`crate::checker::boolean_negation::validate_weakening`] and
/// [`crate::checker::boolean_derived::validate_eq_reflexive`].
///
/// Write `n = clause.len() + premise.len()`. Each validator's whole cost is:
///
///  * `reordering`: `2n` element copies (`clause.to_vec()`,
///    `premise.to_vec()`), two `sort_unstable` calls at `<= c*n*log2(n)`
///    comparisons each, and one `Vec` comparison at `<= n`;
///  * `weakening`: one length comparison and one prefix slice comparison,
///    `<= n`;
///  * `eq_reflexive`: `O(1)` — a unit-clause guard, one `decode_app`, one
///    `TermId` comparison.
///
/// The base per-step payload walk debits one work unit per clause literal, per
/// argument and per literal of every RESOLVABLE premise clause, and then debits
/// `roots.len()` a second time, so `payload.work >= 2n`. (A premise the meter
/// cannot resolve is exactly one `premise_clause` rejects with
/// `MissingPremise` / `NonPriorPremise` / `PremiseHasNoClause` before the
/// validator reads a literal, so it is absent from both sides.)
/// [`comparison_sort_bound`] of `payload.work` therefore dominates every term
/// above, and [`CLAUSE_IDENTITY_WORK_FACTOR`] copies of it cover two sorts at
/// `c = 2` plus the three linear passes plus the `O(1)` tail.
///
/// Capped by [`replaced_general_product`] so this is a TIGHTENING at every
/// payload: the cap can only ever select the value the shipped `General` model
/// already charges, so no proof that fits a caller's envelope today can stop
/// fitting it, and no charge this class emits is larger than the one it
/// replaces. The cap binds only where `unfolded_work` is below roughly
/// `8*log2(work)` — i.e. only for steps whose clause and premise together hold
/// a few dozen literals, where the modelled work is a few hundred operations
/// and the charge is byte-identical to today's.
///
/// Bytes are left at the `General`/private model (`payload.bytes`), which
/// already dominates the two `to_vec()` allocations: `push_term_slice` debits
/// `size_of::<TermId>()` bytes per clause and per premise literal, exactly the
/// `n * size_of::<TermId>()` those two exact-capacity `Vec`s allocate, and the
/// DAG walk's own byte charges are on top. Keeping the byte limb where it is
/// makes this a pure work-side correction that cannot newly refuse on bytes.
fn clause_identity_route_charge(payload: PayloadStats) -> Result<(usize, usize), ProofCheckError> {
    let sorts = checked_mul_usize(
        comparison_sort_bound(payload.work),
        CLAUSE_IDENTITY_WORK_FACTOR,
    )?;
    // The `eq_reflexive` tail is O(1) and a `work = 0` payload must still be
    // charged for the constant-time guards the validator runs.
    let modelled = checked_add_usize(sorts, CLAUSE_IDENTITY_WORK_FACTOR)?;
    Ok((
        modelled.min(replaced_general_product(payload, 1)),
        payload.bytes,
    ))
}

/// Exact model for [`SemanticChargeClass::TrustKindProgressMetered`].
///
/// Everything the route can spend beyond what it debits itself is LINEAR: the
/// clause sort/shape scan, and at most two `clause.to_vec()` clones (the
/// deferred-trust collector entry and the derived-clause record). One copy of
/// `work + unfolded_work` covers all of it with headroom; the polynomial part
/// of the route is `nia_linear_ideal`, which charges through the same
/// `progress` callback and is capped by its own `WorkMeter`.
///
/// Capped by [`replaced_general_product`] so it is a TIGHTENING at every
/// payload: no proof that fits a caller's envelope today can stop fitting it.
/// Bytes are left at the `General`/private model (`payload.bytes`) — the byte
/// limb was never the binding one for this family, which keeps this a pure
/// work-side correction.
fn trust_kind_progress_charge(payload: PayloadStats) -> Result<(usize, usize), ProofCheckError> {
    let structural = checked_add_usize(payload.work, payload.unfolded_work)?;
    Ok((
        structural.min(replaced_general_product(payload, 1)),
        payload.bytes,
    ))
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
pub(super) fn replaced_general_product(payload: PayloadStats, scale: usize) -> usize {
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
///
/// `AletheRule::OrPos(_)` shares this model exactly. Its validator
/// ([`crate::checker::boolean::validate_or_pos`]) scans the clause for a
/// `(not (or ...))` literal, materializes `[not_or] ++ args`, and hands both to
/// the SAME `clause_matches_unordered` — which returns immediately unless the
/// two lengths are equal, so its pairwise phase is bounded by `clause_len^2`
/// just as `Or`'s is. The one linear pass neither model names — reading the
/// disjunction's argument list — is already paid for by the per-node payload
/// walk that produced `work`/`unfolded_work` in the first place, which is why
/// this class deliberately charges the CLAUSE and not the term DAG.
///
/// Measured on the `storeinv_t3_np_nf_10` QF_AX canary, one `OrPos(0)` step
/// with `payload(work = 2_035, unfolded_work = 23_046)` was billed the
/// `General` product `23_046^2 = 531_118_116` against a 350_000_000 envelope
/// — 1.5x the WHOLE envelope for a few dozen `TermId` comparisons — and a
/// correct `unsat` published as `unknown`.
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
        } => {
            // The exact ground kernel now borrows this same caller and prices
            // its structural walks, clones, enumeration and numeric scratch
            // before work/allocation. A worst-case 65,536-assignment byte
            // multiplier would double-charge even a one-assignment ground DAG.
            (0, 0)
        }
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::FpClassification { .. },
            ..
        } => {
            // The metered unique-DAG census counts the same distinct FP
            // variable bits as the bounded evaluator. Ground clauses have
            // one assignment; the 16-bit enumeration ceiling is unchanged.
            scale_validator_charge(base_work, payload.bytes, payload.fp_assignments.max(1))?
        }
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::OrderIteTautology,
            ..
        } => scale_validator_charge(base_work, payload.bytes, payload.order_assignments)?,
        // `BoolTautology` is NOT here: it owns
        // `SemanticChargeClass::BoundedAssignmentEval`, which charges the
        // evaluator's exact worst case. Unannotated BvBitBlast owns its
        // replay-aware class; annotated gates retain this conservative
        // product for their additional recursive gate-matching path.
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

/// Name the charge MODEL behind one semantic precharge under
/// `--probe-strict-check`.
///
/// `ProofCheckError::ResourceLimit`'s own doc says the remedy "lives in the
/// charge model or the envelope constant", but the refusal message reports
/// only the aggregate totals — so a single quadratic precharge that exceeds
/// the whole envelope by itself is indistinguishable from a proof that simply
/// accumulated too much. Printing the class and the payload it was computed
/// from is what tells those two apart. Diagnostic only; no behaviour depends
/// on it.
fn probe_semantic_charge(
    step: &ProofStep,
    class: SemanticChargeClass,
    payload: PayloadStats,
    charge: (usize, usize),
) {
    if !ay_core::misc_cli_flags().probe_strict_check {
        return;
    }
    // Only precharges large enough to matter against a caller envelope are
    // worth a line; a large proof emits millions of small ones.
    const PROBE_WORK_FLOOR: usize = 1_000_000;
    if charge.0 < PROBE_WORK_FLOOR {
        return;
    }
    let what = match step {
        ProofStep::Step { rule, .. } => format!("rule {rule:?}"),
        ProofStep::TheoryLemma { kind, .. } => format!("theory lemma {kind:?}"),
        other => format!("{other:?}"),
    };
    eprintln!(
        "--probe-strict-check: semantic precharge class={class:?} on {what}: work={} bytes={} \
         from payload(work={}, unfolded_work={}, bytes={})",
        charge.0, charge.1, payload.work, payload.unfolded_work, payload.bytes
    );
}

pub(super) fn semantic_validator_charge(
    step: &ProofStep,
    payload: PayloadStats,
    class: SemanticChargeClass,
) -> Result<(usize, usize), ProofCheckError> {
    if let Some(charge) = class_specific_semantic_charge(step, payload, class)? {
        probe_semantic_charge(step, class, payload, charge);
        return Ok(charge);
    }
    let named = checked_mul_usize(payload.work, payload.unfolded_work)?;
    let paired = checked_mul_usize(payload.unfolded_work, payload.unfolded_work)?;
    let base_work = named.max(paired);
    let private = private_validator_charge(step, payload, base_work, class)?;
    let charge = (base_work.max(private.0), payload.bytes.max(private.1));
    probe_semantic_charge(step, class, payload, charge);
    Ok(charge)
}

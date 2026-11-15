// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Resource envelopes of the source-bound proof-producing BV checker.
//!
//! One envelope of COUNTED caps serves both callers — gate work, SAT conflicts
//! and decisions, proof bytes, resolution steps and hints, replay work — and
//! the counted caps decide what either of them can prove:
//!
//! * The strict checker's fallback ([`super::proof_producing_control`]) is a
//!   VERDICT path: it decides whether a `BvBitBlast` lemma is accepted. A
//!   counted refusal is a fact about the clause and the caps, so the checker
//!   may remember it (`semantic_decision.rs`).
//! * The source-bound UNSAT authentication lanes
//!   ([`super::authenticate_bool_bv_unsat_query`] and its leaf variants) are
//!   solver-side capability lanes that DECLINE when the envelope runs out.
//!
//! The wall clock only STOPS either of them: the caller's solve deadline when
//! it has one, and otherwise [`PRODUCER_HANG_GUARD`]. A stop is never an
//! acceptance, and it is never remembered as a verdict. (Both lanes used to
//! end at a three-second wall that decided outcomes by host speed and load.)

use super::*;

/// Outer hang guard of the proof producer, for the strict checker and the
/// authentication lanes alike.
///
/// This is NOT a verdict budget. It replaces a three-second wall that decided
/// verdicts: under contention a valid lemma the counted caps accept was
/// rejected because the clock ran out first (measured 2026-09-23 on an 18-core
/// M5 Max, test profile: the 64-bit signed-product lemma validates in 1.0-2.0 s
/// at load 12-40, and was rejected at 3.00-3.03 s with `proof replay deadline
/// expired` under 54 busy spinners).
///
/// The counted caps are finite on their own and calibrated to accept every
/// lemma the old wall accepted (see [`PRODUCER_MAX_CONFLICTS`] and
/// [`PRODUCER_MAX_PROOF_OUTPUT_BYTES`]). The guard remains
/// because ay-sat's bounded producer requires an absolute deadline (its
/// conflict and decision counters do not cover every restart and control-loop
/// iteration), and reaching it still refuses: a stop is never an acceptance.
pub(super) const PRODUCER_HANG_GUARD: Duration = Duration::from_secs(300);

/// Counted SAT conflict cap of one proof-producing attempt.
///
/// With the wall retired, the counted caps ARE the budget, so this one sits
/// above what the three-second wall could buy on the fastest host measured:
/// then no lemma the wall accepted is refused. Measured 2026-09-24 on an
/// 18-core M5 Max, release, load 1.5-6, with an instrumented build (never
/// committed) of the wall (origin/main 5b29370c3) logging every bounded solve,
/// over 12 bit-vector identity families (commutativity, associativity,
/// distributivity, squares, negation, shifts) at 6-16 bits:
///
/// * The wall ended 146 doomed searches after 78,658-180,255 conflicts; the
///   most were 180,255 (9-bit `(x*y)+z = z+(y*x)`), 172,841 (9-bit `bvmul`
///   commutativity) and 168,822 (7-bit `(y+z)*x = y*x + z*x`). An ACCEPTED
///   lemma also had to replay inside the same three seconds (15-20% of its
///   time), so none can have needed more.
/// * The largest refutation it accepted used 90,918 conflicts (13-bit
///   `x*(y<<1) = (x*y)<<1`, 1.90 s); 7-bit distributivity used 80,780 and
///   14-bit `x*(y<<2) = (x*y)<<2` 82,023. A 64,000 cap refused all three.
///
/// 200,000 clears the most the wall ever bought by 1.11x and the largest
/// refutation it accepted by 2.2x. The replay's step cap (250,000) stays above
/// it. What a DOOMED lemma costs is bounded mostly by
/// [`PRODUCER_MAX_PROOF_OUTPUT_BYTES`] (see there), and it pays that once per
/// clause (`semantic_decision.rs`).
///
/// ay-sat's bounded producer is deterministic up to a small trajectory wobble
/// (the same CNF has run out at 83,444 and at 103,134 conflicts in different
/// builds), so a lemma within a few percent of a cap can land either side of
/// it; every accepted lemma above sits far inside.
pub(super) const PRODUCER_MAX_CONFLICTS: u64 = 200_000;

/// Counted cap on the LRAT proof one attempt may emit.
///
/// It sits above the largest proof the replay could ADMIT, so it never refuses
/// a lemma the checker would accept; it only ends sooner an attempt that is
/// refused anyway. Replay admits at most 250,000 steps, 2,000,000 derived
/// literals and 4,000,000 hints (`counted_limits_until`), and binary LRAT is
/// LEB128: at most 3 bytes per literal (at most 150,000 variables), 4 per
/// clause id or hint (ids below 2^27), 3 of framing per step, and deletions
/// batched one record per step, each id deleted once (at most 700,000 inputs
/// plus 200,000 learned). That is 1.75 + 6 + 16 + 0.5 + 3.6 = 27.9 MB at most.
/// Measured (instrumented build, the families above): on every lemma that ran
/// past the hint cap, the 4,000,001st hint lay 9.9-13.3 MB into the stream;
/// the largest accepted proof is 11,919,070 bytes (7-bit distributivity). So
/// 32 MiB (33.5 MB) clears the bound by 1.2x and anything measured by 2.5x.
///
/// Not 64 MiB, the wall's value: that decides nothing more, but a doomed
/// lemma runs twice as long before it stops. Per solve of the CLI probes
/// (16-bit `bvmul` commutativity and distributivity, 32-bit commutativity; 3
/// strict exhaustions and 1 authentication export, all ended by this cap), at
/// 200,000 conflicts and 32 MiB: 5.9-13.0 s in release and 12.4-24.6 s in the
/// test profile, against 29.7-31.3 s for the wall; at 64 MiB, 12.7-17.9 s and
/// 25.9-35.1 s.
pub(super) const PRODUCER_MAX_PROOF_OUTPUT_BYTES: usize = 32 * 1024 * 1024;

pub(super) fn proof_replay_limits(limits: &BvExprProofLimits) -> BvBlastValidateLimits {
    BvBlastValidateLimits {
        deadline: limits
            .resolution
            .validation
            .deadline
            .or(limits.resolution.deadline),
        max_vars: limits.resolution.max_num_vars,
        max_bit_lemmas: limits.max_estimated_gate_work,
        max_clauses: limits.resolution.max_input_clauses,
        max_clause_literals: limits.resolution.max_input_clause_literals,
        max_original_literals: limits.resolution.max_input_literals,
        max_resolution_steps: limits.max_resolution_steps,
        max_derived_literals: limits.resolution.max_derived_literals,
        max_work: limits.resolution.validation.max_work,
    }
}

/// The authentication lanes' envelope: the counted caps below. The wall clock
/// is the caller's solve deadline when it has one — the solve's own budget,
/// which ends everything anyway — and otherwise only [`PRODUCER_HANG_GUARD`].
pub(super) fn proof_producing_limits(
    caller_deadline: Option<Instant>,
) -> (BvExprProofLimits, Instant) {
    ProducerEnvelope::Strict.limits(caller_deadline)
}

/// The strict checker's envelope: exactly the same counted caps, ended only by
/// [`PRODUCER_HANG_GUARD`]. A caller that wants to stop earlier does so
/// through its cancellation poll, which is reported as cancellation rather
/// than as a rejected lemma.
pub(super) fn strict_producer_limits() -> (BvExprProofLimits, Instant) {
    proof_producing_limits(None)
}

/// Which counted envelope one proof-producing attempt runs under.
///
/// `Strict` is the verdict-bearing envelope above: the strict checker's
/// accept/reject of a `BvBitBlast` lemma, and the authentication lanes, are
/// decided by it, so its caps are calibrated never to refuse a lemma the
/// retired three-second wall accepted.
///
/// `Speculative` serves capability probes only — solver-side callers asking
/// "would the checker accept this candidate lemma?" so they may install it
/// when the answer is yes and simply decline their repair when it is no
/// (`recognize_bv_bitblast_speculative_with_progress`). It is a sound
/// under-approximation of `Strict`: every search/proof-size cap is the strict
/// one divided by [`SPECULATIVE_CAP_DIVISOR`], so an acceptance under it is
/// an acceptance under `Strict` (the same decision procedure, stopped
/// sooner), while a refusal says nothing about `Strict` and is remembered
/// only under the speculative envelope's own identity. Its reason to exist
/// is economics: a doomed whole-problem candidate pays the full strict
/// exhaustion (measured 2026-11-07 on QF_BV Mulh_u32.0005's 33-literal
/// authored clause: 35.6 s to the 32 MiB proof-output cap, ~1 MB/s of LRAT
/// emission, in a posture whose verdict a corroboration fallback publishes
/// either way). Callers whose outcome is verdict- or artifact-bearing must
/// stay on `Strict`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum ProducerEnvelope {
    Strict,
    Speculative,
}

/// Every search/proof-size cap of the speculative envelope is the strict one
/// divided by this. A doomed attempt's wall cost is roughly linear in the
/// proof bytes it emits, so the divisor bounds the speculative worst case to
/// about an eighth of the strict one while keeping every internal cap ratio
/// (steps above conflicts, literals per step, hints per step) identical.
const SPECULATIVE_CAP_DIVISOR: u64 = 8;

impl ProducerEnvelope {
    /// This envelope's counted limits and outer deadline, as
    /// [`proof_producing_limits`] for `Strict`.
    pub(super) fn limits(self, caller_deadline: Option<Instant>) -> (BvExprProofLimits, Instant) {
        let hang_guard = Instant::now() + PRODUCER_HANG_GUARD;
        let deadline = caller_deadline.map_or(hang_guard, |outer| outer.min(hang_guard));
        (counted_limits_until_envelope(deadline, self), deadline)
    }

    /// Identity of this envelope's counted caps, for refusal memoization
    /// (`semantic_decision.rs`): a refusal under one envelope is never
    /// replayed under another.
    pub(super) fn id(self) -> u64 {
        match self {
            Self::Strict => strict_producer_envelope_id(),
            Self::Speculative => speculative_producer_envelope_id(),
        }
    }
}

fn envelope_id_of(limits: &BvExprProofLimits) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut limits = limits.clone();
    limits.resolution.deadline = None;
    limits.resolution.validation.deadline = None;
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    format!("{limits:?}").hash(&mut hasher);
    hasher.finish()
}

fn speculative_producer_envelope_id() -> u64 {
    static ID: std::sync::OnceLock<u64> = std::sync::OnceLock::new();
    *ID.get_or_init(|| {
        let (limits, _) = ProducerEnvelope::Speculative.limits(None);
        envelope_id_of(&limits)
    })
}

/// Identity of the strict envelope's COUNTED caps: the key under which a
/// counted refusal may be remembered (see `semantic_decision.rs`).
///
/// Derived from the envelope itself — every field except the two deadlines,
/// which are the hang guard, not caps — so no cap can change without changing
/// the key, and a refusal reached under one set of caps is never replayed
/// under another. Computed once per process: the caps are constants.
pub(super) fn strict_producer_envelope_id() -> u64 {
    static ID: std::sync::OnceLock<u64> = std::sync::OnceLock::new();
    *ID.get_or_init(|| {
        let (limits, _) = strict_producer_limits();
        envelope_id_of(&limits)
    })
}

pub(super) fn counted_limits_until(deadline: Instant) -> BvExprProofLimits {
    counted_limits_until_envelope(deadline, ProducerEnvelope::Strict)
}

/// [`counted_limits_until`] for one envelope: `Strict` is the counted caps
/// below unchanged; `Speculative` divides every search/proof-size cap by
/// [`SPECULATIVE_CAP_DIVISOR`] (admissibility sizes — variables, input
/// clauses and literals, expression shape — are identical, so a speculative
/// attempt reaches the same searches and simply stops them sooner).
pub(super) fn counted_limits_until_envelope(
    deadline: Instant,
    envelope: ProducerEnvelope,
) -> BvExprProofLimits {
    let mut limits = counted_limits_until_strict(deadline);
    if envelope == ProducerEnvelope::Speculative {
        scale_speculative(&mut limits);
    }
    limits
}

/// Divide every search/proof-size cap by [`SPECULATIVE_CAP_DIVISOR`], so the
/// speculative envelope is component-wise at most the strict one (the
/// under-approximation `semantic_decision.rs` relies on when it replays a
/// strict refusal under the speculative envelope without re-deciding).
fn scale_speculative(limits: &mut BvExprProofLimits) {
    fn div_usize(value: usize) -> usize {
        let scaled = (value as u64) / SPECULATIVE_CAP_DIVISOR;
        usize::try_from(scaled.max(1)).unwrap_or(usize::MAX)
    }
    fn div_u64(value: u64) -> u64 {
        (value / SPECULATIVE_CAP_DIVISOR).max(1)
    }
    let resolution = &mut limits.resolution;
    resolution.max_conflicts = resolution.max_conflicts.map(div_u64);
    resolution.max_decisions = resolution.max_decisions.map(div_u64);
    resolution.max_proof_output_bytes = div_usize(resolution.max_proof_output_bytes);
    resolution.max_derived_steps = div_usize(resolution.max_derived_steps);
    resolution.max_derived_literals = div_usize(resolution.max_derived_literals);
    resolution.max_hints = div_usize(resolution.max_hints);
    resolution.max_pending_deletions = div_usize(resolution.max_pending_deletions);
    resolution.max_codec_bytes = div_usize(resolution.max_codec_bytes);
    resolution.max_backward_reconstruction_bytes =
        div_usize(resolution.max_backward_reconstruction_bytes);
    resolution.validation.max_derived_steps = div_usize(resolution.validation.max_derived_steps);
    resolution.validation.max_derived_literals =
        div_usize(resolution.validation.max_derived_literals);
    resolution.validation.max_hints = div_usize(resolution.validation.max_hints);
    resolution.validation.max_work = div_u64(resolution.validation.max_work);
    resolution.validation.max_bytes = div_usize(resolution.validation.max_bytes);
    limits.max_construction_bytes = div_usize(limits.max_construction_bytes);
    limits.max_resolution_steps = div_usize(limits.max_resolution_steps);
    limits.max_expanded_literals = div_usize(limits.max_expanded_literals);
    limits.max_expansion_work = div_usize(limits.max_expansion_work);
    limits.max_expansion_bytes = div_usize(limits.max_expansion_bytes);
}

fn counted_limits_until_strict(deadline: Instant) -> BvExprProofLimits {
    let mut resolution = ResolutionProofLimits {
        deadline: Some(deadline),
        // Keep the pre-upstream size trio. ay-sat documents about 849 resident
        // bytes per variable at construction before clauses; 600k variables
        // alone would exceed 480 MiB before the other separately bounded
        // phases. The clause-db threshold below explicitly is not a solver-wide
        // memory cap, so the larger trio cannot be admitted under the published
        // 768 MiB precharge without bounded/fallible SAT construction or an
        // enforced process RSS envelope.
        max_num_vars: 150_000,
        max_input_clauses: 700_000,
        max_input_literals: 3_000_000,
        max_input_clause_literals: 64,
        max_input_bytes: 64 * 1024 * 1024,
        max_conflicts: Some(PRODUCER_MAX_CONFLICTS),
        max_decisions: Some(2_000_000),
        solver_clause_db_reduction_threshold_bytes: 64 * 1024 * 1024,
        max_proof_output_bytes: PRODUCER_MAX_PROOF_OUTPUT_BYTES,
        max_derived_steps: MAX_PROOF_PRODUCING_RESOLUTION_STEPS,
        max_derived_literals: 2_000_000,
        max_hints: 4_000_000,
        max_pending_deletions: 250_000,
        max_codec_bytes: 192 * 1024 * 1024,
        max_backward_reconstruction_bytes: 64 * 1024 * 1024,
        ..ResolutionProofLimits::default()
    };
    resolution.validation.deadline = Some(deadline);
    resolution.validation.max_original_clauses = resolution.max_input_clauses;
    resolution.validation.max_original_literals = resolution.max_input_literals;
    resolution.validation.max_derived_steps = resolution.max_derived_steps;
    resolution.validation.max_derived_literals = resolution.max_derived_literals;
    resolution.validation.max_hints = resolution.max_hints;
    resolution.validation.max_work = MAX_PROOF_PRODUCING_BV_WORK_PER_LEMMA;
    resolution.validation.max_bytes = PROOF_PRODUCING_REPLAY_BYTES_PER_LEMMA;
    BvExprProofLimits {
        sweep: false,
        max_expr_nodes: MAX_PROOF_PRODUCING_EXPR_NODES,
        // The exporter walks no more occurrences than the lowering may
        // construct; each is one visit and, when it repeats a node, one memo
        // lookup. Encoding work is charged per distinct node above.
        max_expr_occurrences: MAX_PROOF_PRODUCING_CONSTRUCTED_EXPR_NODES,
        max_expr_depth: MAX_PROOF_PRODUCING_EXPR_DEPTH,
        max_leaf_name_bytes: 1024 * 1024,
        max_internal_width: MAX_PROOF_PRODUCING_INTERNAL_BV_WIDTH,
        max_estimated_gate_work: MAX_PROOF_PRODUCING_GATE_WORK,
        max_construction_bytes: PROOF_PRODUCING_REPLAY_BYTES_PER_LEMMA,
        max_resolution_steps: MAX_PROOF_PRODUCING_RESOLUTION_STEPS,
        max_expanded_literals: MAX_PROOF_PRODUCING_EXPANDED_LITERALS,
        max_expansion_work: usize::try_from(MAX_PROOF_PRODUCING_BV_WORK_PER_LEMMA)
            .unwrap_or(usize::MAX),
        max_expansion_bytes: PROOF_PRODUCING_REPLAY_BYTES_PER_LEMMA,
        resolution,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The under-approximation contract `semantic_decision.rs` relies on:
    /// every speculative cap is at most its strict counterpart (so a strict
    /// refusal implies a speculative one), the headline caps are strictly
    /// smaller (so a doomed speculative attempt really is cheaper), and
    /// admissibility sizes are identical (so both envelopes reach the same
    /// searches).
    #[test]
    fn speculative_caps_are_component_wise_at_most_strict() {
        let deadline = Instant::now() + PRODUCER_HANG_GUARD;
        let strict = counted_limits_until_envelope(deadline, ProducerEnvelope::Strict);
        let spec = counted_limits_until_envelope(deadline, ProducerEnvelope::Speculative);
        let (s, p) = (&strict.resolution, &spec.resolution);
        assert!(p.max_conflicts <= s.max_conflicts);
        assert!(p.max_decisions <= s.max_decisions);
        assert!(p.max_proof_output_bytes <= s.max_proof_output_bytes);
        assert!(p.max_derived_steps <= s.max_derived_steps);
        assert!(p.max_derived_literals <= s.max_derived_literals);
        assert!(p.max_hints <= s.max_hints);
        assert!(p.max_pending_deletions <= s.max_pending_deletions);
        assert!(p.max_codec_bytes <= s.max_codec_bytes);
        assert!(p.max_backward_reconstruction_bytes <= s.max_backward_reconstruction_bytes);
        assert!(p.validation.max_derived_steps <= s.validation.max_derived_steps);
        assert!(p.validation.max_derived_literals <= s.validation.max_derived_literals);
        assert!(p.validation.max_hints <= s.validation.max_hints);
        assert!(p.validation.max_work <= s.validation.max_work);
        assert!(p.validation.max_bytes <= s.validation.max_bytes);
        assert!(spec.max_construction_bytes <= strict.max_construction_bytes);
        assert!(spec.max_resolution_steps <= strict.max_resolution_steps);
        assert!(spec.max_expanded_literals <= strict.max_expanded_literals);
        assert!(spec.max_expansion_work <= strict.max_expansion_work);
        assert!(spec.max_expansion_bytes <= strict.max_expansion_bytes);
        assert!(
            p.max_conflicts < s.max_conflicts
                && p.max_proof_output_bytes < s.max_proof_output_bytes,
            "the headline caps must actually shrink"
        );
        assert_eq!(p.max_num_vars, s.max_num_vars);
        assert_eq!(p.max_input_clauses, s.max_input_clauses);
        assert_eq!(p.max_input_literals, s.max_input_literals);
        assert_eq!(p.max_input_clause_literals, s.max_input_clause_literals);
        assert_eq!(p.max_input_bytes, s.max_input_bytes);
        assert_eq!(spec.max_expr_nodes, strict.max_expr_nodes);
        assert_eq!(spec.max_estimated_gate_work, strict.max_estimated_gate_work);
        assert_ne!(
            ProducerEnvelope::Speculative.id(),
            ProducerEnvelope::Strict.id(),
            "the two envelopes must memoize under distinct identities"
        );
    }
}

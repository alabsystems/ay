// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SCC-based Equivalent Literal Substitution (Decompose)
//!
//! Builds the binary implication graph from binary clauses, runs Tarjan's
//! iterative SCC algorithm, and substitutes equivalent literals throughout
//! the clause database. This is CaDiCaL's `decompose.cpp`.
//!
//! If literal `a` and literal `b` are in the same SCC, they are logically
//! equivalent: all occurrences of `b` can be replaced with `a` (choosing
//! the representative with the smallest variable index).
//!
//! If literal `a` and `¬a` are in the same SCC, the formula is UNSAT.
//!
//! Reference: CaDiCaL `decompose.cpp:130-730`

mod rewrite;
mod scc;
#[cfg(test)]
mod tests;

pub(crate) use rewrite::{rewrite_clauses, ClauseMutation};

use crate::literal::Literal;
use crate::watched::WatchedLists;

/// Maximum number of decompose rounds per invocation.
const MAX_ROUNDS: usize = 2;

/// Sentinel value: SCC fully processed, do not revisit.
const TRAVERSED: u32 = u32::MAX;

/// Per-literal DFS state for Tarjan's algorithm.
#[derive(Clone, Copy, Default)]
struct DfsEntry {
    /// DFS index (0 = unvisited, TRAVERSED = done).
    idx: u32,
    /// Minimum reachable DFS index in this SCC.
    min: u32,
}

/// LRAT equivalence chains for a substituted literal.
///
/// For substituted literal `lit` with representative `repr`:
/// - `repr_to_lit`: ClauseRef.0 values along the implication path repr -> lit
///   (used as LRAT hints for proving `(lit | ~repr)`)
/// - `lit_to_repr`: ClauseRef.0 values along the implication path lit -> repr
///   (used as LRAT hints for proving `(repr | ~lit)`)
///
/// Both paths exist because lit and repr are in the same SCC.
/// Reference: CaDiCaL decompose.cpp:266-356 (parent pointer BFS + chain walk).
#[derive(Debug, Clone, Default)]
pub(crate) struct EquivChain {
    pub repr_to_lit: Vec<u32>,
    pub lit_to_repr: Vec<u32>,
}

/// Result of one decompose round.
#[derive(Debug, Default)]
pub(crate) struct DecomposeResult {
    /// Number of variables whose literals were substituted.
    pub substituted: u32,
    /// Number of new units discovered.
    pub new_units: u32,
    /// Whether a new binary clause was created by clause rewriting.
    pub new_binary: bool,
    /// Whether the formula was found to be unsatisfiable.
    pub unsat: bool,
    /// Literals to propagate as units at level 0.
    pub units: Vec<Literal>,
    /// Representative mapping: `reprs[lit.index()]` is the canonical literal
    /// for `lit`. If `reprs[lit.index()] == lit`, the literal is its own
    /// representative (no substitution needed).
    pub reprs: Vec<Literal>,
    /// LRAT equivalence chains for substituted literals.
    /// Indexed by `lit.index()`. Non-empty only for substituted literals.
    pub equiv_chains: Vec<EquivChain>,
}

/// Decompose engine.
pub(crate) struct Decompose {
    /// Per-literal DFS entries, indexed by `lit.index()`.
    dfs: Vec<DfsEntry>,
    /// DFS traversal work stack: `(literal, next_child_position)`.
    work: Vec<(u32, usize)>,
    /// SCC collection stack (literal indices).
    scc_stack: Vec<u32>,
    /// Representative mapping, indexed by `lit.index()`.
    reprs: Vec<Literal>,
    /// Statistics.
    pub stats: DecomposeStats,
    /// Last LRAT decompose dry-run payloads built before fail-closed rejection.
    lrat_dry_run_sidecars: Vec<DecomposeLratDryRunSidecar>,
    /// Decompose-scoped proof-manager observer contexts for retained sidecars.
    lrat_proof_emit_contexts: Vec<DecomposeProofEmitContext>,
    /// Fmla guarded-equivalence overlay LRAT add-row sidecars.
    fmla_guarded_equiv_overlay_lrat_sidecars: Vec<FmlaGuardedEquivOverlayLratSidecar>,
    /// Fmla support-cover LRAT add-row sidecars.
    fmla_guarded_equiv_support_cover_lrat_sidecars: Vec<FmlaGuardedEquivSupportCoverLratSidecar>,
    /// Default-off bridge from retained sidecars to the main proof rewrite materializer.
    lrat_main_rewrite_materializer_preflight_enabled: bool,
    /// Fail-closed LRAT decompose preflight counters.
    lrat_preflight_stats: DecomposeLratPreflightStats,
}

/// Statistics for SCC decomposition.
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct DecomposeStats {
    /// Number of decompose rounds run.
    pub rounds: u64,
    /// Total number of variables substituted by their SCC representative.
    pub substituted: u64,
    /// Number of unit literals discovered during decomposition.
    pub units: u64,
}

/// One checker-facing equivalence derivation planned by an LRAT decompose dry run.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DecomposeLratEquivalenceStep {
    pub original_lit: i64,
    pub representative_lit: i64,
    pub lit_to_repr_source_ids: Vec<u64>,
    pub repr_to_lit_source_ids: Vec<u64>,
    pub planned_lit_to_repr_add_id: u64,
    pub planned_repr_to_lit_add_id: u64,
}

/// Solver-local dry-run payload for one LRAT decompose clause rewrite.
///
/// This payload is retained only as preflight evidence. It never authorizes
/// mutating the clause database in LRAT mode.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DecomposeLratDryRunSidecar {
    pub source_clause_id: u64,
    pub source_clause_lits: Vec<i64>,
    pub rewritten_clause_lits: Vec<i64>,
    pub equivalence_steps: Vec<DecomposeLratEquivalenceStep>,
    pub rewrite_hints: Vec<u64>,
    pub planned_rewrite_add_id: u64,
    pub source_delete_id: u64,
}

/// Scoped context that binds one decompose dry-run sidecar to proof output.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DecomposeProofEmitContext {
    pub transaction_id: u64,
    pub sidecar_context_token: String,
    pub sidecar_row_index: usize,
    pub source_row_id: String,
    pub obligation_id: String,
}

impl DecomposeProofEmitContext {
    pub(crate) fn from_sidecar(
        transaction_id: u64,
        sidecar_row_index: usize,
        sidecar: &DecomposeLratDryRunSidecar,
    ) -> Self {
        Self {
            transaction_id,
            sidecar_context_token: format!("decompose-lrat-{transaction_id}"),
            sidecar_row_index,
            source_row_id: format!("decompose-lrat-source-{}", sidecar.source_clause_id),
            obligation_id: format!("decompose-lrat-{transaction_id}-{sidecar_row_index}"),
        }
    }

    pub(crate) fn from_fmla_guarded_equiv_overlay_binary(
        transaction_id: u64,
        sidecar_row_index: usize,
        direction: &'static str,
        row: &FmlaGuardedEquivOverlayLratBinaryRow,
    ) -> Self {
        Self {
            transaction_id,
            sidecar_context_token: format!("fmla-guarded-equiv-overlay-lrat-{transaction_id}"),
            sidecar_row_index,
            source_row_id: format!(
                "fmla-guarded-equiv-overlay-source-{}",
                row.guarded_ternary_source_id
            ),
            obligation_id: format!(
                "fmla-guarded-equiv-overlay-{transaction_id}-{sidecar_row_index}-{direction}"
            ),
        }
    }

    pub(crate) fn from_fmla_guarded_equiv_support_cover(
        transaction_id: u64,
        sidecar_row_index: usize,
        row: &FmlaGuardedEquivSupportCoverLratSidecar,
    ) -> Self {
        Self {
            transaction_id,
            sidecar_context_token: format!(
                "fmla-guarded-equiv-support-cover-lrat-{transaction_id}"
            ),
            sidecar_row_index,
            source_row_id: format!(
                "fmla-guarded-equiv-support-cover-source-{}",
                row.support_clause_id
            ),
            obligation_id: format!(
                "fmla-guarded-equiv-support-cover-{transaction_id}-{sidecar_row_index}"
            ),
        }
    }
}

/// Checker-visible proof output event kind for scoped decompose observer rows.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum DecomposeProofOutRecordKind {
    Add,
    Delete,
}

/// One proof-manager event bound to a retained decompose sidecar row.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DecomposeProofEmitRecord {
    pub context: DecomposeProofEmitContext,
    pub proof_field: &'static str,
    pub proof_out_record_kind: DecomposeProofOutRecordKind,
    pub checker_visible_id: u64,
    pub delete_source_id: Option<u64>,
    pub clause_lits_dimacs: Vec<i64>,
    pub lrat_hints: Vec<u64>,
    pub proof_manager_mode: &'static str,
    pub solver_runtime_emitted: bool,
    pub proof_writer_io_error: bool,
    pub external_checker_verified: bool,
}

/// One planned overlay LRAT binary add row for a guarded Fmla ternary.
///
/// This is a sidecar row only. It is not a decompose rewrite row and never
/// authorizes deleting or replacing an original clause.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct FmlaGuardedEquivOverlayLratBinaryRow {
    /// Planned checker-visible LRAT id for the overlay binary add.
    pub planned_add_id: u64,
    /// Binary clause literals in DIMACS form.
    pub clause_lits_dimacs: Vec<i64>,
    /// Original guarded ternary source clause id.
    pub guarded_ternary_source_id: u64,
    /// Visible level-0 guard-unit proof id.
    pub guard_unit_proof_id: u64,
    /// File-visible LRAT hints for the planned binary add.
    pub lrat_hints: Vec<u64>,
}

/// Sibling Fmla guarded-equivalence overlay packet retained before SCC preflight.
///
/// The packet represents only planned LRAT additions of guarded binary overlay
/// edges. It has no rewrite target, no delete row, and no model/destructive
/// authority.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct FmlaGuardedEquivOverlayLratSidecar {
    /// Positive guard literal in DIMACS form.
    pub guard_lit_dimacs: i64,
    /// Lower positive endpoint variable in DIMACS form.
    pub lhs_lit_dimacs: i64,
    /// Higher positive endpoint variable in DIMACS form.
    pub rhs_lit_dimacs: i64,
    /// Visible level-0 guard-unit proof id shared by both binary rows.
    pub guard_unit_proof_id: u64,
    /// Forward binary row derived from `-guard -lhs rhs` and the guard unit.
    pub forward_binary: FmlaGuardedEquivOverlayLratBinaryRow,
    /// Reverse binary row derived from `-guard -rhs lhs` and the guard unit.
    pub reverse_binary: FmlaGuardedEquivOverlayLratBinaryRow,
}

/// One planned support-cover LRAT add row for a full guarded-ternary cover.
///
/// This sidecar is add-only. It derives one clause from a positive guard
/// support clause plus one directional ternary for every guard in that support.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct FmlaGuardedEquivSupportCoverLratSidecar {
    /// Planned checker-visible LRAT id for the support-cover add.
    pub planned_add_id: u64,
    /// Positive support clause id used as the last LRAT hint.
    pub support_clause_id: u64,
    /// Positive support guards in DIMACS form.
    pub support_guard_lits_dimacs: Vec<i64>,
    /// Positive source variable in DIMACS form.
    pub source_lit_dimacs: i64,
    /// Positive destination variables in DIMACS form.
    pub destination_lits_dimacs: Vec<i64>,
    /// Derived support-cover clause in DIMACS literal form.
    pub clause_lits_dimacs: Vec<i64>,
    /// Directional guarded ternary source ids, ordered by support guard.
    pub directional_ternary_source_ids: Vec<u64>,
    /// File-visible LRAT hints: directional ternaries, then support clause.
    pub lrat_hints: Vec<u64>,
}

/// Metadata needed to persist a dry-run sidecar in a checker-facing artifact.
#[cfg(test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct DecomposeLratDryRunExport<'a> {
    pub source_dimacs_uri: &'a str,
    pub lrat_proof_uri: &'a str,
    pub transform_transaction_uri: &'a str,
    pub benchmark_id: &'a str,
    pub family: &'a str,
    pub num_vars: u64,
    pub num_clauses: u64,
    pub producer_revision: Option<&'a str>,
}

#[cfg(test)]
impl DecomposeLratDryRunSidecar {
    /// Export this retained preflight sidecar as a stable JSON value.
    pub(crate) fn to_decompose_equivalence_lrat_dry_run_json(
        &self,
        export: &DecomposeLratDryRunExport<'_>,
    ) -> serde_json::Value {
        let equivalence_steps = self
            .equivalence_steps
            .iter()
            .map(|step| {
                serde_json::json!({
                    "original_lit": step.original_lit,
                    "representative_lit": step.representative_lit,
                    "lit_to_repr_source_ids": step.lit_to_repr_source_ids,
                    "repr_to_lit_source_ids": step.repr_to_lit_source_ids,
                    "planned_lit_to_repr_add_id": step.planned_lit_to_repr_add_id,
                    "planned_repr_to_lit_add_id": step.planned_repr_to_lit_add_id,
                })
            })
            .collect::<Vec<_>>();

        serde_json::json!({
            "source_dimacs_uri": export.source_dimacs_uri,
            "lrat_proof_uri": export.lrat_proof_uri,
            "transform_transaction_uri": export.transform_transaction_uri,
            "benchmark_id": export.benchmark_id,
            "family": export.family,
            "num_vars": export.num_vars,
            "num_clauses": export.num_clauses,
            "source_clause_id": self.source_clause_id,
            "source_clause_lits": self.source_clause_lits,
            "rewritten_clause_lits": self.rewritten_clause_lits,
            "equivalence_steps": equivalence_steps,
            "rewrite_hints": self.rewrite_hints,
            "planned_rewrite_add_id": self.planned_rewrite_add_id,
            "source_delete_id": self.source_delete_id,
            "producer_revision": export.producer_revision,
        })
    }
}

/// LRAT decompose preflight counters independent of applied decompose stats.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct DecomposeLratPreflightStats {
    /// Number of LRAT decompose preflight attempts.
    pub attempts: u64,
    /// Number of planned clause rewrite candidates inspected by preflight.
    pub transaction_candidates: u64,
    /// Preflight attempts where SCC decompose found no literal substitutions.
    pub no_substitution: u64,
    /// Preflight attempts where substitutions existed but no rewrite candidates survived.
    pub empty_candidates: u64,
    /// Number of checker-facing dry-run slices retained.
    pub dry_run_emitted: u64,
    /// Number of preflight attempts rejected before mutation.
    pub dry_run_rejected: u64,
    /// Rejections caused by a missing proof manager.
    pub missing_proof_manager: u64,
    /// Rejections caused by a missing or hidden source clause ID.
    pub missing_source_id: u64,
    /// Rejections caused by a missing or hidden implication-chain edge ID.
    pub missing_chain_edge_id: u64,
    /// Rejections caused by a missing equivalence chain.
    pub missing_equiv_chain: u64,
    /// Rejections caused by an unsupported or malformed rewrite shape.
    pub malformed_rewrite: u64,
    /// Rejections caused by a rewrite-side contradiction.
    pub contradiction: u64,
    /// Rejections caused by a missing or hidden level-0 unit proof ID.
    pub missing_level0_unit_id: u64,
    /// Rejections caused by proof-manager planned-add validation.
    pub planned_add_rejected: u64,
    /// Rejections caused by a missing substitution hint for a rewritten literal.
    pub missing_substitution_hint: u64,
    /// Rejections caused by a missing planned transient equivalence proof ID.
    pub missing_transient_equiv_id: u64,
    /// Checker-visible proof additions preflighted in retained dry-run slices.
    pub proof_obligations: u64,
    /// Reconstruction witnesses represented by retained equivalence slices.
    pub reconstruction_witnesses: u64,
    /// Main proof rewrite materializer attempts on the retained preflight path.
    pub main_rewrite_materializer_attempts: u64,
    /// Scoped proof-manager rows seen by the main rewrite materializer.
    pub main_rewrite_materializer_proof_emit_records_seen: u64,
    /// Main rewrite records materialized from runtime proof rows.
    pub main_rewrite_materializer_records: u64,
    /// Materializer attempts that failed closed.
    pub main_rewrite_materializer_fail_closed: u64,
    /// Materializer failures caused by missing runtime proof-manager add/delete rows.
    pub main_rewrite_materializer_missing_runtime_records: u64,
    /// First checker-visible row ID named by a materializer fail-closed rejection.
    pub main_rewrite_materializer_first_reject_checker_visible_id: u64,
    /// First sidecar row index named by a materializer fail-closed rejection.
    pub main_rewrite_materializer_first_reject_sidecar_row_index: u64,
    /// Fmla guarded-equivalence lift preflight attempts.
    pub fmla_lift_attempts: u64,
    /// Whether the Fmla guarded-equivalence packet was detected.
    pub fmla_lift_detected: u64,
    /// Stable Fmla guarded-equivalence scout rejection code.
    pub fmla_lift_rejection_code: u64,
    /// Fmla exactly-one guard groups recovered from the immutable source ledger.
    pub fmla_lift_onehot_groups: u64,
    /// Guarded equivalence pairs recovered from the immutable source ledger.
    pub fmla_lift_guarded_equiv_pairs: u64,
    /// Distinct guards used by recovered guarded equivalences.
    pub fmla_lift_guarded_equiv_guards: u64,
    /// Directional ternary clause witnesses required by recovered guarded equivalences.
    pub fmla_lift_directional_ternary_witnesses: u64,
    /// Variables touched by a future guarded-equivalence rewrite plan.
    pub fmla_lift_touched_vars: u64,
    /// Capture-only runtime ledger records emitted for a representative witness.
    pub fmla_lift_runtime_records: u64,
    /// Capture-only runtime witness checker pass counter.
    pub fmla_lift_witness_checker_passed: u64,
    /// Guarded-equivalence witness pairs checked by the all-source audit.
    pub fmla_lift_all_witness_pairs_checked: u64,
    /// Guarded-equivalence witness pairs missing a recovered guard group.
    pub fmla_lift_all_witness_pairs_missing_guard_group: u64,
    /// LRAT source clause id references checked across all retained witnesses.
    pub fmla_lift_source_id_refs_checked: u64,
    /// Unique LRAT source clause ids checked across all retained witnesses.
    pub fmla_lift_unique_source_ids_checked: u64,
    /// Unique LRAT source clause ids checked by the guarded-equivalence lift.
    pub fmla_lift_source_ids_checked: u64,
    /// LRAT source clause ids that are proof-manager-visible.
    pub fmla_lift_source_ids_visible: u64,
    /// LRAT source clause ids missing from the proof-manager-visible set.
    pub fmla_lift_source_ids_missing: u64,
    /// First missing LRAT source clause id, or zero when every source id is visible.
    pub fmla_lift_first_missing_source_id: u64,
    /// Whether proof obligations are ready for a destructive guarded-equivalence lift.
    pub fmla_lift_proof_ready: u64,
    /// Whether model reconstruction is ready for a destructive guarded-equivalence lift.
    pub fmla_lift_model_ready: u64,
    /// Whether destructive guarded-equivalence lifting is allowed.
    pub fmla_lift_destructive_allowed: u64,
}

/// Read-only Fmla guarded-equivalence lift telemetry captured before SCC preflight.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) struct FmlaGuardedEquivLiftPreflight {
    pub attempts: u64,
    pub detected: u64,
    pub rejection_code: u64,
    pub onehot_groups: u64,
    pub guarded_equiv_pairs: u64,
    pub guarded_equiv_guards: u64,
    pub directional_ternary_witnesses: u64,
    pub touched_vars: u64,
    pub runtime_records: u64,
    pub witness_checker_passed: u64,
    pub all_witness_pairs_checked: u64,
    pub all_witness_pairs_missing_guard_group: u64,
    pub source_id_refs_checked: u64,
    pub unique_source_ids_checked: u64,
    pub source_ids_checked: u64,
    pub source_ids_visible: u64,
    pub source_ids_missing: u64,
    pub first_missing_source_id: u64,
    pub proof_ready: u64,
    pub model_ready: u64,
    pub destructive_allowed: u64,
}

impl Decompose {
    pub(crate) fn new(num_vars: usize) -> Self {
        let num_lits = num_vars * 2;
        Self {
            dfs: vec![DfsEntry::default(); num_lits],
            work: Vec::new(),
            scc_stack: Vec::new(),
            reprs: (0..num_lits as u32).map(Literal).collect(),
            stats: DecomposeStats::default(),
            lrat_dry_run_sidecars: Vec::new(),
            lrat_proof_emit_contexts: Vec::new(),
            fmla_guarded_equiv_overlay_lrat_sidecars: Vec::new(),
            fmla_guarded_equiv_support_cover_lrat_sidecars: Vec::new(),
            lrat_main_rewrite_materializer_preflight_enabled: false,
            lrat_preflight_stats: DecomposeLratPreflightStats::default(),
        }
    }

    /// Restore previously saved statistics (e.g., after compaction recreates
    /// the engine via `Decompose::new()`). Without this, stats are zeroed.
    pub(crate) fn restore_stats(&mut self, stats: DecomposeStats) {
        self.stats = stats;
    }

    pub(crate) fn clear_lrat_dry_run_sidecars(&mut self) {
        self.lrat_dry_run_sidecars.clear();
        self.lrat_proof_emit_contexts.clear();
    }

    pub(crate) fn clear_fmla_guarded_equiv_overlay_lrat_sidecars(&mut self) {
        self.fmla_guarded_equiv_overlay_lrat_sidecars.clear();
        self.fmla_guarded_equiv_support_cover_lrat_sidecars.clear();
    }

    pub(crate) fn set_fmla_guarded_equiv_overlay_lrat_sidecars(
        &mut self,
        sidecars: Vec<FmlaGuardedEquivOverlayLratSidecar>,
    ) {
        self.fmla_guarded_equiv_overlay_lrat_sidecars = sidecars;
    }

    pub(crate) fn set_fmla_guarded_equiv_support_cover_lrat_sidecars(
        &mut self,
        sidecars: Vec<FmlaGuardedEquivSupportCoverLratSidecar>,
    ) {
        self.fmla_guarded_equiv_support_cover_lrat_sidecars = sidecars;
    }

    #[allow(dead_code)]
    pub(crate) fn set_lrat_dry_run_sidecars(&mut self, sidecars: Vec<DecomposeLratDryRunSidecar>) {
        self.set_lrat_dry_run_sidecars_with_contexts(sidecars, Vec::new());
    }

    pub(crate) fn set_lrat_dry_run_sidecars_with_contexts(
        &mut self,
        sidecars: Vec<DecomposeLratDryRunSidecar>,
        contexts: Vec<DecomposeProofEmitContext>,
    ) {
        debug_assert!(
            contexts.is_empty() || contexts.len() == sidecars.len(),
            "BUG: decompose sidecar proof contexts must be empty or sidecar-aligned"
        );
        let proof_obligations = sidecars
            .iter()
            .map(|sidecar| {
                sidecar
                    .equivalence_steps
                    .len()
                    .saturating_mul(2)
                    .saturating_add(1)
            })
            .sum::<usize>() as u64;
        let reconstruction_witnesses = sidecars
            .iter()
            .map(|sidecar| sidecar.equivalence_steps.len())
            .sum::<usize>() as u64;
        self.lrat_preflight_stats.dry_run_emitted = self
            .lrat_preflight_stats
            .dry_run_emitted
            .saturating_add(sidecars.len() as u64);
        self.lrat_preflight_stats.proof_obligations = self
            .lrat_preflight_stats
            .proof_obligations
            .saturating_add(proof_obligations);
        self.lrat_preflight_stats.reconstruction_witnesses = self
            .lrat_preflight_stats
            .reconstruction_witnesses
            .saturating_add(reconstruction_witnesses);
        self.lrat_dry_run_sidecars = sidecars;
        self.lrat_proof_emit_contexts = contexts;
    }

    pub(crate) fn record_lrat_preflight_attempt(&mut self) {
        self.lrat_preflight_stats.attempts = self.lrat_preflight_stats.attempts.saturating_add(1);
    }

    pub(crate) fn record_lrat_preflight_transaction_candidates(&mut self, count: u64) {
        self.lrat_preflight_stats.transaction_candidates = self
            .lrat_preflight_stats
            .transaction_candidates
            .saturating_add(count);
    }

    pub(crate) fn record_lrat_preflight_no_substitution(&mut self) {
        self.lrat_preflight_stats.no_substitution =
            self.lrat_preflight_stats.no_substitution.saturating_add(1);
    }

    pub(crate) fn record_lrat_preflight_empty_candidates(&mut self) {
        self.lrat_preflight_stats.empty_candidates =
            self.lrat_preflight_stats.empty_candidates.saturating_add(1);
    }

    pub(crate) fn record_lrat_preflight_dry_run_rejected(&mut self) {
        self.lrat_preflight_stats.dry_run_rejected =
            self.lrat_preflight_stats.dry_run_rejected.saturating_add(1);
    }

    pub(crate) fn record_lrat_preflight_missing_proof_manager(&mut self) {
        self.lrat_preflight_stats.missing_proof_manager = self
            .lrat_preflight_stats
            .missing_proof_manager
            .saturating_add(1);
    }

    pub(crate) fn record_lrat_preflight_missing_source_id(&mut self) {
        self.lrat_preflight_stats.missing_source_id = self
            .lrat_preflight_stats
            .missing_source_id
            .saturating_add(1);
    }

    pub(crate) fn record_lrat_preflight_missing_chain_edge_id(&mut self) {
        self.lrat_preflight_stats.missing_chain_edge_id = self
            .lrat_preflight_stats
            .missing_chain_edge_id
            .saturating_add(1);
    }

    pub(crate) fn record_lrat_preflight_missing_equiv_chain(&mut self) {
        self.lrat_preflight_stats.missing_equiv_chain = self
            .lrat_preflight_stats
            .missing_equiv_chain
            .saturating_add(1);
    }

    pub(crate) fn record_lrat_preflight_malformed_rewrite(&mut self) {
        self.lrat_preflight_stats.malformed_rewrite = self
            .lrat_preflight_stats
            .malformed_rewrite
            .saturating_add(1);
    }

    pub(crate) fn record_lrat_preflight_contradiction(&mut self) {
        self.lrat_preflight_stats.contradiction =
            self.lrat_preflight_stats.contradiction.saturating_add(1);
    }

    pub(crate) fn record_lrat_preflight_missing_level0_unit_id(&mut self) {
        self.lrat_preflight_stats.missing_level0_unit_id = self
            .lrat_preflight_stats
            .missing_level0_unit_id
            .saturating_add(1);
    }

    pub(crate) fn record_lrat_preflight_planned_add_rejected(&mut self) {
        self.lrat_preflight_stats.planned_add_rejected = self
            .lrat_preflight_stats
            .planned_add_rejected
            .saturating_add(1);
    }

    pub(crate) fn record_lrat_preflight_missing_substitution_hint(&mut self) {
        self.lrat_preflight_stats.missing_substitution_hint = self
            .lrat_preflight_stats
            .missing_substitution_hint
            .saturating_add(1);
    }

    pub(crate) fn record_lrat_preflight_missing_transient_equiv_id(&mut self) {
        self.lrat_preflight_stats.missing_transient_equiv_id = self
            .lrat_preflight_stats
            .missing_transient_equiv_id
            .saturating_add(1);
    }

    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn set_lrat_main_rewrite_materializer_preflight_enabled(&mut self, enabled: bool) {
        self.lrat_main_rewrite_materializer_preflight_enabled = enabled;
    }

    pub(crate) fn lrat_main_rewrite_materializer_preflight_enabled(&self) -> bool {
        self.lrat_main_rewrite_materializer_preflight_enabled
    }

    pub(crate) fn record_lrat_main_rewrite_materializer_attempt(
        &mut self,
        proof_emit_records_seen: u64,
        records_materialized: u64,
    ) {
        self.lrat_preflight_stats.main_rewrite_materializer_attempts = self
            .lrat_preflight_stats
            .main_rewrite_materializer_attempts
            .saturating_add(1);
        self.lrat_preflight_stats
            .main_rewrite_materializer_proof_emit_records_seen = self
            .lrat_preflight_stats
            .main_rewrite_materializer_proof_emit_records_seen
            .saturating_add(proof_emit_records_seen);
        self.lrat_preflight_stats.main_rewrite_materializer_records = self
            .lrat_preflight_stats
            .main_rewrite_materializer_records
            .saturating_add(records_materialized);
    }

    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn record_lrat_main_rewrite_materializer_fail_closed(
        &mut self,
        missing_runtime_record: bool,
    ) {
        self.record_lrat_main_rewrite_materializer_fail_closed_detail(missing_runtime_record, 0, 0);
    }

    pub(crate) fn record_lrat_main_rewrite_materializer_fail_closed_detail(
        &mut self,
        missing_runtime_record: bool,
        sidecar_row_index: usize,
        checker_visible_id: u64,
    ) {
        self.lrat_preflight_stats
            .main_rewrite_materializer_fail_closed = self
            .lrat_preflight_stats
            .main_rewrite_materializer_fail_closed
            .saturating_add(1);
        if missing_runtime_record {
            self.lrat_preflight_stats
                .main_rewrite_materializer_missing_runtime_records = self
                .lrat_preflight_stats
                .main_rewrite_materializer_missing_runtime_records
                .saturating_add(1);
        }
        if checker_visible_id != 0
            && self
                .lrat_preflight_stats
                .main_rewrite_materializer_first_reject_checker_visible_id
                == 0
        {
            self.lrat_preflight_stats
                .main_rewrite_materializer_first_reject_checker_visible_id = checker_visible_id;
            self.lrat_preflight_stats
                .main_rewrite_materializer_first_reject_sidecar_row_index =
                sidecar_row_index as u64;
        }
    }

    pub(crate) fn record_fmla_guarded_equiv_lift_preflight(
        &mut self,
        stats: FmlaGuardedEquivLiftPreflight,
    ) {
        self.lrat_preflight_stats.fmla_lift_attempts = self
            .lrat_preflight_stats
            .fmla_lift_attempts
            .saturating_add(stats.attempts);
        self.lrat_preflight_stats.fmla_lift_detected = self
            .lrat_preflight_stats
            .fmla_lift_detected
            .saturating_add(stats.detected);
        self.lrat_preflight_stats.fmla_lift_rejection_code = stats.rejection_code;
        self.lrat_preflight_stats.fmla_lift_onehot_groups = self
            .lrat_preflight_stats
            .fmla_lift_onehot_groups
            .saturating_add(stats.onehot_groups);
        self.lrat_preflight_stats.fmla_lift_guarded_equiv_pairs = self
            .lrat_preflight_stats
            .fmla_lift_guarded_equiv_pairs
            .saturating_add(stats.guarded_equiv_pairs);
        self.lrat_preflight_stats.fmla_lift_guarded_equiv_guards = self
            .lrat_preflight_stats
            .fmla_lift_guarded_equiv_guards
            .saturating_add(stats.guarded_equiv_guards);
        self.lrat_preflight_stats
            .fmla_lift_directional_ternary_witnesses = self
            .lrat_preflight_stats
            .fmla_lift_directional_ternary_witnesses
            .saturating_add(stats.directional_ternary_witnesses);
        self.lrat_preflight_stats.fmla_lift_touched_vars = self
            .lrat_preflight_stats
            .fmla_lift_touched_vars
            .saturating_add(stats.touched_vars);
        self.lrat_preflight_stats.fmla_lift_runtime_records = self
            .lrat_preflight_stats
            .fmla_lift_runtime_records
            .saturating_add(stats.runtime_records);
        self.lrat_preflight_stats.fmla_lift_witness_checker_passed = self
            .lrat_preflight_stats
            .fmla_lift_witness_checker_passed
            .saturating_add(stats.witness_checker_passed);
        self.lrat_preflight_stats
            .fmla_lift_all_witness_pairs_checked = self
            .lrat_preflight_stats
            .fmla_lift_all_witness_pairs_checked
            .saturating_add(stats.all_witness_pairs_checked);
        self.lrat_preflight_stats
            .fmla_lift_all_witness_pairs_missing_guard_group = self
            .lrat_preflight_stats
            .fmla_lift_all_witness_pairs_missing_guard_group
            .saturating_add(stats.all_witness_pairs_missing_guard_group);
        self.lrat_preflight_stats.fmla_lift_source_id_refs_checked = self
            .lrat_preflight_stats
            .fmla_lift_source_id_refs_checked
            .saturating_add(stats.source_id_refs_checked);
        self.lrat_preflight_stats
            .fmla_lift_unique_source_ids_checked = self
            .lrat_preflight_stats
            .fmla_lift_unique_source_ids_checked
            .saturating_add(stats.unique_source_ids_checked);
        self.lrat_preflight_stats.fmla_lift_source_ids_checked = self
            .lrat_preflight_stats
            .fmla_lift_source_ids_checked
            .saturating_add(stats.source_ids_checked);
        self.lrat_preflight_stats.fmla_lift_source_ids_visible = self
            .lrat_preflight_stats
            .fmla_lift_source_ids_visible
            .saturating_add(stats.source_ids_visible);
        self.lrat_preflight_stats.fmla_lift_source_ids_missing = self
            .lrat_preflight_stats
            .fmla_lift_source_ids_missing
            .saturating_add(stats.source_ids_missing);
        if stats.first_missing_source_id != 0
            && self.lrat_preflight_stats.fmla_lift_first_missing_source_id == 0
        {
            self.lrat_preflight_stats.fmla_lift_first_missing_source_id =
                stats.first_missing_source_id;
        }
        self.lrat_preflight_stats.fmla_lift_proof_ready = self
            .lrat_preflight_stats
            .fmla_lift_proof_ready
            .saturating_add(stats.proof_ready);
        self.lrat_preflight_stats.fmla_lift_model_ready = self
            .lrat_preflight_stats
            .fmla_lift_model_ready
            .saturating_add(stats.model_ready);
        self.lrat_preflight_stats.fmla_lift_destructive_allowed = self
            .lrat_preflight_stats
            .fmla_lift_destructive_allowed
            .saturating_add(stats.destructive_allowed);
    }

    pub(crate) fn record_fmla_guarded_equiv_lift_route_readiness(
        &mut self,
        proof_ready: bool,
        model_ready: bool,
        destructive_allowed: bool,
    ) {
        self.lrat_preflight_stats.fmla_lift_proof_ready = self
            .lrat_preflight_stats
            .fmla_lift_proof_ready
            .saturating_add(u64::from(proof_ready));
        self.lrat_preflight_stats.fmla_lift_model_ready = self
            .lrat_preflight_stats
            .fmla_lift_model_ready
            .saturating_add(u64::from(model_ready));
        self.lrat_preflight_stats.fmla_lift_destructive_allowed = self
            .lrat_preflight_stats
            .fmla_lift_destructive_allowed
            .saturating_add(u64::from(destructive_allowed));
    }

    pub(crate) fn lrat_dry_run_sidecars(&self) -> &[DecomposeLratDryRunSidecar] {
        &self.lrat_dry_run_sidecars
    }

    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn fmla_guarded_equiv_overlay_lrat_sidecars(
        &self,
    ) -> &[FmlaGuardedEquivOverlayLratSidecar] {
        &self.fmla_guarded_equiv_overlay_lrat_sidecars
    }

    pub(crate) fn fmla_guarded_equiv_support_cover_lrat_sidecars(
        &self,
    ) -> &[FmlaGuardedEquivSupportCoverLratSidecar] {
        &self.fmla_guarded_equiv_support_cover_lrat_sidecars
    }

    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn lrat_proof_emit_contexts(&self) -> &[DecomposeProofEmitContext] {
        &self.lrat_proof_emit_contexts
    }

    pub(crate) fn lrat_preflight_stats(&self) -> DecomposeLratPreflightStats {
        self.lrat_preflight_stats
    }

    pub(crate) fn ensure_num_vars(&mut self, num_vars: usize) {
        let num_lits = num_vars * 2;
        if self.dfs.len() < num_lits {
            self.dfs.resize(num_lits, DfsEntry::default());
            let old_len = self.reprs.len();
            self.reprs.resize(num_lits, Literal(0));
            for i in old_len..num_lits {
                self.reprs[i] = Literal(i as u32);
            }
        }
    }

    /// Run up to `MAX_ROUNDS` of SCC decomposition.
    ///
    /// Returns a `DecomposeResult` describing the substitutions found.
    /// The caller is responsible for rewriting clauses and propagating units.
    ///
    /// `need_chains` controls LRAT equivalence-chain construction. The
    /// chains are consumed ONLY by the LRAT hint machinery
    /// (decompose_equiv_ids emission and the decompose LRAT preflight
    /// sidecars); DRAT emission and the no-proof path never read them.
    /// Building them is catastrophically expensive on collapse-heavy
    /// giants: `build_equiv_chains` allocates three O(num_lits) zeroed
    /// buffers PER SCC and `bfs_path_to_repr` three more PER SCC MEMBER —
    /// profiled 2026-07-11 (sparse-prize completion round) on 07cea7a6
    /// (783K vars → 1.57M lits, 275,256 equivalences): a SINGLE
    /// `Decompose::run` spent 100+s, ~90% in `memset`, consuming the whole
    /// 120s competition budget inside preprocess before BVE or search ever
    /// ran. Callers on the non-LRAT route (`decompose_body`, which
    /// early-returns under LRAT) must pass `false`; the LRAT preflight
    /// passes `true`.
    pub(crate) fn run(
        &mut self,
        watches: &WatchedLists,
        num_vars: usize,
        vals: &[i8],
        frozen: &[u32],
        var_states: &[crate::solver::lifecycle::VarState],
        need_chains: bool,
    ) -> DecomposeResult {
        self.run_inner(watches, num_vars, vals, frozen, var_states, need_chains)
    }

    fn run_inner(
        &mut self,
        watches: &WatchedLists,
        num_vars: usize,
        vals: &[i8],
        frozen: &[u32],
        var_states: &[crate::solver::lifecycle::VarState],
        need_chains: bool,
    ) -> DecomposeResult {
        let num_lits = num_vars * 2;
        // CaDiCaL decompose.cpp:139: must have sufficient buffer capacity
        debug_assert!(
            self.dfs.len() >= num_lits,
            "BUG: decompose dfs buffer too small ({} < {num_lits})",
            self.dfs.len(),
        );
        debug_assert!(
            self.reprs.len() >= num_lits,
            "BUG: decompose reprs buffer too small ({} < {num_lits})",
            self.reprs.len(),
        );
        // Reset DFS state.
        for e in self.dfs[..num_lits].iter_mut() {
            *e = DfsEntry::default();
        }
        // Reset representatives to identity.
        for i in 0..num_lits {
            self.reprs[i] = Literal(i as u32);
        }

        let mut combined = DecomposeResult {
            reprs: self.reprs[..num_lits].to_vec(),
            equiv_chains: if need_chains {
                vec![EquivChain::default(); num_lits]
            } else {
                Vec::new()
            },
            ..DecomposeResult::default()
        };

        for _round in 0..MAX_ROUNDS {
            let result = self.run_round(watches, num_vars, vals, frozen, var_states, need_chains);
            self.stats.rounds += 1;
            self.stats.substituted += u64::from(result.substituted);
            self.stats.units += u64::from(result.new_units);

            if result.unsat {
                combined.unsat = true;
                combined.units.extend(result.units);
                combined.reprs = self.reprs[..num_lits].to_vec();
                return combined;
            }

            combined.substituted += result.substituted;
            combined.new_units += result.new_units;
            combined.new_binary |= result.new_binary;
            combined.units.extend(result.units);

            // Merge equiv_chains from this round.
            for (i, chain) in result.equiv_chains.into_iter().enumerate() {
                if (!chain.repr_to_lit.is_empty() || !chain.lit_to_repr.is_empty())
                    && i < combined.equiv_chains.len()
                {
                    combined.equiv_chains[i] = chain;
                }
            }

            if result.substituted == 0 || (!result.new_binary && result.new_units == 0) {
                break;
            }

            // Reset DFS for next round (representatives carry over).
            for e in self.dfs[..num_lits].iter_mut() {
                *e = DfsEntry::default();
            }
        }

        combined.reprs = self.reprs[..num_lits].to_vec();
        combined
    }
}

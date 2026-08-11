// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Clause factorization: introduce extension variables to compress clause structure.
//!
//! Factoring identifies groups of clauses that share all literals except one
//! (the "factor"). A fresh extension variable compresses N clauses into fewer:
//!
//! Given clauses that form a `factors × quotients` matrix (each clause is
//! Q_i ∨ f_j for quotient Q_i and factor f_j), we replace them with:
//!
//! - Binary "divider" clauses: `(fresh ∨ f_j)` for each factor
//! - "Quotient" clauses: `(¬fresh ∨ Q_i)` for each quotient
//!
//! Net effect: `factors * quotients` clauses become `factors + quotients` clauses.
//! Reduction: `factors * quotients - factors - quotients`.
//!
//! Reference: CaDiCaL `factor.cpp` (Biere et al.)

mod chain;
#[cfg(test)]
mod tests;

use crate::clause_arena::ClauseArena;
use crate::literal::{Literal, Variable};
use crate::occ_list::OccList;

use chain::{
    find_best_quotient, find_complementary_factors, flush_unmatched_clauses, QuotientLevel,
};

/// Maximum clause size eligible for factorization.
/// CaDiCaL: `factorsize = 5` (options.hpp:124). Larger clauses rarely
/// factor productively and waste effort scanning occurrence lists.
pub(crate) const FACTOR_SIZE_LIMIT: usize = 5;

/// Minimum factor count for a factoring candidate to be considered.
const MIN_FACTOR_MATCHES: usize = 2;

/// Factor occurrence-list elements (`usize` clause indices, 8 bytes each) that
/// share one 64-byte cache line: `64 / 8 = 8`. kissat charges 1 tick per cache
/// line of watch list scanned (`kissat_cache_lines`, factor.c:341/392) — its
/// watches are 4 bytes so it packs 32 per 128-byte line; AY's occ list stores
/// 8-byte `usize` indices, so 8 per 64-byte line is the physically honest
/// divisor for AY's layout. Mirrors the BCP cache-line accounting convention
/// (`propagation_bcp.rs`, `div_ceil(32)` for its 4-byte SoA watches).
const FACTOR_OCC_ELEMS_PER_CACHE_LINE: u64 = 8;

/// Compile-time default for [`factor_cacheline_ticks_enabled`] when
/// `AY_AB_FACTOR_CACHELINE_TICKS` is unset. DEFAULT OFF (opt-in) — see below.
///
/// A/B decision (wf_b9b100ed, 12-instance dense board ON vs OFF, 120s serial,
/// budgets held per option (a)): every VERDICT held (12/12, zero flips), but
/// cache-line accounting makes the existing 500M/1B budgets bind ~8x deeper, so
/// dense instances that were correctly BUDGET-LIMITED at their productive yield
/// OVER-FACTOR and regress the SPEED floor:
///   - a2fe3213: 320 -> 9835 factors, 9.3s -> 76.9s  (8.3x slower)  [SAT held]
///   - df813fe7: 6746 -> 8088 factors, 24.0s -> 41.8s (1.7x slower) [UNSAT held]
///   - 0ec8c5e9: 88.7s -> 116.9s (deeper prepro drain, near-timeout) [SAT held]
/// Complete-drain and non-factoring floor instances were neutral no-ops
/// (46355da 318=318 factors 2.65s~2.71s; 82851650 326=326 1.31s~1.26s; the
/// fc=0 instances byte-for-behavior). The REGRESSION FLOOR requires verdicts
/// AND speed to hold, so DEFAULT-ON is rejected.
///
/// The change's VALUE is as a TARGETED opt-in for the budget-limited hard band
/// (f6a085f3/6ff70a3a), where deeper factoring toward kissat parity is the goal:
/// enabling it drives f6a085f3 from 20 -> 11235 factorings (toward kissat's
/// ~70,867) under the same 1B cap (no flip in 120s alone — still needs the
/// post-factor BVE-reopen + 58s-wall levers, cf. AY_FACTOR_MAX_EFFORT).
/// Mirrors the sibling AY_FACTOR_MAX_EFFORT knob: measured-negative for a
/// global default, useful opt-in for the f6 band. Option (b) (re-scaling the
/// 500M/1B budgets DOWN ~8x) would neutralize the over-factoring and restore
/// today's per-instance yield, but that is a behavioral no-op (no gain) and is
/// intentionally NOT taken — keeping budgets untouched makes the kill switch
/// byte-identical to main.
const FACTOR_CACHELINE_TICKS_DEFAULT_ON: bool = false;

/// Whether factor-scan tick accounting is cache-line-granular (kissat parity)
/// rather than one-tick-per-occurrence-element. Resolved once from
/// `AY_AB_FACTOR_CACHELINE_TICKS`:
/// - unset  => [`FACTOR_CACHELINE_TICKS_DEFAULT_ON`] (false — per-occ-element
///   accounting, byte-identical to pre-change tick totals)
/// - `"0"`  => forced OFF (explicit kill switch; same as unset)
/// - other  => forced ON (cache-line accounting; the opt-in for the f6 band)
///
/// Cached in a `OnceLock` (mirrors the `AY_AB_*` flag convention) so the hot
/// factor occurrence scans never pay an env syscall.
#[inline]
pub(super) fn factor_cacheline_ticks_enabled() -> bool {
    use std::sync::OnceLock;
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| {
        match std::env::var("AY_AB_FACTOR_CACHELINE_TICKS")
            .ok()
            .as_deref()
        {
            None => FACTOR_CACHELINE_TICKS_DEFAULT_ON,
            Some("0") => false,
            Some(_) => true,
        }
    })
}

/// Compile-time default for [`factor_bin_fastpath_enabled`] when
/// `AY_AB_FACTOR_BIN_FASTPATH` is unset.
///
/// The binary-partner fast path is behavior-preserving: it replaces the
/// generic occurrence scan in `find_next_factor` with kissat's inline binary
/// branch for size-2 source clauses, producing the SAME counted candidates and
/// recorded matches (the arena checks it elides are structurally implied on a
/// binary source), and charging the SAME scan ticks (partner arrays are
/// positionally aligned with the occ lists), so the effort budget binds
/// identically and the SET of applied factorings is unchanged — only the
/// per-occurrence-element cost drops (no clause-arena dereference). Default ON:
/// it holds the regression floor byte-behaviorally (same factor_count, same
/// verdicts) and only accelerates discovery.
const FACTOR_BIN_FASTPATH_DEFAULT_ON: bool = true;

/// Whether `find_next_factor` uses the binary-partner fast path (kissat's
/// inline binary branch) for size-2 source clauses. Resolved once from
/// `AY_AB_FACTOR_BIN_FASTPATH`:
/// - unset  => [`FACTOR_BIN_FASTPATH_DEFAULT_ON`] (true)
/// - `"0"`  => forced OFF (kill switch: `build_factor_occ` skips partner
///   tracking, so `find_next_factor` sees `tracks_partners() == false`
///   and takes the byte-identical generic occ scan)
/// - other  => forced ON
///
/// Cached in a `OnceLock` (mirrors the `AY_AB_*` flag convention) so the hot
/// factor path never pays an env syscall.
#[inline]
pub(crate) fn factor_bin_fastpath_enabled() -> bool {
    use std::sync::OnceLock;
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(
        || match std::env::var("AY_AB_FACTOR_BIN_FASTPATH").ok().as_deref() {
            None => FACTOR_BIN_FASTPATH_DEFAULT_ON,
            Some("0") => false,
            Some(_) => true,
        },
    )
}

/// Tick charge for scanning a factor occurrence list of `n` elements.
///
/// - OFF: `n` — one tick per element (the pre-change accounting). Because every
///   factor occurrence scan visits its whole list (no early `break`), charging
///   `n` in bulk is byte-identical to the former per-element `*ticks += 1`.
/// - ON:  `ceil(n / 8)` — one tick per 64-byte cache line, mirroring
///   `kissat_cache_lines`. This is PURE tick counting (a budget heuristic); it
///   does not touch candidate scoring, extension-var application,
///   reconstruction, or proof emission.
#[inline]
pub(super) fn factor_scan_ticks(n: usize) -> u64 {
    if factor_cacheline_ticks_enabled() {
        (n as u64).div_ceil(FACTOR_OCC_ELEMS_PER_CACHE_LINE)
    } else {
        n as u64
    }
}

/// Solver-local dry-run payload for one LRAT factor extension application.
///
/// This mirrors the checker-facing `FactorExtensionLratDryRun` shape without
/// introducing a `ay-sat -> ay-proof-complexity` dependency. It also retains
/// the signed checker-visible transaction fields derived from the dry-run so a
/// mismatch rejects before any factor mutation.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Deserialize, serde::Serialize))]
pub(crate) struct FactorLratDryRunSidecar {
    pub fresh_lit: i64,
    pub factors: Vec<i64>,
    pub quotient_clauses: Vec<Vec<i64>>,
    pub source_clause_ids_quotient_major: Vec<u64>,
    pub source_clause_lits_quotient_major: Vec<Vec<i64>>,
    pub planned_add_ids: Vec<u64>,
    pub source_delete_ids_quotient_major: Vec<u64>,
    pub divider_clause_ids: Vec<u64>,
    pub divider_rat_pivots: Vec<i64>,
    pub blocked_clause_id: u64,
    pub blocked_signed_lrat_hints: Vec<i64>,
    pub quotient_clause_ids: Vec<u64>,
    pub quotient_lrat_hints: Vec<Vec<u64>>,
    pub proof_only_delete_id: u64,
    pub source_delete_ids: Vec<u64>,
}

impl FactorLratDryRunSidecar {
    pub(crate) fn from_transaction_parts(
        fresh_lit: i64,
        factors: Vec<i64>,
        quotient_clauses: Vec<Vec<i64>>,
        source_clause_ids_quotient_major: Vec<u64>,
        source_clause_lits_quotient_major: Vec<Vec<i64>>,
        planned_add_ids: Vec<u64>,
        source_delete_ids_quotient_major: Vec<u64>,
    ) -> Option<Self> {
        let factor_count = factors.len();
        let quotient_count = quotient_clauses.len();
        let expected_adds = factor_count.checked_add(1)?.checked_add(quotient_count)?;
        if planned_add_ids.len() != expected_adds {
            return None;
        }
        let source_count = factor_count.checked_mul(quotient_count)?;
        if source_clause_ids_quotient_major.len() != source_count
            || source_clause_lits_quotient_major.len() != source_count
            || source_delete_ids_quotient_major.len() != source_count
        {
            return None;
        }

        let divider_clause_ids = planned_add_ids[..factor_count].to_vec();
        let blocked_clause_id = planned_add_ids[factor_count];
        let quotient_clause_ids = planned_add_ids[factor_count + 1..].to_vec();
        let blocked_signed_lrat_hints = negative_lrat_hints_for_ids(&divider_clause_ids)?;
        let quotient_lrat_hints = quotient_lrat_hints_from_source_ids(
            &source_clause_ids_quotient_major,
            factor_count,
            blocked_clause_id,
        )?;

        let sidecar = Self {
            fresh_lit,
            factors,
            quotient_clauses,
            source_clause_ids_quotient_major,
            source_clause_lits_quotient_major,
            planned_add_ids,
            source_delete_ids_quotient_major: source_delete_ids_quotient_major.clone(),
            divider_clause_ids,
            divider_rat_pivots: vec![fresh_lit; factor_count],
            blocked_clause_id,
            blocked_signed_lrat_hints,
            quotient_clause_ids,
            quotient_lrat_hints,
            proof_only_delete_id: blocked_clause_id,
            source_delete_ids: source_delete_ids_quotient_major,
        };

        sidecar
            .has_checker_visible_transaction_contract()
            .then_some(sidecar)
    }

    pub(crate) fn quotient_tails(&self) -> Option<Vec<Vec<i64>>> {
        let fresh_neg = self.fresh_lit.checked_neg()?;
        let mut tails = Vec::with_capacity(self.quotient_clauses.len());
        for quotient in &self.quotient_clauses {
            if quotient.first().copied() != Some(fresh_neg) {
                return None;
            }
            tails.push(quotient[1..].to_vec());
        }
        Some(tails)
    }

    pub(crate) fn has_checker_visible_transaction_contract(&self) -> bool {
        let Some(fresh_var) = dimacs_var(self.fresh_lit) else {
            return false;
        };
        if self.fresh_lit <= 0 || self.factors.len() < MIN_FACTOR_MATCHES {
            return false;
        }
        if self.quotient_clauses.is_empty() || !clause_well_formed_dimacs(&self.factors) {
            return false;
        }
        let Some(quotient_tails) = self.quotient_tails() else {
            return false;
        };
        let factor_count = self.factors.len();
        let quotient_count = quotient_tails.len();
        let expected_adds = match factor_count
            .checked_add(1)
            .and_then(|count| count.checked_add(quotient_count))
        {
            Some(count) => count,
            None => return false,
        };
        let source_count = match factor_count.checked_mul(quotient_count) {
            Some(count) => count,
            None => return false,
        };

        if self.planned_add_ids.len() != expected_adds
            || self.source_clause_ids_quotient_major.len() != source_count
            || self.source_clause_lits_quotient_major.len() != source_count
            || self.source_delete_ids_quotient_major.len() != source_count
            || self.source_delete_ids != self.source_clause_ids_quotient_major
            || self.source_delete_ids_quotient_major != self.source_clause_ids_quotient_major
        {
            return false;
        }
        if self.divider_clause_ids != self.planned_add_ids[..factor_count]
            || self.blocked_clause_id != self.planned_add_ids[factor_count]
            || self.quotient_clause_ids != self.planned_add_ids[factor_count + 1..]
            || self.divider_rat_pivots != vec![self.fresh_lit; factor_count]
            || self.proof_only_delete_id != self.blocked_clause_id
            || !negative_hints_match_ids(&self.blocked_signed_lrat_hints, &self.divider_clause_ids)
        {
            return false;
        }
        if self.quotient_lrat_hints.len() != quotient_count {
            return false;
        }

        if !all_nonzero(&self.source_clause_ids_quotient_major)
            || !all_nonzero(&self.planned_add_ids)
            || !all_unique_u64(&self.source_clause_ids_quotient_major)
            || !all_unique_u64(&self.planned_add_ids)
        {
            return false;
        }
        let mut all_ids = self.source_clause_ids_quotient_major.clone();
        all_ids.extend_from_slice(&self.planned_add_ids);
        if !all_unique_u64(&all_ids) {
            return false;
        }

        for tail in &quotient_tails {
            if tail.is_empty()
                || !clause_well_formed_dimacs(tail)
                || tail
                    .iter()
                    .any(|&lit| dimacs_var(lit) == Some(fresh_var) || self.factors.contains(&lit))
            {
                return false;
            }
        }

        for (quotient_idx, tail) in quotient_tails.iter().enumerate() {
            let source_start = quotient_idx * factor_count;
            let source_end = source_start + factor_count;
            let mut expected_hints =
                self.source_clause_ids_quotient_major[source_start..source_end].to_vec();
            expected_hints.push(self.blocked_clause_id);
            if self.quotient_lrat_hints[quotient_idx] != expected_hints {
                return false;
            }

            for (factor_idx, &factor) in self.factors.iter().enumerate() {
                let source_lits =
                    &self.source_clause_lits_quotient_major[source_start + factor_idx];
                let mut expected_lits = Vec::with_capacity(tail.len() + 1);
                expected_lits.push(factor);
                expected_lits.extend_from_slice(tail);
                if !same_clause_dimacs(source_lits, &expected_lits) {
                    return false;
                }
            }
        }

        true
    }
}

fn dimacs_var(lit: i64) -> Option<u64> {
    if lit == 0 {
        None
    } else {
        Some(lit.unsigned_abs())
    }
}

fn all_nonzero(ids: &[u64]) -> bool {
    ids.iter().all(|&id| id != 0)
}

fn all_unique_u64(ids: &[u64]) -> bool {
    let mut sorted = ids.to_vec();
    sorted.sort_unstable();
    sorted.dedup();
    sorted.len() == ids.len()
}

fn clause_well_formed_dimacs(lits: &[i64]) -> bool {
    if lits.is_empty() || lits.contains(&0) {
        return false;
    }
    for (idx, &lit) in lits.iter().enumerate() {
        for &prev in &lits[..idx] {
            if prev == lit || prev == -lit {
                return false;
            }
        }
    }
    true
}

fn same_clause_dimacs(left: &[i64], right: &[i64]) -> bool {
    if left.len() != right.len() {
        return false;
    }
    let mut left = left.to_vec();
    let mut right = right.to_vec();
    left.sort_unstable();
    right.sort_unstable();
    left == right
}

fn negative_lrat_hints_for_ids(ids: &[u64]) -> Option<Vec<i64>> {
    let mut hints = Vec::with_capacity(ids.len());
    for &id in ids {
        hints.push(i64::try_from(id).ok()?.checked_neg()?);
    }
    Some(hints)
}

fn negative_hints_match_ids(hints: &[i64], ids: &[u64]) -> bool {
    if hints.len() != ids.len() {
        return false;
    }
    hints
        .iter()
        .zip(ids)
        .all(|(&hint, &id)| i64::try_from(id).is_ok() && hint.checked_neg() == Some(id as i64))
}

fn quotient_lrat_hints_from_source_ids(
    source_ids_quotient_major: &[u64],
    factor_count: usize,
    blocked_clause_id: u64,
) -> Option<Vec<Vec<u64>>> {
    if factor_count == 0 || !source_ids_quotient_major.len().is_multiple_of(factor_count) {
        return None;
    }
    let mut hints = Vec::with_capacity(source_ids_quotient_major.len() / factor_count);
    for row in source_ids_quotient_major.chunks(factor_count) {
        let mut row_hints = row.to_vec();
        row_hints.push(blocked_clause_id);
        hints.push(row_hints);
    }
    Some(hints)
}

/// Metadata needed to persist a dry-run sidecar in the checker-facing artifact
/// shape used by `ay-proof-complexity`.
#[cfg(test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct FactorLratDryRunExport<'a> {
    /// Source CNF path or URI immediately before the planned transaction.
    pub source_dimacs_uri: &'a str,
    /// LRAT proof path or URI that contains the planned transaction replay.
    pub lrat_proof_uri: &'a str,
    /// JSON sidecar path or URI for the planned transaction payload.
    pub transform_transaction_uri: &'a str,
    /// Benchmark or fixture identifier.
    pub benchmark_id: &'a str,
    /// Formula family tag.
    pub family: &'a str,
    /// Source CNF variable count before the fresh extension literal.
    pub num_vars: u64,
    /// Source CNF clause count before the planned transaction.
    pub num_clauses: u64,
    /// Producer revision or binary fingerprint.
    pub producer_revision: Option<&'a str>,
}

#[cfg(test)]
impl FactorLratDryRunSidecar {
    /// Export this retained preflight sidecar as a JSON value matching
    /// `FactorExtensionLratDryRun`.
    pub(crate) fn to_factor_extension_lrat_dry_run_json(
        &self,
        export: &FactorLratDryRunExport<'_>,
    ) -> serde_json::Value {
        serde_json::json!({
            "source_dimacs_uri": export.source_dimacs_uri,
            "lrat_proof_uri": export.lrat_proof_uri,
            "transform_transaction_uri": export.transform_transaction_uri,
            "benchmark_id": export.benchmark_id,
            "family": export.family,
            "num_vars": export.num_vars,
            "num_clauses": export.num_clauses,
            "fresh_lit": self.fresh_lit,
            "factors": self.factors,
            "quotient_clauses": self.quotient_clauses,
            "source_clause_ids_quotient_major": self.source_clause_ids_quotient_major,
            "source_clause_lits_quotient_major": self.source_clause_lits_quotient_major,
            "planned_add_ids": self.planned_add_ids,
            "source_delete_ids_quotient_major": self.source_delete_ids_quotient_major,
            "producer_revision": export.producer_revision,
        })
    }

    /// Export this retained preflight sidecar as a JSON value matching the
    /// checker-visible `FactorExtensionLratTransaction` shape.
    pub(crate) fn to_factor_extension_lrat_transaction_json(
        &self,
        export: &FactorLratDryRunExport<'_>,
    ) -> Option<serde_json::Value> {
        if !self.has_checker_visible_transaction_contract() {
            return None;
        }
        Some(serde_json::json!({
            "source_dimacs_uri": export.source_dimacs_uri,
            "lrat_proof_uri": export.lrat_proof_uri,
            "transform_transaction_uri": export.transform_transaction_uri,
            "benchmark_id": export.benchmark_id,
            "family": export.family,
            "num_vars": export.num_vars,
            "num_clauses": export.num_clauses,
            "fresh_lit": self.fresh_lit,
            "factors": self.factors,
            "quotient_tails": self.quotient_tails()?,
            "source_clause_ids_quotient_major": self.source_clause_ids_quotient_major,
            "source_clause_lits_quotient_major": self.source_clause_lits_quotient_major,
            "divider_clause_ids": self.divider_clause_ids,
            "divider_rat_pivots": self.divider_rat_pivots,
            "blocked_clause_id": self.blocked_clause_id,
            "blocked_signed_lrat_hints": self.blocked_signed_lrat_hints,
            "quotient_clause_ids": self.quotient_clause_ids,
            "quotient_lrat_hints": self.quotient_lrat_hints,
            "proof_only_delete_id": self.proof_only_delete_id,
            "source_delete_ids": self.source_delete_ids,
            "producer_revision": export.producer_revision,
        }))
    }
}

/// LRAT factor preflight counters that are independent of applied factor stats.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) struct FactorLratPreflightStats {
    pub transaction_candidates: u64,
    pub dry_run_emitted: u64,
    pub dry_run_rejected: u64,
    pub checker_obligation_missing: u64,
    pub er_obligation_missing: u64,
}

/// One factorization application with full proof structure.
///
/// Each application introduces one extension variable and rewrites a
/// `factors × quotients` clause matrix into `factors + quotients` clauses.
/// The `blocked_clause` is a proof-only artifact needed for DRAT checking
/// (see CaDiCaL `factor.cpp:606-623`).
#[derive(Debug, Clone)]
pub(crate) struct FactorApplication {
    /// The fresh extension variable introduced.
    pub fresh_var: Variable,
    /// Factor literals that were compressed.
    pub factors: Vec<Literal>,
    /// Binary divider clauses: `(fresh ∨ f_j)` for each factor.
    pub divider_clauses: Vec<Vec<Literal>>,
    /// Quotient clauses: `(¬fresh ∨ Q_i)` for each quotient.
    pub quotient_clauses: Vec<Vec<Literal>>,
    /// Proof-only blocked clause: `(¬fresh ∨ ¬f_1 ∨ ¬f_2 ∨ ...)`.
    /// RAT on `¬fresh`. Never added to the clause database.
    pub blocked_clause: Vec<Literal>,
    /// All original clause indices to delete.
    pub to_delete: Vec<usize>,
}

/// Self-subsuming factor application: no extension variable needed.
///
/// When two factors in the quotient chain are complementary (f and ~f),
/// resolving their respective clauses directly produces shorter resolvents
/// (quotient literals only, with the factor literal removed entirely).
///
/// Reference: CaDiCaL `factor.cpp:506-591`.
#[derive(Debug, Clone)]
pub(crate) struct SelfSubsumingApplication {
    /// Resolvent clauses: quotient literals only (factor removed).
    pub resolvents: Vec<Vec<Literal>>,
    /// Original clause indices to delete.
    pub to_delete: Vec<usize>,
    /// Pairs (ci_a, ci_b) of clause indices that produced each resolvent.
    pub proof_pairs: Vec<(usize, usize)>,
}

/// Result of one factorization pass.
#[derive(Debug, Default)]
pub(crate) struct FactorResult {
    /// New clauses to add: each is a list of literals.
    pub new_clauses: Vec<Vec<Literal>>,
    /// Clause indices to delete from clause_db.
    pub to_delete: Vec<usize>,
    /// Number of extension variables introduced.
    pub extension_vars_needed: usize,
    /// Number of factoring applications.
    pub factored_count: usize,
    /// Per-application structured data for proof emission.
    pub applications: Vec<FactorApplication>,
    /// Self-subsuming applications (complementary factor pairs).
    pub self_subsuming: Vec<SelfSubsumingApplication>,
    /// Factor candidates consumed from the schedule in this run.
    pub consumed_candidates: Vec<Literal>,
    /// Whether the candidate schedule was fully processed.
    pub completed: bool,
    /// Ticks consumed during this run (for effort budget tracking).
    pub ticks_consumed: u64,
}

/// Control parameters for a factorization run.
pub(crate) struct FactorConfig {
    /// The next variable index for extension variables.
    pub next_var_id: usize,
    /// Effort limit in ticks for this run.
    pub effort_limit: u64,
    /// Current BVE elimination bound (CaDiCaL factor.cpp:118,888).
    /// Factoring only fires when clause reduction exceeds this bound.
    pub elim_bound: i64,
}

/// Factorization engine.
///
/// Ported from CaDiCaL `factor.cpp`. The algorithm:
/// 1. Schedule candidate literals by occurrence count.
/// 2. For each candidate `first`, build a quotient chain:
///    - Level 0: all clauses containing `first` (these share factor `first`)
///    - Level k: intersect with clauses containing factor `next_k`
/// 3. Find the best depth where `factors * quotients - factors - quotients > 0`.
/// 4. Apply factoring: create extension variable, add divider + quotient clauses.
#[derive(Debug, Clone)]
pub(crate) struct Factor {
    num_vars: usize,
    /// Per-literal marks for factor/quotient identification.
    marks: Vec<u8>,
    /// Reusable counts buffer for `find_next_factor` (avoids per-call allocation).
    counts: Vec<u32>,
    /// Persistent buffer for binary literal counts in `build_factor_occ`
    /// (eliminates per-round `vec![0u32; num_vars*2]` allocation, #8543).
    pub(crate) occ_binary_counts: Vec<u32>,
    /// Persistent buffer for large-clause literal counts in `build_factor_occ`
    /// (eliminates per-round `vec![0u32; num_vars*2]` allocation, #8543).
    pub(crate) occ_large_counts: Vec<u32>,
    /// Persistent buffer for `next_large_counts` swap in the candidate filter
    /// loop (eliminates per-iteration `vec![0u32; num_vars*2]` allocation, #8543).
    pub(crate) occ_next_large_counts: Vec<u32>,
    /// Persistent buffer for candidate clause indices in `build_factor_occ`
    /// (eliminates per-round `Vec::new()` allocation, #8543).
    pub(crate) occ_candidates: Vec<usize>,
    /// Pooled scratch: candidate literals counted in `find_next_factor` (#rank5).
    counted: Vec<Literal>,
    /// Pooled scratch: NOUNTED-marked literals for the current source clause (#rank5).
    nounted: Vec<Literal>,
    /// Pooled scratch: `(candidate, source position, partner clause)` triples
    /// recorded by the single-pass `find_next_factor` scan (#rank6).
    cand_matches: Vec<(Literal, u32, u32)>,
    /// Pooled scratch: eligible clause indices for the current first-factor
    /// candidate (#rank5 — recycled through quotient-chain level 0).
    eligible_buf: Vec<usize>,
    /// Pooled scratch: per-clause dedup marks for matrix extraction (#rank5 —
    /// replaces the O(n^2) `to_delete_set.contains` scan).
    delete_marks: Vec<bool>,
    /// Pooled tombstone buffer for `step` (all-false between steps).
    step_deleted: Vec<bool>,
    /// Incremental candidate schedule (#rank6): max-heap of
    /// `(occurrence count, literal)`, kissat/CaDiCaL-style priority queue.
    /// Ties on occurrence count pop in DESCENDING literal order, matching
    /// CaDiCaL's `factor_occs_size` comparator (factor.hpp:9-17: bigger occ
    /// list first, then `a > b` on the literal index). Scores are validated
    /// lazily at pop time against the LIVE occ count (see `step`), so pop
    /// order tracks current occurrence-list sizes exactly like the
    /// kissat/CaDiCaL heaps, whose comparators read live `occs(lit).size()`.
    schedule: std::collections::BinaryHeap<(usize, Literal)>,
    /// Whether a literal currently has a live entry in `schedule`. Exactly
    /// one live entry per flagged literal: pushes are gated on the flag and
    /// pops clear it, so the heap never accumulates stale duplicates.
    in_schedule: Vec<bool>,
    /// Last solver-side LRAT factor dry-run payloads built before fail-closed
    /// rejection. These are sidecars only and never authorize mutation.
    lrat_dry_run_sidecars: Vec<FactorLratDryRunSidecar>,
    /// Fail-closed LRAT factor preflight counters.
    lrat_preflight_stats: FactorLratPreflightStats,
}

const MARK_FACTOR: u8 = 1;
const MARK_QUOTIENT: u8 = 2;
/// Candidate already counted for the current source clause scan in
/// `find_next_factor` (CaDiCaL's NOUNTED mark).
const MARK_NOUNTED: u8 = 4;

impl Factor {
    pub(crate) fn new(num_vars: usize) -> Self {
        Self {
            num_vars,
            marks: vec![0; num_vars * 2],
            counts: vec![0; num_vars * 2],
            occ_binary_counts: vec![0; num_vars * 2],
            occ_large_counts: vec![0; num_vars * 2],
            occ_next_large_counts: vec![0; num_vars * 2],
            occ_candidates: Vec::new(),
            counted: Vec::new(),
            nounted: Vec::new(),
            cand_matches: Vec::new(),
            eligible_buf: Vec::new(),
            delete_marks: Vec::new(),
            step_deleted: Vec::new(),
            schedule: std::collections::BinaryHeap::new(),
            in_schedule: Vec::new(),
            lrat_dry_run_sidecars: Vec::new(),
            lrat_preflight_stats: FactorLratPreflightStats::default(),
        }
    }

    pub(crate) fn clear_lrat_dry_run_sidecars(&mut self) {
        self.lrat_dry_run_sidecars.clear();
    }

    pub(crate) fn set_lrat_dry_run_sidecars(&mut self, sidecars: Vec<FactorLratDryRunSidecar>) {
        self.lrat_preflight_stats.dry_run_emitted = self
            .lrat_preflight_stats
            .dry_run_emitted
            .saturating_add(sidecars.len() as u64);
        self.lrat_dry_run_sidecars = sidecars;
    }

    pub(crate) fn record_lrat_preflight_transaction_candidates(&mut self, count: u64) {
        self.lrat_preflight_stats.transaction_candidates = self
            .lrat_preflight_stats
            .transaction_candidates
            .saturating_add(count);
    }

    pub(crate) fn record_lrat_preflight_dry_run_rejected(&mut self) {
        self.lrat_preflight_stats.dry_run_rejected =
            self.lrat_preflight_stats.dry_run_rejected.saturating_add(1);
    }

    pub(crate) fn record_lrat_preflight_checker_obligation_missing(&mut self) {
        self.lrat_preflight_stats.checker_obligation_missing = self
            .lrat_preflight_stats
            .checker_obligation_missing
            .saturating_add(1);
    }

    pub(crate) fn record_lrat_preflight_er_obligation_missing(&mut self) {
        self.lrat_preflight_stats.er_obligation_missing = self
            .lrat_preflight_stats
            .er_obligation_missing
            .saturating_add(1);
    }

    pub(crate) fn lrat_dry_run_sidecars(&self) -> &[FactorLratDryRunSidecar] {
        &self.lrat_dry_run_sidecars
    }

    pub(crate) fn lrat_preflight_stats(&self) -> FactorLratPreflightStats {
        self.lrat_preflight_stats
    }

    pub(crate) fn ensure_num_vars(&mut self, num_vars: usize) {
        if num_vars > self.num_vars {
            self.num_vars = num_vars;
            self.marks.resize(num_vars * 2, 0);
            self.counts.resize(num_vars * 2, 0);
            self.occ_binary_counts.resize(num_vars * 2, 0);
            self.occ_large_counts.resize(num_vars * 2, 0);
            self.occ_next_large_counts.resize(num_vars * 2, 0);
        }
    }

    fn mark(&mut self, lit: Literal, flag: u8) {
        let idx = lit.index();
        if idx < self.marks.len() {
            self.marks[idx] |= flag;
        }
    }

    fn unmark(&mut self, lit: Literal, flag: u8) {
        let idx = lit.index();
        if idx < self.marks.len() {
            self.marks[idx] &= !flag;
        }
    }

    fn is_marked(&self, lit: Literal, flag: u8) -> bool {
        let idx = lit.index();
        idx < self.marks.len() && (self.marks[idx] & flag) != 0
    }

    /// Check if a literal is satisfied under the current vals[] assignment.
    /// vals[lit.index()] > 0 means the literal is true.
    #[inline]
    fn lit_satisfied(lit: Literal, vals: &[i8]) -> bool {
        let idx = lit.index();
        idx < vals.len() && vals[idx] > 0
    }

    #[inline]
    fn clause_satisfied(lits: &[Literal], vals: &[i8]) -> bool {
        lits.iter().any(|&lit| Self::lit_satisfied(lit, vals))
    }

    /// Run batch factorization on the clause database (single full pass over
    /// all candidates, no application between factorings).
    ///
    /// The production driver uses the incremental `schedule_candidates` /
    /// `step` / `reschedule_literal` API instead (#rank6); this batch entry
    /// point is kept for the read-only census tests and unit tests, which
    /// measure discovery without mutating a solver.
    ///
    /// `occ`: pre-built occurrence list for irredundant clauses.
    /// `vals`: literal-indexed i8 array (vals[var*2]==0 means unassigned).
    /// `var_states`: per-variable state (active, eliminated, etc.).
    /// `config`: control parameters (next_var_id, effort_limit, elim_bound).
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn run(
        &mut self,
        clause_db: &ClauseArena,
        occ: &OccList,
        vals: &[i8],
        var_states: &[crate::solver::lifecycle::VarState],
        config: &FactorConfig,
    ) -> FactorResult {
        // CaDiCaL factor.cpp:960: vals must cover all variables (2 entries per var)
        debug_assert!(
            vals.len() >= self.num_vars * 2,
            "BUG: factor vals.len()={} < num_vars*2={}",
            vals.len(),
            self.num_vars * 2,
        );
        // CaDiCaL factor.cpp: var_states mask must cover all variables
        debug_assert!(
            var_states.len() >= self.num_vars,
            "BUG: factor var_states.len()={} < num_vars={}",
            var_states.len(),
            self.num_vars,
        );
        let mut result = FactorResult {
            completed: true,
            ..FactorResult::default()
        };
        let mut ticks: u64 = 0;
        let mut next_var = config.next_var_id;

        // Build candidate schedule: literals sorted by occurrence count (descending).
        let mut candidates: Vec<(Literal, usize)> = Vec::new();
        for var_idx in 0..self.num_vars {
            if var_idx * 2 < vals.len() && vals[var_idx * 2] != 0 {
                continue;
            }
            if var_idx < var_states.len() && var_states[var_idx].is_removed() {
                continue;
            }
            for positive in [true, false] {
                let lit = if positive {
                    Literal::positive(Variable(var_idx as u32))
                } else {
                    Literal::negative(Variable(var_idx as u32))
                };
                let count = occ.count(lit);
                if count >= MIN_FACTOR_MATCHES {
                    candidates.push((lit, count));
                }
            }
        }
        // Sort by occurrence count descending (CaDiCaL uses a priority queue).
        candidates.sort_by_key(|b| std::cmp::Reverse(b.1));

        // Already-deleted clauses tracked to avoid double-deletion.
        let mut deleted: Vec<bool> = vec![false; clause_db.len()];

        for &(first_lit, _) in &candidates {
            if ticks > config.effort_limit {
                result.completed = false;
                break;
            }
            result.consumed_candidates.push(first_lit);
            if self.is_marked(first_lit, MARK_FACTOR) {
                continue; // Already used as a factor in a previous application.
            }

            match self.try_candidate(
                clause_db,
                occ,
                vals,
                first_lit,
                &mut deleted,
                &mut ticks,
                config.effort_limit,
                config.elim_bound,
                next_var,
            ) {
                Some(CandidateOutcome::Application(app)) => {
                    next_var += 1;
                    result.extension_vars_needed += 1;
                    Self::flatten_application(&mut result, app);
                }
                Some(CandidateOutcome::SelfSubsuming(app)) => {
                    Self::flatten_self_subsuming(&mut result, app);
                }
                None => {}
            }
        }

        result.ticks_consumed = ticks;

        // Validate structured application data against flattened result.
        assert_eq!(
            result.applications.len() + result.self_subsuming.len(),
            result.factored_count
        );
        for app in &result.applications {
            assert_eq!(app.blocked_clause.len(), 1 + app.factors.len());
            assert_eq!(app.divider_clauses.len(), app.factors.len());
            assert!(app.fresh_var.index() < next_var);
            assert_eq!(
                app.to_delete.len(),
                app.factors.len() * app.quotient_clauses.len()
            );
        }

        result
    }

    /// Flatten one extension-variable application into a `FactorResult`.
    fn flatten_application(result: &mut FactorResult, app: FactorApplication) {
        for divider in &app.divider_clauses {
            result.new_clauses.push(divider.clone());
        }
        for quotient in &app.quotient_clauses {
            result.new_clauses.push(quotient.clone());
        }
        result.to_delete.extend_from_slice(&app.to_delete);
        result.applications.push(app);
        result.factored_count += 1;
    }

    /// Flatten one self-subsuming application into a `FactorResult`.
    fn flatten_self_subsuming(result: &mut FactorResult, app: SelfSubsumingApplication) {
        for resolvent in &app.resolvents {
            result.new_clauses.push(resolvent.clone());
        }
        result.to_delete.extend_from_slice(&app.to_delete);
        result.self_subsuming.push(app);
        result.factored_count += 1;
    }

    /// Try to factor one first-factor candidate literal.
    ///
    /// Builds the quotient chain, picks the best depth, extracts the complete
    /// `factors × quotients` matrix and returns the structured application.
    /// Marks accepted deletions in `deleted` (the caller owns unwinding).
    /// Returns `None` when the candidate is unproductive.
    #[allow(clippy::too_many_arguments)]
    fn try_candidate(
        &mut self,
        clause_db: &ClauseArena,
        occ: &OccList,
        vals: &[i8],
        first_lit: Literal,
        deleted: &mut [bool],
        ticks: &mut u64,
        effort_limit: u64,
        elim_bound: i64,
        next_var: usize,
    ) -> Option<CandidateOutcome> {
        // Collect eligible clauses containing first_lit (pooled buffer, #rank5).
        let mut eligible = std::mem::take(&mut self.eligible_buf);
        eligible.clear();
        // Cache-line-granular scan charge (kissat parity, factor.c first_factor):
        // the whole occ list is touched, so charge once for its cache lines.
        // AY_AB_FACTOR_CACHELINE_TICKS=0 restores the per-element charge.
        let first_occ = occ.get(first_lit);
        *ticks += factor_scan_ticks(first_occ.len());
        for &ci in first_occ {
            if deleted[ci] {
                continue;
            }
            if clause_db.is_empty_clause(ci) || clause_db.is_learned(ci) {
                continue;
            }
            if Self::clause_satisfied(clause_db.literals(ci), vals) {
                continue;
            }
            let len = clause_db.len_of(ci);
            if !(2..=FACTOR_SIZE_LIMIT).contains(&len) {
                continue;
            }
            eligible.push(ci);
        }
        if eligible.len() < MIN_FACTOR_MATCHES {
            self.eligible_buf = eligible;
            return None;
        }

        // Build quotient chain (CaDiCaL: first_factor + next_factor loop).
        // Level 0 takes ownership of the pooled buffer; it is recycled below.
        let mut chain = self.build_quotient_chain(
            clause_db,
            occ,
            vals,
            first_lit,
            eligible,
            deleted,
            ticks,
            effort_limit,
        );

        let outcome = self.extract_factoring(
            clause_db, occ, vals, &mut chain, deleted, elim_bound, next_var,
        );

        // Recycle the level-0 buffer back into the pool.
        if let Some(level0) = chain.first_mut() {
            let mut buf = std::mem::take(&mut level0.clause_indices);
            buf.clear();
            self.eligible_buf = buf;
        }

        outcome
    }

    /// Pick the best quotient depth from a built chain and extract the
    /// complete factoring matrix (or a self-subsuming resolution).
    #[allow(clippy::too_many_arguments)]
    fn extract_factoring(
        &mut self,
        clause_db: &ClauseArena,
        occ: &OccList,
        vals: &[i8],
        chain: &mut [QuotientLevel],
        deleted: &mut [bool],
        elim_bound: i64,
        next_var: usize,
    ) -> Option<CandidateOutcome> {
        if chain.is_empty() {
            return None;
        }

        // Find best quotient level for factoring.
        let (best_idx, reduction) = find_best_quotient(chain)?;

        // CaDiCaL factor.cpp:888: only factor when clause reduction
        // exceeds the current BVE elimination bound. This creates a
        // dual guard: factoring requires `F*Q - F - Q > elimbound`,
        // while BVE rejects elimination when `F*Q > F + Q + elimbound`.
        // These are the same condition, so BVE can never profitably
        // undo a factoring that passed this guard.
        if reduction <= elim_bound {
            return None;
        }
        // Flush unmatched clauses so all levels have identical entry counts.
        // CaDiCaL: apply_factoring calls flush for each level (factor.cpp:711-712).
        for level in (1..=best_idx).rev() {
            flush_unmatched_clauses(chain, level);
        }

        // Apply factoring: create extension variable and rewrite clauses.
        let factors: Vec<Literal> = chain[..=best_idx].iter().map(|q| q.factor).collect();
        let num_quotients = chain[best_idx].clause_indices.len();

        // Self-subsuming check: if two factors are complementary (f, ~f),
        // resolve directly without creating an extension variable.
        // Reference: CaDiCaL factor.cpp:506-591.
        if let Some((comp_a, comp_b)) = find_complementary_factors(&factors) {
            let f_a = factors[comp_a];
            let mut app = SelfSubsumingApplication {
                resolvents: Vec::new(),
                to_delete: Vec::new(),
                proof_pairs: Vec::new(),
            };
            // Build resolvents: clause_a minus its factor literal.
            for i in 0..num_quotients {
                let ci_a = chain[comp_a].clause_indices[i];
                let ci_b = chain[comp_b].clause_indices[i];
                if deleted[ci_a] || deleted[ci_b] {
                    continue;
                }
                let lits = clause_db.literals(ci_a);
                let resolvent: Vec<Literal> = lits.iter().filter(|&&l| l != f_a).copied().collect();
                app.resolvents.push(resolvent);
                app.proof_pairs.push((ci_a, ci_b));
            }
            // Delete ALL original clauses across ALL factor levels.
            for level in &chain[..=best_idx] {
                for &ci in &level.clause_indices[..num_quotients] {
                    if !deleted[ci] {
                        deleted[ci] = true;
                        app.to_delete.push(ci);
                    }
                }
            }
            return Some(CandidateOutcome::SelfSubsuming(app));
        }

        let quotient_clauses: &[usize] = &chain[best_idx].clause_indices;

        // Exact matrix extraction (#factor-quality): after flushing, level
        // l's clause_indices[j] IS the matrix cell `(Q_j ∨ f_l)` — the chain
        // already carries the complete factors × quotients matrix (kissat
        // factor.c `qlauses`/`matches`, CaDiCaL factor.cpp:711-717
        // `apply_factoring` walks the quotient chain directly). The former
        // occ-list re-scan re-found each cell by literal matching and
        // rejected the WHOLE candidate whenever any cell was not re-found
        // (`to_delete_set.len() != expected_delete`), silently dropping
        // profitable factorings — a pure discovery-quality loss, since the
        // chain construction already proved every cell exists.
        //
        // Order is quotient-major, factor-minor — the checker-visible
        // sidecar contract order (`source_clause_ids_quotient_major`).
        //
        // delete_marks is the pooled per-clause bitmap. A duplicate arena
        // index across cells is REAL, not just a duplicate-clause artifact:
        // factor marks are incremental during chain construction, so a
        // level-l partner may carry a FUTURE factor f_m (m > l) inside its
        // quotient — then the same physical clause (Q ∨ f_l) with f_m ∈ Q
        // also serves as the level-m cell of another column. On such
        // structures (e.g. SAT-COMP a2fe3213, pairwise-symmetric: EVERY
        // candidate collides) rejecting the candidate forfeits all
        // discovery — main found 417 factors there, a duplicate-rejecting
        // exact pass found 0 and flipped the instance from SAT ~37s to
        // timeout. Instead, fall back to the former occ-rescan matching
        // (below), which re-derives each column's quotient with factor
        // literals filtered out and therefore assembles a coherent
        // disjoint matrix when one exists.
        let expected_delete = factors.len() * quotient_clauses.len();
        let mut to_delete_set: Vec<usize> = Vec::with_capacity(expected_delete);
        let mut delete_marks = std::mem::take(&mut self.delete_marks);
        if delete_marks.len() < clause_db.len() {
            delete_marks.resize(clause_db.len(), false);
        }
        let mut duplicate_cell = false;
        'matrix: for j in 0..quotient_clauses.len() {
            for level in &chain[..=best_idx] {
                let ci = level.clause_indices[j];
                if deleted[ci] || delete_marks[ci] {
                    duplicate_cell = true;
                    break 'matrix;
                }
                delete_marks[ci] = true;
                to_delete_set.push(ci);
            }
        }

        // Clear the exact-pass marks (both paths below re-derive their own).
        for &ci in &to_delete_set {
            delete_marks[ci] = false;
        }

        if duplicate_cell {
            // Fallback: former occ-rescan extraction. Re-derive each
            // column's quotient from the best-level cell with factor
            // literals filtered OUT, then re-find each (quotient, factor)
            // cell by literal matching, deduplicated via delete_marks. This
            // matches the derived clause construction below (which also
            // filters factor literals out of quotients), so the deleted
            // matrix is exactly the one the new divider/quotient clauses
            // represent. Order stays quotient-major, factor-minor.
            to_delete_set.clear();

            // Mark all factor literals.
            for &f in &factors {
                self.mark(f, MARK_FACTOR);
            }

            for &qi in quotient_clauses {
                let lits = clause_db.literals(qi);
                let quotient: Vec<Literal> = lits
                    .iter()
                    .filter(|l| !self.is_marked(**l, MARK_FACTOR))
                    .copied()
                    .collect();

                // Mark quotient literals.
                for &ql in &quotient {
                    self.mark(ql, MARK_QUOTIENT);
                }

                // Search occ list of rarest quotient literal (same for
                // every factor).
                let rarest = quotient.iter().min_by_key(|&&l| occ.count(l)).copied();

                // For each factor, find a clause that is (factor ∨ quotient).
                for &f in &factors {
                    if let Some(r) = rarest {
                        for &ci in occ.get(r) {
                            if deleted[ci] || delete_marks[ci] {
                                continue;
                            }
                            if clause_db.is_empty_clause(ci) || clause_db.is_learned(ci) {
                                continue;
                            }
                            if Self::clause_satisfied(clause_db.literals(ci), vals) {
                                continue;
                            }
                            if clause_db.len_of(ci) != quotient.len() + 1 {
                                continue;
                            }
                            let c_lits = clause_db.literals(ci);
                            // Check: clause = quotient ∪ {f}.
                            let mut has_factor = false;
                            let mut all_quotient = true;
                            for &lit in c_lits {
                                if lit == f {
                                    has_factor = true;
                                } else if !self.is_marked(lit, MARK_QUOTIENT) {
                                    all_quotient = false;
                                    break;
                                }
                            }
                            if has_factor && all_quotient {
                                delete_marks[ci] = true;
                                to_delete_set.push(ci);
                                break;
                            }
                        }
                    }
                }

                // Clear quotient marks.
                for &ql in &quotient {
                    self.unmark(ql, MARK_QUOTIENT);
                }
            }

            // Clear factor marks.
            for &f in &factors {
                self.unmark(f, MARK_FACTOR);
            }

            // Clear and restore the pooled delete_marks bitmap.
            for &ci in &to_delete_set {
                delete_marks[ci] = false;
            }
            self.delete_marks = delete_marks;

            // Require a complete factors × quotients matrix. A partial
            // rewrite can delete clauses that are not fully represented by
            // the new divider/quotient set, which breaks model soundness.
            if to_delete_set.len() != expected_delete {
                return None;
            }
        } else {
            self.delete_marks = delete_marks;
            debug_assert_eq!(to_delete_set.len(), expected_delete);
        }

        let fresh_var = Variable(next_var as u32);
        let fresh_pos = Literal::positive(fresh_var);
        let fresh_neg = Literal::negative(fresh_var);

        // Binary divider clauses: (fresh ∨ f_i) for each factor.
        let mut app_dividers = Vec::with_capacity(factors.len());
        for &factor in &factors {
            app_dividers.push(vec![fresh_pos, factor]);
        }

        // Quotient clauses: (¬fresh ∨ Q_lits) for each quotient clause.
        let mut app_quotients = Vec::with_capacity(quotient_clauses.len());
        for &qi in quotient_clauses {
            let lits = clause_db.literals(qi);
            let mut q_clause = vec![fresh_neg];
            for &lit in lits {
                // Remove all factor literals from the quotient.
                if !factors.contains(&lit) {
                    q_clause.push(lit);
                }
            }
            app_quotients.push(q_clause);
        }

        // Proof-only blocked clause: (¬fresh ∨ ¬f_1 ∨ ¬f_2 ∨ ...).
        // RAT on ¬fresh. See CaDiCaL factor.cpp:606-623.
        let mut blocked = Vec::with_capacity(1 + factors.len());
        blocked.push(fresh_neg);
        for &f in &factors {
            blocked.push(f.negated());
        }

        let mut app_to_delete = Vec::with_capacity(to_delete_set.len());
        for &ci in &to_delete_set {
            if !deleted[ci] {
                deleted[ci] = true;
                app_to_delete.push(ci);
            }
        }

        Some(CandidateOutcome::Application(FactorApplication {
            fresh_var,
            factors,
            divider_clauses: app_dividers,
            quotient_clauses: app_quotients,
            blocked_clause: blocked,
            to_delete: app_to_delete,
        }))
    }

    /// Build the incremental candidate schedule (#rank6).
    ///
    /// kissat/CaDiCaL keep a max-heap of candidate literals scored by
    /// occurrence count (kissat `factor.c` schedule, CaDiCaL `factor.cpp`
    /// heap). `step` pops candidates from this schedule; after each applied
    /// factoring the driver updates the occurrence list incrementally and
    /// re-inserts only affected literals via `reschedule_literal`.
    pub(crate) fn schedule_candidates(
        &mut self,
        occ: &OccList,
        vals: &[i8],
        var_states: &[crate::solver::lifecycle::VarState],
    ) {
        self.schedule.clear();
        self.in_schedule.clear();
        self.in_schedule.resize(self.num_vars * 2, false);
        // `AY_FACTOR_PROBE=1`: report what the candidate schedule actually saw.
        // AY factors 0 variables where Kissat factors 545, and size limit,
        // scheduling, effort and the acceptance bound are all eliminated — so
        // the open question is whether this schedule is empty (occurrence list
        // build is the defect) or full (quotient construction is).
        let probe = std::env::var_os("AY_FACTOR_PROBE").is_some();
        let (mut max_count, mut nonzero) = (0usize, 0usize);
        for var_idx in 0..self.num_vars {
            if var_idx * 2 < vals.len() && vals[var_idx * 2] != 0 {
                continue;
            }
            if var_idx < var_states.len() && var_states[var_idx].is_removed() {
                continue;
            }
            for positive in [true, false] {
                let lit = if positive {
                    Literal::positive(Variable(var_idx as u32))
                } else {
                    Literal::negative(Variable(var_idx as u32))
                };
                let count = occ.count(lit);
                if probe && count > 0 {
                    max_count = max_count.max(count);
                    nonzero += 1;
                }
                if count >= MIN_FACTOR_MATCHES {
                    self.in_schedule[lit.index()] = true;
                    self.schedule.push((count, lit));
                }
            }
        }
        if probe {
            eprintln!(
                "c factor_probe num_vars={} scheduled={} lits_with_occ={} max_occ={}",
                self.num_vars,
                self.schedule.len(),
                nonzero,
                max_count
            );
        }
    }

    /// Re-insert a literal whose occurrence list changed (#rank6).
    ///
    /// Called by the driver after an applied factoring for every literal in
    /// the consumed and newly-added clauses. Re-scheduling already-processed
    /// literals is what lets the cascade exploit newly-created divider and
    /// quotient clauses (CaDiCaL factor.cpp:698-748 heap re-insertion).
    pub(crate) fn reschedule_literal(
        &mut self,
        lit: Literal,
        occ: &OccList,
        vals: &[i8],
        var_states: &[crate::solver::lifecycle::VarState],
    ) {
        let var_idx = lit.variable().index();
        if var_idx * 2 < vals.len() && vals[var_idx * 2] != 0 {
            return;
        }
        if var_idx < var_states.len() && var_states[var_idx].is_removed() {
            return;
        }
        let count = occ.count(lit);
        if count < MIN_FACTOR_MATCHES {
            return;
        }
        let idx = lit.index();
        if idx >= self.in_schedule.len() {
            self.in_schedule.resize(idx + 1, false);
        }
        // One live entry per literal: if the occ list changes again while
        // scheduled, the stale entry is re-scored lazily at pop time (`step`).
        if !self.in_schedule[idx] {
            self.in_schedule[idx] = true;
            self.schedule.push((count, lit));
        }
    }

    /// Incremental factoring step (#rank6): pop scheduled candidates until
    /// one factoring is found or the schedule/budget is exhausted.
    ///
    /// Returns a `FactorResult` with at most ONE application (or one
    /// self-subsuming resolution). `completed == true` means the schedule
    /// was fully drained without finding a factoring. The driver applies the
    /// result to the clause DB, updates the occurrence list incrementally,
    /// re-schedules affected literals, then calls `step` again — the
    /// kissat/CaDiCaL structure that replaces full occ rebuilds between
    /// passes.
    pub(crate) fn step(
        &mut self,
        clause_db: &ClauseArena,
        occ: &OccList,
        vals: &[i8],
        var_states: &[crate::solver::lifecycle::VarState],
        config: &FactorConfig,
    ) -> FactorResult {
        debug_assert!(
            vals.len() >= self.num_vars * 2,
            "BUG: factor vals.len()={} < num_vars*2={}",
            vals.len(),
            self.num_vars * 2,
        );
        let mut result = FactorResult::default();
        let mut ticks: u64 = 0;

        // Pooled tombstone buffer; all-false on entry, restored on exit.
        if self.step_deleted.len() < clause_db.len() {
            self.step_deleted.resize(clause_db.len(), false);
        }
        let mut deleted = std::mem::take(&mut self.step_deleted);

        loop {
            if ticks > config.effort_limit {
                break; // completed stays false: budget exhausted.
            }
            let Some((score, first_lit)) = self.schedule.pop() else {
                result.completed = true;
                break;
            };
            let fidx = first_lit.index();
            // Lazy live re-scoring (kissat/CaDiCaL parity): their heap
            // comparators read the CURRENT `occs(lit).size()` at compare
            // time, so pop order always tracks live occurrence counts. Our
            // entries freeze the score at push; when the popped score is
            // stale, re-queue with the live count instead of consuming the
            // candidate out of order (standard lazy decrease-key). The
            // one-live-entry-per-literal invariant holds: the re-push
            // replaces the entry just popped.
            let live_count = occ.count(first_lit);
            if live_count != score {
                ticks += 1; // honest accounting for the requeue visit
                if live_count >= MIN_FACTOR_MATCHES {
                    self.schedule.push((live_count, first_lit));
                } else if fidx < self.in_schedule.len() {
                    self.in_schedule[fidx] = false;
                }
                continue;
            }
            if fidx < self.in_schedule.len() {
                self.in_schedule[fidx] = false;
            }
            result.consumed_candidates.push(first_lit);

            // Re-validate at pop time: assignments and occurrence lists may
            // have changed since this entry was pushed.
            let var_idx = first_lit.variable().index();
            if var_idx * 2 < vals.len() && vals[var_idx * 2] != 0 {
                continue;
            }
            if var_idx < var_states.len() && var_states[var_idx].is_removed() {
                continue;
            }
            if occ.count(first_lit) < MIN_FACTOR_MATCHES {
                continue;
            }

            match self.try_candidate(
                clause_db,
                occ,
                vals,
                first_lit,
                &mut deleted,
                &mut ticks,
                config.effort_limit,
                config.elim_bound,
                config.next_var_id,
            ) {
                Some(CandidateOutcome::Application(app)) => {
                    result.extension_vars_needed = 1;
                    Self::flatten_application(&mut result, app);
                    break;
                }
                Some(CandidateOutcome::SelfSubsuming(app)) => {
                    Self::flatten_self_subsuming(&mut result, app);
                    break;
                }
                None => {}
            }
        }

        // Restore the pooled tombstone buffer to all-false: only an accepted
        // factoring marks entries, and those are exactly result.to_delete.
        for &ci in &result.to_delete {
            deleted[ci] = false;
        }
        self.step_deleted = deleted;

        result.ticks_consumed = ticks;
        result
    }
}

/// Outcome of trying one first-factor candidate.
enum CandidateOutcome {
    /// Extension-variable factoring: one fresh variable, dividers + quotients.
    Application(FactorApplication),
    /// Complementary-factor resolution: no extension variable needed.
    SelfSubsuming(SelfSubsumingApplication),
}

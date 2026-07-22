// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Compact proof-obligation artifacts for the ay -> Lean 4 SAT/PB bridge.
//!
//! These structs describe dynamic proof obligations that ay can emit from SAT
//! and pseudo-Boolean proof paths. Lean 4 will later consume the JSON payload via
//! `proofState.openObligation`; until then this module provides the stable
//! ay-side ABI and fingerprint contract.

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

/// Current schema version for SAT/PB proof-obligation artifacts.
pub const SAT_PB_OBLIGATION_SCHEMA_VERSION: &str = "ay.proof-obligation.sat-pb.v1";

/// Domain profile for this bridge artifact.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum ObligationDomainProfile {
    /// SAT plus pseudo-Boolean certificate obligations.
    SatPb,
}

/// Goal shape that Lean 4 should open for the obligation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ObligationGoalKind {
    /// Prove a CNF or transformed CNF is satisfiable under a model witness.
    SatModelSound,
    /// Prove a CNF, PB formula, or derived proof object is unsatisfiable.
    UnsatCertificateSound,
    /// Prove a preprocessing or inprocessing transform preserves satisfiability.
    EquiSatisfiableTransform,
    /// Prove a pseudo-Boolean cutting-planes or VeriPB-style step is sound.
    PbRuleSound,
    /// Prove an LRAT/DRAT replay step or chain is sound.
    ResolutionReplaySound,
    /// Prove a checker accepts only semantically valid artifacts.
    CheckerSoundness,
}

/// Stable reference to an external source or generated artifact.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ArtifactRef {
    /// Logical role of the artifact, for example `source-instance` or `proof-log`.
    pub role: String,
    /// URI or repo-relative path for the artifact.
    pub uri: String,
    /// Optional content hash, preferably `sha256:<lowercase-hex>`.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub sha256: Option<String>,
    /// Optional media type such as `application/dimacs+cnf` or `text/x-lrat`.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub media_type: Option<String>,
}

/// Formula metadata needed by Lean 4 to select the SAT/PB library surface.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Default)]
pub struct FormulaMetadata {
    /// Formula family, if known, such as `php`, `random-3sat`, or `circuit`.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub family: Option<String>,
    /// Number of SAT variables, when the obligation is CNF-backed.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub num_vars: Option<u64>,
    /// Number of CNF clauses, when known.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub num_clauses: Option<u64>,
    /// Number of pseudo-Boolean constraints, when known.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub num_pb_constraints: Option<u64>,
    /// Maximum clause width or PB arity observed in the source artifact.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub max_width: Option<u64>,
}

/// Proof artifact metadata needed to route Lean 4 replay or checker obligations.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Default)]
pub struct ProofMetadata {
    /// Proof format, for example `lrat`, `drat`, `veripb`, or `model`.
    pub format: String,
    /// Producer name, usually `ay`.
    pub producer: String,
    /// Producer version, git revision, or binary fingerprint.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub producer_revision: Option<String>,
    /// Number of proof steps, when known.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub step_count: Option<u64>,
    /// Whether the proof artifact has already passed an external checker.
    pub externally_checked: bool,
}

/// Trust policy requested for Lean 4 consumption.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TrustPolicy {
    /// Whether Lean 4 must reject obligations that require trusted fallbacks.
    pub require_zero_trust: bool,
    /// Whether an external checker verdict must be present before opening.
    pub require_external_checker: bool,
    /// Allowed terminal trust markers for this artifact.
    pub allowed_trust_markers: Vec<String>,
    /// Human-readable policy profile, for example `sat-comp-main`.
    pub profile: String,
}

impl Default for TrustPolicy {
    fn default() -> Self {
        Self {
            require_zero_trust: true,
            require_external_checker: false,
            allowed_trust_markers: Vec::new(),
            profile: "sat-comp-main".to_string(),
        }
    }
}

/// SAT-COMP and benchmark metadata attached to an obligation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Default)]
pub struct BenchmarkTags {
    /// Benchmark corpus or suite name.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub corpus: Option<String>,
    /// Track name, for example `main`.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub track: Option<String>,
    /// Solver profile or variant used to produce the artifact.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub solver_profile: Option<String>,
    /// Additional deterministic tags used for routing and triage.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub tags: Vec<String>,
}

/// Versioned ay SAT/PB proof-obligation artifact.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SatPbProofObligation {
    /// Schema version. Must be [`SAT_PB_OBLIGATION_SCHEMA_VERSION`] for v1.
    pub schema_version: String,
    /// Domain profile. This v1 schema is intentionally limited to `sat-pb`.
    pub domain_profile: ObligationDomainProfile,
    /// Stable obligation identifier from the producing ay component.
    pub obligation_id: String,
    /// Goal shape requested from Lean 4.
    pub goal_kind: ObligationGoalKind,
    /// Source instance and proof/checker artifact references.
    pub artifacts: Vec<ArtifactRef>,
    /// Formula metadata.
    pub formula: FormulaMetadata,
    /// Proof metadata.
    pub proof: ProofMetadata,
    /// Trust policy for Lean 4 opening/replay.
    pub trust_policy: TrustPolicy,
    /// Benchmark and SAT-COMP routing tags.
    pub benchmark: BenchmarkTags,
    /// Optional extension metadata. Keys are sorted for deterministic fingerprints.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub extra: BTreeMap<String, String>,
    /// Stable fingerprint over all semantic fields except this field itself.
    pub fingerprint: String,
}

/// Checker-visible payload for one decompose SCC equivalence-substitution slice.
///
/// Literal fields use DIMACS signed integers. Proof IDs are LRAT clause IDs that
/// must be visible to an external checker, not trusted-transform placeholders.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EquivalenceSubstitutionLratSlice {
    /// Source CNF path or URI.
    pub source_dimacs_uri: String,
    /// LRAT proof path or URI that should contain the slice.
    pub lrat_proof_uri: String,
    /// Optional sidecar JSON path or URI for the slice payload.
    pub transform_slice_uri: String,
    /// Benchmark or instance identifier.
    pub benchmark_id: String,
    /// Formula family tag, for example `equivalence-chain-principle`.
    pub family: String,
    /// Source CNF variable count.
    pub num_vars: u64,
    /// Source CNF clause count.
    pub num_clauses: u64,
    /// Original clause ID before rewriting.
    pub original_clause_id: u64,
    /// Original clause literals before rewriting.
    pub original_clause_lits: Vec<i64>,
    /// Proof ID assigned to the rewritten clause.
    pub rewritten_clause_id: u64,
    /// Rewritten clause literals after substituting the representative.
    pub rewritten_clause_lits: Vec<i64>,
    /// Literal being replaced.
    pub substituted_lit: i64,
    /// SCC representative literal replacing `substituted_lit`.
    pub representative_lit: i64,
    /// LRAT IDs for the binary implication path `substituted_lit -> representative_lit`.
    pub lit_to_repr_edge_clause_ids: Vec<u64>,
    /// LRAT IDs for the binary implication path `representative_lit -> substituted_lit`.
    pub repr_to_lit_edge_clause_ids: Vec<u64>,
    /// Transient proof ID for `(not substituted_lit or representative_lit)`.
    pub lit_to_repr_binary_id: u64,
    /// Transient proof ID for `(substituted_lit or not representative_lit)`.
    pub repr_to_lit_binary_id: u64,
    /// LRAT hints used to add the rewritten clause.
    pub substitution_lrat_hints: Vec<u64>,
    /// Level-0 unit proof IDs used for dropped false literals.
    pub level0_unit_ids: Vec<u64>,
    /// Producer revision or binary fingerprint.
    pub producer_revision: Option<String>,
}

/// Checker-visible payload for one factor extension-variable transaction.
///
/// Literal fields use DIMACS signed integers. Clause IDs are LRAT IDs that must
/// be visible to an external checker. `source_clause_ids_quotient_major` is
/// grouped by quotient, with one source clause per factor in each group.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FactorExtensionLratTransaction {
    /// Source CNF path or URI immediately before this transaction.
    pub source_dimacs_uri: String,
    /// LRAT proof path or URI that should contain the transaction.
    pub lrat_proof_uri: String,
    /// Optional sidecar JSON path or URI for the transaction payload.
    pub transform_transaction_uri: String,
    /// Benchmark or instance identifier.
    pub benchmark_id: String,
    /// Formula family tag, for example `clique-formulas`.
    pub family: String,
    /// Source CNF variable count before introducing the fresh variable.
    pub num_vars: u64,
    /// Source CNF clause count before this transaction.
    pub num_clauses: u64,
    /// Fresh positive extension literal `x`.
    pub fresh_lit: i64,
    /// Factor literals `f_j` compressed by `x`.
    pub factors: Vec<i64>,
    /// Quotient tails `Q_i`, excluding the fresh literal.
    pub quotient_tails: Vec<Vec<i64>>,
    /// Source matrix clause IDs in quotient-major order:
    /// `C_{i,j} = (f_j or Q_i)`.
    pub source_clause_ids_quotient_major: Vec<u64>,
    /// Source matrix clause literals in the same quotient-major order.
    pub source_clause_lits_quotient_major: Vec<Vec<i64>>,
    /// LRAT IDs for divider clauses `(x or f_j)`.
    pub divider_clause_ids: Vec<u64>,
    /// Fresh-literal RAT pivots for divider clauses. These document the only
    /// allowed empty-hint divider surface: vacuous RAT on fresh `x`.
    pub divider_rat_pivots: Vec<i64>,
    /// LRAT ID for the proof-only blocked clause
    /// `(not x or not f_1 or ... or not f_n)`.
    pub blocked_clause_id: u64,
    /// Signed LRAT hints for the blocked clause. Expected shape is
    /// `[-divider_id_1, -divider_id_2, ...]`.
    pub blocked_signed_lrat_hints: Vec<i64>,
    /// LRAT IDs for quotient clauses `(not x or Q_i)`.
    pub quotient_clause_ids: Vec<u64>,
    /// Positive LRAT hints for each quotient clause. Expected shape is the
    /// corresponding source matrix IDs followed by `blocked_clause_id`.
    pub quotient_lrat_hints: Vec<Vec<u64>>,
    /// Proof-only delete target for the blocked clause.
    pub proof_only_delete_id: u64,
    /// Source clause delete IDs after live factor clauses are installed.
    pub source_delete_ids: Vec<u64>,
    /// Producer revision or binary fingerprint.
    pub producer_revision: Option<String>,
}

/// Dry-run payload for one planned factor application before solver mutation.
///
/// This mirrors the non-mutating handoff available after the SAT solver runs
/// factor LRAT preflight: one structured factor application plus the planned
/// forward-add LRAT IDs for that same application. It intentionally emits only
/// obligations; it does not make LRAT factor preprocessing legal by itself.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FactorExtensionLratDryRun {
    /// Source CNF path or URI immediately before this transaction.
    pub source_dimacs_uri: String,
    /// LRAT proof path or URI that should contain the transaction.
    pub lrat_proof_uri: String,
    /// Optional sidecar JSON path or URI for the transaction payload.
    pub transform_transaction_uri: String,
    /// Benchmark or instance identifier.
    pub benchmark_id: String,
    /// Formula family tag, for example `clique-formulas`.
    pub family: String,
    /// Source CNF variable count before introducing the fresh variable.
    pub num_vars: u64,
    /// Source CNF clause count before this transaction.
    pub num_clauses: u64,
    /// Fresh positive extension literal `x`.
    pub fresh_lit: i64,
    /// Factor literals `f_j` compressed by `x`.
    pub factors: Vec<i64>,
    /// Planned quotient clauses `(not x or Q_i)`, including the leading
    /// negative fresh literal.
    pub quotient_clauses: Vec<Vec<i64>>,
    /// Source matrix clause IDs in quotient-major order:
    /// `C_{i,j} = (f_j or Q_i)`.
    pub source_clause_ids_quotient_major: Vec<u64>,
    /// Source matrix clause literals in the same quotient-major order.
    pub source_clause_lits_quotient_major: Vec<Vec<i64>>,
    /// Planned LRAT add IDs for this application in solver emission order:
    /// divider IDs, proof-only blocked ID, then quotient IDs.
    pub planned_add_ids: Vec<u64>,
    /// Source clause delete IDs for this application in quotient-major order.
    pub source_delete_ids_quotient_major: Vec<u64>,
    /// Producer revision or binary fingerprint.
    pub producer_revision: Option<String>,
}

impl FactorExtensionLratDryRun {
    /// Build a checker-visible transaction from a dry-run factor application.
    ///
    /// Returns `None` unless the planned application already contains the full
    /// divider, blocked, quotient, source, and delete payload required by
    /// `FactorExtensionLratTransaction`.
    #[must_use]
    pub fn into_transaction(self) -> Option<FactorExtensionLratTransaction> {
        FactorExtensionLratTransaction::from_dry_run_parts(self)
    }

    /// Build the SAT/PB proof obligation for this dry-run factor application.
    ///
    /// This remains fail-closed by delegating to `into_transaction()` first.
    #[must_use]
    pub fn into_obligation(self) -> Option<SatPbProofObligation> {
        self.into_transaction()?.into_obligation()
    }
}

impl FactorExtensionLratTransaction {
    /// Build a checker-visible transaction from dry-run factor application parts.
    ///
    /// The input is intentionally the full dry-run payload instead of a live
    /// solver reference, so tests can pin the external LRAT contract without
    /// enabling factor preprocessing under LRAT.
    #[must_use]
    pub fn from_dry_run_parts(dry_run: FactorExtensionLratDryRun) -> Option<Self> {
        if dry_run.fresh_lit <= 0 {
            return None;
        }
        let fresh_neg = dry_run.fresh_lit.checked_neg()?;
        let expected_adds = dry_run
            .factors
            .len()
            .checked_add(1)?
            .checked_add(dry_run.quotient_clauses.len())?;
        if dry_run.planned_add_ids.len() != expected_adds {
            return None;
        }

        let mut quotient_tails = Vec::with_capacity(dry_run.quotient_clauses.len());
        for quotient in &dry_run.quotient_clauses {
            if quotient.first().copied() != Some(fresh_neg) {
                return None;
            }
            quotient_tails.push(quotient[1..].to_vec());
        }

        let factor_count = dry_run.factors.len();
        let divider_clause_ids = dry_run.planned_add_ids[..factor_count].to_vec();
        let blocked_clause_id = dry_run.planned_add_ids[factor_count];
        let quotient_clause_ids = dry_run.planned_add_ids[factor_count + 1..].to_vec();
        let blocked_signed_lrat_hints = negative_lrat_hints_for_ids(&divider_clause_ids)?;
        let quotient_lrat_hints = factor_quotient_lrat_hints(
            &dry_run.source_clause_ids_quotient_major,
            factor_count,
            blocked_clause_id,
        )?;

        let transaction = Self {
            source_dimacs_uri: dry_run.source_dimacs_uri,
            lrat_proof_uri: dry_run.lrat_proof_uri,
            transform_transaction_uri: dry_run.transform_transaction_uri,
            benchmark_id: dry_run.benchmark_id,
            family: dry_run.family,
            num_vars: dry_run.num_vars,
            num_clauses: dry_run.num_clauses,
            fresh_lit: dry_run.fresh_lit,
            factors: dry_run.factors,
            quotient_tails,
            source_clause_ids_quotient_major: dry_run.source_clause_ids_quotient_major,
            source_clause_lits_quotient_major: dry_run.source_clause_lits_quotient_major,
            divider_clause_ids,
            divider_rat_pivots: vec![dry_run.fresh_lit; factor_count],
            blocked_clause_id,
            blocked_signed_lrat_hints,
            quotient_clause_ids,
            quotient_lrat_hints,
            proof_only_delete_id: blocked_clause_id,
            source_delete_ids: dry_run.source_delete_ids_quotient_major,
            producer_revision: dry_run.producer_revision,
        };

        transaction
            .has_checker_visible_contract()
            .then_some(transaction)
    }
    /// Return true when this transaction has the minimum external LRAT payload.
    #[must_use]
    pub fn has_checker_visible_contract(&self) -> bool {
        let Some(fresh_var) = dimacs_var(self.fresh_lit) else {
            return false;
        };
        if self.fresh_lit <= 0 || fresh_var <= self.num_vars {
            return false;
        }
        if self.factors.len() < 2 || self.quotient_tails.is_empty() {
            return false;
        }
        if !clause_well_formed_dimacs(&self.factors) {
            return false;
        }
        if self.divider_clause_ids.len() != self.factors.len()
            || self.divider_rat_pivots.len() != self.factors.len()
            || self.quotient_clause_ids.len() != self.quotient_tails.len()
            || self.quotient_lrat_hints.len() != self.quotient_tails.len()
        {
            return false;
        }

        let source_count = self.factors.len() * self.quotient_tails.len();
        if self.source_clause_ids_quotient_major.len() != source_count
            || self.source_clause_lits_quotient_major.len() != source_count
            || self.source_delete_ids != self.source_clause_ids_quotient_major
        {
            return false;
        }
        if !all_nonzero(&self.source_clause_ids_quotient_major)
            || !all_nonzero(&self.divider_clause_ids)
            || !all_nonzero(&self.quotient_clause_ids)
            || self.blocked_clause_id == 0
            || self.proof_only_delete_id != self.blocked_clause_id
        {
            return false;
        }
        if !all_unique_u64(&self.source_clause_ids_quotient_major)
            || !all_unique_u64(&self.divider_clause_ids)
            || !all_unique_u64(&self.quotient_clause_ids)
        {
            return false;
        }
        let mut add_ids = self.divider_clause_ids.clone();
        add_ids.push(self.blocked_clause_id);
        add_ids.extend_from_slice(&self.quotient_clause_ids);
        if !all_unique_u64(&add_ids) {
            return false;
        }
        let mut all_clause_ids = self.source_clause_ids_quotient_major.clone();
        all_clause_ids.extend_from_slice(&add_ids);
        if !all_unique_u64(&all_clause_ids) {
            return false;
        }
        if self
            .divider_rat_pivots
            .iter()
            .any(|&pivot| pivot != self.fresh_lit)
        {
            return false;
        }
        if !negative_hints_match_ids(&self.blocked_signed_lrat_hints, &self.divider_clause_ids) {
            return false;
        }

        for tail in &self.quotient_tails {
            if tail.is_empty()
                || !clause_well_formed_dimacs(tail)
                || tail
                    .iter()
                    .any(|&lit| dimacs_var(lit) == Some(fresh_var) || self.factors.contains(&lit))
            {
                return false;
            }
        }

        for (quotient_idx, tail) in self.quotient_tails.iter().enumerate() {
            let source_start = quotient_idx * self.factors.len();
            let source_end = source_start + self.factors.len();
            let source_ids = &self.source_clause_ids_quotient_major[source_start..source_end];
            let mut expected_hints = source_ids.to_vec();
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

    /// Build the SAT/PB obligation for this LRAT transaction.
    ///
    /// Returns `None` instead of emitting a partial contract if any checker
    /// visible proof ingredient is absent.
    #[must_use]
    pub fn into_obligation(self) -> Option<SatPbProofObligation> {
        if !self.has_checker_visible_contract() {
            return None;
        }

        let obligation_id = format!(
            "sat:factor-extension-lrat:{}:x{}",
            self.benchmark_id, self.fresh_lit
        );
        let artifacts = vec![
            ArtifactRef {
                role: "source-instance".to_string(),
                uri: self.source_dimacs_uri.clone(),
                sha256: None,
                media_type: Some("application/dimacs+cnf".to_string()),
            },
            ArtifactRef {
                role: "proof-log".to_string(),
                uri: self.lrat_proof_uri.clone(),
                sha256: None,
                media_type: Some("text/x-lrat".to_string()),
            },
            ArtifactRef {
                role: "transform-transaction".to_string(),
                uri: self.transform_transaction_uri.clone(),
                sha256: None,
                media_type: Some(
                    "application/vnd.ay.factor-extension-lrat-transaction+json".to_string(),
                ),
            },
        ];

        let mut obligation = SatPbProofObligation::new(
            obligation_id,
            ObligationGoalKind::ResolutionReplaySound,
            artifacts,
            FormulaMetadata {
                family: Some(self.family.clone()),
                num_vars: Some(self.num_vars),
                num_clauses: Some(self.num_clauses),
                num_pb_constraints: None,
                max_width: factor_transaction_max_width(&self),
            },
            ProofMetadata {
                format: "lrat".to_string(),
                producer: "ay".to_string(),
                producer_revision: self.producer_revision.clone(),
                step_count: None,
                externally_checked: false,
            },
            TrustPolicy {
                require_zero_trust: true,
                require_external_checker: true,
                allowed_trust_markers: Vec::new(),
                profile: "sat-comp-main".to_string(),
            },
            BenchmarkTags {
                corpus: Some("satcomp-main-proxy".to_string()),
                track: Some("main".to_string()),
                solver_profile: Some("default-lrat".to_string()),
                tags: vec![
                    "proof-required".to_string(),
                    "factor".to_string(),
                    "extension-variable".to_string(),
                    "clique-shaped".to_string(),
                    self.benchmark_id.clone(),
                ],
            },
        );
        obligation.extra.insert(
            "proof_replay_entrypoint".to_string(),
            "proofState.openObligation".to_string(),
        );
        obligation.extra.insert(
            "transform.contract_version".to_string(),
            "ay.factor-extension-lrat-transaction.v1".to_string(),
        );
        obligation.extra.insert(
            "transform.fail_closed_on".to_string(),
            "missing-proof-manager,extension-var-count-mismatch,fresh-var-out-of-range,duplicate-fresh-var,malformed-application,missing-or-hidden-source-id,duplicate-source-id,malformed-clause,new-clause-count-mismatch,planned-add-rejected,trusted-transform-empty-hints,missing-signed-rat-witness,pending-deletion,external-check-failure"
                .to_string(),
        );
        obligation.extra.insert(
            "transform.name".to_string(),
            "factor-extension-variable-transaction".to_string(),
        );
        obligation.extra.insert(
            "factor.addition_order".to_string(),
            "dividers,blocked,quotients,delete-blocked,delete-sources".to_string(),
        );
        obligation.extra.insert(
            "factor.source_id_order".to_string(),
            "quotient-major".to_string(),
        );
        obligation
            .extra
            .insert("factor.fresh_lit".to_string(), self.fresh_lit.to_string());
        obligation
            .extra
            .insert("factor.factors".to_string(), join_i64s(&self.factors));
        obligation.extra.insert(
            "factor.quotient_tails".to_string(),
            join_i64_groups(&self.quotient_tails),
        );
        obligation.extra.insert(
            "factor.source_clause_ids_quotient_major".to_string(),
            join_u64s(&self.source_clause_ids_quotient_major),
        );
        obligation.extra.insert(
            "factor.source_clause_lits_quotient_major".to_string(),
            join_i64_groups(&self.source_clause_lits_quotient_major),
        );
        obligation.extra.insert(
            "factor.divider_clause_ids".to_string(),
            join_u64s(&self.divider_clause_ids),
        );
        obligation.extra.insert(
            "factor.divider_clause_lits".to_string(),
            join_i64_groups(&factor_divider_clauses(self.fresh_lit, &self.factors)),
        );
        obligation.extra.insert(
            "factor.divider_rat_pivots".to_string(),
            join_i64s(&self.divider_rat_pivots),
        );
        obligation.extra.insert(
            "factor.blocked_clause_id".to_string(),
            self.blocked_clause_id.to_string(),
        );
        obligation.extra.insert(
            "factor.blocked_clause_lits".to_string(),
            join_i64s(&factor_blocked_clause(self.fresh_lit, &self.factors)),
        );
        obligation.extra.insert(
            "factor.blocked_signed_lrat_hints".to_string(),
            join_i64s(&self.blocked_signed_lrat_hints),
        );
        obligation.extra.insert(
            "factor.quotient_clause_ids".to_string(),
            join_u64s(&self.quotient_clause_ids),
        );
        obligation.extra.insert(
            "factor.quotient_clause_lits".to_string(),
            join_i64_groups(&factor_quotient_clauses(
                self.fresh_lit,
                &self.quotient_tails,
            )),
        );
        obligation.extra.insert(
            "factor.quotient_lrat_hints".to_string(),
            join_u64_groups(&self.quotient_lrat_hints),
        );
        obligation.extra.insert(
            "factor.proof_only_delete_id".to_string(),
            self.proof_only_delete_id.to_string(),
        );
        obligation.extra.insert(
            "factor.source_delete_ids".to_string(),
            join_u64s(&self.source_delete_ids),
        );
        obligation.refresh_fingerprint();
        Some(obligation)
    }
}

impl EquivalenceSubstitutionLratSlice {
    /// Return true when this slice has the minimum external LRAT proof payload.
    #[must_use]
    pub fn has_checker_visible_contract(&self) -> bool {
        self.original_clause_id != 0
            && self.rewritten_clause_id != 0
            && self.substituted_lit != 0
            && self.representative_lit != 0
            && self.substituted_lit != self.representative_lit
            && !self.original_clause_lits.is_empty()
            && !self.rewritten_clause_lits.is_empty()
            && !self.lit_to_repr_edge_clause_ids.is_empty()
            && !self.repr_to_lit_edge_clause_ids.is_empty()
            && all_nonzero(&self.lit_to_repr_edge_clause_ids)
            && all_nonzero(&self.repr_to_lit_edge_clause_ids)
            && self.lit_to_repr_binary_id != 0
            && self.repr_to_lit_binary_id != 0
            && !self.substitution_lrat_hints.is_empty()
            && all_nonzero(&self.substitution_lrat_hints)
            && all_nonzero(&self.level0_unit_ids)
            && self
                .substitution_lrat_hints
                .contains(&self.lit_to_repr_binary_id)
            && self.substitution_lrat_hints.last() == Some(&self.original_clause_id)
    }

    /// Build the SAT/PB obligation for this LRAT slice.
    ///
    /// Returns `None` instead of emitting a partial contract if any checker
    /// visible proof ingredient is absent.
    #[must_use]
    pub fn into_obligation(self) -> Option<SatPbProofObligation> {
        if !self.has_checker_visible_contract() {
            return None;
        }

        let obligation_id = format!(
            "sat:decompose-scc-lrat:{}:c{}-to-c{}",
            self.benchmark_id, self.original_clause_id, self.rewritten_clause_id
        );
        let artifacts = vec![
            ArtifactRef {
                role: "source-instance".to_string(),
                uri: self.source_dimacs_uri.clone(),
                sha256: None,
                media_type: Some("application/dimacs+cnf".to_string()),
            },
            ArtifactRef {
                role: "proof-log".to_string(),
                uri: self.lrat_proof_uri.clone(),
                sha256: None,
                media_type: Some("text/x-lrat".to_string()),
            },
            ArtifactRef {
                role: "transform-slice".to_string(),
                uri: self.transform_slice_uri.clone(),
                sha256: None,
                media_type: Some("application/vnd.ay.decompose-lrat-slice+json".to_string()),
            },
        ];

        let mut obligation = SatPbProofObligation::new(
            obligation_id,
            ObligationGoalKind::ResolutionReplaySound,
            artifacts,
            FormulaMetadata {
                family: Some(self.family.clone()),
                num_vars: Some(self.num_vars),
                num_clauses: Some(self.num_clauses),
                num_pb_constraints: None,
                max_width: None,
            },
            ProofMetadata {
                format: "lrat".to_string(),
                producer: "ay".to_string(),
                producer_revision: self.producer_revision.clone(),
                step_count: None,
                externally_checked: false,
            },
            TrustPolicy {
                require_zero_trust: true,
                require_external_checker: true,
                allowed_trust_markers: Vec::new(),
                profile: "sat-comp-main".to_string(),
            },
            BenchmarkTags {
                corpus: Some("satcomp-main-proxy".to_string()),
                track: Some("main".to_string()),
                solver_profile: Some("default-lrat".to_string()),
                tags: vec![
                    "proof-required".to_string(),
                    "decompose".to_string(),
                    "scc-equivalence".to_string(),
                    self.benchmark_id.clone(),
                ],
            },
        );
        obligation.extra.insert(
            "proof_replay_entrypoint".to_string(),
            "proofState.openObligation".to_string(),
        );
        obligation.extra.insert(
            "transform.contract_version".to_string(),
            "ay.decompose-scc-lrat-slice.v1".to_string(),
        );
        obligation.extra.insert(
            "transform.fail_closed_on".to_string(),
            "missing-chain-edge-id,zero-proof-id,trusted-transform,pending-deletion,external-check-failure"
                .to_string(),
        );
        obligation.extra.insert(
            "transform.name".to_string(),
            "decompose-scc-equivalence-substitution".to_string(),
        );
        obligation.extra.insert(
            "decompose.original_clause_id".to_string(),
            self.original_clause_id.to_string(),
        );
        obligation.extra.insert(
            "decompose.original_clause_lits".to_string(),
            join_i64s(&self.original_clause_lits),
        );
        obligation.extra.insert(
            "decompose.rewritten_clause_id".to_string(),
            self.rewritten_clause_id.to_string(),
        );
        obligation.extra.insert(
            "decompose.rewritten_clause_lits".to_string(),
            join_i64s(&self.rewritten_clause_lits),
        );
        obligation.extra.insert(
            "decompose.substituted_lit".to_string(),
            self.substituted_lit.to_string(),
        );
        obligation.extra.insert(
            "decompose.representative_lit".to_string(),
            self.representative_lit.to_string(),
        );
        obligation.extra.insert(
            "decompose.lit_to_repr_edge_clause_ids".to_string(),
            join_u64s(&self.lit_to_repr_edge_clause_ids),
        );
        obligation.extra.insert(
            "decompose.repr_to_lit_edge_clause_ids".to_string(),
            join_u64s(&self.repr_to_lit_edge_clause_ids),
        );
        obligation.extra.insert(
            "decompose.lit_to_repr_binary_id".to_string(),
            self.lit_to_repr_binary_id.to_string(),
        );
        obligation.extra.insert(
            "decompose.repr_to_lit_binary_id".to_string(),
            self.repr_to_lit_binary_id.to_string(),
        );
        obligation.extra.insert(
            "decompose.lit_to_repr_binary_lits".to_string(),
            join_i64s(&[-self.substituted_lit, self.representative_lit]),
        );
        obligation.extra.insert(
            "decompose.repr_to_lit_binary_lits".to_string(),
            join_i64s(&[self.substituted_lit, -self.representative_lit]),
        );
        obligation.extra.insert(
            "decompose.substitution_lrat_hints".to_string(),
            join_u64s(&self.substitution_lrat_hints),
        );
        obligation.extra.insert(
            "decompose.level0_unit_ids".to_string(),
            join_u64s(&self.level0_unit_ids),
        );
        obligation.refresh_fingerprint();
        Some(obligation)
    }
}

impl SatPbProofObligation {
    /// Construct a v1 obligation and populate its stable fingerprint.
    #[must_use]
    pub fn new(
        obligation_id: impl Into<String>,
        goal_kind: ObligationGoalKind,
        artifacts: Vec<ArtifactRef>,
        formula: FormulaMetadata,
        proof: ProofMetadata,
        trust_policy: TrustPolicy,
        benchmark: BenchmarkTags,
    ) -> Self {
        let mut obligation = Self {
            schema_version: SAT_PB_OBLIGATION_SCHEMA_VERSION.to_string(),
            domain_profile: ObligationDomainProfile::SatPb,
            obligation_id: obligation_id.into(),
            goal_kind,
            artifacts,
            formula,
            proof,
            trust_policy,
            benchmark,
            extra: BTreeMap::new(),
            fingerprint: String::new(),
        };
        obligation.refresh_fingerprint();
        obligation
    }

    /// Recompute and update [`SatPbProofObligation::fingerprint`].
    pub fn refresh_fingerprint(&mut self) {
        self.fingerprint = self.compute_fingerprint();
    }

    /// Compute the stable fingerprint for this obligation.
    #[must_use]
    pub fn compute_fingerprint(&self) -> String {
        let mut hasher = Sha256::new();
        self.write_fingerprint_material(&mut |part| hasher.update(part.as_bytes()));
        format!("sha256:{}", hex_lower(&hasher.finalize()))
    }

    /// Return true when the stored fingerprint matches the current fields.
    #[must_use]
    pub fn fingerprint_is_current(&self) -> bool {
        self.fingerprint == self.compute_fingerprint()
    }

    fn write_fingerprint_material(&self, sink: &mut dyn FnMut(&str)) {
        field(sink, "schema_version", &self.schema_version);
        field(sink, "domain_profile", "sat-pb");
        field(sink, "obligation_id", &self.obligation_id);
        field(sink, "goal_kind", goal_kind_name(self.goal_kind));

        for (idx, artifact) in self.artifacts.iter().enumerate() {
            field(sink, &format!("artifacts[{idx}].role"), &artifact.role);
            field(sink, &format!("artifacts[{idx}].uri"), &artifact.uri);
            opt_field(
                sink,
                &format!("artifacts[{idx}].sha256"),
                artifact.sha256.as_deref(),
            );
            opt_field(
                sink,
                &format!("artifacts[{idx}].media_type"),
                artifact.media_type.as_deref(),
            );
        }

        opt_field(sink, "formula.family", self.formula.family.as_deref());
        opt_u64(sink, "formula.num_vars", self.formula.num_vars);
        opt_u64(sink, "formula.num_clauses", self.formula.num_clauses);
        opt_u64(
            sink,
            "formula.num_pb_constraints",
            self.formula.num_pb_constraints,
        );
        opt_u64(sink, "formula.max_width", self.formula.max_width);

        field(sink, "proof.format", &self.proof.format);
        field(sink, "proof.producer", &self.proof.producer);
        opt_field(
            sink,
            "proof.producer_revision",
            self.proof.producer_revision.as_deref(),
        );
        opt_u64(sink, "proof.step_count", self.proof.step_count);
        field(
            sink,
            "proof.externally_checked",
            bool_name(self.proof.externally_checked),
        );

        field(
            sink,
            "trust_policy.require_zero_trust",
            bool_name(self.trust_policy.require_zero_trust),
        );
        field(
            sink,
            "trust_policy.require_external_checker",
            bool_name(self.trust_policy.require_external_checker),
        );
        for (idx, marker) in self.trust_policy.allowed_trust_markers.iter().enumerate() {
            field(
                sink,
                &format!("trust_policy.allowed_trust_markers[{idx}]"),
                marker,
            );
        }
        field(sink, "trust_policy.profile", &self.trust_policy.profile);

        opt_field(sink, "benchmark.corpus", self.benchmark.corpus.as_deref());
        opt_field(sink, "benchmark.track", self.benchmark.track.as_deref());
        opt_field(
            sink,
            "benchmark.solver_profile",
            self.benchmark.solver_profile.as_deref(),
        );
        for (idx, tag) in self.benchmark.tags.iter().enumerate() {
            field(sink, &format!("benchmark.tags[{idx}]"), tag);
        }

        for (key, value) in &self.extra {
            field(sink, &format!("extra.{key}"), value);
        }
    }
}

fn field(sink: &mut dyn FnMut(&str), key: &str, value: &str) {
    sink(key);
    sink("\0");
    sink(value);
    sink("\n");
}

fn opt_field(sink: &mut dyn FnMut(&str), key: &str, value: Option<&str>) {
    if let Some(value) = value {
        field(sink, key, value);
    }
}

fn opt_u64(sink: &mut dyn FnMut(&str), key: &str, value: Option<u64>) {
    if let Some(value) = value {
        field(sink, key, &value.to_string());
    }
}

fn bool_name(value: bool) -> &'static str {
    if value {
        "true"
    } else {
        "false"
    }
}

fn goal_kind_name(goal_kind: ObligationGoalKind) -> &'static str {
    match goal_kind {
        ObligationGoalKind::SatModelSound => "sat_model_sound",
        ObligationGoalKind::UnsatCertificateSound => "unsat_certificate_sound",
        ObligationGoalKind::EquiSatisfiableTransform => "equi_satisfiable_transform",
        ObligationGoalKind::PbRuleSound => "pb_rule_sound",
        ObligationGoalKind::ResolutionReplaySound => "resolution_replay_sound",
        ObligationGoalKind::CheckerSoundness => "checker_soundness",
    }
}

fn hex_lower(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len() * 2);
    for &byte in bytes {
        out.push(HEX[(byte >> 4) as usize] as char);
        out.push(HEX[(byte & 0x0f) as usize] as char);
    }
    out
}

fn all_nonzero(values: &[u64]) -> bool {
    values.iter().all(|&value| value != 0)
}

fn all_unique_u64(values: &[u64]) -> bool {
    let mut seen = std::collections::BTreeSet::new();
    values.iter().all(|&value| seen.insert(value))
}

fn dimacs_var(lit: i64) -> Option<u64> {
    if lit == 0 || lit == i64::MIN {
        return None;
    }
    Some(lit.unsigned_abs())
}

fn clause_well_formed_dimacs(lits: &[i64]) -> bool {
    if lits.is_empty() {
        return false;
    }
    for (idx, &lit) in lits.iter().enumerate() {
        if dimacs_var(lit).is_none() {
            return false;
        }
        for &prev in &lits[..idx] {
            if prev == lit || prev == -lit {
                return false;
            }
        }
    }
    true
}

fn same_clause_dimacs(left: &[i64], right: &[i64]) -> bool {
    if !clause_well_formed_dimacs(left) || !clause_well_formed_dimacs(right) {
        return false;
    }
    let mut left = left.to_vec();
    let mut right = right.to_vec();
    left.sort_unstable();
    right.sort_unstable();
    left == right
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

fn negative_lrat_hints_for_ids(ids: &[u64]) -> Option<Vec<i64>> {
    let mut hints = Vec::with_capacity(ids.len());
    for &id in ids {
        hints.push(i64::try_from(id).ok()?.checked_neg()?);
    }
    Some(hints)
}

fn factor_quotient_lrat_hints(
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

fn factor_divider_clauses(fresh_lit: i64, factors: &[i64]) -> Vec<Vec<i64>> {
    factors
        .iter()
        .map(|&factor| vec![fresh_lit, factor])
        .collect()
}

fn factor_blocked_clause(fresh_lit: i64, factors: &[i64]) -> Vec<i64> {
    let mut blocked = Vec::with_capacity(factors.len() + 1);
    blocked.push(-fresh_lit);
    blocked.extend(factors.iter().map(|&factor| -factor));
    blocked
}

fn factor_quotient_clauses(fresh_lit: i64, quotient_tails: &[Vec<i64>]) -> Vec<Vec<i64>> {
    quotient_tails
        .iter()
        .map(|tail| {
            let mut clause = Vec::with_capacity(tail.len() + 1);
            clause.push(-fresh_lit);
            clause.extend_from_slice(tail);
            clause
        })
        .collect()
}

fn factor_transaction_max_width(transaction: &FactorExtensionLratTransaction) -> Option<u64> {
    let source_width = transaction
        .source_clause_lits_quotient_major
        .iter()
        .map(Vec::len)
        .max()
        .unwrap_or(0);
    let quotient_width = transaction
        .quotient_tails
        .iter()
        .map(|tail| tail.len() + 1)
        .max()
        .unwrap_or(0);
    let width = source_width
        .max(quotient_width)
        .max(transaction.factors.len() + 1);
    (width != 0).then_some(width as u64)
}

fn join_u64s(values: &[u64]) -> String {
    values
        .iter()
        .map(u64::to_string)
        .collect::<Vec<_>>()
        .join(",")
}

fn join_i64s(values: &[i64]) -> String {
    values
        .iter()
        .map(i64::to_string)
        .collect::<Vec<_>>()
        .join(",")
}

fn join_u64_groups(values: &[Vec<u64>]) -> String {
    values
        .iter()
        .map(|group| join_u64s(group))
        .collect::<Vec<_>>()
        .join(";")
}

fn join_i64_groups(values: &[Vec<i64>]) -> String {
    values
        .iter()
        .map(|group| join_i64s(group))
        .collect::<Vec<_>>()
        .join(";")
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::{json, Value};

    const PROOF_REPLAY_OPEN_OBLIGATION_SCHEMA_VERSION: &str = "proof_replay-open-obligation-v1";
    const PROOF_REPLAY_PROOF_STATE_SCHEMA_VERSION: &str = "proof_replay-proof-state-v2";

    fn sample_obligation() -> SatPbProofObligation {
        let mut obligation = SatPbProofObligation::new(
            "sat-pb:php21:lrat-root-empty",
            ObligationGoalKind::UnsatCertificateSound,
            vec![
                ArtifactRef {
                    role: "source-instance".to_string(),
                    uri: "benchmarks/sat/php21.cnf".to_string(),
                    sha256: Some(
                        "sha256:1111111111111111111111111111111111111111111111111111111111111111"
                            .to_string(),
                    ),
                    media_type: Some("application/dimacs+cnf".to_string()),
                },
                ArtifactRef {
                    role: "proof-log".to_string(),
                    uri: "artifacts/php21/proof.lrat".to_string(),
                    sha256: Some(
                        "sha256:2222222222222222222222222222222222222222222222222222222222222222"
                            .to_string(),
                    ),
                    media_type: Some("text/x-lrat".to_string()),
                },
            ],
            FormulaMetadata {
                family: Some("pigeonhole".to_string()),
                num_vars: Some(2),
                num_clauses: Some(4),
                num_pb_constraints: None,
                max_width: Some(2),
            },
            ProofMetadata {
                format: "lrat".to_string(),
                producer: "ay".to_string(),
                producer_revision: Some("ay-test-rev".to_string()),
                step_count: Some(3),
                externally_checked: true,
            },
            TrustPolicy {
                require_zero_trust: true,
                require_external_checker: true,
                allowed_trust_markers: Vec::new(),
                profile: "sat-comp-main".to_string(),
            },
            BenchmarkTags {
                corpus: Some("satcomp-main-proxy".to_string()),
                track: Some("main".to_string()),
                solver_profile: Some("default".to_string()),
                tags: vec!["proof-required".to_string(), "php".to_string()],
            },
        );
        obligation.extra.insert(
            "proof_replay_entrypoint".to_string(),
            "proofState.openObligation".to_string(),
        );
        obligation.refresh_fingerprint();
        obligation
    }

    fn sample_factor_transaction() -> FactorExtensionLratTransaction {
        FactorExtensionLratTransaction {
            source_dimacs_uri: "benchmarks/sat/satcomp2024-sample/cb2e8b7fada420c5046f587ea754d052-clique_n2_k10.sanitized.cnf.xz".to_string(),
            lrat_proof_uri: "target/clique-factor/proof.lrat".to_string(),
            transform_transaction_uri: "target/clique-factor/factor-transaction-0001.json"
                .to_string(),
            benchmark_id: "clique_n2_k10".to_string(),
            family: "clique-formulas".to_string(),
            num_vars: 7,
            num_clauses: 10,
            fresh_lit: 8,
            factors: vec![1, 2],
            quotient_tails: vec![vec![3, 4], vec![3, 5], vec![4, 5]],
            source_clause_ids_quotient_major: vec![1, 2, 3, 4, 5, 6],
            source_clause_lits_quotient_major: vec![
                vec![1, 3, 4],
                vec![2, 3, 4],
                vec![1, 3, 5],
                vec![2, 3, 5],
                vec![1, 4, 5],
                vec![2, 4, 5],
            ],
            divider_clause_ids: vec![11, 12],
            divider_rat_pivots: vec![8, 8],
            blocked_clause_id: 13,
            blocked_signed_lrat_hints: vec![-11, -12],
            quotient_clause_ids: vec![14, 15, 16],
            quotient_lrat_hints: vec![vec![1, 2, 13], vec![3, 4, 13], vec![5, 6, 13]],
            proof_only_delete_id: 13,
            source_delete_ids: vec![1, 2, 3, 4, 5, 6],
            producer_revision: Some("ay-test-rev".to_string()),
        }
    }

    fn sample_factor_dry_run() -> FactorExtensionLratDryRun {
        FactorExtensionLratDryRun {
            source_dimacs_uri: "benchmarks/sat/satcomp2024-sample/cb2e8b7fada420c5046f587ea754d052-clique_n2_k10.sanitized.cnf.xz".to_string(),
            lrat_proof_uri: "target/clique-factor/proof.lrat".to_string(),
            transform_transaction_uri: "target/clique-factor/factor-transaction-0001.json"
                .to_string(),
            benchmark_id: "clique_n2_k10".to_string(),
            family: "clique-formulas".to_string(),
            num_vars: 7,
            num_clauses: 10,
            fresh_lit: 8,
            factors: vec![1, 2],
            quotient_clauses: vec![vec![-8, 3, 4], vec![-8, 3, 5], vec![-8, 4, 5]],
            source_clause_ids_quotient_major: vec![1, 2, 3, 4, 5, 6],
            source_clause_lits_quotient_major: vec![
                vec![1, 3, 4],
                vec![2, 3, 4],
                vec![1, 3, 5],
                vec![2, 3, 5],
                vec![1, 4, 5],
                vec![2, 4, 5],
            ],
            planned_add_ids: vec![11, 12, 13, 14, 15, 16],
            source_delete_ids_quotient_major: vec![1, 2, 3, 4, 5, 6],
            producer_revision: Some("ay-test-rev".to_string()),
        }
    }

    #[derive(Debug, Clone)]
    struct MinimalEquivalenceChainFixture {
        num_vars: u64,
        edge_clause_ids: [u64; 3],
        original_clause_id: u64,
        lit_to_repr_binary_id: u64,
        repr_to_lit_binary_id: u64,
        rewritten_clause_id: u64,
    }

    impl MinimalEquivalenceChainFixture {
        fn source_dimacs(&self) -> String {
            "p cnf 4 4\n-1 2 0\n-2 3 0\n-3 1 0\n3 4 0\n".to_string()
        }

        fn planned_lrat_prefix(&self) -> String {
            format!(
                "{} -3 1 0 {} 0\n{} 3 -1 0 {} {} 0\n{} 1 4 0 {} {} 0\n{} d {} {} 0\n",
                self.lit_to_repr_binary_id,
                self.edge_clause_ids[2],
                self.repr_to_lit_binary_id,
                self.edge_clause_ids[0],
                self.edge_clause_ids[1],
                self.rewritten_clause_id,
                self.lit_to_repr_binary_id,
                self.original_clause_id,
                self.rewritten_clause_id + 1,
                self.lit_to_repr_binary_id,
                self.repr_to_lit_binary_id
            )
        }

        fn slice(&self) -> EquivalenceSubstitutionLratSlice {
            EquivalenceSubstitutionLratSlice {
                source_dimacs_uri: "inline:minimal-fmla-equivalence-chain-3cycle.cnf".to_string(),
                lrat_proof_uri: "inline:minimal-fmla-equivalence-chain-3cycle.lrat".to_string(),
                transform_slice_uri: "inline:minimal-fmla-equivalence-chain-3cycle.slice.json"
                    .to_string(),
                benchmark_id: "minimal_fmla_equiv_chain_3cycle".to_string(),
                family: "equivalence-chain-principle".to_string(),
                num_vars: self.num_vars,
                num_clauses: 4,
                original_clause_id: self.original_clause_id,
                original_clause_lits: vec![3, 4],
                rewritten_clause_id: self.rewritten_clause_id,
                rewritten_clause_lits: vec![1, 4],
                substituted_lit: 3,
                representative_lit: 1,
                lit_to_repr_edge_clause_ids: vec![self.edge_clause_ids[2]],
                repr_to_lit_edge_clause_ids: vec![self.edge_clause_ids[0], self.edge_clause_ids[1]],
                lit_to_repr_binary_id: self.lit_to_repr_binary_id,
                repr_to_lit_binary_id: self.repr_to_lit_binary_id,
                substitution_lrat_hints: vec![self.lit_to_repr_binary_id, self.original_clause_id],
                level0_unit_ids: Vec::new(),
                producer_revision: Some("ay-test-rev".to_string()),
            }
        }
    }

    fn minimal_equivalence_chain_fixture() -> MinimalEquivalenceChainFixture {
        // Three binary implications form an SCC, and the target clause is the
        // smallest non-unit clause whose positive chain literal can be rewritten.
        // This is only an obligation fixture; it does not enable solver routing.
        MinimalEquivalenceChainFixture {
            num_vars: 4,
            edge_clause_ids: [1, 2, 3],
            original_clause_id: 4,
            lit_to_repr_binary_id: 5,
            repr_to_lit_binary_id: 6,
            rewritten_clause_id: 7,
        }
    }

    #[derive(Debug, Clone)]
    struct MinimalCliqueFactorFixture {
        num_vars: u64,
        fresh_lit: i64,
        factors: Vec<i64>,
        quotient_tails: Vec<Vec<i64>>,
        first_source_clause_id: u64,
        first_planned_add_id: u64,
    }

    impl MinimalCliqueFactorFixture {
        fn source_clause_lits_quotient_major(&self) -> Vec<Vec<i64>> {
            self.quotient_tails
                .iter()
                .flat_map(|tail| {
                    self.factors.iter().map(move |&factor| {
                        let mut clause = Vec::with_capacity(tail.len() + 1);
                        clause.push(factor);
                        clause.extend_from_slice(tail);
                        clause
                    })
                })
                .collect()
        }

        fn source_clause_ids_quotient_major(&self) -> Vec<u64> {
            (0..self.source_clause_lits_quotient_major().len())
                .map(|idx| self.first_source_clause_id + idx as u64)
                .collect()
        }

        fn source_dimacs(&self) -> String {
            let clauses = self.source_clause_lits_quotient_major();
            let mut dimacs = format!("p cnf {} {}\n", self.num_vars, clauses.len());
            for clause in clauses {
                for lit in clause {
                    dimacs.push_str(&format!("{lit} "));
                }
                dimacs.push_str("0\n");
            }
            dimacs
        }

        fn planned_add_ids(&self) -> Vec<u64> {
            let add_count = self.factors.len() + 1 + self.quotient_tails.len();
            (0..add_count)
                .map(|idx| self.first_planned_add_id + idx as u64)
                .collect()
        }

        fn dry_run(&self) -> FactorExtensionLratDryRun {
            let source_clause_ids = self.source_clause_ids_quotient_major();
            FactorExtensionLratDryRun {
                source_dimacs_uri: "inline:minimal-clique-factor-2x3.cnf".to_string(),
                lrat_proof_uri: "target/minimal-clique-factor/proof.lrat".to_string(),
                transform_transaction_uri:
                    "target/minimal-clique-factor/factor-transaction-0001.json".to_string(),
                benchmark_id: "minimal_clique_factor_2x3".to_string(),
                family: "clique-formulas".to_string(),
                num_vars: self.num_vars,
                num_clauses: source_clause_ids.len() as u64,
                fresh_lit: self.fresh_lit,
                factors: self.factors.clone(),
                quotient_clauses: factor_quotient_clauses(self.fresh_lit, &self.quotient_tails),
                source_clause_ids_quotient_major: source_clause_ids.clone(),
                source_clause_lits_quotient_major: self.source_clause_lits_quotient_major(),
                planned_add_ids: self.planned_add_ids(),
                source_delete_ids_quotient_major: source_clause_ids,
                producer_revision: Some("ay-test-rev".to_string()),
            }
        }
    }

    fn minimal_clique_factor_fixture() -> MinimalCliqueFactorFixture {
        // Mirrors the ay-sat proof_lrat 2x3 factor surface. It is minimal for
        // a live-clause reduction: 2x2 ternary factoring breaks even, while
        // binary source clauses are outside the solver factor candidate shape.
        MinimalCliqueFactorFixture {
            num_vars: 5,
            fresh_lit: 6,
            factors: vec![1, 2],
            quotient_tails: vec![vec![3, 4], vec![3, 5], vec![4, 5]],
            first_source_clause_id: 21,
            first_planned_add_id: 31,
        }
    }

    #[test]
    fn json_roundtrip_preserves_obligation() {
        let obligation = sample_obligation();
        let json = serde_json::to_string_pretty(&obligation).expect("serialize obligation");
        let decoded: SatPbProofObligation =
            serde_json::from_str(&json).expect("deserialize obligation");

        assert_eq!(decoded, obligation);
        assert!(decoded.fingerprint_is_current());
        assert_eq!(decoded.schema_version, SAT_PB_OBLIGATION_SCHEMA_VERSION);
        assert_eq!(decoded.domain_profile, ObligationDomainProfile::SatPb);
    }

    #[test]
    fn fingerprint_is_stable_for_same_content() {
        let left = sample_obligation();
        let right = sample_obligation();

        assert_eq!(left.fingerprint, right.fingerprint);
        assert_eq!(left.compute_fingerprint(), right.compute_fingerprint());
        assert!(left.fingerprint.starts_with("sha256:"));
        assert_eq!(left.fingerprint.len(), "sha256:".len() + 64);
    }

    #[test]
    fn fingerprint_excludes_fingerprint_field_but_tracks_semantic_changes() {
        let mut obligation = sample_obligation();
        let original = obligation.fingerprint.clone();

        obligation.fingerprint = "sha256:stale".to_string();
        assert_eq!(obligation.compute_fingerprint(), original);
        assert!(!obligation.fingerprint_is_current());

        obligation.proof.step_count = Some(4);
        assert_ne!(obligation.compute_fingerprint(), original);
    }

    #[test]
    fn decompose_equivalence_lrat_slice_obligation_records_checker_visible_contract() {
        let slice = EquivalenceSubstitutionLratSlice {
            source_dimacs_uri: "benchmarks/sat/satcomp2024-sample/9cd3acdb765c15163bc239ae3a57f880-FmlaEquivChain_4_6_6.sanitized.cnf.xz".to_string(),
            lrat_proof_uri: "target/fmla-equiv-chain/proof.lrat".to_string(),
            transform_slice_uri: "target/fmla-equiv-chain/decompose-slice-0001.json".to_string(),
            benchmark_id: "FmlaEquivChain_4_6_6".to_string(),
            family: "equivalence-chain-principle".to_string(),
            num_vars: 54_411,
            num_clauses: 437_952,
            original_clause_id: 101,
            original_clause_lits: vec![42, -7, 19],
            rewritten_clause_id: 202,
            rewritten_clause_lits: vec![5, -7, 19],
            substituted_lit: 42,
            representative_lit: 5,
            lit_to_repr_edge_clause_ids: vec![11, 12, 13],
            repr_to_lit_edge_clause_ids: vec![17, 18],
            lit_to_repr_binary_id: 301,
            repr_to_lit_binary_id: 302,
            substitution_lrat_hints: vec![301, 101],
            level0_unit_ids: Vec::new(),
            producer_revision: Some("ay-test-rev".to_string()),
        };

        assert!(slice.has_checker_visible_contract());
        let obligation = slice
            .into_obligation()
            .expect("complete slice should emit an obligation");

        assert_eq!(
            obligation.goal_kind,
            ObligationGoalKind::ResolutionReplaySound
        );
        assert_eq!(obligation.proof.format, "lrat");
        assert!(obligation.trust_policy.require_zero_trust);
        assert!(obligation.trust_policy.require_external_checker);
        assert_eq!(
            obligation.extra["transform.contract_version"],
            "ay.decompose-scc-lrat-slice.v1"
        );
        assert_eq!(
            obligation.extra["transform.fail_closed_on"],
            "missing-chain-edge-id,zero-proof-id,trusted-transform,pending-deletion,external-check-failure"
        );
        assert_eq!(obligation.extra["decompose.original_clause_id"], "101");
        assert_eq!(
            obligation.extra["decompose.original_clause_lits"],
            "42,-7,19"
        );
        assert_eq!(obligation.extra["decompose.rewritten_clause_id"], "202");
        assert_eq!(
            obligation.extra["decompose.rewritten_clause_lits"],
            "5,-7,19"
        );
        assert_eq!(
            obligation.extra["decompose.lit_to_repr_binary_lits"],
            "-42,5"
        );
        assert_eq!(
            obligation.extra["decompose.repr_to_lit_binary_lits"],
            "42,-5"
        );
        assert_eq!(
            obligation.extra["decompose.lit_to_repr_edge_clause_ids"],
            "11,12,13"
        );
        assert_eq!(
            obligation.extra["decompose.repr_to_lit_edge_clause_ids"],
            "17,18"
        );
        assert_eq!(
            obligation.extra["decompose.substitution_lrat_hints"],
            "301,101"
        );
        assert_eq!(obligation.extra["decompose.level0_unit_ids"], "");
        assert!(obligation.fingerprint_is_current());
    }

    #[test]
    fn decompose_minimal_equivalence_chain_fixture_records_obligation_shape() {
        let fixture = minimal_equivalence_chain_fixture();
        assert_eq!(
            fixture.source_dimacs(),
            "p cnf 4 4\n-1 2 0\n-2 3 0\n-3 1 0\n3 4 0\n"
        );
        assert_eq!(
            fixture.planned_lrat_prefix(),
            "5 -3 1 0 3 0\n6 3 -1 0 1 2 0\n7 1 4 0 5 4 0\n8 d 5 6 0\n"
        );

        let slice = fixture.slice();
        assert!(slice.has_checker_visible_contract());
        let obligation = slice
            .into_obligation()
            .expect("minimal equivalence-chain fixture should emit an obligation");

        assert_eq!(
            obligation.obligation_id,
            "sat:decompose-scc-lrat:minimal_fmla_equiv_chain_3cycle:c4-to-c7"
        );
        assert_eq!(
            obligation.goal_kind,
            ObligationGoalKind::ResolutionReplaySound
        );
        assert_eq!(obligation.proof.format, "lrat");
        assert!(!obligation.proof.externally_checked);
        assert_eq!(obligation.formula.num_vars, Some(4));
        assert_eq!(obligation.formula.num_clauses, Some(4));
        assert_eq!(
            obligation.extra["transform.name"],
            "decompose-scc-equivalence-substitution"
        );
        assert_eq!(obligation.extra["decompose.original_clause_id"], "4");
        assert_eq!(obligation.extra["decompose.original_clause_lits"], "3,4");
        assert_eq!(obligation.extra["decompose.rewritten_clause_id"], "7");
        assert_eq!(obligation.extra["decompose.rewritten_clause_lits"], "1,4");
        assert_eq!(obligation.extra["decompose.substituted_lit"], "3");
        assert_eq!(obligation.extra["decompose.representative_lit"], "1");
        assert_eq!(
            obligation.extra["decompose.lit_to_repr_edge_clause_ids"],
            "3"
        );
        assert_eq!(
            obligation.extra["decompose.repr_to_lit_edge_clause_ids"],
            "1,2"
        );
        assert_eq!(obligation.extra["decompose.lit_to_repr_binary_id"], "5");
        assert_eq!(obligation.extra["decompose.repr_to_lit_binary_id"], "6");
        assert_eq!(
            obligation.extra["decompose.lit_to_repr_binary_lits"],
            "-3,1"
        );
        assert_eq!(
            obligation.extra["decompose.repr_to_lit_binary_lits"],
            "3,-1"
        );
        assert_eq!(obligation.extra["decompose.substitution_lrat_hints"], "5,4");
        assert_eq!(obligation.extra["decompose.level0_unit_ids"], "");
        assert!(obligation.trust_policy.require_external_checker);
        assert!(obligation.fingerprint_is_current());
    }

    #[test]
    fn decompose_minimal_equivalence_chain_fixture_fails_closed_without_path_ids() {
        let mut slice = minimal_equivalence_chain_fixture().slice();
        slice.repr_to_lit_edge_clause_ids.clear();

        assert!(!slice.has_checker_visible_contract());
        assert!(slice.into_obligation().is_none());
    }

    #[test]
    fn decompose_equivalence_lrat_slice_obligation_fails_closed_on_zero_ids() {
        let slice = EquivalenceSubstitutionLratSlice {
            source_dimacs_uri: "benchmarks/fmla.cnf".to_string(),
            lrat_proof_uri: "target/fmla/proof.lrat".to_string(),
            transform_slice_uri: "target/fmla/slice.json".to_string(),
            benchmark_id: "FmlaEquivChain_4_6_6".to_string(),
            family: "equivalence-chain-principle".to_string(),
            num_vars: 54_411,
            num_clauses: 437_952,
            original_clause_id: 101,
            original_clause_lits: vec![42, -7],
            rewritten_clause_id: 202,
            rewritten_clause_lits: vec![5, -7],
            substituted_lit: 42,
            representative_lit: 5,
            lit_to_repr_edge_clause_ids: vec![11, 0, 13],
            repr_to_lit_edge_clause_ids: vec![17, 18],
            lit_to_repr_binary_id: 301,
            repr_to_lit_binary_id: 302,
            substitution_lrat_hints: vec![301, 101],
            level0_unit_ids: Vec::new(),
            producer_revision: None,
        };

        assert!(!slice.has_checker_visible_contract());
        assert!(slice.into_obligation().is_none());
    }

    #[test]
    fn factor_extension_lrat_transaction_obligation_records_checker_visible_payload() {
        let transaction = sample_factor_transaction();

        assert!(transaction.has_checker_visible_contract());
        let obligation = transaction
            .into_obligation()
            .expect("complete factor transaction should emit an obligation");

        assert_eq!(
            obligation.goal_kind,
            ObligationGoalKind::ResolutionReplaySound
        );
        assert_eq!(obligation.proof.format, "lrat");
        assert!(obligation.trust_policy.require_zero_trust);
        assert!(obligation.trust_policy.require_external_checker);
        assert_eq!(
            obligation.extra["transform.contract_version"],
            "ay.factor-extension-lrat-transaction.v1"
        );
        assert_eq!(
            obligation.extra["transform.name"],
            "factor-extension-variable-transaction"
        );
        assert_eq!(obligation.extra["factor.fresh_lit"], "8");
        assert_eq!(obligation.extra["factor.factors"], "1,2");
        assert_eq!(obligation.extra["factor.quotient_tails"], "3,4;3,5;4,5");
        assert_eq!(
            obligation.extra["factor.source_clause_ids_quotient_major"],
            "1,2,3,4,5,6"
        );
        assert_eq!(
            obligation.extra["factor.source_clause_lits_quotient_major"],
            "1,3,4;2,3,4;1,3,5;2,3,5;1,4,5;2,4,5"
        );
        assert_eq!(obligation.extra["factor.divider_clause_ids"], "11,12");
        assert_eq!(obligation.extra["factor.divider_clause_lits"], "8,1;8,2");
        assert_eq!(obligation.extra["factor.divider_rat_pivots"], "8,8");
        assert_eq!(obligation.extra["factor.blocked_clause_id"], "13");
        assert_eq!(obligation.extra["factor.blocked_clause_lits"], "-8,-1,-2");
        assert_eq!(
            obligation.extra["factor.blocked_signed_lrat_hints"],
            "-11,-12"
        );
        assert_eq!(obligation.extra["factor.quotient_clause_ids"], "14,15,16");
        assert_eq!(
            obligation.extra["factor.quotient_clause_lits"],
            "-8,3,4;-8,3,5;-8,4,5"
        );
        assert_eq!(
            obligation.extra["factor.quotient_lrat_hints"],
            "1,2,13;3,4,13;5,6,13"
        );
        assert_eq!(obligation.extra["factor.proof_only_delete_id"], "13");
        assert_eq!(obligation.extra["factor.source_delete_ids"], "1,2,3,4,5,6");
        assert!(
            obligation.extra["transform.fail_closed_on"].contains("trusted-transform-empty-hints")
        );
        assert!(obligation.fingerprint_is_current());
    }

    #[test]
    fn factor_extension_lrat_transaction_fails_closed_without_signed_blocked_hints() {
        let mut transaction = sample_factor_transaction();
        transaction.blocked_signed_lrat_hints = vec![-11];

        assert!(!transaction.has_checker_visible_contract());
        assert!(transaction.into_obligation().is_none());
    }

    #[test]
    fn factor_extension_lrat_dry_run_emits_obligation_from_planned_application() {
        let dry_run = sample_factor_dry_run();
        let transaction = dry_run
            .clone()
            .into_transaction()
            .expect("dry-run payload should build the transaction contract");

        assert!(transaction.has_checker_visible_contract());
        assert_eq!(transaction.divider_clause_ids, vec![11, 12]);
        assert_eq!(transaction.blocked_clause_id, 13);
        assert_eq!(transaction.blocked_signed_lrat_hints, vec![-11, -12]);
        assert_eq!(transaction.quotient_clause_ids, vec![14, 15, 16]);
        assert_eq!(
            transaction.quotient_lrat_hints,
            vec![vec![1, 2, 13], vec![3, 4, 13], vec![5, 6, 13]]
        );

        let obligation = dry_run
            .into_obligation()
            .expect("dry run should emit a checker-visible obligation");
        assert_eq!(
            obligation.extra["transform.contract_version"],
            "ay.factor-extension-lrat-transaction.v1"
        );
        assert_eq!(
            obligation.extra["factor.addition_order"],
            "dividers,blocked,quotients,delete-blocked,delete-sources"
        );
        assert!(obligation.fingerprint_is_current());
    }

    #[test]
    fn factor_extension_lrat_dry_run_matches_minimal_clique_factor_fixture() {
        let fixture = minimal_clique_factor_fixture();
        assert_eq!(
            fixture.source_dimacs(),
            concat!(
                "p cnf 5 6\n",
                "1 3 4 0\n",
                "2 3 4 0\n",
                "1 3 5 0\n",
                "2 3 5 0\n",
                "1 4 5 0\n",
                "2 4 5 0\n",
            )
        );

        let dry_run = fixture.dry_run();
        assert_eq!(
            dry_run.source_clause_lits_quotient_major,
            fixture.source_clause_lits_quotient_major()
        );
        assert_eq!(
            dry_run.quotient_clauses,
            vec![vec![-6, 3, 4], vec![-6, 3, 5], vec![-6, 4, 5]]
        );

        let transaction = FactorExtensionLratTransaction::from_dry_run_parts(dry_run.clone())
            .expect("minimal clique factor dry-run should build a transaction");
        assert!(transaction.has_checker_visible_contract());
        assert_eq!(transaction.num_vars, 5);
        assert_eq!(transaction.num_clauses, 6);
        assert_eq!(transaction.fresh_lit, 6);
        assert_eq!(transaction.factors, vec![1, 2]);
        assert_eq!(
            transaction.quotient_tails,
            vec![vec![3, 4], vec![3, 5], vec![4, 5]]
        );
        assert_eq!(
            transaction.source_clause_ids_quotient_major,
            vec![21, 22, 23, 24, 25, 26]
        );
        assert_eq!(transaction.source_delete_ids, vec![21, 22, 23, 24, 25, 26]);
        assert_eq!(transaction.divider_clause_ids, vec![31, 32]);
        assert_eq!(transaction.divider_rat_pivots, vec![6, 6]);
        assert_eq!(transaction.blocked_clause_id, 33);
        assert_eq!(transaction.blocked_signed_lrat_hints, vec![-31, -32]);
        assert_eq!(transaction.quotient_clause_ids, vec![34, 35, 36]);
        assert_eq!(
            transaction.quotient_lrat_hints,
            vec![vec![21, 22, 33], vec![23, 24, 33], vec![25, 26, 33]]
        );

        let obligation = dry_run
            .into_obligation()
            .expect("minimal clique fixture should emit an obligation");
        assert_eq!(obligation.formula.num_vars, Some(5));
        assert_eq!(obligation.formula.num_clauses, Some(6));
        assert_eq!(obligation.formula.max_width, Some(3));
        assert!(obligation
            .benchmark
            .tags
            .iter()
            .any(|tag| tag == "clique-shaped"));
        assert_eq!(
            obligation.extra["factor.source_clause_lits_quotient_major"],
            "1,3,4;2,3,4;1,3,5;2,3,5;1,4,5;2,4,5"
        );
        assert_eq!(
            obligation.extra["factor.quotient_clause_lits"],
            "-6,3,4;-6,3,5;-6,4,5"
        );
        assert_eq!(
            obligation.extra["factor.quotient_lrat_hints"],
            "21,22,33;23,24,33;25,26,33"
        );
        assert!(obligation.fingerprint_is_current());
    }

    #[test]
    fn factor_extension_lrat_dry_run_fails_closed_on_incomplete_planned_ids() {
        let mut dry_run = sample_factor_dry_run();
        dry_run.planned_add_ids = vec![11, 12, 14, 15, 16];

        assert!(dry_run.into_transaction().is_none());
    }

    #[test]
    fn proof_replay_open_obligation_projection_matches_sat_pb_schema_contract() {
        let obligation = sample_obligation();
        let proof_replay_request = project_to_proof_replay_open_obligation_json(&obligation);

        assert_eq!(
            proof_replay_request["schema_version"],
            PROOF_REPLAY_OPEN_OBLIGATION_SCHEMA_VERSION
        );
        assert_eq!(proof_replay_request["domain_profile"], "sat-pb");
        assert_eq!(proof_replay_request["trust_policy"], "constructive-only");
        assert_eq!(
            proof_replay_request["min_schema_version"],
            PROOF_REPLAY_PROOF_STATE_SCHEMA_VERSION
        );
        assert_eq!(
            proof_replay_request["max_schema_version"],
            PROOF_REPLAY_PROOF_STATE_SCHEMA_VERSION
        );
        assert_eq!(proof_replay_request["ttl_sec"], 600);
        assert_eq!(proof_replay_request["max_states"], 4096);

        let goal = proof_replay_request
            .get("goal")
            .expect("Lean 4 request should include goal payload");
        assert_eq!(goal["type_pp"], "Prop");
        assert!(
            goal["pretty"]
                .as_str()
                .expect("goal pretty should be a string")
                .contains("unsat_certificate_sound"),
            "goal pretty should preserve ay goal kind for deterministic routing: {goal:?}"
        );

        let artifacts = proof_replay_request["artifact_refs"]
            .as_array()
            .expect("artifact_refs should be an array");
        assert_eq!(artifacts.len(), 2);
        assert_eq!(artifacts[0]["kind"], "dimacs");
        assert_eq!(artifacts[0]["path"], "benchmarks/sat/php21.cnf");
        assert_eq!(artifacts[0]["media_type"], "application/dimacs+cnf");
        assert_eq!(artifacts[1]["kind"], "lrat");
        assert_eq!(artifacts[1]["path"], "artifacts/php21/proof.lrat");
        assert_eq!(artifacts[1]["media_type"], "text/x-lrat");

        for artifact in artifacts {
            let digest = artifact["sha256"]
                .as_str()
                .expect("Lean 4 artifact sha256 should be a string");
            assert_eq!(
                digest.len(),
                64,
                "Lean 4 OpenObligation artifact refs use bare lowercase SHA-256 hex"
            );
            assert!(
                digest
                    .chars()
                    .all(|c| c.is_ascii_hexdigit() && !c.is_ascii_uppercase()),
                "digest should be lowercase hex: {digest}"
            );
        }
    }

    fn project_to_proof_replay_open_obligation_json(obligation: &SatPbProofObligation) -> Value {
        assert_eq!(obligation.domain_profile, ObligationDomainProfile::SatPb);

        json!({
            "schema_version": PROOF_REPLAY_OPEN_OBLIGATION_SCHEMA_VERSION,
            "environment_id": obligation
                .extra
                .get("proof_replay_environment_id")
                .cloned()
                .unwrap_or_else(|| "env_blake3_sat_pb_placeholder".to_string()),
            "domain_profile": "sat-pb",
            "goal": {
                "pretty": format!(
                    "ay SAT/PB {} obligation {}",
                    goal_kind_name(obligation.goal_kind),
                    obligation.obligation_id
                ),
                "type_pp": "Prop",
            },
            "local_context": [],
            "artifact_refs": obligation
                .artifacts
                .iter()
                .map(project_artifact_ref_to_proof_replay_json)
                .collect::<Vec<_>>(),
            "trust_policy": if obligation.trust_policy.require_zero_trust {
                "constructive-only"
            } else {
                "allow-trusted-arith"
            },
            "ttl_sec": 600,
            "max_states": 4096,
            "min_schema_version": PROOF_REPLAY_PROOF_STATE_SCHEMA_VERSION,
            "max_schema_version": PROOF_REPLAY_PROOF_STATE_SCHEMA_VERSION,
        })
    }

    fn project_artifact_ref_to_proof_replay_json(artifact: &ArtifactRef) -> Value {
        json!({
            "kind": proof_replay_artifact_kind(artifact),
            "sha256": artifact.sha256.as_deref().and_then(strip_sha256_prefix),
            "path": &artifact.uri,
            "media_type": artifact.media_type.as_deref(),
        })
    }

    fn proof_replay_artifact_kind(artifact: &ArtifactRef) -> &'static str {
        match artifact.media_type.as_deref() {
            Some("application/opb") | Some("text/x-opb") => "opb",
            Some("text/x-veripb") => "veripb",
            Some("application/dimacs+cnf") | Some("text/x-dimacs") => "dimacs",
            Some("text/x-lrat") => "lrat",
            Some("text/x-drat") => "drat",
            _ => "other",
        }
    }

    fn strip_sha256_prefix(digest: &str) -> Option<&str> {
        digest.strip_prefix("sha256:").or(Some(digest))
    }
}

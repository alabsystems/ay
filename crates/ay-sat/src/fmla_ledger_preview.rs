// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Read-only Fmla guarded-equivalence preprocessing-ledger preview.
//!
//! This module maps audited `FmlaGuardedEquivScout` counters into the ledger
//! transaction classes described by W52/W55/W58. It is diagnostic only: it
//! does not route solving, mutate clauses, allocate proof IDs, or record model
//! reconstruction state.

use crate::fmla_guarded_equiv_scout::{FmlaGuardedEquivRejection, FmlaGuardedEquivScout};
use std::collections::BTreeMap;

const BYTES_PER_GUARD_GROUP_EVIDENCE: usize = 184;
const BYTES_PER_GUARDED_EQUIVALENCE_EVIDENCE: usize = 64;
const BYTES_PER_MODEL_WITNESS_STUB: usize = 16;
const BYTES_PER_TOUCHED_VAR_INDEX: usize = 4;

const FMLA_FAIL_CLOSED_CRITERIA: &[&str] = &[
    "require-visible-onehot-support-and-mutex-source-ids",
    "require-two-directional-ternary-source-ids-per-guarded-equivalence",
    "require-original-dimacs-model-reconstruction-witnesses-before-any-elimination",
    "require-checker-visible-unsat-proof-plan-before-any-clause-deletion-or-rewrite",
];

const CONTROL_FAIL_CLOSED_CRITERIA: &[&str] =
    &["no-width-six-onehot-groups", "no-guarded-equivalence-pairs"];

/// Stable transaction-class name for one-hot guard-group evidence.
pub const FMLA_GUARD_GROUP_EVIDENCE: &str = "FmlaGuardGroupEvidence";
/// Stable transaction-class name for guarded-equivalence source evidence.
pub const FMLA_GUARDED_EQUIVALENCE_EVIDENCE: &str = "FmlaGuardedEquivalenceEvidence";
/// Stable transaction-class name for future guarded-equivalence rewrite plans.
pub const FMLA_GUARDED_EQUIVALENCE_REWRITE_PLAN: &str = "FmlaGuardedEquivalenceRewritePlan";

/// Read-only source-count preview for the Fmla ledger plan.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FmlaLedgerPreviewCounts {
    /// One-hot guard-group transactions.
    pub guard_group_transactions: usize,
    /// Pairwise mutex source-clause witnesses across all one-hot groups.
    pub mutex_source_clause_witnesses: usize,
    /// Guarded-equivalence evidence transactions.
    pub guarded_equivalence_transactions: usize,
    /// Directional ternary source-clause witnesses.
    pub directional_ternary_clause_witnesses: usize,
    /// Variables touched by a future destructive guarded-equivalence transform.
    pub touched_vars: usize,
    /// Original-DIMACS model witnesses required before substitution/elimination.
    pub model_reconstruction_witnesses_if_substituted: usize,
}

/// Payload-sized memory estimate for the preview.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FmlaLedgerPreviewMemoryEstimate {
    /// Bytes for one-hot guard-group evidence payloads.
    pub guard_group_evidence_bytes: usize,
    /// Bytes for guarded-equivalence evidence payloads.
    pub guarded_equivalence_evidence_bytes: usize,
    /// Bytes for model-witness stubs.
    pub model_witness_stub_bytes: usize,
    /// Bytes for touched-variable indexes.
    pub touched_var_index_bytes: usize,
    /// Total estimated payload bytes.
    pub total_bytes: usize,
}

impl FmlaLedgerPreviewMemoryEstimate {
    /// Total estimated payload size in MiB, rounded to three decimals.
    #[must_use]
    pub fn total_mib_x1000(self) -> usize {
        (self.total_bytes * 1000 + (1024 * 1024 / 2)) / (1024 * 1024)
    }
}

/// Read-only transaction-class preview row.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FmlaLedgerPreviewTransactionClass {
    /// Stable transaction-class name.
    pub transaction_class: &'static str,
    /// Number of preview records in this class.
    pub count: usize,
    /// Distinct touched-variable count associated with this class.
    pub touched_vars: usize,
}

/// Read-only Fmla guarded-equivalence ledger preview.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FmlaLedgerPreview {
    /// True when the scout detected the Fmla guarded-equivalence packet.
    pub detected_packet: bool,
    /// Source-count preview.
    pub source_counts: FmlaLedgerPreviewCounts,
    /// Guard variables with detected guarded equivalences.
    pub guard_vars_with_equivalences: usize,
    /// Endpoint variables used by detected guarded equivalences.
    pub endpoint_vars: usize,
    /// One-hot width histogram copied from the scout.
    pub onehot_width_hist: BTreeMap<usize, usize>,
    /// Guard fanout histogram copied from the scout.
    pub guard_fanout_hist: BTreeMap<usize, usize>,
    /// Payload-sized memory estimate.
    pub memory_estimate: FmlaLedgerPreviewMemoryEstimate,
    /// Preview transaction classes.
    pub transaction_classes: Vec<FmlaLedgerPreviewTransactionClass>,
    /// Stable fail-closed criteria for this preview.
    pub fail_closed_criteria: Vec<&'static str>,
    /// Scout rejection retained for controls and diagnostics.
    pub rejection: FmlaGuardedEquivRejection,
}

impl FmlaLedgerPreview {
    /// Build a read-only ledger preview from scout counters.
    #[must_use]
    pub fn from_scout(scout: &FmlaGuardedEquivScout) -> Self {
        let detected_packet = scout.detected();
        let guard_group_transactions = scout.onehot_groups;
        let mutex_source_clause_witnesses = mutex_witness_count(&scout.onehot_width_hist);
        let guarded_equivalence_transactions = scout.guarded_equivalence_pairs;
        let directional_ternary_clause_witnesses =
            guarded_equivalence_transactions.saturating_mul(2);
        let guard_vars_with_equivalences = if detected_packet {
            scout.guarded_equivalence_guards
        } else {
            0
        };
        let endpoint_vars = if detected_packet {
            scout.num_vars.saturating_sub(guard_vars_with_equivalences)
        } else {
            0
        };
        let touched_vars = if detected_packet {
            guard_vars_with_equivalences.saturating_add(endpoint_vars)
        } else {
            0
        };
        let model_reconstruction_witnesses_if_substituted = touched_vars;
        let source_counts = FmlaLedgerPreviewCounts {
            guard_group_transactions,
            mutex_source_clause_witnesses,
            guarded_equivalence_transactions,
            directional_ternary_clause_witnesses,
            touched_vars,
            model_reconstruction_witnesses_if_substituted,
        };
        let memory_estimate = memory_estimate(&source_counts);
        let transaction_classes = vec![
            FmlaLedgerPreviewTransactionClass {
                transaction_class: FMLA_GUARD_GROUP_EVIDENCE,
                count: guard_group_transactions,
                touched_vars: scout.onehot_variables,
            },
            FmlaLedgerPreviewTransactionClass {
                transaction_class: FMLA_GUARDED_EQUIVALENCE_EVIDENCE,
                count: guarded_equivalence_transactions,
                touched_vars,
            },
            FmlaLedgerPreviewTransactionClass {
                transaction_class: FMLA_GUARDED_EQUIVALENCE_REWRITE_PLAN,
                count: guarded_equivalence_transactions,
                touched_vars,
            },
        ];
        let fail_closed_criteria = if detected_packet {
            FMLA_FAIL_CLOSED_CRITERIA.to_vec()
        } else {
            CONTROL_FAIL_CLOSED_CRITERIA.to_vec()
        };

        Self {
            detected_packet,
            source_counts,
            guard_vars_with_equivalences,
            endpoint_vars,
            onehot_width_hist: scout.onehot_width_hist.clone(),
            guard_fanout_hist: scout.guarded_equivalence_guard_fanout_hist.clone(),
            memory_estimate,
            transaction_classes,
            fail_closed_criteria,
            rejection: scout.rejection,
        }
    }
}

fn mutex_witness_count(width_hist: &BTreeMap<usize, usize>) -> usize {
    width_hist
        .iter()
        .map(|(width, groups)| width.saturating_mul(width.saturating_sub(1)) / 2 * groups)
        .sum()
}

fn memory_estimate(counts: &FmlaLedgerPreviewCounts) -> FmlaLedgerPreviewMemoryEstimate {
    let guard_group_evidence_bytes =
        counts.guard_group_transactions * BYTES_PER_GUARD_GROUP_EVIDENCE;
    let guarded_equivalence_evidence_bytes =
        counts.guarded_equivalence_transactions * BYTES_PER_GUARDED_EQUIVALENCE_EVIDENCE;
    let model_witness_stub_bytes =
        counts.model_reconstruction_witnesses_if_substituted * BYTES_PER_MODEL_WITNESS_STUB;
    let touched_var_index_bytes = counts.touched_vars * BYTES_PER_TOUCHED_VAR_INDEX;
    let total_bytes = guard_group_evidence_bytes
        + guarded_equivalence_evidence_bytes
        + model_witness_stub_bytes
        + touched_var_index_bytes;

    FmlaLedgerPreviewMemoryEstimate {
        guard_group_evidence_bytes,
        guarded_equivalence_evidence_bytes,
        model_witness_stub_bytes,
        touched_var_index_bytes,
        total_bytes,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fmla_guarded_equiv_scout::FmlaGuardedEquivScout;
    use crate::literal::Variable;
    use crate::{parse_dimacs, Literal};
    use std::path::Path;

    fn pos(var: usize) -> Literal {
        Literal::positive(Variable(var as u32))
    }

    fn neg(var: usize) -> Literal {
        Literal::negative(Variable(var as u32))
    }

    fn guarded_fixture() -> Vec<Vec<Literal>> {
        let mut clauses = vec![(0..6).map(pos).collect()];
        for lhs in 0..6 {
            for rhs in (lhs + 1)..6 {
                clauses.push(vec![neg(lhs), neg(rhs)]);
            }
        }
        clauses.push(vec![neg(0), neg(6), pos(7)]);
        clauses.push(vec![neg(0), neg(7), pos(6)]);
        clauses
    }

    #[test]
    fn fmla_guarded_equiv_ledger_preview_fixture_is_read_only() {
        let clauses = guarded_fixture();
        let before = clauses.clone();
        let scout = FmlaGuardedEquivScout::scan(8, &clauses);
        let preview = FmlaLedgerPreview::from_scout(&scout);

        assert_eq!(clauses, before, "ledger preview must be read-only");
        assert!(preview.detected_packet);
        assert_eq!(preview.source_counts.guard_group_transactions, 1);
        assert_eq!(preview.source_counts.mutex_source_clause_witnesses, 15);
        assert_eq!(preview.source_counts.guarded_equivalence_transactions, 1);
        assert_eq!(
            preview.source_counts.directional_ternary_clause_witnesses,
            2
        );
        assert_eq!(preview.guard_vars_with_equivalences, 1);
        assert_eq!(preview.endpoint_vars, 7);
        assert_eq!(preview.source_counts.touched_vars, 8);
        assert_eq!(
            preview
                .source_counts
                .model_reconstruction_witnesses_if_substituted,
            8
        );
    }

    #[test]
    fn fmla_guarded_equiv_ledger_preview_locks_w58_counts() {
        let Some(formula) = parse_optional_xz_fixture(
            "../../benchmarks/sat/satcomp2024-sample/\
             9cd3acdb765c15163bc239ae3a57f880-FmlaEquivChain_4_6_6.sanitized.cnf.xz",
        ) else {
            return;
        };
        let scout = FmlaGuardedEquivScout::scan(formula.num_vars, &formula.clauses);
        let preview = FmlaLedgerPreview::from_scout(&scout);

        eprintln!(
            "fmla_guarded_equiv_ledger_preview fmla guard_group_transactions={} guarded_equivalence_transactions={} directional_ternary_clause_witnesses={} touched_vars={} memory_total_bytes={} memory_total_mib_x1000={}",
            preview.source_counts.guard_group_transactions,
            preview.source_counts.guarded_equivalence_transactions,
            preview.source_counts.directional_ternary_clause_witnesses,
            preview.source_counts.touched_vars,
            preview.memory_estimate.total_bytes,
            preview.memory_estimate.total_mib_x1000()
        );

        assert!(preview.detected_packet);
        assert_eq!(preview.source_counts.guard_group_transactions, 7_770);
        assert_eq!(preview.source_counts.mutex_source_clause_witnesses, 116_550);
        assert_eq!(
            preview.source_counts.guarded_equivalence_transactions,
            155_520
        );
        assert_eq!(
            preview.source_counts.directional_ternary_clause_witnesses,
            311_040
        );
        assert_eq!(preview.guard_vars_with_equivalences, 27_195);
        assert_eq!(preview.endpoint_vars, 27_216);
        assert_eq!(preview.source_counts.touched_vars, 54_411);
        assert_eq!(
            preview
                .source_counts
                .model_reconstruction_witnesses_if_substituted,
            54_411
        );
        assert_eq!(preview.onehot_width_hist, BTreeMap::from([(6, 7_770)]));
        assert_eq!(
            preview.guard_fanout_hist,
            BTreeMap::from([
                (1, 6_480),
                (2, 16_200),
                (6, 1_080),
                (12, 2_700),
                (36, 180),
                (72, 450),
                (216, 30),
                (432, 75),
            ])
        );
        assert_eq!(preview.memory_estimate.total_bytes, 12_471_180);
        assert_eq!(preview.memory_estimate.total_mib_x1000(), 11_893);
        assert_eq!(
            class_counts(&preview),
            BTreeMap::from([
                (FMLA_GUARD_GROUP_EVIDENCE, 7_770),
                (FMLA_GUARDED_EQUIVALENCE_EVIDENCE, 155_520),
                (FMLA_GUARDED_EQUIVALENCE_REWRITE_PLAN, 155_520),
            ])
        );
        assert_eq!(preview.fail_closed_criteria, FMLA_FAIL_CLOSED_CRITERIA);
    }

    #[test]
    fn fmla_guarded_equiv_ledger_preview_controls_fail_closed_zero() {
        let Some(clique) = parse_optional_xz_fixture(
            "../../benchmarks/sat/satcomp2024-sample/\
             cb2e8b7fada420c5046f587ea754d052-clique_n2_k10.sanitized.cnf.xz",
        ) else {
            return;
        };
        let clique_preview = FmlaLedgerPreview::from_scout(&FmlaGuardedEquivScout::scan(
            clique.num_vars,
            &clique.clauses,
        ));
        assert_control_preview(&clique_preview, 10, 1_530);

        let circuit = parse_required_xz_fixture(
            "../../benchmarks/sat/satcomp2024-sample/\
             c5ae0ec49de0959cd14431ce851c14f8-Circuit_multiplier22.cnf.xz",
        );
        let circuit_preview = FmlaLedgerPreview::from_scout(&FmlaGuardedEquivScout::scan(
            circuit.num_vars,
            &circuit.clauses,
        ));
        assert_control_preview(&circuit_preview, 2, 2);
    }

    fn assert_control_preview(
        preview: &FmlaLedgerPreview,
        expected_guard_groups: usize,
        expected_mutex_witnesses: usize,
    ) {
        assert!(!preview.detected_packet);
        assert_eq!(
            preview.source_counts.guard_group_transactions,
            expected_guard_groups
        );
        assert_eq!(
            preview.source_counts.mutex_source_clause_witnesses,
            expected_mutex_witnesses
        );
        assert_eq!(preview.source_counts.guarded_equivalence_transactions, 0);
        assert_eq!(
            preview.source_counts.directional_ternary_clause_witnesses,
            0
        );
        assert_eq!(preview.guard_vars_with_equivalences, 0);
        assert_eq!(preview.endpoint_vars, 0);
        assert_eq!(preview.source_counts.touched_vars, 0);
        assert_eq!(
            preview
                .source_counts
                .model_reconstruction_witnesses_if_substituted,
            0
        );
        assert_eq!(
            class_counts(preview).get(FMLA_GUARDED_EQUIVALENCE_EVIDENCE),
            Some(&0)
        );
        assert_eq!(
            class_counts(preview).get(FMLA_GUARDED_EQUIVALENCE_REWRITE_PLAN),
            Some(&0)
        );
        assert_eq!(preview.fail_closed_criteria, CONTROL_FAIL_CLOSED_CRITERIA);
    }

    fn class_counts(preview: &FmlaLedgerPreview) -> BTreeMap<&'static str, usize> {
        preview
            .transaction_classes
            .iter()
            .map(|class| (class.transaction_class, class.count))
            .collect()
    }

    fn parse_optional_xz_fixture(relative_path: &str) -> Option<crate::DimacsFormula> {
        let path = Path::new(env!("CARGO_MANIFEST_DIR")).join(relative_path);
        if !path.exists() {
            eprintln!("Fmla ledger preview fixture missing: {}", path.display());
            return None;
        }
        let content = String::from_utf8(crate::test_xz::decompress_xz_path(&path)?)
            .expect("fixture is UTF-8 DIMACS");
        Some(parse_dimacs(&content).expect("parse DIMACS fixture"))
    }

    fn parse_required_xz_fixture(relative_path: &str) -> crate::DimacsFormula {
        let path = Path::new(env!("CARGO_MANIFEST_DIR")).join(relative_path);
        let content = String::from_utf8(crate::test_xz::decompress_required_xz_path(&path))
            .expect("required tracked fixture is UTF-8 DIMACS");
        parse_dimacs(&content).expect("parse required tracked DIMACS fixture")
    }
}

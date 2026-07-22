// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SAT guidance v2 compatibility fingerprints and import decisions.

use crate::literal::Literal;
use std::fmt;

/// Stable format marker for SAT guidance v2 payloads.
pub const SAT_GUIDANCE_V2_FORMAT: &str = "ay-sat-guidance-v2";

const FNV_OFFSET: u64 = 0xcbf2_9ce4_8422_2325;
const FNV_PRIME: u64 = 0x0000_0100_0000_01b3;

/// Formula fingerprints used to decide how much SAT guidance may be imported.
///
/// The exact digest is order-sensitive and is the only compatibility layer
/// that permits learned-clause replay without independent proof evidence.
/// The other layers are diagnostics for downgrade/rejection decisions.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[non_exhaustive]
pub struct SatGuidanceFingerprint {
    /// Number of user-visible variables in the producer formula.
    pub num_vars: usize,
    /// Number of original clauses in the producer formula.
    pub num_clauses: usize,
    /// Number of original literals across all clauses.
    pub num_literals: usize,
    /// Order-sensitive DIMACS-style digest of the original clause ledger.
    pub exact_dimacs_digest: u64,
    /// Order-insensitive digest of the original clause multiset.
    pub clause_multiset_digest: u64,
    /// Digest after canonical variable renumbering over the clause multiset.
    pub literal_normalized_digest: u64,
    /// Digest of the current variable map; today this is the identity map.
    pub variable_map_digest: u64,
    /// Digest of preprocessing state relevant to replay compatibility.
    pub preprocessing_ledger_digest: u64,
    /// Coarse profile digest for quick mismatch diagnostics.
    pub profile_digest: u64,
}

impl SatGuidanceFingerprint {
    /// Build a fingerprint from explicit original clauses.
    pub fn from_clauses(num_vars: usize, clauses: &[Vec<Literal>]) -> Self {
        Self::from_clause_iter(num_vars, clauses.iter().map(Vec::as_slice))
    }

    pub(crate) fn from_clause_iter<'a, I>(num_vars: usize, clauses: I) -> Self
    where
        I: IntoIterator<Item = &'a [Literal]>,
    {
        let clauses: Vec<Vec<Literal>> = clauses.into_iter().map(<[Literal]>::to_vec).collect();
        let num_clauses = clauses.len();
        let num_literals = clauses.iter().map(Vec::len).sum();

        let exact_dimacs_digest = exact_dimacs_digest(num_vars, &clauses);
        let clause_multiset_digest = clause_multiset_digest(num_vars, &clauses);
        let literal_normalized_digest = literal_normalized_digest(&clauses);
        let variable_map_digest = variable_map_digest(num_vars);
        let preprocessing_ledger_digest =
            preprocessing_ledger_digest(exact_dimacs_digest, clause_multiset_digest);
        let profile_digest = profile_digest(num_vars, num_clauses, num_literals, &clauses);

        Self {
            num_vars,
            num_clauses,
            num_literals,
            exact_dimacs_digest,
            clause_multiset_digest,
            literal_normalized_digest,
            variable_map_digest,
            preprocessing_ledger_digest,
            profile_digest,
        }
    }

    /// Classify import compatibility between this producer and a current formula.
    #[must_use]
    pub fn classify_import(&self, current: &Self) -> SatGuidanceImportDecision {
        if self.exact_dimacs_digest == current.exact_dimacs_digest
            && self.variable_map_digest == current.variable_map_digest
            && self.preprocessing_ledger_digest == current.preprocessing_ledger_digest
            && self.profile_digest == current.profile_digest
        {
            return SatGuidanceImportDecision {
                level: SatGuidanceImportLevel::ExactReplayHints,
                reason: SatGuidanceImportReason::ExactReplayCompatible,
            };
        }

        if self.profile_digest != current.profile_digest
            || self.num_vars != current.num_vars
            || self.num_clauses != current.num_clauses
            || self.num_literals != current.num_literals
        {
            return SatGuidanceImportDecision {
                level: SatGuidanceImportLevel::HeuristicHintsOnly,
                reason: SatGuidanceImportReason::FormulaProfileChanged,
            };
        }

        if self.clause_multiset_digest == current.clause_multiset_digest {
            return SatGuidanceImportDecision {
                level: SatGuidanceImportLevel::HeuristicHintsOnly,
                reason: SatGuidanceImportReason::ClauseOrderChanged,
            };
        }

        // The persisted map digest is identity today. A normalized match after
        // exact/multiset mismatch means a non-identity remap would be required.
        if self.literal_normalized_digest == current.literal_normalized_digest {
            return SatGuidanceImportDecision {
                level: SatGuidanceImportLevel::HeuristicHintsOnly,
                reason: SatGuidanceImportReason::VariableMapChanged,
            };
        }

        SatGuidanceImportDecision {
            level: SatGuidanceImportLevel::Reject,
            reason: SatGuidanceImportReason::FormulaTampered,
        }
    }
}

/// Import level chosen for a guidance payload.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[non_exhaustive]
pub enum SatGuidanceImportLevel {
    /// Import nothing from the guidance payload.
    Reject,
    /// Import only heuristic hints such as activities and saved phases.
    #[default]
    HeuristicHintsOnly,
    /// Exact formula replay; learned clauses may be replayed as hints.
    ExactReplayHints,
    /// Learned clauses were independently proof checked before insertion.
    ProofCheckedLearnedClauses,
}

impl SatGuidanceImportLevel {
    /// Whether this level permits heuristic hints such as saved phases or activities.
    #[must_use]
    pub fn imports_heuristic_hints(self) -> bool {
        !matches!(self, Self::Reject)
    }

    /// Whether this level permits learned-clause insertion.
    #[must_use]
    pub fn imports_learned_clauses(self) -> bool {
        matches!(
            self,
            Self::ExactReplayHints | Self::ProofCheckedLearnedClauses
        )
    }
}

impl fmt::Display for SatGuidanceImportLevel {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Reject => f.write_str("reject"),
            Self::HeuristicHintsOnly => f.write_str("heuristic-hints-only"),
            Self::ExactReplayHints => f.write_str("exact-replay-hints"),
            Self::ProofCheckedLearnedClauses => f.write_str("proof-checked-learned-clauses"),
        }
    }
}

/// Reason attached to a guidance import decision.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[non_exhaustive]
pub enum SatGuidanceImportReason {
    /// Producer and consumer fingerprints are exact-replay compatible.
    ExactReplayCompatible,
    /// The payload had no v2 fingerprint, so it is treated as legacy guidance.
    #[default]
    LegacyGuidanceMissingFingerprint,
    /// Clause content matched as a multiset, but the exact clause order changed.
    ClauseOrderChanged,
    /// Variable, clause, or literal profile changed.
    FormulaProfileChanged,
    /// Formula content changed while the coarse profile stayed compatible.
    FormulaTampered,
    /// A non-identity variable map would be needed for exact replay.
    VariableMapChanged,
    /// Learned clauses require proof evidence before import.
    ProofEvidenceRequired,
}

impl fmt::Display for SatGuidanceImportReason {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ExactReplayCompatible => f.write_str("exact-replay-compatible"),
            Self::LegacyGuidanceMissingFingerprint => {
                f.write_str("legacy-guidance-missing-fingerprint")
            }
            Self::ClauseOrderChanged => f.write_str("clause-order-changed"),
            Self::FormulaProfileChanged => f.write_str("formula-profile-changed"),
            Self::FormulaTampered => f.write_str("formula-tampered"),
            Self::VariableMapChanged => f.write_str("variable-map-changed"),
            Self::ProofEvidenceRequired => f.write_str("proof-evidence-required"),
        }
    }
}

/// Decision returned by guidance compatibility checks.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[non_exhaustive]
pub struct SatGuidanceImportDecision {
    /// Maximum guidance import level allowed for the payload.
    pub level: SatGuidanceImportLevel,
    /// Why this import level was selected.
    pub reason: SatGuidanceImportReason,
}

impl SatGuidanceImportDecision {
    /// Decision for legacy v1 guidance that has no formula fingerprint.
    #[must_use]
    pub fn legacy_v1() -> Self {
        Self {
            level: SatGuidanceImportLevel::HeuristicHintsOnly,
            reason: SatGuidanceImportReason::LegacyGuidanceMissingFingerprint,
        }
    }
}

fn exact_dimacs_digest(num_vars: usize, clauses: &[Vec<Literal>]) -> u64 {
    let mut state = tagged_state("sat-guidance-exact-dimacs-v1");
    mix_u64(&mut state, num_vars as u64);
    mix_u64(&mut state, clauses.len() as u64);
    for clause in clauses {
        mix_u64(&mut state, clause.len() as u64);
        for &lit in clause {
            mix_i64(&mut state, i64::from(lit.to_dimacs()));
        }
    }
    finish(state)
}

fn clause_multiset_digest(num_vars: usize, clauses: &[Vec<Literal>]) -> u64 {
    let mut clause_hashes: Vec<u64> = clauses
        .iter()
        .map(|clause| {
            let mut lits: Vec<i32> = clause.iter().map(|lit| lit.to_dimacs()).collect();
            lits.sort_unstable();
            let mut state = tagged_state("sat-guidance-clause-v1");
            mix_u64(&mut state, lits.len() as u64);
            for lit in lits {
                mix_i64(&mut state, i64::from(lit));
            }
            finish(state)
        })
        .collect();
    clause_hashes.sort_unstable();

    let mut state = tagged_state("sat-guidance-clause-multiset-v1");
    mix_u64(&mut state, num_vars as u64);
    mix_u64(&mut state, clause_hashes.len() as u64);
    for hash in clause_hashes {
        mix_u64(&mut state, hash);
    }
    finish(state)
}

fn literal_normalized_digest(clauses: &[Vec<Literal>]) -> u64 {
    let mut canonical: Vec<Vec<i32>> = clauses
        .iter()
        .map(|clause| {
            let mut lits: Vec<i32> = clause.iter().map(|lit| lit.to_dimacs()).collect();
            lits.sort_unstable();
            lits
        })
        .collect();
    canonical.sort_unstable();

    let mut var_map = Vec::<u32>::new();
    let mut state = tagged_state("sat-guidance-literal-normalized-v1");
    mix_u64(&mut state, canonical.len() as u64);
    for clause in canonical {
        mix_u64(&mut state, clause.len() as u64);
        for lit in clause {
            let var = lit.unsigned_abs();
            let mapped = match var_map.iter().position(|&seen| seen == var) {
                Some(index) => (index + 1) as i32,
                None => {
                    var_map.push(var);
                    var_map.len() as i32
                }
            };
            let normalized = if lit > 0 { mapped } else { -mapped };
            mix_i64(&mut state, i64::from(normalized));
        }
    }
    finish(state)
}

fn variable_map_digest(num_vars: usize) -> u64 {
    let mut state = tagged_state("sat-guidance-variable-map-identity-v1");
    mix_u64(&mut state, num_vars as u64);
    for var in 0..num_vars {
        mix_u64(&mut state, var as u64);
    }
    finish(state)
}

fn preprocessing_ledger_digest(exact: u64, multiset: u64) -> u64 {
    let mut state = tagged_state("sat-guidance-preprocessing-ledger-none-v1");
    mix_u64(&mut state, exact);
    mix_u64(&mut state, multiset);
    finish(state)
}

fn profile_digest(
    num_vars: usize,
    num_clauses: usize,
    num_literals: usize,
    clauses: &[Vec<Literal>],
) -> u64 {
    let mut min_len = usize::MAX;
    let mut max_len = 0usize;
    let mut len_xor = 0u64;
    for clause in clauses {
        min_len = min_len.min(clause.len());
        max_len = max_len.max(clause.len());
        len_xor ^= clause.len() as u64;
    }
    if clauses.is_empty() {
        min_len = 0;
    }

    let mut state = tagged_state("sat-guidance-profile-v1");
    mix_u64(&mut state, num_vars as u64);
    mix_u64(&mut state, num_clauses as u64);
    mix_u64(&mut state, num_literals as u64);
    mix_u64(&mut state, min_len as u64);
    mix_u64(&mut state, max_len as u64);
    mix_u64(&mut state, len_xor);
    finish(state)
}

fn tagged_state(tag: &str) -> u64 {
    let mut state = FNV_OFFSET;
    for byte in tag.bytes() {
        mix_u64(&mut state, u64::from(byte));
    }
    state
}

fn mix_i64(state: &mut u64, value: i64) {
    mix_u64(state, value as u64);
}

fn mix_u64(state: &mut u64, value: u64) {
    *state ^= value;
    *state = state.wrapping_mul(FNV_PRIME);
}

fn finish(mut state: u64) -> u64 {
    state ^= state >> 33;
    state = state.wrapping_mul(0xff51_afd7_ed55_8ccd);
    state ^= state >> 33;
    state = state.wrapping_mul(0xc4ce_b9fe_1a85_ec53);
    state ^ (state >> 33)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Literal, Variable};

    fn pos(var: u32) -> Literal {
        Literal::positive(Variable::new(var))
    }

    fn neg(var: u32) -> Literal {
        Literal::negative(Variable::new(var))
    }

    #[test]
    fn clause_order_preserves_multiset_but_not_exact_replay() {
        let a = SatGuidanceFingerprint::from_clauses(3, &[vec![pos(0), neg(1)], vec![pos(2)]]);
        let b = SatGuidanceFingerprint::from_clauses(3, &[vec![pos(2)], vec![pos(0), neg(1)]]);

        assert_ne!(a.exact_dimacs_digest, b.exact_dimacs_digest);
        assert_eq!(a.clause_multiset_digest, b.clause_multiset_digest);
        assert_eq!(
            a.classify_import(&b),
            SatGuidanceImportDecision {
                level: SatGuidanceImportLevel::HeuristicHintsOnly,
                reason: SatGuidanceImportReason::ClauseOrderChanged,
            }
        );
    }

    #[test]
    fn same_counts_clause_tamper_rejects_import() {
        let a = SatGuidanceFingerprint::from_clauses(3, &[vec![pos(0), neg(1)], vec![pos(2)]]);
        let b = SatGuidanceFingerprint::from_clauses(3, &[vec![pos(0), pos(1)], vec![pos(2)]]);

        assert_eq!(a.num_vars, b.num_vars);
        assert_eq!(a.num_clauses, b.num_clauses);
        assert_eq!(a.num_literals, b.num_literals);
        assert_ne!(a.exact_dimacs_digest, b.exact_dimacs_digest);
        assert_ne!(a.clause_multiset_digest, b.clause_multiset_digest);
        assert_eq!(
            a.classify_import(&b),
            SatGuidanceImportDecision {
                level: SatGuidanceImportLevel::Reject,
                reason: SatGuidanceImportReason::FormulaTampered,
            }
        );
    }

    #[test]
    fn variable_renumbering_downgrades_without_learned_replay() {
        let a = SatGuidanceFingerprint::from_clauses(2, &[vec![pos(0), neg(1)]]);
        let b = SatGuidanceFingerprint::from_clauses(2, &[vec![pos(1), neg(0)]]);

        assert_ne!(a.exact_dimacs_digest, b.exact_dimacs_digest);
        assert_ne!(a.clause_multiset_digest, b.clause_multiset_digest);
        assert_eq!(a.literal_normalized_digest, b.literal_normalized_digest);

        let decision = a.classify_import(&b);
        assert_eq!(
            decision,
            SatGuidanceImportDecision {
                level: SatGuidanceImportLevel::HeuristicHintsOnly,
                reason: SatGuidanceImportReason::VariableMapChanged,
            }
        );
        assert!(decision.level.imports_heuristic_hints());
        assert!(
            !decision.level.imports_learned_clauses(),
            "renumbered formulas must not replay learned clauses without a proof"
        );
    }

    #[test]
    fn exact_fingerprint_allows_exact_replay_hints() {
        let a =
            SatGuidanceFingerprint::from_clauses(2, &[vec![pos(0), neg(1)], vec![neg(0), pos(1)]]);
        let b =
            SatGuidanceFingerprint::from_clauses(2, &[vec![pos(0), neg(1)], vec![neg(0), pos(1)]]);

        assert_eq!(
            a.classify_import(&b),
            SatGuidanceImportDecision {
                level: SatGuidanceImportLevel::ExactReplayHints,
                reason: SatGuidanceImportReason::ExactReplayCompatible,
            }
        );
    }
}

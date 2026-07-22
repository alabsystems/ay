// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Read-only FmlaEquivChain guarded-equivalence structure scouting.
//!
//! The scout recognizes DIMACS-visible exactly-one guard groups and ternary
//! pairs of the form `g -> (x <-> y)`. It is diagnostic only: it does not
//! simplify clauses, add clauses, delete clauses, derive a verdict, or relax
//! proof/model obligations.

use crate::literal::Literal;
use std::collections::{BTreeMap, BTreeSet};

/// Read-only counters recovered by the Fmla guarded-equivalence scout.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FmlaGuardedEquivScout {
    /// Number of variables declared by the DIMACS header.
    pub num_vars: usize,
    /// Number of clauses supplied to the scout.
    pub num_clauses: usize,
    /// Positive clauses whose variables have all pairwise negative mutexes.
    pub onehot_groups: usize,
    /// Width histogram for recovered exactly-one groups.
    pub onehot_width_hist: BTreeMap<usize, usize>,
    /// Distinct variables covered by recovered exactly-one groups.
    pub onehot_variables: usize,
    /// Recovered guarded equivalences `g -> (x <-> y)`.
    pub guarded_equivalence_pairs: usize,
    /// Distinct one-hot guard variables used by recovered guarded equivalences.
    pub guarded_equivalence_guards: usize,
    /// Histogram of recovered guarded-equivalence fanout per guard.
    pub guarded_equivalence_guard_fanout_hist: BTreeMap<usize, usize>,
    /// Stable fail-closed classification for default-off routing.
    pub rejection: FmlaGuardedEquivRejection,
}

/// Fail-closed reason for the scout not identifying an Fmla guarded-equivalence packet.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FmlaGuardedEquivRejection {
    /// The scout found a guarded-equivalence packet.
    None,
    /// No exactly-one guard groups were recovered.
    NoOnehotGroups,
    /// One-hot groups exist, but not with the Fmla width-6 surface.
    NoWidthSixOnehotGroups,
    /// No paired guarded equivalences were recovered over one-hot guards.
    NoGuardedEquivalencePairs,
}

/// DIMACS-source witness for a recovered exactly-one guard group.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FmlaOneHotGroupWitness {
    /// One-based DIMACS clause id of the positive support clause.
    pub support_clause_id: usize,
    /// Positive DIMACS variables in the guard group.
    pub vars: Vec<i32>,
    /// One-based DIMACS clause ids for all pairwise mutex clauses.
    pub mutex_clause_ids: Vec<usize>,
}

/// DIMACS-source witness for one guarded equivalence `guard -> (lhs <-> rhs)`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FmlaGuardedEquivalenceWitness {
    /// Positive DIMACS guard variable.
    pub guard: i32,
    /// Lower positive DIMACS endpoint variable.
    pub lhs: i32,
    /// Higher positive DIMACS endpoint variable.
    pub rhs: i32,
    /// One-based DIMACS clause id for `-guard -lhs rhs`.
    pub forward_clause_id: usize,
    /// One-based DIMACS clause id for `-guard -rhs lhs`.
    pub reverse_clause_id: usize,
    /// Forward clause literals as they appeared in the input.
    pub forward_clause_lits: Vec<i32>,
    /// Reverse clause literals as they appeared in the input.
    pub reverse_clause_lits: Vec<i32>,
}

/// DIMACS-source witness for one support-cover guarded ternary row.
///
/// For a recovered one-hot support `(g1 v ... v gn)`, this records one source
/// variable `s` where every guard has a directional ternary `-gi -s di`. The
/// implied proof row is `-s v d1 v ... v dn` with LRAT hints equal to the
/// ternary source ids in guard order followed by the support clause id.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FmlaSupportCoverWitness {
    /// One-based DIMACS clause id of the positive support clause.
    pub support_clause_id: usize,
    /// Positive DIMACS guard variables, in support-clause sorted order.
    pub guard_vars: Vec<i32>,
    /// Positive DIMACS source variable common to all guarded ternaries.
    pub source_var: i32,
    /// Positive DIMACS destination variables, aligned with `guard_vars`.
    pub destination_vars: Vec<i32>,
    /// Derived support-cover clause in DIMACS literal form.
    pub clause_lits: Vec<i32>,
    /// Source clause ids for the directional guarded ternaries, aligned with `guard_vars`.
    pub ternary_source_clause_ids: Vec<usize>,
    /// LRAT hints for the derived row: ternary source ids, then `support_clause_id`.
    pub lrat_hints: Vec<usize>,
}

/// Bounded source witnesses recovered by the Fmla guarded-equivalence scout.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FmlaGuardedEquivWitnesses {
    /// Sampled exactly-one guard-group witnesses.
    pub onehot_groups: Vec<FmlaOneHotGroupWitness>,
    /// Sampled guarded-equivalence witnesses.
    pub guarded_equivalences: Vec<FmlaGuardedEquivalenceWitness>,
}

/// All-source visibility audit for guarded-equivalence witnesses.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct FmlaGuardedEquivSourceAudit {
    /// Guarded equivalence pairs checked by the all-source audit.
    pub witness_pairs_checked: usize,
    /// Guarded equivalence pairs whose guard had no recovered exactly-one group.
    pub witness_pairs_missing_guard_group: usize,
    /// Source clause id references checked, counting repeated guard-group witnesses per pair.
    pub source_id_refs_checked: usize,
    /// Unique source clause ids checked across all audited pairs.
    pub unique_source_ids_checked: usize,
    /// Unique source clause ids accepted by the supplied visibility predicate.
    pub source_ids_visible: usize,
    /// Unique source clause ids rejected by the supplied visibility predicate.
    pub source_ids_missing: usize,
    /// First rejected source clause id, or zero when every source id is visible.
    pub first_missing_source_id: usize,
}

impl FmlaGuardedEquivRejection {
    /// Stable numeric code for stats counters.
    #[must_use]
    pub const fn code(self) -> u64 {
        match self {
            Self::None => 0,
            Self::NoOnehotGroups => 1,
            Self::NoWidthSixOnehotGroups => 2,
            Self::NoGuardedEquivalencePairs => 3,
        }
    }

    /// Stable short label for diagnostic messages and reports.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::None => "none",
            Self::NoOnehotGroups => "no-onehot-groups",
            Self::NoWidthSixOnehotGroups => "no-width-six-onehot-groups",
            Self::NoGuardedEquivalencePairs => "no-guarded-equivalence-pairs",
        }
    }
}

impl FmlaGuardedEquivScout {
    /// Scan a CNF for the Fmla guarded-equivalence packet.
    #[must_use]
    pub fn scan(num_vars: usize, clauses: &[Vec<Literal>]) -> Self {
        let binary_set = collect_binary_clause_set(clauses);
        let onehot_groups = collect_onehot_groups(clauses, &binary_set);
        let mut onehot_width_hist = BTreeMap::new();
        let mut onehot_vars = BTreeSet::new();
        for group in &onehot_groups {
            *onehot_width_hist.entry(group.len()).or_insert(0) += 1;
            onehot_vars.extend(group.iter().copied());
        }

        let (guarded_equivalence_pairs, guard_fanout) =
            count_guarded_equivalences(clauses, &onehot_vars);
        let mut guarded_equivalence_guard_fanout_hist = BTreeMap::new();
        for fanout in guard_fanout.values().copied() {
            *guarded_equivalence_guard_fanout_hist
                .entry(fanout)
                .or_insert(0) += 1;
        }

        let rejection = if onehot_groups.is_empty() {
            FmlaGuardedEquivRejection::NoOnehotGroups
        } else if !onehot_width_hist.contains_key(&6) {
            FmlaGuardedEquivRejection::NoWidthSixOnehotGroups
        } else if guarded_equivalence_pairs == 0 {
            FmlaGuardedEquivRejection::NoGuardedEquivalencePairs
        } else {
            FmlaGuardedEquivRejection::None
        };

        Self {
            num_vars,
            num_clauses: clauses.len(),
            onehot_groups: onehot_groups.len(),
            onehot_width_hist,
            onehot_variables: onehot_vars.len(),
            guarded_equivalence_pairs,
            guarded_equivalence_guards: guard_fanout.len(),
            guarded_equivalence_guard_fanout_hist,
            rejection,
        }
    }

    /// True when the read-only packet is present. This is not a solver route.
    #[must_use]
    pub const fn detected(&self) -> bool {
        matches!(self.rejection, FmlaGuardedEquivRejection::None)
    }
}

impl FmlaGuardedEquivWitnesses {
    /// Scan a CNF and retain up to `sample_limit` source witnesses per class.
    ///
    /// This is read-only and preserves the same recognition surface as
    /// [`FmlaGuardedEquivScout::scan`], but retains one-based DIMACS clause ids
    /// needed by proof/model ledger scaffolds.
    #[must_use]
    pub fn scan(clauses: &[Vec<Literal>], sample_limit: usize) -> Self {
        Self::scan_with_limit(clauses, sample_limit)
    }

    /// Scan a CNF and retain every recovered source witness.
    ///
    /// This is read-only. It is intended for fail-closed admission audits before
    /// any future destructive guarded-equivalence transform is allowed.
    #[must_use]
    pub fn scan_all(clauses: &[Vec<Literal>]) -> Self {
        Self::scan_with_limit(clauses, usize::MAX)
    }

    fn scan_with_limit(clauses: &[Vec<Literal>], sample_limit: usize) -> Self {
        if sample_limit == 0 {
            return Self {
                onehot_groups: Vec::new(),
                guarded_equivalences: Vec::new(),
            };
        }

        let binary_ids = collect_binary_clause_id_map(clauses);
        let onehot_groups = collect_onehot_group_witnesses(clauses, &binary_ids);
        let mut onehot_vars = BTreeSet::new();
        for group in &onehot_groups {
            onehot_vars.extend(group.vars.iter().copied());
        }

        Self {
            onehot_groups: onehot_groups.into_iter().take(sample_limit).collect(),
            guarded_equivalences: collect_guarded_equivalence_witnesses(
                clauses,
                &onehot_vars,
                sample_limit,
            ),
        }
    }

    /// Audit source clause ids for every retained guarded-equivalence witness.
    #[must_use]
    pub fn source_audit<F>(&self, mut source_id_visible: F) -> FmlaGuardedEquivSourceAudit
    where
        F: FnMut(usize) -> bool,
    {
        let mut audit = FmlaGuardedEquivSourceAudit {
            witness_pairs_checked: self.guarded_equivalences.len(),
            ..FmlaGuardedEquivSourceAudit::default()
        };
        let mut unique_source_ids = BTreeSet::new();
        let mut guard_groups = BTreeMap::new();
        for group in &self.onehot_groups {
            for &guard in &group.vars {
                guard_groups.entry(guard).or_insert(group);
            }
        }

        for equivalence in &self.guarded_equivalences {
            let Some(group) = guard_groups.get(&equivalence.guard).copied() else {
                audit.witness_pairs_missing_guard_group =
                    audit.witness_pairs_missing_guard_group.saturating_add(1);
                continue;
            };

            let mut source_ids = Vec::with_capacity(3 + group.mutex_clause_ids.len());
            source_ids.push(group.support_clause_id);
            source_ids.extend(group.mutex_clause_ids.iter().copied());
            source_ids.push(equivalence.forward_clause_id);
            source_ids.push(equivalence.reverse_clause_id);

            audit.source_id_refs_checked = audit
                .source_id_refs_checked
                .saturating_add(source_ids.len());
            unique_source_ids.extend(source_ids);
        }

        audit.unique_source_ids_checked = unique_source_ids.len();
        for source_id in unique_source_ids {
            if source_id != 0 && source_id_visible(source_id) {
                audit.source_ids_visible = audit.source_ids_visible.saturating_add(1);
            } else {
                audit.source_ids_missing = audit.source_ids_missing.saturating_add(1);
                if audit.first_missing_source_id == 0 {
                    audit.first_missing_source_id = source_id;
                }
            }
        }
        audit
    }

    /// Find a retained guard group containing `guard`.
    #[must_use]
    pub fn guard_group_for(&self, guard: i32) -> Option<&FmlaOneHotGroupWitness> {
        self.onehot_groups
            .iter()
            .find(|group| group.vars.contains(&guard))
    }

    /// Recover deterministic support-cover rows from retained witnesses.
    ///
    /// The rows are read-only proof candidates: they do not claim a solver
    /// rewrite, model reconstruction, or guard assignment. The caller remains
    /// responsible for checking source-id visibility before emitting proof rows.
    #[must_use]
    pub fn support_cover_witnesses(&self) -> Vec<FmlaSupportCoverWitness> {
        collect_support_cover_witnesses(&self.onehot_groups, &self.guarded_equivalences)
    }
}

fn collect_binary_clause_set(clauses: &[Vec<Literal>]) -> BTreeSet<(i32, i32)> {
    let mut binary_set = BTreeSet::new();
    for clause in clauses {
        if clause.len() != 2 {
            continue;
        }
        let a = clause[0].to_dimacs();
        let b = clause[1].to_dimacs();
        binary_set.insert(ordered_pair(a, b));
    }
    binary_set
}

fn collect_binary_clause_id_map(clauses: &[Vec<Literal>]) -> BTreeMap<(i32, i32), usize> {
    let mut binary_ids = BTreeMap::new();
    for (clause_id, clause) in clauses.iter().enumerate() {
        if clause.len() != 2 {
            continue;
        }
        let a = clause[0].to_dimacs();
        let b = clause[1].to_dimacs();
        binary_ids
            .entry(ordered_pair(a, b))
            .or_insert(clause_id + 1);
    }
    binary_ids
}

fn collect_onehot_groups(
    clauses: &[Vec<Literal>],
    binary_set: &BTreeSet<(i32, i32)>,
) -> Vec<Vec<i32>> {
    let mut groups = Vec::new();
    for clause in clauses {
        if clause.len() < 2 || clause.iter().any(|lit| !lit.is_positive()) {
            continue;
        }
        let mut vars: Vec<_> = clause.iter().map(|lit| lit.to_dimacs()).collect();
        vars.sort_unstable();
        let mut complete_mutex = true;
        'pairs: for lhs in 0..vars.len() {
            for rhs in (lhs + 1)..vars.len() {
                if !binary_set.contains(&ordered_pair(-vars[lhs], -vars[rhs])) {
                    complete_mutex = false;
                    break 'pairs;
                }
            }
        }
        if complete_mutex {
            groups.push(vars);
        }
    }
    groups
}

fn collect_onehot_group_witnesses(
    clauses: &[Vec<Literal>],
    binary_ids: &BTreeMap<(i32, i32), usize>,
) -> Vec<FmlaOneHotGroupWitness> {
    let mut groups = Vec::new();
    for (clause_id, clause) in clauses.iter().enumerate() {
        if clause.len() < 2 || clause.iter().any(|lit| !lit.is_positive()) {
            continue;
        }
        let mut vars: Vec<_> = clause.iter().map(|lit| lit.to_dimacs()).collect();
        vars.sort_unstable();
        let mut mutex_clause_ids = Vec::new();
        let mut complete_mutex = true;
        'pairs: for lhs in 0..vars.len() {
            for rhs in (lhs + 1)..vars.len() {
                let Some(&mutex_id) = binary_ids.get(&ordered_pair(-vars[lhs], -vars[rhs])) else {
                    complete_mutex = false;
                    break 'pairs;
                };
                mutex_clause_ids.push(mutex_id);
            }
        }
        if complete_mutex {
            groups.push(FmlaOneHotGroupWitness {
                support_clause_id: clause_id + 1,
                vars,
                mutex_clause_ids,
            });
        }
    }
    groups
}

fn count_guarded_equivalences(
    clauses: &[Vec<Literal>],
    onehot_vars: &BTreeSet<i32>,
) -> (usize, BTreeMap<i32, usize>) {
    let mut candidates: BTreeMap<(i32, i32, i32), DirectionSet> = BTreeMap::new();
    for clause in clauses {
        if clause.len() != 3 {
            continue;
        }
        let mut neg = Vec::with_capacity(2);
        let mut pos = Vec::with_capacity(1);
        for lit in clause {
            let dimacs = lit.to_dimacs();
            if dimacs < 0 {
                neg.push(-dimacs);
            } else {
                pos.push(dimacs);
            }
        }
        if neg.len() != 2 || pos.len() != 1 {
            continue;
        }
        for (guard, src) in [(neg[0], neg[1]), (neg[1], neg[0])] {
            let dst = pos[0];
            if onehot_vars.contains(&guard)
                && !onehot_vars.contains(&src)
                && !onehot_vars.contains(&dst)
            {
                let (lo, hi) = ordered_pair(src, dst);
                let directions = candidates.entry((guard, lo, hi)).or_default();
                directions.observe(src, dst);
            }
        }
    }

    let mut pairs = 0usize;
    let mut guard_fanout = BTreeMap::new();
    for ((guard, _lo, _hi), directions) in candidates {
        if directions.bidirectional() {
            pairs += 1;
            *guard_fanout.entry(guard).or_insert(0) += 1;
        }
    }
    (pairs, guard_fanout)
}

fn collect_guarded_equivalence_witnesses(
    clauses: &[Vec<Literal>],
    onehot_vars: &BTreeSet<i32>,
    sample_limit: usize,
) -> Vec<FmlaGuardedEquivalenceWitness> {
    let mut candidates: BTreeMap<(i32, i32, i32), DirectionClauseWitnesses> = BTreeMap::new();
    for (clause_id, clause) in clauses.iter().enumerate() {
        if clause.len() != 3 {
            continue;
        }
        let mut neg = Vec::with_capacity(2);
        let mut pos = Vec::with_capacity(1);
        let clause_lits: Vec<_> = clause.iter().map(|lit| lit.to_dimacs()).collect();
        for dimacs in &clause_lits {
            if *dimacs < 0 {
                neg.push(-*dimacs);
            } else {
                pos.push(*dimacs);
            }
        }
        if neg.len() != 2 || pos.len() != 1 {
            continue;
        }
        for (guard, src) in [(neg[0], neg[1]), (neg[1], neg[0])] {
            let dst = pos[0];
            if onehot_vars.contains(&guard)
                && !onehot_vars.contains(&src)
                && !onehot_vars.contains(&dst)
            {
                let (lo, hi) = ordered_pair(src, dst);
                let directions = candidates.entry((guard, lo, hi)).or_default();
                directions.observe(src, dst, clause_id + 1, &clause_lits);
            }
        }
    }

    let mut witnesses = Vec::new();
    for ((guard, lhs, rhs), directions) in candidates {
        let Some((forward_clause_id, forward_clause_lits)) = directions.lo_to_hi else {
            continue;
        };
        let Some((reverse_clause_id, reverse_clause_lits)) = directions.hi_to_lo else {
            continue;
        };
        witnesses.push(FmlaGuardedEquivalenceWitness {
            guard,
            lhs,
            rhs,
            forward_clause_id,
            reverse_clause_id,
            forward_clause_lits,
            reverse_clause_lits,
        });
        if witnesses.len() == sample_limit {
            break;
        }
    }
    witnesses
}

fn collect_support_cover_witnesses(
    onehot_groups: &[FmlaOneHotGroupWitness],
    guarded_equivalences: &[FmlaGuardedEquivalenceWitness],
) -> Vec<FmlaSupportCoverWitness> {
    let mut by_guard_source: BTreeMap<(i32, i32), Vec<DirectionalTernaryWitness>> = BTreeMap::new();
    let mut guard_sources: BTreeMap<i32, BTreeSet<i32>> = BTreeMap::new();
    for equivalence in guarded_equivalences {
        let forward = DirectionalTernaryWitness {
            destination: equivalence.rhs,
            source_clause_id: equivalence.forward_clause_id,
        };
        by_guard_source
            .entry((equivalence.guard, equivalence.lhs))
            .or_default()
            .push(forward);
        guard_sources
            .entry(equivalence.guard)
            .or_default()
            .insert(equivalence.lhs);

        let reverse = DirectionalTernaryWitness {
            destination: equivalence.lhs,
            source_clause_id: equivalence.reverse_clause_id,
        };
        by_guard_source
            .entry((equivalence.guard, equivalence.rhs))
            .or_default()
            .push(reverse);
        guard_sources
            .entry(equivalence.guard)
            .or_default()
            .insert(equivalence.rhs);
    }

    let mut witnesses = Vec::new();
    for group in onehot_groups {
        let mut candidate_sources = BTreeSet::new();
        for guard in &group.vars {
            if let Some(sources) = guard_sources.get(guard) {
                candidate_sources.extend(sources.iter().copied());
            }
        }

        for source_var in candidate_sources {
            let mut destination_vars = Vec::with_capacity(group.vars.len());
            let mut ternary_source_clause_ids = Vec::with_capacity(group.vars.len());
            let mut destination_seen = BTreeSet::new();
            let mut complete_cover = true;
            for guard in &group.vars {
                let Some(ternaries) = by_guard_source.get(&(*guard, source_var)) else {
                    complete_cover = false;
                    break;
                };
                let [ternary] = ternaries.as_slice() else {
                    complete_cover = false;
                    break;
                };
                if !destination_seen.insert(ternary.destination) {
                    complete_cover = false;
                    break;
                }
                destination_vars.push(ternary.destination);
                ternary_source_clause_ids.push(ternary.source_clause_id);
            }
            if !complete_cover {
                continue;
            }

            let mut clause_lits = Vec::with_capacity(destination_vars.len() + 1);
            clause_lits.push(-source_var);
            clause_lits.extend(destination_vars.iter().copied());

            let mut lrat_hints = ternary_source_clause_ids.clone();
            lrat_hints.push(group.support_clause_id);

            witnesses.push(FmlaSupportCoverWitness {
                support_clause_id: group.support_clause_id,
                guard_vars: group.vars.clone(),
                source_var,
                destination_vars,
                clause_lits,
                ternary_source_clause_ids,
                lrat_hints,
            });
        }
    }
    witnesses
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct DirectionalTernaryWitness {
    destination: i32,
    source_clause_id: usize,
}

#[derive(Debug, Clone, Copy, Default)]
struct DirectionSet {
    lo_to_hi: bool,
    hi_to_lo: bool,
}

#[derive(Debug, Clone, Default)]
struct DirectionClauseWitnesses {
    lo_to_hi: Option<(usize, Vec<i32>)>,
    hi_to_lo: Option<(usize, Vec<i32>)>,
}

impl DirectionClauseWitnesses {
    fn observe(&mut self, src: i32, dst: i32, clause_id: usize, clause_lits: &[i32]) {
        let slot = if src <= dst {
            &mut self.lo_to_hi
        } else {
            &mut self.hi_to_lo
        };
        if slot.is_none() {
            *slot = Some((clause_id, clause_lits.to_vec()));
        }
    }
}

impl DirectionSet {
    fn observe(&mut self, src: i32, dst: i32) {
        if src <= dst {
            self.lo_to_hi = true;
        } else {
            self.hi_to_lo = true;
        }
    }

    const fn bidirectional(self) -> bool {
        self.lo_to_hi && self.hi_to_lo
    }
}

const fn ordered_pair(a: i32, b: i32) -> (i32, i32) {
    if a <= b {
        (a, b)
    } else {
        (b, a)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::literal::Variable;
    use crate::parse_dimacs;
    use std::path::{Path, PathBuf};

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

    fn guarded_fixture_two_pairs() -> Vec<Vec<Literal>> {
        let mut clauses = guarded_fixture();
        clauses.push(vec![neg(0), neg(8), pos(9)]);
        clauses.push(vec![neg(0), neg(9), pos(8)]);
        clauses
    }

    fn support_cover_fixture() -> Vec<Vec<Literal>> {
        let mut clauses = vec![(0..6).map(pos).collect()];
        for lhs in 0..6 {
            for rhs in (lhs + 1)..6 {
                clauses.push(vec![neg(lhs), neg(rhs)]);
            }
        }
        for guard in 0..6 {
            let destination = 7 + guard;
            clauses.push(vec![neg(guard), neg(6), pos(destination)]);
            clauses.push(vec![neg(guard), neg(destination), pos(6)]);
        }
        clauses
    }

    #[test]
    fn scout_recovers_guarded_equiv_fixture_without_mutation() {
        let clauses = guarded_fixture();
        let before = clauses.clone();

        let scout = FmlaGuardedEquivScout::scan(8, &clauses);
        let witnesses = FmlaGuardedEquivWitnesses::scan(&clauses, 1);

        assert_eq!(clauses, before, "scout must be read-only");
        assert!(scout.detected(), "got {scout:?}");
        assert_eq!(scout.num_vars, 8);
        assert_eq!(scout.num_clauses, 18);
        assert_eq!(scout.onehot_groups, 1);
        assert_eq!(scout.onehot_width_hist.get(&6), Some(&1));
        assert_eq!(scout.onehot_variables, 6);
        assert_eq!(scout.guarded_equivalence_pairs, 1);
        assert_eq!(scout.guarded_equivalence_guards, 1);
        assert_eq!(
            scout.guarded_equivalence_guard_fanout_hist.get(&1),
            Some(&1)
        );
        assert_eq!(witnesses.onehot_groups.len(), 1);
        assert_eq!(witnesses.onehot_groups[0].support_clause_id, 1);
        assert_eq!(witnesses.onehot_groups[0].mutex_clause_ids.len(), 15);
        assert_eq!(witnesses.guarded_equivalences.len(), 1);
        let equiv = &witnesses.guarded_equivalences[0];
        assert_eq!(equiv.guard, 1);
        assert_eq!(equiv.lhs, 7);
        assert_eq!(equiv.rhs, 8);
        assert_eq!(equiv.forward_clause_id, 17);
        assert_eq!(equiv.reverse_clause_id, 18);
        assert_eq!(equiv.forward_clause_lits, vec![-1, -7, 8]);
        assert_eq!(equiv.reverse_clause_lits, vec![-1, -8, 7]);
    }

    #[test]
    fn scan_all_recovers_all_guarded_equiv_witnesses_for_multi_pair_fixture() {
        let clauses = guarded_fixture_two_pairs();

        let sampled = FmlaGuardedEquivWitnesses::scan(&clauses, 1);
        let all = FmlaGuardedEquivWitnesses::scan_all(&clauses);

        assert_eq!(sampled.onehot_groups.len(), 1);
        assert_eq!(sampled.guarded_equivalences.len(), 1);
        assert_eq!(all.onehot_groups.len(), 1);
        assert_eq!(all.guarded_equivalences.len(), 2);
        assert_eq!(all.guarded_equivalences[0].forward_clause_id, 17);
        assert_eq!(all.guarded_equivalences[0].reverse_clause_id, 18);
        assert_eq!(all.guarded_equivalences[1].forward_clause_id, 19);
        assert_eq!(all.guarded_equivalences[1].reverse_clause_id, 20);
    }

    #[test]
    fn support_cover_witnesses_are_deterministic_for_complete_guard_cover() {
        let clauses = support_cover_fixture();
        let witnesses = FmlaGuardedEquivWitnesses::scan_all(&clauses);

        let covers = witnesses.support_cover_witnesses();

        assert_eq!(witnesses.onehot_groups.len(), 1);
        assert_eq!(witnesses.guarded_equivalences.len(), 6);
        assert_eq!(covers.len(), 1);
        let cover = &covers[0];
        assert_eq!(cover.support_clause_id, 1);
        assert_eq!(cover.guard_vars, vec![1, 2, 3, 4, 5, 6]);
        assert_eq!(cover.source_var, 7);
        assert_eq!(cover.destination_vars, vec![8, 9, 10, 11, 12, 13]);
        assert_eq!(cover.clause_lits, vec![-7, 8, 9, 10, 11, 12, 13]);
        assert_eq!(
            cover.ternary_source_clause_ids,
            vec![17, 19, 21, 23, 25, 27]
        );
        assert_eq!(cover.lrat_hints, vec![17, 19, 21, 23, 25, 27, 1]);
    }

    #[test]
    fn source_audit_reports_missing_source_id_for_all_retained_pairs() {
        let clauses = guarded_fixture_two_pairs();
        let witnesses = FmlaGuardedEquivWitnesses::scan_all(&clauses);
        let hidden = witnesses.guarded_equivalences[1].reverse_clause_id;

        let audit = witnesses.source_audit(|source_id| source_id != hidden);

        assert_eq!(audit.witness_pairs_checked, 2);
        assert_eq!(audit.witness_pairs_missing_guard_group, 0);
        assert_eq!(audit.source_id_refs_checked, 36);
        assert_eq!(audit.unique_source_ids_checked, 20);
        assert_eq!(audit.source_ids_visible, 19);
        assert_eq!(audit.source_ids_missing, 1);
        assert_eq!(audit.first_missing_source_id, hidden);
    }

    #[test]
    fn unpaired_guarded_implication_rejects_fail_closed() {
        let mut clauses = guarded_fixture();
        clauses.pop();

        let scout = FmlaGuardedEquivScout::scan(8, &clauses);

        assert!(!scout.detected());
        assert_eq!(
            scout.rejection,
            FmlaGuardedEquivRejection::NoGuardedEquivalencePairs
        );
        assert_eq!(scout.guarded_equivalence_pairs, 0);
    }

    #[test]
    fn fmla_equiv_chain_xz_fixture_recovers_w38_counts() {
        let Some(formula) = parse_optional_xz_fixture(
            "../../benchmarks/sat/satcomp2024-sample/\
             9cd3acdb765c15163bc239ae3a57f880-FmlaEquivChain_4_6_6.sanitized.cnf.xz",
        ) else {
            return;
        };

        let scout = FmlaGuardedEquivScout::scan(formula.num_vars, &formula.clauses);

        eprintln!(
            "fmla_guarded_equiv_scout fmla onehot_groups={} onehot_variables={} guarded_equivalence_pairs={} guarded_equivalence_guards={} guard_fanout_hist={:?}",
            scout.onehot_groups,
            scout.onehot_variables,
            scout.guarded_equivalence_pairs,
            scout.guarded_equivalence_guards,
            scout.guarded_equivalence_guard_fanout_hist
        );
        assert!(scout.detected(), "got {scout:?}");
        assert_eq!(scout.num_vars, 54_411);
        assert_eq!(scout.num_clauses, 437_952);
        assert_eq!(scout.onehot_groups, 7_770);
        assert_eq!(scout.onehot_width_hist.get(&6), Some(&7_770));
        assert_eq!(scout.onehot_variables, 27_195);
        assert_eq!(scout.guarded_equivalence_pairs, 155_520);
        assert_eq!(scout.guarded_equivalence_guards, 27_195);
        assert_eq!(
            scout.guarded_equivalence_guard_fanout_hist,
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

        let witnesses = FmlaGuardedEquivWitnesses::scan(&formula.clauses, 1);
        assert_eq!(witnesses.onehot_groups.len(), 1);
        assert_eq!(witnesses.onehot_groups[0].support_clause_id, 2_593);
        assert_eq!(
            witnesses.onehot_groups[0].vars,
            vec![27_217, 27_218, 27_220, 27_223, 27_227, 27_232]
        );
        assert_eq!(witnesses.onehot_groups[0].mutex_clause_ids.len(), 15);
        assert_eq!(witnesses.guarded_equivalences.len(), 1);
        let equiv = &witnesses.guarded_equivalences[0];
        assert_eq!(equiv.guard, 27_217);
        assert_eq!(equiv.lhs, 3_889);
        assert_eq!(equiv.rhs, 5_185);
        assert_eq!(equiv.forward_clause_id, 173_569);
        assert_eq!(equiv.reverse_clause_id, 173_570);
        assert_eq!(equiv.forward_clause_lits, vec![-27_217, -3_889, 5_185]);
        assert_eq!(equiv.reverse_clause_lits, vec![-27_217, -5_185, 3_889]);

        let all_witnesses = FmlaGuardedEquivWitnesses::scan_all(&formula.clauses);
        let source_audit = all_witnesses.source_audit(|_| true);
        assert_eq!(all_witnesses.onehot_groups.len(), 7_770);
        assert_eq!(all_witnesses.guarded_equivalences.len(), 155_520);
        assert_eq!(source_audit.witness_pairs_checked, 155_520);
        assert_eq!(source_audit.witness_pairs_missing_guard_group, 0);
        assert_eq!(source_audit.source_id_refs_checked, 2_799_360);
        assert_eq!(source_audit.unique_source_ids_checked, 435_360);
        assert_eq!(source_audit.source_ids_visible, 435_360);
        assert_eq!(source_audit.source_ids_missing, 0);
        assert_eq!(source_audit.first_missing_source_id, 0);
    }

    #[test]
    fn fmla_equiv_chain_xz_fixture_recovers_support_cover_representative() {
        let Some(formula) = parse_optional_xz_fixture(
            "../../benchmarks/sat/satcomp2024-sample/\
             9cd3acdb765c15163bc239ae3a57f880-FmlaEquivChain_4_6_6.sanitized.cnf.xz",
        ) else {
            return;
        };

        let all_witnesses = FmlaGuardedEquivWitnesses::scan_all(&formula.clauses);
        let covers = all_witnesses.support_cover_witnesses();

        assert_eq!(covers.len(), 51_840);
        let representative = covers
            .iter()
            .find(|cover| {
                cover.support_clause_id == 2_593
                    && cover.clause_lits == vec![-3_889, 5_185, 5_401, 5_617, 5_833, 6_049, 6_265]
            })
            .expect("real Fmla fixture should expose representative support-cover row");
        assert_eq!(
            representative.guard_vars,
            vec![27_217, 27_218, 27_220, 27_223, 27_227, 27_232]
        );
        assert_eq!(representative.source_var, 3_889);
        assert_eq!(
            representative.destination_vars,
            vec![5_185, 5_401, 5_617, 5_833, 6_049, 6_265]
        );
        assert_eq!(
            representative.ternary_source_clause_ids,
            vec![173_569, 174_001, 174_433, 174_865, 175_297, 175_729]
        );
        assert_eq!(
            representative.lrat_hints,
            vec![173_569, 174_001, 174_433, 174_865, 175_297, 175_729, 2_593]
        );
    }

    #[test]
    fn controls_reject_with_zero_guarded_equivalence_pairs() {
        let Some(clique) = parse_optional_xz_fixture(
            "../../benchmarks/sat/satcomp2024-sample/\
             cb2e8b7fada420c5046f587ea754d052-clique_n2_k10.sanitized.cnf.xz",
        ) else {
            return;
        };
        let clique_scout = FmlaGuardedEquivScout::scan(clique.num_vars, &clique.clauses);
        eprintln!(
            "fmla_guarded_equiv_scout clique onehot_groups={} guarded_equivalence_pairs={} rejection={}",
            clique_scout.onehot_groups,
            clique_scout.guarded_equivalence_pairs,
            clique_scout.rejection.as_str()
        );
        assert!(!clique_scout.detected());
        assert_eq!(clique_scout.onehot_groups, 10);
        assert_eq!(clique_scout.guarded_equivalence_pairs, 0);

        let circuit = parse_required_xz_fixture(
            "../../benchmarks/sat/satcomp2024-sample/\
             c5ae0ec49de0959cd14431ce851c14f8-Circuit_multiplier22.cnf.xz",
        );
        let circuit_scout = FmlaGuardedEquivScout::scan(circuit.num_vars, &circuit.clauses);
        eprintln!(
            "fmla_guarded_equiv_scout circuit onehot_groups={} guarded_equivalence_pairs={} rejection={}",
            circuit_scout.onehot_groups,
            circuit_scout.guarded_equivalence_pairs,
            circuit_scout.rejection.as_str()
        );
        assert!(!circuit_scout.detected());
        assert_eq!(circuit_scout.onehot_groups, 2);
        assert_eq!(circuit_scout.guarded_equivalence_pairs, 0);
    }

    fn parse_optional_xz_fixture(relative_path: &str) -> Option<crate::DimacsFormula> {
        let path = Path::new(env!("CARGO_MANIFEST_DIR")).join(relative_path);
        if !path.exists() {
            eprintln!(
                "Fmla guarded-equivalence scout fixture missing: {}",
                path.display()
            );
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

    fn _repo_root() -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
    }
}

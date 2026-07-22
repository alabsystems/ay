// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Dual Implication Point (DIP) detection and Extended Resolution Clause Learning.
//!
//! Implements DIP-ERCL from: Buss, Chung, Ganesh, Oliveras. "Extended Resolution
//! Clause Learning via Dual Implication Points." arXiv:2406.14190 [cs.LO], 2024.
//!
//! A DIP is a pair of literals {a, b} such that every path from the decision
//! variable to the conflict passes through at least one of a or b. This
//! generalizes UIPs (single-vertex dominators) to two-vertex dominators (TVDs).
//!
//! When a DIP is found, the 1UIP learned clause is split into two shorter
//! clauses using an extension variable z <-> (a AND b):
//!   - Pre-DIP clause:  (NOT uip) OR (NOT C) OR z
//!   - Post-DIP clause: (NOT z) OR (NOT D)
//!   - Tseitin definition clauses for z.

use crate::kani_compat::DetHashMap as HashMap;
use crate::literal::{Literal, Variable};
use crate::solver::VarData;

/// Minimum number of current-level literals required to attempt DIP detection.
/// With fewer than 3 current-level seen variables (UIP + 2 others), there is
/// no room for a meaningful DIP pair between the UIP and conflict.
const MIN_CURRENT_LEVEL_LITS: usize = 3;

/// Minimum occurrence count for a DIP pair to be considered useful.
/// From xMapleLCM: pairs that occur fewer than this many times are filtered.
const MIN_OCCURRENCE_THRESHOLD: u64 = 20;

/// Interval (in conflicts) between extension variable garbage collection passes.
const GC_INTERVAL: u64 = 1000;

/// Maximum number of extension variables to retain. Beyond this, GC is forced.
const MAX_EXTENSION_VARS: usize = 5000;

/// A pair of literals forming a Dual Implication Point.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct DipPair {
    /// First literal of the DIP (closer to conflict).
    pub(crate) a: Literal,
    /// Second literal of the DIP.
    pub(crate) b: Literal,
}

/// Result of DIP detection within the implication graph.
#[derive(Debug, Clone)]
pub(crate) struct DipResult {
    /// The DIP pair found.
    pub(crate) pair: DipPair,
    /// Literals between the UIP and the DIP (pre-DIP region).
    pub(crate) pre_dip_lits: Vec<Literal>,
    /// Literals between the DIP and the conflict (post-DIP region).
    pub(crate) post_dip_lits: Vec<Literal>,
}

/// Result of applying DIP-based extended resolution clause learning.
#[derive(Debug, Clone)]
pub(crate) struct DipErclResult {
    /// Pre-DIP clause: (NOT uip) OR (NOT C) OR z
    pub(crate) pre_dip_clause: Vec<Literal>,
    /// Post-DIP clause: (NOT z) OR (NOT D)
    pub(crate) post_dip_clause: Vec<Literal>,
    /// Three Tseitin definition clauses for the extension variable:
    ///   [0]: (NOT z) OR a
    ///   [1]: (NOT z) OR b
    ///   [2]: (NOT a) OR (NOT b) OR z
    pub(crate) definition_clauses: [Vec<Literal>; 3],
    /// The extension variable introduced.
    pub(crate) ext_var: Variable,
    /// The backtrack level for the post-DIP clause.
    pub(crate) backtrack_level: u32,
}

/// Statistics for DIP-ERCL.
#[derive(Debug, Default, Clone)]
pub(crate) struct DipStats {
    /// Number of times a valid DIP was found during conflict analysis.
    pub(crate) dip_found: u64,
    /// Number of extension variables created.
    pub(crate) dip_extensions_created: u64,
    /// Number of extension variables deleted during GC.
    pub(crate) dip_gc_deleted: u64,
    /// Number of DIP attempts (conflicts where DIP detection ran).
    pub(crate) dip_attempts: u64,
    /// Number of times DIP was skipped (too few current-level lits, etc.).
    pub(crate) dip_skipped: u64,
    /// Number of literal-pair reuses (existing extension variable matched).
    pub(crate) dip_reuses: u64,
}

/// Manages extension variables and DIP-ERCL state across conflicts.
#[derive(Clone)]
pub(crate) struct DipManager {
    /// Map from canonical literal pair -> extension variable index.
    /// The pair is stored as (min(a.0, b.0), max(a.0, b.0)) for canonical ordering.
    pub(crate) extension_var_defs: HashMap<(u32, u32), u32>,
    /// Reverse map: extension variable index -> (lit_a, lit_b) definition.
    pub(crate) extension_var_sources: HashMap<u32, (Literal, Literal)>,
    /// Number of extension variables created.
    pub(crate) extension_var_count: u64,
    /// Conflicts since last GC.
    pub(crate) conflicts_since_gc: u64,
    /// Per-pair occurrence count for quality filtering.
    pub(crate) pair_occurrences: HashMap<(u32, u32), u64>,
    /// Activity scores for extension variables (for GC).
    pub(crate) extension_activity: HashMap<u32, f64>,
    /// Stats.
    pub(crate) stats: DipStats,
    /// Whether DIP-ERCL is enabled. Automatically disabled if it shows no benefit.
    pub(crate) enabled: bool,
}

impl DipManager {
    /// Create a new DIP manager.
    pub(crate) fn new() -> Self {
        Self {
            extension_var_defs: HashMap::default(),
            extension_var_sources: HashMap::default(),
            extension_var_count: 0,
            conflicts_since_gc: 0,
            pair_occurrences: HashMap::default(),
            extension_activity: HashMap::default(),
            stats: DipStats::default(),
            // DIP-ERCL DISABLED: The Tseitin definition clauses and/or the
            // split learned clauses are not RUP-derivable from the original
            // formula, causing false UNSAT on SAT instances (battleship-14-26,
            // Circuit_multiplier22, mp1-klieber). The extension variable
            // introduction requires proper DRAT proof support (RAT clauses)
            // that the current implementation does not provide.
            // See #8448 for investigation details.
            enabled: false,
        }
    }

    /// Canonical key for a literal pair (order-independent).
    #[inline]
    fn canonical_pair(a: Literal, b: Literal) -> (u32, u32) {
        let (x, y) = (a.0, b.0);
        if x <= y {
            (x, y)
        } else {
            (y, x)
        }
    }

    /// Increment the occurrence count for a literal pair.
    fn record_pair_occurrence(&mut self, a: Literal, b: Literal) {
        let key = Self::canonical_pair(a, b);
        *self.pair_occurrences.entry(key).or_insert(0) += 1;
    }

    /// Check if a pair has been seen enough times to warrant an extension variable.
    fn pair_meets_threshold(&self, a: Literal, b: Literal) -> bool {
        let key = Self::canonical_pair(a, b);
        self.pair_occurrences.get(&key).copied().unwrap_or(0) >= MIN_OCCURRENCE_THRESHOLD
    }

    /// Look up an existing extension variable for a literal pair.
    pub(crate) fn lookup_extension(&self, a: Literal, b: Literal) -> Option<u32> {
        let key = Self::canonical_pair(a, b);
        self.extension_var_defs.get(&key).copied()
    }

    /// Register a new extension variable for a literal pair.
    pub(crate) fn register_extension(&mut self, a: Literal, b: Literal, ext_var_idx: u32) {
        let key = Self::canonical_pair(a, b);
        self.extension_var_defs.insert(key, ext_var_idx);
        self.extension_var_sources.insert(ext_var_idx, (a, b));
        self.extension_activity.insert(ext_var_idx, 1.0);
        self.extension_var_count += 1;
        self.stats.dip_extensions_created += 1;
    }

    /// Bump activity of an extension variable (called when its clauses participate
    /// in conflict analysis or propagation).
    pub(crate) fn bump_activity(&mut self, ext_var_idx: u32) {
        if let Some(act) = self.extension_activity.get_mut(&ext_var_idx) {
            *act += 1.0;
        }
    }

    /// Tick the conflict counter and return true if GC should run.
    pub(crate) fn tick_conflict(&mut self) -> bool {
        self.conflicts_since_gc += 1;
        self.conflicts_since_gc >= GC_INTERVAL
            && self.extension_var_defs.len() > MAX_EXTENSION_VARS / 2
    }

    /// Collect low-activity extension variables for deletion.
    ///
    /// Returns a list of (extension_var_index, lit_a, lit_b) tuples to delete.
    /// Deletes the bottom 25% by activity.
    pub(crate) fn gc_extension_vars(&mut self) -> Vec<(u32, Literal, Literal)> {
        self.conflicts_since_gc = 0;

        if self.extension_var_defs.is_empty() {
            return Vec::new();
        }

        // Sort extension vars by activity (ascending).
        let mut vars_by_activity: Vec<(u32, f64)> = self
            .extension_activity
            .iter()
            .map(|(var, act)| (*var, *act))
            .collect();
        vars_by_activity.sort_by(|a, b| a.1.partial_cmp(&b.1).unwrap_or(std::cmp::Ordering::Equal));

        // Delete bottom 25%.
        let delete_count = vars_by_activity.len() / 4;
        let mut deleted = Vec::with_capacity(delete_count);

        for &(var_idx, _) in vars_by_activity.iter().take(delete_count) {
            if let Some((lit_a, lit_b)) = self.extension_var_sources.remove(&var_idx) {
                let key = Self::canonical_pair(lit_a, lit_b);
                self.extension_var_defs.remove(&key);
                self.extension_activity.remove(&var_idx);
                self.pair_occurrences.remove(&key);
                deleted.push((var_idx, lit_a, lit_b));
                self.stats.dip_gc_deleted += 1;
            }
        }

        // Decay all remaining activities by 0.5.
        for (_, act) in self.extension_activity.iter_mut() {
            *act *= 0.5;
        }

        deleted
    }

    /// Try to apply DIP-ERCL to a 1UIP learned clause.
    ///
    /// Returns `None` if no valid DIP is found or conditions are not met.
    ///
    /// Parameters:
    /// - `learned_clause`: the 1UIP learned clause (first lit is UIP negated)
    /// - `trail`: the solver trail
    /// - `var_data`: per-variable metadata
    /// - `decision_level`: current decision level
    /// - `next_var_index`: the next available variable index for extension vars
    ///
    /// The caller is responsible for actually allocating the extension variable
    /// using `new_var_internal()` if this returns `Some`.
    pub(crate) fn try_dip_ercl(
        &mut self,
        learned_clause: &[Literal],
        trail: &[Literal],
        var_data: &[VarData],
        decision_level: u32,
        next_var_index: u32,
    ) -> Option<DipErclResult> {
        if !self.enabled || learned_clause.len() < 4 {
            self.stats.dip_skipped += 1;
            return None;
        }
        self.stats.dip_attempts += 1;

        let uip = learned_clause[0];
        let uip_var = uip.variable().index();

        // Separate current-level literals from non-current-level literals.
        let mut current_level_lits: Vec<Literal> = Vec::new();
        let mut other_level_lits: Vec<Literal> = Vec::new();

        for &lit in &learned_clause[1..] {
            let var_idx = lit.variable().index();
            if var_idx < var_data.len() && var_data[var_idx].level == decision_level {
                current_level_lits.push(lit);
            } else {
                other_level_lits.push(lit);
            }
        }

        // Need at least 2 current-level literals beyond UIP to form a DIP.
        if current_level_lits.len() < 2 {
            self.stats.dip_skipped += 1;
            return None;
        }

        // Find DIP: use the simplified heuristic — pick the two current-level
        // literals closest to the conflict (highest trail position).
        let dip_result = find_dip_closest_to_conflict(
            &current_level_lits,
            var_data,
            uip_var,
            decision_level,
            trail,
        )?;

        self.stats.dip_found += 1;

        // Record pair occurrence for quality filtering.
        let dip_a = dip_result.pair.a;
        let dip_b = dip_result.pair.b;
        self.record_pair_occurrence(dip_a, dip_b);

        // Check if we should create or reuse an extension variable.
        let (ext_var_idx, _is_reuse) = if let Some(existing) = self.lookup_extension(dip_a, dip_b) {
            self.stats.dip_reuses += 1;
            self.bump_activity(existing);
            (existing, true)
        } else {
            // Only create new extension variable if the pair meets the occurrence threshold.
            if !self.pair_meets_threshold(dip_a, dip_b) {
                return None;
            }
            let new_var = next_var_index;
            self.register_extension(dip_a, dip_b, new_var);
            (new_var, false)
        };

        let ext_var = Variable(ext_var_idx);
        let z_pos = Literal::positive(ext_var);
        let z_neg = Literal::negative(ext_var);

        // Build pre-DIP clause: (NOT uip) OR (NOT C) OR z
        // where C = other-level literals + pre-DIP current-level literals
        let mut pre_dip_clause =
            Vec::with_capacity(1 + other_level_lits.len() + dip_result.pre_dip_lits.len() + 1);
        pre_dip_clause.push(uip); // UIP negated (asserting literal)
        pre_dip_clause.extend_from_slice(&other_level_lits);
        pre_dip_clause.extend_from_slice(&dip_result.pre_dip_lits);
        pre_dip_clause.push(z_pos);

        // Build post-DIP clause: (NOT z) OR (NOT D)
        // where D = post-DIP current-level literals
        let mut post_dip_clause = Vec::with_capacity(1 + dip_result.post_dip_lits.len());
        post_dip_clause.push(z_neg);
        post_dip_clause.extend_from_slice(&dip_result.post_dip_lits);

        // Compute backtrack level for post-DIP clause.
        let bt_level = post_dip_clause
            .iter()
            .skip(1) // skip z_neg
            .filter_map(|lit| {
                let vi = lit.variable().index();
                if vi < var_data.len() {
                    Some(var_data[vi].level)
                } else {
                    None
                }
            })
            .max()
            .unwrap_or(0);

        // Build Tseitin definition clauses for z <-> (a AND b):
        //   (NOT z) OR a     — if z is true, a must be true
        //   (NOT z) OR b     — if z is true, b must be true
        //   (NOT a) OR (NOT b) OR z  — if both a and b are true, z must be true
        //
        // Note: dip_a and dip_b are NEGATED literals from the learned clause
        // (they appear as NOT a, NOT b in the clause). The DIP definition uses
        // the POSITIVE sense: z <-> (a AND b) where a, b are the variables
        // that were assigned true on the trail.
        let a_pos = dip_a.negated(); // the true-on-trail literal
        let b_pos = dip_b.negated();

        let def0 = vec![z_neg, a_pos];
        let def1 = vec![z_neg, b_pos];
        let def2 = vec![dip_a, dip_b, z_pos]; // NOT a_pos OR NOT b_pos OR z

        let definition_clauses = [def0, def1, def2];

        Some(DipErclResult {
            pre_dip_clause,
            post_dip_clause,
            definition_clauses,
            ext_var,
            backtrack_level: bt_level,
        })
    }
}

/// Find a DIP pair using the "closest to conflict" heuristic.
///
/// Among the current-level literals in the learned clause, pick the two with
/// the highest trail positions (closest to the conflict). These form a natural
/// two-vertex separator because all paths from the decision to the conflict
/// must pass through at least one of them to reach the conflict side.
///
/// This is the simplest DIP selection strategy from Buss et al. (2024).
fn find_dip_closest_to_conflict(
    current_level_lits: &[Literal],
    var_data: &[VarData],
    uip_var: usize,
    _decision_level: u32,
    _trail: &[Literal],
) -> Option<DipResult> {
    if current_level_lits.len() < 2 {
        return None;
    }

    // Sort current-level literals by trail position (descending = closest to conflict first).
    let mut sorted_lits: Vec<(Literal, u32)> = current_level_lits
        .iter()
        .filter_map(|&lit| {
            let vi = lit.variable().index();
            if vi < var_data.len() && vi != uip_var {
                Some((lit, var_data[vi].trail_pos))
            } else {
                None
            }
        })
        .collect();

    sorted_lits.sort_by_key(|b| std::cmp::Reverse(b.1));

    if sorted_lits.len() < 2 {
        return None;
    }

    let dip_a = sorted_lits[0].0;
    let dip_b = sorted_lits[1].0;
    let dip_a_pos = sorted_lits[0].1;
    let dip_b_pos = sorted_lits[1].1;

    // Ensure a comes before b on the trail (a has lower trail_pos).
    let (dip_a, dip_b, split_pos) = if dip_a_pos <= dip_b_pos {
        (dip_a, dip_b, dip_a_pos)
    } else {
        (dip_b, dip_a, dip_b_pos)
    };

    // Partition remaining current-level literals into pre-DIP and post-DIP.
    let mut pre_dip_lits = Vec::new();
    let mut post_dip_lits = Vec::new();

    for &lit in current_level_lits {
        let vi = lit.variable().index();
        if vi == dip_a.variable().index() || vi == dip_b.variable().index() {
            continue;
        }
        if vi < var_data.len() {
            let tp = var_data[vi].trail_pos;
            if tp < split_pos {
                pre_dip_lits.push(lit);
            } else {
                post_dip_lits.push(lit);
            }
        }
    }

    Some(DipResult {
        pair: DipPair { a: dip_a, b: dip_b },
        pre_dip_lits,
        post_dip_lits,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::solver::VarData;

    /// Helper to create a VarData with specific level and trail_pos.
    fn make_var_data(level: u32, trail_pos: u32) -> VarData {
        let mut vd = VarData::UNASSIGNED;
        vd.level = level;
        vd.trail_pos = trail_pos;
        vd
    }

    #[test]
    fn test_dip_manager_new() {
        let mgr = DipManager::new();
        // DIP-ERCL disabled (#8448): extension variables are not RUP-derivable,
        // causing false UNSAT. mgr.enabled starts false pending correct
        // reimplementation with proper DRAT proof support.
        assert!(!mgr.enabled);
        assert_eq!(mgr.extension_var_count, 0);
        assert!(mgr.extension_var_defs.is_empty());
    }

    #[test]
    fn test_canonical_pair_ordering() {
        let a = Literal(10);
        let b = Literal(20);
        assert_eq!(DipManager::canonical_pair(a, b), (10, 20));
        assert_eq!(DipManager::canonical_pair(b, a), (10, 20));
    }

    #[test]
    fn test_register_and_lookup_extension() {
        let mut mgr = DipManager::new();
        let a = Literal(10);
        let b = Literal(20);
        mgr.register_extension(a, b, 100);
        assert_eq!(mgr.lookup_extension(a, b), Some(100));
        assert_eq!(mgr.lookup_extension(b, a), Some(100)); // Order-independent
        assert_eq!(mgr.lookup_extension(Literal(30), b), None);
    }

    #[test]
    fn test_occurrence_tracking() {
        let mut mgr = DipManager::new();
        let a = Literal(10);
        let b = Literal(20);

        assert!(!mgr.pair_meets_threshold(a, b));

        for _ in 0..MIN_OCCURRENCE_THRESHOLD {
            mgr.record_pair_occurrence(a, b);
        }
        assert!(mgr.pair_meets_threshold(a, b));
        // Order independence
        assert!(mgr.pair_meets_threshold(b, a));
    }

    #[test]
    fn test_gc_extension_vars() {
        let mut mgr = DipManager::new();
        let lits: Vec<Literal> = (0..20).map(|i| Literal(i * 2)).collect();

        // Register 10 extension variables with varying activity.
        for i in 0..10 {
            let a = lits[i * 2];
            let b = lits[i * 2 + 1];
            let ext_var = 1000 + i as u32;
            mgr.register_extension(a, b, ext_var);
            // Set activity proportional to index.
            mgr.extension_activity.insert(ext_var, (i + 1) as f64);
        }
        assert_eq!(mgr.extension_var_defs.len(), 10);

        let deleted = mgr.gc_extension_vars();
        // Bottom 25% of 10 = 2 deleted.
        assert_eq!(deleted.len(), 2);
        // Lowest activity vars (1000 with act=1, 1001 with act=2) should be deleted.
        let deleted_vars: Vec<u32> = deleted.iter().map(|&(v, _, _)| v).collect();
        assert!(deleted_vars.contains(&1000));
        assert!(deleted_vars.contains(&1001));
        assert_eq!(mgr.extension_var_defs.len(), 8);
    }

    #[test]
    fn test_find_dip_too_few_lits() {
        // Only 1 current-level literal: no DIP possible.
        let var_data = vec![make_var_data(1, 0), make_var_data(1, 1)];
        let result = find_dip_closest_to_conflict(
            &[Literal::negative(Variable(1))],
            &var_data,
            0, // uip_var
            1, // decision_level
            &[],
        );
        assert!(result.is_none());
    }

    #[test]
    fn test_find_dip_basic() {
        // 5 variables at decision level 3.
        // UIP is var 0, others are vars 1..4 at trail positions 5,6,7,8.
        let var_data = vec![
            make_var_data(3, 4), // var 0: UIP
            make_var_data(3, 5), // var 1
            make_var_data(3, 6), // var 2
            make_var_data(3, 7), // var 3
            make_var_data(3, 8), // var 4
        ];

        let current_level_lits = vec![
            Literal::negative(Variable(1)),
            Literal::negative(Variable(2)),
            Literal::negative(Variable(3)),
            Literal::negative(Variable(4)),
        ];

        let result = find_dip_closest_to_conflict(
            &current_level_lits,
            &var_data,
            0, // uip_var
            3, // decision_level
            &[],
        );

        assert!(result.is_some());
        let dip = result.expect("DIP should be found");

        // The two closest to conflict are vars 3 (pos 7) and 4 (pos 8).
        let dip_vars: Vec<usize> =
            vec![dip.pair.a.variable().index(), dip.pair.b.variable().index()];
        assert!(dip_vars.contains(&3) || dip_vars.contains(&4));
    }

    #[test]
    fn test_try_dip_ercl_too_short_clause() {
        let mut mgr = DipManager::new();
        // Clause with only 3 literals: too short for DIP.
        let clause = vec![
            Literal::negative(Variable(0)),
            Literal::negative(Variable(1)),
            Literal::negative(Variable(2)),
        ];
        let var_data = vec![
            make_var_data(2, 0),
            make_var_data(1, 1),
            make_var_data(1, 2),
        ];
        let result = mgr.try_dip_ercl(&clause, &[], &var_data, 2, 10);
        assert!(result.is_none());
    }

    #[test]
    fn test_try_dip_ercl_with_threshold_met() {
        let mut mgr = DipManager::new();
        mgr.enabled = true; // Override default-disabled for unit test

        // Build a scenario with 5 variables, decision level 3.
        // UIP = var 0 at level 3. Vars 1-4 at level 3 with varying trail pos.
        // Var 5 at level 1 (other level).
        let var_data = vec![
            make_var_data(3, 4), // var 0: UIP
            make_var_data(3, 5), // var 1
            make_var_data(3, 6), // var 2
            make_var_data(3, 7), // var 3
            make_var_data(3, 8), // var 4
            make_var_data(1, 2), // var 5: lower level
        ];

        let clause = vec![
            Literal::negative(Variable(0)), // UIP
            Literal::negative(Variable(1)),
            Literal::negative(Variable(2)),
            Literal::negative(Variable(3)),
            Literal::negative(Variable(4)),
            Literal::negative(Variable(5)),
        ];

        // First, pump up the pair occurrence count to meet threshold.
        // The DIP will be vars 3,4 (closest to conflict).
        let dip_a = Literal::negative(Variable(3));
        let dip_b = Literal::negative(Variable(4));
        for _ in 0..MIN_OCCURRENCE_THRESHOLD {
            mgr.record_pair_occurrence(dip_a, dip_b);
        }

        let result = mgr.try_dip_ercl(&clause, &[], &var_data, 3, 100);

        assert!(result.is_some());
        let ercl = result.expect("ERCL should succeed");

        // Extension variable should be 100.
        assert_eq!(ercl.ext_var, Variable(100));

        // Pre-DIP clause should contain UIP + non-current-level + pre-DIP lits + z.
        assert!(ercl
            .pre_dip_clause
            .contains(&Literal::negative(Variable(0))));
        assert!(ercl
            .pre_dip_clause
            .contains(&Literal::positive(Variable(100))));

        // Post-DIP clause should contain NOT z + post-DIP lits.
        assert!(ercl
            .post_dip_clause
            .contains(&Literal::negative(Variable(100))));

        // Definition clauses should have 3 elements.
        assert_eq!(ercl.definition_clauses.len(), 3);
        assert_eq!(ercl.definition_clauses[0].len(), 2);
        assert_eq!(ercl.definition_clauses[1].len(), 2);
        assert_eq!(ercl.definition_clauses[2].len(), 3);
    }

    #[test]
    fn test_dip_disabled() {
        let mut mgr = DipManager::new();
        mgr.enabled = false;

        let clause = vec![
            Literal::negative(Variable(0)),
            Literal::negative(Variable(1)),
            Literal::negative(Variable(2)),
            Literal::negative(Variable(3)),
            Literal::negative(Variable(4)),
        ];
        let var_data = vec![
            make_var_data(2, 0),
            make_var_data(2, 1),
            make_var_data(2, 2),
            make_var_data(2, 3),
            make_var_data(2, 4),
        ];

        let result = mgr.try_dip_ercl(&clause, &[], &var_data, 2, 100);
        assert!(result.is_none());
        assert_eq!(mgr.stats.dip_skipped, 1);
    }

    #[test]
    fn test_extension_var_reuse() {
        let mut mgr = DipManager::new();
        mgr.enabled = true; // Override default-disabled for unit test
        let a = Literal::negative(Variable(3));
        let b = Literal::negative(Variable(4));

        // Pre-register an extension variable.
        mgr.register_extension(a, b, 50);

        // Pump occurrences.
        for _ in 0..MIN_OCCURRENCE_THRESHOLD {
            mgr.record_pair_occurrence(a, b);
        }

        let var_data = vec![
            make_var_data(3, 4), // var 0: UIP
            make_var_data(3, 5),
            make_var_data(3, 6),
            make_var_data(3, 7),
            make_var_data(3, 8),
            make_var_data(1, 2),
        ];

        let clause = vec![
            Literal::negative(Variable(0)),
            Literal::negative(Variable(1)),
            Literal::negative(Variable(2)),
            a,
            b,
            Literal::negative(Variable(5)),
        ];

        let result = mgr.try_dip_ercl(&clause, &[], &var_data, 3, 100);
        assert!(result.is_some());
        let ercl = result.expect("ERCL should succeed with reuse");
        // Should reuse existing extension variable 50, not allocate 100.
        assert_eq!(ercl.ext_var, Variable(50));
        assert_eq!(mgr.stats.dip_reuses, 1);
    }

    #[test]
    fn test_tick_conflict_gc_trigger() {
        let mut mgr = DipManager::new();

        // Add enough extension vars to exceed the threshold.
        for i in 0..3000 {
            let a = Literal(i * 4);
            let b = Literal(i * 4 + 2);
            mgr.register_extension(a, b, 10000 + i);
        }

        // Tick up to GC_INTERVAL.
        for _ in 0..GC_INTERVAL - 1 {
            assert!(!mgr.tick_conflict());
        }
        assert!(mgr.tick_conflict());
    }
}

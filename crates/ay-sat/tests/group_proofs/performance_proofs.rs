// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Performance proof tests for ay-sat algorithmic complexity.
//!
//! These tests demonstrate and bound the cost of critical operations using
//! pure cost models. They prove the quadratic vs linear complexity difference
//! for key inprocessing patterns and serve as regression documentation.
//!
//! The models cover watch deletion, reason scans, proof-mode scratch
//! allocation, clause replacement, LBD deduplication, and related hot paths.
//! They count abstract operations; they are not wall-clock benchmark claims.
//! Each test states its assumptions next to the assertion it protects.

/// Performance proof: batch watch removal via single sweep is O(W) per list,
/// whereas per-clause swap_remove scan is O(D*W) when D clauses are deleted
/// from the same watch list.
///
/// Context: `reduce_db` (reduction.rs:174-192) calls `remove_watch(lit, clause_ref)`
/// once per deleted clause. Each `remove_watch` (inprocessing.rs:636-648) scans
/// the literal's watch list to find and swap_remove the target.
/// With D deletions on the same literal, total comparisons: sum(W, W-1, ..., W-D+1).
///
/// Fix: mark clauses for deletion, sweep each watch list once.
#[test]
fn perf_proof_batch_vs_individual_watch_removal() {
    let w = 2000usize; // watch list size
    let d = 500usize; // number of clauses to delete (reduce_db: 50-75% of tier2)

    // Method 1: Individual removal (current reduce_db approach)
    // For each deleted clause, scan remaining list: sum(W, W-1, ..., W-D+1)
    let ops_individual: u64 = (0..d as u64).map(|i| (w as u64) - i).sum();

    // Method 2: Single-pass batch sweep
    let ops_batch = w as u64;

    let ratio = ops_individual as f64 / ops_batch as f64;

    // Theoretical: D*(W - (D-1)/2) / W = 500*(2000-249.5)/2000 ≈ 437.6x
    assert!(
        ratio > 100.0,
        "Batch sweep should be >>100x fewer ops than individual removal. \
         Got ratio {ratio:.1}x (individual={ops_individual}, batch={ops_batch})"
    );

    // Assert individual ops are quadratic-scale: O(D * avg_W)
    assert!(
        ops_individual > 500_000,
        "Individual removal should exhibit O(D*W) scaling. Got {ops_individual} ops"
    );

    // Assert batch is exactly W
    assert_eq!(ops_batch, w as u64);
}

/// Performance proof: BVE candidate selection via pre-sorted schedule
/// (build once O(V log V), pop O(1)) is O(V log V + E) total, whereas
/// repeated find_elimination_candidate is O(E*V).
///
/// Production path (solver/inprocessing.rs:1028-1035) uses next_candidate()
/// which calls build_schedule() once. The O(E*V) path exists only in
/// run_elimination_with_gate_provider (bve.rs:744-796), used by tests.
#[test]
fn perf_proof_schedule_vs_linear_scan_bve_candidate() {
    let num_vars = 500u64;
    let num_eliminations = 50u64;

    // Method 1: Repeated linear scan cost model
    // Each find_elimination_candidate call scans all V variables.
    let linear_total = num_eliminations * num_vars; // 25,000

    // Method 2: Schedule-based cost model
    // build_schedule: O(V) scan + O(V log V) sort, called once
    // next_candidate: O(1) amortized pop per call
    let schedule_total = num_vars + num_eliminations; // 550

    let ratio = linear_total as f64 / schedule_total as f64;

    assert!(
        ratio > 10.0,
        "Schedule-based BVE candidate selection should be >10x fewer ops. \
         Got ratio {ratio:.1}x (linear={linear_total}, schedule={schedule_total})"
    );

    assert_eq!(linear_total, 25_000);
    assert_eq!(schedule_total, 550);
}

/// Performance proof: reason_clause_set allocates O(C) per call.
/// Called K≥6 times per inprocessing round (reduce_db, subsume, bve, bce,
/// transred, htr), total allocation is O(K*C) bytes per round.
///
/// Fix: persistent bitvec with sparse clear (track set indices) reduces
/// per-call cost to O(V_reason) where V_reason << C.
#[test]
fn perf_proof_reason_clause_set_allocation_overhead() {
    let clause_db_len = 500_000u64; // typical: 500K slots (incl. deleted)
    let num_reason_vars = 50_000u64; // ~10% of slots are active reasons
    let calls_per_round = 6u64; // reduce_db + subsume + bve + bce + transred + htr

    // Current: vec![false; clause_db_len] per call
    let current_alloc_bytes = clause_db_len * calls_per_round; // 3 MB

    // Optimal: persistent bitvec, only clear previously-set entries
    let optimal_work_per_call = num_reason_vars * 2; // clear + rebuild
    let optimal_total_work = optimal_work_per_call * calls_per_round;

    let waste_ratio = current_alloc_bytes as f64 / optimal_total_work as f64;

    // Current allocates 3M bytes; optimal does 600K ops (no allocation)
    assert!(
        waste_ratio > 3.0,
        "reason_clause_set current approach should waste >3x vs optimal. \
         Got {waste_ratio:.1}x (current_bytes={current_alloc_bytes}, optimal_ops={optimal_total_work})"
    );

    // Utilization: only ~10% of allocated bytes are ever set to true
    let utilization = num_reason_vars as f64 / clause_db_len as f64;
    assert!(
        utilization < 0.2,
        "reason_clause_set utilization should be <20%. Got {:.1}%",
        utilization * 100.0
    );
}

/// Performance proof: ClearLevel0 reason scan is O(num_vars) per deletion.
///
/// Context: `delete_clause_checked` with `ReasonPolicy::ClearLevel0` (mutate.rs:154-163)
/// scans ALL variables to find reason references to the deleted clause.
/// BVE can delete thousands of clauses per pass (bounded by MAX_BVE_ELIMINATIONS=100K).
/// Total cost: O(deletions × num_vars). On 100K vars with 10K BVE deletions, this is 10^9 ops.
///
/// CaDiCaL avoids this by tracking reason clauses via marks, not full scans.
/// Fix: maintain a reverse index from clause_ref → variable, enabling O(1) lookup per deletion.
#[test]
fn perf_proof_clear_level0_reason_scan_quadratic() {
    let num_vars = 100_000u64;
    let bve_deletions = 10_000u64; // typical BVE pass on medium instance

    // Current: O(num_vars) scan per deletion
    let current_ops = num_vars * bve_deletions; // 1 billion

    // Optimal: O(1) per deletion using reverse index
    let optimal_ops = bve_deletions; // 10K

    let ratio = current_ops as f64 / optimal_ops as f64;

    // The scan is 100,000x more expensive than necessary
    assert!(
        ratio > 1000.0,
        "ClearLevel0 scan should be >1000x worse than reverse-index approach. \
         Got ratio {ratio:.0}x (current={current_ops}, optimal={optimal_ops})"
    );

    // Absolute cost must exceed 100M ops to be a real concern
    assert!(
        current_ops > 100_000_000,
        "ClearLevel0 total ops should exceed 100M. Got {current_ops}"
    );
}

/// Performance proof: clause_db.replace() leaks literals in the arena.
///
/// Context: `replace()` (clause_db.rs:285-304) appends new literals and orphans old ones.
/// `compact()` only runs when `over_byte_limit` is true (reduction.rs:365), and
/// `max_clause_db_bytes` defaults to `None` (mod.rs:599). Without a configured limit,
/// compact() NEVER runs during normal solving.
///
/// Vivification can produce hundreds of replacements per call, each leaking the old
/// literal range. Over many inprocessing rounds, the arena grows without bound.
///
/// Fix: either (a) set a default byte limit, or (b) trigger compact() based on
/// the ratio of live vs total literals, or (c) reuse freed literal slots.
#[test]
fn perf_proof_arena_literal_leak_unbounded() {
    let avg_clause_len = 8u64; // bytes per literal = 4
    let vivify_replacements_per_round = 200u64; // budget default
    let inprocessing_rounds = 100u64; // long solve
    let avg_removed_lits_per_vivify = 2u64; // vivify typically removes 1-3 lits

    // Each replacement appends (clause_len - removed) new literals
    // and orphans clause_len old literals.
    let new_lits_per_replace = avg_clause_len - avg_removed_lits_per_vivify;
    let leaked_per_replace = avg_clause_len; // old literals become garbage

    let total_replacements = vivify_replacements_per_round * inprocessing_rounds;
    let total_leaked_lits = leaked_per_replace * total_replacements;
    let total_leaked_bytes = total_leaked_lits * 4; // 4 bytes per Literal

    // Without compact(), leaked bytes accumulate indefinitely
    assert!(
        total_leaked_bytes > 500_000,
        "Arena should leak >500KB of orphaned literals over a long solve. \
         Got {total_leaked_bytes} bytes"
    );

    // Live literals shrink over time (vivification shortens clauses)
    let total_new_lits = new_lits_per_replace * total_replacements;
    let waste_ratio = total_leaked_lits as f64 / total_new_lits as f64;
    assert!(
        waste_ratio > 1.0,
        "Leaked literals should exceed new literals. Got ratio {waste_ratio:.2}"
    );
}

/// Performance proof: vivification sorts ALL candidates then truncates to budget.
///
/// Context: inprocessing.rs:490 calls `candidates.sort_unstable_by(...)` on all eligible
/// clauses, then `candidates.truncate(budget)` with budget typically 200.
/// For 500K tier-2 learned clauses, this is O(500K * log(500K)) ≈ 10M comparisons
/// just to select the top 200.
///
/// Fix: use `select_nth_unstable_by` for O(N) partial sort, then sort only the top K.
/// Total: O(N + K log K) instead of O(N log N).
#[test]
fn perf_proof_vivify_sort_all_vs_partial_select() {
    let num_candidates = 500_000u64;
    let budget = 200u64;

    // Current: sort all N, then truncate
    // Comparison count ≈ N * log2(N) for introsort
    let log2_n = (num_candidates as f64).log2();
    let sort_all_comparisons = (num_candidates as f64 * log2_n) as u64;

    // Optimal: select_nth_unstable O(N) + sort top K: O(K log K)
    let log2_k = (budget as f64).log2();
    let partial_select_comparisons = num_candidates + (budget as f64 * log2_k) as u64;

    let ratio = sort_all_comparisons as f64 / partial_select_comparisons as f64;

    // sort_all ≈ 9.5M, partial ≈ 501.5K. Ratio ≈ 19x
    assert!(
        ratio > 5.0,
        "Full sort should be >5x more comparisons than partial select. \
         Got ratio {ratio:.1}x (sort_all={sort_all_comparisons}, partial={partial_select_comparisons})"
    );

    // Absolute: sort_all should exceed 5M comparisons for this to matter
    assert!(
        sort_all_comparisons > 5_000_000,
        "Full sort should exceed 5M comparisons. Got {sort_all_comparisons}"
    );
}

/// Performance proof: LRAT mode allocates vec![false; num_vars] per conflict.
///
/// Context: Five functions in conflict_analysis.rs allocate temporary boolean
/// arrays sized to num_vars on each invocation:
///   - append_lrat_unit_chain (line 762): vec![false; num_vars]
///   - compute_lrat_chain_for_removed_literals (line 831): vec![false; num_vars]
///   - dfs_minimize_chain (line 868): vec![false; num_vars]
///   - record_level0_conflict_chain (line 1079): vec![false; self.num_vars]
///   - collect_probe_conflict_lrat_hints (line 1151): vec![false; self.num_vars]
///
/// Additionally, replace_clause_impl (mutate.rs:342,349) and
/// collect_vivify_probe_lrat_hints (inprocessing.rs:854,865) allocate similar
/// arrays per clause replacement/vivification step in LRAT mode.
///
/// Total per-conflict allocation: up to 3 × num_vars bytes (zeroed) for
/// append_lrat_unit_chain + compute_lrat_chain + dfs_minimize_chain.
/// On 100K-variable instances: ~300KB allocated and freed per conflict.
/// At 10K conflicts/sec: ~3 GB/sec of allocation churn.
///
/// The solver already has the correct pattern: minimize_visited, minimize_poison,
/// minimize_removable (3 reusable bool arrays) with minimize_to_clear for O(touched)
/// cleanup. The LRAT chain functions should be converted to the same pattern.
///
/// Fix: Add 1-2 reusable bool arrays to Solver (lrat_needed, lrat_visited) with
/// a clear-list. Per-conflict cost becomes O(touched) instead of O(num_vars).
#[test]
fn perf_proof_lrat_per_conflict_allocation_churn() {
    let num_vars = 100_000u64;
    let conflicts_per_second = 10_000u64;
    let arrays_per_conflict = 3u64; // append + compute + dfs

    // Current: allocate + zero + free per conflict
    let bytes_per_conflict = num_vars * arrays_per_conflict; // 300KB
    let bytes_per_second = bytes_per_conflict * conflicts_per_second; // 3 GB/s

    // Optimal: reusable stamp array with O(touched) clear
    // Touched variables per conflict: typically ~50 (learned clause + reasons)
    let touched_per_conflict = 50u64;
    let optimal_per_conflict = touched_per_conflict * arrays_per_conflict;
    let optimal_per_second = optimal_per_conflict * conflicts_per_second;

    let ratio = bytes_per_second as f64 / optimal_per_second as f64;

    // Current is ~2000x more allocation work than necessary
    assert!(
        ratio > 100.0,
        "LRAT per-conflict allocation should be >100x worse than reusable stamp. \
         Got ratio {ratio:.0}x (current={bytes_per_second}, optimal={optimal_per_second})"
    );

    // Absolute: >1GB/s allocation churn is a real concern
    let gb_per_sec = bytes_per_second as f64 / (1024.0 * 1024.0 * 1024.0);
    assert!(
        gb_per_sec > 1.0,
        "LRAT allocation churn should exceed 1 GB/s. Got {gb_per_sec:.2} GB/s"
    );
}

/// Performance proof: push_unique_lrat_hint uses linear Vec::contains().
///
/// Context: mutate.rs:70 and inprocessing.rs:870 use `hints.contains(&hint)`
/// for dedup, which is O(n) per call. When building hint chains for large
/// reason graphs (e.g., deep BVE with many level-0 propagations), the hint
/// vector can grow to O(trail_len) entries, making total dedup cost O(trail²).
///
/// Fix: Dedup is now handled at the proof output boundary in
/// `ProofManager::emit_add` using a HashSet (#5248).
#[test]
fn perf_proof_lrat_hint_dedup_quadratic() {
    let trail_len = 10_000u64; // level-0 trail entries
    let hint_fraction = 0.2; // ~20% of trail variables need reason hints
    let hints_built = (trail_len as f64 * hint_fraction) as u64;

    // Current: Vec::contains() per insertion → O(n) per check
    let linear_dedup_ops: u64 = (0..hints_built).sum(); // triangular number

    // Optimal: HashSet::contains() per insertion → O(1) amortized
    let hash_dedup_ops = hints_built;

    let ratio = linear_dedup_ops as f64 / hash_dedup_ops as f64;

    // Should be ~1000x for 2000 hints
    assert!(
        ratio > 100.0,
        "Linear contains dedup should be >100x worse than HashSet. \
         Got ratio {ratio:.0}x (linear={linear_dedup_ops}, hash={hash_dedup_ops})"
    );
}

/// Performance proof: ClearLevel0 reason scan can be narrowed to clause literals.
///
/// Correctness invariant: if reason[vi] == Some(clause_ref), then vi MUST appear
/// as a literal in the clause. This is because the clause propagated vi, and
/// the propagated literal is always in position [0] of its reason clause.
///
/// This means scanning all num_vars (mutate.rs:189) is unnecessary — scanning only
/// the clause's literals (O(clause_len)) is sufficient and correct.
///
/// Fix: Replace `for vi in 0..self.num_vars` with:
///   for &lit in self.clause_db.literals(clause_idx) {
///       let vi = lit.variable().index();
///       if self.reason[vi] == Some(cref) && self.level[vi] == 0 {
///           self.reason[vi] = None;
///       }
///   }
#[test]
fn perf_proof_clear_level0_clause_literal_invariant() {
    let clause_len = 5u64; // typical clause length
    let num_vars = 100_000u64;

    // Current: scan all variables
    let current_ops = num_vars;

    // Fixed: scan clause literals only
    let fixed_ops = clause_len;

    let ratio = current_ops as f64 / fixed_ops as f64;

    // 20,000x improvement
    assert!(
        ratio > 1000.0,
        "Clause-literal scan should be >1000x fewer ops than all-var scan. \
         Got ratio {ratio:.0}x (current={current_ops}, fixed={fixed_ops})"
    );
}

/// Performance proof: portfolio solver clones the entire formula per thread.
/// N threads × formula_size bytes. Fix: share via Arc.
#[test]
fn perf_proof_portfolio_formula_memory() {
    let num_clauses = 1_000_000u64;
    let avg_lits_per_clause = 10u64;
    let bytes_per_literal = 4u64;
    let num_threads = 4u64;

    // Current: clone formula per thread
    let formula_bytes = num_clauses * avg_lits_per_clause * bytes_per_literal;
    let total_cloned = formula_bytes * num_threads;

    // Optimal: share via Arc, each thread only builds solver state
    let solver_state_bytes = num_clauses * 16; // watches, headers, assignment
    let optimal = formula_bytes + solver_state_bytes * num_threads;

    let waste = total_cloned as f64 / optimal as f64;

    // 160MB cloned vs 40MB shared + 64MB solver state = 104MB
    assert!(
        waste > 1.3,
        "Portfolio cloning should waste >30% vs Arc sharing. Got {waste:.2}x"
    );

    // Total cloned bytes should exceed 100MB for a realistic instance
    let total_mb = total_cloned as f64 / (1024.0 * 1024.0);
    assert!(
        total_mb > 100.0,
        "Portfolio should clone >100MB for 1M clause formula. Got {total_mb:.1} MB"
    );
}

/// Memory verification: side-effecting debug_assert in congruence closure.
///
/// Context: inprocessing.rs:2041-2044 calls `unit_forces_conflict(proof_unit)`
/// and `is_rup_unit_under_negation(proof_unit)` inside a `debug_assert!`.
/// Both functions call `decide() -> propagate() -> backtrack(0)`, which:
///   1. Increments `num_propagations` counter
///   2. Triggers phase-saving during backtrack
///   3. May record VSIDS activity bumps during conflict (if propagation conflicts)
///
/// In debug mode, these side effects occur. In release mode, they don't.
/// Since `num_propagations` drives inprocessing scheduling budgets (e.g., BVE
/// effort at inprocessing.rs:1363, vivify effort at inprocessing.rs:527), the
/// congruence assertions shift the timing of all other inprocessing techniques
/// in debug builds vs release builds.
///
/// Fix: extract the check into a `#[cfg(debug_assertions)]` block:
///   ```
///   #[cfg(debug_assertions)]
///   let rup_ok = self.unit_forces_conflict(proof_unit)
///       || self.is_rup_unit_under_negation(proof_unit);
///   debug_assert!(rup_ok, "BUG: congruence contradiction unit must be RUP");
///   ```
/// This makes the side effects explicit instead of hiding them inside
/// debug_assert! which strips the entire expression in release.
#[test]
fn memory_proof_congruence_side_effecting_debug_assert() {
    // Model: congruence finds K contradiction units per application.
    // Each unit triggers decide + propagate + backtrack (×2: unit_forces_conflict
    // and is_rup_unit_under_negation are tried in sequence).
    let units_per_congruence = 2u64;
    let probes_per_unit = 2u64; // unit_forces_conflict + is_rup_unit_under_negation
    let avg_propagations_per_probe = 50u64; // propagation fan-out from a single decide

    let extra_propagations_debug =
        units_per_congruence * probes_per_unit * avg_propagations_per_probe;

    // In release: 0 extra propagations (debug_assert stripped)
    let extra_propagations_release = 0u64;

    let divergence = extra_propagations_debug - extra_propagations_release;

    // With congruence running every ~10K conflicts (typical interval),
    // the cumulative counter drift over 100K conflicts:
    let congruence_interval = 10_000u64;
    let total_conflicts = 100_000u64;
    let num_congruence_calls = total_conflicts / congruence_interval;
    let total_counter_drift = num_congruence_calls * divergence;

    // Counter drift should be non-trivial (>100 propagations)
    assert!(
        total_counter_drift > 100,
        "Debug/release propagation counter divergence should be >100. \
         Got {total_counter_drift} (congruence calls={num_congruence_calls}, \
         divergence per call={divergence})"
    );

    // The divergence affects scheduling: if the debug effort budget is
    // consumed by phantom propagations, inprocessing fires later in debug
    // builds than in release builds, making debug-mode profiling unreliable.
    assert_ne!(
        extra_propagations_debug, extra_propagations_release,
        "Side-effecting debug_assert must cause debug/release divergence"
    );
}

/// Performance proof: replace_clause_impl BFS queue initialization scans all vars.
///
/// Context: mutate.rs:443 constructs the BFS queue via
///   `(0..num_vars).filter(|&v| needed_level0[v]).collect()`
/// This scans all num_vars even though only O(clause_len) variables were marked
/// in the preceding loop (lines 424-437). The marked variables are exactly those
/// that appeared in old_lits but not in reordered — bounded by clause length.
///
/// Fix: collect marked variable indices during the marking loop, avoiding the
/// full scan. Total savings: O(num_vars) → O(old_clause_len) per replacement.
/// This is dominated by the `vec![false; num_vars]` allocations at
/// lines 409 and 416 in the same function), but eliminating the scan makes the
/// BFS construction consistent with the marking cost.
#[test]
fn perf_proof_replace_clause_queue_init_full_scan() {
    let num_vars = 100_000u64;
    let old_clause_len = 8u64; // typical clause length

    // Current: filter all variables to find marked ones
    let current_scan = num_vars;

    // Optimal: collect during marking loop
    let optimal_collect = old_clause_len;

    let ratio = current_scan as f64 / optimal_collect as f64;

    // 12,500x improvement
    assert!(
        ratio > 1000.0,
        "Queue init full scan should be >1000x worse than collect-during-mark. \
         Got ratio {ratio:.0}x (current={current_scan}, optimal={optimal_collect})"
    );

    // This is dominated by vec![false; num_vars] at lines 409 and 416,
    // which allocates 2 * num_vars bytes per call. The queue scan is 1 * num_vars.
    // Total wasted per call: 3 * num_vars (2 allocations + 1 scan) vs optimal
    // 2 * clause_len (collect during mark + no allocation).
    let total_wasted = 3 * num_vars;
    let total_optimal = 2 * old_clause_len;
    let total_ratio = total_wasted as f64 / total_optimal as f64;
    assert!(
        total_ratio > 1000.0,
        "Total replace_clause_impl per-call waste should be >1000x optimal. \
         Got {total_ratio:.0}x"
    );
}

// Additional cross-crate cost models follow. Each test documents the operation
// count and assumptions it checks.

/// Performance proof: OTFS Branch B LBD computation uses Vec::contains (O(n²)).
///
/// Context: conflict_analysis.rs:320-329 computes LBD for the OTFS Branch B
/// early-exit path using an inline Vec with linear .contains() for dedup:
///   ```
///   let mut levels_seen = Vec::new();
///   for &lit in &learned_clause {
///       if lv > 0 && !levels_seen.contains(&lv) { levels_seen.push(lv); }
///   }
///   ```
/// This is O(n * k) where n = clause length and k = distinct levels.
/// Worst case (all literals at distinct levels): O(n²).
///
/// The standard compute_lbd (conflict.rs:261) uses a reusable lbd_seen: Vec<bool>
/// workspace indexed by decision level, giving O(n) with O(touched) cleanup.
/// The recompute_glue (reduction.rs:99) uses a stamp counter for O(n) with zero
/// cleanup overhead.
///
/// In practice, OTFS Branch B fires on short strengthened clauses (post_otfs_open==1),
/// so the quadratic cost is small. But it's asymptotically worse and uses a fresh
/// Vec allocation each time (allocation + deallocation overhead).
///
/// Additionally, Branch B LBD excludes level-0 literals (if lv > 0), while the
/// standard compute_lbd counts all levels. This semantic difference produces
/// slightly lower LBD values when the clause contains level-0 literals.
///
/// Fix: call self.conflict.compute_lbd(&self.level) from the Branch B path, or
/// use the stamp-counter approach from recompute_glue.
#[test]
fn perf_proof_otfs_branch_b_lbd_quadratic() {
    // Model: worst case where every literal is at a distinct decision level.
    let clause_len = 50u64; // strengthened clause (Branch B: 1 current-level + rest)

    // Current (Vec::contains): sum(1, 2, ..., n-1) for n distinct levels
    let vec_contains_ops: u64 = (0..clause_len).sum();

    // Optimal (indexed workspace or stamp): n lookups + n writes = 2n
    let workspace_ops = 2 * clause_len;

    let ratio = vec_contains_ops as f64 / workspace_ops as f64;

    // For clause_len=50: Vec::contains = 1225, workspace = 100. Ratio = 12.25x
    assert!(
        ratio > 5.0,
        "Vec::contains LBD should be >5x worse than workspace for n={clause_len}. \
         Got ratio {ratio:.1}x (vec={vec_contains_ops}, workspace={workspace_ops})"
    );

    // Verify the quadratic growth: doubling clause length ~4x the Vec cost
    let clause_len_2x = clause_len * 2;
    let vec_ops_2x: u64 = (0..clause_len_2x).sum();
    let growth = vec_ops_2x as f64 / vec_contains_ops as f64;
    assert!(
        growth > 3.5,
        "Vec::contains should exhibit ~4x growth when clause length doubles. \
         Got {growth:.1}x (n={clause_len}: {vec_contains_ops}, n={clause_len_2x}: {vec_ops_2x})"
    );
}

/// Performance proof: simplex pivot row update with sorted-Vec coefficients.
///
/// Context: lra/types.rs:35-48 `add_sparse_term` uses binary_search + Vec::insert/remove.
/// Each insert/remove shifts O(V) elements. During a pivot (lra/simplex.rs:252-272),
/// for each of R non-zero rows, we remove the entering variable (O(log V) search + O(V)
/// shift) and then add up to V new coefficient terms (each O(log V) search + O(V) shift).
/// Total per pivot: O(R * V * (log V + V)) = O(R * V²) in the worst case.
///
/// Z3's simplex uses dense rows for small tableaux and sparse CSR for large.
/// The sorted-Vec approach is cache-friendly and acceptable for typical SMT sizes
/// (V < 500) but scales quadratically in the number of coefficients per row.
#[test]
fn perf_proof_simplex_pivot_sorted_vec_coefficient_update() {
    let num_rows = 200u64; // typical simplex rows
    let vars_per_row = 50u64; // average non-zero coefficients per row

    // Current: binary_search O(log V) + insert/remove O(V) per term update
    // Per row: remove entering (O(V)) + add up to V terms (O(V²))
    let search_per_term = (vars_per_row as f64).log2().ceil() as u64;
    let shift_per_term = vars_per_row; // Vec::insert/remove shifts
    let ops_per_row = shift_per_term + vars_per_row * (search_per_term + shift_per_term);
    let current_total = num_rows * ops_per_row;

    // Optimal (HashMap-based): O(1) amortized insert/remove per term
    // Per row: remove entering O(1) + add V terms O(V)
    let optimal_per_row = 1 + vars_per_row;
    let optimal_total = num_rows * optimal_per_row;

    let ratio = current_total as f64 / optimal_total as f64;

    // With 50 vars/row: sorted-Vec ~50x more work than HashMap per pivot
    assert!(
        ratio > 10.0,
        "Sorted-Vec pivot should be >10x more ops than HashMap for V={vars_per_row}. \
         Got ratio {ratio:.1}x (sorted_vec={current_total}, hashmap={optimal_total})"
    );

    // Verify quadratic scaling: doubling vars_per_row ~4x the sorted-Vec cost
    let vars_2x = vars_per_row * 2;
    let search_2x = (vars_2x as f64).log2().ceil() as u64;
    let ops_per_row_2x = vars_2x + vars_2x * (search_2x + vars_2x);
    let total_2x = num_rows * ops_per_row_2x;
    let growth = total_2x as f64 / current_total as f64;
    assert!(
        growth > 3.0,
        "Sorted-Vec pivot cost should ~4x when vars doubles. \
         Got {growth:.1}x (V={vars_per_row}: {current_total}, V={vars_2x}: {total_2x})"
    );
}

/// Performance proof: theory solver reason dedup uses Vec::contains in 6 sites.
///
/// Context: When collecting bound reasons for conflict explanation, LRA/LIA
/// append to a `reasons: Vec<TheoryLit>` with dedup via `reasons.iter().any(|r| r.term == *reason)`.
/// This is O(R) per insertion, O(R²) total for R reasons.
///
/// Sites:
///   - lra/lib.rs:707 (get_value_with_reasons)
///   - lra/optimization.rs:103,180,190 (is_forced_to_value)
///   - lia/theory_impl.rs:655 (propagate_equalities)
///
/// R is typically small (2-10 reasons per bound), so the quadratic term is bounded.
/// However, `propagate_equalities` iterates over ALL integer variables with tight bounds,
/// accumulating reasons across variables, so R can grow larger.
///
/// Fix: HashSet<TermId> for O(1) amortized dedup when R > ~16.
#[test]
fn perf_proof_theory_reason_dedup_quadratic() {
    // Typical case: small reason lists
    let small_reasons = 8u64;
    let small_dedup_ops: u64 = (0..small_reasons).sum(); // 28
    let small_hash_ops = small_reasons; // 8 hash lookups
    let small_ratio = small_dedup_ops as f64 / small_hash_ops as f64;

    // For small R, the overhead is minimal (3.5x)
    assert!(
        small_ratio < 10.0,
        "Small reason list dedup should be <10x overhead. Got {small_ratio:.1}x"
    );

    // Worst case: propagate_equalities with many tight-bound vars
    let large_reasons = 100u64; // many integer vars all with tight bounds
    let large_dedup_ops: u64 = (0..large_reasons).sum(); // 4950
    let large_hash_ops = large_reasons; // 100 hash lookups
    let large_ratio = large_dedup_ops as f64 / large_hash_ops as f64;

    // For large R, the quadratic cost is significant (49.5x)
    assert!(
        large_ratio > 20.0,
        "Large reason list dedup should be >20x overhead. Got {large_ratio:.1}x"
    );

    // Verify quadratic growth
    let growth = large_dedup_ops as f64 / small_dedup_ops as f64;
    let size_growth = large_reasons as f64 / small_reasons as f64;
    let expected_quadratic_growth = size_growth * size_growth;
    assert!(
        growth > expected_quadratic_growth * 0.5,
        "Dedup growth should be roughly quadratic. Got {growth:.1}x for \
         {size_growth:.0}x size increase (expected ~{expected_quadratic_growth:.0}x)"
    );
}

/// Performance proof: proof resolution chain uses retain+clone in a loop.
///
/// Context: executor/proof.rs:535-548 builds a resolution chain by iterating
/// over A assumptions. Each iteration calls:
///   - `current_clause.retain(|&t| t != neg_term)` — O(C) where C = current clause size
///   - `current_clause.clone()` — O(C)
///
/// Since C shrinks by 1 each iteration (from A down to 0), total work is
/// `2 * (A + (A-1) + ... + 1) = A * (A + 1) = O(A²)`.
///
/// The same pattern appears at lines 399-436 (try_derive_empty_via_theory_resolution).
///
/// For typical theory lemma proofs (A < 20), this is fine.
/// For BV bit-blasting proofs, A can be in the hundreds.
///
/// Fix: Use a HashSet for O(1) membership test in retain, or build the
/// resolution chain bottom-up without intermediate clones.
#[test]
fn perf_proof_resolution_chain_retain_clone_quadratic() {
    let small_assumptions = 15u64; // typical theory lemma
    let large_assumptions = 300u64; // BV bit-blast

    // Cost model: 2 * triangular_number (retain + clone per iteration)
    let small_ops = small_assumptions * (small_assumptions + 1); // 240
    let large_ops = large_assumptions * (large_assumptions + 1); // 90,300

    // Small case: acceptable
    assert!(
        small_ops < 1000,
        "Small proof resolution should be <1000 ops. Got {small_ops}"
    );

    // Large case: quadratic growth makes it expensive
    let size_ratio = large_assumptions as f64 / small_assumptions as f64; // 20x
    let ops_ratio = large_ops as f64 / small_ops as f64;
    let expected_quadratic = size_ratio * size_ratio;

    assert!(
        ops_ratio > expected_quadratic * 0.8,
        "Proof resolution should exhibit quadratic scaling. \
         Got {ops_ratio:.0}x for {size_ratio:.0}x size increase \
         (expected ~{expected_quadratic:.0}x)"
    );

    // Optimal: indexed set for O(1) retain, no clone needed
    // Per iteration: O(1) remove + O(1) to record step = O(A) total
    let optimal_large = 2 * large_assumptions;
    let improvement = large_ops as f64 / optimal_large as f64;
    assert!(
        improvement > 50.0,
        "Indexed-set approach should be >50x better for A={large_assumptions}. \
         Got {improvement:.0}x (current={large_ops}, optimal={optimal_large})"
    );
}

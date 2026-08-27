// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

fn emit_dimacs_human_search_core(solver: &SatSolver) {
    let props = solver.num_propagations();
    let search_props = solver.num_search_propagations();
    let confs = solver.num_conflicts();
    let decs = solver.num_decisions();
    let (mli_detected, mli_reimplied, mli_used) = solver.mli_stats();
    safe_eprintln!("c");
    safe_eprintln!("c --- AY statistics ---");
    safe_eprintln!("c propagations:    {props:>12}");
    safe_eprintln!("c search props:    {search_props:>12}");
    safe_eprintln!("c conflicts:       {confs:>12}");
    safe_eprintln!("c decisions:       {decs:>12}");
    safe_eprintln!("c restarts:        {:>12}", solver.num_restarts());
    safe_eprintln!("c cold_restarts:   {:>12}", solver.num_cold_restarts());
    {
        // CaDiCaL prints `reused: N (X% per restart)`; AY had no equivalent, so
        // its trail-reuse rate was unobservable.
        let restarts = solver.num_restarts();
        let reuse_restarts = solver.num_trail_reuse_restarts();
        let pct = if restarts > 0 {
            100.0 * reuse_restarts as f64 / restarts as f64
        } else {
            0.0
        };
        safe_eprintln!("c trail_reused:    {reuse_restarts:>12}   {pct:>6.2} % per restart");
        safe_eprintln!(
            "c trail_reuse_lvl: {:>12}",
            solver.num_trail_reused_levels()
        );
        // Mean trail occupancy and mean depth at conflict. `decisions` is
        // Sum(decision_level - target_level), so depth is one of its terms and
        // was previously unobservable.
        if confs > 0 {
            let mean_trail = solver.trail_at_conflict_sum() as f64 / confs as f64;
            let mean_level = solver.level_at_conflict_sum() as f64 / confs as f64;
            safe_eprintln!("c trail_at_confl:  {mean_trail:>12.1}   mean");
            safe_eprintln!("c level_at_confl:  {mean_level:>12.1}   mean");
        }
    }
    safe_eprintln!("c chrono_bt:       {:>12}", solver.num_chrono_backtracks());
    safe_eprintln!("c forced_bt:       {:>12}", solver.num_forced_backtracks());
    safe_eprintln!("c mli_detected:    {mli_detected:>12}");
    safe_eprintln!("c mli_reimplied:   {mli_reimplied:>12}");
    safe_eprintln!("c mli_used_anlyz:  {mli_used:>12}");
    safe_eprintln!("c random_decs:     {:>12}", solver.num_random_decisions());
    safe_eprintln!(
        "c approxbcp_noop:  {:>12}",
        solver.approx_bcp_noop_matched()
    );
    safe_eprintln!(
        "c approxbcp_conf:  {:>12}",
        solver.approx_bcp_conflict_matched()
    );
    safe_eprintln!(
        "c approxbcp_bad:   {:>12}",
        solver.approx_bcp_mismatch_detected()
    );
    safe_eprintln!("c fixed_vars:      {:>12}", solver.num_fixed());
    safe_eprintln!("c original_cls:    {:>12}", solver.num_original_clauses());
    safe_eprintln!("c learned_cls:     {:>12}", solver.num_learned_clauses());
}

fn emit_dimacs_human_search_ratios(solver: &SatSolver) {
    let props = solver.num_propagations();
    let confs = solver.num_conflicts();
    let decs = solver.num_decisions();
    let props_per_conf = if confs > 0 {
        props as f64 / confs as f64
    } else {
        0.0
    };
    let props_per_dec = if decs > 0 {
        props as f64 / decs as f64
    } else {
        0.0
    };
    safe_eprintln!("c props/conflict:  {props_per_conf:>12.1}");
    safe_eprintln!("c props/decision:  {props_per_dec:>12.1}");
    let search_ticks = solver.total_search_ticks();
    safe_eprintln!("c search_ticks:    {search_ticks:>12}");
    // Per-mode ticks are the real stabilization share (kissat mode.c budgets
    // stable phases in exactly the ticks the previous focused phase used);
    // focused_decs/stable_decs are inflated by post-restart re-descent.
    let (focused_ticks, stable_ticks) = solver.mode_search_ticks();
    safe_eprintln!("c ticks_focused:   {focused_ticks:>12}");
    safe_eprintln!("c ticks_stable:    {stable_ticks:>12}");
    let ticks_per_conf = if confs > 0 {
        search_ticks as f64 / confs as f64
    } else {
        0.0
    };
    safe_eprintln!("c ticks/conflict:  {ticks_per_conf:>12.1}");
    safe_eprintln!("c peak_dec_level:  {:>12}", solver.peak_decision_level());
    safe_eprintln!("c avg_dec_level:   {:>12.1}", solver.avg_decision_level());
}

fn emit_dimacs_human_sidecars(
    guard_cover: Option<&GuardCoverSidecarRunStats>,
    separator_cover: Option<&SeparatorCoverSidecarRunStats>,
) {
    if let Some(sidecar) = guard_cover {
        safe_eprintln!("c --- guard-cover sidecar ---");
        safe_eprintln!("c gc_path:         {}", sidecar.path);
        safe_eprintln!("c gc_status:       {:>12}", sidecar.status_label());
        safe_eprintln!(
            "c gc_empty_cut:    {:>12}",
            if sidecar.injected_empty_cut {
                "yes"
            } else {
                "no"
            }
        );
        safe_eprintln!("c gc_cuts:         {:>12}", sidecar.cuts);
        safe_eprintln!("c gc_guards:       {:>12}", sidecar.guards);
        safe_eprintln!("c gc_budget_rhs:   {:>12}", sidecar.budget_rhs);
        safe_eprintln!("c gc_deficit:      {:>12}", sidecar.packed_deficit);
    }
    if let Some(sidecar) = separator_cover {
        safe_eprintln!("c --- separator-cover sidecar ---");
        safe_eprintln!("c sc_path:         {}", sidecar.path);
        safe_eprintln!("c sc_status:       {:>12}", sidecar.status_label());
        safe_eprintln!(
            "c sc_empty_cut:    {:>12}",
            if sidecar.injected_empty_cut {
                "yes"
            } else {
                "no"
            }
        );
        safe_eprintln!("c sc_sep_vars:     {:>12}", sidecar.separator_vars);
        safe_eprintln!("c sc_cubes:        {:>12}", sidecar.cubes);
        safe_eprintln!("c sc_covered_asgn: {:>12}", sidecar.covered_assignments);
    }
}

/// Independent-support brancher counters (`solver/indep_support.rs`). Silent
/// unless the analysis actually ran, so off-route stats output is unchanged.
fn emit_dimacs_human_indep_support(solver: &SatSolver) {
    let (installed, size, decidable, gates, rejected, decisions, fallbacks, ns) =
        solver.indep_support_report();
    if size == 0 && rejected == 0 && gates == 0 && ns == 0 {
        return;
    }
    safe_eprintln!("c --- indep support ---");
    safe_eprintln!("c indep_support_installed_size: {:>10}", installed);
    safe_eprintln!("c indep_support_size: {:>10}", size);
    safe_eprintln!("c indep_support_decidable_vars: {:>10}", decidable);
    safe_eprintln!("c indep_support_gates: {:>10}", gates);
    safe_eprintln!("c indep_support_rejected_size: {:>10}", rejected);
    safe_eprintln!("c indep_support_decisions: {:>10}", decisions);
    safe_eprintln!("c indep_support_fallback_decisions: {:>10}", fallbacks);
    safe_eprintln!("c indep_support_ms: {:>10}", ns / 1_000_000);
}

/// Bit-parallel support-enumerator counters (`solver/indep_enum.rs`). Silent
/// unless the probe actually ran.
fn emit_dimacs_human_indep_enum(solver: &SatSolver) {
    let (
        size,
        constraints,
        projected,
        admitted,
        blocks,
        assignments,
        visits,
        exhausted,
        stalled,
        verify_failures,
        budget_exhausted,
        ns,
    ) = solver.indep_enum_report();
    if admitted == 0 && size == 0 && ns == 0 {
        return;
    }
    safe_eprintln!("c --- indep enum ---");
    safe_eprintln!("c indep_enum_support_size: {:>10}", size);
    safe_eprintln!("c indep_enum_constraints: {:>10}", constraints);
    safe_eprintln!("c indep_enum_projected_visits: {:>10}", projected);
    safe_eprintln!("c indep_enum_admitted: {:>10}", admitted);
    safe_eprintln!("c indep_enum_blocks: {:>10}", blocks);
    safe_eprintln!("c indep_enum_assignments: {:>10}", assignments);
    safe_eprintln!("c indep_enum_visits: {:>10}", visits);
    safe_eprintln!("c indep_enum_exhausted: {:>10}", exhausted);
    safe_eprintln!("c indep_enum_stalled: {:>10}", stalled);
    safe_eprintln!("c indep_enum_verify_failures: {:>10}", verify_failures);
    safe_eprintln!("c indep_enum_budget_exhausted: {:>10}", budget_exhausted);
    safe_eprintln!("c indep_enum_ms: {:>10}", ns / 1_000_000);
    if ns > 0 {
        safe_eprintln!(
            "c indep_enum_assignments_per_s: {:>10.0}",
            assignments as f64 / (ns as f64 / 1e9)
        );
        safe_eprintln!(
            "c indep_enum_visits_per_s: {:>10.0}",
            visits as f64 / (ns as f64 / 1e9)
        );
    }
}

fn emit_dimacs_human_timing_and_lbd(solver: &SatSolver) {
    let preprocess_ns = solver.preprocess_time_ns();
    let search_ns = solver.search_time_ns();
    let lucky_ns = solver.lucky_time_ns();
    let walk_ns = solver.walk_time_ns();
    let total_ns = preprocess_ns + search_ns + lucky_ns + walk_ns;
    let inproc_ns: u64 = solver
        .inprocessing_pass_times_ns()
        .iter()
        .map(|&(_, v)| v)
        .sum();
    safe_eprintln!("c --- phase timing ---");
    safe_eprintln!("c preprocess_ms:   {:>12}", preprocess_ns / 1_000_000);
    safe_eprintln!("c lucky_ms:        {:>12}", lucky_ns / 1_000_000);
    safe_eprintln!("c walk_ms:         {:>12}", walk_ns / 1_000_000);
    // `walk_ms` is the STARTUP walk only. Report the in-search rephase walk
    // separately so "walk_ms: 0" can never again be read as "walk never ran".
    let (rw_runs, rw_skips, rw_ns) = solver.rephase_walk_report();
    safe_eprintln!("c rephase_walks:   {rw_runs:>12}");
    safe_eprintln!("c rephase_walk_ms: {:>12}", rw_ns / 1_000_000);
    safe_eprintln!("c rephase_walk_gated: {rw_skips:>9}");
    safe_eprintln!("c search_ms:       {:>12}", search_ns / 1_000_000);
    if total_ns > 0 {
        safe_eprintln!(
            "c preprocess%:     {:>11.1}%",
            preprocess_ns as f64 / total_ns as f64 * 100.0
        );
        safe_eprintln!(
            "c search%:         {:>11.1}%",
            search_ns as f64 / total_ns as f64 * 100.0
        );
        safe_eprintln!(
            "c inprocessing%:   {:>11.1}%",
            inproc_ns as f64 / total_ns as f64 * 100.0
        );
    }
    safe_eprintln!("c --- rates ---");
    let search_secs = search_ns as f64 / 1_000_000_000.0;
    if search_secs > 0.0 {
        safe_eprintln!(
            "c props/sec:       {:>12.0}",
            solver.num_propagations() as f64 / search_secs
        );
        safe_eprintln!(
            "c conflicts/sec:   {:>12.0}",
            solver.num_conflicts() as f64 / search_secs
        );
        safe_eprintln!(
            "c decisions/sec:   {:>12.0}",
            solver.num_decisions() as f64 / search_secs
        );
    }
    let confs = solver.num_conflicts();
    let decs_per_conf = if confs > 0 {
        solver.num_decisions() as f64 / confs as f64
    } else {
        0.0
    };
    safe_eprintln!("c decs/conflict:   {decs_per_conf:>12.2}");
    safe_eprintln!("c --- learned clause LBD distribution ---");
    let (lbd_sum, lbd_count) = solver.lbd_sum_count();
    if lbd_count > 0 {
        safe_eprintln!(
            "c avg_lbd:         {:>12.2}",
            lbd_sum as f64 / lbd_count as f64
        );
    }
    let buckets = solver.lbd_buckets();
    safe_eprintln!("c lbd_1:           {:>12}", buckets[0]);
    safe_eprintln!("c lbd_2:           {:>12}", buckets[1]);
    safe_eprintln!("c lbd_3to5:        {:>12}", buckets[2]);
    safe_eprintln!("c lbd_6to10:       {:>12}", buckets[3]);
    safe_eprintln!("c lbd_11plus:      {:>12}", buckets[4]);
}

fn emit_dimacs_human_bcp_and_search(solver: &SatSolver) {
    let (bcp_blocker, bcp_binary, bcp_scan) = solver.bcp_stats();
    let saved = solver.bcp_saved_pos_stats();
    let long = solver.bcp_long_scan_stats();
    safe_eprintln!("c --- BCP internals ---");
    safe_eprintln!("c bcp_blocker_hit: {bcp_blocker:>12}");
    safe_eprintln!("c bcp_binary_hit:  {bcp_binary:>12}");
    safe_eprintln!("c bcp_scan_steps:  {bcp_scan:>12}");
    safe_eprintln!(
        "c bcp_scan_attr:   binary {:>12} nonbinary {:>12} learned {:>12} original {:>12}",
        long.scan_steps_binary,
        long.scan_steps_non_binary,
        long.scan_steps_learned,
        long.scan_steps_original
    );
    safe_eprintln!(
        "c bcp_long_spos:   {:>12} start_false {:>12} true {:>12} unassigned {:>12} none {:>12}",
        saved.long_scans,
        saved.long_start_false,
        saved.long_found_true,
        saved.long_found_unassigned,
        saved.long_no_replacement
    );
    safe_eprintln!(
        "c bcp_len18_spos:  {:>12} start_false {:>12} true {:>12} unassigned {:>12} none {:>12}",
        saved.len18_scans,
        saved.len18_start_false,
        saved.len18_found_true,
        saved.len18_found_unassigned,
        saved.len18_no_replacement
    );
    let total_scans: u64 = long.scans_by_len.iter().sum();
    if total_scans > 0 || long.long_blocker_fastpath_hits > 0 {
        safe_eprintln!(
            "c bcp_long_scan:  {:>12} found {:>12} unit {:>12} conflict {:>12} learned {:>12}",
            total_scans,
            long.found_replacement_by_len.iter().sum::<u64>(),
            long.unit_by_len.iter().sum::<u64>(),
            long.conflict_by_len.iter().sum::<u64>(),
            long.learned_scans_by_len.iter().sum::<u64>()
        );
        safe_eprintln!("c bcp_long_block: {:>12}", long.long_blocker_fastpath_hits);
    }
    safe_eprintln!("c jumped_reasons:  {:>12}", solver.jumped_reasons());
    let (otfs_cand, otfs_sub, otfs_str) = solver.otfs_stats();
    safe_eprintln!("c otfs_candidates: {otfs_cand:>12}");
    safe_eprintln!("c otfs_subsumed:   {otfs_sub:>12}");
    safe_eprintln!("c otfs_strength:   {otfs_str:>12}");
    safe_eprintln!("c otfs_branch_b:   {:>12}", solver.otfs_branch_b());
    safe_eprintln!("c otfs_branch_c:   {:>12}", solver.otfs_branch_c());
    safe_eprintln!("c otfs_cls_subsmd: {:>12}", solver.otfs_clause_subsumed());
    let (attempts, improvements, skipped) = solver.ibcl_stats();
    let skipped_pivots = solver.ibcl_skipped_missing_pivots();
    if attempts > 0 || skipped > 0 || skipped_pivots > 0 {
        safe_eprintln!("c ibcl_attempts:   {attempts:>12}");
        safe_eprintln!("c ibcl_improved:   {improvements:>12}");
        safe_eprintln!("c ibcl_skip_short: {skipped:>12}");
        safe_eprintln!("c ibcl_skip_pivot: {skipped_pivots:>12}");
    }
    let (entries, iterations, max_depth, saturated) = solver.bcp_theory_fixpoint_stats();
    if entries > 0 {
        safe_eprintln!("c fp_entries:      {entries:>12}");
        safe_eprintln!("c fp_iterations:   {iterations:>12}");
        safe_eprintln!(
            "c fp_avg_depth:    {:>12.2}",
            iterations as f64 / entries as f64
        );
        safe_eprintln!("c fp_max_depth:    {max_depth:>12}");
        safe_eprintln!("c fp_saturated:    {saturated:>12}");
    }
    safe_eprintln!("c shrink_attempts: {:>12}", solver.shrink_block_attempts());
    safe_eprintln!("c shrink_success:  {:>12}", solver.shrink_block_successes());
}

fn emit_dimacs_human_modes(solver: &SatSolver) {
    safe_eprintln!("c --- mode/heuristic ---");
    let (focused_decs, stable_decs) = solver.mode_decisions();
    let (ema_checks, ema_fires) = solver.focused_ema_stats();
    safe_eprintln!("c mode_switches:   {:>12}", solver.mode_switch_count());
    safe_eprintln!("c focused_decs:    {focused_decs:>12}");
    safe_eprintln!("c stable_decs:     {stable_decs:>12}");
    safe_eprintln!("c focused_fires:   {ema_fires:>12}");
    safe_eprintln!("c focused_checks:  {ema_checks:>12}");
    safe_eprintln!(
        "c focused_blocked: {:>12}",
        solver.focused_ema_blocked_by_conflict_gate()
    );
    safe_eprintln!("c focused_gate:    {:>12}", solver.focused_restart_gate());
    safe_eprintln!(
        "c dense_gate_upd:  {:>12}",
        solver.dense_mutex_focused_restart_gate_updates()
    );
    safe_eprintln!(
        "c dense_rt_check:  {:>12}",
        solver.dense_mutex_focused_restart_runtime_checked()
    );
    safe_eprintln!(
        "c dense_rt_cand:   {:>12}",
        u64::from(solver.dense_mutex_focused_restart_runtime_candidate())
    );
    safe_eprintln!(
        "c dense_rt_gate:   {:>12}",
        solver.dense_mutex_focused_restart_computed_gate()
    );
    safe_eprintln!("c reluctant_fires: {:>12}", solver.stable_reluctant_fires());
    safe_eprintln!("c stable_ema_rst:  {:>12}", solver.stable_ema_fires());
    safe_eprintln!("c mab_switches:    {:>12}", solver.mab_arm_switches());
}

fn emit_dimacs_human_core(
    solver: &SatSolver,
    guard_cover: Option<&GuardCoverSidecarRunStats>,
    separator_cover: Option<&SeparatorCoverSidecarRunStats>,
) {
    emit_dimacs_human_search_core(solver);
    emit_dimacs_human_sidecars(guard_cover, separator_cover);
    emit_dimacs_human_search_ratios(solver);
    emit_dimacs_human_indep_support(solver);
    emit_dimacs_human_indep_enum(solver);
    emit_dimacs_human_timing_and_lbd(solver);
    emit_dimacs_human_bcp_and_search(solver);
    emit_dimacs_human_modes(solver);
}

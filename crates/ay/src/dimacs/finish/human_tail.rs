// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

fn emit_dimacs_human_subsumption_and_database(solver: &SatSolver) {
    let sbs = solver.subsume_stats();
    safe_eprintln!(
        "c strengthened:    {val:>12}",
        val = sbs.strengthened_clauses
    );
    safe_eprintln!(
        "c strength_lits:   {val:>12}",
        val = sbs.strengthened_literals
    );
    safe_eprintln!("c total_subsumed:  {:>12}", solver.total_subsumed());
    safe_eprintln!("c  fwd_subsumed:   {:>12}", sbs.forward_subsumed);
    safe_eprintln!(
        "c  bve_bw_subsmd:  {:>12}",
        solver.bve_stats().backward_subsumed
    );
    safe_eprintln!("c  otfs_subsmd:    {:>12}", solver.otfs_clause_subsumed());
    safe_eprintln!("c  eager_subsmd:   {:>12}", solver.num_eager_subsumptions());
    let vs = solver.vivify_stats();
    safe_eprintln!("c  viv_inline_s:   {:>12}", vs.inline_subsumed);
    safe_eprintln!("c  viv_anlysis_s:  {:>12}", vs.analysis_subsumed);
    safe_eprintln!(
        "c  cong_subsmd:    {:>12}",
        solver.congruence_stats().congruence_subsumed
    );
    safe_eprintln!("c  dedup_deleted:   {:>12}", solver.dedup_deleted());
    safe_eprintln!("c --- inprocessing pass times (ms) ---");
    for (label, value) in solver.inprocessing_pass_times_ms() {
        safe_eprintln!("c {label:<16} {value:>12}");
    }
    safe_eprintln!("c --- clause db ---");
    safe_eprintln!("c flushes:         {:>12}", solver.num_flushes());
    safe_eprintln!("c reductions:      {:>12}", solver.num_reductions());
    safe_eprintln!("c arena_compacts:  {:>12}", solver.num_arena_compactions());
    safe_eprintln!(
        "c arena_cmp_skips: {:>12}",
        solver.num_arena_compaction_skips()
    );
    let factor_skips = solver.factor_skip_breakdown();
    if factor_skips.iter().any(|&(_, n)| n > 0) {
        let rendered: Vec<String> = factor_skips
            .iter()
            .filter(|&&(_, n)| n > 0)
            .map(|(tag, n)| format!("{tag}={n}"))
            .collect();
        safe_eprintln!("c factor_skips:    {}", rendered.join(" "));
    }
    safe_eprintln!("c inprobe_phases:  {:>12}", solver.inprobe_phases());
    safe_eprintln!("c eager_subsumed:  {:>12}", solver.num_eager_subsumptions());
}

fn emit_dimacs_human_elimination_techniques(solver: &SatSolver) {
    let bces = solver.bce_stats();
    safe_eprintln!("c --- BCE ---");
    safe_eprintln!("c bce_rounds:      {:>12}", bces.rounds);
    safe_eprintln!("c bce_eliminated:  {:>12}", bces.clauses_eliminated);
    safe_eprintln!("c bce_checks:      {:>12}", bces.checks_performed);
    let cces = solver.cce_stats();
    safe_eprintln!("c --- CCE ---");
    safe_eprintln!("c cce_rounds:      {:>12}", cces.rounds);
    safe_eprintln!("c cce_blocked:     {:>12}", cces.blocked);
    safe_eprintln!("c cce_cla_steps:   {:>12}", cces.cla_steps);
    let htr = solver.htr_stats();
    safe_eprintln!("c --- HTR ---");
    safe_eprintln!("c htr_rounds:      {:>12}", htr.rounds);
    safe_eprintln!("c htr_ternary:     {:>12}", htr.ternary_resolvents);
    safe_eprintln!("c htr_binary:      {:>12}", htr.binary_resolvents);
    let conds = solver.conditioning_stats();
    safe_eprintln!("c --- conditioning ---");
    safe_eprintln!("c cond_rounds:     {:>12}", conds.rounds);
    safe_eprintln!("c cond_eliminated: {:>12}", conds.clauses_eliminated);
    safe_eprintln!("c cond_checked:    {:>12}", conds.candidates_checked);
    let occ_incr = solver.occ_incremental_refreshes();
    let occ_full = solver.occ_full_rebuilds();
    if occ_incr > 0 || occ_full > 0 {
        safe_eprintln!("c --- occ list ---");
        safe_eprintln!("c occ_incr_refresh:{occ_incr:>12}");
        safe_eprintln!("c occ_full_rebuild:{occ_full:>12}");
    }
    let (reductions, deleted, decays) = solver.between_solve_stats();
    if reductions > 0 {
        safe_eprintln!("c --- between-solve ---");
        safe_eprintln!("c bs_reductions:   {reductions:>12}");
        safe_eprintln!("c bs_cls_deleted:  {deleted:>12}");
        safe_eprintln!("c bs_used_decays:  {decays:>12}");
    }
    let (dbcp_skips, dbcp_calls) = solver.domain_bcp_stats();
    if dbcp_calls > 0 {
        safe_eprintln!("c --- domain BCP ---");
        safe_eprintln!("c domain_bcp_calls:{dbcp_calls:>12}");
        safe_eprintln!("c domain_bcp_skips:{dbcp_skips:>12}");
    }
    let stale_skips = solver.stale_enqueue_skips();
    if stale_skips > 0 {
        safe_eprintln!("c WARN stale_enq:  {stale_skips:>12}");
    }
    let stale_bcp = solver.stale_bcp_watch_skips();
    if stale_bcp > 0 {
        safe_eprintln!("c WARN stale_bcp:  {stale_bcp:>12}");
    }
}

fn emit_dimacs_human_native_and_memory(solver: &SatSolver) {
    safe_eprintln!("c --- backbone ---");
    safe_eprintln!("c bb_binary_units: {:>12}", solver.backbone_binary_units());
    safe_eprintln!("c --- SAT JIT competition telemetry ---");
    safe_eprintln!(
        "c sat_lc_app:     {:>12}",
        solver.sat_learned_clause_candidate_applications()
    );
    safe_eprintln!(
        "c sat_native_app: {:>12}",
        solver.sat_native_code_helper_applications()
    );
    safe_eprintln!(
        "c sat_wloop_inst: {:>12}",
        solver.sat_whole_loop_guard_installs()
    );
    safe_eprintln!(
        "c sat_wloop_app:  {:>12}",
        solver.sat_whole_loop_guard_applications()
    );
    safe_eprintln!(
        "c sat_subsume_app:{:>12}",
        solver.sat_subsumption_native_applications()
    );
    safe_eprintln!(
        "c sat_confjit_app:{:>12}",
        solver.sat_conflict_analysis_native_applications()
    );
    if solver.sat_propagation_native_active() {
        safe_eprintln!("c --- SAT propagation native telemetry ---");
        safe_eprintln!("c sat_prop_active: {:>12}", "yes");
        safe_eprintln!(
            "c sat_prop_cls:    {:>12}",
            solver.sat_propagation_native_clauses()
        );
        safe_eprintln!(
            "c sat_prop_rounds: {:>12}",
            solver.sat_propagation_native_rounds()
        );
        safe_eprintln!(
            "c sat_prop_props:  {:>12}",
            solver.sat_propagation_native_propagations()
        );
        safe_eprintln!(
            "c sat_prop_confl:  {:>12}",
            solver.sat_propagation_native_conflicts()
        );
        safe_eprintln!(
            "c sat_prop_cmp_us: {:>12}",
            solver.sat_propagation_native_compile_time_us()
        );
    }
    let cc_total = solver.code_cache_total_bytes();
    let cc_peak = solver.code_cache_peak_bytes();
    if cc_peak > 0 {
        safe_eprintln!("c --- code cache ---");
        safe_eprintln!("c cc_total_bytes:  {:>12}", cc_total);
        safe_eprintln!("c cc_peak_bytes:   {:>12}", cc_peak);
        safe_eprintln!("c cc_evictions:    {:>12}", solver.code_cache_evictions());
        safe_eprintln!(
            "c cc_bytes_evict:  {:>12}",
            solver.code_cache_bytes_evicted()
        );
    }
    safe_eprintln!("c --- memory ---");
    safe_eprintln!("c arena_words:     {:>12}", solver.arena_words());
    safe_eprintln!("c arena_dead:      {:>12}", solver.arena_dead_words());
    safe_eprintln!("c arena_slots:     {:>12}", solver.arena_clause_slots());
    safe_eprintln!("c active_clauses:  {:>12}", solver.active_clause_count());
    safe_eprintln!("c");
}

fn emit_dimacs_human_tail(solver: &SatSolver) {
    emit_dimacs_human_subsumption_and_database(solver);
    emit_dimacs_human_elimination_techniques(solver);
    emit_dimacs_human_native_and_memory(solver);
}

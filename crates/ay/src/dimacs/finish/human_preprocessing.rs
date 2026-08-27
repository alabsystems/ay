// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

fn emit_dimacs_human_lookahead_and_bve(solver: &SatSolver) {
    let (la_rounds, la_failed, la_used) = solver.lookahead_stats();
    if la_rounds > 0 {
        safe_eprintln!("c --- lookahead ---");
        safe_eprintln!("c la_rounds:       {la_rounds:>12}");
        safe_eprintln!("c la_failed_lits:  {la_failed:>12}");
        safe_eprintln!("c la_decs_used:    {la_used:>12}");
    }
    let bs = solver.bve_stats();
    safe_eprintln!("c --- preprocessing ---");
    safe_eprintln!("c bve_eliminated:  {val:>12}", val = bs.vars_eliminated);
    safe_eprintln!("c bve_cls_removed: {val:>12}", val = bs.clauses_removed);
    safe_eprintln!("c bve_resolvents:  {val:>12}", val = bs.resolvents_added);
    safe_eprintln!("c bve_tautologies: {val:>12}", val = bs.tautologies_skipped);
    safe_eprintln!("c bve_single_otfs: {val:>12}", val = bs.single_otfs);
    safe_eprintln!("c bve_double_otfs: {val:>12}", val = bs.double_otfs);
    safe_eprintln!(
        "c bve_root_pruned: {val:>12}",
        val = bs.root_literals_pruned
    );
    safe_eprintln!(
        "c bve_root_sat:    {val:>12}",
        val = bs.root_satisfied_parents
    );
    safe_eprintln!("c bve_max_res_len: {val:>12}", val = bs.max_resolvent_len);
    safe_eprintln!("c bve_nonunit_res: {val:>12}", val = bs.non_unit_resolvents);
    if bs.non_unit_resolvents > 0 {
        safe_eprintln!(
            "c bve_avg_res_len: {val:>12.1}",
            val = bs.total_resolvent_literals as f64 / bs.non_unit_resolvents as f64
        );
    }
    let net = bs.resolvents_added as i64 - bs.clauses_removed as i64;
    safe_eprintln!("c bve_net_clauses: {net:>12}");
    safe_eprintln!("c bve_bw_subsumed: {val:>12}", val = bs.backward_subsumed);
    safe_eprintln!(
        "c bve_bw_strength: {val:>12}",
        val = bs.backward_strengthened
    );
    safe_eprintln!("c bve_bw_units:    {val:>12}", val = bs.backward_units);
    safe_eprintln!(
        "c bve_bw_sig_filt: {val:>12}",
        val = bs.backward_sig_filtered
    );
    if bs.lrat_preflight_rejected > 0 {
        safe_eprintln!(
            "c bve_lrat_reject:{val:>12}",
            val = bs.lrat_preflight_rejected
        );
        safe_eprintln!(
            "c bve_lrat_src_hid:{val:>11}",
            val = bs.lrat_preflight_missing_or_hidden_source_id
        );
        safe_eprintln!(
            "c bve_lrat_del_dead:{val:>10}",
            val = bs.lrat_preflight_deletion_target_not_live
        );
        safe_eprintln!(
            "c bve_lrat_cleanup:{val:>11}",
            val = bs.lrat_preflight_replacement_cleanup_unit
        );
        safe_eprintln!(
            "c bve_lrat_plan: {val:>12}",
            val = bs.lrat_preflight_planned_add_rejected
        );
        safe_eprintln!(
            "c bve_lrat_out_id:{val:>11}",
            val = bs.lrat_preflight_planned_output_id_mismatch
        );
        safe_eprintln!(
            "c bve_lrat_unknown:{val:>10}",
            val = bs.lrat_preflight_planned_unknown_hint
        );
    }
    safe_eprintln!("c bve_fastelim_v:  {val:>12}", val = bs.fast_elim_vars);
    safe_eprintln!("c bve_fastelim_c:  {val:>12}", val = bs.fast_elim_clauses);
    let search_secs = solver.search_time_ns() as f64 / 1_000_000_000.0;
    if search_secs > 0.0 && bs.vars_eliminated > 0 {
        safe_eprintln!(
            "c bve_elim/sec:    {:>12.0}",
            bs.vars_eliminated as f64 / search_secs
        );
    }
    let gs = solver.gate_stats();
    safe_eprintln!("c gate_and:        {val:>12}", val = gs.and_gates);
    safe_eprintln!("c gate_xor:        {val:>12}", val = gs.xor_gates);
    safe_eprintln!("c gate_equiv:      {val:>12}", val = gs.equivalences);
    safe_eprintln!("c gate_ite:        {val:>12}", val = gs.ite_gates);
    safe_eprintln!(
        "c probe_failed:    {val:>12}",
        val = solver.probe_stats().failed
    );
}

fn emit_dimacs_human_simplification(solver: &SatSolver, route: DimacsFinishStatisticsRoute) {
    let cs = solver.congruence_stats();
    let ss = solver.sweep_stats();
    safe_eprintln!("c --- simplification ---");
    safe_eprintln!("c cong_rounds:     {val:>12}", val = cs.rounds);
    safe_eprintln!("c cong_gates:      {val:>12}", val = cs.gates_analyzed);
    safe_eprintln!("c cong_equivs:     {val:>12}", val = cs.equivalences_found);
    safe_eprintln!("c cong_lits_rwt:   {val:>12}", val = cs.literals_rewritten);
    safe_eprintln!("c sweep_rounds:    {val:>12}", val = ss.rounds);
    safe_eprintln!("c sweep_lits_rwt:  {val:>12}", val = ss.literals_rewritten);
    safe_eprintln!("c sweep_equivs:    {val:>12}", val = ss.kitten_equivalences);
    safe_eprintln!("c sweep_environs:  {val:>12}", val = ss.kitten_environments);
    safe_eprintln!("c sweep_backbone:  {val:>12}", val = ss.kitten_backbone);
    safe_eprintln!("c sweep_cls_rwt:   {val:>12}", val = ss.clauses_rewritten);
    let sy = solver.symmetry_report();
    safe_eprintln!("c symmetry_runs:   {val:>12}", val = sy.runs);
    safe_eprintln!("c symmetry_pairs:  {val:>12}", val = sy.pairs_detected);
    safe_eprintln!("c symmetry_groups: {val:>12}", val = sy.groups_nontrivial);
    safe_eprintln!("c symmetry_grp_ob: {val:>12}", val = sy.groups_over_budget);
    safe_eprintln!("c symmetry_grp_max:{val:>12}", val = sy.largest_group);
    safe_eprintln!("c symmetry_sb_cls: {val:>12}", val = sy.sb_clauses_added);
    safe_eprintln!(
        "c symmetry_skip:   {val:>12}",
        val = sy.skipped.unwrap_or("-")
    );
    for (route, outcome) in &sy.routes {
        safe_eprintln!("c symmetry_route:  {route:<12} {outcome}");
    }
    match route {
        DimacsFinishStatisticsRoute::Rescue => emit_startup_capability_plan_unavailable(
            "finalize-rescue",
            "retry startup plan differs from the discarded first attempt",
        ),
        DimacsFinishStatisticsRoute::Primary => emit_startup_capability_plan(solver),
    }
    let ds = solver.decompose_stats();
    let ts = solver.transred_stats();
    let fs = solver.factor_stats();
    safe_eprintln!("c decomp_rounds:   {val:>12}", val = ds.rounds);
    safe_eprintln!("c decomp_subst:    {val:>12}", val = ds.substituted);
    safe_eprintln!("c transred_rounds: {val:>12}", val = ts.rounds);
    safe_eprintln!("c transred_cls_rm: {val:>12}", val = ts.clauses_removed);
    safe_eprintln!("c factor_rounds:   {val:>12}", val = fs.rounds);
    safe_eprintln!("c factor_count:    {val:>12}", val = fs.factored_count);
}

fn emit_dimacs_human_rebuild_rates(solver: &SatSolver) {
    let (pr_ns, pr_props) = solver.post_rebuild_bcp_stats();
    if pr_props > 0 && pr_ns > 0 {
        safe_eprintln!(
            "c post_rw_Mpps:    {:>11.1}",
            pr_props as f64 / (pr_ns as f64 / 1_000.0)
        );
    }
    let (fr_ns, fr_props) = solver.post_full_rebuild_bcp_stats();
    if fr_props > 0 && fr_ns > 0 {
        safe_eprintln!(
            "c full_rw_Mpps:    {:>11.1}",
            fr_props as f64 / (fr_ns as f64 / 1_000.0)
        );
    }
    let (ir_ns, ir_props) = solver.post_incremental_reconnect_bcp_stats();
    if ir_props > 0 && ir_ns > 0 {
        safe_eprintln!(
            "c incr_rw_Mpps:    {:>11.1}",
            ir_props as f64 / (ir_ns as f64 / 1_000.0)
        );
    }
    let props = solver.num_propagations();
    let search_ns = solver.search_time_ns();
    if props > 0 && search_ns > 0 {
        safe_eprintln!(
            "c overall_Mpps:    {:>11.1}",
            props as f64 / (search_ns as f64 / 1_000.0)
        );
    }
}

fn emit_dimacs_human_inprocessing(solver: &SatSolver) {
    let vs = solver.vivify_stats();
    safe_eprintln!("c --- inprocessing ---");
    safe_eprintln!("c inproc_rounds:   {:>12}", solver.inprocessing_rounds());
    safe_eprintln!(
        "c incr_inproc_rnd: {:>12}",
        solver.incremental_inprocessing_rounds()
    );
    safe_eprintln!(
        "c inproc_simplif:  {:>12}",
        solver.inprocessing_simplifications()
    );
    safe_eprintln!("c rebuild_watch_us:{:>12}", solver.rebuild_watches_us());
    safe_eprintln!("c rebuild_watch_n: {:>12}", solver.rebuild_watches_calls());
    safe_eprintln!(
        "c full_rw_us:      {:>12}",
        solver.full_rebuild_watches_us()
    );
    safe_eprintln!(
        "c full_rw_n:       {:>12}",
        solver.full_rebuild_watches_calls()
    );
    safe_eprintln!(
        "c incr_rw_us:      {:>12}",
        solver.incremental_reconnect_watches_us()
    );
    safe_eprintln!(
        "c incr_rw_n:       {:>12}",
        solver.incremental_reconnect_watches_calls()
    );
    emit_dimacs_human_rebuild_rates(solver);
    safe_eprintln!("c vivify_examined: {val:>12}", val = vs.clauses_examined);
    safe_eprintln!(
        "c vivify_strength: {val:>12}",
        val = vs.clauses_strengthened
    );
    safe_eprintln!("c vivify_lits_rm:  {val:>12}", val = vs.literals_removed);
    safe_eprintln!("c vivify_sat:      {val:>12}", val = vs.clauses_satisfied);
    safe_eprintln!("c viv_irr_exam:    {val:>12}", val = vs.irred_examined);
    safe_eprintln!("c viv_irr_str:     {val:>12}", val = vs.irred_strengthened);
    safe_eprintln!(
        "c viv_irr_lits_rm: {val:>12}",
        val = vs.irred_literals_removed
    );
    safe_eprintln!("c viv_irr_del:     {val:>12}", val = vs.irred_deleted);
    safe_eprintln!(
        "c viv_irr_calls_pp:{val:>12}",
        val = vs.irred_calls_preprocess
    );
    safe_eprintln!("c viv_irr_calls_ip:{val:>12}", val = vs.irred_calls_inproc);
    safe_eprintln!("c viv_pp_rounds:   {val:>12}", val = vs.preprocess_rounds);
    safe_eprintln!("c viv_pp_ticks:    {val:>12}", val = vs.preprocess_ticks);
    safe_eprintln!(
        "c viv_pp_converged:{val:>12}",
        val = vs.preprocess_stop_converged
    );
    safe_eprintln!(
        "c viv_pp_stop_bdgt:{val:>12}",
        val = vs.preprocess_stop_budget
    );
    safe_eprintln!(
        "c viv_pp_stop_rnds:{val:>12}",
        val = vs.preprocess_stop_rounds
    );
    safe_eprintln!(
        "c viv_pp_stop_dead:{val:>12}",
        val = vs.preprocess_stop_deadline
    );
    safe_eprintln!("c viv_ip_admitted: {val:>12}", val = vs.inproc_admitted);
    safe_eprintln!(
        "c viv_ip_sk_dense: {val:>12}",
        val = vs.inproc_skip_small_dense
    );
    safe_eprintln!(
        "c viv_ip_sk_intvl: {val:>12}",
        val = vs.inproc_skip_interval
    );
    safe_eprintln!(
        "c viv_ip_sk_thrsh: {val:>12}",
        val = vs.inproc_skip_threshold
    );
    safe_eprintln!(
        "c viv_ip_sk_disab: {val:>12}",
        val = vs.inproc_skip_disabled
    );
    let search_secs = solver.search_time_ns() as f64 / 1_000_000_000.0;
    if search_secs > 0.0 && vs.clauses_strengthened > 0 {
        safe_eprintln!(
            "c vivify_str/sec:  {:>12.0}",
            vs.clauses_strengthened as f64 / search_secs
        );
    }
    safe_eprintln!(
        "c subsumed:        {val:>12}",
        val = solver.subsume_stats().forward_subsumed
    );
}

fn emit_dimacs_human_preprocessing(solver: &SatSolver, route: DimacsFinishStatisticsRoute) {
    emit_dimacs_human_lookahead_and_bve(solver);
    emit_dimacs_human_simplification(solver, route);
    emit_dimacs_human_inprocessing(solver);
}

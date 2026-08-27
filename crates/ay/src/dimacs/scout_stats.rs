// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

fn boolify_stats_counter(
    map: &mut serde_json::Map<String, serde_json::Value>,
    run_stats: &stats_output::RunStatistics,
    key: &str,
) {
    if let Some(enabled) = run_stats.counters.get(key) {
        map.insert(key.to_string(), serde_json::json!(*enabled != 0));
    }
}

fn insert_dense_clique_scout_stats(
    run_stats: &mut stats_output::RunStatistics,
    source: DimacsInputSource<'_>,
) {
    let requested = ay_core::sat_ab_switches().dense_clique_scout;
    run_stats.insert(SAT_DENSE_CLIQUE_SCOUT_REQUESTED_KEY, u64::from(requested));
    if !requested {
        insert_empty_dense_clique_scout_stats(run_stats, 0);
        return;
    }

    let Some(content) = dimacs_source_text_for_scout(source) else {
        insert_empty_dense_clique_scout_stats(run_stats, 99);
        return;
    };
    let Ok(formula) = parse_dimacs(&content) else {
        insert_empty_dense_clique_scout_stats(run_stats, 98);
        return;
    };
    let scout = ay_sat::dense_clique::DenseCliqueScout::scan(formula.num_vars, &formula.clauses);
    let detected = scout.detected();
    run_stats.insert(SAT_DENSE_CLIQUE_SCOUT_ENABLED_KEY, u64::from(detected));
    run_stats.insert(SAT_DENSE_CLIQUE_SCOUT_EXERCISED_KEY, u64::from(detected));
    run_stats.insert(
        SAT_DENSE_CLIQUE_SCOUT_REJECTION_CODE_KEY,
        scout.rejection.code(),
    );
    run_stats.insert(
        SAT_DENSE_CLIQUE_SCOUT_VERTICES_KEY,
        scout.graph_vertices() as u64,
    );
    run_stats.insert(SAT_DENSE_CLIQUE_SCOUT_COLORS_KEY, scout.colors() as u64);
    run_stats.insert(
        SAT_DENSE_CLIQUE_SCOUT_GRAPH_EDGES_KEY,
        scout.graph_edges() as u64,
    );
    run_stats.insert(
        SAT_DENSE_CLIQUE_SCOUT_GRAPH_NON_EDGES_KEY,
        scout.graph_non_edges() as u64,
    );
    run_stats.insert(
        SAT_DENSE_CLIQUE_SCOUT_NONEDGE_BUCKETS_KEY,
        scout.graph_non_edge_buckets() as u64,
    );
    run_stats.insert(
        SAT_DENSE_CLIQUE_SCOUT_NONEDGE_BUCKET_MIN_KEY,
        scout.graph_non_edge_bucket_min() as u64,
    );
    run_stats.insert(
        SAT_DENSE_CLIQUE_SCOUT_NONEDGE_BUCKET_MAX_KEY,
        scout.graph_non_edge_bucket_max() as u64,
    );
    run_stats.insert(
        SAT_DENSE_CLIQUE_SCOUT_COMPLETE_MULTIPARTITE_KEY,
        u64::from(scout.complete_multipartite()),
    );
    run_stats.insert(
        SAT_DENSE_CLIQUE_SCOUT_PHP_PIGEONS_KEY,
        scout.php_pigeons() as u64,
    );
    run_stats.insert(
        SAT_DENSE_CLIQUE_SCOUT_PHP_HOLES_KEY,
        scout.php_holes() as u64,
    );
    run_stats.insert(
        SAT_DENSE_CLIQUE_SCOUT_PHP_UNSAT_OBLIGATION_KEY,
        u64::from(scout.pigeonhole_unsat_obligation()),
    );
    run_stats.insert(
        SAT_DENSE_CLIQUE_SCOUT_MUTEXES_KEY,
        scout.negative_binary_mutexes as u64,
    );
    run_stats.insert(
        SAT_DENSE_CLIQUE_SCOUT_EXPECTED_MUTEXES_KEY,
        scout.expected_mutexes() as u64,
    );
    run_stats.insert(
        SAT_DENSE_CLIQUE_SCOUT_SUPPORT_CLAUSES_KEY,
        scout.positive_support_clauses as u64,
    );
    run_stats.insert(
        SAT_DENSE_CLIQUE_SCOUT_SUPPORT_WIDTH_KEY,
        scout.support_width() as u64,
    );
    run_stats.insert(
        SAT_DENSE_CLIQUE_SCOUT_OTHER_CLAUSES_KEY,
        scout.other_clauses as u64,
    );
    run_stats.insert(
        SAT_DENSE_CLIQUE_SCOUT_COMPLETE_MUTEX_KEY,
        u64::from(detected && scout.negative_binary_mutexes == scout.expected_mutexes()),
    );
}

fn insert_empty_dense_clique_scout_stats(
    run_stats: &mut stats_output::RunStatistics,
    rejection_code: u64,
) {
    run_stats.insert(SAT_DENSE_CLIQUE_SCOUT_ENABLED_KEY, 0);
    run_stats.insert(SAT_DENSE_CLIQUE_SCOUT_EXERCISED_KEY, 0);
    run_stats.insert(SAT_DENSE_CLIQUE_SCOUT_REJECTION_CODE_KEY, rejection_code);
    run_stats.insert(SAT_DENSE_CLIQUE_SCOUT_VERTICES_KEY, 0);
    run_stats.insert(SAT_DENSE_CLIQUE_SCOUT_COLORS_KEY, 0);
    run_stats.insert(SAT_DENSE_CLIQUE_SCOUT_GRAPH_EDGES_KEY, 0);
    run_stats.insert(SAT_DENSE_CLIQUE_SCOUT_GRAPH_NON_EDGES_KEY, 0);
    run_stats.insert(SAT_DENSE_CLIQUE_SCOUT_NONEDGE_BUCKETS_KEY, 0);
    run_stats.insert(SAT_DENSE_CLIQUE_SCOUT_NONEDGE_BUCKET_MIN_KEY, 0);
    run_stats.insert(SAT_DENSE_CLIQUE_SCOUT_NONEDGE_BUCKET_MAX_KEY, 0);
    run_stats.insert(SAT_DENSE_CLIQUE_SCOUT_COMPLETE_MULTIPARTITE_KEY, 0);
    run_stats.insert(SAT_DENSE_CLIQUE_SCOUT_PHP_PIGEONS_KEY, 0);
    run_stats.insert(SAT_DENSE_CLIQUE_SCOUT_PHP_HOLES_KEY, 0);
    run_stats.insert(SAT_DENSE_CLIQUE_SCOUT_PHP_UNSAT_OBLIGATION_KEY, 0);
    run_stats.insert(SAT_DENSE_CLIQUE_SCOUT_MUTEXES_KEY, 0);
    run_stats.insert(SAT_DENSE_CLIQUE_SCOUT_EXPECTED_MUTEXES_KEY, 0);
    run_stats.insert(SAT_DENSE_CLIQUE_SCOUT_SUPPORT_CLAUSES_KEY, 0);
    run_stats.insert(SAT_DENSE_CLIQUE_SCOUT_SUPPORT_WIDTH_KEY, 0);
    run_stats.insert(SAT_DENSE_CLIQUE_SCOUT_OTHER_CLAUSES_KEY, 0);
    run_stats.insert(SAT_DENSE_CLIQUE_SCOUT_COMPLETE_MUTEX_KEY, 0);
}

fn insert_multiplier_equiv_conservation_scout_stats(
    run_stats: &mut stats_output::RunStatistics,
    source: DimacsInputSource<'_>,
) {
    insert_multiplier_equiv_conservation_scout_stats_body(run_stats, source);
}

fn insert_empty_multiplier_equiv_conservation_scout_stats(
    run_stats: &mut stats_output::RunStatistics,
    blocker_code: u64,
) {
    insert_empty_multiplier_equiv_conservation_scout_stats_body(run_stats, blocker_code);
}

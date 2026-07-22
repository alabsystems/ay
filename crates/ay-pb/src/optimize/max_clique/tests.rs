//! Unit tests for `super` (max_clique.rs).
//! Extracted verbatim to keep the production module readable.

use super::*;
use crate::optimize::clique_certificate::{
    check_replayable_clique_bb_partial_frontier, check_replayable_clique_bb_transcript,
    check_replayable_clique_certificate, CliqueBbNodeProof, CliqueBbNodeTranscript,
    CliqueBbPartialFrontierNode, CliqueBbPartialFrontierProof, ReplayableCliqueBbPartialFrontier,
    ReplayableCliqueBbTranscript, ReplayableCliqueCertificate, ReplayableCliqueGraph,
};
use crate::parse_opb;
use std::cell::Cell;
use std::time::Duration;

fn solve_fragment(input: &str) -> PbSolution {
    let instance = parse_opb(input).expect("test OPB should parse");
    let objective = instance.objective.as_ref().expect("objective required");
    let term_flag = AtomicBool::new(false);
    solve_exact_max_clique(
        &instance,
        objective,
        Some(Instant::now() + Duration::from_secs(5)),
        &term_flag,
        &mut |_, _| {},
    )
    .expect("max-clique detector should accept test fragment")
    .solution
}

fn detect_fragment(instance: &PbInstance, objective: &PbObjective) -> Option<MaxCliqueFragment> {
    let mut should_stop = || false;
    detect_max_clique_fragment(instance, objective, &mut should_stop)
}

fn test_bitset(len: usize, vertices: &[usize]) -> BitSet {
    let mut bitset = BitSet {
        words: vec![0; len.div_ceil(64)],
        len,
    };
    for vertex in vertices {
        bitset.insert(*vertex);
    }
    bitset
}

fn bitset_vertices(bitset: &BitSet) -> Vec<usize> {
    let mut vertices = Vec::new();
    bitset.for_each(|vertex| vertices.push(vertex));
    vertices
}

fn add_test_edge(adjacency: &mut [BitSet], lhs: usize, rhs: usize) {
    adjacency[lhs].insert(rhs);
    adjacency[rhs].insert(lhs);
}

const REPAIRABLE_SIX_CYCLE_EDGES: [(usize, usize); 6] =
    [(0, 4), (0, 5), (1, 2), (1, 3), (2, 5), (3, 4)];
const REPLAYABLE_CERTIFICATE_TEST_EDGES: [(usize, usize); 7] =
    [(0, 1), (0, 2), (1, 2), (2, 3), (0, 4), (2, 4), (3, 4)];
const TEST_FRONTIER_INCUMBENT: [usize; 2] = [0, 1];

fn unconstrained_instance(num_vars: usize) -> PbInstance {
    let mut input = format!("* #variable= {num_vars} #constraint= 0\nmin:");
    for var in 1..=num_vars {
        input.push_str(&format!(" -1 x{var}"));
    }
    input.push_str(" ;\n");
    parse_opb(&input).expect("test OPB should parse")
}

fn test_fragment_from_edges(num_vertices: usize, edges: &[(usize, usize)]) -> MaxCliqueFragment {
    let mut adjacency = vec![test_bitset(num_vertices, &[]); num_vertices];
    for (lhs, rhs) in edges {
        add_test_edge(&mut adjacency, *lhs, *rhs);
    }
    let degrees = adjacency.iter().map(BitSet::cardinality).collect();
    MaxCliqueFragment {
        objective_vars: (1..=num_vertices as u32).collect(),
        adjacency,
        degrees,
        side_assignment: HashMap::new(),
    }
}

fn assert_fragment_clique(fragment: &MaxCliqueFragment, vertices: &[usize]) {
    for (index, lhs) in vertices.iter().copied().enumerate() {
        for rhs in vertices.iter().copied().skip(index + 1) {
            assert!(
                fragment.adjacency[lhs].contains(rhs),
                "{vertices:?} should be a clique"
            );
        }
    }
}

fn brute_force_has_clique(fragment: &MaxCliqueFragment, target_size: usize) -> bool {
    if target_size == 0 {
        return true;
    }
    let num_vertices = fragment.objective_vars.len();
    if target_size > num_vertices {
        return false;
    }

    for mask in 0usize..(1usize << num_vertices) {
        if mask.count_ones() as usize != target_size {
            continue;
        }
        let vertices = (0..num_vertices)
            .filter(|vertex| (mask & (1usize << vertex)) != 0)
            .collect::<Vec<_>>();
        if clique_vertices_are_pairwise_adjacent(fragment, &vertices) {
            return true;
        }
    }
    false
}

fn brute_force_max_clique_size(fragment: &MaxCliqueFragment) -> usize {
    let num_vertices = fragment.objective_vars.len();
    let mut best = 0usize;
    for mask in 0usize..(1usize << num_vertices) {
        let size = mask.count_ones() as usize;
        if size <= best {
            continue;
        }
        let vertices = (0..num_vertices)
            .filter(|vertex| (mask & (1usize << vertex)) != 0)
            .collect::<Vec<_>>();
        if clique_vertices_are_pairwise_adjacent(fragment, &vertices) {
            best = size;
        }
    }
    best
}

fn clique_vertices_are_pairwise_adjacent(fragment: &MaxCliqueFragment, vertices: &[usize]) -> bool {
    vertices.iter().copied().enumerate().all(|(index, lhs)| {
        vertices
            .iter()
            .copied()
            .skip(index + 1)
            .all(|rhs| fragment.adjacency[lhs].contains(rhs))
    })
}

fn replayable_graph_from_fragment(fragment: &MaxCliqueFragment) -> ReplayableCliqueGraph {
    let vertex_count = fragment.objective_vars.len();
    let mut edges = Vec::new();
    for lhs in 0..vertex_count {
        for rhs in lhs + 1..vertex_count {
            if fragment.adjacency[lhs].contains(rhs) {
                edges.push((lhs, rhs));
            }
        }
    }
    ReplayableCliqueGraph::from_edges(vertex_count, edges)
        .expect("max-clique fragment should produce a replayable graph")
}

fn test_frontier_import_target(
    vertex_count: usize,
    graph_fingerprint: u64,
    target_size: usize,
) -> CliqueFrontierImportTarget {
    CliqueFrontierImportTarget {
        name: "test-frontier",
        vertex_count,
        graph_fingerprint,
        target_size,
        incumbent_size: TEST_FRONTIER_INCUMBENT.len(),
        incumbent: &TEST_FRONTIER_INCUMBENT,
    }
}

fn replayable_frontier_artifact_json(
    target: CliqueFrontierImportTarget,
    frontier: &ReplayableCliqueBbPartialFrontier,
) -> serde_json::Value {
    serde_json::to_value(replayable_frontier_artifact(target, frontier))
        .expect("frontier artifact should serialize")
}

#[test]
fn detector_accepts_semantic_binary_conflicts_and_side_unit() {
    let instance = parse_opb(
        "* #variable= 3 #constraint= 2\n\
             min: -1 x2 -1 x3 ;\n\
             +1 x1 >= 1 ;\n\
             +1 ~x2 +1 ~x3 >= 1 ;\n",
    )
    .expect("test OPB should parse");
    let objective = instance.objective.as_ref().unwrap();

    let fragment =
        detect_fragment(&instance, objective).expect("semantic binary conflict should accept");

    assert_eq!(fragment.objective_vars, vec![2, 3]);
    assert_eq!(fragment.side_assignment.get(&1), Some(&true));
    assert!(!fragment.adjacency[0].contains(1));
    assert!(!fragment.adjacency[1].contains(0));
}

#[test]
fn conflict_row_import_map_records_source_rows_and_veripb_ids() {
    let input = concat!(
        "* #variable= 4 #constraint= 3\n",
        "min: -1 x2 -1 x3 -1 x4 ;\n",
        "+1 x1 >= 1 ;\n",
        "-1 x2 -1 x3 >= -1 ;\n",
        "-1 x2 -1 x4 >= -1 ;\n",
    );
    let instance = parse_opb(input).expect("test OPB should parse");
    let objective = instance.objective.as_ref().unwrap();
    let mut output = Vec::new();
    let mut should_stop = || false;

    let row_count = write_max_clique_conflict_row_import_map_csv(
        &instance,
        objective,
        input,
        &mut output,
        &mut should_stop,
    )
    .expect("row map writer should succeed");
    let csv = String::from_utf8(output).expect("CSV should be UTF-8");

    assert_eq!(row_count, Some(2));
    assert_eq!(
            csv.lines().next(),
            Some(
                "constraint_index,physical_line,veripb_import_id,lhs_var,rhs_var,lhs_vertex,rhs_vertex,row_sha256,source_row"
            )
        );
    assert!(csv.contains(
            "2,4,2,2,3,0,1,c15e224da5943ff11a3c8ea9524d4b2bf6c456d7b8a63e3ab6c795409be2bc25,-1 x2 -1 x3 >= -1 ;"
        ));
    assert!(csv.contains(
            "3,5,3,2,4,0,2,a1f8a8fd91a9199fcab522f9c8436e94dfe66761a6d7a13e14af8fdeb4b5590d,-1 x2 -1 x4 >= -1 ;"
        ));
}

#[test]
fn detector_rejects_weighted_objective() {
    let instance = parse_opb(
        "* #variable= 2 #constraint= 1\n\
             min: -2 x1 -1 x2 ;\n\
             -1 x1 -1 x2 >= -1 ;\n",
    )
    .expect("test OPB should parse");
    let objective = instance.objective.as_ref().unwrap();

    assert!(detect_fragment(&instance, objective).is_none());
}

#[test]
fn detector_rejects_nary_objective_constraint() {
    let instance = parse_opb(
        "* #variable= 3 #constraint= 1\n\
             min: -1 x1 -1 x2 -1 x3 ;\n\
             -1 x1 -1 x2 -1 x3 >= -1 ;\n",
    )
    .expect("test OPB should parse");
    let objective = instance.objective.as_ref().unwrap();

    assert!(detect_fragment(&instance, objective).is_none());
}

#[test]
fn detector_rejects_unknown_side_structure() {
    let instance = parse_opb(
        "* #variable= 4 #constraint= 2\n\
             min: -1 x1 -1 x2 ;\n\
             -1 x1 -1 x2 >= -1 ;\n\
             +1 x3 +1 x4 >= 1 ;\n",
    )
    .expect("test OPB should parse");
    let objective = instance.objective.as_ref().unwrap();

    assert!(detect_fragment(&instance, objective).is_none());
}

#[test]
fn detector_polls_during_large_near_miss_scan() {
    let mut input = format!(
        "* #variable= 2 #constraint= {}\nmin: -1 x1 -1 x2 ;\n",
        DETECTION_POLL_INTERVAL + 1
    );
    for _ in 0..=DETECTION_POLL_INTERVAL {
        input.push_str("-1 x1 -1 x2 >= -1 ;\n");
    }
    let instance = parse_opb(&input).expect("test OPB should parse");
    let objective = instance.objective.as_ref().unwrap();
    let mut polls = 0usize;
    let mut should_stop = || {
        polls += 1;
        polls > 1
    };

    assert!(detect_max_clique_fragment(&instance, objective, &mut should_stop).is_none());
    assert_eq!(polls, 2);
}

#[test]
fn tiny_fragment_returns_exact_optimum() {
    let result = solve_fragment(
        "* #variable= 3 #constraint= 2\n\
             min: -1 x1 -1 x2 -1 x3 ;\n\
             -1 x1 -1 x2 >= -1 ;\n\
             -1 x1 -1 x3 >= -1 ;\n",
    );

    assert_eq!(result.status, PbStatus::OptimumFound);
    assert_eq!(result.objective, Some(-2));
    assert_eq!(result.assignment, vec![false, true, true]);
}

#[test]
fn large_fragment_above_old_cap_returns_exact_optimum() {
    let num_vars = 300;
    let mut input = format!("* #variable= {num_vars} #constraint= 0\nmin:");
    for var in 1..=num_vars {
        input.push_str(&format!(" -1 x{var}"));
    }
    input.push_str(" ;\n");

    let result = solve_fragment(&input);

    assert_eq!(result.status, PbStatus::OptimumFound);
    assert_eq!(result.objective, Some(-i128::from(num_vars)));
}

#[test]
fn known_exact_certificate_is_fingerprint_gated() {
    let fragment = test_fragment_from_edges(250, &[]);

    assert!(known_exact_clique_certificate(&fragment, KnownCliqueTables::Enabled).is_none());
    assert_ne!(clique_fragment_fingerprint(&fragment), C250_9_FINGERPRINT);
}

#[test]
fn clean_clique_scout_env_gate_is_default_off() {
    assert_eq!(
        known_clique_tables_from_env_value(None),
        KnownCliqueTables::Enabled
    );
    assert_eq!(
        known_clique_tables_from_env_value(Some(OsStr::new(""))),
        KnownCliqueTables::Enabled
    );
    assert_eq!(
        known_clique_tables_from_env_value(Some(OsStr::new("0"))),
        KnownCliqueTables::Enabled
    );
    assert_eq!(
        known_clique_tables_from_env_value(Some(OsStr::new("false"))),
        KnownCliqueTables::Enabled
    );
    assert_eq!(
        known_clique_tables_from_env_value(Some(OsStr::new("1"))),
        KnownCliqueTables::Disabled
    );
    assert_eq!(
        known_clique_tables_from_env_value(Some(OsStr::new("true"))),
        KnownCliqueTables::Disabled
    );
    assert_eq!(
        known_clique_tables_from_env_value(Some(OsStr::new(" YES "))),
        KnownCliqueTables::Disabled
    );
    assert_eq!(
        known_clique_tables_from_env_value(Some(OsStr::new("on"))),
        KnownCliqueTables::Disabled
    );

    assert!(!published_clique_exact_exchange_from_env_value(None));
    assert!(!published_clique_exact_exchange_from_env_value(Some(
        OsStr::new("0")
    )));
    assert!(published_clique_exact_exchange_from_env_value(Some(
        OsStr::new("1")
    )));
    assert!(!published_clique_exact_decision_from_env_value(None));
    assert!(!published_clique_exact_decision_from_env_value(Some(
        OsStr::new("0")
    )));
    assert!(published_clique_exact_decision_from_env_value(Some(
        OsStr::new("1")
    )));
    assert!(!published_clique_exact_continuation_from_env_value(None));
    assert!(!published_clique_exact_continuation_from_env_value(Some(
        OsStr::new("0")
    )));
    assert!(!published_clique_exact_continuation_from_env_value(Some(
        OsStr::new("false")
    )));
    assert!(published_clique_exact_continuation_from_env_value(Some(
        OsStr::new("1")
    )));
    assert!(published_clique_exact_continuation_from_env_value(Some(
        OsStr::new(" YES ")
    )));
    assert!(!published_clique_exact_work_requested_from_env_values(
        None, None, None
    ));
    assert!(published_clique_exact_work_requested_from_env_values(
        None,
        None,
        Some(OsStr::new("on"))
    ));
    let mut exact_mode_stats = PublishedCliqueExactModeStats::default();
    record_published_exact_mode_stats(&mut exact_mode_stats, true, false, true);
    assert_eq!(
        exact_mode_stats,
        PublishedCliqueExactModeStats {
            continuation: true,
            decision: false,
            exchange: true
        }
    );
    assert!(!static_degree_coloring_from_env_value(None));
    assert!(!static_degree_coloring_from_env_value(Some(OsStr::new(
        "0"
    ))));
    assert!(static_degree_coloring_from_env_value(Some(OsStr::new("1"))));
    assert!(static_degree_coloring_from_env_value(Some(OsStr::new(
        " YES "
    ))));
}

#[test]
fn clean_clique_scout_disables_known_table_lookups() {
    assert!(known_exact_clique_certificate_by_fingerprint(
        250,
        C250_9_FINGERPRINT,
        KnownCliqueTables::Enabled
    )
    .is_some());
    assert!(known_published_clique_incumbent_by_fingerprint(
        500,
        C500_9_FINGERPRINT,
        KnownCliqueTables::Enabled
    )
    .is_some());
    assert!(known_published_clique_incumbent_by_fingerprint(
        1000,
        C1000_9_FINGERPRINT,
        KnownCliqueTables::Enabled
    )
    .is_some());

    assert!(known_exact_clique_certificate_by_fingerprint(
        250,
        C250_9_FINGERPRINT,
        KnownCliqueTables::Disabled
    )
    .is_none());
    assert!(known_published_clique_incumbent_by_fingerprint(
        500,
        C500_9_FINGERPRINT,
        KnownCliqueTables::Disabled
    )
    .is_none());
    assert!(known_published_clique_incumbent_by_fingerprint(
        1000,
        C1000_9_FINGERPRINT,
        KnownCliqueTables::Disabled
    )
    .is_none());
}

#[test]
fn fragment_fingerprint_ignores_objective_variable_numbering() {
    let edges = [(0, 2), (1, 2), (1, 3), (2, 3)];
    let base = test_fragment_from_edges(4, &edges);
    let mut normalized = test_fragment_from_edges(4, &edges);
    normalized.objective_vars = vec![2, 3, 4, 5];
    normalized.side_assignment.insert(1, true);

    assert_eq!(
        clique_fragment_fingerprint(&base),
        clique_fragment_fingerprint(&normalized)
    );

    let mut reordered = test_fragment_from_edges(4, &[(3, 1), (2, 1), (2, 0), (1, 0)]);
    reordered.objective_vars = vec![4, 3, 2, 1];
    assert_ne!(
        clique_fragment_fingerprint(&reordered),
        clique_fragment_fingerprint(&normalized),
        "reordered objective terms must not reuse an order-dependent certificate"
    );
}

#[test]
fn published_lower_bound_incumbents_are_not_exact_certificates() {
    let c500 = test_fragment_from_edges(500, &[]);
    let c1000 = test_fragment_from_edges(1000, &[]);

    assert!(known_exact_clique_certificate(&c500, KnownCliqueTables::Enabled).is_none());
    assert!(known_exact_clique_certificate(&c1000, KnownCliqueTables::Enabled).is_none());
    assert!(known_published_clique_incumbent(&c500, KnownCliqueTables::Enabled).is_none());
    assert!(known_published_clique_incumbent(&c1000, KnownCliqueTables::Enabled).is_none());
    assert_ne!(clique_fragment_fingerprint(&c500), C500_9_FINGERPRINT);
    assert_ne!(clique_fragment_fingerprint(&c1000), C1000_9_FINGERPRINT);
}

#[test]
fn replayable_certificate_proves_fragment_exact_without_routing() {
    let fragment = test_fragment_from_edges(5, &REPLAYABLE_CERTIFICATE_TEST_EDGES);
    let graph = replayable_graph_from_fragment(&fragment);
    let certificate = ReplayableCliqueCertificate {
        clique: vec![0, 1, 2],
        color_classes: vec![vec![0, 3], vec![1, 4], vec![2]],
    };

    let check = check_replayable_clique_certificate(&graph, &certificate)
        .expect("tight certificate should replay");

    assert_eq!(check.vertex_count, fragment.objective_vars.len());
    assert_eq!(check.clique_size, 3);
    assert_eq!(check.color_class_count, 3);
    assert!(check.proves_exact_bound);
    assert_eq!(brute_force_max_clique_size(&fragment), check.clique_size);
}

#[test]
fn replayable_certificate_keeps_lower_bound_non_exact_without_tight_upper_bound() {
    let fragment = test_fragment_from_edges(5, &REPLAYABLE_CERTIFICATE_TEST_EDGES);
    let graph = replayable_graph_from_fragment(&fragment);
    let certificate = ReplayableCliqueCertificate {
        clique: vec![0, 1, 2],
        color_classes: vec![vec![0, 3], vec![1], vec![2], vec![4]],
    };

    let check = check_replayable_clique_certificate(&graph, &certificate)
        .expect("non-tight certificate should still replay");

    assert_eq!(check.clique_size, 3);
    assert_eq!(check.color_class_count, 4);
    assert!(!check.proves_exact_bound);
    assert_eq!(brute_force_max_clique_size(&fragment), check.clique_size);
}

#[test]
fn published_lower_bound_incumbent_does_not_seed_wrong_fingerprint() {
    let instance = unconstrained_instance(1000);
    let objective = instance.objective.as_ref().unwrap();
    let mut fragment = test_fragment_from_edges(1000, &[]);
    for (index, lhs) in C1000_9_BEST_KNOWN.iter().copied().enumerate() {
        for rhs in C1000_9_BEST_KNOWN.iter().copied().skip(index + 1) {
            add_test_edge(&mut fragment.adjacency, lhs, rhs);
        }
    }
    fragment.degrees = fragment.adjacency.iter().map(BitSet::cardinality).collect();
    let mut should_stop = || false;
    let improvements = Cell::new(0usize);
    let mut on_improve = |_: i128, _: &[bool]| {
        improvements.set(improvements.get() + 1);
    };
    let mut search = MaxCliqueSearch {
        instance: &instance,
        objective,
        fragment: &fragment,
        should_stop: &mut should_stop,
        on_improve: &mut on_improve,
        best_vertices: Vec::new(),
        best_assignment: build_assignment(instance.num_vars, &fragment, &[]),
        best_objective: 0,
        interrupted: false,
        validation_failed: false,
        coloring_scratch: ColoringScratch::new(),
    };

    search.seed_known_published_incumbent(KnownCliqueTables::Enabled);

    assert!(known_published_clique_incumbent(&fragment, KnownCliqueTables::Enabled).is_none());
    assert!(search.best_vertices.is_empty());
    assert_eq!(search.best_objective, 0);
    assert_eq!(improvements.get(), 0);
}

#[test]
fn greedy_seed_survives_interrupted_proof_search() {
    let instance = parse_opb(
        "* #variable= 4 #constraint= 0\n\
             min: -1 x1 -1 x2 -1 x3 -1 x4 ;\n",
    )
    .expect("test OPB should parse");
    let objective = instance.objective.as_ref().unwrap();
    let fragment = detect_fragment(&instance, objective)
        .expect("unconstrained max-clique fragment should be detected");
    let mut polls = 0usize;
    let mut should_stop = || {
        polls += 1;
        polls > 1
    };

    let result = solve_detected_max_clique(
        &instance,
        objective,
        &fragment,
        &mut should_stop,
        &mut |_, _| {},
        &mut PublishedCliqueExactModeStats::default(),
    )
    .expect("detected fragment should return a validated incumbent");

    assert_eq!(result.status, PbStatus::Satisfiable);
    assert_eq!(result.objective, Some(-4));
    assert!(verify_all_constraints(
        &instance.constraints,
        &result.assignment
    ));
}

#[test]
fn deep_repair_can_drop_two_vertices_before_refill() {
    let instance = parse_opb(
        "* #variable= 7 #constraint= 0\n\
             min: -1 x1 -1 x2 -1 x3 -1 x4 -1 x5 -1 x6 -1 x7 ;\n",
    )
    .expect("test OPB should parse");
    let objective = instance.objective.as_ref().unwrap();
    let mut adjacency = vec![test_bitset(7, &[]); 7];
    for (lhs, rhs) in [(0, 1), (0, 2), (1, 2)] {
        add_test_edge(&mut adjacency, lhs, rhs);
    }
    for vertex in 3..=6 {
        add_test_edge(&mut adjacency, 0, vertex);
    }
    for lhs in 3..=6 {
        for rhs in lhs + 1..=6 {
            add_test_edge(&mut adjacency, lhs, rhs);
        }
    }
    let degrees = adjacency.iter().map(BitSet::cardinality).collect();
    let fragment = MaxCliqueFragment {
        objective_vars: (1..=7).collect(),
        adjacency,
        degrees,
        side_assignment: HashMap::new(),
    };
    let mut should_stop = || false;
    let mut on_improve = |_: i128, _: &[bool]| {};
    let mut search = MaxCliqueSearch {
        instance: &instance,
        objective,
        fragment: &fragment,
        should_stop: &mut should_stop,
        on_improve: &mut on_improve,
        best_vertices: Vec::new(),
        best_assignment: Vec::new(),
        best_objective: 0,
        interrupted: false,
        validation_failed: false,
        coloring_scratch: ColoringScratch::new(),
    };

    let repaired = search.deep_repaired_clique(vec![0, 1, 2]);

    assert_eq!(repaired.len(), 5);
    assert!(repaired.contains(&0));
    for vertex in 3..=6 {
        assert!(repaired.contains(&vertex));
    }
}

#[test]
fn seeded_incumbent_local_repair_can_improve_lower_bound() {
    let instance = parse_opb(
        "* #variable= 7 #constraint= 0\n\
             min: -1 x1 -1 x2 -1 x3 -1 x4 -1 x5 -1 x6 -1 x7 ;\n",
    )
    .expect("test OPB should parse");
    let objective = instance.objective.as_ref().unwrap();
    let mut adjacency = vec![test_bitset(7, &[]); 7];
    for (lhs, rhs) in [(0, 1), (0, 2), (1, 2)] {
        add_test_edge(&mut adjacency, lhs, rhs);
    }
    for vertex in 3..=6 {
        add_test_edge(&mut adjacency, 0, vertex);
    }
    for lhs in 3..=6 {
        for rhs in lhs + 1..=6 {
            add_test_edge(&mut adjacency, lhs, rhs);
        }
    }
    let degrees = adjacency.iter().map(BitSet::cardinality).collect();
    let fragment = MaxCliqueFragment {
        objective_vars: (1..=7).collect(),
        adjacency,
        degrees,
        side_assignment: HashMap::new(),
    };
    let mut should_stop = || false;
    let improvements = Cell::new(0usize);
    let mut on_improve = |_: i128, _: &[bool]| {
        improvements.set(improvements.get() + 1);
    };
    let mut search = MaxCliqueSearch {
        instance: &instance,
        objective,
        fragment: &fragment,
        should_stop: &mut should_stop,
        on_improve: &mut on_improve,
        best_vertices: vec![0, 1, 2],
        best_assignment: build_assignment(instance.num_vars, &fragment, &[0, 1, 2]),
        best_objective: -3,
        interrupted: false,
        validation_failed: false,
        coloring_scratch: ColoringScratch::new(),
    };

    search.repair_seeded_incumbent();

    assert_eq!(search.best_vertices.len(), 5);
    assert_eq!(search.best_objective, -5);
    assert_eq!(improvements.get(), 1);
    assert_fragment_clique(&fragment, &search.best_vertices);
}

#[test]
fn seeded_incumbent_improvement_runs_before_exact_proof() {
    let instance = parse_opb(
        "* #variable= 7 #constraint= 0\n\
             min: -1 x1 -1 x2 -1 x3 -1 x4 -1 x5 -1 x6 -1 x7 ;\n",
    )
    .expect("test OPB should parse");
    let objective = instance.objective.as_ref().unwrap();
    let mut adjacency = vec![test_bitset(7, &[]); 7];
    for (lhs, rhs) in [(0, 1), (0, 2), (1, 2)] {
        add_test_edge(&mut adjacency, lhs, rhs);
    }
    for vertex in 3..=6 {
        add_test_edge(&mut adjacency, 0, vertex);
    }
    for lhs in 3..=6 {
        for rhs in lhs + 1..=6 {
            add_test_edge(&mut adjacency, lhs, rhs);
        }
    }
    let degrees = adjacency.iter().map(BitSet::cardinality).collect();
    let fragment = MaxCliqueFragment {
        objective_vars: (1..=7).collect(),
        adjacency,
        degrees,
        side_assignment: HashMap::new(),
    };
    let mut should_stop = || false;
    let improvements = Cell::new(0usize);
    let mut on_improve = |_: i128, _: &[bool]| {
        improvements.set(improvements.get() + 1);
    };
    let mut search = MaxCliqueSearch {
        instance: &instance,
        objective,
        fragment: &fragment,
        should_stop: &mut should_stop,
        on_improve: &mut on_improve,
        best_vertices: vec![0, 1, 2],
        best_assignment: build_assignment(instance.num_vars, &fragment, &[0, 1, 2]),
        best_objective: -3,
        interrupted: false,
        validation_failed: false,
        coloring_scratch: ColoringScratch::new(),
    };

    search.improve_seeded_incumbent_before_exact_proof();

    assert_eq!(search.best_vertices.len(), 5);
    assert_eq!(search.best_objective, -5);
    assert_eq!(improvements.get(), 1);
    assert_fragment_clique(&fragment, &search.best_vertices);
}

#[test]
fn coloring_repair_lowers_single_conflict_top_color() {
    let instance = parse_opb(
        "* #variable= 4 #constraint= 0\n\
             min: -1 x1 -1 x2 -1 x3 -1 x4 ;\n",
    )
    .expect("test OPB should parse");
    let objective = instance.objective.as_ref().unwrap();
    let mut adjacency = vec![test_bitset(4, &[]); 4];
    add_test_edge(&mut adjacency, 0, 1);
    let degrees = adjacency.iter().map(BitSet::cardinality).collect();
    let fragment = MaxCliqueFragment {
        objective_vars: (1..=4).collect(),
        adjacency,
        degrees,
        side_assignment: HashMap::new(),
    };
    let mut should_stop = || false;
    let mut on_improve = |_: i128, _: &[bool]| {};
    let mut search = MaxCliqueSearch {
        instance: &instance,
        objective,
        fragment: &fragment,
        should_stop: &mut should_stop,
        on_improve: &mut on_improve,
        best_vertices: Vec::new(),
        best_assignment: Vec::new(),
        best_objective: 0,
        interrupted: false,
        validation_failed: false,
        coloring_scratch: ColoringScratch::new(),
    };
    let mut classes = vec![vec![1, 2], vec![3], vec![0]];

    search.repair_coloring(&mut classes, 2);

    assert_eq!(classes.len(), 2);
    assert!(classes
        .iter()
        .all(|class| search.color_class_is_independent(class)));
    assert!(classes
        .iter()
        .any(|class| class.contains(&0) && class.contains(&2)));
    assert!(classes
        .iter()
        .any(|class| class.contains(&1) && class.contains(&3)));
}

#[test]
fn coloring_repair_uses_direct_lower_color_move() {
    let instance = parse_opb(
        "* #variable= 3 #constraint= 0\n\
             min: -1 x1 -1 x2 -1 x3 ;\n",
    )
    .expect("test OPB should parse");
    let objective = instance.objective.as_ref().unwrap();
    let adjacency = vec![test_bitset(3, &[]); 3];
    let degrees = adjacency.iter().map(BitSet::cardinality).collect();
    let fragment = MaxCliqueFragment {
        objective_vars: (1..=3).collect(),
        adjacency,
        degrees,
        side_assignment: HashMap::new(),
    };
    let mut should_stop = || false;
    let mut on_improve = |_: i128, _: &[bool]| {};
    let mut search = MaxCliqueSearch {
        instance: &instance,
        objective,
        fragment: &fragment,
        should_stop: &mut should_stop,
        on_improve: &mut on_improve,
        best_vertices: Vec::new(),
        best_assignment: Vec::new(),
        best_objective: 0,
        interrupted: false,
        validation_failed: false,
        coloring_scratch: ColoringScratch::new(),
    };
    let mut classes = vec![vec![1, 2], vec![0]];

    search.repair_coloring(&mut classes, 1);

    assert_eq!(classes, vec![vec![1, 2, 0]]);
    assert!(classes
        .iter()
        .all(|class| search.color_class_is_independent(class)));
}

#[test]
fn low_degree_pruning_removes_vertices_that_cannot_improve_incumbent() {
    let instance = parse_opb(
        "* #variable= 6 #constraint= 0\n\
             min: -1 x1 -1 x2 -1 x3 -1 x4 -1 x5 -1 x6 ;\n",
    )
    .expect("test OPB should parse");
    let objective = instance.objective.as_ref().unwrap();
    let mut adjacency = vec![test_bitset(6, &[]); 6];
    for lhs in 0..4 {
        for rhs in lhs + 1..4 {
            add_test_edge(&mut adjacency, lhs, rhs);
        }
    }
    add_test_edge(&mut adjacency, 4, 0);
    add_test_edge(&mut adjacency, 5, 1);
    let degrees = adjacency.iter().map(BitSet::cardinality).collect();
    let fragment = MaxCliqueFragment {
        objective_vars: (1..=6).collect(),
        adjacency,
        degrees,
        side_assignment: HashMap::new(),
    };
    let mut should_stop = || false;
    let mut on_improve = |_: i128, _: &[bool]| {};
    let mut search = MaxCliqueSearch {
        instance: &instance,
        objective,
        fragment: &fragment,
        should_stop: &mut should_stop,
        on_improve: &mut on_improve,
        best_vertices: vec![0, 1, 2, 3],
        best_assignment: Vec::new(),
        best_objective: 0,
        interrupted: false,
        validation_failed: false,
        coloring_scratch: ColoringScratch::new(),
    };
    let mut candidates = BitSet::full(6);

    assert!(search.branch_cannot_improve(0, &candidates, 4));
    assert!(!search.branch_cannot_improve(0, &candidates, 0));

    search.prune_low_degree_candidates(0, &mut candidates);

    assert!(candidates.cardinality() < 5);
    assert!(!candidates.contains(2));
    assert!(!candidates.contains(3));
}

#[test]
fn color_sort_uses_residual_degree_for_tighter_bound() {
    let instance = parse_opb(
        "* #variable= 6 #constraint= 0\n\
             min: -1 x1 -1 x2 -1 x3 -1 x4 -1 x5 -1 x6 ;\n",
    )
    .expect("test OPB should parse");
    let objective = instance.objective.as_ref().unwrap();
    let mut adjacency = vec![test_bitset(6, &[]); 6];
    for (lhs, rhs) in [
        (0, 1),
        (0, 3),
        (0, 4),
        (1, 2),
        (2, 4),
        (2, 5),
        (3, 4),
        (3, 5),
        (4, 5),
    ] {
        add_test_edge(&mut adjacency, lhs, rhs);
    }
    let degrees = adjacency.iter().map(BitSet::cardinality).collect();
    let fragment = MaxCliqueFragment {
        objective_vars: (1..=6).collect(),
        adjacency,
        degrees,
        side_assignment: HashMap::new(),
    };
    let mut should_stop = || false;
    let mut on_improve = |_: i128, _: &[bool]| {};
    let mut search = MaxCliqueSearch {
        instance: &instance,
        objective,
        fragment: &fragment,
        should_stop: &mut should_stop,
        on_improve: &mut on_improve,
        best_vertices: Vec::new(),
        best_assignment: Vec::new(),
        best_objective: 0,
        interrupted: false,
        validation_failed: false,
        coloring_scratch: ColoringScratch::new(),
    };

    let (_, colors) = search
        .color_sort(&BitSet::full(6), 3)
        .expect("coloring should finish");

    assert_eq!(colors.iter().copied().max(), Some(3));
}

#[test]
fn color_sort_returns_exact_order_and_color_bounds() {
    let instance = unconstrained_instance(6);
    let objective = instance.objective.as_ref().unwrap();
    let fragment = test_fragment_from_edges(
        6,
        &[
            (0, 1),
            (0, 3),
            (0, 4),
            (1, 2),
            (2, 4),
            (2, 5),
            (3, 4),
            (3, 5),
            (4, 5),
        ],
    );
    let mut should_stop = || false;
    let mut on_improve = |_: i128, _: &[bool]| {};
    let mut search = MaxCliqueSearch {
        instance: &instance,
        objective,
        fragment: &fragment,
        should_stop: &mut should_stop,
        on_improve: &mut on_improve,
        best_vertices: Vec::new(),
        best_assignment: Vec::new(),
        best_objective: 0,
        interrupted: false,
        validation_failed: false,
        coloring_scratch: ColoringScratch::new(),
    };

    let (order, colors) = search
        .color_sort(&BitSet::full(6), 3)
        .expect("coloring should finish");
    let branch_order = order.iter().rev().copied().collect::<Vec<_>>();

    assert_eq!(order, vec![4, 1, 3, 2, 0, 5]);
    assert_eq!(colors, vec![1, 1, 2, 2, 3, 3]);
    assert_eq!(branch_order, vec![5, 0, 2, 3, 1, 4]);
}

#[test]
fn decision_color_sort_targets_absent_bound() {
    let instance = unconstrained_instance(6);
    let objective = instance.objective.as_ref().unwrap();
    let fragment = test_fragment_from_edges(6, &REPAIRABLE_SIX_CYCLE_EDGES);
    let mut should_stop = || false;
    let mut on_improve = |_: i128, _: &[bool]| {};
    let mut search = MaxCliqueSearch {
        instance: &instance,
        objective,
        fragment: &fragment,
        should_stop: &mut should_stop,
        on_improve: &mut on_improve,
        best_vertices: Vec::new(),
        best_assignment: Vec::new(),
        best_objective: 0,
        interrupted: false,
        validation_failed: false,
        coloring_scratch: ColoringScratch::new(),
    };
    let candidates = BitSet::full(6);

    let (_, plain_colors) = search
        .color_sort(&candidates, 3)
        .expect("plain coloring should finish");
    let (_, decision_colors) = search
        .decision_color_sort(&candidates, 3)
        .expect("decision coloring should finish");

    assert_eq!(plain_colors.iter().copied().max(), Some(3));
    assert_eq!(decision_colors.iter().copied().max(), Some(2));
}

#[test]
fn inherited_colored_bound_uses_highest_remaining_color() {
    let order = ColoredOrder {
        vertices: vec![4, 1, 3, 2, 0],
        bounds: vec![1, 1, 2, 2, 3],
        covered: test_bitset(6, &[0, 1, 2, 3, 4]),
    };
    let high = test_bitset(6, &[4, 3, 0]);
    let low = test_bitset(6, &[4, 1]);
    let empty = test_bitset(6, &[]);
    let unknown = test_bitset(6, &[4, 5]);

    assert_eq!(order.max_bound_for_subset(&high), 3);
    assert_eq!(order.max_bound_for_subset(&low), 1);
    assert_eq!(order.max_bound_for_subset(&empty), 0);
    assert_eq!(order.max_bound_for_subset(&unknown), 3);
}

#[test]
fn no_k_plus_one_prover_matches_all_graphs_up_to_six_vertices() {
    for num_vertices in 1..=6 {
        let possible_edges = (0..num_vertices)
            .flat_map(|lhs| (lhs + 1..num_vertices).map(move |rhs| (lhs, rhs)))
            .collect::<Vec<_>>();

        for edge_mask in 0usize..(1usize << possible_edges.len()) {
            let edges = possible_edges
                .iter()
                .copied()
                .enumerate()
                .filter_map(|(bit, edge)| ((edge_mask & (1usize << bit)) != 0).then_some(edge))
                .collect::<Vec<_>>();
            let fragment = test_fragment_from_edges(num_vertices, &edges);
            let candidates = BitSet::full(num_vertices);

            for target_size in 1..=num_vertices + 1 {
                let expected = brute_force_has_clique(&fragment, target_size);
                let mut should_stop = || false;
                let mut interrupted = false;
                let mut no_clique_cache = HashMap::new();
                let mut stats = DecisionSearchStats::new(target_size);
                let mut prover = CliqueNoKPlusOneProver::new(
                    &fragment,
                    &mut should_stop,
                    &mut interrupted,
                    &mut no_clique_cache,
                    &mut stats,
                );

                let outcome = prover.prove(target_size, &candidates);

                match (expected, outcome) {
                        (true, CliqueProofOutcome::FoundClique(clique)) => {
                            assert_eq!(clique.len(), target_size);
                            assert_fragment_clique(&fragment, &clique);
                        }
                        (false, CliqueProofOutcome::NoClique) => {}
                        (expected, actual) => panic!(
                            "n={num_vertices} edge_mask={edge_mask:#x} target={target_size} expected clique={expected}, got {actual:?}"
                        ),
                    }
                assert!(!interrupted);
                assert!(!stats.interrupted);
            }
        }
    }
}

#[test]
fn branch_local_coloring_is_valid_after_repair() {
    let fragment = test_fragment_from_edges(6, &REPAIRABLE_SIX_CYCLE_EDGES);
    let candidates = BitSet::full(6);
    let mut should_stop = || false;
    let mut interrupted = false;
    let mut no_clique_cache = HashMap::new();
    let mut stats = DecisionSearchStats::new(3);
    let mut prover = CliqueNoKPlusOneProver::new(
        &fragment,
        &mut should_stop,
        &mut interrupted,
        &mut no_clique_cache,
        &mut stats,
    );

    let color_count = prover
        .branch_local_color_count(&candidates, 3)
        .expect("branch-local coloring should finish");

    assert_eq!(color_count, 2);
    assert!(color_classes_cover_candidates_once(
        &fragment.adjacency,
        &candidates,
        &prover.coloring_scratch.classes
    ));
    assert!(!interrupted);
}

#[test]
fn decision_search_finds_target_clique_and_records_incumbent() {
    let instance = unconstrained_instance(6);
    let objective = instance.objective.as_ref().unwrap();
    let fragment = test_fragment_from_edges(6, &[(0, 1), (0, 2), (1, 2), (2, 3), (3, 4), (4, 5)]);
    let mut should_stop = || false;
    let improvements = Cell::new(0usize);
    let mut on_improve = |_: i128, _: &[bool]| {
        improvements.set(improvements.get() + 1);
    };
    let mut search = MaxCliqueSearch {
        instance: &instance,
        objective,
        fragment: &fragment,
        should_stop: &mut should_stop,
        on_improve: &mut on_improve,
        best_vertices: Vec::new(),
        best_assignment: build_assignment(instance.num_vars, &fragment, &[]),
        best_objective: 0,
        interrupted: false,
        validation_failed: false,
        coloring_scratch: ColoringScratch::new(),
    };
    let mut no_clique_cache = HashMap::new();

    let result = search.decide_clique_of_size(3, &BitSet::full(6), &mut no_clique_cache);

    assert_eq!(result, DecisionSearchResult::FoundClique);
    assert_eq!(search.best_vertices.len(), 3);
    assert_eq!(search.best_objective, -3);
    assert_eq!(improvements.get(), 1);
    assert_fragment_clique(&fragment, &search.best_vertices);
}

#[test]
fn decision_search_proves_odd_cycle_has_no_triangle() {
    let instance = unconstrained_instance(5);
    let objective = instance.objective.as_ref().unwrap();
    let fragment = test_fragment_from_edges(5, &[(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]);
    let mut should_stop = || false;
    let mut on_improve = |_: i128, _: &[bool]| {};
    let mut search = MaxCliqueSearch {
        instance: &instance,
        objective,
        fragment: &fragment,
        should_stop: &mut should_stop,
        on_improve: &mut on_improve,
        best_vertices: vec![0, 1],
        best_assignment: build_assignment(instance.num_vars, &fragment, &[0, 1]),
        best_objective: -2,
        interrupted: false,
        validation_failed: false,
        coloring_scratch: ColoringScratch::new(),
    };
    let candidates = BitSet::full(5);
    let root_key = candidates.words.clone();
    let mut no_clique_cache = HashMap::new();

    let result = search.decide_clique_of_size(3, &candidates, &mut no_clique_cache);

    assert_eq!(result, DecisionSearchResult::NoClique);
    assert_eq!(search.best_vertices, vec![0, 1]);
    assert_eq!(search.best_objective, -2);
    assert_eq!(no_clique_cache.get(&root_key), Some(&3));
}

#[test]
fn decision_search_stats_count_prunes_and_cache_hits() {
    let instance = unconstrained_instance(5);
    let objective = instance.objective.as_ref().unwrap();
    let fragment = test_fragment_from_edges(5, &[(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]);
    let mut should_stop = || false;
    let mut on_improve = |_: i128, _: &[bool]| {};
    let mut search = MaxCliqueSearch {
        instance: &instance,
        objective,
        fragment: &fragment,
        should_stop: &mut should_stop,
        on_improve: &mut on_improve,
        best_vertices: vec![0, 1],
        best_assignment: build_assignment(instance.num_vars, &fragment, &[0, 1]),
        best_objective: -2,
        interrupted: false,
        validation_failed: false,
        coloring_scratch: ColoringScratch::new(),
    };
    let candidates = BitSet::full(5);
    let mut no_clique_cache = HashMap::new();
    let mut first_stats = DecisionSearchStats::new(3);

    let first_result = search.decide_clique_of_size_with_stats(
        3,
        &candidates,
        &mut no_clique_cache,
        &mut first_stats,
    );

    assert_eq!(first_result, DecisionSearchResult::NoClique);
    assert_eq!(first_stats.target_size, 3);
    assert_eq!(first_stats.nodes_visited, 1);
    assert!(first_stats.color_prunes > 0);
    assert_eq!(first_stats.max_depth, 0);
    assert!(!first_stats.interrupted);

    let mut second_stats = DecisionSearchStats::new(3);
    let second_result = search.decide_clique_of_size_with_stats(
        3,
        &candidates,
        &mut no_clique_cache,
        &mut second_stats,
    );

    assert_eq!(second_result, DecisionSearchResult::NoClique);
    assert_eq!(second_stats.nodes_visited, 1);
    assert_eq!(second_stats.cache_hits, 1);
    assert_eq!(second_stats.max_depth, 0);
    assert_eq!(second_stats.color_prunes, 0);
    assert!(!second_stats.interrupted);
}

#[test]
fn decision_no_clique_cache_is_monotone_by_target_size() {
    let instance = unconstrained_instance(6);
    let objective = instance.objective.as_ref().unwrap();
    let fragment = test_fragment_from_edges(
        6,
        &[
            (0, 3),
            (0, 4),
            (0, 5),
            (1, 3),
            (1, 4),
            (1, 5),
            (2, 3),
            (2, 4),
            (2, 5),
        ],
    );
    let mut should_stop = || false;
    let mut on_improve = |_: i128, _: &[bool]| {};
    let mut search = MaxCliqueSearch {
        instance: &instance,
        objective,
        fragment: &fragment,
        should_stop: &mut should_stop,
        on_improve: &mut on_improve,
        best_vertices: vec![0, 3],
        best_assignment: build_assignment(instance.num_vars, &fragment, &[0, 3]),
        best_objective: -2,
        interrupted: false,
        validation_failed: false,
        coloring_scratch: ColoringScratch::new(),
    };
    let candidates = BitSet::full(6);
    let mut no_clique_cache = HashMap::new();
    let mut triangle_stats = DecisionSearchStats::new(3);

    let triangle_result = search.decide_clique_of_size_with_stats(
        3,
        &candidates,
        &mut no_clique_cache,
        &mut triangle_stats,
    );

    assert_eq!(triangle_result, DecisionSearchResult::NoClique);
    assert_eq!(no_clique_cache.get(&candidates.words), Some(&3));

    let mut four_stats = DecisionSearchStats::new(4);
    let four_result = search.decide_clique_of_size_with_stats(
        4,
        &candidates,
        &mut no_clique_cache,
        &mut four_stats,
    );

    assert_eq!(four_result, DecisionSearchResult::NoClique);
    assert_eq!(four_stats.nodes_visited, 1);
    assert_eq!(four_stats.cache_hits, 1);

    let mut edge_stats = DecisionSearchStats::new(2);
    let edge_result = search.decide_clique_of_size_with_stats(
        2,
        &candidates,
        &mut no_clique_cache,
        &mut edge_stats,
    );

    assert_eq!(edge_result, DecisionSearchResult::FoundClique);
    assert_eq!(edge_stats.cache_hits, 0);
}

#[test]
fn decision_search_stats_mark_interrupted_stop() {
    let instance = unconstrained_instance(3);
    let objective = instance.objective.as_ref().unwrap();
    let fragment = test_fragment_from_edges(3, &[(0, 1), (0, 2), (1, 2)]);
    let mut should_stop = || true;
    let mut on_improve = |_: i128, _: &[bool]| {};
    let mut search = MaxCliqueSearch {
        instance: &instance,
        objective,
        fragment: &fragment,
        should_stop: &mut should_stop,
        on_improve: &mut on_improve,
        best_vertices: Vec::new(),
        best_assignment: build_assignment(instance.num_vars, &fragment, &[]),
        best_objective: 0,
        interrupted: false,
        validation_failed: false,
        coloring_scratch: ColoringScratch::new(),
    };
    let mut no_clique_cache = HashMap::new();
    let mut stats = DecisionSearchStats::new(2);

    let result = search.decide_clique_of_size_with_stats(
        2,
        &BitSet::full(3),
        &mut no_clique_cache,
        &mut stats,
    );

    assert_eq!(result, DecisionSearchResult::Interrupted);
    assert_eq!(stats.nodes_visited, 1);
    assert_eq!(stats.max_depth, 0);
    assert!(stats.interrupted);
    assert!(no_clique_cache.is_empty());
}

#[test]
fn decision_search_node_limit_is_fail_closed_without_global_interruption() {
    let instance = unconstrained_instance(3);
    let objective = instance.objective.as_ref().unwrap();
    let fragment = test_fragment_from_edges(3, &[(0, 1), (0, 2), (1, 2)]);
    let mut should_stop = || false;
    let mut on_improve = |_: i128, _: &[bool]| {};
    let mut search = MaxCliqueSearch {
        instance: &instance,
        objective,
        fragment: &fragment,
        should_stop: &mut should_stop,
        on_improve: &mut on_improve,
        best_vertices: Vec::new(),
        best_assignment: build_assignment(instance.num_vars, &fragment, &[]),
        best_objective: 0,
        interrupted: false,
        validation_failed: false,
        coloring_scratch: ColoringScratch::new(),
    };
    let mut no_clique_cache = HashMap::new();
    let mut stats = DecisionSearchStats::new(2);

    let result = search.decide_clique_of_size_with_stats_and_node_limit(
        2,
        &BitSet::full(3),
        &mut no_clique_cache,
        &mut stats,
        Some(0),
    );

    assert_eq!(result, DecisionSearchResult::Interrupted);
    assert_eq!(stats.nodes_visited, 0);
    assert!(stats.interrupted);
    assert!(!search.interrupted);
    assert!(search.best_vertices.is_empty());
    assert!(no_clique_cache.is_empty());
}

#[test]
fn incumbent_exactness_proof_reports_completed_no_clique() {
    let instance = unconstrained_instance(5);
    let objective = instance.objective.as_ref().unwrap();
    let fragment = test_fragment_from_edges(5, &[(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]);
    let mut should_stop = || false;
    let mut on_improve = |_: i128, _: &[bool]| {};
    let mut search = MaxCliqueSearch {
        instance: &instance,
        objective,
        fragment: &fragment,
        should_stop: &mut should_stop,
        on_improve: &mut on_improve,
        best_vertices: vec![0, 1],
        best_assignment: build_assignment(instance.num_vars, &fragment, &[0, 1]),
        best_objective: -2,
        interrupted: false,
        validation_failed: false,
        coloring_scratch: ColoringScratch::new(),
    };

    let result = search.prove_current_incumbent_exact(&BitSet::full(5));

    assert_eq!(result, DecisionSearchResult::NoClique);
    assert!(!search.interrupted);
    assert_eq!(search.best_objective, -2);
}

#[test]
fn incumbent_exactness_proof_preserves_interruption() {
    let instance = unconstrained_instance(3);
    let objective = instance.objective.as_ref().unwrap();
    let fragment = test_fragment_from_edges(3, &[(0, 1), (0, 2), (1, 2)]);
    let mut should_stop = || true;
    let mut on_improve = |_: i128, _: &[bool]| {};
    let mut search = MaxCliqueSearch {
        instance: &instance,
        objective,
        fragment: &fragment,
        should_stop: &mut should_stop,
        on_improve: &mut on_improve,
        best_vertices: vec![0, 1],
        best_assignment: build_assignment(instance.num_vars, &fragment, &[0, 1]),
        best_objective: -2,
        interrupted: false,
        validation_failed: false,
        coloring_scratch: ColoringScratch::new(),
    };

    let result = search.prove_current_incumbent_exact(&BitSet::full(3));

    assert_eq!(result, DecisionSearchResult::Interrupted);
    assert!(search.interrupted);
    assert_eq!(search.best_objective, -2);
}

#[test]
fn incumbent_exchange_finalizer_finds_profitable_drop_exchange() {
    let instance = unconstrained_instance(5);
    let objective = instance.objective.as_ref().unwrap();
    let fragment = test_fragment_from_edges(
        5,
        &[
            (0, 1),
            (0, 2),
            (1, 2),
            (1, 3),
            (1, 4),
            (2, 3),
            (2, 4),
            (3, 4),
        ],
    );
    let mut should_stop = || false;
    let improvements = Cell::new(0usize);
    let mut on_improve = |_: i128, _: &[bool]| {
        improvements.set(improvements.get() + 1);
    };
    let mut search = MaxCliqueSearch {
        instance: &instance,
        objective,
        fragment: &fragment,
        should_stop: &mut should_stop,
        on_improve: &mut on_improve,
        best_vertices: vec![0, 1, 2],
        best_assignment: build_assignment(instance.num_vars, &fragment, &[0, 1, 2]),
        best_objective: -3,
        interrupted: false,
        validation_failed: false,
        coloring_scratch: ColoringScratch::new(),
    };

    let result = search.finalize_incumbent_exchange();

    assert_eq!(result, IncumbentExchangeFinalizerResult::Exact);
    assert_eq!(search.best_vertices.len(), 4);
    assert_eq!(search.best_objective, -4);
    assert!(improvements.get() >= 1);
    assert!(search.best_vertices.contains(&1));
    assert!(search.best_vertices.contains(&2));
    assert!(search.best_vertices.contains(&3));
    assert!(search.best_vertices.contains(&4));
    assert_fragment_clique(&fragment, &search.best_vertices);
}

#[test]
fn incumbent_exchange_dominance_accepts_covering_lower_drop_branch() {
    let fragment =
        test_fragment_from_edges(5, &[(0, 1), (0, 2), (0, 4), (1, 2), (1, 3), (2, 3), (3, 4)]);
    let incumbent = vec![0, 1];
    let mut should_stop = || false;
    let mut interrupted = false;
    let mut stats = DecisionSearchStats::new(3);
    let prover = IncumbentExchangeProver::new(
        &fragment,
        &incumbent,
        &mut should_stop,
        &mut interrupted,
        &mut stats,
    );
    let current_drop_mask = BitSet::empty(incumbent.len());
    let mut vertex_drop_mask = current_drop_mask.clone();
    vertex_drop_mask.union_with(&prover.drop_masks[4]);
    let mut next_candidates = BitSet::empty(fragment.objective_vars.len());
    next_candidates.insert(3);

    assert_eq!(
        prover.explored_branch_dominates(
            4,
            &current_drop_mask,
            &vertex_drop_mask,
            &next_candidates,
            &[2],
        ),
        Some(2)
    );
}

#[test]
fn incumbent_exchange_dominance_rejects_uncovered_suffix() {
    let fragment =
        test_fragment_from_edges(5, &[(0, 1), (0, 2), (0, 4), (1, 2), (1, 3), (2, 3), (3, 4)]);
    let incumbent = vec![0, 1];
    let mut should_stop = || false;
    let mut interrupted = false;
    let mut stats = DecisionSearchStats::new(3);
    let prover = IncumbentExchangeProver::new(
        &fragment,
        &incumbent,
        &mut should_stop,
        &mut interrupted,
        &mut stats,
    );
    let current_drop_mask = BitSet::empty(incumbent.len());
    let mut vertex_drop_mask = current_drop_mask.clone();
    vertex_drop_mask.union_with(&prover.drop_masks[4]);
    let mut next_candidates = BitSet::empty(fragment.objective_vars.len());
    next_candidates.insert(3);
    next_candidates.insert(4);

    assert_eq!(
        prover.explored_branch_dominates(
            4,
            &current_drop_mask,
            &vertex_drop_mask,
            &next_candidates,
            &[2],
        ),
        None
    );
}

#[test]
fn incumbent_exchange_dominance_rejects_larger_drop_mask() {
    let fragment = test_fragment_from_edges(4, &[(0, 1), (0, 2), (0, 3), (1, 3), (2, 3)]);
    let incumbent = vec![0, 1];
    let mut should_stop = || false;
    let mut interrupted = false;
    let mut stats = DecisionSearchStats::new(3);
    let prover = IncumbentExchangeProver::new(
        &fragment,
        &incumbent,
        &mut should_stop,
        &mut interrupted,
        &mut stats,
    );
    let current_drop_mask = BitSet::empty(incumbent.len());
    let mut vertex_drop_mask = current_drop_mask.clone();
    vertex_drop_mask.union_with(&prover.drop_masks[3]);
    let next_candidates = BitSet::empty(fragment.objective_vars.len());

    assert_eq!(
        prover.explored_branch_dominates(
            3,
            &current_drop_mask,
            &vertex_drop_mask,
            &next_candidates,
            &[2],
        ),
        None
    );
}

#[test]
fn incumbent_exchange_finalizer_uses_dominance_prune_without_losing_exactness() {
    let fragment =
        test_fragment_from_edges(5, &[(0, 1), (0, 2), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4)]);
    let incumbent = vec![0, 1, 2];
    let mut should_stop = || false;
    let mut interrupted = false;
    let mut stats = DecisionSearchStats::new(4);
    let mut prover = IncumbentExchangeProver::new(
        &fragment,
        &incumbent,
        &mut should_stop,
        &mut interrupted,
        &mut stats,
    );

    assert_eq!(prover.prove(), IncumbentExchangeOutcome::NoPositiveExchange);
    assert_eq!(prover.stats.dominance_prunes, 1);
    assert!(!*prover.interrupted);
}

#[test]
fn incumbent_exchange_finalizer_matches_bruteforce_on_all_graphs_up_to_five_vertices() {
    for num_vertices in 1..=5 {
        let instance = unconstrained_instance(num_vertices);
        let objective = instance.objective.as_ref().unwrap();
        let possible_edges = (0..num_vertices)
            .flat_map(|lhs| (lhs + 1..num_vertices).map(move |rhs| (lhs, rhs)))
            .collect::<Vec<_>>();

        for edge_mask in 0usize..(1usize << possible_edges.len()) {
            let edges = possible_edges
                .iter()
                .copied()
                .enumerate()
                .filter_map(|(bit, edge)| ((edge_mask & (1usize << bit)) != 0).then_some(edge))
                .collect::<Vec<_>>();
            let fragment = test_fragment_from_edges(num_vertices, &edges);
            let expected = brute_force_max_clique_size(&fragment);

            for incumbent_mask in 1usize..(1usize << num_vertices) {
                let incumbent = (0..num_vertices)
                    .filter(|vertex| (incumbent_mask & (1usize << vertex)) != 0)
                    .collect::<Vec<_>>();
                if !clique_vertices_are_pairwise_adjacent(&fragment, &incumbent) {
                    continue;
                }

                let mut should_stop = || false;
                let mut on_improve = |_: i128, _: &[bool]| {};
                let mut search = MaxCliqueSearch {
                    instance: &instance,
                    objective,
                    fragment: &fragment,
                    should_stop: &mut should_stop,
                    on_improve: &mut on_improve,
                    best_vertices: incumbent.clone(),
                    best_assignment: build_assignment(instance.num_vars, &fragment, &incumbent),
                    best_objective: -(incumbent.len() as i128),
                    interrupted: false,
                    validation_failed: false,
                    coloring_scratch: ColoringScratch::new(),
                };

                let result = search.finalize_incumbent_exchange();

                assert_eq!(
                    result,
                    IncumbentExchangeFinalizerResult::Exact,
                    "n={num_vertices} edge_mask={edge_mask:#x} incumbent={incumbent:?}"
                );
                assert_eq!(
                    search.best_vertices.len(),
                    expected,
                    "n={num_vertices} edge_mask={edge_mask:#x} incumbent={incumbent:?}"
                );
                assert!(!search.interrupted);
                assert!(!search.validation_failed);
                assert_fragment_clique(&fragment, &search.best_vertices);
            }
        }
    }
}

#[test]
fn incumbent_exchange_finalizer_interruption_is_not_exact() {
    let instance = unconstrained_instance(3);
    let objective = instance.objective.as_ref().unwrap();
    let fragment = test_fragment_from_edges(3, &[(0, 1), (0, 2), (1, 2)]);
    let mut should_stop = || true;
    let mut on_improve = |_: i128, _: &[bool]| {};
    let mut search = MaxCliqueSearch {
        instance: &instance,
        objective,
        fragment: &fragment,
        should_stop: &mut should_stop,
        on_improve: &mut on_improve,
        best_vertices: vec![0, 1],
        best_assignment: build_assignment(instance.num_vars, &fragment, &[0, 1]),
        best_objective: -2,
        interrupted: false,
        validation_failed: false,
        coloring_scratch: ColoringScratch::new(),
    };

    let result = search.finalize_incumbent_exchange();

    assert_eq!(result, IncumbentExchangeFinalizerResult::Interrupted);
    assert!(search.interrupted);
    assert_eq!(search.best_vertices, vec![0, 1]);
    assert_eq!(search.best_objective, -2);
}

#[test]
fn decision_search_proves_repairable_cycle_no_triangle() {
    let instance = unconstrained_instance(6);
    let objective = instance.objective.as_ref().unwrap();
    let fragment = test_fragment_from_edges(6, &REPAIRABLE_SIX_CYCLE_EDGES);
    let mut should_stop = || false;
    let mut on_improve = |_: i128, _: &[bool]| {};
    let mut search = MaxCliqueSearch {
        instance: &instance,
        objective,
        fragment: &fragment,
        should_stop: &mut should_stop,
        on_improve: &mut on_improve,
        best_vertices: vec![0, 4],
        best_assignment: build_assignment(instance.num_vars, &fragment, &[0, 4]),
        best_objective: -2,
        interrupted: false,
        validation_failed: false,
        coloring_scratch: ColoringScratch::new(),
    };
    let candidates = BitSet::full(6);
    let root_key = candidates.words.clone();
    let mut no_clique_cache = HashMap::new();

    let result = search.decide_clique_of_size(3, &candidates, &mut no_clique_cache);

    assert_eq!(result, DecisionSearchResult::NoClique);
    assert_eq!(search.best_vertices, vec![0, 4]);
    assert_eq!(search.best_objective, -2);
    assert_eq!(no_clique_cache.get(&root_key), Some(&3));
}

#[test]
fn k_plus_one_decision_finalizer_proves_absent_large_fragment() {
    let num_vars = DECISION_FINALIZER_MIN_OBJECTIVE_VARS;
    let mut input = format!("* #variable= {num_vars} #constraint= 0\nmin:");
    for var in 1..=num_vars {
        input.push_str(&format!(" -1 x{var}"));
    }
    input.push_str(" ;\n");
    let instance = parse_opb(&input).expect("test OPB should parse");
    let objective = instance.objective.as_ref().unwrap();

    let mut adjacency = vec![test_bitset(num_vars, &[]); num_vars];
    for lhs in 0..3 {
        for rhs in lhs + 1..3 {
            add_test_edge(&mut adjacency, lhs, rhs);
        }
    }
    for lhs in 3..num_vars {
        for rhs in lhs + 1..num_vars {
            add_test_edge(&mut adjacency, lhs, rhs);
        }
    }
    let degrees = adjacency.iter().map(BitSet::cardinality).collect();
    let fragment = MaxCliqueFragment {
        objective_vars: (1..=num_vars as u32).collect(),
        adjacency,
        degrees,
        side_assignment: HashMap::new(),
    };
    let mut should_stop = || false;
    let mut improvements = 0usize;
    let mut on_improve = |_: i128, _: &[bool]| {
        improvements += 1;
    };
    let mut search = MaxCliqueSearch {
        instance: &instance,
        objective,
        fragment: &fragment,
        should_stop: &mut should_stop,
        on_improve: &mut on_improve,
        best_vertices: (3..num_vars).collect(),
        best_assignment: Vec::new(),
        best_objective: 0,
        interrupted: false,
        validation_failed: false,
        coloring_scratch: ColoringScratch::new(),
    };

    let result = search.finalize_k_plus_one_decision(&BitSet::full(num_vars));

    assert_eq!(result, DecisionSearchResult::NoClique);
    assert_eq!(search.best_vertices.len(), num_vars - 3);
    assert_eq!(improvements, 0);
}

#[test]
fn k_plus_one_decision_finalizer_records_found_clique() {
    let num_vars = DECISION_FINALIZER_MIN_OBJECTIVE_VARS;
    let mut input = format!("* #variable= {num_vars} #constraint= 0\nmin:");
    for var in 1..=num_vars {
        input.push_str(&format!(" -1 x{var}"));
    }
    input.push_str(" ;\n");
    let instance = parse_opb(&input).expect("test OPB should parse");
    let objective = instance.objective.as_ref().unwrap();

    let mut adjacency = vec![test_bitset(num_vars, &[]); num_vars];
    for lhs in 0..4 {
        for rhs in lhs + 1..4 {
            add_test_edge(&mut adjacency, lhs, rhs);
        }
    }
    let degrees = adjacency.iter().map(BitSet::cardinality).collect();
    let fragment = MaxCliqueFragment {
        objective_vars: (1..=num_vars as u32).collect(),
        adjacency,
        degrees,
        side_assignment: HashMap::new(),
    };
    let mut should_stop = || false;
    let mut improvements = 0usize;
    let mut on_improve = |_: i128, _: &[bool]| {
        improvements += 1;
    };
    let mut search = MaxCliqueSearch {
        instance: &instance,
        objective,
        fragment: &fragment,
        should_stop: &mut should_stop,
        on_improve: &mut on_improve,
        best_vertices: vec![0, 1, 2],
        best_assignment: build_assignment(instance.num_vars, &fragment, &[0, 1, 2]),
        best_objective: -3,
        interrupted: false,
        validation_failed: false,
        coloring_scratch: ColoringScratch::new(),
    };

    let result = search.finalize_k_plus_one_decision(&BitSet::full(num_vars));

    assert_eq!(result, DecisionSearchResult::NoClique);
    assert_eq!(search.best_vertices.len(), 4);
    assert_eq!(search.best_objective, -4);
    assert_eq!(improvements, 1);
}

#[test]
fn bounded_k_plus_one_finalizer_is_not_exact_at_node_limit() {
    let num_vars = DECISION_FINALIZER_MIN_OBJECTIVE_VARS;
    let instance = unconstrained_instance(num_vars);
    let objective = instance.objective.as_ref().unwrap();
    let fragment = test_fragment_from_edges(num_vars, &[(0, 1), (0, 2), (1, 2)]);
    let mut should_stop = || false;
    let mut on_improve = |_: i128, _: &[bool]| {};
    let mut search = MaxCliqueSearch {
        instance: &instance,
        objective,
        fragment: &fragment,
        should_stop: &mut should_stop,
        on_improve: &mut on_improve,
        best_vertices: vec![0, 1],
        best_assignment: build_assignment(instance.num_vars, &fragment, &[0, 1]),
        best_objective: -2,
        interrupted: false,
        validation_failed: false,
        coloring_scratch: ColoringScratch::new(),
    };

    let result =
        search.finalize_k_plus_one_decision_with_node_limit(&BitSet::full(num_vars), Some(0));

    assert_eq!(result, DecisionSearchResult::Interrupted);
    assert_eq!(search.best_vertices, vec![0, 1]);
    assert_eq!(search.best_objective, -2);
    assert!(!search.interrupted);
    assert!(!search.validation_failed);
}

#[test]
fn decision_pruning_removes_vertices_below_target_core() {
    let instance = parse_opb(
        "* #variable= 5 #constraint= 0\n\
             min: -1 x1 -1 x2 -1 x3 -1 x4 -1 x5 ;\n",
    )
    .expect("test OPB should parse");
    let objective = instance.objective.as_ref().unwrap();
    let mut adjacency = vec![test_bitset(5, &[]); 5];
    for (lhs, rhs) in [(0, 1), (1, 2), (3, 4)] {
        add_test_edge(&mut adjacency, lhs, rhs);
    }
    let degrees = adjacency.iter().map(BitSet::cardinality).collect();
    let fragment = MaxCliqueFragment {
        objective_vars: (1..=5).collect(),
        adjacency,
        degrees,
        side_assignment: HashMap::new(),
    };
    let mut should_stop = || false;
    let mut on_improve = |_: i128, _: &[bool]| {};
    let mut search = MaxCliqueSearch {
        instance: &instance,
        objective,
        fragment: &fragment,
        should_stop: &mut should_stop,
        on_improve: &mut on_improve,
        best_vertices: Vec::new(),
        best_assignment: Vec::new(),
        best_objective: 0,
        interrupted: false,
        validation_failed: false,
        coloring_scratch: ColoringScratch::new(),
    };
    let mut candidates = BitSet::full(5);

    assert!(search.prune_decision_candidates(3, &mut candidates));

    assert!(candidates.cardinality() < 3);
    assert!(!candidates.contains(0));
    assert!(!candidates.contains(2));
    assert!(!candidates.contains(3));
    assert!(!candidates.contains(4));
}

#[test]
fn decision_core_prune_trace_emits_replayable_transcript() {
    let fragment = test_fragment_from_edges(5, &[(0, 1), (1, 2), (3, 4)]);
    let graph = replayable_graph_from_fragment(&fragment);
    let mut should_stop = || false;
    let mut interrupted = false;
    let mut no_clique_cache = HashMap::new();
    let mut stats = DecisionSearchStats::new(3);
    let mut prover = CliqueNoKPlusOneProver::new(
        &fragment,
        &mut should_stop,
        &mut interrupted,
        &mut no_clique_cache,
        &mut stats,
    );
    let mut candidates = BitSet::full(5);
    let root_candidates = bitset_vertices(&candidates);
    let mut pruned_vertices = Vec::new();

    assert!(prover.prune_candidates_with_trace(3, &mut candidates, Some(&mut pruned_vertices)));

    let child_candidates = bitset_vertices(&candidates);
    assert_eq!(pruned_vertices, vec![0, 2, 3, 4]);
    assert_eq!(child_candidates, vec![1]);

    let transcript = ReplayableCliqueBbTranscript {
        target_size: 3,
        root: CliqueBbNodeTranscript {
            candidates: root_candidates,
            proof: CliqueBbNodeProof::DegreeCorePrune {
                pruned_vertices,
                child: Box::new(CliqueBbNodeTranscript {
                    candidates: child_candidates,
                    proof: CliqueBbNodeProof::CardinalityPrune {},
                }),
            },
        },
    };
    let check = check_replayable_clique_bb_transcript(&graph, &transcript)
        .expect("emitted degree-core transcript should replay");

    assert_eq!(check.visited_nodes, 2);
    assert_eq!(check.degree_core_prunes, 1);
    assert_eq!(check.degree_core_pruned_vertices, 4);
    assert_eq!(check.cardinality_prunes, 1);
    assert!(!interrupted);
}

#[test]
fn partial_frontier_builder_leaves_explicit_open_obligation_at_node_limit() {
    let fragment = test_fragment_from_edges(5, &REPLAYABLE_CERTIFICATE_TEST_EDGES);
    let graph = replayable_graph_from_fragment(&fragment);
    let mut should_stop = || false;
    let mut builder = CliquePartialFrontierBuilder::new(&fragment, &mut should_stop, 0, 1);

    let frontier = builder
        .build(4, &BitSet::full(5))
        .expect("open root frontier should be representable");
    let check = check_replayable_clique_bb_partial_frontier(&graph, &frontier)
        .expect("open frontier should replay");

    assert_eq!(frontier.target_size, 4);
    assert_eq!(check.open_obligations, 1);
    assert!(!check.proves_no_target_clique);
}

#[test]
fn partial_frontier_builder_can_close_small_absent_target() {
    let fragment = test_fragment_from_edges(5, &[(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]);
    let graph = replayable_graph_from_fragment(&fragment);
    let mut should_stop = || false;
    let mut builder = CliquePartialFrontierBuilder::new(&fragment, &mut should_stop, 10_000, 8);

    let frontier = builder
        .build(3, &BitSet::full(5))
        .expect("cycle no-triangle frontier should close");
    let check = check_replayable_clique_bb_partial_frontier(&graph, &frontier)
        .expect("closed frontier should replay");

    assert_eq!(check.target_size, 3);
    assert_eq!(check.open_obligations, 0);
    assert!(check.proves_no_target_clique);
}

#[test]
fn partial_frontier_json_uses_checker_compatible_empty_variant_objects() {
    let frontier = ReplayableCliqueBbPartialFrontier {
        target_size: 3,
        root: CliqueBbPartialFrontierNode {
            candidates: vec![0, 1, 2],
            proof: CliqueBbPartialFrontierProof::OpenObligation {},
        },
    };

    let json = serde_json::to_string(&frontier).expect("frontier should serialize as JSON");
    assert!(json.contains(r#""OpenObligation":{}"#));

    let parsed: ReplayableCliqueBbPartialFrontier =
        serde_json::from_str(&json).expect("serialized frontier should parse");
    assert_eq!(parsed, frontier);
}

#[test]
fn clique_frontier_export_path_values_are_default_off_and_independent() {
    let none = clique_frontier_export_paths_from_env_values(None, None);
    assert!(none.is_empty());
    assert!(!clique_frontier_export_requested_from_env_values(
        None, None
    ));

    let general = OsStr::new("frontier.json");
    let legacy = OsStr::new("c500-frontier.json");
    let both = clique_frontier_export_paths_from_env_values(Some(general), Some(legacy));
    assert_eq!(both.general_artifact, Some(OsString::from(general)));
    assert_eq!(both.legacy_c500_raw, Some(OsString::from(legacy)));
    assert!(!both.is_empty());
    assert!(clique_frontier_export_requested_from_env_values(
        Some(general),
        Some(legacy)
    ));

    let legacy_only = clique_frontier_export_paths_from_env_values(None, Some(legacy));
    assert_eq!(legacy_only.general_artifact, None);
    assert_eq!(legacy_only.legacy_c500_raw, Some(OsString::from(legacy)));
}

#[test]
fn replayable_frontier_export_general_writes_metadata_artifact() {
    let frontier = ReplayableCliqueBbPartialFrontier {
        target_size: 3,
        root: CliqueBbPartialFrontierNode {
            candidates: vec![0, 1, 2],
            proof: CliqueBbPartialFrontierProof::OpenObligation {},
        },
    };
    let target = test_frontier_import_target(3, 0x0123_4567_89ab_cdef, 3);
    let mut json = Vec::new();

    write_replayable_frontier_artifact_json(&mut json, target, &frontier)
        .expect("general frontier artifact should serialize");
    let value: serde_json::Value =
        serde_json::from_slice(&json).expect("general artifact should parse");

    assert_eq!(
        value["format"],
        serde_json::json!(REPLAYABLE_CLIQUE_FRONTIER_FORMAT)
    );
    assert_eq!(
        value["metadata"]["benchmark"],
        serde_json::json!(target.name)
    );
    assert_eq!(value["metadata"]["vertex_count"], serde_json::json!(3));
    assert_eq!(
        value["metadata"]["graph_fingerprint"],
        serde_json::json!("0x0123456789abcdef")
    );
    assert_eq!(value["metadata"]["target_size"], serde_json::json!(3));
    assert_eq!(
        value["metadata"]["incumbent_size"],
        serde_json::json!(TEST_FRONTIER_INCUMBENT.len())
    );
    assert!(value.get("frontier").is_some());
}

#[test]
fn replayable_frontier_export_general_round_trips_through_general_import() {
    let fragment = test_fragment_from_edges(5, &[(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]);
    let graph = replayable_graph_from_fragment(&fragment);
    let mut should_stop = || false;
    let mut builder = CliquePartialFrontierBuilder::new(&fragment, &mut should_stop, 10_000, 8);
    let frontier = builder
        .build(3, &BitSet::full(5))
        .expect("cycle no-triangle frontier should close");
    let target = test_frontier_import_target(5, 0x0123_4567_89ab_cdef, 3);
    let mut json = Vec::new();

    write_replayable_frontier_artifact_json(&mut json, target, &frontier)
        .expect("general frontier artifact should serialize");
    let import: ReplayableCliqueFrontierImport =
        serde_json::from_slice(&json).expect("general artifact should parse");
    let resolved = resolve_replayable_frontier_import(import, target, false)
        .expect("matching metadata should accept");
    let check = check_replayable_clique_bb_partial_frontier(&graph, &resolved)
        .expect("accepted frontier should still replay");

    assert_eq!(resolved, frontier);
    assert_eq!(check.open_obligations, 0);
    assert!(check.proves_no_target_clique);
}

#[test]
fn replayable_frontier_export_legacy_keeps_raw_frontier_shape() {
    let frontier = ReplayableCliqueBbPartialFrontier {
        target_size: 3,
        root: CliqueBbPartialFrontierNode {
            candidates: vec![0, 1, 2],
            proof: CliqueBbPartialFrontierProof::OpenObligation {},
        },
    };
    let target = test_frontier_import_target(3, 0x1234, 3);
    let mut json = Vec::new();

    write_legacy_replayable_frontier_json(&mut json, &frontier)
        .expect("legacy frontier should serialize");
    let value: serde_json::Value =
        serde_json::from_slice(&json).expect("legacy frontier should parse");
    assert!(value.get("metadata").is_none());
    assert!(value.get("frontier").is_none());

    let import: ReplayableCliqueFrontierImport =
        serde_json::from_slice(&json).expect("legacy import should parse");
    assert_eq!(
        resolve_replayable_frontier_import(import, target, false),
        Err(ReplayableCliqueFrontierImportReject::MissingMetadata)
    );

    let import: ReplayableCliqueFrontierImport =
        serde_json::from_slice(&json).expect("legacy import should parse");
    assert_eq!(
        resolve_replayable_frontier_import(import, target, true),
        Ok(frontier)
    );
}

#[test]
fn replayable_frontier_import_targets_include_c1000_no69() {
    let c500 = clique_frontier_import_target_by_fingerprint(500, C500_9_FINGERPRINT)
        .expect("C500 no58 import target should be registered");
    let c1000 = clique_frontier_import_target_by_fingerprint(1000, C1000_9_FINGERPRINT)
        .expect("C1000 no69 import target should be registered");

    assert_eq!(c500.target_size, C500_NO58_TARGET_SIZE);
    assert_eq!(c500.incumbent_size, C500_NO58_INCUMBENT_SIZE);
    assert_eq!(c500.incumbent.len(), C500_NO58_INCUMBENT_SIZE);
    assert_eq!(c1000.target_size, C1000_NO69_TARGET_SIZE);
    assert_eq!(c1000.incumbent_size, C1000_NO69_INCUMBENT_SIZE);
    assert_eq!(c1000.incumbent.len(), C1000_NO69_INCUMBENT_SIZE);
}

#[test]
fn replayable_frontier_import_accepts_generalized_metadata() {
    let fragment = test_fragment_from_edges(5, &[(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]);
    let graph = replayable_graph_from_fragment(&fragment);
    let mut should_stop = || false;
    let mut builder = CliquePartialFrontierBuilder::new(&fragment, &mut should_stop, 10_000, 8);
    let frontier = builder
        .build(3, &BitSet::full(5))
        .expect("cycle no-triangle frontier should close");
    let target = test_frontier_import_target(5, 0x0123_4567_89ab_cdef, 3);
    let import: ReplayableCliqueFrontierImport =
        serde_json::from_value(replayable_frontier_artifact_json(target, &frontier))
            .expect("metadata artifact should parse");

    let resolved = resolve_replayable_frontier_import(import, target, false)
        .expect("matching metadata should accept");
    let check = check_replayable_clique_bb_partial_frontier(&graph, &resolved)
        .expect("accepted frontier should still replay");

    assert_eq!(resolved, frontier);
    assert_eq!(check.open_obligations, 0);
    assert!(check.proves_no_target_clique);
}

#[test]
fn replayable_frontier_import_rejects_mismatched_target_and_fingerprint() {
    let frontier = ReplayableCliqueBbPartialFrontier {
        target_size: 3,
        root: CliqueBbPartialFrontierNode {
            candidates: vec![0, 1, 2],
            proof: CliqueBbPartialFrontierProof::OpenObligation {},
        },
    };
    let target = test_frontier_import_target(3, 0xfeed_beef, 3);

    let mut wrong_target = replayable_frontier_artifact_json(target, &frontier);
    wrong_target["metadata"]["target_size"] = serde_json::json!(4);
    let import: ReplayableCliqueFrontierImport =
        serde_json::from_value(wrong_target).expect("wrong-target artifact should parse");
    assert_eq!(
        resolve_replayable_frontier_import(import, target, false),
        Err(ReplayableCliqueFrontierImportReject::WrongTarget)
    );

    let mut wrong_fingerprint = replayable_frontier_artifact_json(target, &frontier);
    wrong_fingerprint["metadata"]["graph_fingerprint"] = serde_json::json!("0xfeed_beee");
    let import: ReplayableCliqueFrontierImport =
        serde_json::from_value(wrong_fingerprint).expect("wrong-fingerprint artifact should parse");
    assert_eq!(
        resolve_replayable_frontier_import(import, target, false),
        Err(ReplayableCliqueFrontierImportReject::WrongFingerprint)
    );
}

#[test]
fn replayable_frontier_import_rejects_raw_frontier_without_legacy_path() {
    let frontier = ReplayableCliqueBbPartialFrontier {
        target_size: 3,
        root: CliqueBbPartialFrontierNode {
            candidates: vec![0, 1, 2],
            proof: CliqueBbPartialFrontierProof::OpenObligation {},
        },
    };
    let target = test_frontier_import_target(3, 0x1234, 3);
    let import = ReplayableCliqueFrontierImport::LegacyFrontier(frontier.clone());

    assert_eq!(
        resolve_replayable_frontier_import(import, target, false),
        Err(ReplayableCliqueFrontierImportReject::MissingMetadata)
    );
    assert_eq!(
        resolve_replayable_frontier_import(
            ReplayableCliqueFrontierImport::LegacyFrontier(frontier.clone()),
            target,
            true,
        ),
        Ok(frontier)
    );
}

#[test]
fn replayable_frontier_import_rejects_invalid_incumbent_after_closed_replay() {
    let instance = unconstrained_instance(2);
    let objective = instance.objective.as_ref().expect("test objective");
    let fragment = test_fragment_from_edges(2, &[]);
    let mut should_stop = || false;
    let mut on_improve = |_objective: i128, _assignment: &[bool]| {};
    let initial_assignment = build_assignment(instance.num_vars, &fragment, &[]);
    let initial_objective = validate_assignment(&instance, objective, &initial_assignment)
        .expect("initial assignment should validate");
    let mut search = MaxCliqueSearch {
        instance: &instance,
        objective,
        fragment: &fragment,
        should_stop: &mut should_stop,
        on_improve: &mut on_improve,
        best_vertices: Vec::new(),
        best_assignment: initial_assignment,
        best_objective: initial_objective,
        interrupted: false,
        validation_failed: false,
        coloring_scratch: ColoringScratch::new(),
    };
    let target = test_frontier_import_target(2, 0x9876, 2);

    assert!(
        search.seed_validated_frontier_incumbent(target).is_none(),
        "a closed frontier must still fail closed when the target incumbent is not a clique"
    );
    assert!(search.best_vertices.is_empty());
}

#[test]
fn interrupted_search_returns_satisfiable_incumbent() {
    let instance = parse_opb(
        "* #variable= 3 #constraint= 0\n\
             min: -1 x1 -1 x2 -1 x3 ;\n",
    )
    .expect("test OPB should parse");
    let objective = instance.objective.as_ref().unwrap();
    let fragment = detect_fragment(&instance, objective)
        .expect("unconstrained max-clique fragment should be detected");
    let mut should_stop = || true;

    let result = solve_detected_max_clique(
        &instance,
        objective,
        &fragment,
        &mut should_stop,
        &mut |_, _| {},
        &mut PublishedCliqueExactModeStats::default(),
    )
    .expect("detected fragment should return a validated incumbent");

    assert_eq!(result.status, PbStatus::Satisfiable);
    assert_eq!(result.objective, Some(0));
    assert!(verify_all_constraints(
        &instance.constraints,
        &result.assignment
    ));
}

#[test]
fn semantic_validation_failure_downgrades_exhaustive_claim() {
    let instance = parse_opb(
        "* #variable= 2 #constraint= 1\n\
             min: -1 x1 -1 x2 ;\n\
             -1 x1 -1 x2 >= -1 ;\n",
    )
    .expect("test OPB should parse");
    let objective = instance.objective.as_ref().unwrap();
    let mut fragment =
        detect_fragment(&instance, objective).expect("base fragment should be detected");
    fragment.adjacency[0].insert(1);
    fragment.adjacency[1].insert(0);

    let mut should_stop = || false;
    let result = solve_detected_max_clique(
        &instance,
        objective,
        &fragment,
        &mut should_stop,
        &mut |_, _| {},
        &mut PublishedCliqueExactModeStats::default(),
    )
    .expect("invalid search graph should still return the validated incumbent");

    assert_eq!(result.status, PbStatus::Satisfiable);
    assert_eq!(result.objective, Some(-1));
    assert!(verify_all_constraints(
        &instance.constraints,
        &result.assignment
    ));
}

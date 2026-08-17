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

include!("tests/detector_and_certificate_gate.rs");

include!("tests/certificate_and_repair.rs");

include!("tests/coloring_and_decision_search.rs");

include!("tests/decision_limits_and_exchange.rs");

include!("tests/finalizers_and_frontier_export.rs");

include!("tests/frontier_import_and_outcomes.rs");

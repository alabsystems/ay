// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::expr::{ChcSort, ChcVar};

#[test]
fn test_dependency_graph_intern() {
    let mut graph = DependencyGraph::new();

    let x = ChcVar::new("x", ChcSort::Int);
    let expr1 = ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(5));
    let expr2 = ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(10));

    // First intern gets id 0
    let id1 = graph.intern(expr1.clone());
    assert_eq!(id1, 0);

    // Second different expr gets id 1
    let id2 = graph.intern(expr2);
    assert_eq!(id2, 1);

    // Same expr should return same id
    let id1_again = graph.intern(expr1);
    assert_eq!(id1_again, 0);

    assert_eq!(graph.num_nodes(), 2);
}

#[test]
fn test_dependency_graph_edges() {
    let mut graph = DependencyGraph::new();

    let x = ChcVar::new("x", ChcSort::Int);
    let expr1 = ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(5));
    let expr2 = ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(10));

    let id1 = graph.intern(expr1);
    let id2 = graph.intern(expr2);

    // No edges initially
    assert!(!graph.has_edge(id1, id2));
    assert!(!graph.has_edge(id2, id1));

    // Add edge
    graph.add_edge(id1, id2);
    assert!(graph.has_edge(id1, id2));
    assert!(!graph.has_edge(id2, id1)); // Directed

    assert_eq!(graph.num_edges(), 1);
}

#[test]
fn test_trace_clear_preserves_graph() {
    let mut trace = Trace::new();

    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(5));
    let id = trace.graph.intern(expr);

    trace.elements.push(TraceElement {
        _transition_id: 0,
        implicant_id: id,
        model: FxHashMap::default(),
    });

    assert_eq!(trace.len(), 1);
    assert_eq!(trace.graph.num_nodes(), 1);

    // Clear should preserve graph
    trace.clear();
    assert_eq!(trace.len(), 0);
    assert_eq!(trace.graph.num_nodes(), 1); // Graph preserved!
}

#[test]
fn test_trace_push_adds_edges() {
    let mut trace = Trace::new();

    let x = ChcVar::new("x", ChcSort::Int);
    let expr1 = ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(5));
    let expr2 = ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(10));

    let id1 = trace.graph.intern(expr1);
    let id2 = trace.graph.intern(expr2);

    // Push first element - no edge yet
    trace.push(TraceElement {
        _transition_id: 0,
        implicant_id: id1,
        model: FxHashMap::default(),
    });
    assert_eq!(trace.graph.num_edges(), 0);

    // Push second element - should add edge from first to second
    trace.push(TraceElement {
        _transition_id: 1,
        implicant_id: id2,
        model: FxHashMap::default(),
    });
    assert!(trace.graph.has_edge(id1, id2));
    assert_eq!(trace.graph.num_edges(), 1);
}

#[test]
fn test_find_looping_infix_no_loop() {
    let mut trace = Trace::new();

    let x = ChcVar::new("x", ChcSort::Int);
    let expr1 = ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(5));
    let expr2 = ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(10));

    let id1 = trace.graph.intern(expr1);
    let id2 = trace.graph.intern(expr2);

    trace.push(TraceElement {
        _transition_id: 0,
        implicant_id: id1,
        model: FxHashMap::default(),
    });
    trace.push(TraceElement {
        _transition_id: 1,
        implicant_id: id2,
        model: FxHashMap::default(),
    });

    // Only edge is id1 -> id2 (forward), no back edge
    assert!(trace.find_looping_infix().is_none());
}

#[test]
fn test_find_looping_infix_with_loop() {
    let mut trace = Trace::new();

    let x = ChcVar::new("x", ChcSort::Int);
    let expr1 = ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(5));
    let expr2 = ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(10));

    let id1 = trace.graph.intern(expr1);
    let id2 = trace.graph.intern(expr2);

    // Manually add a back edge (id2 -> id1) to simulate loop
    trace.graph.add_edge(id2, id1);

    trace.push(TraceElement {
        _transition_id: 0,
        implicant_id: id1,
        model: FxHashMap::default(),
    });
    trace.push(TraceElement {
        _transition_id: 1,
        implicant_id: id2,
        model: FxHashMap::default(),
    });

    // Should find loop from position 0 to 1
    let result = trace.find_looping_infix();
    assert!(result.is_some());
    let (start, end) = result.unwrap();
    assert_eq!(start, 0);
    assert_eq!(end, 1);
}

#[test]
fn test_versioned_name() {
    assert_eq!(versioned_name("x", 0), "x");
    assert_eq!(versioned_name("x", 1), "x_1");
    assert_eq!(versioned_name("x", 2), "x_2");
    assert_eq!(versioned_name("counter", 5), "counter_5");
}

mod build_trace;

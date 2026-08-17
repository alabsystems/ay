// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_build_trace_populates_elements_and_edges() {
    let mut trace = Trace::new();
    let mbp = Mbp::new();

    let trace_var_name = "t";
    let state_var_names = vec!["x".to_string()];

    let t = ChcVar::new(trace_var_name, ChcSort::Int);
    let x = ChcVar::new("x", ChcSort::Int);
    let x_next = ChcVar::new("x_next", ChcSort::Int);

    let _transition_id = 1;
    let rule = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(t), ChcExpr::int(_transition_id)),
        ChcExpr::eq(
            ChcExpr::var(x_next),
            ChcExpr::add(ChcExpr::var(x), ChcExpr::int(1)),
        ),
    );

    let mut rule_map: FxHashMap<i128, ChcExpr> = FxHashMap::default();
    rule_map.insert(_transition_id, rule);

    let mut model: FxHashMap<String, SmtValue> = FxHashMap::default();
    // Depth 2 requires t@0 ("t") and t@1 ("t_1"), plus x@0, x@1, x@2.
    model.insert("t".to_string(), SmtValue::Int(_transition_id));
    model.insert("t_1".to_string(), SmtValue::Int(_transition_id));
    model.insert("x".to_string(), SmtValue::Int(0));
    model.insert("x_1".to_string(), SmtValue::Int(1));
    model.insert("x_2".to_string(), SmtValue::Int(2));

    build_trace(
        &mut trace,
        2,
        trace_var_name,
        &state_var_names,
        &rule_map,
        &model,
        &mbp,
    );

    assert_eq!(trace.len(), 2);
    assert_eq!(trace.graph.num_edges(), 1);

    let id0 = trace.elements[0].implicant_id;
    let id1 = trace.elements[1].implicant_id;
    assert!(trace.graph.has_edge(id0, id1));
    assert!(trace.graph.get_expr(id0).is_some());
    assert!(trace.graph.get_expr(id1).is_some());

    assert_eq!(trace.elements[0]._transition_id, _transition_id);
    assert_eq!(trace.elements[1]._transition_id, _transition_id);

    assert_eq!(trace.elements[0].model.get("x"), Some(&SmtValue::Int(0)));
    assert_eq!(
        trace.elements[0].model.get("x_next"),
        Some(&SmtValue::Int(1))
    );
    assert_eq!(
        trace.elements[0].model.get("t"),
        Some(&SmtValue::Int(_transition_id))
    );

    assert_eq!(trace.elements[1].model.get("x"), Some(&SmtValue::Int(1)));
    assert_eq!(
        trace.elements[1].model.get("x_next"),
        Some(&SmtValue::Int(2))
    );
    assert_eq!(
        trace.elements[1].model.get("t"),
        Some(&SmtValue::Int(_transition_id))
    );
}

#[test]
fn test_build_trace_preserves_dependency_graph() {
    let mut trace = Trace::new();
    let mbp = Mbp::new();

    let trace_var_name = "t";
    let state_var_names = vec!["x".to_string()];

    let x = ChcVar::new("x", ChcSort::Int);
    let preexisting = ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0));
    let pre_id = trace.graph.intern(preexisting.clone());
    assert_eq!(pre_id, 0);
    assert_eq!(trace.graph.num_nodes(), 1);
    trace.graph.add_edge(pre_id, pre_id);
    assert_eq!(trace.graph.num_edges(), 1);

    trace.elements.push(TraceElement {
        _transition_id: 0,
        implicant_id: pre_id,
        model: FxHashMap::default(),
    });

    let t = ChcVar::new(trace_var_name, ChcSort::Int);
    let x_next = ChcVar::new("x_next", ChcSort::Int);

    let _transition_id = 1;
    let rule = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(t), ChcExpr::int(_transition_id)),
        ChcExpr::eq(
            ChcExpr::var(x_next),
            ChcExpr::add(ChcExpr::var(x), ChcExpr::int(1)),
        ),
    );

    let mut rule_map: FxHashMap<i128, ChcExpr> = FxHashMap::default();
    rule_map.insert(_transition_id, rule);

    let mut model: FxHashMap<String, SmtValue> = FxHashMap::default();
    model.insert("t".to_string(), SmtValue::Int(_transition_id));
    model.insert("x".to_string(), SmtValue::Int(0));
    model.insert("x_1".to_string(), SmtValue::Int(1));

    build_trace(
        &mut trace,
        1,
        trace_var_name,
        &state_var_names,
        &rule_map,
        &model,
        &mbp,
    );

    // build_trace clears elements, but preserves and extends the graph.
    assert_eq!(trace.len(), 1);
    assert_eq!(trace.graph.num_nodes(), 2);
    assert_eq!(trace.graph.num_edges(), 1);
    assert!(trace.graph.has_edge(pre_id, pre_id));
    assert_eq!(trace.graph.get_expr(pre_id), Some(&preexisting));
}

#[test]
fn test_build_trace_missing_trace_var_skips_step() {
    // Test that missing trace_var values result in skipping that step
    let mut trace = Trace::new();
    let mbp = Mbp::new();

    let trace_var_name = "t";
    let state_var_names = vec!["x".to_string()];

    let t = ChcVar::new(trace_var_name, ChcSort::Int);
    let x = ChcVar::new("x", ChcSort::Int);
    let x_next = ChcVar::new("x_next", ChcSort::Int);

    let rule = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(t), ChcExpr::int(1)),
        ChcExpr::eq(
            ChcExpr::var(x_next),
            ChcExpr::add(ChcExpr::var(x), ChcExpr::int(1)),
        ),
    );

    let mut rule_map: FxHashMap<i128, ChcExpr> = FxHashMap::default();
    rule_map.insert(1, rule);

    // Model missing trace_var at time 0, only present at time 1
    let mut model: FxHashMap<String, SmtValue> = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(0));
    // t@0 ("t") is MISSING
    model.insert("x_1".to_string(), SmtValue::Int(10));
    model.insert("t_1".to_string(), SmtValue::Int(1)); // Present at time 1
    model.insert("x_2".to_string(), SmtValue::Int(11));

    build_trace(
        &mut trace,
        2,
        trace_var_name,
        &state_var_names,
        &rule_map,
        &model,
        &mbp,
    );

    // Should have only 1 element (step 0 skipped due to missing trace_var)
    assert_eq!(trace.len(), 1);
    assert_eq!(trace.elements[0]._transition_id, 1);
    assert_eq!(trace.elements[0].model.get("x"), Some(&SmtValue::Int(10)));
    assert_eq!(
        trace.elements[0].model.get("x_next"),
        Some(&SmtValue::Int(11))
    );
    assert_eq!(trace.elements[0].model.get("t"), Some(&SmtValue::Int(1)));
}

#[test]
fn test_build_trace_unknown_rule_skips_step() {
    // Test that unknown transition IDs result in skipping that step
    let mut trace = Trace::new();
    let mbp = Mbp::new();

    let trace_var_name = "t";
    let state_var_names = vec!["x".to_string()];

    let t = ChcVar::new(trace_var_name, ChcSort::Int);
    let x = ChcVar::new("x", ChcSort::Int);
    let x_next = ChcVar::new("x_next", ChcSort::Int);

    let rule = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(t), ChcExpr::int(1)),
        ChcExpr::eq(ChcExpr::var(x_next), ChcExpr::var(x)),
    );

    let mut rule_map: FxHashMap<i128, ChcExpr> = FxHashMap::default();
    rule_map.insert(1, rule);
    // Note: rule 99 is NOT in rule_map

    let mut model: FxHashMap<String, SmtValue> = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(5));
    model.insert("t".to_string(), SmtValue::Int(99)); // Unknown rule!
    model.insert("x_1".to_string(), SmtValue::Int(5));

    build_trace(
        &mut trace,
        1,
        trace_var_name,
        &state_var_names,
        &rule_map,
        &model,
        &mbp,
    );

    // Should have 0 elements (step skipped due to unknown rule)
    assert_eq!(trace.len(), 0);
    assert_eq!(trace.graph.num_nodes(), 0);
    assert_eq!(trace.graph.num_edges(), 0);
}

#[test]
fn test_build_trace_empty_model() {
    // Test with empty model - all steps should be skipped
    let mut trace = Trace::new();
    let mbp = Mbp::new();

    let state_var_names = vec!["x".to_string()];
    let trace_var_name = "t";

    let rule_map: FxHashMap<i128, ChcExpr> = FxHashMap::default();
    let model: FxHashMap<String, SmtValue> = FxHashMap::default();

    build_trace(
        &mut trace,
        3,
        trace_var_name,
        &state_var_names,
        &rule_map,
        &model,
        &mbp,
    );

    // Should have 0 elements
    assert_eq!(trace.len(), 0);
    assert_eq!(trace.graph.num_nodes(), 0);
    assert_eq!(trace.graph.num_edges(), 0);
}

#[test]
fn test_build_trace_preserves_existing_edges() {
    let mut trace = Trace::new();
    let mbp = Mbp::new();

    let x = ChcVar::new("x", ChcSort::Int);
    let expr1 = ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0));
    let expr2 = ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(1));

    let id1 = trace.graph.intern(expr1);
    let id2 = trace.graph.intern(expr2);

    trace.push(TraceElement {
        _transition_id: 0,
        implicant_id: id1,
        model: FxHashMap::default(),
    });
    trace.push(TraceElement {
        _transition_id: 0,
        implicant_id: id2,
        model: FxHashMap::default(),
    });
    assert!(trace.graph.has_edge(id1, id2));
    assert_eq!(trace.graph.num_nodes(), 2);
    assert_eq!(trace.graph.num_edges(), 1);

    // Depth 0 triggers trace.clear() but does not add any new nodes/edges.
    build_trace(
        &mut trace,
        0,
        "t",
        &["x".to_string()],
        &FxHashMap::default(),
        &FxHashMap::default(),
        &mbp,
    );

    assert!(trace.is_empty());
    assert_eq!(trace.graph.num_nodes(), 2);
    assert_eq!(trace.graph.num_edges(), 1);
    assert!(trace.graph.has_edge(id1, id2));
}

#[test]
fn test_build_trace_missing_next_state_value_omits_next_var() {
    let mut trace = Trace::new();
    let mbp = Mbp::new();

    let trace_var_name = "t";
    let state_var_names = vec!["x".to_string()];

    let t = ChcVar::new(trace_var_name, ChcSort::Int);
    let x = ChcVar::new("x", ChcSort::Int);

    let _transition_id = 1;
    let rule = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(t), ChcExpr::int(_transition_id)),
        ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(7)),
    );

    let mut rule_map: FxHashMap<i128, ChcExpr> = FxHashMap::default();
    rule_map.insert(_transition_id, rule);

    // Intentionally omit x@1 ("x_1"), so x_next should not be present in the projected model.
    let mut model: FxHashMap<String, SmtValue> = FxHashMap::default();
    model.insert("t".to_string(), SmtValue::Int(_transition_id));
    model.insert("x".to_string(), SmtValue::Int(7));

    build_trace(
        &mut trace,
        1,
        trace_var_name,
        &state_var_names,
        &rule_map,
        &model,
        &mbp,
    );

    assert_eq!(trace.len(), 1);
    assert_eq!(trace.elements[0].model.get("x"), Some(&SmtValue::Int(7)));
    assert!(!trace.elements[0].model.contains_key("x_next"));
}

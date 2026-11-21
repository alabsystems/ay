// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The engine bounds its SAT core's clause database by the memory it is
//! given (`set_memory_budget`).

use super::*;
use crate::domain::Domain;

fn small_model(engine: &mut CpSatEngine) {
    let x = engine.new_int_var(Domain::new(0, 9), Some("x"));
    let y = engine.new_int_var(Domain::new(0, 9), Some("y"));
    engine.add_constraint(Constraint::LinearLe {
        coeffs: vec![1, 1],
        vars: vec![x, y],
        rhs: 7,
    });
    engine.add_constraint(Constraint::LinearGe {
        coeffs: vec![1, -1],
        vars: vec![x, y],
        rhs: 3,
    });
}

#[test]
fn memory_budget_installs_a_clause_db_ceiling_when_the_search_starts() {
    let mut engine = CpSatEngine::new();
    small_model(&mut engine);
    let budget = 1 << 30;
    engine.set_memory_budget(budget);
    assert_eq!(engine.clause_db_ceiling(), None, "nothing before a search");

    assert!(matches!(engine.solve(), CpSolveResult::Sat(_)));

    let ceiling = engine
        .clause_db_ceiling()
        .expect("a search with propagators installs the ceiling");
    assert!(
        ceiling < budget,
        "the clause database gets a share of the budget, not all of it: {ceiling}"
    );
    assert!(ceiling > 0);
}

#[test]
fn no_memory_budget_no_ceiling() {
    let mut engine = CpSatEngine::new();
    small_model(&mut engine);
    engine.set_memory_budget(0);
    assert!(matches!(engine.solve(), CpSolveResult::Sat(_)));
    assert_eq!(engine.clause_db_ceiling(), None);
}

/// The engine writes no proof, so its SAT core keeps no clause-ID table: the
/// table costs 8 bytes per arena word, twice the clause arena.
#[test]
fn the_sat_core_keeps_no_clause_id_table() {
    let mut engine = CpSatEngine::new();
    small_model(&mut engine);
    assert!(matches!(engine.solve(), CpSolveResult::Sat(_)));
    let report = engine.sat.memory_report();
    assert!(report.contains("ids_disabled=true"), "{report}");
    assert!(report.contains("clause_ids=0 "), "{report}");
}

/// A memory budget sizes the order encoding: a domain over the default
/// limit is planned when the budget covers it, and the engine still refuses
/// one the budget does not cover. The plan is checked, not a solve: encoding
/// 2^21 literals takes about 1.6 GB.
#[test]
fn memory_budget_sizes_the_order_encoding() {
    let default = crate::encoder::MAX_PREALLOCATED_ORDER_LITERALS;
    let wide = default as i64 * 2;
    let literals = wide as u128 + 2;
    let build = |budget: usize| {
        let mut engine = CpSatEngine::new();
        engine.set_memory_budget(budget);
        engine.new_int_var(Domain::new(0, wide), Some("x"));
        engine
    };

    // Without a budget: the default limit refuses it, as before.
    let engine = build(0);
    assert_eq!(engine.encoder.literal_limit(), default);
    assert_eq!(
        engine.encoder.preallocation_plan(),
        Err(
            crate::encoder::OrderEncodingCapacityError::LiteralLimitExceeded {
                required: literals,
                limit: default,
            }
        )
    );

    // A budget covering twice the literals at ORDER_LITERAL_BYTES each:
    // half of it goes to the encoding.
    let budget = 4 * literals as usize * ORDER_LITERAL_BYTES;
    let engine = build(budget);
    assert_eq!(engine.encoder.literal_limit(), 2 * literals);
    assert_eq!(engine.encoder.preallocation_plan(), Ok(literals));

    // A budget too small for it keeps the default limit and refuses.
    let mut engine = build(64 * 1024 * 1024);
    assert_eq!(engine.encoder.literal_limit(), default);
    assert!(matches!(
        engine.try_pre_compile(),
        Err(crate::encoder::OrderEncodingCapacityError::LiteralLimitExceeded { .. })
    ));
}

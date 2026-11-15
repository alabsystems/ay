// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! ITP-BOARD unit tests (the board is process-global: assert lower bounds).

use super::*;

fn find_cell<'v>(board: &'v Value, engine: &str, source: &str, recipe: &str) -> &'v Value {
    board["itp"]
        .as_array()
        .unwrap()
        .iter()
        .find(|cell| {
            cell["engine"] == engine && cell["source"] == source && cell["recipe"] == recipe
        })
        .unwrap()
}

#[test]
fn requests_outcomes_and_exits_accumulate() {
    let recipe = Some(ItpRecipe::McMillanPrime);
    record_request(EngineTag::SplitTpa, Source::SessionBound, recipe);
    record_request(EngineTag::SplitTpa, Source::SessionBound, recipe);
    record_outcome(
        EngineTag::SplitTpa,
        Source::SessionBound,
        recipe,
        ItpOutcome::Served { solves: 3 },
        Duration::from_micros(40),
    );
    record_outcome(
        EngineTag::SplitTpa,
        Source::SessionBound,
        recipe,
        ItpOutcome::Failed(ItpFail::TrustStep),
        Duration::from_micros(4000),
    );
    record_pre_validation_invalid(EngineTag::SplitTpa, Source::SessionBound, recipe);
    record_engine_exit_detail(
        EngineTag::SplitTpa,
        ExitReason::BaseUnknown,
        7,
        "budget_shaped=true",
    );
    let board = board_json();
    let cell = find_cell(&board, "split_tpa", "session_bound", "mcmillan_prime");
    assert!(cell["requests"].as_u64().unwrap() >= 2);
    assert!(cell["served"].as_u64().unwrap() >= 1);
    assert!(cell["solves"].as_u64().unwrap() >= 3);
    assert!(cell["fail"]["trust_step"].as_u64().unwrap() >= 1);
    assert!(cell["pre_validation_invalid"].as_u64().unwrap() >= 1);
    assert!(board["exits"]
        .as_array()
        .unwrap()
        .iter()
        .any(|e| e["engine"] == "split_tpa" && e["reason"] == "base_unknown" && e["k"] == 7));
}

#[test]
fn engine_tag_scope_nests_and_restores() {
    assert_eq!(current_engine(), EngineTag::Other);
    {
        let _outer = ScopedEngineTag::install(EngineTag::Imc);
        assert_eq!(current_engine(), EngineTag::Imc);
        {
            let _inner = ScopedEngineTag::install(EngineTag::Pdr);
            assert_eq!(current_engine(), EngineTag::Pdr);
        }
        assert_eq!(current_engine(), EngineTag::Imc);
    }
    assert_eq!(current_engine(), EngineTag::Other);
}

#[test]
fn histogram_buckets_are_log2_upper_bounds() {
    let mut hist = Hist::default();
    hist.add(Duration::from_micros(0));
    hist.add(Duration::from_micros(1));
    hist.add(Duration::from_micros(1000));
    let json = hist.to_json();
    assert_eq!(json["count"], 3);
    assert_eq!(json["max_us"], 1000);
    let buckets = json["le_us"].as_array().unwrap();
    assert_eq!(buckets[0], json!([1, 1]));
    assert_eq!(buckets[1], json!([2, 1]));
    assert_eq!(buckets[2], json!([1024, 1]));
}

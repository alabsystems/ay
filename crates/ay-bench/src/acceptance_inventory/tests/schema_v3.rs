// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::{Inventory, INVENTORY_SCHEMA_V2, INVENTORY_SCHEMA_V3};
use serde_json::{json, Value};

fn document() -> Value {
    let mut value = super::schema_v2::document();
    value["schema"] = json!(INVENTORY_SCHEMA_V3);
    value["request_inventory"].as_array_mut().expect("requests").push(json!({
        "id":"R23", "title":"ordinary typed range writes",
        "source_requests":["the development design notes"],
        "required_routes":["chc-consumer-native-typed-pdr"],
        "harness_or_solve_budget_ms":null,
        "required_checks":["both Safe originals and reachable Unsafe with private consumer replay"],
        "stored_input_ids":[]
    }));
    value
}

#[test]
fn v3_preserves_all_32_prior_contracts_and_keeps_all_33_unqualified() {
    let previous = Inventory::parse(&super::schema_v2::document().to_string()).expect("v2");
    let current = Inventory::parse(&document().to_string()).expect("v3");
    assert_eq!(
        &current.document.request_inventory[..32],
        previous.document.request_inventory.as_slice()
    );
    let plan = current.plan();
    assert_eq!(plan.requests.len(), 33);
    assert!(!plan.promotable_for_ask_closure);
    assert!(plan.requests.iter().all(|r| !r.blockers.is_empty()));
}

#[test]
fn v3_refuses_missing_and_extra_contracts_and_v2_refuses_expansion() {
    for id in ["R01", "R22a", "R22d", "R23", "U7"] {
        let mut value = document();
        value["request_inventory"]
            .as_array_mut()
            .expect("requests")
            .retain(|r| r["id"] != id);
        assert!(
            Inventory::parse(&value.to_string()).is_err(),
            "missing {id}"
        );
    }
    let mut value = document();
    value["request_inventory"][32]["id"] = json!("R24");
    assert!(Inventory::parse(&value.to_string()).is_err());
    value = document();
    value["schema"] = json!(INVENTORY_SCHEMA_V2);
    assert!(Inventory::parse(&value.to_string()).is_err());
}

#[test]
fn v3_validates_the_new_consumer_route_instead_of_skipping_it() {
    let mut value = document();
    value["request_inventory"][32]["required_routes"] = json!(["undefined-range-write-route"]);
    assert!(Inventory::parse(&value.to_string()).is_err());
}

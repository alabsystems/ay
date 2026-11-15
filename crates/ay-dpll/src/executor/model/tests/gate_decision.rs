// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::gate_decision::gate_keeps_sat;

/// Runs whichever twin this build compiled (`gate_decision.rs` under
/// `cfg(deductive_verify)`, else `gate_decision_stock.rs`): an enforced gate keeps
/// only a confirmed `sat`, and nothing that was not `sat` is ever kept.
#[test]
fn gate_keeps_only_confirmed_sat_under_enforcement() {
    for was_sat in [false, true] {
        for confirmed in [false, true] {
            for enforce in [false, true] {
                assert_eq!(
                    gate_keeps_sat(was_sat, confirmed, enforce),
                    was_sat && (confirmed || !enforce),
                    "was_sat={was_sat} confirmed={confirmed} enforce={enforce}"
                );
            }
        }
    }
}

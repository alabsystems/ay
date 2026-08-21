// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

pub(super) fn sat_relu_rup_parser_enforces_caps_before_body_allocation() {
    let digest = "00".repeat(32);
    for oversized in [
        format!("vars={}", MAX_SAT_RELU_RUP_VARS + 1),
        format!("originals={}", MAX_SAT_RELU_RUP_ORIGINALS + 1),
        format!("steps={}", MAX_SAT_RELU_RUP_STEPS + 1),
        format!("derived_lits={}", MAX_SAT_RELU_RUP_LITERALS + 1),
        format!("hints={}", MAX_SAT_RELU_RUP_HINTS + 1),
    ] {
        let mut fields = vec![
            "vars=1".to_owned(),
            "originals=1".to_owned(),
            "steps=1".to_owned(),
            "derived_lits=0".to_owned(),
            "hints=1".to_owned(),
        ];
        let key = oversized.split('=').next().expect("field key");
        let position = fields
            .iter()
            .position(|field| field.starts_with(key))
            .expect("known field");
        fields[position] = oversized;
        let header = format!(
            "sat-relu-rup format=1 model=sha256:{digest} cnf=sha256:{digest} {} empty=2",
            fields.join(" ")
        );
        let lines = [header.as_str(), "step 2 lits=0 hints=1 1", "end"];
        assert!(
            parse_sat_relu_rup(&lines, 0).is_err(),
            "oversized header must decline before allocating its declared body"
        );
    }

    let header = format!(
        "sat-relu-rup format=1 model=sha256:{digest} cnf=sha256:{digest} \
             vars=1 originals=1 steps=1 derived_lits={} hints=0 empty=2",
        MAX_SAT_RELU_RUP_ITEMS_PER_STEP + 1
    );
    let step = format!(
        "step 2 lits={} hints=0",
        MAX_SAT_RELU_RUP_ITEMS_PER_STEP + 1
    );
    let lines = [header.as_str(), step.as_str(), "end"];
    assert!(
        parse_sat_relu_rup(&lines, 0).is_err(),
        "one oversized clause must fail before literal allocation"
    );
}

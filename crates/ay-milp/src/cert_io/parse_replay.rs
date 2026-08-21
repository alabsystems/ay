// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

pub(super) fn parse_replay(
    lines: &[&str],
    start: usize,
) -> Result<(ReplayClaim, usize), CertIoError> {
    let claim = lines[start].trim()["replay".len()..].trim().to_string();
    let mut rc = ReplayClaim {
        claim,
        device: String::new(),
        method: String::new(),
        arithmetic: String::new(),
        nodes_visited: None,
        node_budget: 0,
        outcome: String::new(),
        nondeterminism: Vec::new(),
        reproduce: String::new(),
        tcb: String::new(),
    };
    let mut i = start + 1;
    while i < lines.len() {
        let l = lines[i].trim();
        if l == "end" {
            return Ok((rc, i + 1));
        }
        let (k, v) = l.split_once(char::is_whitespace).unwrap_or((l, ""));
        let v = v.trim().to_string();
        match k {
            "device" => rc.device = v,
            "method" => rc.method = v,
            "arithmetic" => rc.arithmetic = v,
            "nodes-visited" => rc.nodes_visited = v.parse().ok(),
            "node-budget" => rc.node_budget = v.parse().unwrap_or(0),
            "outcome" => rc.outcome = v,
            "nondeterminism" => rc.nondeterminism.push(v),
            "reproduce" => rc.reproduce = v,
            "tcb" => rc.tcb = v,
            other => {
                return Err(CertIoError::Malformed {
                    line: i + 1,
                    msg: format!("unknown replay record `{other}`"),
                })
            }
        }
        i += 1;
    }
    Err(CertIoError::Malformed {
        line: start + 1,
        msg: "replay block not terminated".into(),
    })
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

pub(super) fn parity_infeasibility_block(certificate: &ParityInfeasibilityCertificate) -> String {
    let mut block = String::new();
    let _ = writeln!(block, "parity-gf2 rows={}", certificate.rows().len());
    for &row in certificate.rows() {
        let _ = writeln!(block, "row {row}");
    }
    let _ = writeln!(block, "end");
    block
}

pub(super) const MAX_SAT_RELU_RUP_BYTES: usize = 64 * 1024 * 1024;
pub(super) const MAX_SAT_RELU_RUP_VARS: usize = 1_000_000;
pub(super) const MAX_SAT_RELU_RUP_ORIGINALS: usize = 2_000_000;
pub(super) const MAX_SAT_RELU_RUP_STEPS: usize = 2_000_000;
pub(super) const MAX_SAT_RELU_RUP_LITERALS: usize = 8_000_000;
pub(super) const MAX_SAT_RELU_RUP_HINTS: usize = 8_000_000;
pub(super) const MAX_SAT_RELU_RUP_ITEMS_PER_STEP: usize = 1_048_576;

pub(super) fn resolution_literal_token(literal: Literal) -> Option<i32> {
    let variable = i32::try_from(literal.variable().index())
        .ok()?
        .checked_add(1)?;
    Some(if literal.is_positive() {
        variable
    } else {
        -variable
    })
}

pub(super) fn digest_hex(digest: &[u8; 32]) -> String {
    let mut encoded = String::with_capacity(64);
    for byte in digest {
        let _ = write!(encoded, "{byte:02x}");
    }
    encoded
}

pub(super) fn sat_relu_rup_structure_is_canonical(
    certificate: &SatReluInfeasibilityCertificate,
) -> bool {
    let derived = certificate.derived();
    let Some(last) = derived.last() else {
        return false;
    };
    if last.id != certificate.empty_clause_id() || !last.clause.is_empty() {
        return false;
    }

    let mut previous = certificate.num_original_clauses() as u64;
    for (index, step) in derived.iter().enumerate() {
        if step.id <= previous
            || step
                .clause
                .iter()
                .any(|literal| literal.variable().index() >= certificate.num_vars())
        {
            return false;
        }
        if step.rup_hints.iter().any(|&hint| {
            hint == 0
                || hint >= step.id
                || (hint > certificate.num_original_clauses() as u64
                    && derived[..index]
                        .binary_search_by_key(&hint, |known| known.id)
                        .is_err())
        }) {
            return false;
        }
        previous = step.id;
    }
    true
}

pub(super) fn sat_relu_rup_block(
    certificate: &SatReluInfeasibilityCertificate,
    byte_limit: usize,
) -> Option<String> {
    let byte_limit = byte_limit.min(MAX_SAT_RELU_RUP_BYTES);
    let derived_literals = certificate
        .derived()
        .iter()
        .try_fold(0usize, |total, step| total.checked_add(step.clause.len()))?;
    let hints = certificate
        .derived()
        .iter()
        .try_fold(0usize, |total, step| {
            total.checked_add(step.rup_hints.len())
        })?;
    if certificate.format() != 1
        || certificate.num_vars() > MAX_SAT_RELU_RUP_VARS
        || certificate.num_original_clauses() > MAX_SAT_RELU_RUP_ORIGINALS
        || certificate.derived().len() > MAX_SAT_RELU_RUP_STEPS
        || derived_literals > MAX_SAT_RELU_RUP_LITERALS
        || hints > MAX_SAT_RELU_RUP_HINTS
        || certificate.empty_clause_id() > u64::from(u32::MAX)
        || !sat_relu_rup_structure_is_canonical(certificate)
        || certificate.derived().iter().any(|step| {
            step.id == 0
                || step.id > u64::from(u32::MAX)
                || step.clause.len() > MAX_SAT_RELU_RUP_ITEMS_PER_STEP
                || step.rup_hints.len() > MAX_SAT_RELU_RUP_ITEMS_PER_STEP
        })
    {
        return None;
    }

    let mut block = String::new();
    let _ = writeln!(
        block,
        "sat-relu-rup format={} model=sha256:{} cnf=sha256:{} vars={} originals={} \
         steps={} derived_lits={} hints={} empty={}",
        certificate.format(),
        digest_hex(certificate.model_canon_sha256()),
        digest_hex(certificate.cnf_sha256()),
        certificate.num_vars(),
        certificate.num_original_clauses(),
        certificate.derived().len(),
        derived_literals,
        hints,
        certificate.empty_clause_id(),
    );
    if block.len() > byte_limit {
        return None;
    }
    for step in certificate.derived() {
        let _ = write!(block, "step {} lits={}", step.id, step.clause.len());
        for &literal in &step.clause {
            let _ = write!(block, " {}", resolution_literal_token(literal)?);
            if block.len() > byte_limit {
                return None;
            }
        }
        let _ = write!(block, " hints={}", step.rup_hints.len());
        for hint in &step.rup_hints {
            let _ = write!(block, " {hint}");
            if block.len() > byte_limit {
                return None;
            }
        }
        block.push('\n');
        if block.len() > byte_limit {
            return None;
        }
    }
    let _ = writeln!(block, "end");
    (block.len() <= byte_limit).then_some(block)
}

pub(super) fn single_row_dp_block(
    certificate: &SingleRowDpInfeasibilityCertificate,
) -> Option<String> {
    let encoded = encode_single_row_dp_infeasibility_certificate_json(certificate).ok()?;
    let json = std::str::from_utf8(&encoded).ok()?;
    let mut block = String::new();
    let _ = writeln!(block, "single-row-dp json_bytes={}", encoded.len());
    let _ = writeln!(block, "{json}");
    let _ = writeln!(block, "end");
    Some(block)
}

pub(super) fn multi_row_bdd_block(
    certificate: &MultiRowBddInfeasibilityCertificate,
) -> Option<String> {
    let encoded = encode_multi_row_bdd_infeasibility_certificate_json(certificate).ok()?;
    let json = std::str::from_utf8(&encoded).ok()?;
    let mut block = String::new();
    let _ = writeln!(block, "multi-row-bdd json_bytes={}", encoded.len());
    let _ = writeln!(block, "{json}");
    let _ = writeln!(block, "end");
    Some(block)
}

pub(super) fn open_domain_dp_block(
    certificate: &SingleRowDpInfeasibilityCertificate,
) -> Option<String> {
    let encoded = encode_single_row_dp_infeasibility_certificate_json(certificate).ok()?;
    let json = std::str::from_utf8(&encoded).ok()?;
    let mut block = String::new();
    let _ = writeln!(block, "open-domain-dp json_bytes={}", encoded.len());
    let _ = writeln!(block, "{json}");
    let _ = writeln!(block, "end");
    Some(block)
}

pub(super) fn open_domain_bdd_block(
    certificate: &MultiRowBddInfeasibilityCertificate,
) -> Option<String> {
    let encoded = encode_multi_row_bdd_infeasibility_certificate_json(certificate).ok()?;
    let json = std::str::from_utf8(&encoded).ok()?;
    let mut block = String::new();
    let _ = writeln!(block, "open-domain-bdd json_bytes={}", encoded.len());
    let _ = writeln!(block, "{json}");
    let _ = writeln!(block, "end");
    Some(block)
}

pub(super) fn network_design_infeasibility_block(
    certificate: &NetworkDesignInfeasibilityCertificate,
) -> Option<String> {
    let (kind, encoded) = match crate::network_design_route::infeasibility_refutation(certificate) {
        crate::network_design_route::NetworkDesignPbRefutationRef::SingleRow(proof) => (
            "single-row",
            encode_single_row_dp_infeasibility_certificate_json(proof).ok()?,
        ),
        crate::network_design_route::NetworkDesignPbRefutationRef::MultiRow(proof) => (
            "multi-row",
            encode_multi_row_bdd_infeasibility_certificate_json(proof).ok()?,
        ),
    };
    let json = std::str::from_utf8(&encoded).ok()?;
    let mut block = String::new();
    let _ = writeln!(
        block,
        "network-design-infeasibility kind={kind} json_bytes={}",
        encoded.len()
    );
    let _ = writeln!(block, "{json}");
    let _ = writeln!(block, "end");
    Some(block)
}

pub(super) fn network_design_optimality_block(
    certificate: &NetworkDesignOptimalityCertificate,
) -> Option<String> {
    let (value, proof) = crate::network_design_route::optimality_parts(certificate);
    match proof {
        crate::network_design_route::NetworkDesignOptimalityProofRef::StrictBetter(proof) => {
            let encoded = encode_multi_row_bdd_infeasibility_certificate_json(proof).ok()?;
            let json = std::str::from_utf8(&encoded).ok()?;
            let mut block = String::new();
            let _ = writeln!(
                block,
                "network-design-optimality value={} frame=model json_bytes={}",
                fmt_rat(value),
                encoded.len()
            );
            let _ = writeln!(block, "{json}");
            let _ = writeln!(block, "end");
            Some(block)
        }
        crate::network_design_route::NetworkDesignOptimalityProofRef::PatternCount(proof) => {
            let width = proof.blocks.first()?.len();
            if proof.blocks.len() < 2
                || width == 0
                || proof.blocks.iter().any(|block| block.len() != width)
            {
                return None;
            }
            let mut block = String::new();
            let _ = writeln!(
                block,
                "network-design-optimality value={} frame=model kind=pattern-count \
                 pb_value={} blocks={} width={}",
                fmt_rat(value),
                proof.pb_value,
                proof.blocks.len(),
                width
            );
            for variables in &proof.blocks {
                block.push_str("block");
                for variable in variables {
                    let _ = write!(block, " {variable}");
                }
                block.push('\n');
            }
            let _ = writeln!(block, "end");
            Some(block)
        }
    }
}

pub(super) fn block_angular_optimality_block(
    certificate: &BlockAngularOptimalityCertificate,
) -> String {
    let (value, multipliers, minimizers) =
        crate::block_angular_route::certificate_parts(certificate);
    let mut block = String::new();
    let _ = writeln!(
        block,
        "block-angular-optimality value={} frame=model masters={} blocks={}",
        fmt_rat(value),
        multipliers.len(),
        minimizers.len()
    );
    for (row, multiplier) in multipliers {
        let _ = writeln!(block, "master {row} {}", fmt_rat(multiplier));
    }
    for pattern in minimizers {
        if let Some((amounts, exits)) = crate::block_angular_route::source_pattern_parts(pattern) {
            let _ = write!(block, "source width={}", amounts.len());
            for amount in amounts {
                let _ = write!(block, " {amount}");
            }
            block.push_str(" exits");
            for exit in exits {
                let _ = write!(block, " {exit}");
            }
            block.push('\n');
        } else if let Some(exit) = crate::block_angular_route::initial_pattern_exit(pattern) {
            let _ = writeln!(block, "initial exit={exit}");
        }
    }
    let _ = writeln!(block, "end");
    block
}

pub(super) fn single_machine_scheduling_optimality_block(
    certificate: &SingleMachineSchedulingOptimalityCertificate,
) -> String {
    let (value, sequence) = crate::scheduling_route::optimality_parts(certificate);
    let mut block = String::new();
    let _ = writeln!(
        block,
        "single-machine-scheduling-optimality value={} frame=model jobs={}",
        fmt_rat(value),
        sequence.len()
    );
    block.push_str("sequence");
    for column in sequence {
        let _ = write!(block, " {column}");
    }
    block.push('\n');
    let _ = writeln!(block, "end");
    block
}

pub(super) fn hybrid_pb_lp_block(
    certificate: &HybridPbLpInfeasibilityCertificate,
) -> Option<String> {
    hybrid_pb_lp_named_block("hybrid-pb-lp", certificate)
}

pub(super) fn open_domain_hybrid_pb_lp_block(
    certificate: &HybridPbLpInfeasibilityCertificate,
) -> Option<String> {
    hybrid_pb_lp_named_block("open-domain-hybrid-pb-lp", certificate)
}

pub(super) fn hybrid_pb_lp_named_block(
    label: &str,
    certificate: &HybridPbLpInfeasibilityCertificate,
) -> Option<String> {
    let encoded = encode_hybrid_pb_lp_infeasibility_certificate_json(certificate).ok()?;
    let json = std::str::from_utf8(&encoded).ok()?;
    let mut block = String::new();
    let _ = writeln!(block, "{label} json_bytes={}", encoded.len());
    let _ = writeln!(block, "{json}");
    let _ = writeln!(block, "end");
    Some(block)
}

pub(super) fn hybrid_integer_lift_block(
    certificate: &HybridIntegerLiftInfeasibilityCertificate,
) -> Option<String> {
    hybrid_integer_lift_named_block("hybrid-integer-lift", certificate)
}

pub(super) fn open_domain_hybrid_integer_lift_block(
    certificate: &HybridIntegerLiftInfeasibilityCertificate,
) -> Option<String> {
    hybrid_integer_lift_named_block("open-domain-hybrid-integer-lift", certificate)
}

pub(super) fn hybrid_integer_lift_named_block(
    label: &str,
    certificate: &HybridIntegerLiftInfeasibilityCertificate,
) -> Option<String> {
    let encoded = encode_hybrid_integer_lift_infeasibility_certificate_json(certificate).ok()?;
    let json = std::str::from_utf8(&encoded).ok()?;
    let mut block = String::new();
    let _ = writeln!(block, "{label} json_bytes={}", encoded.len());
    let _ = writeln!(block, "{json}");
    let _ = writeln!(block, "end");
    Some(block)
}

pub(super) fn replay_block(rc: &ReplayClaim) -> String {
    let mut s = String::new();
    let _ = writeln!(s, "replay {}", sanitize(&rc.claim));
    let _ = writeln!(s, "device {}", sanitize(&rc.device));
    let _ = writeln!(s, "method {}", sanitize(&rc.method));
    let _ = writeln!(s, "arithmetic {}", sanitize(&rc.arithmetic));
    let _ = writeln!(
        s,
        "nodes-visited {}",
        rc.nodes_visited
            .map_or_else(|| "unknown".into(), |n| n.to_string())
    );
    let _ = writeln!(s, "node-budget {}", rc.node_budget);
    let _ = writeln!(s, "outcome {}", sanitize(&rc.outcome));
    for n in &rc.nondeterminism {
        let _ = writeln!(s, "nondeterminism {}", sanitize(n));
    }
    let _ = writeln!(s, "reproduce {}", sanitize(&rc.reproduce));
    let _ = writeln!(s, "tcb {}", sanitize(&rc.tcb));
    let _ = writeln!(s, "end");
    s
}

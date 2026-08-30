// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

pub(super) fn parse_core_block(
    lines: &[&str],
    line: &mut usize,
    state: &mut ParseState,
) -> Result<(), CertIoError> {
    match lines[*line].split_whitespace().next().unwrap_or_default() {
        "witness" => {
            let (values, next) = parse_witness(lines, *line)?;
            state.certificate.witness = Some(values);
            *line = next;
        }
        "farkas" => {
            let (multipliers, next) = parse_mults(lines, *line + 1, "end")?;
            state.certificate.farkas = Some(FarkasCertificate { multipliers });
            *line = next;
        }
        "optcert" => {
            let (certificate, trivial, next) = parse_optcert(lines, *line)?;
            state.certificate.optcert = Some(certificate);
            state.certificate.optcert_trivial = trivial;
            *line = next;
        }
        "rootdual" => {
            if state.certificate.root_dual_bound.is_some() {
                return Err(malformed(*line, "duplicate rootdual block"));
            }
            let (record, next) = parse_root_dual(lines, *line)?;
            state.certificate.root_dual_bound = Some(record);
            *line = next;
        }
        "tree" => {
            let (root, next) = parse_tree(lines, *line + 1)?;
            state.certificate.tree = Some(MilpInfeasibilityCertificate { root });
            *line = next;
        }
        "opttree" => {
            let (root, next) = parse_opt_tree(lines, *line + 1)?;
            state.certificate.opt_tree = Some(root);
            *line = next;
        }
        "affine-aggregation" => parse_unique_affine(lines, line, &mut state.certificate)?,
        "parity-gf2" => parse_unique_parity(lines, line, &mut state.certificate)?,
        "sat-relu-rup" => parse_unique_sat_relu(lines, line, &mut state.certificate)?,
        _ => return Err(malformed(*line, "unknown core proof block")),
    }
    Ok(())
}

pub(super) fn parse_unique_affine(
    lines: &[&str],
    line: &mut usize,
    certificate: &mut Certificate,
) -> Result<(), CertIoError> {
    if certificate.affine_aggregation.is_some() {
        return Err(malformed(*line, "duplicate affine-aggregation block"));
    }
    let (proof, next) = parse_affine_aggregation(lines, *line)?;
    certificate.affine_aggregation = Some(proof);
    *line = next;
    Ok(())
}

pub(super) fn parse_unique_parity(
    lines: &[&str],
    line: &mut usize,
    certificate: &mut Certificate,
) -> Result<(), CertIoError> {
    if certificate.parity_infeasibility.is_some() {
        return Err(malformed(*line, "duplicate parity-gf2 block"));
    }
    let (proof, next) = parse_parity_infeasibility(lines, *line)?;
    certificate.parity_infeasibility = Some(proof);
    *line = next;
    Ok(())
}

pub(super) fn parse_unique_sat_relu(
    lines: &[&str],
    line: &mut usize,
    certificate: &mut Certificate,
) -> Result<(), CertIoError> {
    if certificate.sat_relu_infeasibility.is_some() {
        return Err(malformed(*line, "duplicate sat-relu-rup block"));
    }
    let (proof, next) = parse_sat_relu_rup(lines, *line)?;
    certificate.sat_relu_infeasibility = Some(proof);
    *line = next;
    Ok(())
}

pub(super) fn parse_route_block(
    lines: &[&str],
    fields: &[&str],
    line: &mut usize,
    state: &mut ParseState,
) -> Result<(), CertIoError> {
    match fields[0] {
        "network-design-infeasibility" => {
            parse_network_infeasibility(lines, fields, line, &mut state.certificate)
        }
        "network-design-optimality" => {
            parse_network_optimality(lines, fields, line, &mut state.certificate)
        }
        "block-angular-optimality" => {
            if state.certificate.block_angular_optimality.is_some() {
                return Err(malformed(*line, "duplicate block-angular-optimality block"));
            }
            let (proof, next) = parse_block_angular_optimality(lines, *line)?;
            state.certificate.block_angular_optimality = Some(proof);
            *line = next;
            Ok(())
        }
        "single-machine-scheduling-optimality" => {
            if state
                .certificate
                .single_machine_scheduling_optimality
                .is_some()
            {
                return Err(malformed(
                    *line,
                    "duplicate single-machine-scheduling-optimality block",
                ));
            }
            let (proof, next) = parse_single_machine_scheduling_optimality(lines, *line)?;
            state.certificate.single_machine_scheduling_optimality = Some(proof);
            *line = next;
            Ok(())
        }
        _ => Err(malformed(*line, "unknown route proof block")),
    }
}

pub(super) fn parse_network_infeasibility(
    lines: &[&str],
    fields: &[&str],
    line: &mut usize,
    certificate: &mut Certificate,
) -> Result<(), CertIoError> {
    if certificate.network_design_infeasibility.is_some() {
        return Err(malformed(
            *line,
            "duplicate network-design-infeasibility block",
        ));
    }
    let kind = kv(fields, "kind")
        .ok_or_else(|| malformed(*line, "network-design-infeasibility has no kind="))?;
    let (json, next) = parse_json_body(lines, *line, "network-design-infeasibility")?;
    let proof = match kind {
        "single-row" => {
            let proof = decode_single_row_dp_infeasibility_certificate_json(json.as_bytes())
                .map_err(|error| CertIoError::Malformed {
                    line: *line + 2,
                    msg: format!("network-design single-row JSON rejected: {error}"),
                })?;
            crate::network_design_route::infeasibility_from_single_row(proof)
        }
        "multi-row" => {
            let proof = decode_multi_row_bdd_infeasibility_certificate_json(json.as_bytes())
                .map_err(|error| CertIoError::Malformed {
                    line: *line + 2,
                    msg: format!("network-design multi-row JSON rejected: {error}"),
                })?;
            crate::network_design_route::infeasibility_from_multi_row(proof)
        }
        _ => return Err(malformed(*line, "unknown network-design refutation kind")),
    };
    certificate.network_design_infeasibility = Some(proof);
    *line = next;
    Ok(())
}

pub(super) fn parse_network_optimality(
    lines: &[&str],
    fields: &[&str],
    line: &mut usize,
    certificate: &mut Certificate,
) -> Result<(), CertIoError> {
    if certificate.network_design_optimality.is_some() {
        return Err(malformed(
            *line,
            "duplicate network-design-optimality block",
        ));
    }
    if kv(fields, "frame") != Some("model") {
        return Err(malformed(
            *line,
            "network-design optimality value must use frame=model",
        ));
    }
    let value = kv(fields, "value")
        .and_then(parse_rat)
        .ok_or_else(|| malformed(*line, "network-design-optimality has invalid value="))?;
    let (proof, next) = match kv(fields, "kind").unwrap_or("multi-row") {
        "multi-row" => {
            let (json, next) = parse_json_body(lines, *line, "network-design-optimality")?;
            let proof = decode_multi_row_bdd_infeasibility_certificate_json(json.as_bytes())
                .map_err(|error| CertIoError::Malformed {
                    line: *line + 2,
                    msg: format!("network-design optimality JSON rejected: {error}"),
                })?;
            (
                crate::network_design_route::optimality_from_strict_better(value, proof),
                next,
            )
        }
        "pattern-count" => {
            let (proof, next) = parse_network_design_pattern_count(lines, *line)?;
            (
                crate::network_design_route::optimality_from_pattern_count(value, proof),
                next,
            )
        }
        _ => {
            return Err(malformed(
                *line,
                "unknown network-design optimality proof kind",
            ))
        }
    };
    certificate.network_design_optimality = Some(proof);
    *line = next;
    Ok(())
}

pub(super) fn parse_encoded_block(
    lines: &[&str],
    line: &mut usize,
    state: &mut ParseState,
) -> Result<(), CertIoError> {
    let name = lines[*line].split_whitespace().next().unwrap_or_default();
    match name {
        "single-row-dp" => {
            let (proof, next) = parse_single_row_dp(lines, *line)?;
            state.certificate.single_row_dp = Some(proof);
            *line = next;
        }
        "multi-row-bdd" => {
            let (proof, next) = parse_multi_row_bdd(lines, *line)?;
            state.certificate.multi_row_bdd = Some(proof);
            *line = next;
        }
        "open-domain-dp" => {
            let (proof, next) = parse_single_row_dp(lines, *line)?;
            state.certificate.open_domain_dp = Some(proof);
            *line = next;
        }
        "open-domain-bdd" => {
            let (proof, next) = parse_multi_row_bdd(lines, *line)?;
            state.certificate.open_domain_bdd = Some(proof);
            *line = next;
        }
        "open-domain-hybrid-pb-lp" => parse_open_hybrid_pb(lines, line, state)?,
        "open-domain-hybrid-integer-lift" => parse_open_hybrid_lift(lines, line, state)?,
        "hybrid-pb-lp" => {
            if state.certificate.hybrid_pb_lp.is_some() {
                return Err(malformed(*line, "duplicate hybrid-pb-lp block"));
            }
            let (proof, next) = parse_hybrid_pb_lp(lines, *line)?;
            state.certificate.hybrid_pb_lp = Some(proof);
            *line = next;
        }
        "hybrid-integer-lift" => {
            if state.certificate.hybrid_integer_lift.is_some() {
                return Err(malformed(*line, "duplicate hybrid-integer-lift block"));
            }
            let (proof, next) = parse_hybrid_integer_lift(lines, *line)?;
            state.certificate.hybrid_integer_lift = Some(proof);
            *line = next;
        }
        _ => return Err(malformed(*line, "unknown encoded proof block")),
    }
    Ok(())
}

pub(super) fn parse_open_hybrid_pb(
    lines: &[&str],
    line: &mut usize,
    state: &mut ParseState,
) -> Result<(), CertIoError> {
    if state.certificate.open_domain_hybrid_pb_lp.is_some() {
        return Err(malformed(*line, "duplicate open-domain-hybrid-pb-lp block"));
    }
    let (json, next) = parse_json_body(lines, *line, "open-domain-hybrid-pb-lp")?;
    let proof =
        decode_hybrid_pb_lp_infeasibility_certificate_json(json.as_bytes()).map_err(|error| {
            CertIoError::Malformed {
                line: *line + 2,
                msg: format!("open-domain-hybrid-pb-lp JSON rejected: {error}"),
            }
        })?;
    state.certificate.open_domain_hybrid_pb_lp = Some(proof);
    *line = next;
    Ok(())
}

pub(super) fn parse_open_hybrid_lift(
    lines: &[&str],
    line: &mut usize,
    state: &mut ParseState,
) -> Result<(), CertIoError> {
    if state.certificate.open_domain_hybrid_integer_lift.is_some() {
        return Err(malformed(
            *line,
            "duplicate open-domain-hybrid-integer-lift block",
        ));
    }
    let (json, next) = parse_json_body(lines, *line, "open-domain-hybrid-integer-lift")?;
    let proof = decode_hybrid_integer_lift_infeasibility_certificate_json(json.as_bytes())
        .map_err(|error| CertIoError::Malformed {
            line: *line + 2,
            msg: format!("open-domain-hybrid-integer-lift JSON rejected: {error}"),
        })?;
    state.certificate.open_domain_hybrid_integer_lift = Some(proof);
    *line = next;
    Ok(())
}

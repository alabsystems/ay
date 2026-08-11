// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Certified VeriPB routes for exact Koops PB-COMP rows.

use std::io::Write;

use super::{ConstraintId, ProofStep, Result, VeriPbWriter};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct KoopsIdentityComplementRedCapacityParams {
    pub label: &'static str,
    pub factor_count: u32,
    pub block_width: u32,
    pub cover_rows: u64,
    pub red_rhs: u32,
}

impl KoopsIdentityComplementRedCapacityParams {
    pub fn expected_final_id(self, input_constraints: u64) -> u64 {
        input_constraints
            + u64::from(self.factor_count)
            + u64::from(self.factor_count.saturating_sub(1))
            + self.cover_rows.saturating_sub(1)
            + 1
    }
}

pub const KOOPS_MAT98_IDENTITY_COMPLEMENT_RED_CAPACITY_PARAMS:
    KoopsIdentityComplementRedCapacityParams = KoopsIdentityComplementRedCapacityParams {
    label: "koops_mat98_identity_complement",
    factor_count: 8,
    block_width: 9,
    cover_rows: 9,
    red_rhs: 8,
};

pub const KOOPS_MAT10_9_IDENTITY_COMPLEMENT_RED_CAPACITY_PARAMS:
    KoopsIdentityComplementRedCapacityParams = KoopsIdentityComplementRedCapacityParams {
    label: "koops_mat10_9_identity_complement",
    factor_count: 9,
    block_width: 10,
    cover_rows: 10,
    red_rhs: 9,
};

pub const KOOPS_MAT12_11_IDENTITY_COMPLEMENT_RED_CAPACITY_PARAMS:
    KoopsIdentityComplementRedCapacityParams = KoopsIdentityComplementRedCapacityParams {
    label: "koops_mat12_11_identity_complement",
    factor_count: 11,
    block_width: 12,
    cover_rows: 12,
    red_rhs: 11,
};

pub const KOOPS_MAT16_15_IDENTITY_COMPLEMENT_RED_CAPACITY_PARAMS:
    KoopsIdentityComplementRedCapacityParams = KoopsIdentityComplementRedCapacityParams {
    label: "koops_mat16_15_identity_complement",
    factor_count: 17,
    block_width: 18,
    cover_rows: 18,
    red_rhs: 17,
};

pub const KOOPS_MAT20_19_IDENTITY_COMPLEMENT_RED_CAPACITY_PARAMS:
    KoopsIdentityComplementRedCapacityParams = KoopsIdentityComplementRedCapacityParams {
    label: "koops_mat20_19_identity_complement",
    factor_count: 19,
    block_width: 20,
    cover_rows: 20,
    red_rhs: 19,
};

/// Emits the checker-accepted RED-capacity proof for the exact PB25
/// Koops identity-complement boundary rows.
///
/// This proof relies on the first imported cover rows and RED capacity rows
/// over the diagonal variable blocks. The caller is responsible for exact
/// fingerprint gating before using this certified shortcut.
pub fn emit_koops_identity_complement_red_capacity_proof<W: Write>(
    writer: &mut VeriPbWriter<W>,
    params: KoopsIdentityComplementRedCapacityParams,
) -> Result<ConstraintId> {
    debug_assert!(params.factor_count > 0);
    debug_assert!(params.block_width > 0);
    debug_assert!(params.cover_rows > 0);

    let mut red_ids = Vec::with_capacity(params.factor_count as usize);
    for block in 0..params.factor_count {
        let first_var = block * params.block_width + 1;
        let last_var = first_var + params.block_width - 1;
        let constraint = positive_unit_sum_constraint(first_var, last_var, params.red_rhs);
        let witness = force_true_witness(first_var, last_var);
        red_ids.push(writer.log_step(ProofStep::Red(constraint, witness))?);
    }

    let red_sum_id = add_ids_left_associative(writer, &red_ids)?;
    let cover_ids = (1..=params.cover_rows)
        .map(ConstraintId::from_raw)
        .collect::<Vec<_>>();
    let cover_sum_id = add_ids_left_associative(writer, &cover_ids)?;
    let contradiction_id = writer.log_step(ProofStep::Addition(red_sum_id, cover_sum_id))?;
    writer.conclude_unsat(contradiction_id)?;
    Ok(contradiction_id)
}

/// Emits the checker-accepted RED-capacity proof for the exact PB25
/// `normalized-mat12_11_identity_complement` Koops boundary row.
pub fn emit_koops_mat12_11_identity_complement_red_capacity_proof<W: Write>(
    writer: &mut VeriPbWriter<W>,
) -> Result<ConstraintId> {
    emit_koops_identity_complement_red_capacity_proof(
        writer,
        KOOPS_MAT12_11_IDENTITY_COMPLEMENT_RED_CAPACITY_PARAMS,
    )
}

fn add_ids_left_associative<W: Write>(
    writer: &mut VeriPbWriter<W>,
    ids: &[ConstraintId],
) -> Result<ConstraintId> {
    debug_assert!(!ids.is_empty(), "at least one proof ID is required");
    let mut iter = ids.iter().copied();
    let mut sum = iter.next().expect("non-empty ID list");
    for next in iter {
        sum = writer.log_step(ProofStep::Addition(sum, next))?;
    }
    Ok(sum)
}

fn positive_unit_sum_constraint(first_var: u32, last_var: u32, rhs: u32) -> String {
    let terms = (first_var..=last_var)
        .map(|var| format!("+1 x{var}"))
        .collect::<Vec<_>>()
        .join(" ");
    format!("{terms} >= {rhs}")
}

fn force_true_witness(first_var: u32, last_var: u32) -> String {
    let substitutions = (first_var..=last_var)
        .map(|var| format!("x{var} -> 1"))
        .collect::<Vec<_>>()
        .join(" ");
    format!("{substitutions} ;")
}

#[cfg(test)]
mod tests {
    use super::{
        emit_koops_identity_complement_red_capacity_proof,
        emit_koops_mat12_11_identity_complement_red_capacity_proof,
        KOOPS_MAT10_9_IDENTITY_COMPLEMENT_RED_CAPACITY_PARAMS,
        KOOPS_MAT12_11_IDENTITY_COMPLEMENT_RED_CAPACITY_PARAMS,
        KOOPS_MAT16_15_IDENTITY_COMPLEMENT_RED_CAPACITY_PARAMS,
        KOOPS_MAT20_19_IDENTITY_COMPLEMENT_RED_CAPACITY_PARAMS,
        KOOPS_MAT98_IDENTITY_COMPLEMENT_RED_CAPACITY_PARAMS,
    };
    use crate::{proof::VeriPbWriter, ConstraintId};

    #[test]
    fn test_koops_mat12_11_red_capacity_proof_matches_checked_fixture() {
        let mut writer = VeriPbWriter::new(Vec::new(), 50_832).expect("header writes to memory");
        let final_id = emit_koops_mat12_11_identity_complement_red_capacity_proof(&mut writer)
            .expect("exact proof emits");

        assert_eq!(
            final_id,
            ConstraintId::new(50_865).expect("final contradiction ID is non-zero")
        );
        assert_eq!(
            String::from_utf8(writer.writer).expect("proof output is utf-8"),
            include_str!(
                "../../../ay-pb/tests/instances/koops_mat12_11_identity_complement_red_capacity.pbp"
            ),
        );
    }

    #[test]
    fn test_koops_identity_complement_red_capacity_final_ids() {
        let cases = [
            (
                KOOPS_MAT98_IDENTITY_COMPLEMENT_RED_CAPACITY_PARAMS,
                11_529,
                11_553,
            ),
            (
                KOOPS_MAT10_9_IDENTITY_COMPLEMENT_RED_CAPACITY_PARAMS,
                19_855,
                19_882,
            ),
            (
                KOOPS_MAT12_11_IDENTITY_COMPLEMENT_RED_CAPACITY_PARAMS,
                50_832,
                50_865,
            ),
            (
                KOOPS_MAT16_15_IDENTITY_COMPLEMENT_RED_CAPACITY_PARAMS,
                408_375,
                408_426,
            ),
            (
                KOOPS_MAT20_19_IDENTITY_COMPLEMENT_RED_CAPACITY_PARAMS,
                700_360,
                700_417,
            ),
        ];

        for (params, input_constraints, expected_final_id) in cases {
            let mut writer =
                VeriPbWriter::new(Vec::new(), input_constraints).expect("header writes to memory");
            let final_id = emit_koops_identity_complement_red_capacity_proof(&mut writer, params)
                .unwrap_or_else(|error| panic!("{} proof emits: {error}", params.label));

            assert_eq!(
                params.expected_final_id(input_constraints),
                expected_final_id,
                "{} expected ID formula",
                params.label
            );
            assert_eq!(
                final_id,
                ConstraintId::new(expected_final_id)
                    .unwrap_or_else(|| panic!("{} final ID is non-zero", params.label)),
                "{} final contradiction ID",
                params.label
            );
            let proof = String::from_utf8(writer.writer).expect("proof output is utf-8");
            assert!(
                proof.contains(&format!("conclusion UNSAT : {expected_final_id};")),
                "{} proof should conclude on the expected contradiction ID: {proof}",
                params.label
            );
        }
    }
}

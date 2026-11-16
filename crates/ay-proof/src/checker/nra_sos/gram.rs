// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact Schur-complement PSD validation. A zero pivot is admissible only
//! when its entire remaining row/column vanishes; no regularization is used.

use super::*;
use rational::{binary, Operation};
use std::mem::size_of;

pub(super) fn decode_and_check(
    raw: &[Vec<NraSosRational>],
    meter: &mut WorkMeter<'_>,
) -> Result<Vec<Vec<BigRational>>, String> {
    let n = raw.len();
    if n > NraSosCertificate::MAX_BASIS || raw.iter().any(|row| row.len() != n) {
        return Err("invalid Gram shape".to_string());
    }
    meter.charge_private_allocation(
        n * n,
        n * n * size_of::<BigRational>() + n * size_of::<Vec<BigRational>>(),
    )?;
    let mut matrix = Vec::new();
    matrix
        .try_reserve_exact(n)
        .map_err(|_| WORK_METER_RESOURCE_LIMIT.to_string())?;
    for row in raw {
        let mut decoded = Vec::new();
        decoded
            .try_reserve_exact(n)
            .map_err(|_| WORK_METER_RESOURCE_LIMIT.to_string())?;
        for coefficient in row {
            decoded.push(rational::decode(coefficient, meter)?);
        }
        matrix.push(decoded);
    }
    for row in 0..n {
        for column in 0..row {
            meter.charge_ops(1)?;
            if matrix[row][column] != matrix[column][row] {
                return Err("asymmetric Gram matrix".to_string());
            }
        }
    }
    check_psd(&matrix, meter)?;
    Ok(matrix)
}

#[allow(clippy::needless_range_loop)] // Indices identify exact matrix pivot/row/column roles.
fn check_psd(matrix: &[Vec<BigRational>], meter: &mut WorkMeter<'_>) -> Result<(), String> {
    let n = matrix.len();
    meter.charge_private_allocation(
        n * n,
        n * n * size_of::<BigRational>() + size_of_val(matrix),
    )?;
    let mut work = Vec::new();
    work.try_reserve_exact(n)
        .map_err(|_| WORK_METER_RESOURCE_LIMIT.to_string())?;
    for row in matrix {
        let mut copied = Vec::new();
        copied
            .try_reserve_exact(n)
            .map_err(|_| WORK_METER_RESOURCE_LIMIT.to_string())?;
        for coefficient in row {
            copied.push(rational::copy(coefficient, meter)?);
        }
        work.push(copied);
    }
    for pivot_index in 0..n {
        let pivot = rational::copy(&work[pivot_index][pivot_index], meter)?;
        if pivot.is_negative() {
            return Err("Gram matrix is not PSD".to_string());
        }
        if pivot.is_zero() {
            for index in pivot_index + 1..n {
                meter.charge_ops(1)?;
                if !work[index][pivot_index].is_zero() || !work[pivot_index][index].is_zero() {
                    return Err("zero Gram pivot has a nonzero tail".to_string());
                }
            }
            continue;
        }
        for row in pivot_index + 1..n {
            meter.poll()?;
            if work[row][pivot_index].is_zero() {
                continue;
            }
            let factor = binary(&work[row][pivot_index], &pivot, Operation::Divide, meter)?;
            for column in pivot_index + 1..n {
                let product = binary(
                    &factor,
                    &work[pivot_index][column],
                    Operation::Multiply,
                    meter,
                )?;
                work[row][column] =
                    binary(&work[row][column], &product, Operation::Subtract, meter)?;
            }
        }
    }
    meter.poll()
}

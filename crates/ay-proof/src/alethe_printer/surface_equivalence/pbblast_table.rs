// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Carcara's pseudo-Boolean blasting table for the unsigned comparisons the
//! operand-swap reversal relates (moved verbatim out of the parent module).

/// `(minuend is the first operand, threshold)` of carcara's pseudo-Boolean
/// blasting for one unsigned comparison, read off
/// `checker/rules/pb_blasting.rs`: `pbblast_bvuge` concludes
/// `(= (bvuge x y) (>= (- Sx Sy) 0))`, `pbblast_bvule` `(>= (- Sy Sx) 0)`,
/// `pbblast_bvugt` `(>= (- Sx Sy) 1)` and `pbblast_bvult` `(>= (- Sy Sx) 1)`.
pub(super) fn unsigned_comparison_pbblast(operator: &str) -> Option<(bool, u8)> {
    match operator {
        "bvuge" => Some((true, 0)),
        "bvule" => Some((false, 0)),
        "bvugt" => Some((true, 1)),
        "bvult" => Some((false, 1)),
        _ => None,
    }
}

/// The `pbblast_*` step concluding `(= comparison blasted)`. Each rule name
/// is spelled literally, so the wire-rule inventory reads it off this table.
pub(super) fn unsigned_comparison_pbblast_step(
    id: &str,
    operator: &str,
    comparison: &str,
    blasted: &str,
) -> Option<String> {
    let conclusion = format!("(cl (= {comparison} {blasted}))");
    Some(match operator {
        "bvuge" => format!("(step {id} {conclusion} :rule pbblast_bvuge)"),
        "bvule" => format!("(step {id} {conclusion} :rule pbblast_bvule)"),
        "bvugt" => format!("(step {id} {conclusion} :rule pbblast_bvugt)"),
        "bvult" => format!("(step {id} {conclusion} :rule pbblast_bvult)"),
        _ => return None,
    })
}

/// The operator that states `(operator x y)` with its operands swapped.
pub(super) fn swapped_unsigned_comparison(operator: &str) -> Option<&'static str> {
    match operator {
        "bvuge" => Some("bvule"),
        "bvule" => Some("bvuge"),
        "bvugt" => Some("bvult"),
        "bvult" => Some("bvugt"),
        _ => None,
    }
}

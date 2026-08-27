// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Observational ICP diagnostics carried by the public miscellaneous CLI flags.
//!
//! Nothing in this module may change a candidate, box, budget, or verdict.

use std::fmt;

use super::*;

pub(super) fn trace_enabled() -> bool {
    ay_core::misc_cli_flags().nra_diag
}

/// Keep stderr emission in one place so diagnostics remain an explicit edge.
pub(super) fn emit(arguments: fmt::Arguments<'_>) {
    eprintln!("{arguments}");
}

/// Externally supplied rational witness, parsed once from `--nra-witness`.
pub(super) fn witness() -> &'static [(String, BigRational)] {
    static WITNESS: std::sync::OnceLock<Vec<(String, BigRational)>> = std::sync::OnceLock::new();
    WITNESS
        .get_or_init(|| {
            let Some(raw) = ay_core::misc_cli_flags().nra_witness.clone() else {
                return Vec::new();
            };
            raw.split([',', ' ', '\t', '\n'])
                .filter(|item| !item.is_empty())
                .filter_map(parse_assignment)
                .collect()
        })
        .as_slice()
}

fn parse_assignment(item: &str) -> Option<(String, BigRational)> {
    let (name, value) = item.split_once('=')?;
    let value = value.trim();
    let rational = match value.split_once('/') {
        Some((numerator, denominator)) => {
            let numerator = numerator.trim().parse::<BigInt>().ok()?;
            let denominator = denominator.trim().parse::<BigInt>().ok()?;
            (!denominator.is_zero()).then(|| BigRational::new(numerator, denominator))?
        }
        None => BigRational::from_integer(value.parse::<BigInt>().ok()?),
    };
    Some((name.trim().to_string(), rational))
}

pub(super) fn render_box(solver: &NraSolver<'_>, vars: &[TermId], bx: &VarBox) -> String {
    let mut rendered = String::new();
    for &var in vars {
        let name = match solver.terms.get(var) {
            ay_core::TermData::Var(name, _) => name.clone(),
            other => format!("{other:?}"),
        };
        let endpoint = |value: &Endpoint| match value {
            Endpoint::Finite(value, _) => value.to_string(),
            Endpoint::NegInf => "-inf".to_string(),
            Endpoint::PosInf => "+inf".to_string(),
        };
        match bx.get(&var) {
            Some(interval) => rendered.push_str(&format!(
                "{name}=[{},{}] ",
                endpoint(&interval.lo),
                endpoint(&interval.hi)
            )),
            None => rendered.push_str(&format!("{name}=<none> ")),
        }
    }
    rendered
}

/// Report whether the supplied witness survived this call's bounds and
/// contraction. This is observational: the witness never enters search state.
pub(super) fn report_witness(
    solver: &NraSolver<'_>,
    constraints: &[MultiConstraint],
    vars: &[TermId],
    pre: &VarBox,
    post: &VarBox,
    refuted: bool,
    coverage: ParseCoverage,
) {
    let supplied = witness();
    let mut model = Vec::new();
    let mut uncovered = 0usize;
    for &var in vars {
        let name = match solver.terms.get(var) {
            ay_core::TermData::Var(name, _) => name.clone(),
            _ => String::new(),
        };
        match supplied
            .iter()
            .find(|entry| entry.0.as_str() == name.as_str())
        {
            Some((_, value)) => model.push((var, value.clone())),
            None => uncovered += 1,
        }
    }
    if uncovered > 0 {
        emit(format_args!(
            "NRA-WIT skip uncovered={uncovered}/{}",
            vars.len()
        ));
        return;
    }

    let point_box: VarBox = model
        .iter()
        .map(|(var, value)| (*var, Interval::point(value.clone())))
        .collect();
    let sat_constraints = constraints.iter().all(|constraint| {
        eval_poly_interval(&constraint.poly, &point_box)
            .map(|interval| !constraint_is_infeasible(constraint.rel, &interval))
            .unwrap_or(false)
    });
    let all_parsed = coverage.allows_sat();
    let sat_atoms = all_parsed && solver.verify_model(&model);
    let membership = |bx: &VarBox| -> (usize, String) {
        let mut outside = 0usize;
        let mut detail = String::new();
        for (var, value) in &model {
            if bx.get(var).is_some_and(|iv| interval_contains(iv, value)) {
                continue;
            }
            outside += 1;
            detail.push_str(&format!(
                "[{value} OUT OF {}] ",
                render_box(solver, &[*var], bx)
            ));
        }
        (outside, detail)
    };
    let (pre_out, pre_detail) = membership(pre);
    let (post_out, post_detail) = membership(post);
    emit(format_args!(
        "NRA-WIT vars={} cons={} sat_cons={} sat_atoms={} all_parsed={} refuted={} \
         pre_out={}/{} post_out={}/{} PRE {}POST {}",
        vars.len(),
        constraints.len(),
        u8::from(sat_constraints),
        u8::from(sat_atoms),
        u8::from(all_parsed),
        u8::from(refuted),
        pre_out,
        model.len(),
        post_out,
        model.len(),
        pre_detail,
        post_detail
    ));
}

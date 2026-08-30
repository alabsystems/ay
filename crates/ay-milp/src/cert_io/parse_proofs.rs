// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum ProofParseMode {
    General,
    Affine,
}

pub(super) fn parse_proof_rat(token: &str, mode: ProofParseMode) -> Option<BigRational> {
    match mode {
        ProofParseMode::General => parse_rat(token),
        ProofParseMode::Affine => parse_affine_rat(token),
    }
}

pub(super) fn parse_mults(
    lines: &[&str],
    start: usize,
    terminator: &str,
) -> Result<(Vec<Multiplier>, usize), CertIoError> {
    parse_mults_mode(lines, start, terminator, ProofParseMode::General)
}

pub(super) fn parse_mults_mode(
    lines: &[&str],
    start: usize,
    terminator: &str,
    mode: ProofParseMode,
) -> Result<(Vec<Multiplier>, usize), CertIoError> {
    let mut mults = Vec::new();
    let mut i = start;
    while i < lines.len() {
        let l = lines[i].trim();
        if l == terminator {
            return Ok((mults, i + 1));
        }
        let f: Vec<&str> = l.split_whitespace().collect();
        if f.len() != 5 || f[0] != "mult" {
            return Err(CertIoError::Malformed {
                line: i + 1,
                msg: format!("malformed multiplier record `{l}`"),
            });
        }
        let idx: u32 = f[2].parse().map_err(|_| CertIoError::Malformed {
            line: i + 1,
            msg: "malformed multiplier index".into(),
        })?;
        let side = parse_side(f[3]).ok_or(CertIoError::Malformed {
            line: i + 1,
            msg: "malformed multiplier side".into(),
        })?;
        let fact = match f[1] {
            "row" => FactRef::RowBound {
                row: Row(idx),
                side,
            },
            "col" => FactRef::ColBound {
                col: Col(idx),
                side,
            },
            _ => {
                return Err(CertIoError::Malformed {
                    line: i + 1,
                    msg: "multiplier names neither row nor col".into(),
                })
            }
        };
        if mode == ProofParseMode::Affine && mults.len() >= MAX_AFFINE_PROOF_MULTIPLIERS {
            return Err(CertIoError::Malformed {
                line: i + 1,
                msg: "affine multiplier count exceeds hard cap".into(),
            });
        }
        let coeff = parse_proof_rat(f[4], mode).ok_or(CertIoError::Malformed {
            line: i + 1,
            msg: "malformed multiplier coefficient".into(),
        })?;
        mults.push(Multiplier { fact, coeff });
        i += 1;
    }
    Err(CertIoError::Malformed {
        line: start,
        msg: format!("block not terminated by `{terminator}`"),
    })
}

/// Parse a `rootdual` block: an [`OptimalityCertificate`] used as a BOUND,
/// plus the residual the emitter recorded.
///
/// The `gap` field is parsed but NOT believed: [`check`] re-derives it from
/// `bound` and the verdict line and refuses a block whose two records disagree.
/// Parsing it here rather than skipping it is what makes that comparison
/// possible at all.
pub(super) fn parse_root_dual(
    lines: &[&str],
    start: usize,
) -> Result<(RootDualBoundRecord, usize), CertIoError> {
    let head: Vec<&str> = lines[start].split_whitespace().collect();
    let bad = |msg: &str| CertIoError::Malformed {
        line: start + 1,
        msg: msg.to_string(),
    };
    let sense = kv(&head, "sense")
        .and_then(parse_sense)
        .ok_or_else(|| bad("rootdual sense"))?;
    let bound = kv(&head, "bound")
        .and_then(parse_rat)
        .ok_or_else(|| bad("rootdual bound"))?;
    let gap = kv(&head, "gap")
        .and_then(parse_rat)
        .ok_or_else(|| bad("rootdual gap"))?;
    let (objective, i) = parse_objective_records(lines, start + 1)?;
    let (multipliers, next) = parse_mults(lines, i, "end")?;
    Ok((
        RootDualBoundRecord {
            certificate: OptimalityCertificate {
                sense,
                objective,
                bound,
                multipliers,
            },
            gap,
        },
        next,
    ))
}

/// The `obj <col> <coeff>` run shared by `optcert` and `rootdual`.
fn parse_objective_records(
    lines: &[&str],
    start: usize,
) -> Result<(Vec<(u32, BigRational)>, usize), CertIoError> {
    let mut objective = Vec::new();
    let mut i = start;
    while i < lines.len() {
        let l = lines[i].trim();
        let f: Vec<&str> = l.split_whitespace().collect();
        if f.first() != Some(&"obj") {
            break;
        }
        if f.len() != 3 {
            return Err(CertIoError::Malformed {
                line: i + 1,
                msg: "malformed obj record".into(),
            });
        }
        let c: u32 = f[1].parse().map_err(|_| CertIoError::Malformed {
            line: i + 1,
            msg: "malformed obj column".into(),
        })?;
        let a = parse_rat(f[2]).ok_or(CertIoError::Malformed {
            line: i + 1,
            msg: "malformed obj coefficient".into(),
        })?;
        objective.push((c, a));
        i += 1;
    }
    Ok((objective, i))
}

pub(super) fn parse_optcert(
    lines: &[&str],
    start: usize,
) -> Result<(OptimalityCertificate, bool, usize), CertIoError> {
    let head: Vec<&str> = lines[start].split_whitespace().collect();
    let bad = |msg: &str| CertIoError::Malformed {
        line: start + 1,
        msg: msg.to_string(),
    };
    let sense = kv(&head, "sense")
        .and_then(parse_sense)
        .ok_or_else(|| bad("optcert sense"))?;
    let bound = kv(&head, "bound")
        .and_then(parse_rat)
        .ok_or_else(|| bad("optcert bound"))?;
    let trivial = kv(&head, "trivial") == Some("1");
    let (objective, i) = parse_objective_records(lines, start + 1)?;
    let (multipliers, next) = parse_mults(lines, i, "end")?;
    Ok((
        OptimalityCertificate {
            sense,
            objective,
            bound,
            multipliers,
        },
        trivial,
        next,
    ))
}

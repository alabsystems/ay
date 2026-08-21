// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

pub(super) fn strip_sha(t: &str) -> Option<String> {
    let h = t.strip_prefix("sha256:")?;
    if h.len() == 64 && h.bytes().all(|b| b.is_ascii_hexdigit()) {
        Some(h.to_string())
    } else {
        None
    }
}

pub(super) fn kv<'a>(f: &[&'a str], key: &str) -> Option<&'a str> {
    f.iter()
        .find_map(|t| t.split_once('=').filter(|(k, _)| *k == key).map(|(_, v)| v))
}

pub(super) fn kv_usize(f: &[&str], key: &str) -> Option<usize> {
    kv(f, key).and_then(|v| v.parse().ok())
}

pub(super) fn parse_parity_infeasibility(
    lines: &[&str],
    start: usize,
) -> Result<(ParityInfeasibilityCertificate, usize), CertIoError> {
    let head: Vec<&str> = lines[start].split_whitespace().collect();
    let expected_rows = kv_usize(&head, "rows").ok_or(CertIoError::Malformed {
        line: start + 1,
        msg: "parity-gf2 has no rows=".into(),
    })?;
    let mut rows = Vec::with_capacity(expected_rows);
    let mut i = start + 1;
    while i < lines.len() {
        let line = lines[i].trim();
        if line == "end" {
            if rows.len() != expected_rows {
                return Err(CertIoError::Malformed {
                    line: start + 1,
                    msg: format!(
                        "parity-gf2 declares {expected_rows} rows, carries {}",
                        rows.len()
                    ),
                });
            }
            return Ok((ParityInfeasibilityCertificate::from_rows(rows), i + 1));
        }
        let fields: Vec<&str> = line.split_whitespace().collect();
        if fields.len() != 2 || fields[0] != "row" {
            return Err(CertIoError::Malformed {
                line: i + 1,
                msg: "malformed parity-gf2 row record".into(),
            });
        }
        let row = fields[1]
            .parse::<u32>()
            .map_err(|_| CertIoError::Malformed {
                line: i + 1,
                msg: "malformed parity-gf2 row index".into(),
            })?;
        if rows.last().is_some_and(|&previous| previous >= row) {
            return Err(CertIoError::Malformed {
                line: i + 1,
                msg: "parity-gf2 row indices are not strictly increasing".into(),
            });
        }
        rows.push(row);
        if rows.len() > expected_rows {
            return Err(CertIoError::Malformed {
                line: i + 1,
                msg: "parity-gf2 carries more rows than declared".into(),
            });
        }
        i += 1;
    }
    Err(CertIoError::Malformed {
        line: start + 1,
        msg: "parity-gf2 block not terminated".into(),
    })
}

pub(super) fn parse_resolution_literal(
    token: &str,
    num_vars: usize,
    line: usize,
) -> Result<Literal, CertIoError> {
    let signed = token.parse::<i64>().map_err(|_| CertIoError::Malformed {
        line,
        msg: "malformed sat-relu-rup literal".into(),
    })?;
    let magnitude = signed
        .checked_abs()
        .filter(|value| *value > 0)
        .ok_or_else(|| CertIoError::Malformed {
            line,
            msg: "sat-relu-rup literal is zero or out of range".into(),
        })?;
    let index = usize::try_from(magnitude - 1).map_err(|_| CertIoError::Malformed {
        line,
        msg: "sat-relu-rup variable index does not fit usize".into(),
    })?;
    if index >= num_vars {
        return Err(CertIoError::Malformed {
            line,
            msg: format!("sat-relu-rup variable {index} is outside vars={num_vars}"),
        });
    }
    let variable = Variable::new(u32::try_from(index).map_err(|_| CertIoError::Malformed {
        line,
        msg: "sat-relu-rup variable index does not fit u32".into(),
    })?);
    Ok(if signed > 0 {
        Literal::positive(variable)
    } else {
        Literal::negative(variable)
    })
}

pub(super) fn parse_digest32(token: &str) -> Option<[u8; 32]> {
    let hex = token.strip_prefix("sha256:")?;
    if hex.len() != 64
        || !hex
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return None;
    }
    let mut digest = [0u8; 32];
    for (index, byte) in digest.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&hex[index * 2..index * 2 + 2], 16).ok()?;
    }
    Some(digest)
}

pub(super) fn push_parsed_value<T>(
    values: &mut Vec<T>,
    value: T,
    line: usize,
    what: &str,
) -> Result<(), CertIoError> {
    if values.len() == values.capacity() {
        values.try_reserve(1).map_err(|_| CertIoError::Malformed {
            line,
            msg: format!("sat-relu-rup could not allocate {what}"),
        })?;
    }
    values.push(value);
    Ok(())
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::io;

use super::ProofStep;
use crate::literal::Literal;

fn invalid_lrat(line_number: usize, message: impl Into<String>) -> io::Error {
    io::Error::new(
        io::ErrorKind::InvalidData,
        format!(
            "malformed LRAT text at line {line_number}: {}",
            message.into()
        ),
    )
}

fn parse_clause_id(token: &str, line_number: usize) -> io::Result<u64> {
    let clause_id = token
        .parse::<u64>()
        .map_err(|err| invalid_lrat(line_number, format!("invalid clause id: {err}")))?;
    if clause_id == 0 {
        return Err(invalid_lrat(line_number, "clause id must be positive"));
    }
    Ok(clause_id)
}

fn validate_deletion(tokens: &[&str], line_number: usize) -> io::Result<()> {
    let _ = parse_clause_id(tokens[0], line_number)?;
    if tokens.last().copied() != Some("0") {
        return Err(invalid_lrat(line_number, "missing deletion terminator 0"));
    }
    for token in &tokens[2..tokens.len() - 1] {
        let deleted = token.parse::<u64>().map_err(|err| {
            invalid_lrat(line_number, format!("invalid deleted clause id: {err}"))
        })?;
        if deleted == 0 {
            return Err(invalid_lrat(
                line_number,
                "deleted clause id must be positive",
            ));
        }
    }
    Ok(())
}

pub(super) fn parse_lrat_text_addition(
    line: &str,
    line_number: usize,
) -> io::Result<Option<ProofStep>> {
    let tokens: Vec<&str> = line.split_whitespace().collect();
    if tokens.is_empty() {
        return Ok(None);
    }
    if tokens.get(1) == Some(&"d") {
        validate_deletion(&tokens, line_number)?;
        return Ok(None);
    }
    let clause_id = parse_clause_id(tokens[0], line_number)?;

    let first_zero = tokens
        .iter()
        .position(|&token| token == "0")
        .ok_or_else(|| invalid_lrat(line_number, "missing literal terminator 0"))?;
    if first_zero == 0 {
        return Err(invalid_lrat(
            line_number,
            "missing clause id before literals",
        ));
    }
    if first_zero + 1 >= tokens.len() || tokens.last().copied() != Some("0") {
        return Err(invalid_lrat(line_number, "missing final hint terminator 0"));
    }

    let mut literals = Vec::with_capacity(first_zero.saturating_sub(1));
    for token in &tokens[1..first_zero] {
        let raw = token
            .parse::<i32>()
            .map_err(|err| invalid_lrat(line_number, format!("invalid literal: {err}")))?;
        if raw == 0 || raw == i32::MIN {
            return Err(invalid_lrat(line_number, "literal is outside DIMACS range"));
        }
        literals.push(Literal::from_dimacs(raw));
    }

    let mut hints = Vec::with_capacity(tokens.len().saturating_sub(first_zero + 2));
    for token in &tokens[first_zero + 1..tokens.len() - 1] {
        let hint = token
            .parse::<i64>()
            .map_err(|err| invalid_lrat(line_number, format!("invalid hint: {err}")))?;
        if hint == 0 {
            return Err(invalid_lrat(line_number, "hint 0 before terminator"));
        }
        hints.push(hint);
    }

    Ok(Some(ProofStep {
        clause_id,
        literals,
        hints,
    }))
}

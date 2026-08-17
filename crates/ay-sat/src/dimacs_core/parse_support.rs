// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

struct ByteTokens<'a> {
    bytes: &'a [u8],
    pos: usize,
}

impl<'a> ByteTokens<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, pos: 0 }
    }
}

impl<'a> Iterator for ByteTokens<'a> {
    type Item = &'a [u8];

    fn next(&mut self) -> Option<Self::Item> {
        while self.pos < self.bytes.len() && self.bytes[self.pos].is_ascii_whitespace() {
            self.pos += 1;
        }
        if self.pos == self.bytes.len() {
            return None;
        }

        let start = self.pos;
        while self.pos < self.bytes.len() && !self.bytes[self.pos].is_ascii_whitespace() {
            self.pos += 1;
        }
        Some(&self.bytes[start..self.pos])
    }
}

fn trim_ascii(bytes: &[u8]) -> &[u8] {
    let mut start = 0;
    while start < bytes.len() && bytes[start].is_ascii_whitespace() {
        start += 1;
    }

    let mut end = bytes.len();
    while end > start && bytes[end - 1].is_ascii_whitespace() {
        end -= 1;
    }

    &bytes[start..end]
}

fn parse_header_line(line: &[u8], line_number: usize) -> Result<DimacsHeader, DimacsCoreError> {
    let mut tokens = ByteTokens::new(line);
    let _problem = tokens
        .next()
        .ok_or_else(|| invalid_header(line, line_number))?;
    let kind = tokens
        .next()
        .ok_or_else(|| invalid_header(line, line_number))?;
    let vars = tokens
        .next()
        .ok_or_else(|| invalid_header(line, line_number))?;
    let clauses = tokens
        .next()
        .ok_or_else(|| invalid_header(line, line_number))?;

    if kind != b"cnf" {
        return Err(invalid_header(line, line_number));
    }

    let num_vars = parse_usize_token(vars).ok_or_else(|| invalid_header(line, line_number))?;
    let num_clauses =
        parse_usize_token(clauses).ok_or_else(|| invalid_header(line, line_number))?;

    // NOTE: the declared `num_vars` is deliberately NOT used to size any
    // allocation and is NOT range-checked here. It is untrusted metadata: an
    // over-declared header like `p cnf 4000000000 1` describes a valid instance
    // whose real variable count is tiny. Consumers size their per-variable state
    // by the variables that ACTUALLY appear (see `MAX_DIMACS_VARS` and the
    // content-driven sizing in `dimacs::parse` / the streaming path), so a lying
    // header can no longer drive an allocation.
    Ok(DimacsHeader {
        num_vars,
        num_clauses,
    })
}

fn parse_usize_token(token: &[u8]) -> Option<usize> {
    let mut pos = 0;
    if token.first() == Some(&b'+') {
        pos = 1;
    }
    if pos == token.len() {
        return None;
    }

    let mut value = 0usize;
    while pos < token.len() {
        let byte = token[pos];
        if !byte.is_ascii_digit() {
            return None;
        }
        value = value.checked_mul(10)?;
        value = value.checked_add(usize::from(byte - b'0'))?;
        pos += 1;
    }
    Some(value)
}

fn parse_i32_token(token: &[u8]) -> Option<i32> {
    let mut pos = 0;
    let mut negative = false;

    match token.first().copied() {
        Some(b'-') => {
            negative = true;
            pos = 1;
        }
        Some(b'+') => {
            pos = 1;
        }
        Some(_) => {}
        None => return None,
    }

    if pos == token.len() {
        return None;
    }

    let limit = if negative {
        i32::MAX as u32 + 1
    } else {
        i32::MAX as u32
    };
    let mut value = 0u32;
    while pos < token.len() {
        let byte = token[pos];
        if !byte.is_ascii_digit() {
            return None;
        }
        value = value.checked_mul(10)?;
        value = value.checked_add(u32::from(byte - b'0'))?;
        if value > limit {
            return None;
        }
        pos += 1;
    }

    if negative {
        if value == i32::MAX as u32 + 1 {
            Some(i32::MIN)
        } else {
            Some(-(value as i32))
        }
    } else {
        Some(value as i32)
    }
}

fn invalid_header(line: &[u8], line_number: usize) -> DimacsCoreError {
    DimacsCoreError::InvalidHeader {
        line_content: String::from_utf8_lossy(line).into_owned(),
        line_number,
    }
}

fn invalid_literal(token: &[u8], line_number: usize) -> DimacsCoreError {
    DimacsCoreError::InvalidLiteral {
        token: String::from_utf8_lossy(token).into_owned(),
        line_number,
    }
}

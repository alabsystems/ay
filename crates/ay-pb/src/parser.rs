// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Author: Andrew Yates <andrewyates.name@gmail.com>
//! Parser for OPB and WBO pseudo-Boolean competition formats.
//!
//! Reference: <https://www.cril.univ-artois.fr/PB24/OPBcompetition.pdf>

use crate::types::{PbConstraint, PbInstance, PbLit, PbObjective, PbRel, PbTerm, WboInstance};
use thiserror::Error;

const PARSE_STOP_POLL_INTERVAL: usize = 256;
const HEADER_CONSTRAINT_PREALLOC_LIMIT: usize = 131_072;
const FAST_LINEAR_TERM_PREALLOC_LIMIT: usize = 131_072;
const FAST_LINEAR_TERM_BYTES_ESTIMATE: usize = 8;

/// Errors that can occur during OPB/WBO parsing.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
#[non_exhaustive]
pub enum ParseError {
    /// A coefficient is syntactically valid but exceeds the solver's supported
    /// range (beyond i128). Per PB competition rules, solvers may respond with
    /// `s UNSUPPORTED` for such instances.
    #[error("line {line}: coefficient exceeds solver's supported range (i128): '{token}'")]
    CoefficientUnsupported { line: usize, token: String },

    /// A coefficient exceeds the i128 range.
    ///
    /// Alias for [`ParseError::CoefficientUnsupported`], retained for backwards
    /// compatibility. New code should prefer pattern-matching on the
    /// `CoefficientUnsupported` variant directly.
    #[error("line {line}: coefficient overflow (exceeds i128 range): '{token}'")]
    CoefficientOverflow { line: usize, token: String },

    /// The declared or inferred variable count exceeds the solver's supported
    /// range. Solvers may respond with `s UNSUPPORTED` for such instances.
    #[error("variable count {count} exceeds the maximum supported {max}; refusing to allocate")]
    VariableCountUnsupported { count: u32, max: u32 },

    /// Expected a relational operator (`>=` or `=`) but found something else.
    #[error("line {line}: expected relational operator (>= or =), found '{found}'")]
    ExpectedRelOp { line: usize, found: String },

    /// Expected a semicolon terminator.
    #[error("line {line}: expected ';' at end of constraint")]
    ExpectedSemicolon { line: usize },

    /// Expected an integer constant.
    #[error("line {line}: expected integer, found '{found}'")]
    ExpectedInteger { line: usize, found: String },

    /// Expected a literal (`x<N>` or `~x<N>`).
    #[error("line {line}: expected literal (`x<N>` or `~x<N>`), found '{found}'")]
    ExpectedLiteral { line: usize, found: String },

    /// Invalid variable index (must be >= 1).
    #[error("line {line}: invalid variable index '{index}' (must be >= 1)")]
    InvalidVariable { line: usize, index: String },

    /// Missing `soft:` declaration in WBO format.
    #[error("line {line}: expected 'soft:' declaration")]
    ExpectedSoftDecl { line: usize },

    /// WBO does not permit an explicit objective function.
    #[error(
        "line {line}: WBO instances do not allow explicit 'min:' objectives; encode optimization with 'soft:' and '[cost]' constraints"
    )]
    WboObjectiveUnsupported { line: usize },

    /// Unexpected end of input.
    #[error("line {line}: unexpected end of input")]
    UnexpectedEof { line: usize },

    /// Parsing stopped because the caller requested termination.
    #[error("line {line}: parsing interrupted")]
    Interrupted { line: usize },

    /// Generic parse error.
    #[error("line {line}: {message}")]
    Generic { line: usize, message: String },
}

impl ParseError {
    /// Returns `true` if this error indicates a coefficient exceeds the solver's
    /// supported precision range (i128). Parsers that want to emit
    /// `s UNSUPPORTED` per PB competition rules should check this.
    #[must_use]
    pub fn is_unsupported_coefficient(&self) -> bool {
        matches!(
            self,
            Self::CoefficientUnsupported { .. } | Self::CoefficientOverflow { .. }
        )
    }

    /// Returns `true` if this error marks a well-formed but unsupported input
    /// (out-of-range coefficient or variable count) rather than a syntax
    /// error. Drivers should map these to `s UNSUPPORTED` per PB competition
    /// rules instead of exiting without an `s` line.
    #[must_use]
    pub fn is_unsupported_input(&self) -> bool {
        self.is_unsupported_coefficient() || matches!(self, Self::VariableCountUnsupported { .. })
    }

    /// Returns the line number associated with the error.
    #[must_use]
    pub fn line(&self) -> usize {
        match self {
            Self::VariableCountUnsupported { .. } => 0,
            Self::CoefficientUnsupported { line, .. }
            | Self::CoefficientOverflow { line, .. }
            | Self::ExpectedRelOp { line, .. }
            | Self::ExpectedSemicolon { line }
            | Self::ExpectedInteger { line, .. }
            | Self::ExpectedLiteral { line, .. }
            | Self::InvalidVariable { line, .. }
            | Self::ExpectedSoftDecl { line }
            | Self::WboObjectiveUnsupported { line }
            | Self::UnexpectedEof { line }
            | Self::Interrupted { line }
            | Self::Generic { line, .. } => *line,
        }
    }
}

/// Parse an OPB format string into a `PbInstance`.
///
/// Accepts input with or without a leading UTF-8 BOM. Line endings may be
/// `\n` or `\r\n`.
pub fn parse_opb(input: &str) -> Result<PbInstance, ParseError> {
    parse_opb_interruptible(input, || false)
}

/// Serialize a `PbInstance` to OPB text (the inverse of [`parse_opb`] for linear
/// instances). Round-trips a linear PB instance; used to emit the PROJECTED OPB
/// formula that a WBO certificate's VeriPB proof is written over, so the proof is
/// self-contained and checkable (`veripb <emitted-opb> <proof>`). Non-linear
/// (product) terms are written with all their literals space-joined, matching the
/// OPB product syntax.
pub fn instance_to_opb(instance: &PbInstance) -> String {
    use crate::types::PbRel;
    use std::fmt::Write as _;
    let mut s = String::new();
    let _ = writeln!(
        s,
        "* #variable= {} #constraint= {}",
        instance.num_vars,
        instance.constraints.len()
    );
    let write_terms = |s: &mut String, terms: &[PbTerm]| {
        for t in terms {
            let sign = if t.coeff >= 0 { "+" } else { "" };
            let _ = write!(s, "{sign}{} ", t.coeff);
            for lit in &t.lits {
                let _ = write!(s, "{}x{} ", if lit.negated { "~" } else { "" }, lit.var);
            }
        }
    };
    if let Some(obj) = &instance.objective {
        let _ = write!(s, "min: ");
        write_terms(&mut s, &obj.terms);
        let _ = writeln!(s, ";");
    }
    for con in &instance.constraints {
        write_terms(&mut s, &con.terms);
        let rel = match con.rel {
            PbRel::Ge => ">=",
            PbRel::Eq => "=",
        };
        let _ = writeln!(s, "{rel} {} ;", con.rhs);
    }
    s
}

/// Parse an OPB format string into a `PbInstance`, aborting if `should_stop`
/// returns true.
pub fn parse_opb_interruptible<F>(input: &str, mut should_stop: F) -> Result<PbInstance, ParseError>
where
    F: FnMut() -> bool,
{
    parse_opb_with_stop(input, &mut should_stop)
}

fn parse_opb_with_stop<F>(input: &str, should_stop: &mut F) -> Result<PbInstance, ParseError>
where
    F: FnMut() -> bool,
{
    let input = strip_bom(input);
    let mut num_vars: u32 = 0;
    let mut num_constraints: u32 = 0;
    let mut constraints = Vec::new();
    let mut objective = None;

    for (line_idx, line) in input.lines().enumerate() {
        let line_num = line_idx.saturating_add(1);
        if should_stop() {
            return Err(ParseError::Interrupted { line: line_num });
        }
        let trimmed = line.trim();

        // Skip empty lines
        if trimmed.is_empty() {
            continue;
        }

        // Comment lines start with '*'
        if trimmed.starts_with('*') {
            // Try to parse header metadata from comment
            let previous_num_constraints = num_constraints;
            parse_header_comment(trimmed, &mut num_vars, &mut num_constraints);
            maybe_reserve_header_constraints(
                &mut constraints,
                previous_num_constraints,
                num_constraints,
            );
            continue;
        }

        // Objective line: "min: ... ;"
        if let Some(body) = trimmed.strip_prefix("min:") {
            objective = Some(parse_objective(body, line_num, should_stop)?);
            continue;
        }

        // Otherwise it's a constraint
        let constraint = parse_constraint(trimmed, line_num, should_stop)?;
        constraints.push(constraint);
    }

    // If num_vars was not in the header, infer it from the literals that appear.
    if num_vars == 0 {
        num_vars = infer_max_var_constraints(&constraints, &objective);
    }

    check_max_pb_vars(num_vars)?;

    Ok(PbInstance {
        num_vars,
        num_constraints,
        constraints,
        objective,
    })
}

/// Refuse variable counts whose per-variable arrays could not be allocated.
///
/// Unlike the SAT/QDIMACS paths, a PB solution assignment is defined over the
/// declared variable set (the optimizer pads/normalizes incumbents to exactly
/// `num_vars`), so `num_vars` is the real output dimension and cannot be
/// shrunk to the variables that happen to appear. Bound that dimension: a
/// value beyond this would require a hundreds-of-GB-long assignment and the
/// CDCL solver's matching per-variable arrays (activity, phases, VSIDS heap,
/// three DenseCp coeff/stamp arrays), so it is refused rather than allocated.
/// Applies to both the OPB and WBO paths (WBO additionally adds one relaxation
/// variable per paid soft constraint on top of this count).
fn check_max_pb_vars(num_vars: u32) -> Result<(), ParseError> {
    const MAX_PB_VARS: u32 = 1 << 28;
    if num_vars > MAX_PB_VARS {
        return Err(ParseError::VariableCountUnsupported {
            count: num_vars,
            max: MAX_PB_VARS,
        });
    }
    Ok(())
}

/// Parse a WBO format string into a `WboInstance`.
///
/// Accepts input with or without a leading UTF-8 BOM. Line endings may be
/// `\n` or `\r\n`.
pub fn parse_wbo(input: &str) -> Result<WboInstance, ParseError> {
    parse_wbo_interruptible(input, || false)
}

/// Parse a WBO format string into a `WboInstance`, aborting if `should_stop`
/// returns true.
pub fn parse_wbo_interruptible<F>(
    input: &str,
    mut should_stop: F,
) -> Result<WboInstance, ParseError>
where
    F: FnMut() -> bool,
{
    parse_wbo_with_stop(input, &mut should_stop)
}

fn parse_wbo_with_stop<F>(input: &str, should_stop: &mut F) -> Result<WboInstance, ParseError>
where
    F: FnMut() -> bool,
{
    let input = strip_bom(input);
    let mut lines_iter = input.lines().enumerate().peekable();
    let mut num_vars: u32 = 0;
    let mut num_constraints: u32 = 0;
    let mut top_cost: Option<i128> = None;
    let mut found_soft_decl = false;
    let mut hard_constraints = Vec::new();
    let mut soft_constraints = Vec::new();
    let objective = None;

    // Find the `soft:` declaration (skip comments first)
    while let Some(&(line_idx, line)) = lines_iter.peek() {
        let trimmed = line.trim();
        let line_num = line_idx.saturating_add(1);
        if should_stop() {
            return Err(ParseError::Interrupted { line: line_num });
        }

        if trimmed.is_empty() {
            lines_iter.next();
            continue;
        }

        if trimmed.starts_with('*') {
            let previous_num_constraints = num_constraints;
            parse_header_comment(trimmed, &mut num_vars, &mut num_constraints);
            maybe_reserve_wbo_header_constraints(
                &mut hard_constraints,
                &mut soft_constraints,
                previous_num_constraints,
                num_constraints,
            );
            lines_iter.next();
            continue;
        }

        // First non-comment, non-empty line must be "soft: [<cost>] ;". The
        // integer is optional: a bare "soft: ;" means there is no top-cost
        // bound (T = infinity in the official format).
        if let Some(rest) = trimmed.strip_prefix("soft:") {
            let body = rest.trim();
            let body = body
                .strip_suffix(';')
                .ok_or(ParseError::ExpectedSemicolon { line: line_num })?
                .trim();
            top_cost = if body.is_empty() {
                None
            } else {
                Some(parse_i64_token(body, line_num)?)
            };
            found_soft_decl = true;
            lines_iter.next();
            break;
        }

        return Err(ParseError::ExpectedSoftDecl { line: line_num });
    }

    if !found_soft_decl {
        return Err(ParseError::ExpectedSoftDecl { line: 1 });
    }

    // Parse remaining lines
    for (line_idx, line) in lines_iter {
        let line_num = line_idx.saturating_add(1);
        if should_stop() {
            return Err(ParseError::Interrupted { line: line_num });
        }
        let trimmed = line.trim();

        if trimmed.is_empty() {
            continue;
        }

        if trimmed.starts_with('*') {
            continue;
        }

        // Objective
        if trimmed.starts_with("min:") {
            return Err(ParseError::WboObjectiveUnsupported { line: line_num });
        }

        // Soft constraint: "[cost] constraint ;"
        if trimmed.starts_with('[') {
            let (cost, rest) = parse_soft_prefix_interruptible(trimmed, line_num, should_stop)?;
            let constraint = parse_constraint(rest, line_num, should_stop)?;
            soft_constraints.push((cost, constraint));
            continue;
        }

        // Hard constraint
        let constraint = parse_constraint(trimmed, line_num, should_stop)?;
        hard_constraints.push(constraint);
    }

    // Take the max of the declared header count and the variables actually
    // used. Trusting an understated header would be UNSOUND here: the WBO
    // relaxation allocates its relaxation variables starting at num_vars + 1,
    // so an in-use variable above the header count would be aliased by a
    // relaxation variable (wrong models, incomplete v lines).
    num_vars = num_vars.max(infer_max_var_wbo(
        &hard_constraints,
        &soft_constraints,
        &objective,
    ));
    check_max_pb_vars(num_vars)?;

    Ok(WboInstance {
        top_cost,
        num_vars,
        hard_constraints,
        soft_constraints,
        objective,
    })
}

// --- Internal helpers ---

/// Strip the UTF-8 byte-order mark (`\u{FEFF}`), if present, from the start
/// of the input. Some editors write OPB/WBO files with a BOM.
fn strip_bom(input: &str) -> &str {
    input.strip_prefix('\u{FEFF}').unwrap_or(input)
}

/// Try to extract `#variable=` and `#constraint=` from a header comment.
fn parse_header_comment(comment: &str, num_vars: &mut u32, num_constraints: &mut u32) {
    // Format: "* #variable= N #constraint= M"
    if let Some(pos) = comment.find("#variable=") {
        let after = &comment[pos + 10..];
        if let Some(val) = extract_next_u32(after) {
            *num_vars = val;
        }
    }
    if let Some(pos) = comment.find("#constraint=") {
        let after = &comment[pos + 12..];
        if let Some(val) = extract_next_u32(after) {
            *num_constraints = val;
        }
    }
}

/// Extract the next whitespace-delimited u32 from a string.
fn extract_next_u32(s: &str) -> Option<u32> {
    let trimmed = s.trim_start();
    let end = trimmed
        .find(|c: char| !c.is_ascii_digit())
        .unwrap_or(trimmed.len());
    trimmed[..end].parse().ok()
}

fn maybe_reserve_header_constraints<T>(
    constraints: &mut Vec<T>,
    previous_num_constraints: u32,
    num_constraints: u32,
) {
    if previous_num_constraints != 0 || num_constraints == 0 || constraints.capacity() != 0 {
        return;
    }
    try_reserve_bounded_header_constraints(
        constraints,
        bounded_header_constraint_capacity(num_constraints),
    );
}

fn maybe_reserve_wbo_header_constraints(
    hard_constraints: &mut Vec<PbConstraint>,
    soft_constraints: &mut Vec<(i128, PbConstraint)>,
    previous_num_constraints: u32,
    num_constraints: u32,
) {
    if previous_num_constraints != 0
        || num_constraints == 0
        || hard_constraints.capacity() != 0
        || soft_constraints.capacity() != 0
    {
        return;
    }

    let capacity = bounded_header_constraint_capacity(num_constraints);
    let hard_capacity = capacity / 2;
    let soft_capacity = capacity.saturating_sub(hard_capacity);
    try_reserve_bounded_header_constraints(hard_constraints, hard_capacity);
    try_reserve_bounded_header_constraints(soft_constraints, soft_capacity);
}

fn bounded_header_constraint_capacity(num_constraints: u32) -> usize {
    (num_constraints as usize).min(HEADER_CONSTRAINT_PREALLOC_LIMIT)
}

fn try_reserve_bounded_header_constraints<T>(constraints: &mut Vec<T>, capacity: usize) {
    if capacity == 0 {
        return;
    }
    let _ = constraints.try_reserve(capacity);
}

fn fast_linear_terms_with_bounded_capacity(line: &str) -> Vec<PbTerm> {
    let capacity =
        (line.len() / FAST_LINEAR_TERM_BYTES_ESTIMATE).min(FAST_LINEAR_TERM_PREALLOC_LIMIT);
    let mut terms = Vec::new();
    if capacity > 0 {
        let _ = terms.try_reserve(capacity);
    }
    terms
}

/// Parse an objective body (everything after "min:" up to ";").
fn parse_objective<F>(
    body: &str,
    line_num: usize,
    should_stop: &mut F,
) -> Result<PbObjective, ParseError>
where
    F: FnMut() -> bool,
{
    let body = body
        .trim()
        .strip_suffix(';')
        .ok_or(ParseError::ExpectedSemicolon { line: line_num })?
        .trim();
    if let Some(terms) = parse_linear_sum_bytes(body, line_num, should_stop) {
        return terms.map(|terms| PbObjective { terms });
    }
    if let Some(terms) = parse_linear_sum_tokens(body, line_num, should_stop) {
        return terms.map(|terms| PbObjective { terms });
    }

    let terms = parse_sum(body, line_num, should_stop)?;
    Ok(PbObjective { terms })
}

/// Parse a constraint line: `<sum> <relop> <integer> ;`
fn parse_constraint<F>(
    line: &str,
    line_num: usize,
    should_stop: &mut F,
) -> Result<PbConstraint, ParseError>
where
    F: FnMut() -> bool,
{
    let line = line
        .strip_suffix(';')
        .ok_or(ParseError::ExpectedSemicolon { line: line_num })?;
    let line = line.trim();
    if let Some(constraint) = parse_linear_constraint_bytes(line, line_num, should_stop) {
        return constraint;
    }
    if let Some(constraint) = parse_linear_constraint_tokens(line, line_num, should_stop) {
        return constraint;
    }

    // Find the relational operator by scanning from the end.
    let (sum_part, rel, rhs) = split_constraint_interruptible(line, line_num, should_stop)?;
    let terms = parse_sum(sum_part, line_num, should_stop)?;

    canonicalize_parsed_constraint(terms, rel, rhs, line_num)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ParsedRel {
    Ge,
    Eq,
    Le,
}

/// Maximum decimal digits handled by the byte-cursor integer fast path.
///
/// Every 19-digit magnitude (max 9_999_999_999_999_999_999) fits u64, so the
/// fast path accumulates digits with NO per-digit overflow check. Longer
/// tokens — potentially still valid i128 — deviate to the token-based fast
/// path, whose `parse_i64_token` handles full i128 range and the
/// overflow-vs-garbage error classification.
const FAST_INT_MAX_DIGITS: usize = 19;

/// Single-pass byte cursor over one (already `;`-stripped, trimmed) line.
///
/// This is the hot pre-search tokenizer: `str::split_ascii_whitespace` +
/// per-token `parse_i64_token`/`try_parse_literal` walk every byte twice
/// (once to find token boundaries, once to parse) and cost ~0.2s of the
/// measured 0.85s parse on the 6.4M-row lopes-172. The cursor parses
/// coefficients and literals directly off the byte slice in one pass.
///
/// STRICT-SUBSET CONTRACT: every scanner returns `None` on ANY deviation
/// from the clean linear shape (missing digits, out-of-range values, a token
/// not ending at whitespace/end-of-line, ...). Callers translate `None` into
/// a fallback to the token-based fast path and then the general parser, so
/// deviating input takes EXACTLY the pre-existing code paths (same accepted
/// language, same errors). The differential parse-digest gate over the full
/// selected-PB24 corpus locks this equivalence.
struct ByteCursor<'a> {
    bytes: &'a [u8],
    pos: usize,
}

impl<'a> ByteCursor<'a> {
    fn new(line: &'a str) -> Self {
        Self {
            bytes: line.as_bytes(),
            pos: 0,
        }
    }

    fn skip_ws(&mut self) {
        while let Some(&byte) = self.bytes.get(self.pos) {
            if !byte.is_ascii_whitespace() {
                break;
            }
            self.pos += 1;
        }
    }

    fn at_end(&self) -> bool {
        self.pos >= self.bytes.len()
    }

    fn peek(&self) -> Option<u8> {
        self.bytes.get(self.pos).copied()
    }

    fn peek_at(&self, offset: usize) -> Option<u8> {
        self.bytes.get(self.pos + offset).copied()
    }

    /// Whether the current position is a token boundary (whitespace or end).
    fn at_ws_or_end(&self) -> bool {
        self.bytes
            .get(self.pos)
            .is_none_or(|byte| byte.is_ascii_whitespace())
    }

    /// Scans `[+|-]<digits>` (at most [`FAST_INT_MAX_DIGITS`]) ending at a
    /// token boundary. `None` on any deviation; the cursor is only advanced
    /// on success.
    fn scan_small_int(&mut self) -> Option<i128> {
        let bytes = self.bytes;
        let mut pos = self.pos;
        let mut negative = false;
        match bytes.get(pos).copied() {
            Some(b'+') => pos += 1,
            Some(b'-') => {
                negative = true;
                pos += 1;
            }
            _ => {}
        }

        let digits_start = pos;
        let mut value = 0u64;
        while let Some(&byte) = bytes.get(pos) {
            if !byte.is_ascii_digit() {
                break;
            }
            if pos - digits_start >= FAST_INT_MAX_DIGITS {
                return None;
            }
            value = value * 10 + u64::from(byte - b'0');
            pos += 1;
        }
        if pos == digits_start {
            return None;
        }
        if bytes
            .get(pos)
            .is_some_and(|byte| !byte.is_ascii_whitespace())
        {
            return None;
        }

        self.pos = pos;
        let value = i128::from(value);
        Some(if negative { -value } else { value })
    }

    /// Scans `[~]x<digits>` (a nonzero u32 variable index) ending at a token
    /// boundary. `None` on any deviation; the cursor is only advanced on
    /// success.
    fn scan_literal(&mut self) -> Option<PbLit> {
        let bytes = self.bytes;
        let mut pos = self.pos;
        let mut negated = false;
        if bytes.get(pos) == Some(&b'~') {
            negated = true;
            pos += 1;
        }
        if bytes.get(pos) != Some(&b'x') {
            return None;
        }
        pos += 1;

        let digits_start = pos;
        let mut value = 0u64;
        while let Some(&byte) = bytes.get(pos) {
            if !byte.is_ascii_digit() {
                break;
            }
            // > 10 digits cannot be a u32 index.
            if pos - digits_start >= 10 {
                return None;
            }
            value = value * 10 + u64::from(byte - b'0');
            pos += 1;
        }
        if pos == digits_start || value == 0 || value > u64::from(u32::MAX) {
            return None;
        }
        if bytes
            .get(pos)
            .is_some_and(|byte| !byte.is_ascii_whitespace())
        {
            return None;
        }

        self.pos = pos;
        Some(PbLit {
            var: value as u32,
            negated,
        })
    }
}

/// Byte-cursor fast path for a clean linear constraint line
/// (`<coeff> <lit> ... <relop> <rhs>`, `;` already stripped, trimmed).
/// Returns `None` on any deviation (see [`ByteCursor`]); the caller then
/// retries with the token-based fast path and the general parser.
fn parse_linear_constraint_bytes(
    line: &str,
    line_num: usize,
    should_stop: &mut impl FnMut() -> bool,
) -> Option<Result<PbConstraint, ParseError>> {
    let mut cursor = ByteCursor::new(line);
    let mut terms = fast_linear_terms_with_bounded_capacity(line);
    let mut poll_counter = 0;

    loop {
        cursor.skip_ws();
        if let Err(err) = poll_parse_stop(should_stop, line_num, &mut poll_counter) {
            return Some(Err(err));
        }

        let rel = match cursor.peek() {
            // End of line without a relational operator: not a constraint.
            None => return None,
            Some(b'>') if cursor.peek_at(1) == Some(b'=') => {
                cursor.pos += 2;
                ParsedRel::Ge
            }
            Some(b'<') if cursor.peek_at(1) == Some(b'=') => {
                cursor.pos += 2;
                ParsedRel::Le
            }
            Some(b'=') => {
                cursor.pos += 1;
                ParsedRel::Eq
            }
            _ => {
                let coeff = cursor.scan_small_int()?;
                cursor.skip_ws();
                let lit = cursor.scan_literal()?;
                terms.push(PbTerm {
                    coeff,
                    lits: vec![lit],
                });
                continue;
            }
        };

        // The token fast path only matched `>=`/`<=`/`=` as standalone
        // whitespace-delimited tokens; anything glued to the operator (e.g.
        // `>=3`) must deviate to the general parser exactly as before.
        if !cursor.at_ws_or_end() {
            return None;
        }
        cursor.skip_ws();
        let rhs = cursor.scan_small_int()?;
        cursor.skip_ws();
        if !cursor.at_end() {
            return None;
        }
        return Some(canonicalize_parsed_constraint(terms, rel, rhs, line_num));
    }
}

/// Byte-cursor fast path for a clean linear sum (objective body, `;` already
/// stripped, trimmed). Returns `None` on any deviation (see [`ByteCursor`]).
fn parse_linear_sum_bytes(
    line: &str,
    line_num: usize,
    should_stop: &mut impl FnMut() -> bool,
) -> Option<Result<Vec<PbTerm>, ParseError>> {
    let mut cursor = ByteCursor::new(line);
    let mut terms = fast_linear_terms_with_bounded_capacity(line);
    let mut poll_counter = 0;

    loop {
        cursor.skip_ws();
        if cursor.at_end() {
            return Some(Ok(terms));
        }
        if let Err(err) = poll_parse_stop(should_stop, line_num, &mut poll_counter) {
            return Some(Err(err));
        }

        let coeff = cursor.scan_small_int()?;
        cursor.skip_ws();
        let lit = cursor.scan_literal()?;
        terms.push(PbTerm {
            coeff,
            lits: vec![lit],
        });
    }
}

fn parse_linear_constraint_tokens(
    line: &str,
    line_num: usize,
    should_stop: &mut impl FnMut() -> bool,
) -> Option<Result<PbConstraint, ParseError>> {
    let mut tokens = line.split_ascii_whitespace();
    let mut terms = fast_linear_terms_with_bounded_capacity(line);
    let mut poll_counter = 0;

    loop {
        let token = tokens.next()?;
        if let Err(err) = poll_parse_stop(should_stop, line_num, &mut poll_counter) {
            return Some(Err(err));
        }
        let rel = match token {
            ">=" => ParsedRel::Ge,
            "=" => ParsedRel::Eq,
            "<=" => ParsedRel::Le,
            _ => {
                match parse_i64_token(token, line_num) {
                    Ok(coeff) => {
                        let lit_token = tokens.next()?;
                        let lit = try_parse_literal(lit_token)?;
                        terms.push(PbTerm {
                            coeff,
                            lits: vec![lit],
                        });
                    }
                    Err(err) if err.is_unsupported_coefficient() => {
                        return Some(Err(err));
                    }
                    Err(_) => return None,
                }
                continue;
            }
        };

        let rhs_token = tokens.next()?;
        if let Err(err) = poll_parse_stop(should_stop, line_num, &mut poll_counter) {
            return Some(Err(err));
        }
        if tokens.next().is_some() {
            return None;
        }
        return Some(
            parse_i64_token(rhs_token, line_num)
                .and_then(|rhs| canonicalize_parsed_constraint(terms, rel, rhs, line_num)),
        );
    }
}

fn parse_linear_sum_tokens(
    line: &str,
    line_num: usize,
    should_stop: &mut impl FnMut() -> bool,
) -> Option<Result<Vec<PbTerm>, ParseError>> {
    let mut tokens = line.split_ascii_whitespace();
    let mut terms = fast_linear_terms_with_bounded_capacity(line);
    let mut poll_counter = 0;

    loop {
        let Some(coeff_token) = tokens.next() else {
            return Some(Ok(terms));
        };
        if let Err(err) = poll_parse_stop(should_stop, line_num, &mut poll_counter) {
            return Some(Err(err));
        }

        let coeff = match parse_i64_token(coeff_token, line_num) {
            Ok(coeff) => coeff,
            Err(err) if matches!(err, ParseError::CoefficientOverflow { .. }) => {
                return Some(Err(err));
            }
            Err(_) => return None,
        };

        let lit_token = tokens.next()?;
        let lit = try_parse_literal(lit_token)?;
        terms.push(PbTerm {
            coeff,
            lits: vec![lit],
        });
    }
}

/// Split a constraint into (sum_str, rel, rhs).
fn split_constraint_interruptible<'a, F>(
    line: &'a str,
    line_num: usize,
    should_stop: &mut F,
) -> Result<(&'a str, ParsedRel, i128), ParseError>
where
    F: FnMut() -> bool,
{
    let bytes = line.as_bytes();
    let mut poll_counter = 0;

    for i in (0..bytes.len()).rev() {
        poll_parse_stop(should_stop, line_num, &mut poll_counter)?;
        if bytes[i] != b'=' {
            continue;
        }

        if i > 0 && bytes[i - 1] == b'>' {
            let sum_part = line[..i - 1].trim();
            let rhs_str = line[i + 1..].trim();
            let rhs = parse_i64_token(rhs_str, line_num)?;
            return Ok((sum_part, ParsedRel::Ge, rhs));
        }

        if i > 0 && bytes[i - 1] == b'<' {
            let sum_part = line[..i - 1].trim();
            let rhs_str = line[i + 1..].trim();
            let rhs = parse_i64_token(rhs_str, line_num)?;
            return Ok((sum_part, ParsedRel::Le, rhs));
        }

        let sum_part = line[..i].trim();
        let rhs_str = line[i + 1..].trim();
        let rhs = parse_i64_token(rhs_str, line_num)?;
        return Ok((sum_part, ParsedRel::Eq, rhs));
    }

    Err(ParseError::ExpectedRelOp {
        line: line_num,
        found: line.to_string(),
    })
}

fn canonicalize_parsed_constraint(
    terms: Vec<PbTerm>,
    rel: ParsedRel,
    rhs: i128,
    line_num: usize,
) -> Result<PbConstraint, ParseError> {
    match rel {
        ParsedRel::Ge => Ok(PbConstraint {
            terms,
            rel: PbRel::Ge,
            rhs,
        }),
        ParsedRel::Eq => Ok(PbConstraint {
            terms,
            rel: PbRel::Eq,
            rhs,
        }),
        ParsedRel::Le => Ok(PbConstraint {
            terms: negate_terms(terms, line_num)?,
            rel: PbRel::Ge,
            rhs: checked_neg_i64(rhs, line_num)?,
        }),
    }
}

fn negate_terms(terms: Vec<PbTerm>, line_num: usize) -> Result<Vec<PbTerm>, ParseError> {
    terms
        .into_iter()
        .map(|term| {
            Ok(PbTerm {
                coeff: checked_neg_i64(term.coeff, line_num)?,
                lits: term.lits,
            })
        })
        .collect()
}

fn checked_neg_i64(value: i128, line_num: usize) -> Result<i128, ParseError> {
    value
        .checked_neg()
        .ok_or(ParseError::CoefficientUnsupported {
            line: line_num,
            token: value.to_string(),
        })
}

/// Parse a sum of terms: `<coeff> <lit>+ <coeff> <lit>+ ...`
fn parse_sum<F>(s: &str, line_num: usize, should_stop: &mut F) -> Result<Vec<PbTerm>, ParseError>
where
    F: FnMut() -> bool,
{
    let s = s.trim();
    if s.is_empty() {
        return Ok(Vec::new());
    }

    let mut tokens = TokenCursor::new(s);
    let mut terms = fast_linear_terms_with_bounded_capacity(s);

    while let Some(coeff_token) = tokens.next_token(line_num, should_stop)? {
        let coeff = parse_i64_token(coeff_token, line_num)?;

        // Parse one or more literals (non-linear term if multiple)
        let mut lits = Vec::new();
        while let Some(token) = tokens.peek_token(line_num, should_stop)? {
            if let Some(lit) = try_parse_literal(token) {
                lits.push(lit);
                tokens.next_token(line_num, should_stop)?;
            } else {
                break;
            }
        }

        if lits.is_empty() {
            let found = tokens
                .peek_token(line_num, should_stop)?
                .unwrap_or("<end of line>")
                .to_string();
            return Err(ParseError::ExpectedLiteral {
                line: line_num,
                found,
            });
        }

        terms.push(PbTerm { coeff, lits });
    }

    Ok(terms)
}

/// Try to parse a token as a literal. Returns None if it's not a literal.
fn try_parse_literal(token: &str) -> Option<PbLit> {
    let (negated, rest) = if let Some(rest) = token.strip_prefix('~') {
        (true, rest)
    } else {
        (false, token)
    };
    let var = parse_u32_ascii(rest.strip_prefix('x')?)?;
    if var == 0 {
        return None;
    }
    Some(PbLit { var, negated })
}

/// Parse a token as an i128, reporting overflow on failure.
fn parse_i64_token(token: &str, line_num: usize) -> Result<i128, ParseError> {
    let token = token.trim();
    // Handle explicit '+' prefix
    let normalized = token.strip_prefix('+').unwrap_or(token);
    match parse_i64_ascii(normalized) {
        Some(value) => Ok(value),
        None => {
            // Distinguish overflow from non-integer.
            if normalized.chars().all(|c| c.is_ascii_digit() || c == '-') && !normalized.is_empty()
            {
                Err(ParseError::CoefficientOverflow {
                    line: line_num,
                    token: token.to_string(),
                })
            } else {
                Err(ParseError::ExpectedInteger {
                    line: line_num,
                    found: token.to_string(),
                })
            }
        }
    }
}

fn parse_u32_ascii(s: &str) -> Option<u32> {
    let mut value = 0u32;
    let mut saw_digit = false;
    for byte in s.bytes() {
        if !byte.is_ascii_digit() {
            return None;
        }
        saw_digit = true;
        let digit = u32::from(byte - b'0');
        value = value.checked_mul(10)?.checked_add(digit)?;
    }
    saw_digit.then_some(value)
}

fn parse_i64_ascii(s: &str) -> Option<i128> {
    let bytes = s.as_bytes();
    let (negative, digits) = match bytes.first().copied() {
        Some(b'-') => (true, &bytes[1..]),
        Some(_) => (false, bytes),
        None => return None,
    };
    if digits.is_empty() {
        return None;
    }

    // Symmetric magnitude cap at i128::MAX for BOTH signs: i128::MIN is
    // deliberately rejected (classified as an unsupported coefficient by the
    // caller). Every downstream normalization negates coefficients (`<=` row
    // flips, objective-improving rows, dual bounds), and `-i128::MIN`
    // overflows — with overflow checks on, that is a mid-solve panic (an
    // instance with objective coefficient i128::MIN panicked in
    // unified_score); with them off it would be silent wraparound. A value
    // whose negation does not exist in the domain is not supportable.
    let limit = i128::MAX as u128;
    let mut value = 0u128;
    for &byte in digits {
        if !byte.is_ascii_digit() {
            return None;
        }
        let digit = u128::from(byte - b'0');
        if value > (limit - digit) / 10 {
            return None;
        }
        value = value * 10 + digit;
    }

    if negative {
        Some(-(value as i128))
    } else {
        Some(value as i128)
    }
}

/// Parse the `[cost]` prefix of a soft constraint. Returns (cost, rest_of_line).
fn parse_soft_prefix_interruptible<'a, F>(
    line: &'a str,
    line_num: usize,
    should_stop: &mut F,
) -> Result<(i128, &'a str), ParseError>
where
    F: FnMut() -> bool,
{
    let bytes = line.as_bytes();
    let mut poll_counter = 0;
    let mut close_bracket = None;
    for (idx, &byte) in bytes.iter().enumerate() {
        poll_parse_stop(should_stop, line_num, &mut poll_counter)?;
        if byte == b']' {
            close_bracket = Some(idx);
            break;
        }
    }
    let close_bracket = close_bracket.ok_or(ParseError::Generic {
        line: line_num,
        message: "missing ']' in soft constraint weight".to_string(),
    })?;
    let cost_str = &line[1..close_bracket];
    let cost = parse_i64_token(cost_str.trim(), line_num)?;
    let rest = line[close_bracket + 1..].trim();
    Ok((cost, rest))
}

fn poll_parse_stop<F>(
    should_stop: &mut F,
    line_num: usize,
    poll_counter: &mut usize,
) -> Result<(), ParseError>
where
    F: FnMut() -> bool,
{
    *poll_counter = poll_counter.wrapping_add(1);
    if *poll_counter == 1 || *poll_counter >= PARSE_STOP_POLL_INTERVAL {
        *poll_counter = 0;
        if should_stop() {
            return Err(ParseError::Interrupted { line: line_num });
        }
    }
    Ok(())
}

struct TokenCursor<'a> {
    input: &'a str,
    pos: usize,
    peeked: Option<&'a str>,
    poll_counter: usize,
}

impl<'a> TokenCursor<'a> {
    fn new(input: &'a str) -> Self {
        Self {
            input,
            pos: 0,
            peeked: None,
            poll_counter: 0,
        }
    }

    fn next_token<F>(
        &mut self,
        line_num: usize,
        should_stop: &mut F,
    ) -> Result<Option<&'a str>, ParseError>
    where
        F: FnMut() -> bool,
    {
        if let Some(token) = self.peeked.take() {
            return Ok(Some(token));
        }
        self.scan_next_token(line_num, should_stop)
    }

    fn peek_token<F>(
        &mut self,
        line_num: usize,
        should_stop: &mut F,
    ) -> Result<Option<&'a str>, ParseError>
    where
        F: FnMut() -> bool,
    {
        if self.peeked.is_none() {
            self.peeked = self.scan_next_token(line_num, should_stop)?;
        }
        Ok(self.peeked)
    }

    fn scan_next_token<F>(
        &mut self,
        line_num: usize,
        should_stop: &mut F,
    ) -> Result<Option<&'a str>, ParseError>
    where
        F: FnMut() -> bool,
    {
        let bytes = self.input.as_bytes();
        while self.pos < bytes.len() && bytes[self.pos].is_ascii_whitespace() {
            poll_parse_stop(should_stop, line_num, &mut self.poll_counter)?;
            self.pos = self.pos.saturating_add(1);
        }
        if self.pos >= bytes.len() {
            return Ok(None);
        }

        let start = self.pos;
        while self.pos < bytes.len() && !bytes[self.pos].is_ascii_whitespace() {
            poll_parse_stop(should_stop, line_num, &mut self.poll_counter)?;
            self.pos = self.pos.saturating_add(1);
        }
        Ok(Some(&self.input[start..self.pos]))
    }
}

/// Infer the maximum variable index from all constraints and objective.
fn infer_max_var_constraints(constraints: &[PbConstraint], objective: &Option<PbObjective>) -> u32 {
    let mut max_var: u32 = 0;
    for c in constraints {
        for term in &c.terms {
            for lit in &term.lits {
                max_var = max_var.max(lit.var);
            }
        }
    }
    if let Some(obj) = objective {
        for term in &obj.terms {
            for lit in &term.lits {
                max_var = max_var.max(lit.var);
            }
        }
    }
    max_var
}

/// Infer the maximum variable index from a WBO instance.
fn infer_max_var_wbo(
    hard: &[PbConstraint],
    soft: &[(i128, PbConstraint)],
    objective: &Option<PbObjective>,
) -> u32 {
    let mut max_var: u32 = 0;
    for c in hard {
        for term in &c.terms {
            for lit in &term.lits {
                max_var = max_var.max(lit.var);
            }
        }
    }
    for (_, c) in soft {
        for term in &c.terms {
            for lit in &term.lits {
                max_var = max_var.max(lit.var);
            }
        }
    }
    if let Some(obj) = objective {
        for term in &obj.terms {
            for lit in &term.lits {
                max_var = max_var.max(lit.var);
            }
        }
    }
    max_var
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fmt::Write as _;

    #[test]
    fn test_parse_opb_bounds_variable_dimension_without_oom() {
        // A PB solution assignment is defined over the declared variable set, so
        // `num_vars` is the real output dimension. A value that would require a
        // hundreds-of-GB assignment + per-variable arrays is refused rather than
        // allocated (whether it comes from the `#variable=` header or, as here,
        // from an explicitly-used high variable index).
        let err = parse_opb("* #constraint= 1\n+1 x300000000 >= 1 ;\n")
            .expect_err("a variable dimension of 3e8 must be refused");
        assert!(
            matches!(err, ParseError::VariableCountUnsupported { .. }),
            "expected VariableCountUnsupported (drivers map it to s UNSUPPORTED), got {err:?}"
        );
        // A normal instance still parses, with the assignment dimension preserved.
        let ok = parse_opb("* #variable= 4 #constraint= 1\n+1 x1 >= 1 ;\n")
            .expect("normal instance must parse");
        assert_eq!(ok.num_vars, 4, "declared assignment dimension is preserved");
    }

    #[test]
    fn test_parse_opb_simple_constraint() {
        let input = "* comment\n+1 x1 +2 x2 >= 3 ;\n";
        let result = parse_opb(input).expect("should parse");
        assert_eq!(result.constraints.len(), 1);
        let c = &result.constraints[0];
        assert_eq!(c.terms.len(), 2);
        assert_eq!(c.terms[0].coeff, 1);
        assert_eq!(c.terms[0].lits[0].var, 1);
        assert!(!c.terms[0].lits[0].negated);
        assert_eq!(c.terms[1].coeff, 2);
        assert_eq!(c.terms[1].lits[0].var, 2);
        assert_eq!(c.rel, PbRel::Ge);
        assert_eq!(c.rhs, 3);
    }

    #[test]
    fn test_parse_opb_fast_single_linear_constraint() {
        let input = "* #variable= 2 #constraint= 1\n+7 ~x2 >= -3 ;\n";
        let result = parse_opb(input).expect("should parse fast single-literal row");

        assert_eq!(result.num_vars, 2);
        assert_eq!(result.constraints.len(), 1);
        let c = &result.constraints[0];
        assert_eq!(c.terms.len(), 1);
        assert_eq!(c.terms[0].coeff, 7);
        assert_eq!(c.terms[0].lits.len(), 1);
        assert_eq!(c.terms[0].lits[0].var, 2);
        assert!(c.terms[0].lits[0].negated);
        assert_eq!(c.rel, PbRel::Ge);
        assert_eq!(c.rhs, -3);
    }

    #[test]
    fn test_parse_opb_equality() {
        let input = "+1 x1 -1 x2 = 0 ;\n";
        let result = parse_opb(input).expect("should parse");
        assert_eq!(result.constraints.len(), 1);
        let c = &result.constraints[0];
        assert_eq!(c.terms[0].coeff, 1);
        assert_eq!(c.terms[1].coeff, -1);
        assert_eq!(c.rel, PbRel::Eq);
        assert_eq!(c.rhs, 0);
    }

    #[test]
    fn test_parse_opb_less_equal_canonicalizes_fast_linear_row() {
        let input = "+1 x1 -2 x2 <= 3 ;\n";
        let result = parse_opb(input).expect("<= should parse");
        let c = &result.constraints[0];

        assert_eq!(c.rel, PbRel::Ge);
        assert_eq!(c.rhs, -3);
        assert_eq!(c.terms.len(), 2);
        assert_eq!(c.terms[0].coeff, -1);
        assert_eq!(c.terms[0].lits[0].var, 1);
        assert_eq!(c.terms[1].coeff, 2);
        assert_eq!(c.terms[1].lits[0].var, 2);
    }

    #[test]
    fn test_parse_opb_less_equal_canonicalizes_nonlinear_row() {
        let input = "+3 x1 x2 -4 ~x3 <= -2 ;\n";
        let result = parse_opb(input).expect("nonlinear <= should parse");
        let c = &result.constraints[0];

        assert_eq!(c.rel, PbRel::Ge);
        assert_eq!(c.rhs, 2);
        assert_eq!(c.terms.len(), 2);
        assert_eq!(c.terms[0].coeff, -3);
        assert_eq!(c.terms[0].lits.len(), 2);
        assert_eq!(c.terms[1].coeff, 4);
        assert!(c.terms[1].lits[0].negated);
    }

    #[test]
    fn test_parse_opb_nonlinear_product_rows_use_general_sum_path() {
        let mut input = String::from("* #variable= 64 #constraint= 1\n");
        for var in 1..=64 {
            write!(&mut input, "+1 x{} x{} ", var, 65 - var).unwrap();
        }
        input.push_str(">= 1 ;\n");

        let result = parse_opb(&input).expect("nonlinear product row should parse");
        let c = &result.constraints[0];

        assert_eq!(c.terms.len(), 64);
        assert!(c.terms.iter().all(|term| term.coeff == 1));
        assert!(c.terms.iter().all(|term| term.lits.len() == 2));
        assert_eq!(c.rel, PbRel::Ge);
        assert_eq!(c.rhs, 1);
    }

    #[test]
    fn test_parse_opb_less_equal_overflow_fails_as_unsupported() {
        let rhs_min = "+1 x1 <= -170141183460469231731687303715884105728 ;\n";
        let err = parse_opb(rhs_min).expect_err("negating i128::MIN rhs is unsupported");
        assert!(err.is_unsupported_coefficient());
        assert_eq!(err.line(), 1);

        let coeff_min = "-170141183460469231731687303715884105728 x1 <= 0 ;\n";
        let err = parse_opb(coeff_min).expect_err("negating i128::MIN coeff is unsupported");
        assert!(err.is_unsupported_coefficient());
        assert_eq!(err.line(), 1);
    }

    #[test]
    fn test_parse_opb_negated_literal() {
        let input = "+1 ~x1 +1 x2 >= 1 ;\n";
        let result = parse_opb(input).expect("should parse");
        let c = &result.constraints[0];
        assert!(c.terms[0].lits[0].negated);
        assert_eq!(c.terms[0].lits[0].var, 1);
        assert!(!c.terms[1].lits[0].negated);
    }

    #[test]
    fn test_parse_opb_with_objective() {
        let input = "min: +1 x1 +2 x2 ;\n+1 x1 +1 x2 >= 1 ;\n";
        let result = parse_opb(input).expect("should parse");
        assert!(result.objective.is_some());
        let obj = result.objective.as_ref().unwrap();
        assert_eq!(obj.terms.len(), 2);
        assert_eq!(obj.terms[0].coeff, 1);
        assert_eq!(obj.terms[1].coeff, 2);
    }

    #[test]
    fn test_parse_opb_objective_requires_semicolon() {
        let input = "min: +1 x1 +2 x2\n+1 x1 +1 x2 >= 1 ;\n";
        let err = parse_opb(input).expect_err("objective must require semicolon");
        assert!(matches!(err, ParseError::ExpectedSemicolon { line: 1 }));
    }

    #[test]
    fn test_parse_opb_fast_linear_objective() {
        let input = "min: +3 x1 -5 ~x2 +7 x3 ;\n+1 x1 >= 1 ;\n";
        let result = parse_opb(input).expect("should parse fast linear objective");

        let obj = result.objective.as_ref().expect("objective should parse");
        assert_eq!(obj.terms.len(), 3);
        assert_eq!(obj.terms[0].coeff, 3);
        assert_eq!(obj.terms[0].lits[0].var, 1);
        assert!(!obj.terms[0].lits[0].negated);
        assert_eq!(obj.terms[1].coeff, -5);
        assert_eq!(obj.terms[1].lits[0].var, 2);
        assert!(obj.terms[1].lits[0].negated);
        assert_eq!(obj.terms[2].coeff, 7);
        assert_eq!(obj.terms[2].lits[0].var, 3);
    }

    #[test]
    fn test_parse_opb_large_fast_linear_objective_and_row() {
        const TERMS: usize = 4_096;

        let mut input = String::from("* #variable= 4096 #constraint= 1\nmin:");
        for var in 1..=TERMS {
            let coeff = (var % 17) + 1;
            write!(&mut input, " +{coeff} x{var}").unwrap();
        }
        input.push_str(" ;\n");
        for var in 1..=TERMS {
            write!(&mut input, " +1 x{var}").unwrap();
        }
        input.push_str(" <= 2048 ;\n");

        let result = parse_opb(&input).expect("large fast-linear OPB should parse");
        let obj = result.objective.as_ref().expect("objective should parse");
        assert_eq!(obj.terms.len(), TERMS);
        assert_eq!(obj.terms[0].coeff, 2);
        assert_eq!(obj.terms[0].lits[0].var, 1);
        assert_eq!(obj.terms[TERMS - 1].coeff, 17);
        assert_eq!(obj.terms[TERMS - 1].lits[0].var, TERMS as u32);

        assert_eq!(result.constraints.len(), 1);
        let row = &result.constraints[0];
        assert_eq!(row.rel, PbRel::Ge);
        assert_eq!(row.rhs, -2048);
        assert_eq!(row.terms.len(), TERMS);
        assert_eq!(row.terms[0].coeff, -1);
        assert_eq!(row.terms[0].lits[0].var, 1);
        assert_eq!(row.terms[TERMS - 1].coeff, -1);
        assert_eq!(row.terms[TERMS - 1].lits[0].var, TERMS as u32);
    }

    #[test]
    fn test_parse_opb_header() {
        let input = "* #variable= 5 #constraint= 3\n+1 x1 >= 1 ;\n";
        let result = parse_opb(input).expect("should parse");
        assert_eq!(result.num_vars, 5);
        assert_eq!(result.num_constraints, 3);
    }

    #[test]
    fn test_parse_opb_nonlinear() {
        let input = "+1 x1 x2 +2 x3 >= 1 ;\n";
        let result = parse_opb(input).expect("should parse");
        let c = &result.constraints[0];
        assert_eq!(c.terms.len(), 2);
        // First term is non-linear: x1 * x2
        assert_eq!(c.terms[0].lits.len(), 2);
        assert_eq!(c.terms[0].lits[0].var, 1);
        assert_eq!(c.terms[0].lits[1].var, 2);
        assert_eq!(c.terms[0].coeff, 1);
        // Second term is linear
        assert_eq!(c.terms[1].lits.len(), 1);
        assert_eq!(c.terms[1].lits[0].var, 3);
    }

    #[test]
    fn test_parse_opb_infer_num_vars() {
        let input = "+1 x5 +1 x3 >= 1 ;\n";
        let result = parse_opb(input).expect("should parse");
        assert_eq!(result.num_vars, 5);
    }

    #[test]
    fn test_parse_opb_negative_rhs() {
        let input = "+1 x1 >= -5 ;\n";
        let result = parse_opb(input).expect("should parse");
        assert_eq!(result.constraints[0].rhs, -5);
    }

    #[test]
    fn test_parse_opb_missing_semicolon() {
        let input = "+1 x1 >= 1\n";
        let result = parse_opb(input);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(matches!(err, ParseError::ExpectedSemicolon { line: 1 }));
    }

    #[test]
    fn test_parse_opb_overflow() {
        // i128::MAX + 1
        let input = "+1 x1 >= 170141183460469231731687303715884105728 ;\n";
        let result = parse_opb(input);
        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            ParseError::CoefficientOverflow { .. }
        ));
    }

    #[test]
    fn test_fast_ascii_integer_parser_boundaries() {
        // Symmetric magnitude cap: ±i128::MAX parse exactly at the supported
        // edge; i128::MIN is DELIBERATELY rejected (its negation overflows,
        // and every downstream normalization negates — see parse_i64_ascii).
        assert_eq!(
            parse_i64_token("+170141183460469231731687303715884105727", 1),
            Ok(i128::MAX)
        );
        assert_eq!(
            parse_i64_token("-170141183460469231731687303715884105727", 1),
            Ok(-i128::MAX)
        );
        assert!(matches!(
            parse_i64_token("-170141183460469231731687303715884105728", 1),
            Err(ParseError::CoefficientOverflow { .. })
        ));
        // i128::MAX + 1 must overflow.
        assert!(matches!(
            parse_i64_token("170141183460469231731687303715884105728", 1),
            Err(ParseError::CoefficientOverflow { .. })
        ));
        assert!(matches!(
            parse_i64_token("12x", 1),
            Err(ParseError::ExpectedInteger { .. })
        ));
    }

    #[test]
    fn test_fast_ascii_literal_parser_rejects_bad_or_overflow_var() {
        assert_eq!(
            try_parse_literal("~x4294967295"),
            Some(PbLit {
                var: u32::MAX,
                negated: true
            })
        );
        assert_eq!(try_parse_literal("x0"), None);
        assert_eq!(try_parse_literal("x4294967296"), None);
        assert_eq!(try_parse_literal("x12y"), None);
    }

    #[test]
    fn test_parse_opb_byte_fast_path_deviations_fall_back_identically() {
        // 20+ digit coefficient: beyond the byte cursor's u64 fast range but a
        // valid i128 — must deviate to the token path and parse exactly.
        let big = "+12345678901234567890 x1 >= 12345678901234567890 ;\n";
        let result = parse_opb(big).expect("20-digit i128 coeff must still parse");
        assert_eq!(
            result.constraints[0].terms[0].coeff,
            12_345_678_901_234_567_890
        );
        assert_eq!(result.constraints[0].rhs, 12_345_678_901_234_567_890);

        // Max u32 variable index (10 digits) scans on the fast path and is
        // refused by the SAME instance-level variable-dimension cap as before
        // (not a literal-level syntax error).
        let maxvar = "+1 ~x4294967295 >= 1 ;\n";
        let err = parse_opb(maxvar).expect_err("u32::MAX var exceeds the dimension cap");
        assert!(matches!(
            err,
            ParseError::VariableCountUnsupported {
                count: u32::MAX,
                ..
            }
        ));

        // Overflowing variable index: deviates all the way to the general
        // parser and errors as a missing literal, exactly as before.
        let overvar = "+1 x4294967296 >= 1 ;\n";
        let err = parse_opb(overvar).expect_err("over-u32 var index must error");
        assert!(matches!(err, ParseError::ExpectedLiteral { line: 1, .. }));

        // Operator glued to the rhs: the byte and token fast paths deviate;
        // the general parser's reverse relop scan ACCEPTS this shape (as it
        // always has), so the row still parses with rhs 3.
        let glued = "+1 x1 >=3 ;\n";
        let result = parse_opb(glued).expect("glued >=3 parses via the general path as before");
        assert_eq!(result.constraints[0].rel, PbRel::Ge);
        assert_eq!(result.constraints[0].rhs, 3);

        // Mixed tab/space separators stay on the fast path.
        let tabs = "+2\tx1 \t +3 x2\t>=\t1 ;\n";
        let result = parse_opb(tabs).expect("tab-separated row must parse");
        assert_eq!(result.constraints[0].terms.len(), 2);
        assert_eq!(result.constraints[0].terms[1].coeff, 3);
        assert_eq!(result.constraints[0].rhs, 1);

        // Trailing junk after the rhs deviates and errors as before.
        let junk = "+1 x1 >= 1 x9 ;\n";
        let err = parse_opb(junk).expect_err("trailing junk must error");
        assert!(matches!(err, ParseError::ExpectedInteger { line: 1, .. }));
    }

    #[test]
    fn test_parse_opb_byte_fast_path_min_i128_rhs_still_exact() {
        // -i128::MAX (39 digits, beyond the byte fast range) must deviate and
        // parse exactly via the token path.
        let input = "+1 x1 >= -170141183460469231731687303715884105727 ;\n";
        let result = parse_opb(input).expect("-i128::MAX rhs must parse");
        assert_eq!(result.constraints[0].rhs, -i128::MAX);
    }

    #[test]
    fn test_parse_opb_rejects_i128_min_as_unsupported() {
        // i128::MIN is DELIBERATELY unsupported (symmetric magnitude cap):
        // every downstream normalization negates coefficients/rhs values, and
        // `-i128::MIN` overflows — with overflow checks on, that is a
        // mid-solve panic (observed in unified_score on an objective
        // coefficient of i128::MIN). The parse must classify it as an
        // unsupported coefficient so the driver emits `s UNSUPPORTED`.
        for input in [
            "+1 x1 >= -170141183460469231731687303715884105728 ;\n",
            "-170141183460469231731687303715884105728 x1 >= 1 ;\n",
            "min: -170141183460469231731687303715884105728 x1 ;\n+1 x1 >= 0 ;\n",
        ] {
            let err = parse_opb(input).expect_err("i128::MIN must not parse");
            assert!(
                err.is_unsupported_coefficient(),
                "i128::MIN must classify as unsupported for s UNSUPPORTED: {err:?}"
            );
        }
    }

    #[test]
    fn test_parse_wbo_basic() {
        let input = "\
soft: 10 ;
[5] +1 x1 +1 x2 >= 1 ;
+1 x1 >= 1 ;
";
        let result = parse_wbo(input).expect("should parse");
        assert_eq!(result.top_cost, Some(10));
        assert_eq!(result.hard_constraints.len(), 1);
        assert_eq!(result.soft_constraints.len(), 1);
        assert_eq!(result.soft_constraints[0].0, 5);
    }

    #[test]
    fn test_parse_wbo_soft_decl_requires_semicolon() {
        let input = "soft: 10\n[5] +1 x1 >= 1 ;\n";
        let err = parse_wbo(input).expect_err("soft declaration must require semicolon");
        assert!(matches!(err, ParseError::ExpectedSemicolon { line: 1 }));
    }

    #[test]
    fn test_parse_wbo_omitted_top_cost_means_no_bound() {
        // The official grammar makes the integer optional: "soft: ;" means
        // there is no top-cost bound (T = infinity).
        let input = "soft: ;\n[5] +1 x1 >= 1 ;\n+1 x1 >= 1 ;\n";
        let result = parse_wbo(input).expect("omitted top cost should parse");
        assert_eq!(result.top_cost, None);
        assert_eq!(result.hard_constraints.len(), 1);
        assert_eq!(result.soft_constraints.len(), 1);
    }

    #[test]
    fn test_parse_wbo_zero_top_cost_is_preserved() {
        let input = "soft: 0 ;\n[5] +1 x1 >= 1 ;\n";
        let result = parse_wbo(input).expect("zero top cost should parse");
        assert_eq!(result.top_cost, Some(0));
    }

    #[test]
    fn test_variable_count_over_cap_is_unsupported_not_generic() {
        // Drivers map unsupported-input parse errors to `s UNSUPPORTED`; a
        // generic error would exit with no s line at all.
        let opb = parse_opb("* #variable= 400000000 #constraint= 1\n+1 x1 >= 1 ;\n")
            .expect_err("over-cap OPB variable count should be refused");
        assert!(matches!(
            opb,
            ParseError::VariableCountUnsupported {
                count: 400_000_000,
                ..
            }
        ));
        assert!(opb.is_unsupported_input());

        let wbo = parse_wbo("* #variable= 400000000\nsoft: 10 ;\n[5] +1 x1 >= 1 ;\n")
            .expect_err("over-cap WBO variable count should be refused");
        assert!(wbo.is_unsupported_input());
    }

    #[test]
    fn test_parse_wbo_num_vars_covers_variables_beyond_header() {
        // An understated "#variable=" header must not shrink the variable
        // space: relaxation variables are allocated at num_vars + 1, so a
        // trusted-but-wrong header would alias an in-use variable.
        let input = "\
* #variable= 2 #constraint= 2
soft: 10 ;
+1 x3 >= 1 ;
[5] +1 x1 >= 1 ;
";
        let result = parse_wbo(input).expect("should parse");
        assert_eq!(result.num_vars, 3);
    }

    #[test]
    fn test_parse_wbo_with_comments() {
        let input = "\
* header comment
* #variable= 3 #constraint= 2
soft: 100 ;
* another comment
[10] +1 x1 +1 x2 >= 1 ;
+1 x3 >= 1 ;
";
        let result = parse_wbo(input).expect("should parse");
        assert_eq!(result.top_cost, Some(100));
        assert_eq!(result.num_vars, 3);
        assert_eq!(result.soft_constraints.len(), 1);
        assert_eq!(result.hard_constraints.len(), 1);
    }

    #[test]
    fn test_parse_wbo_missing_soft_decl() {
        let input = "+1 x1 >= 1 ;\n";
        let result = parse_wbo(input);
        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            ParseError::ExpectedSoftDecl { .. }
        ));
    }

    #[test]
    fn test_parse_wbo_rejects_explicit_objective() {
        let input = "soft: 10 ;\nmin: +1 x1 ;\n[5] +1 x1 >= 1 ;\n";
        let err = parse_wbo(input).expect_err("WBO objective should be rejected");
        assert!(matches!(
            err,
            ParseError::WboObjectiveUnsupported { line: 2 }
        ));
        assert!(err
            .to_string()
            .contains("WBO instances do not allow explicit 'min:' objectives"));
    }

    #[test]
    fn test_parse_wbo_less_equal_hard_and_soft_constraints() {
        let input = "soft: 10 ;\n+1 x1 <= 0 ;\n[5] +2 x2 <= 1 ;\n";
        let result = parse_wbo(input).expect("WBO <= rows should parse");

        assert_eq!(result.hard_constraints.len(), 1);
        assert_eq!(result.hard_constraints[0].rel, PbRel::Ge);
        assert_eq!(result.hard_constraints[0].rhs, 0);
        assert_eq!(result.hard_constraints[0].terms[0].coeff, -1);

        assert_eq!(result.soft_constraints.len(), 1);
        let (cost, soft) = &result.soft_constraints[0];
        assert_eq!(*cost, 5);
        assert_eq!(soft.rel, PbRel::Ge);
        assert_eq!(soft.rhs, -1);
        assert_eq!(soft.terms[0].coeff, -2);
    }

    #[test]
    fn test_parse_opb_large_instance() {
        // Generate a moderate-size instance
        let mut lines = Vec::new();
        lines.push("* #variable= 100 #constraint= 50".to_string());
        lines.push("min: +1 x1 +1 x2 +1 x3 ;".to_string());
        for i in 0..50 {
            let v1 = (i % 100) + 1;
            let v2 = ((i + 1) % 100) + 1;
            lines.push(format!("+1 x{v1} +1 x{v2} >= 1 ;"));
        }
        let input = lines.join("\n");
        let result = parse_opb(&input).expect("should parse");
        assert_eq!(result.constraints.len(), 50);
        assert_eq!(result.num_vars, 100);
        assert!(result.objective.is_some());
    }

    #[test]
    fn test_parse_opb_empty_input() {
        let result = parse_opb("").expect("should parse empty");
        assert_eq!(result.constraints.len(), 0);
        assert!(result.objective.is_none());
        assert_eq!(result.num_vars, 0);
    }

    #[test]
    fn test_parse_opb_only_comments() {
        let input = "* comment 1\n* comment 2\n";
        let result = parse_opb(input).expect("should parse");
        assert_eq!(result.constraints.len(), 0);
    }

    #[test]
    fn test_parse_opb_nonlinear_with_negation() {
        let input = "+3 x1 ~x2 x3 >= 2 ;\n";
        let result = parse_opb(input).expect("should parse");
        let c = &result.constraints[0];
        assert_eq!(c.terms[0].lits.len(), 3);
        assert!(!c.terms[0].lits[0].negated);
        assert!(c.terms[0].lits[1].negated);
        assert!(!c.terms[0].lits[2].negated);
        assert_eq!(c.terms[0].coeff, 3);
    }

    #[test]
    fn test_parse_opb_multiple_constraints() {
        let input = "\
* #variable= 4 #constraint= 3
+1 x1 +1 x2 >= 1 ;
+1 x3 +1 x4 >= 1 ;
+1 x1 +1 x3 = 1 ;
";
        let result = parse_opb(input).expect("should parse");
        assert_eq!(result.constraints.len(), 3);
        assert_eq!(result.constraints[0].rel, PbRel::Ge);
        assert_eq!(result.constraints[1].rel, PbRel::Ge);
        assert_eq!(result.constraints[2].rel, PbRel::Eq);
    }

    #[test]
    fn test_parse_opb_with_utf8_bom() {
        // Files saved by Windows editors may have a UTF-8 BOM (EF BB BF) at
        // the start. The parser must skip it to avoid mistaking it for part
        // of the first comment or constraint.
        let input = "\u{FEFF}* #variable= 1 #constraint= 1\n+1 x1 >= 1 ;\n";
        let result = parse_opb(input).expect("should parse BOM-prefixed input");
        assert_eq!(result.num_vars, 1);
        assert_eq!(result.constraints.len(), 1);
    }

    #[test]
    fn test_parse_wbo_with_utf8_bom() {
        let input = "\u{FEFF}soft: 10 ;\n+1 x1 >= 1 ;\n[5] +1 x2 >= 1 ;\n";
        let result = parse_wbo(input).expect("should parse BOM-prefixed WBO");
        assert_eq!(result.top_cost, Some(10));
        assert_eq!(result.hard_constraints.len(), 1);
        assert_eq!(result.soft_constraints.len(), 1);
    }

    #[test]
    fn test_parse_opb_with_crlf_line_endings() {
        // Files from Windows may use \r\n. Rust's str::lines() handles both,
        // but trim() in the parser also removes any stray \r.
        let input = "* header\r\n+1 x1 +1 x2 >= 1 ;\r\n+1 x3 = 1 ;\r\n";
        let result = parse_opb(input).expect("should parse CRLF input");
        assert_eq!(result.constraints.len(), 2);
        assert_eq!(result.constraints[0].rel, PbRel::Ge);
        assert_eq!(result.constraints[1].rel, PbRel::Eq);
    }

    #[test]
    fn test_parse_error_line_and_classification_helpers() {
        // A syntactically-valid coefficient that overflows i128 must be
        // reported via a dedicated error kind and must be classifiable as an
        // "unsupported coefficient" so the caller can emit s UNSUPPORTED.
        let input = "+1 x1 >= 0\n+1 x1 +170141183460469231731687303715884105728 x2 >= 1 ;\n";
        let err = parse_opb(input).unwrap_err();
        // First error we hit is the missing semicolon on line 1.
        assert_eq!(err.line(), 1);
        assert!(matches!(err, ParseError::ExpectedSemicolon { .. }));
        assert!(!err.is_unsupported_coefficient());

        let overflow_input = "+170141183460469231731687303715884105728 x1 >= 1 ;\n";
        let err = parse_opb(overflow_input).unwrap_err();
        assert!(err.is_unsupported_coefficient());
        assert_eq!(err.line(), 1);
    }

    #[test]
    fn test_parse_opb_trailing_whitespace_after_semicolon() {
        // Some corpus files pad constraint lines with trailing spaces/tabs
        // between the `;` and the newline. The leading line trim handles
        // it, but the suffix of `;` is only found if there is no trailing
        // whitespace before `;` — the trim() keeps the string up to and
        // including `;`. Verify the common case works.
        let input = "+1 x1 >= 1 ;   \n+1 x2 = 1 ;\t\n";
        let result = parse_opb(input).expect("should parse trailing-whitespace input");
        assert_eq!(result.constraints.len(), 2);
    }

    #[test]
    fn test_parse_opb_only_header_then_instance() {
        // Real PB25 files typically start with a long header block of
        // comments describing the encoding, then the instance. Confirm a
        // representative shape parses.
        let input = "\
* Instance family: pigeonhole
* Problem: at-least-1 for each pigeon
* #variable= 3 #constraint= 3 intsize= 1
+1 x1 +1 x2 +1 x3 >= 1 ;
+1 ~x1 >= 0 ;
+1 ~x2 >= 0 ;
";
        let result = parse_opb(input).expect("should parse annotated header");
        assert_eq!(result.num_vars, 3);
        assert_eq!(result.num_constraints, 3);
        assert_eq!(result.constraints.len(), 3);
    }

    #[test]
    fn test_parse_opb_huge_constraint_header_preallocation_is_fail_soft() {
        let input = "\
* #variable= 1 #constraint= 4294967295
+1 x1 >= 1 ;
";
        let result = parse_opb(input).expect("huge header count should not make parsing fail");

        assert_eq!(result.num_vars, 1);
        assert_eq!(result.num_constraints, u32::MAX);
        assert_eq!(result.constraints.len(), 1);
    }

    #[test]
    fn test_parse_wbo_huge_constraint_header_preallocation_is_fail_soft() {
        let input = "\
* #variable= 2 #constraint= 4294967295
soft: 10 ;
[5] +1 x1 >= 1 ;
+1 x2 >= 1 ;
";
        let result = parse_wbo(input).expect("huge WBO header count should not make parsing fail");

        assert_eq!(result.num_vars, 2);
        assert_eq!(result.top_cost, Some(10));
        assert_eq!(result.soft_constraints.len(), 1);
        assert_eq!(result.hard_constraints.len(), 1);
    }

    #[test]
    fn test_parse_opb_interruptible_stops_early() {
        let input = "* #variable= 1 #constraint= 1\n+1 x1 >= 1 ;\n";
        let result = parse_opb_interruptible(input, || true);

        assert!(matches!(result, Err(ParseError::Interrupted { line: 1 })));
    }

    #[test]
    fn test_parse_opb_interruptible_stops_while_scanning_large_sum_line() {
        let mut input = String::from("* #variable= 1 #constraint= 1\nmin:");
        for _ in 0..20_000 {
            input.push_str(" +1 x1");
        }
        input.push_str(" ;\n");

        let mut polls = 0;
        let result = parse_opb_interruptible(&input, || {
            polls += 1;
            polls >= 3
        });

        assert!(matches!(result, Err(ParseError::Interrupted { line: 2 })));
        assert!(polls >= 3);
    }

    #[test]
    fn test_parse_opb_interruptible_stops_inside_large_fast_linear_objective() {
        let mut input = String::from("min:");
        for _ in 0..20_000 {
            input.push_str(" +1 x1");
        }
        input.push_str(" ;\n");

        let mut polls = 0;
        let result = parse_opb_interruptible(&input, || {
            polls += 1;
            polls >= 3
        });

        assert!(matches!(result, Err(ParseError::Interrupted { line: 1 })));
        assert!(polls >= 3);
    }

    #[test]
    fn test_parse_opb_interruptible_stops_on_fast_linear_constraint() {
        let mut input = String::from("* #variable= 1 #constraint= 1\n");
        for _ in 0..20_000 {
            input.push_str("+1 x1 ");
        }
        input.push_str(">= 1 ;\n");

        let mut polls = 0;
        let result = parse_opb_interruptible(&input, || {
            polls += 1;
            polls >= 3
        });

        assert!(matches!(result, Err(ParseError::Interrupted { line: 2 })));
        assert!(polls >= 3);
    }

    #[test]
    fn test_parse_wbo_representative_corpus_shape() {
        // Shape mimicking a small corpus WBO: annotated header, min objective
        // absent, mixed hard/soft with varying coefficient sizes.
        let input = "\
* #variable= 4 #constraint= 4
* WBO mini corpus
soft: 100 ;
+1 x1 +1 x2 >= 1 ;
+1 x3 +1 x4 >= 1 ;
[7] +1 ~x1 >= 1 ;
[3] +1 ~x3 +1 ~x4 >= 1 ;
";
        let result = parse_wbo(input).expect("corpus-like WBO parses");
        assert_eq!(result.num_vars, 4);
        assert_eq!(result.top_cost, Some(100));
        assert_eq!(result.hard_constraints.len(), 2);
        assert_eq!(result.soft_constraints.len(), 2);
        assert_eq!(result.soft_constraints[0].0, 7);
        assert_eq!(result.soft_constraints[1].0, 3);
    }

    #[test]
    fn test_strip_bom_helper_is_idempotent() {
        assert_eq!(strip_bom("hello"), "hello");
        assert_eq!(strip_bom("\u{FEFF}hello"), "hello");
        assert_eq!(strip_bom(""), "");
        // Only the first BOM is stripped.
        assert_eq!(strip_bom("\u{FEFF}\u{FEFF}hi"), "\u{FEFF}hi");
    }
}

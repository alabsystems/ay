// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::collections::BTreeMap;
use std::time::Duration;

use serde::{Deserialize, Serialize, Serializer};

use crate::{
    Domain, EnumerationResult, LinearExpr, Model, OptimizationResult, SearchError, SolveOptions,
    SolveResult,
};

/// Maximum UTF-8 byte length of one restricted SearchSpec equation.
pub const MAX_EXPRESSION_BYTES: usize = 65_536;
/// Maximum number of non-EOF tokens in one restricted SearchSpec equation.
pub const MAX_EXPRESSION_TOKENS: usize = 4_096;
/// Maximum number of solutions retained by untrusted SearchSpec execution.
/// Direct typed-Rust `Model::enumerate_all` remains an explicit trusted API.
pub const MAX_SEARCH_SPEC_SOLUTIONS: u64 = 10_000;
/// Maximum `solutions * variables` assignment cells retained and serialized by
/// one SearchSpec enumeration run.
pub const MAX_SEARCH_SPEC_RESULT_CELLS: u64 = 1_000_000;
/// Maximum conservative JSON byte size of a retained SearchSpec enumeration
/// result. The estimate accounts for every repeated assignment name and the
/// longest selectable label for each variable, including JSON escaping.
pub const MAX_SEARCH_SPEC_RESULT_BYTES: u64 = 16 * 1024 * 1024;
/// Maximum SMT-LIB bytes rendered by a SearchSpec compile request.
///
/// Table and element lowerings repeat variable names, so a compact JSON
/// document can otherwise amplify into a much larger output. Typed Rust
/// callers that intentionally need a larger rendering can use
/// [`Model::to_smt2`] directly.
pub const MAX_SEARCH_SPEC_SMT_BYTES: u64 = 16 * 1024 * 1024;

/// Portable JSON description of a finite-domain search problem.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SearchSpec {
    pub version: u32,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub name: Option<String>,
    pub variables: Vec<VariableSpec>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub constraints: Vec<ConstraintSpec>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub objective: Option<ObjectiveSpec>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub limits: Option<LimitsSpec>,
}

/// A named variable in a [`SearchSpec`].
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VariableSpec {
    pub name: String,
    pub domain: DomainSpec,
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub labels: BTreeMap<i64, String>,
}

/// JSON domain syntax: either `{ "min": ..., "max": ... }` or
/// `{ "values": [...] }`.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(untagged, deny_unknown_fields)]
pub enum DomainSpec {
    Interval { min: i64, max: i64 },
    Values { values: Vec<i64> },
}

/// Supported high-level constraint objects.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(untagged, deny_unknown_fields)]
pub enum ConstraintSpec {
    Expression { expression: String },
    AllDifferent { all_different: Vec<String> },
    Table { table: TableSpec },
    Element { element: ElementSpec },
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TableSpec {
    pub variables: Vec<String>,
    pub tuples: Vec<Vec<i64>>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ElementSpec {
    pub index: String,
    pub array: Vec<String>,
    pub result: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ObjectiveSense {
    Minimize,
    Maximize,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ObjectiveSpec {
    pub sense: ObjectiveSense,
    pub expression: String,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LimitsSpec {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub timeout_ms: Option<u64>,
    /// Select capped enumeration for satisfaction models. This cannot be
    /// combined with `objective`, which selects optimization. SearchSpec runs
    /// are capped by [`MAX_SEARCH_SPEC_SOLUTIONS`],
    /// [`MAX_SEARCH_SPEC_RESULT_CELLS`], and
    /// [`MAX_SEARCH_SPEC_RESULT_BYTES`]; trusted Rust callers can use the
    /// explicit `Model` enumeration methods directly.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub max_solutions: Option<u64>,
}

/// A validated, executable search specification.
#[derive(Debug)]
pub struct SearchProblem {
    name: Option<String>,
    model: Model,
    objective: Option<(ObjectiveSense, LinearExpr)>,
    limits: LimitsSpec,
}

/// Result selected by the specification: optimization when an objective is
/// present, enumeration when `max_solutions` is present, otherwise one solve.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum SearchRunResult {
    Solve(SolveResult),
    Enumeration(EnumerationResult),
    Optimization(OptimizationResult),
}

impl Serialize for SearchRunResult {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match self {
            Self::Solve(result) => result.serialize(serializer),
            Self::Enumeration(result) => result.serialize(serializer),
            Self::Optimization(result) => result.serialize(serializer),
        }
    }
}

impl SearchSpec {
    /// Parse JSON without accepting unknown fields or executable code.
    pub fn from_json(input: &str) -> Result<Self, SearchError> {
        Ok(serde_json::from_str(input)?)
    }

    /// Validate names/domains/references and parse the restricted expressions.
    pub fn build(&self) -> Result<SearchProblem, SearchError> {
        if self.version != 1 {
            return Err(SearchError::UnsupportedVersion(self.version));
        }
        let limits = self.limits.clone().unwrap_or_default();
        if limits.timeout_ms == Some(0) {
            return Err(SearchError::InvalidLimit {
                name: "timeout_ms",
                value: 0,
            });
        }
        if limits.max_solutions == Some(0) {
            return Err(SearchError::InvalidLimit {
                name: "max_solutions",
                value: 0,
            });
        }
        if let Some(max_solutions) = limits.max_solutions {
            if max_solutions > MAX_SEARCH_SPEC_SOLUTIONS {
                return Err(SearchError::InvalidLimit {
                    name: "max_solutions",
                    value: max_solutions,
                });
            }
            let cells = u128::from(max_solutions).saturating_mul(self.variables.len() as u128);
            if cells > u128::from(MAX_SEARCH_SPEC_RESULT_CELLS) {
                return Err(SearchError::EnumerationResultTooLarge {
                    cells,
                    limit: MAX_SEARCH_SPEC_RESULT_CELLS,
                });
            }
            let estimated_bytes =
                enumeration_result_json_upper_bound(&self.variables, max_solutions);
            if estimated_bytes > u128::from(MAX_SEARCH_SPEC_RESULT_BYTES) {
                return Err(SearchError::EnumerationOutputTooLarge {
                    estimated_bytes,
                    limit: MAX_SEARCH_SPEC_RESULT_BYTES,
                });
            }
        }
        if self.objective.is_some() && limits.max_solutions.is_some() {
            return Err(SearchError::ConflictingExecutionModes);
        }

        let mut model = Model::new();
        for variable in &self.variables {
            let domain = match &variable.domain {
                DomainSpec::Interval { min, max } => Domain::interval(*min, *max)?,
                DomainSpec::Values { values } => Domain::values(values.iter().copied())?,
            };
            let handle = model.int_var(variable.name.clone(), domain)?;
            for (&value, label) in &variable.labels {
                model.set_choice_label(handle, value, label.clone())?;
            }
        }

        for constraint in &self.constraints {
            match constraint {
                ConstraintSpec::Expression { expression } => {
                    let (lhs, relation, rhs) = parse_relation(expression, &model)?;
                    match relation {
                        ParsedRelation::Eq => model.eq(lhs, rhs)?,
                        ParsedRelation::Le => model.le(lhs, rhs)?,
                        ParsedRelation::Ge => model.ge(lhs, rhs)?,
                        ParsedRelation::Ne => model.ne(lhs, rhs)?,
                    }
                }
                ConstraintSpec::AllDifferent { all_different } => {
                    let variables = resolve_variables(all_different, &model)?;
                    model.all_different(&variables)?;
                }
                ConstraintSpec::Table { table } => {
                    let variables = resolve_variables(&table.variables, &model)?;
                    model.table(&variables, &table.tuples)?;
                }
                ConstraintSpec::Element { element } => {
                    let index = resolve_variable(&element.index, &model)?;
                    let array = resolve_variables(&element.array, &model)?;
                    let result = resolve_variable(&element.result, &model)?;
                    model.element(index, &array, result)?;
                }
            }
        }

        let objective = self
            .objective
            .as_ref()
            .map(|objective| {
                Ok::<_, SearchError>((
                    objective.sense,
                    parse_linear_expression(&objective.expression, &model)?,
                ))
            })
            .transpose()?;

        Ok(SearchProblem {
            name: self.name.clone(),
            model,
            objective,
            limits,
        })
    }

    /// Build and lower this specification to standalone SMT-LIB 2.
    pub fn to_smt2(&self) -> Result<String, SearchError> {
        self.build()?.to_smt2()
    }
}

/// Conservative byte bound for serde_json's compact serialization of an
/// enumeration result. Container constants intentionally include slack so a
/// future status spelling or punctuation adjustment cannot invalidate the
/// bound without a structural serialization change.
fn enumeration_result_json_upper_bound(variables: &[VariableSpec], max_solutions: u64) -> u128 {
    const RESULT_CONTAINER_BYTES: u128 = 64;
    const SOLUTION_CONTAINER_BYTES: u128 = 64;
    const I64_DECIMAL_BYTES: u128 = 20;

    let mut solution_bytes = SOLUTION_CONTAINER_BYTES;
    for variable in variables {
        let name_bytes = json_string_bytes(&variable.name);
        // Assignment map entry: quoted name, colon, signed i64, and a comma.
        solution_bytes = solution_bytes
            .saturating_add(name_bytes)
            .saturating_add(1 + I64_DECIMAL_BYTES + 1);

        // At most one choice label is selected for a variable in a solution.
        // Charge the longest possible serialized label plus the repeated name.
        if let Some(label_bytes) = variable
            .labels
            .values()
            .map(|label| json_string_bytes(label))
            .max()
        {
            solution_bytes = solution_bytes
                .saturating_add(name_bytes)
                .saturating_add(1)
                .saturating_add(label_bytes)
                .saturating_add(1);
        }
    }

    RESULT_CONTAINER_BYTES
        .saturating_add(u128::from(max_solutions).saturating_mul(solution_bytes.saturating_add(1)))
}

/// Exact compact serde_json string size for the escape set used by serde_json:
/// quotes/backslashes and five short control escapes take two bytes, remaining
/// ASCII controls take six, and all other UTF-8 bytes pass through unchanged.
fn json_string_bytes(value: &str) -> u128 {
    let content_bytes = value.as_bytes().iter().fold(0u128, |length, byte| {
        let escaped = match byte {
            b'"' | b'\\' | b'\x08' | b'\t' | b'\n' | b'\x0c' | b'\r' => 2,
            0x00..=0x1f => 6,
            _ => 1,
        };
        length.saturating_add(escaped)
    });
    content_bytes.saturating_add(2)
}

impl SearchProblem {
    pub fn name(&self) -> Option<&str> {
        self.name.as_deref()
    }

    pub fn model(&self) -> &Model {
        &self.model
    }

    /// Execute the mode implied by the specification.
    pub fn run(&self) -> Result<SearchRunResult, SearchError> {
        let options = SolveOptions {
            timeout: self.limits.timeout_ms.map(Duration::from_millis),
        };
        if let Some((sense, objective)) = &self.objective {
            let result = match sense {
                ObjectiveSense::Minimize => self
                    .model
                    .minimize_with_options(objective.clone(), options)?,
                ObjectiveSense::Maximize => self
                    .model
                    .maximize_with_options(objective.clone(), options)?,
            };
            return Ok(SearchRunResult::Optimization(result));
        }
        if let Some(max_solutions) = self.limits.max_solutions {
            let cap = usize::try_from(max_solutions).map_err(|_| SearchError::InvalidLimit {
                name: "max_solutions",
                value: max_solutions,
            })?;
            return Ok(SearchRunResult::Enumeration(
                self.model.enumerate(Some(cap), options)?,
            ));
        }
        Ok(SearchRunResult::Solve(
            self.model.solve_with_options(options)?,
        ))
    }

    /// Exact SMT-LIB lowering, including an optional Optimize objective.
    pub fn to_smt2(&self) -> Result<String, SearchError> {
        let mut estimated_bytes = self.model.smt2_size_upper_bound();
        if let Some((sense, objective)) = &self.objective {
            let command = match sense {
                ObjectiveSense::Minimize => "minimize",
                ObjectiveSense::Maximize => "maximize",
            };
            estimated_bytes = estimated_bytes.saturating_add(
                self.model
                    .expression_smt_size_upper_bound(objective)?
                    .saturating_add(command.len() as u128)
                    // `(` + command + space + expression + `)` + newline.
                    .saturating_add(4),
            );
        }
        if estimated_bytes > u128::from(MAX_SEARCH_SPEC_SMT_BYTES) {
            return Err(SearchError::SmtOutputTooLarge {
                estimated_bytes,
                limit: MAX_SEARCH_SPEC_SMT_BYTES,
            });
        }

        let mut smt = self.model.to_smt2()?;
        if let Some((sense, objective)) = &self.objective {
            let command = match sense {
                ObjectiveSense::Minimize => "minimize",
                ObjectiveSense::Maximize => "maximize",
            };
            let rendered = self.model.expression_to_smt(objective)?;
            let insertion = format!("({command} {rendered})\n");
            if let Some(position) = smt.find("(check-sat)\n") {
                smt.insert_str(position, &insertion);
            }
        }
        Ok(smt)
    }
}

fn resolve_variable(name: &str, model: &Model) -> Result<crate::IntVar, SearchError> {
    model
        .variable(name)
        .ok_or_else(|| SearchError::UnknownVariable(name.to_owned()))
}

fn resolve_variables(names: &[String], model: &Model) -> Result<Vec<crate::IntVar>, SearchError> {
    names
        .iter()
        .map(|name| resolve_variable(name, model))
        .collect()
}

#[derive(Debug, Clone, Copy)]
enum ParsedRelation {
    Eq,
    Le,
    Ge,
    Ne,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum TokenKind {
    Identifier(String),
    Integer(i128),
    Plus,
    Minus,
    Star,
    LeftParen,
    RightParen,
    Eq,
    Ne,
    Le,
    Ge,
    End,
}

#[derive(Debug, Clone)]
struct Token {
    kind: TokenKind,
    position: usize,
}

struct Parser<'a> {
    tokens: Vec<Token>,
    cursor: usize,
    model: &'a Model,
    /// Current `(`-nesting depth. Bounded so hostile input cannot overflow the
    /// stack through the parse_atom -> parse_sum recursion (this parser is
    /// reachable from the public `ay_search_solve_json` C ABI).
    depth: usize,
}

/// Maximum `(`-nesting depth accepted by the spec expression parser. Any real
/// linear-expression spec is a handful of levels; the bound exists so a
/// stranger's input fails with a parse error instead of a stack overflow.
const MAX_EXPR_DEPTH: usize = 128;

impl<'a> Parser<'a> {
    fn new(input: &str, model: &'a Model) -> Result<Self, SearchError> {
        if input.len() > MAX_EXPRESSION_BYTES {
            return Err(SearchError::ExpressionLimit {
                resource: "input byte length",
                limit: MAX_EXPRESSION_BYTES,
            });
        }
        Ok(Self {
            tokens: lex(input)?,
            cursor: 0,
            model,
            depth: 0,
        })
    }

    fn parse_sum(&mut self) -> Result<LinearExpr, SearchError> {
        let mut expression = self.parse_product()?;
        loop {
            match self.peek().kind {
                TokenKind::Plus => {
                    self.cursor += 1;
                    expression = expression + self.parse_product()?;
                }
                TokenKind::Minus => {
                    self.cursor += 1;
                    expression = expression - self.parse_product()?;
                }
                _ => return Ok(expression),
            }
        }
    }

    fn parse_product(&mut self) -> Result<LinearExpr, SearchError> {
        let mut expression = self.parse_unary()?;
        while matches!(self.peek().kind, TokenKind::Star) {
            let position = self.peek().position;
            self.cursor += 1;
            let rhs = self.parse_unary()?;
            // `constant_value` intentionally exposes the stored value even
            // after checked arithmetic records overflow. Multiplication may
            // use that value to preserve the expression shape, but it must
            // never launder the overflow bit by returning the other operand.
            // Without this taint, `((i128::MAX + 1) * x) - i128::MAX*x - x`
            // incorrectly normalizes to `-x` instead of failing closed.
            let overflowed = expression.overflowed || rhs.overflowed;
            expression = match (expression.constant_value(), rhs.constant_value()) {
                (Some(left), _) => rhs.scaled(left),
                (_, Some(right)) => expression.scaled(right),
                (None, None) => {
                    let _ = position;
                    return Err(SearchError::NonlinearExpression);
                }
            };
            expression.overflowed |= overflowed;
        }
        Ok(expression)
    }

    fn parse_unary(&mut self) -> Result<LinearExpr, SearchError> {
        // Iterative on purpose: a recursive descent here means one stack frame
        // per leading `+`/`-`, and a long `----…x` chain from untrusted input
        // overflows the stack (observed at ~42k frames via the C ABI). Fold
        // the whole prefix into a sign first.
        let mut negate = false;
        loop {
            match self.peek().kind {
                TokenKind::Plus => self.cursor += 1,
                TokenKind::Minus => {
                    negate = !negate;
                    self.cursor += 1;
                }
                _ => break,
            }
        }
        let atom = self.parse_atom()?;
        Ok(if negate { -atom } else { atom })
    }

    fn parse_atom(&mut self) -> Result<LinearExpr, SearchError> {
        let token = self.peek().clone();
        match token.kind {
            TokenKind::Integer(value) => {
                self.cursor += 1;
                Ok(LinearExpr {
                    terms: BTreeMap::new(),
                    constant: value,
                    overflowed: false,
                })
            }
            TokenKind::Identifier(name) => {
                self.cursor += 1;
                Ok(LinearExpr::from(resolve_variable(&name, self.model)?))
            }
            TokenKind::LeftParen => {
                if self.depth >= MAX_EXPR_DEPTH {
                    return Err(SearchError::ExpressionLimit {
                        resource: "parenthesis nesting depth",
                        limit: MAX_EXPR_DEPTH,
                    });
                }
                self.depth += 1;
                self.cursor += 1;
                let expression = self.parse_sum();
                self.depth -= 1;
                let expression = expression?;
                if !matches!(self.peek().kind, TokenKind::RightParen) {
                    return Err(parse_error(self.peek(), "expected `)`"));
                }
                self.cursor += 1;
                Ok(expression)
            }
            _ => Err(parse_error(&token, "expected a number, variable, or `(`")),
        }
    }

    fn peek(&self) -> &Token {
        &self.tokens[self.cursor]
    }
}

fn parse_linear_expression(input: &str, model: &Model) -> Result<LinearExpr, SearchError> {
    let mut parser = Parser::new(input, model)?;
    let expression = parser.parse_sum()?;
    if !matches!(parser.peek().kind, TokenKind::End) {
        return Err(parse_error(
            parser.peek(),
            "unexpected token after expression",
        ));
    }
    Ok(expression)
}

fn parse_relation(
    input: &str,
    model: &Model,
) -> Result<(LinearExpr, ParsedRelation, LinearExpr), SearchError> {
    let mut parser = Parser::new(input, model)?;
    let lhs = parser.parse_sum()?;
    let relation = match parser.peek().kind {
        TokenKind::Eq => ParsedRelation::Eq,
        TokenKind::Ne => ParsedRelation::Ne,
        TokenKind::Le => ParsedRelation::Le,
        TokenKind::Ge => ParsedRelation::Ge,
        TokenKind::End => return Err(SearchError::MissingRelation),
        _ => return Err(parse_error(parser.peek(), "expected ==, !=, <=, or >=")),
    };
    parser.cursor += 1;
    let rhs = parser.parse_sum()?;
    if !matches!(parser.peek().kind, TokenKind::End) {
        return Err(parse_error(parser.peek(), "only one relation is allowed"));
    }
    Ok((lhs, relation, rhs))
}

fn lex(input: &str) -> Result<Vec<Token>, SearchError> {
    let bytes = input.as_bytes();
    let mut tokens = Vec::new();
    let mut cursor = 0;
    while cursor < bytes.len() {
        if bytes[cursor].is_ascii_whitespace() {
            cursor += 1;
            continue;
        }
        let position = cursor;
        let kind = match bytes[cursor] {
            b'+' => {
                cursor += 1;
                TokenKind::Plus
            }
            b'-' => {
                cursor += 1;
                TokenKind::Minus
            }
            b'*' => {
                cursor += 1;
                TokenKind::Star
            }
            b'(' => {
                cursor += 1;
                TokenKind::LeftParen
            }
            b')' => {
                cursor += 1;
                TokenKind::RightParen
            }
            b'=' if bytes.get(cursor + 1) == Some(&b'=') => {
                cursor += 2;
                TokenKind::Eq
            }
            b'!' if bytes.get(cursor + 1) == Some(&b'=') => {
                cursor += 2;
                TokenKind::Ne
            }
            b'<' if bytes.get(cursor + 1) == Some(&b'=') => {
                cursor += 2;
                TokenKind::Le
            }
            b'>' if bytes.get(cursor + 1) == Some(&b'=') => {
                cursor += 2;
                TokenKind::Ge
            }
            byte if byte.is_ascii_digit() => {
                let start = cursor;
                while cursor < bytes.len() && bytes[cursor].is_ascii_digit() {
                    cursor += 1;
                }
                let digits = &input[start..cursor];
                let value = digits
                    .parse::<i128>()
                    .map_err(|_| SearchError::ExpressionParse {
                        position: start,
                        message: "integer literal is too large".to_owned(),
                    })?;
                TokenKind::Integer(value)
            }
            byte if byte == b'_' || byte.is_ascii_alphabetic() => {
                let start = cursor;
                cursor += 1;
                while cursor < bytes.len()
                    && (bytes[cursor] == b'_' || bytes[cursor].is_ascii_alphanumeric())
                {
                    cursor += 1;
                }
                TokenKind::Identifier(input[start..cursor].to_owned())
            }
            _ => {
                return Err(SearchError::ExpressionParse {
                    position,
                    message: "unsupported character".to_owned(),
                });
            }
        };
        if tokens.len() >= MAX_EXPRESSION_TOKENS {
            return Err(SearchError::ExpressionLimit {
                resource: "token count",
                limit: MAX_EXPRESSION_TOKENS,
            });
        }
        tokens.push(Token { kind, position });
    }
    tokens.push(Token {
        kind: TokenKind::End,
        position: input.len(),
    });
    Ok(tokens)
}

fn parse_error(token: &Token, message: &str) -> SearchError {
    SearchError::ExpressionParse {
        position: token.position,
        message: message.to_owned(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hostile_unary_chain_is_bounded_without_recursion() {
        // Regression: a recursive parse_unary crashed at ~42k frames on a long
        // minus chain reaching the parser through the public C ABI. Unary
        // parsing is iterative, and resource caps now reject hostile chains.
        let mut model = Model::new();
        model.int_var("x", Domain::interval(0, 3).unwrap()).unwrap();
        let at_token_limit = format!("{}x", "-".repeat(MAX_EXPRESSION_TOKENS - 1));
        parse_linear_expression(&at_token_limit, &model).expect("token limit is inclusive");

        let too_many_tokens = format!("{}x", "-".repeat(MAX_EXPRESSION_TOKENS));
        assert!(matches!(
            parse_linear_expression(&too_many_tokens, &model),
            Err(SearchError::ExpressionLimit {
                resource: "token count",
                ..
            })
        ));

        let too_many_bytes = format!("{}x", "+".repeat(MAX_EXPRESSION_BYTES));
        assert!(matches!(
            parse_linear_expression(&too_many_bytes, &model),
            Err(SearchError::ExpressionLimit {
                resource: "input byte length",
                ..
            })
        ));
    }

    #[test]
    fn hostile_paren_nesting_fails_closed_at_the_depth_limit() {
        let mut model = Model::new();
        model.int_var("x", Domain::interval(0, 3).unwrap()).unwrap();
        // At the limit: parses.
        let ok = format!(
            "{}x{}",
            "(".repeat(MAX_EXPR_DEPTH),
            ")".repeat(MAX_EXPR_DEPTH)
        );
        parse_linear_expression(&ok, &model).expect("nesting at the limit parses");
        // One past the limit: clean error, not a crash.
        let too_deep = format!(
            "{}x{}",
            "(".repeat(MAX_EXPR_DEPTH + 1),
            ")".repeat(MAX_EXPR_DEPTH + 1)
        );
        assert!(matches!(
            parse_linear_expression(&too_deep, &model),
            Err(SearchError::ExpressionLimit {
                resource: "parenthesis nesting depth",
                ..
            })
        ));
        // And absurd depth from hostile input: still just an error.
        let hostile = format!("{}x{}", "(".repeat(500_000), ")".repeat(500_000));
        assert!(matches!(
            parse_linear_expression(&hostile, &model),
            Err(SearchError::ExpressionLimit { .. })
        ));
    }

    #[test]
    fn parser_rejects_nonlinear_and_injection_syntax() {
        let mut model = Model::new();
        model.int_var("x", Domain::interval(0, 3).unwrap()).unwrap();
        model.int_var("y", Domain::interval(0, 3).unwrap()).unwrap();

        assert!(matches!(
            parse_linear_expression("x * y", &model),
            Err(SearchError::NonlinearExpression)
        ));
        assert!(matches!(
            parse_linear_expression("x); (check-sat)", &model),
            Err(SearchError::ExpressionParse { .. })
        ));
    }

    #[test]
    fn parser_does_not_launder_overflow_through_multiply_and_cancellation() {
        let max = i128::MAX;
        let json = format!(
            r#"{{
              "version":1,
              "variables":[{{"name":"x","domain":{{"min":1,"max":1}}}}],
              "constraints":[
                {{"expression":"(({max} + 1) * x) - ({max} * x) - x == 0"}}
              ]
            }}"#
        );
        assert!(matches!(
            SearchSpec::from_json(&json).unwrap().build(),
            Err(SearchError::ExpressionOverflow)
        ));
    }

    #[test]
    fn json_round_trip_and_safe_equation_solve() {
        let json = r#"{
          "version": 1,
          "variables": [
            {"name":"x","domain":{"min":0,"max":10}},
            {"name":"y","domain":{"values":[1,3,8]}}
          ],
          "constraints": [{"expression":"2*x + y == 9"}]
        }"#;
        let spec = SearchSpec::from_json(json).unwrap();
        let rendered = serde_json::to_string(&spec).unwrap();
        let problem = SearchSpec::from_json(&rendered).unwrap().build().unwrap();
        let SearchRunResult::Solve(SolveResult::Sat(solution)) = problem.run().unwrap() else {
            panic!("expected SAT");
        };
        assert_eq!(solution.value("x"), Some(3));
        assert_eq!(solution.value("y"), Some(3));
    }

    #[test]
    fn objective_and_enumeration_limit_are_rejected_as_conflicting_modes() {
        let json = r#"{
          "version":1,
          "variables":[{"name":"x","domain":{"min":0,"max":1}}],
          "objective":{"sense":"maximize","expression":"x"},
          "limits":{"max_solutions":2}
        }"#;
        assert!(matches!(
            SearchSpec::from_json(json).unwrap().build(),
            Err(SearchError::ConflictingExecutionModes)
        ));
    }

    #[test]
    fn search_spec_enumeration_has_solution_and_assignment_cell_caps() {
        let too_many_solutions = format!(
            r#"{{"version":1,"variables":[],"limits":{{"max_solutions":{}}}}}"#,
            MAX_SEARCH_SPEC_SOLUTIONS + 1
        );
        assert!(matches!(
            SearchSpec::from_json(&too_many_solutions).unwrap().build(),
            Err(SearchError::InvalidLimit {
                name: "max_solutions",
                ..
            })
        ));

        let variable_count = 101;
        let variables = (0..variable_count)
            .map(|index| format!(r#"{{"name":"x_{index}","domain":{{"min":0,"max":1}}}}"#))
            .collect::<Vec<_>>()
            .join(",");
        let max_solutions = MAX_SEARCH_SPEC_RESULT_CELLS / variable_count + 1;
        let too_many_cells = format!(
            r#"{{"version":1,"variables":[{variables}],"limits":{{"max_solutions":{max_solutions}}}}}"#
        );
        assert!(matches!(
            SearchSpec::from_json(&too_many_cells).unwrap().build(),
            Err(SearchError::EnumerationResultTooLarge { .. })
        ));
    }

    #[test]
    fn search_spec_enumeration_caps_repeated_names_and_labels_in_json_output() {
        let long_name = format!("x{}", "a".repeat(1_700));
        let mut repeated_name_variables = vec![VariableSpec {
            name: long_name,
            domain: DomainSpec::Interval { min: 0, max: 1 },
            labels: BTreeMap::new(),
        }];
        repeated_name_variables.extend((1..14).map(|index| VariableSpec {
            name: format!("x_{index}"),
            domain: DomainSpec::Interval { min: 0, max: 1 },
            labels: BTreeMap::new(),
        }));
        let repeated_name = SearchSpec {
            version: 1,
            name: None,
            // 2^14 assignments ensure the requested 10,000-result cap is
            // reachable; the long name would really be repeated 10,000 times.
            variables: repeated_name_variables,
            constraints: Vec::new(),
            objective: None,
            limits: Some(LimitsSpec {
                timeout_ms: None,
                max_solutions: Some(MAX_SEARCH_SPEC_SOLUTIONS),
            }),
        };
        assert!(matches!(
            repeated_name.build(),
            Err(SearchError::EnumerationOutputTooLarge { .. })
        ));

        // One control byte is six bytes in compact JSON (`\u0001`). The
        // selected label is repeated in every retained solution just like the
        // assignment name, so escaped size—not source String length—must count.
        let long_escaped_label = "\u{1}".repeat(300);
        let mut escaped_label_variables = vec![VariableSpec {
            name: "route".to_owned(),
            domain: DomainSpec::Interval { min: 0, max: 1 },
            labels: BTreeMap::from([(0, long_escaped_label.clone()), (1, long_escaped_label)]),
        }];
        escaped_label_variables.extend((1..14).map(|index| VariableSpec {
            name: format!("route_{index}"),
            domain: DomainSpec::Interval { min: 0, max: 1 },
            labels: BTreeMap::new(),
        }));
        let escaped_label = SearchSpec {
            version: 1,
            name: None,
            variables: escaped_label_variables,
            constraints: Vec::new(),
            objective: None,
            limits: Some(LimitsSpec {
                timeout_ms: None,
                max_solutions: Some(MAX_SEARCH_SPEC_SOLUTIONS),
            }),
        };
        assert!(matches!(
            escaped_label.build(),
            Err(SearchError::EnumerationOutputTooLarge { .. })
        ));
    }

    #[test]
    fn enumeration_json_estimate_bounds_the_actual_serializer() {
        let spec = SearchSpec {
            version: 1,
            name: None,
            variables: vec![
                VariableSpec {
                    name: "x".to_owned(),
                    domain: DomainSpec::Interval { min: 0, max: 1 },
                    labels: BTreeMap::from([(0, "\u{1}\"\\é".to_owned())]),
                },
                VariableSpec {
                    name: "y".to_owned(),
                    domain: DomainSpec::Interval { min: 0, max: 1 },
                    labels: BTreeMap::from([(1, "line\nbreak".to_owned())]),
                },
            ],
            constraints: Vec::new(),
            objective: None,
            limits: Some(LimitsSpec {
                timeout_ms: None,
                max_solutions: Some(4),
            }),
        };
        let estimate = enumeration_result_json_upper_bound(&spec.variables, 4);
        let result = spec.build().unwrap().run().unwrap();
        let actual = serde_json::to_vec(&result).unwrap().len() as u128;
        assert!(actual <= estimate, "actual={actual}, estimate={estimate}");
        assert!(estimate <= u128::from(MAX_SEARCH_SPEC_RESULT_BYTES));
    }

    #[test]
    fn smt_size_preflight_matches_all_normalized_lowerings() {
        let spec = SearchSpec {
            version: 1,
            name: None,
            variables: vec![
                VariableSpec {
                    name: "index".to_owned(),
                    domain: DomainSpec::Interval { min: 0, max: 1 },
                    labels: BTreeMap::new(),
                },
                VariableSpec {
                    name: "first".to_owned(),
                    domain: DomainSpec::Values {
                        values: vec![-2, 4],
                    },
                    labels: BTreeMap::new(),
                },
                VariableSpec {
                    name: "second".to_owned(),
                    domain: DomainSpec::Interval { min: -1, max: 5 },
                    labels: BTreeMap::new(),
                },
                VariableSpec {
                    name: "selected".to_owned(),
                    domain: DomainSpec::Interval { min: -2, max: 5 },
                    labels: BTreeMap::new(),
                },
            ],
            constraints: vec![
                ConstraintSpec::Expression {
                    expression: "2*first - second != -3".to_owned(),
                },
                ConstraintSpec::Expression {
                    expression: "1 == 2".to_owned(),
                },
                ConstraintSpec::AllDifferent {
                    all_different: vec!["first".to_owned(), "second".to_owned()],
                },
                ConstraintSpec::Table {
                    table: TableSpec {
                        variables: vec!["first".to_owned(), "second".to_owned()],
                        tuples: vec![vec![-2, -1], vec![4, 5]],
                    },
                },
                ConstraintSpec::Element {
                    element: ElementSpec {
                        index: "index".to_owned(),
                        array: vec!["first".to_owned(), "second".to_owned()],
                        result: "selected".to_owned(),
                    },
                },
            ],
            objective: Some(ObjectiveSpec {
                sense: ObjectiveSense::Maximize,
                expression: "selected + 2".to_owned(),
            }),
            limits: None,
        };
        let problem = spec.build().unwrap();
        let mut estimated = problem.model.smt2_size_upper_bound();
        let (_, objective) = problem.objective.as_ref().unwrap();
        estimated += problem
            .model
            .expression_smt_size_upper_bound(objective)
            .unwrap()
            + "maximize".len() as u128
            + 4;
        let rendered = problem.to_smt2().unwrap();
        assert_eq!(rendered.len() as u128, estimated);
    }

    #[test]
    fn search_spec_smt_compile_rejects_table_name_amplification() {
        let variable_count = 100;
        let variables = (0..variable_count)
            .map(|index| VariableSpec {
                name: format!("x_{index}_{}", "a".repeat(2_000)),
                domain: DomainSpec::Interval { min: 0, max: 1 },
                labels: BTreeMap::new(),
            })
            .collect::<Vec<_>>();
        let variable_names = variables
            .iter()
            .map(|variable| variable.name.clone())
            .collect();
        let spec = SearchSpec {
            version: 1,
            name: None,
            variables,
            constraints: vec![ConstraintSpec::Table {
                table: TableSpec {
                    variables: variable_names,
                    // Compact JSON (100,000 small integers) would render each
                    // 2,000-byte name once per cell, amplifying past 16 MiB.
                    tuples: vec![vec![0; variable_count]; 1_000],
                },
            }],
            objective: None,
            limits: None,
        };
        assert!(matches!(
            spec.to_smt2(),
            Err(SearchError::SmtOutputTooLarge {
                estimated_bytes,
                limit: MAX_SEARCH_SPEC_SMT_BYTES,
            }) if estimated_bytes > u128::from(MAX_SEARCH_SPEC_SMT_BYTES)
        ));
    }
}

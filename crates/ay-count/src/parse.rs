// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Parser for the Model Counting Competition DIMACS-like input format
//! (format spec v1.2, 2026).
//!
//! Supports all five problem types: `mc`, `wmc`, `pmc`, `pwmc`, and
//! `amc-complex`. Weights are parsed to exact rationals (decimal, scientific
//! notation, or `a/b` fraction; complex `a+bi`). Per the spec, the type line
//! is authoritative when present; otherwise the type is inferred from the
//! presence of `c p show` / `c p weight` lines.

use std::fmt;
use std::str::FromStr;

use num_bigint::{BigInt, BigUint};
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

/// Bound compact decimal-exponent expansion. Longer mantissas remain
/// input-proportional, but a handful of exponent digits must not request a
/// multi-gigabyte `BigInt` allocation.
const MAX_DECIMAL_EXPONENT_ABS: u64 = 1_000_000;

/// Model-counting engines keep multiple dense arrays per variable. This
/// consumer-specific ceiling is intentionally lower than the syntax-only
/// DIMACS bound so an accepted header remains practically allocatable.
const MAX_COUNT_VARS: usize = 1 << 20;

/// Problem type of a counting instance.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProblemType {
    /// Exact unweighted model counting.
    Mc,
    /// Weighted model counting.
    Wmc,
    /// Projected model counting.
    Pmc,
    /// Projected weighted model counting.
    Pwmc,
    /// Algebraic model counting over complex numbers.
    AmcComplex,
}

impl ProblemType {
    /// Competition string for the `c s type` output line.
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Mc => "mc",
            Self::Wmc => "wmc",
            Self::Pmc => "pmc",
            Self::Pwmc => "pwmc",
            Self::AmcComplex => "amc-complex",
        }
    }

    fn from_token(token: &str) -> Option<Self> {
        match token.to_ascii_lowercase().as_str() {
            "mc" => Some(Self::Mc),
            "wmc" => Some(Self::Wmc),
            "pmc" => Some(Self::Pmc),
            "pwmc" => Some(Self::Pwmc),
            "amc-complex" | "amc_complex" | "amc" => Some(Self::AmcComplex),
            _ => None,
        }
    }
}

/// A parsed literal weight: real rational or complex rational.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RawWeight {
    /// Real rational weight.
    Rat(BigRational),
    /// Complex rational weight (real, imaginary).
    Complex(BigRational, BigRational),
}

/// A parsed counting instance.
#[derive(Debug)]
pub struct Instance {
    /// Number of variables from the `p cnf` header.
    pub num_vars: usize,
    /// Clauses as signed DIMACS literals (validated in range, no zeros).
    pub clauses: Vec<Vec<i32>>,
    /// Effective problem type (type line authoritative, else inferred).
    pub ptype: ProblemType,
    /// Projection variables (1-based, sorted, deduplicated) from `c p show`.
    /// `None` when no show line was seen.
    pub show: Option<Vec<u32>>,
    /// Raw weight lines in file order: (literal, weight).
    pub weights: Vec<(i32, RawWeight)>,
    /// Warnings the competition spec requires or suggests emitting.
    pub warnings: Vec<String>,
}

/// Parse error with a competition-appropriate message.
#[derive(Debug)]
pub struct ParseError(pub String);

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl std::error::Error for ParseError {}

fn err<T>(msg: impl Into<String>) -> Result<T, ParseError> {
    Err(ParseError(msg.into()))
}

/// Parse an exact rational from decimal (`0.4`, `-12`, `.5`), scientific
/// (`1.23e+4`), or fraction (`3/10`) notation.
pub fn parse_rational(s: &str) -> Result<BigRational, ParseError> {
    let s = s.trim();
    if s.is_empty() {
        return err("empty number");
    }
    if let Some(slash) = s.find('/') {
        let (num_str, den_str) = (&s[..slash], &s[slash + 1..]);
        let num = BigInt::from_str(num_str.trim())
            .map_err(|_| ParseError(format!("invalid fraction numerator `{num_str}`")))?;
        let den = BigInt::from_str(den_str.trim())
            .map_err(|_| ParseError(format!("invalid fraction denominator `{den_str}`")))?;
        if den.is_zero() {
            return err(format!("zero denominator in fraction `{s}`"));
        }
        return Ok(BigRational::new(num, den));
    }
    // Decimal, possibly with exponent: [-+]?digits[.digits][eE[-+]?digits]
    let (mantissa, exp10) = match s.find(['e', 'E']) {
        Some(epos) => {
            let exp_str = &s[epos + 1..];
            let exp: i64 = exp_str
                .parse()
                .map_err(|_| ParseError(format!("invalid exponent `{exp_str}`")))?;
            (&s[..epos], exp)
        }
        None => (s, 0i64),
    };
    let (int_part, frac_part) = match mantissa.find('.') {
        Some(dot) => (&mantissa[..dot], &mantissa[dot + 1..]),
        None => (mantissa, ""),
    };
    let (sign, int_digits) = match int_part.strip_prefix('-') {
        Some(rest) => (-1i32, rest),
        None => (1i32, int_part.strip_prefix('+').unwrap_or(int_part)),
    };
    if int_digits.is_empty() && frac_part.is_empty() {
        return err(format!("invalid number `{s}`"));
    }
    if !int_digits.chars().all(|c| c.is_ascii_digit())
        || !frac_part.chars().all(|c| c.is_ascii_digit())
    {
        return err(format!("invalid number `{s}`"));
    }
    let digits = format!("{int_digits}{frac_part}");
    let digits = if digits.is_empty() {
        "0".into()
    } else {
        digits
    };
    let mut num = BigInt::from(
        BigUint::from_str(&digits).map_err(|_| ParseError(format!("invalid number `{s}`")))?,
    );
    if sign < 0 {
        num = -num;
    }
    let scale = i64::try_from(frac_part.len())
        .map_err(|_| ParseError(format!("decimal scale is too large in `{s}`")))?;
    let net_exp = exp10
        .checked_sub(scale)
        .ok_or_else(|| ParseError(format!("decimal exponent overflows in `{s}`")))?;
    let exponent = net_exp.unsigned_abs();
    if exponent > MAX_DECIMAL_EXPONENT_ABS {
        return err(format!(
            "decimal exponent magnitude {exponent} exceeds the supported maximum {MAX_DECIMAL_EXPONENT_ABS}"
        ));
    }
    let exponent = exponent as u32;
    let ten = BigInt::from(10u32);
    Ok(if net_exp >= 0 {
        BigRational::from_integer(num * ten.pow(exponent))
    } else {
        BigRational::new(num, ten.pow(exponent))
    })
}

/// Parse a weight token: real rational or complex `a+bi` / `a-bi`.
pub fn parse_weight(s: &str) -> Result<RawWeight, ParseError> {
    let s = s.trim();
    if let Some(body) = s.strip_suffix(['i', 'I']) {
        // Find the split sign: last '+'/'-' not at position 0 and not directly
        // after an exponent marker (so `1.2e+3+0.5i` splits at the second '+').
        let bytes = body.as_bytes();
        let mut split = None;
        for idx in (1..bytes.len()).rev() {
            let b = bytes[idx];
            if (b == b'+' || b == b'-') && !matches!(bytes[idx - 1], b'e' | b'E') {
                split = Some(idx);
                break;
            }
        }
        let Some(idx) = split else {
            // Pure imaginary like `0.5i` (not in spec examples, but unambiguous).
            return Ok(RawWeight::Complex(
                BigRational::zero(),
                parse_rational(body)?,
            ));
        };
        let re = parse_rational(&body[..idx])?;
        let im_str = &body[idx..];
        let im = if im_str == "+" {
            BigRational::one()
        } else if im_str == "-" {
            -BigRational::one()
        } else {
            parse_rational(im_str)?
        };
        Ok(RawWeight::Complex(re, im))
    } else {
        Ok(RawWeight::Rat(parse_rational(s)?))
    }
}

/// Parse a complete MC-2026 instance from text.
pub fn parse_instance(content: &str) -> Result<Instance, ParseError> {
    let mut num_vars: Option<usize> = None;
    let mut declared_clauses: usize = 0;
    let mut clauses: Vec<Vec<i32>> = Vec::new();
    let mut current: Vec<i32> = Vec::new();
    let mut in_clause = false;
    let mut explicit_type: Option<ProblemType> = None;
    let mut show_vars: Vec<u32> = Vec::new();
    let mut saw_show = false;
    let mut weights: Vec<(i32, RawWeight)> = Vec::new();
    let mut warnings: Vec<String> = Vec::new();

    for (line_no, raw_line) in content.lines().enumerate() {
        let line_no = line_no + 1;
        let line = raw_line.trim();
        if line.is_empty() {
            continue;
        }
        if let Some(rest) = line.strip_prefix('p') {
            // Problem line: `p cnf n m` (tolerate a third count per Example 4).
            if num_vars.is_some() {
                return err(format!("duplicate `p` line at line {line_no}"));
            }
            let tokens: Vec<&str> = rest.split_whitespace().collect();
            if tokens.len() < 3 || tokens[0] != "cnf" {
                return err(format!(
                    "malformed problem line at line {line_no}: `{line}`"
                ));
            }
            let n: usize = tokens[1]
                .parse()
                .map_err(|_| ParseError(format!("invalid variable count at line {line_no}")))?;
            if n > MAX_COUNT_VARS {
                return err(format!(
                    "variable count {n} exceeds the maximum supported {MAX_COUNT_VARS}; refusing to allocate"
                ));
            }
            let m: usize = tokens[2]
                .parse()
                .map_err(|_| ParseError(format!("invalid clause count at line {line_no}")))?;
            num_vars = Some(n);
            declared_clauses = m;
            continue;
        }
        if line.starts_with('c') {
            let tokens: Vec<&str> = line.split_whitespace().collect();
            // `c t TYPE`
            if tokens.len() >= 3 && tokens[0] == "c" && tokens[1] == "t" {
                match ProblemType::from_token(tokens[2]) {
                    Some(t) => {
                        if let Some(prev) = explicit_type {
                            if prev != t {
                                return err(format!(
                                    "conflicting `c t` lines: {} then {}",
                                    prev.as_str(),
                                    t.as_str()
                                ));
                            }
                        }
                        explicit_type = Some(t);
                    }
                    None => {
                        return err(format!(
                            "unsupported problem type `{}` at line {line_no}",
                            tokens[2]
                        ));
                    }
                }
                continue;
            }
            // `c p show ... 0` / `c p weight LIT W [0]`
            if tokens.len() >= 3 && tokens[0] == "c" && tokens[1] == "p" {
                match tokens[2] {
                    "show" => {
                        saw_show = true;
                        let mut terminated = false;
                        for token in &tokens[3..] {
                            if *token == "0" {
                                terminated = true;
                                break;
                            }
                            let var: u32 = token.parse().map_err(|_| {
                                ParseError(format!(
                                    "invalid projection variable `{token}` at line {line_no}"
                                ))
                            })?;
                            if var == 0 {
                                return err(format!("projection variable 0 at line {line_no}"));
                            }
                            show_vars.push(var);
                        }
                        if !terminated {
                            return err(format!("projection line {line_no} missing terminating 0"));
                        }
                    }
                    "weight" => {
                        // `c p weight LIT W 0` (trailing 0 optional in the wild).
                        if tokens.len() < 5 {
                            return err(format!("malformed weight line at line {line_no}"));
                        }
                        let lit: i32 = tokens[3].parse().map_err(|_| {
                            ParseError(format!(
                                "invalid weight literal `{}` at line {line_no}",
                                tokens[3]
                            ))
                        })?;
                        if lit == 0 {
                            return err(format!("weight literal 0 at line {line_no}"));
                        }
                        let w = parse_weight(tokens[4])
                            .map_err(|e| ParseError(format!("line {line_no}: {e}")))?;
                        weights.push((lit, w));
                    }
                    _ => {
                        // Unknown problem-specific line: tolerate as comment.
                    }
                }
                continue;
            }
            // Any other c-line is a comment.
            continue;
        }
        // Clause data line.
        if num_vars.is_none() {
            return err(format!(
                "clause data before `p cnf` header at line {line_no}"
            ));
        }
        for token in line.split_whitespace() {
            let lit: i32 = token
                .parse()
                .map_err(|_| ParseError(format!("invalid literal `{token}` at line {line_no}")))?;
            if lit == 0 {
                if clauses.len() == declared_clauses {
                    return err(format!(
                        "more clauses than the {declared_clauses} announced in the header (line {line_no})"
                    ));
                }
                clauses.push(std::mem::take(&mut current));
                in_clause = false;
            } else {
                let var = lit.unsigned_abs() as usize;
                if var > num_vars.unwrap_or(0) {
                    return err(format!(
                        "literal {lit} exceeds variable count {} (line {line_no})",
                        num_vars.unwrap_or(0)
                    ));
                }
                current.push(lit);
                in_clause = true;
            }
        }
    }

    let Some(num_vars) = num_vars else {
        return err("missing `p cnf` header");
    };
    if in_clause {
        // Trailing clause without terminating 0: accept it (common in the wild).
        if clauses.len() == declared_clauses {
            return err(format!(
                "more clauses than the {declared_clauses} announced in the header (unterminated final clause)"
            ));
        }
        clauses.push(current);
        warnings.push("last clause missing terminating 0; accepted".to_string());
    }
    if clauses.len() < declared_clauses {
        warnings.push(format!(
            "header announced {declared_clauses} clauses but file contains {}",
            clauses.len()
        ));
    }

    for &var in &show_vars {
        if var as usize > num_vars {
            return err(format!(
                "projection variable {var} exceeds variable count {num_vars}"
            ));
        }
    }
    show_vars.sort_unstable();
    show_vars.dedup();

    for (lit, _) in &weights {
        if lit.unsigned_abs() as usize > num_vars {
            return err(format!(
                "weight literal {lit} exceeds variable count {num_vars}"
            ));
        }
    }

    let has_weights = !weights.is_empty();
    let has_complex = weights
        .iter()
        .any(|(_, w)| matches!(w, RawWeight::Complex(_, _)));
    let ptype = match explicit_type {
        Some(t) => t,
        None => {
            if has_complex {
                ProblemType::AmcComplex
            } else if has_weights && saw_show {
                ProblemType::Pwmc
            } else if has_weights {
                ProblemType::Wmc
            } else if saw_show {
                ProblemType::Pmc
            } else {
                ProblemType::Mc
            }
        }
    };

    // Cross-validate declared type against problem-specific lines.
    match ptype {
        ProblemType::Mc => {
            if has_weights {
                warnings.push("type is mc but weight lines present; weights ignored".into());
                weights.clear();
            }
            if saw_show {
                warnings.push("type is mc but show lines present; projection ignored".into());
                saw_show = false;
                show_vars.clear();
            }
        }
        ProblemType::Wmc => {
            if saw_show {
                // Full show set is equivalent to wmc; partial show contradicts.
                if show_vars.len() != num_vars {
                    warnings.push(
                        "type is wmc but a partial show line is present; projection ignored".into(),
                    );
                }
                saw_show = false;
                show_vars.clear();
            }
        }
        ProblemType::Pmc => {
            if has_weights {
                warnings.push("type is pmc but weight lines present; weights ignored".into());
                weights.clear();
            }
        }
        ProblemType::Pwmc | ProblemType::AmcComplex => {}
    }

    let show = if saw_show { Some(show_vars) } else { None };

    Ok(Instance {
        num_vars,
        clauses,
        ptype,
        show,
        weights,
        warnings,
    })
}

/// Resolved real-weight table plus warnings, built per the spec's defaulting
/// rules (missing complement of `0<w<1` is `1-w`; missing pair is `1`;
/// `w<=0` with missing complement is a format error).
pub struct ResolvedWeights {
    /// Per-literal weights indexed by literal code (`(var-1)*2 + negated`).
    pub weights: Vec<BigRational>,
    /// Spec-mandated warnings emitted during resolution.
    pub warnings: Vec<String>,
}

/// Resolve real weights for `wmc`/`pwmc`.
///
/// `projected`: when `Some`, weights given on non-projection variables trigger
/// a warning and are ignored (2025 rule: weights only on projection vars).
pub fn resolve_real_weights(
    num_vars: usize,
    raw: &[(i32, RawWeight)],
    projected: Option<&[bool]>,
) -> Result<ResolvedWeights, ParseError> {
    let mut given: Vec<Option<BigRational>> = vec![None; num_vars * 2];
    let mut warnings = Vec::new();
    for (lit, w) in raw {
        let w = match w {
            RawWeight::Rat(r) => r.clone(),
            RawWeight::Complex(_, _) => {
                return err(format!(
                    "complex weight on literal {lit} in a real-weighted instance"
                ));
            }
        };
        let var = lit.unsigned_abs() as usize - 1;
        if let Some(proj) = projected {
            if !proj[var] {
                warnings.push(format!(
                    "weight given for non-projection variable {} ; ignored",
                    var + 1
                ));
                continue;
            }
        }
        let code = var * 2 + usize::from(*lit < 0);
        if let Some(prev) = &given[code] {
            if *prev != w {
                warnings.push(format!(
                    "duplicate weight for literal {lit}; using the last occurrence"
                ));
            }
        }
        given[code] = Some(w);
    }

    let one: BigRational = One::one();
    let mut weights = Vec::with_capacity(num_vars * 2);
    for var in 0..num_vars {
        let pos = given[var * 2].clone();
        let neg = given[var * 2 + 1].clone();
        let (wp, wn) = match (pos, neg) {
            (Some(p), Some(n)) => (p, n),
            (None, None) => (one.clone(), one.clone()),
            (Some(p), None) => {
                if p.is_positive() && p < one {
                    let n = &one - &p;
                    warnings.push(format!(
                        "weight for literal -{} not given; set to 1-w = {}",
                        var + 1,
                        n
                    ));
                    (p, n)
                } else {
                    return err(format!(
                        "weight {} for literal {} requires the complement weight to be given",
                        p,
                        var + 1
                    ));
                }
            }
            (None, Some(n)) => {
                if n.is_positive() && n < one {
                    let p = &one - &n;
                    warnings.push(format!(
                        "weight for literal {} not given; set to 1-w = {}",
                        var + 1,
                        p
                    ));
                    (p, n)
                } else {
                    return err(format!(
                        "weight {} for literal -{} requires the complement weight to be given",
                        n,
                        var + 1
                    ));
                }
            }
        };
        if wp.is_zero() {
            warnings.push(format!("weight of literal {} is 0", var + 1));
        }
        if wn.is_zero() {
            warnings.push(format!("weight of literal -{} is 0", var + 1));
        }
        weights.push(wp);
        weights.push(wn);
    }
    Ok(ResolvedWeights { weights, warnings })
}

/// Resolved complex weights for `amc-complex`.
pub struct ResolvedComplexWeights {
    /// Per-literal complex weights `(re, im)` indexed by literal code.
    pub weights: Vec<(BigRational, BigRational)>,
    /// Warnings emitted during resolution.
    pub warnings: Vec<String>,
}

/// Resolve complex weights: default `1+0i` for untouched variables; a single
/// given polarity without its complement is a format error.
pub fn resolve_complex_weights(
    num_vars: usize,
    raw: &[(i32, RawWeight)],
) -> Result<ResolvedComplexWeights, ParseError> {
    let mut given: Vec<Option<(BigRational, BigRational)>> = vec![None; num_vars * 2];
    let mut warnings = Vec::new();
    for (lit, w) in raw {
        let (re, im) = match w {
            RawWeight::Rat(r) => (r.clone(), BigRational::zero()),
            RawWeight::Complex(re, im) => (re.clone(), im.clone()),
        };
        let var = lit.unsigned_abs() as usize - 1;
        let code = var * 2 + usize::from(*lit < 0);
        given[code] = Some((re, im));
    }
    let mut weights = Vec::with_capacity(num_vars * 2);
    for var in 0..num_vars {
        let pos = given[var * 2].clone();
        let neg = given[var * 2 + 1].clone();
        let (wp, wn) = match (pos, neg) {
            (Some(p), Some(n)) => (p, n),
            (None, None) => (
                (One::one(), BigRational::zero()),
                (One::one(), BigRational::zero()),
            ),
            _ => {
                return err(format!(
                    "algebraic instance gives a weight for only one polarity of variable {}",
                    var + 1
                ));
            }
        };
        if wp.0.is_zero() && wp.1.is_zero() {
            warnings.push(format!("weight of literal {} is 0", var + 1));
        }
        if wn.0.is_zero() && wn.1.is_zero() {
            warnings.push(format!("weight of literal -{} is 0", var + 1));
        }
        weights.push(wp);
        weights.push(wn);
    }
    Ok(ResolvedComplexWeights { weights, warnings })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rat(s: &str) -> BigRational {
        parse_rational(s).unwrap()
    }

    #[test]
    fn rational_forms() {
        assert_eq!(rat("0.4"), BigRational::new(2.into(), 5.into()));
        assert_eq!(rat("3/10"), BigRational::new(3.into(), 10.into()));
        assert_eq!(rat("-0.5"), BigRational::new((-1).into(), 2.into()));
        assert_eq!(rat("1.23e+4"), BigRational::from_integer(12300.into()));
        assert_eq!(rat("1e-2"), BigRational::new(1.into(), 100.into()));
        assert_eq!(rat("7"), BigRational::from_integer(7.into()));
        assert!(parse_rational("1/0").is_err());
        assert!(parse_rational("abc").is_err());
    }

    #[test]
    fn rational_exponent_does_not_wrap_or_amplify_without_bound() {
        assert!(parse_rational("1e4294967296").is_err());
        assert!(parse_rational("1e-9223372036854775808").is_err());
    }

    #[test]
    fn parser_rejects_variable_count_above_dense_allocation_cap() {
        let text = format!("p cnf {} 0\n", MAX_COUNT_VARS + 1);
        let error = parse_instance(&text).expect_err("overlarge header must fail closed");
        assert!(error.to_string().contains("maximum supported"));
    }

    #[test]
    fn complex_weight_forms() {
        match parse_weight("0.4+0.2i").unwrap() {
            RawWeight::Complex(re, im) => {
                assert_eq!(re, rat("0.4"));
                assert_eq!(im, rat("0.2"));
            }
            RawWeight::Rat(_) => panic!("expected complex"),
        }
        match parse_weight("0.6-0.6i").unwrap() {
            RawWeight::Complex(re, im) => {
                assert_eq!(re, rat("0.6"));
                assert_eq!(im, rat("-0.6"));
            }
            RawWeight::Rat(_) => panic!("expected complex"),
        }
        match parse_weight("1/2+3/10i").unwrap() {
            RawWeight::Complex(re, im) => {
                assert_eq!(re, rat("1/2"));
                assert_eq!(im, rat("3/10"));
            }
            RawWeight::Rat(_) => panic!("expected complex"),
        }
        match parse_weight("1.2e+3+0.5i").unwrap() {
            RawWeight::Complex(re, im) => {
                assert_eq!(re, rat("1200"));
                assert_eq!(im, rat("0.5"));
            }
            RawWeight::Rat(_) => panic!("expected complex"),
        }
    }

    #[test]
    fn parses_spec_example_1() {
        let text = "c c comment\np cnf 6 4\nc t mc\n-1 -2\n0\n2 3 -4 0\n4 5 0\n4 6 0\n";
        let inst = parse_instance(text).unwrap();
        assert_eq!(inst.num_vars, 6);
        assert_eq!(inst.clauses.len(), 4);
        assert_eq!(inst.ptype, ProblemType::Mc);
        assert_eq!(inst.clauses[0], vec![-1, -2]);
    }

    #[test]
    fn parses_spec_example_4_pmc() {
        let text = "p cnf 6 4 2\nc t pmc\nc p show 1 2 0\n-1 -2 0\n2 3 -4 0\n4 5 0\n4 6 0\n";
        let inst = parse_instance(text).unwrap();
        assert_eq!(inst.ptype, ProblemType::Pmc);
        assert_eq!(inst.show, Some(vec![1, 2]));
    }

    #[test]
    fn rejects_excess_clauses() {
        let text = "p cnf 2 1\n1 0\n2 0\n";
        assert!(parse_instance(text).is_err());
    }

    #[test]
    fn rejects_unterminated_excess_clause() {
        let text = "p cnf 1 0\n1";
        let error = parse_instance(text).expect_err("unterminated clause still counts");
        assert!(error.to_string().contains("more clauses than the 0"));
    }

    #[test]
    fn infers_wmc_from_weight_lines() {
        let text = "p cnf 2 1\nc p weight 1 0.4 0\nc p weight -1 0.6 0\n1 2 0\n";
        let inst = parse_instance(text).unwrap();
        assert_eq!(inst.ptype, ProblemType::Wmc);
    }

    #[test]
    fn weight_complement_defaulting() {
        let raw = vec![(1i32, RawWeight::Rat(rat("0.4")))];
        let resolved = resolve_real_weights(1, &raw, None).unwrap();
        assert_eq!(resolved.weights[0], rat("0.4"));
        assert_eq!(resolved.weights[1], rat("0.6"));
        assert_eq!(resolved.warnings.len(), 1);
    }

    #[test]
    fn nonpositive_weight_without_complement_is_error() {
        let raw = vec![(1i32, RawWeight::Rat(rat("-0.5")))];
        assert!(resolve_real_weights(1, &raw, None).is_err());
    }

    #[test]
    fn negative_weight_with_complement_ok() {
        let raw = vec![
            (1i32, RawWeight::Rat(rat("-0.5"))),
            (-1i32, RawWeight::Rat(rat("1.5"))),
        ];
        let resolved = resolve_real_weights(1, &raw, None).unwrap();
        assert_eq!(resolved.weights[0], rat("-0.5"));
        assert_eq!(resolved.weights[1], rat("1.5"));
    }

    #[test]
    fn missing_terminator_on_show_is_error() {
        let text = "p cnf 2 1\nc p show 1 2\n1 0\n";
        assert!(parse_instance(text).is_err());
    }
}

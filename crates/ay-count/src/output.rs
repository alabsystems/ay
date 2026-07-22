// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model Counting Competition output rendering (format spec v1.2 §3).
//!
//! Mandatory lines: the `s` satisfiability line, `c s type`, the
//! `c s [neg]log10-estimate` line (two for complex results), and the
//! `c s SOLVERTYPE PRECISION NOTATION VALUE` solution line. All estimates are
//! rendered at 15 fractional digits; exact values render in `int` notation
//! for unweighted tracks, `frac` for weighted, and complex `a+bi` with
//! fractional parts for the algebraic track.

use num_bigint::{BigInt, BigUint};
use num_rational::BigRational;
use num_traits::{Signed, Zero};

use crate::engine::Stats;
use crate::parse::ProblemType;

/// Exact result value across the track value domains.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExactValue {
    /// Unweighted count (mc/pmc).
    Nat(BigUint),
    /// Weighted count (wmc/pwmc), exact rational.
    Rat(BigRational),
    /// Algebraic count (amc-complex): (real, imaginary).
    Complex(BigRational, BigRational),
}

impl ExactValue {
    /// True when the value is exactly zero.
    pub fn is_zero(&self) -> bool {
        match self {
            Self::Nat(n) => n.is_zero(),
            Self::Rat(r) => r.is_zero(),
            Self::Complex(re, im) => re.is_zero() && im.is_zero(),
        }
    }
}

/// A complete solve outcome ready for rendering.
#[derive(Debug)]
pub struct SolveOutcome {
    /// Problem type for the `c s type` line.
    pub ptype: ProblemType,
    /// Satisfiability for the `s` line (`None` renders UNKNOWN).
    pub satisfiable: Option<bool>,
    /// The exact count (`None` renders no solution lines, only UNKNOWN).
    pub value: Option<ExactValue>,
    /// Warnings to render as `c o WARNING` lines.
    pub warnings: Vec<String>,
    /// Engine statistics for `c o` lines (optional).
    pub stats: Option<Stats>,
}

/// log10 of a positive big integer, accurate to ~15 significant digits.
fn log10_biguint(n: &BigUint) -> f64 {
    debug_assert!(!n.is_zero());
    let decimal = n.to_str_radix(10);
    let leading_len = decimal.len().min(16);
    let leading: f64 = decimal[..leading_len]
        .parse()
        .expect("decimal digits parse as f64");
    leading.log10() + (decimal.len() - leading_len) as f64
}

/// log10 of |q| for a nonzero rational.
fn log10_abs_rational(q: &BigRational) -> f64 {
    let num = q.numer().magnitude();
    let den = q.denom().magnitude();
    log10_biguint(num) - log10_biguint(den)
}

fn estimate_lines(value: &ExactValue) -> Vec<String> {
    match value {
        ExactValue::Nat(n) => {
            if n.is_zero() {
                vec!["c s log10-estimate -inf".to_string()]
            } else {
                vec![format!("c s log10-estimate {:.15}", log10_biguint(n))]
            }
        }
        ExactValue::Rat(r) => {
            if r.is_zero() {
                vec!["c s log10-estimate -inf".to_string()]
            } else if r.is_negative() {
                vec![format!(
                    "c s neglog10-estimate {:.15}",
                    log10_abs_rational(r)
                )]
            } else {
                vec![format!("c s log10-estimate {:.15}", log10_abs_rational(r))]
            }
        }
        ExactValue::Complex(re, im) => {
            vec![
                part_estimate_line(re, "real"),
                part_estimate_line(im, "imag"),
            ]
        }
    }
}

fn part_estimate_line(part: &BigRational, suffix: &str) -> String {
    if part.is_zero() {
        format!("c s log10-estimate-{suffix} -inf")
    } else if part.is_negative() {
        format!(
            "c s neglog10-estimate-{suffix} {:.15}",
            log10_abs_rational(part)
        )
    } else {
        format!(
            "c s log10-estimate-{suffix} {:.15}",
            log10_abs_rational(part)
        )
    }
}

fn frac_str(q: &BigRational) -> String {
    format!("{}/{}", q.numer(), q.denom())
}

/// The complex value as `a+bi`/`a-bi` with fractional parts (no spaces).
fn complex_str(re: &BigRational, im: &BigRational) -> String {
    if im.is_negative() {
        let mag = BigRational::new(
            BigInt::from(im.numer().magnitude().clone()),
            im.denom().clone(),
        );
        format!("{}-{}i", frac_str(re), frac_str(&mag))
    } else {
        format!("{}+{}i", frac_str(re), frac_str(im))
    }
}

fn solution_line(value: &ExactValue) -> String {
    match value {
        ExactValue::Nat(n) => format!("c s exact arb int {n}"),
        ExactValue::Rat(r) => format!("c s exact arb frac {}", frac_str(r)),
        ExactValue::Complex(re, im) => {
            format!("c s exact arb frac {}", complex_str(re, im))
        }
    }
}

/// Render the complete competition output block.
pub fn render(outcome: &SolveOutcome) -> String {
    let mut out = String::new();
    out.push_str("c o ay exact model counter (component-caching DPLL)\n");
    for w in &outcome.warnings {
        out.push_str(&format!("c o WARNING {w}\n"));
    }
    let s_line = match outcome.satisfiable {
        Some(true) => "s SATISFIABLE",
        Some(false) => "s UNSATISFIABLE",
        None => "s UNKNOWN",
    };
    out.push_str(s_line);
    out.push('\n');
    out.push_str(&format!("c s type {}\n", outcome.ptype.as_str()));
    if let Some(value) = &outcome.value {
        for line in estimate_lines(value) {
            out.push_str(&line);
            out.push('\n');
        }
        out.push_str(&solution_line(value));
        out.push('\n');
    }
    if let Some(stats) = &outcome.stats {
        out.push_str(&format!(
            "c o decisions={} conflicts={} cache_hits={} cache_stores={} evictions={} purged={} components={} sat_oracle_calls={} failed_literals={} learned={} learned_units={} max_depth={}\n",
            stats.decisions,
            stats.conflicts,
            stats.cache_hits,
            stats.cache_stores,
            stats.cache_evictions,
            stats.cache_purged,
            stats.components,
            stats.sat_oracle_calls,
            stats.failed_literals,
            stats.learned_clauses,
            stats.learned_units,
            stats.max_depth,
        ));
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn renders_spec_example_1_shape() {
        let outcome = SolveOutcome {
            ptype: ProblemType::Mc,
            satisfiable: Some(true),
            value: Some(ExactValue::Nat(BigUint::from(22u32))),
            warnings: vec![],
            stats: None,
        };
        let text = render(&outcome);
        assert!(text.contains("s SATISFIABLE\n"));
        assert!(text.contains("c s type mc\n"));
        assert!(text.contains("c s log10-estimate 1.342422680822206\n"));
        assert!(text.contains("c s exact arb int 22\n"));
    }

    #[test]
    fn renders_zero_count_as_unsat_minus_inf() {
        let outcome = SolveOutcome {
            ptype: ProblemType::Mc,
            satisfiable: Some(false),
            value: Some(ExactValue::Nat(BigUint::zero())),
            warnings: vec![],
            stats: None,
        };
        let text = render(&outcome);
        assert!(text.contains("s UNSATISFIABLE\n"));
        assert!(text.contains("c s log10-estimate -inf\n"));
        assert!(text.contains("c s exact arb int 0\n"));
    }

    #[test]
    fn renders_negative_weighted_count() {
        let outcome = SolveOutcome {
            ptype: ProblemType::Wmc,
            satisfiable: Some(true),
            value: Some(ExactValue::Rat(BigRational::new((-3).into(), 10.into()))),
            warnings: vec![],
            stats: None,
        };
        let text = render(&outcome);
        assert!(text.contains("c s neglog10-estimate -0.522878745280338\n"));
        assert!(text.contains("c s exact arb frac -3/10\n"));
    }

    #[test]
    fn renders_complex_value_spec_example_5_shape() {
        // 0.55 - 1.1i => 11/20 - 11/10 i
        let outcome = SolveOutcome {
            ptype: ProblemType::AmcComplex,
            satisfiable: Some(true),
            value: Some(ExactValue::Complex(
                BigRational::new(11.into(), 20.into()),
                BigRational::new((-11).into(), 10.into()),
            )),
            warnings: vec![],
            stats: None,
        };
        let text = render(&outcome);
        assert!(text.contains("c s type amc-complex\n"));
        assert!(text.contains("c s log10-estimate-real -0.259637310505756\n"));
        assert!(text.contains("c s neglog10-estimate-imag 0.041392685158225\n"));
        assert!(text.contains("c s exact arb frac 11/20-11/10i\n"));
    }

    #[test]
    fn big_log10_estimate_is_accurate() {
        // 2^70 = 1180591620717411303424; log10 = 70*log10(2) = 21.0721...
        let n = BigUint::from(1u8) << 70;
        let est = log10_biguint(&n);
        assert!((est - 21.072_099_696_478_683).abs() < 1e-12);
    }
}

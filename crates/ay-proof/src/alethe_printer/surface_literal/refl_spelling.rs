// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Two printed spellings pinned Carcara's `refl` equates: numeric constants
//! written two ways, and equalities written in either operand order.
//!
//! Carcara 1.1.0 (git 9a352ee) checks `refl` up to its term identity, which
//! folds a signed or divided numeric constant and reorders `=`. MEASURED
//! there, each as `(step t1 (cl (= S T)) :rule refl)`: valid for
//! `(= (= -2 x) (= y -3))`/`(= (= y (- 3)) (= x -2))`, `(< x -2)`/`(< x (- 2.0))`,
//! `(< x -2.5)`/`(< x (- (/ 5.0 2.0))))`, `(> -2 x)`/`(> (- 2) x)`,
//! `(not (= 0 x))`/`(not (= x -0))` and `(or (= (f -1) y) p)`/`(or (= y (f (-
//! 1))) p)`; invalid for `-0`/`(- 0)` (d0e349259b), `(> -2 x)`/`(< x (- 2))`
//! (a different operator) and `(not (>= x -3))`/`(not (<= (- 3) x))`.
//!
//! So the judge compares two printed trees where (a) a NONZERO numeric
//! constant — `N`, `-N`, `N.M`, `-N.M`, `(- c)`, `(/ c d)`, `(- (/ c d))` over
//! unsigned literals — is read by its value, (b) a zero is only one of the
//! atoms `0`, `-0`, `0.0`, `-0.0`, never `(- 0)`, and (c) the two operands of
//! a binary `=` may be swapped. Anything else is compared token for token;
//! the judge is narrower than the checker, never wider.

use super::*;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::Zero;

const MAX_REFL_BYTES: usize = 64 * 1024;
const MAX_REFL_DEPTH: usize = 64;
const MAX_REFL_NODES: usize = 4096;

/// `(step id (cl (= left right)) :rule refl)` when pinned Carcara's `refl`
/// equates the two printed terms and they differ in bytes; `None` otherwise.
pub(in crate::alethe_printer) fn carcara_refl_steps(
    id: &str,
    left: &str,
    right: &str,
) -> Option<Vec<String>> {
    if left == right || left.len() > MAX_REFL_BYTES || right.len() > MAX_REFL_BYTES {
        return None;
    }
    let mut nodes = 0;
    refl_equal(left, right, 0, &mut nodes)
        .then(|| vec![format!("(step {id} (cl (= {left} {right})) :rule refl)")])
}

/// `text` with every bare negative literal (`-2`, `-2.5`) written the way the
/// printer renders the constant (`(- 2)`, `(- (/ 5.0 2.0))`), or `None` when
/// it has none. A caller pairs the result with `text` by [`carcara_refl_steps`].
pub(in crate::alethe_printer) fn canonical_literal_respelling(text: &str) -> Option<String> {
    if text.len() > MAX_REFL_BYTES {
        return None;
    }
    let mut changed = false;
    let mut nodes = 0;
    let respelled = respell(text, 0, &mut nodes, &mut changed)?;
    changed.then_some(respelled)
}

fn respell(text: &str, depth: usize, nodes: &mut usize, changed: &mut bool) -> Option<String> {
    *nodes += 1;
    if depth > MAX_REFL_DEPTH || *nodes > MAX_REFL_NODES {
        return None;
    }
    let Some(inner) = text.strip_prefix('(').and_then(|t| t.strip_suffix(')')) else {
        let Some(magnitude) = text.strip_prefix('-') else {
            return Some(text.to_string());
        };
        let Some(value) = unsigned_literal(magnitude) else {
            return Some(text.to_string());
        };
        if value.is_zero() {
            return Some(text.to_string());
        }
        *changed = true;
        return Some(if magnitude.contains('.') {
            let rational = Constant::Rational(ay_core::RationalWrapper(-value));
            AlethePrinter::format_constant(&rational)
        } else {
            format!("(- {magnitude})")
        });
    };
    let parts = split_smt_terms(inner)?;
    let rendered = parts
        .iter()
        .map(|part| respell(part, depth + 1, nodes, changed))
        .collect::<Option<Vec<_>>>()?;
    Some(format!("({})", rendered.join(" ")))
}

/// An unsigned numeral or decimal token's value.
fn unsigned_literal(text: &str) -> Option<BigRational> {
    let digits = |part: &str| !part.is_empty() && part.bytes().all(|byte| byte.is_ascii_digit());
    let (whole, fraction) = text.split_once('.').unwrap_or((text, ""));
    if !digits(whole) || !(fraction.is_empty() || digits(fraction)) || text.ends_with('.') {
        return None;
    }
    let scale = BigInt::from(10u8).pow(u32::try_from(fraction.len()).ok()?);
    Some(BigRational::new(
        format!("{whole}{fraction}").parse().ok()?,
        scale,
    ))
}

/// How the judge reads one printed node.
enum Reading {
    Zero,
    Nonzero(BigRational),
    Other,
}

fn read_constant(text: &str) -> Reading {
    let value = if let Some(inner) = text.strip_prefix('(').and_then(|t| t.strip_suffix(')')) {
        let Some(parts) = split_smt_terms(inner) else {
            return Reading::Other;
        };
        match parts.as_slice() {
            [minus, operand] if minus == "-" => match read_constant(operand) {
                // `(- 0)` is not `0` to the checker.
                Reading::Nonzero(value) => Some(-value),
                _ => None,
            },
            [slash, numerator, denominator] if slash == "/" => {
                match (unsigned_literal(numerator), unsigned_literal(denominator)) {
                    (Some(n), Some(d)) if !d.is_zero() && !n.is_zero() => Some(n / d),
                    _ => None,
                }
            }
            _ => None,
        }
    } else if let Some(magnitude) = text.strip_prefix('-') {
        match unsigned_literal(magnitude) {
            Some(value) if value.is_zero() => return Reading::Zero,
            Some(value) => Some(-value),
            None => None,
        }
    } else {
        match unsigned_literal(text) {
            Some(value) if value.is_zero() => return Reading::Zero,
            other => other,
        }
    };
    value.map_or(Reading::Other, Reading::Nonzero)
}

fn refl_equal(left: &str, right: &str, depth: usize, nodes: &mut usize) -> bool {
    if left == right {
        return true;
    }
    *nodes += 1;
    if depth > MAX_REFL_DEPTH || *nodes > MAX_REFL_NODES {
        return false;
    }
    match (read_constant(left), read_constant(right)) {
        (Reading::Zero, Reading::Zero) => return true,
        (Reading::Nonzero(a), Reading::Nonzero(b)) => return a == b,
        (Reading::Other, Reading::Other) => {}
        _ => return false,
    }
    let (Some(left_inner), Some(right_inner)) = (
        left.strip_prefix('(').and_then(|t| t.strip_suffix(')')),
        right.strip_prefix('(').and_then(|t| t.strip_suffix(')')),
    ) else {
        return false;
    };
    let (Some(left_parts), Some(right_parts)) =
        (split_smt_terms(left_inner), split_smt_terms(right_inner))
    else {
        return false;
    };
    if left_parts.len() != right_parts.len() || left_parts.first() != right_parts.first() {
        return false;
    }
    let mut pairwise = |order: &[usize]| {
        left_parts
            .iter()
            .skip(1)
            .zip(order.iter().map(|&index| &right_parts[index]))
            .all(|(l, r)| refl_equal(l, r, depth + 1, nodes))
    };
    let in_order: Vec<usize> = (1..right_parts.len()).collect();
    if pairwise(&in_order) {
        return true;
    }
    left_parts.len() == 3 && left_parts[0] == "=" && pairwise(&[2, 1])
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Every row MEASURED as a one-step `refl` document against pinned
    /// Carcara 1.1.0 (git 9a352ee) on 2026-10-02.
    #[test]
    fn refl_is_judged_as_pinned_carcara_checks_it() {
        for (left, right, valid) in [
            ("(= -2 x)", "(= x -2)", true),
            ("(= -2 x)", "(= x (- 2))", true),
            ("(= 2 x)", "(= x 2)", true),
            ("(and (= -2 x) p)", "(and (= x (- 2)) p)", true),
            ("(or (= (f -1) y) p)", "(or (= y (f (- 1))) p)", true),
            ("(= (= -2 x) (= y -3))", "(= (= x (- 2)) (= (- 3) y))", true),
            ("(= (= -2 x) (= y -3))", "(= (= y (- 3)) (= x -2))", true),
            ("(not (= 0 x))", "(not (= x -0))", true),
            ("(< x -2.5)", "(< x (- (/ 5.0 2.0)))", true),
            ("(< x -2)", "(< x (- 2.0))", true),
            ("(> -2 x)", "(> (- 2) x)", true),
            ("-2", "(- 2)", true),
            ("-0", "0", true),
            ("-0", "(- 0)", false),
            ("-2", "(- 3)", false),
            ("(> -2 x)", "(< x (- 2))", false),
            ("(not (>= x -3))", "(not (<= (- 3) x))", false),
            ("(< x y)", "(< y x)", false),
            ("(f x y)", "(f y x)", false),
        ] {
            assert_eq!(
                carcara_refl_steps("t", left, right).is_some(),
                valid,
                "{left} / {right}"
            );
        }
        assert_eq!(carcara_refl_steps("t", "(< x 1)", "(< x 1)"), None);
    }

    #[test]
    fn a_bare_negative_literal_is_respelled_as_the_printer_renders_its_constant() {
        assert_eq!(
            canonical_literal_respelling("(> -2 x)").as_deref(),
            Some("(> (- 2) x)")
        );
        assert_eq!(
            canonical_literal_respelling("(not (>= x -2.5))").as_deref(),
            Some("(not (>= x (- (/ 5.0 2.0))))")
        );
        assert_eq!(
            canonical_literal_respelling("(< x -2.0)").as_deref(),
            Some("(< x (- 2.0))")
        );
        assert_eq!(canonical_literal_respelling("(< x -0)"), None);
        assert_eq!(canonical_literal_respelling("(< x (- 2))"), None);
        assert_eq!(canonical_literal_respelling("|-2|"), None);
    }
}

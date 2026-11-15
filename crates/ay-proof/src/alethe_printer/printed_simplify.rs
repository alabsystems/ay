// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `comp_simplify` and `evaluate` judged over the bytes they ship.
//!
//! Both rules are checked by pinned Carcara 1.1.0 (git 9a352ee) on the PRINTED
//! terms, while AY derives the steps over its term store, where `(> x x)` and
//! `(< x x)`, or `-4` and `(- 4)`, are one value. Two shipped steps showed the
//! gap: the comparison-reversal chain's `(= (not (<= x x)) (< x x)) :rule
//! comp_simplify` and `(= (+ (- 2) (- 2)) (- 4)) :rule evaluate` were both
//! derived soundly and refused by Carcara. Their producers are fixed; this is
//! the chokepoint that keeps any other producer from shipping such a step:
//! like `judge_printed_la_disequality`, a refused command declines its step to
//! the honest hole over the step's own clause.
//!
//! `comp_simplify`, MEASURED (each a one-step document): Carcara rewrites the
//! left side one rule at a time and accepts as soon as it equals the right
//! side, else does the same from the right side; it never accepts before one
//! rewrite (`(= (< x 5) (< x 5))` fails). The rules, in Carcara's order:
//! `(< c1 c2)` and `(<= c1 c2)` over numbers fold to `true`/`false`;
//! `(>= t1 t2)` is `(<= t2 t1)`; `(> t1 t2)` is `(not (<= t1 t2))`, even over
//! numbers and for `t1 = t2` (`(= (> x x) (not (<= x x)))` passes, `(= (> (- 2)
//! (- 3)) true)` fails); `(< t t)` is `false`, `(<= t t)` is `true`; and
//! `(< t1 t2)` is `(not (<= t2 t1))`. The judge replays exactly that, and
//! declines whatever it cannot read exactly: a comparison of two closed terms
//! that are not both plain numbers, and two operands that differ in text but
//! might parse to one term.
//!
//! `evaluate`, MEASURED: the conclusion is `(= t v)`, and Carcara compares the
//! value of `t` with `v` as a term, so `v` must be a literal (`4`, `-4`,
//! `4.0`, `-2.5`, `true`, a bit-vector or string literal); `(- 4)` and
//! `(/ 5.0 2.0)` are applications and fail.

use super::la_generic_surface::{printed_step_definitions, StepDefinitions};
use super::printed_command::{printed_commands, rendered_rule_field_names, PrintedCommandRead};
use super::surface_tokens::split_alethe_application_bounded;
use super::*;
use num_rational::BigRational;

const COMP_SIMPLIFY: &str = "comp_simplify";
const EVALUATE: &str = "evaluate";

/// Rewrites tried from one side before the judge gives up; Carcara's own
/// chains are at most three long (`(> a b)` never rewrites twice).
const MAX_REWRITES: usize = 4;

/// The arguments of the printed application `(op a1 .. an)`, or `None`.
fn application<'t>(text: &'t str, op: &str) -> Option<Vec<&'t str>> {
    split_alethe_application_bounded(text, op, usize::MAX, usize::MAX).ok()
}

/// A plain number Carcara folds: a numeral or decimal, signed or not, or
/// `(- n)` of one.
fn plain_number(text: &str) -> Option<BigRational> {
    if let Some(inner) = application(text, "-") {
        let [operand] = inner.as_slice() else {
            return None;
        };
        return unsigned_number(operand).map(|value| -value);
    }
    match text.strip_prefix('-') {
        Some(magnitude) => unsigned_number(magnitude).map(|value| -value),
        None => unsigned_number(text),
    }
}

fn unsigned_number(text: &str) -> Option<BigRational> {
    let digits = |part: &str| !part.is_empty() && part.bytes().all(|byte| byte.is_ascii_digit());
    let (whole, fraction) = text.split_once('.').unwrap_or((text, ""));
    if !digits(whole) || !(fraction.is_empty() || digits(fraction)) || text.ends_with('.') {
        return None;
    }
    let scale = num_bigint::BigInt::from(10u8).pow(u32::try_from(fraction.len()).ok()?);
    let numerator = format!("{whole}{fraction}")
        .parse::<num_bigint::BigInt>()
        .ok()?;
    Some(BigRational::new(numerator, scale))
}

/// Whether `text` names no symbol: digits, signs and arithmetic only. Two
/// such operands that are not both [`plain_number`]s may be folded by Carcara
/// in a way this judge does not model, so it declines them.
fn is_closed_arithmetic(text: &str) -> bool {
    text.bytes()
        .all(|byte| byte.is_ascii_digit() || b"-+*/.() \t\n".contains(&byte))
}

/// `text` with every `(- n)` of an unsigned number written `-n`: two
/// operands that differ in bytes but agree here may be one Carcara term.
fn number_spelling_key(text: &str) -> String {
    let mut key = String::with_capacity(text.len());
    let mut rest = text;
    while let Some(at) = rest.find("(- ") {
        key.push_str(&rest[..at]);
        let after = &rest[at + 3..];
        let end = after.find(')').unwrap_or(after.len());
        let operand = &after[..end];
        if end < after.len() && unsigned_number(operand).is_some() {
            key.push('-');
            key.push_str(operand);
            rest = &after[end + 1..];
        } else {
            key.push_str("(- ");
            rest = after;
        }
    }
    key.push_str(rest);
    key
}

/// The comparison `(op a b)` read from `text`.
fn comparison(text: &str) -> Option<(&'static str, String, String)> {
    for op in ["<", "<=", ">", ">="] {
        if let Some(operands) = application(text, op) {
            let [left, right] = operands.as_slice() else {
                return None;
            };
            return Some((op, (*left).to_string(), (*right).to_string()));
        }
    }
    None
}

/// What one Carcara `comp_simplify` rewrite does to `text`.
enum Rewrite {
    To(String),
    /// No rule applies.
    Stuck,
    /// A rule might apply in a way this judge does not model.
    Unknown,
}

fn rewrite(text: &str) -> Rewrite {
    let Some((op, left, right)) = comparison(text) else {
        return Rewrite::Stuck;
    };
    let folds = matches!(op, "<" | "<=");
    if folds {
        match (plain_number(&left), plain_number(&right)) {
            (Some(a), Some(b)) => {
                let holds = if op == "<" { a < b } else { a <= b };
                return Rewrite::To(holds.to_string());
            }
            _ if is_closed_arithmetic(&left) && is_closed_arithmetic(&right) => {
                return Rewrite::Unknown;
            }
            _ => {}
        }
        if left != right && number_spelling_key(&left) == number_spelling_key(&right) {
            return Rewrite::Unknown;
        }
    }
    Rewrite::To(match op {
        ">=" => format!("(<= {right} {left})"),
        ">" => format!("(not (<= {left} {right}))"),
        "<" if left == right => "false".to_string(),
        "<=" if left == right => "true".to_string(),
        "<" => format!("(not (<= {right} {left}))"),
        _ => return Rewrite::Stuck,
    })
}

/// Whether rewriting `from` reaches `goal` after at least one rewrite;
/// `None` when the chase meets a rewrite the judge does not model.
fn chase(from: &str, goal: &str) -> Option<bool> {
    let mut current = from.to_string();
    for _ in 0..MAX_REWRITES {
        match rewrite(&current) {
            Rewrite::To(next) => current = next,
            Rewrite::Stuck => return Some(false),
            Rewrite::Unknown => return None,
        }
        if current == goal {
            return Some(true);
        }
    }
    Some(false)
}

/// Whether a printed `comp_simplify` conclusion is an instance of the rule as
/// pinned Carcara checks it. A name the step defines (`define-fun`) is read
/// as the term it names, as the checker inlines it.
pub(super) fn printed_comp_simplify_holds<'t>(
    conclusion: &[&'t str],
    definitions: &StepDefinitions<'t>,
) -> bool {
    let [equality] = conclusion else {
        return false;
    };
    let Some(sides) = definitions
        .inline_top(equality)
        .and_then(|equality| application(equality, "="))
    else {
        return false;
    };
    let [left, right] = sides.as_slice() else {
        return false;
    };
    let (Some(left), Some(right)) = (definitions.inline_top(left), definitions.inline_top(right))
    else {
        return false;
    };
    chase(left, right) == Some(true) || chase(right, left) == Some(true)
}

/// Whether Carcara reads `text` as a literal value.
fn is_literal_value(text: &str) -> bool {
    if matches!(text, "true" | "false") || plain_literal_number(text) {
        return true;
    }
    if let Some(digits) = text.strip_prefix("#b") {
        return !digits.is_empty() && digits.bytes().all(|byte| matches!(byte, b'0' | b'1'));
    }
    if let Some(digits) = text.strip_prefix("#x") {
        return !digits.is_empty() && digits.bytes().all(|byte| byte.is_ascii_hexdigit());
    }
    if text.len() >= 2 && text.starts_with('"') && text.ends_with('"') {
        return true;
    }
    application(text, "_").is_some_and(|indexed| match indexed.as_slice() {
        [value, width] => {
            value
                .strip_prefix("bv")
                .is_some_and(|digits| unsigned_number(digits).is_some() && !digits.contains('.'))
                && unsigned_number(width).is_some()
                && !width.contains('.')
        }
        _ => false,
    })
}

/// A numeral or decimal token, signed or not; never `(- n)`.
fn plain_literal_number(text: &str) -> bool {
    !text.starts_with('(') && plain_number(text).is_some()
}

/// Whether a printed `evaluate` conclusion has the `(= t v)` shape Carcara
/// checks, with `v` a literal; step-defined names read as the terms they name.
pub(super) fn printed_evaluate_value_is_literal<'t>(
    conclusion: &[&'t str],
    definitions: &StepDefinitions<'t>,
) -> bool {
    let [equality] = conclusion else {
        return false;
    };
    definitions
        .inline_top(equality)
        .and_then(|equality| application(equality, "="))
        .is_some_and(|sides| match sides.as_slice() {
            [evaluated, value] => {
                definitions.inline_top(value).is_some_and(is_literal_value)
                    && definitions
                        .inline_top(evaluated)
                        .is_some_and(integer_division_is_truncation_safe)
            }
            _ => false,
        })
}

/// The balanced parenthesized term starting at byte `start` of `text`.
fn balanced_from(text: &str, start: usize) -> Option<&str> {
    let mut depth = 0usize;
    for (offset, byte) in text.as_bytes()[start..].iter().enumerate() {
        match byte {
            b'(' => depth += 1,
            b')' => {
                depth = depth.checked_sub(1)?;
                if depth == 0 {
                    return text.get(start..=start + offset);
                }
            }
            _ => {}
        }
    }
    None
}

/// Whether every printed `div` / `mod` in `evaluated` divides an unsigned
/// numeral, and no `rem` appears: pinned Carcara's `evaluate` divides by
/// TRUNCATION (MEASURED: `(= (div (- 7) 2) -4)` fails with "'-3' and '-4'",
/// `(= (mod (- 7) 2) 1)` with "'-1' and '1'"), which agrees with SMT-LIB only
/// for a non-negative dividend (`(div 7 (- 2))` is `-3` to both). The side's
/// own top-level step name is inlined by the caller; the step-local names
/// below it (`mul_overflow_cert`'s) are bit-vector terms.
fn integer_division_is_truncation_safe(evaluated: &str) -> bool {
    if evaluated.contains("(rem ") {
        return false;
    }
    for op in ["div", "mod"] {
        let needle = format!("({op} ");
        let mut from = 0;
        while let Some(at) = evaluated[from..].find(&needle) {
            let start = from + at;
            let Some(arguments) =
                balanced_from(evaluated, start).and_then(|term| application(term, op))
            else {
                return false;
            };
            let unsigned_numeral = arguments.first().is_some_and(|dividend| {
                !dividend.is_empty() && dividend.bytes().all(|byte| byte.is_ascii_digit())
            });
            if !unsigned_numeral {
                return false;
            }
            from = start + needle.len();
        }
    }
    true
}

impl AlethePrinter<'_> {
    /// Judge every `:rule comp_simplify` and `:rule evaluate` command in one
    /// rendered step; a refusal declines the step to the honest hole over its
    /// own clause, or declines the export where the step has no clause.
    pub(super) fn judge_printed_simplify(
        &self,
        step: &ProofStep,
        id: ProofId,
        rendered: String,
    ) -> Result<String, AlethePrintError> {
        if !rendered.contains(COMP_SIMPLIFY) && !rendered.contains(EVALUATE) {
            return Ok(rendered);
        }
        let definitions = printed_step_definitions(&rendered);
        let holds = |rule: &str, conclusion: &[&str]| match rule {
            COMP_SIMPLIFY => printed_comp_simplify_holds(conclusion, &definitions),
            _ => printed_evaluate_value_is_literal(conclusion, &definitions),
        };
        let refused = match printed_commands(&rendered) {
            Ok(commands) => commands.iter().find_map(|command| match command {
                PrintedCommandRead::Command(command) => match command.rule() {
                    Some(rule @ (COMP_SIMPLIFY | EVALUATE)) => {
                        let accepted = command
                            .conclusion()
                            .is_some_and(|conclusion| holds(rule, &conclusion));
                        (!accepted).then(|| (rule, command.name().unwrap_or("?").to_string()))
                    }
                    _ => None,
                },
                PrintedCommandRead::Unsplittable(text) => {
                    rendered_rule_field_names(text, &[COMP_SIMPLIFY, EVALUATE])
                        .then(|| ("comp_simplify/evaluate", id.to_string()))
                }
            }),
            Err(_) => rendered_rule_field_names(&rendered, &[COMP_SIMPLIFY, EVALUATE])
                .then(|| ("comp_simplify/evaluate", id.to_string())),
        };
        let Some((rule, refused_name)) = refused else {
            return Ok(rendered);
        };
        let clause: Option<&[TermId]> = match step {
            ProofStep::Resolution { clause, .. }
            | ProofStep::TheoryLemma { clause, .. }
            | ProofStep::FiniteFieldLinear { clause, .. }
            | ProofStep::NraSos { clause, .. }
            | ProofStep::Step { clause, .. } => Some(clause),
            _ => None,
        };
        let Some(clause) = clause else {
            return Err(AlethePrintError::InvalidSurfaceStep {
                id,
                reason: format!(
                    "printed step `{refused_name}` is not an instance of {rule} over the text it ships"
                ),
            });
        };
        Ok(format!(
            "(step {id} {} :rule {})",
            self.format_clause(clause),
            ay_core::UNPROVED_STEP_RULE
        ))
    }
}

#[cfg(test)]
#[path = "printed_simplify_tests.rs"]
mod tests;

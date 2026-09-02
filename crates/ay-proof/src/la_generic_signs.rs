// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Carcara-faithful signing of Alethe `la_generic` coefficients, computed over
//! the **printed** atom strings (exactly what an external checker parses).
//!
//! The internal certificate keeps non-negative Farkas magnitudes and lets the
//! validator search either orientation of each equality. Alethe's `la_generic`
//! has no such search: the printed equality coefficient is signed, and the
//! checker forms the single linear combination the args dictate, reading atoms
//! from the printed proof. AY's printer applies surface-syntax overrides that
//! may reorient an equality (e.g. `(= (* 2 r2) -7)` is printed
//! `(= (- (* 2 r2)) 7)`), so resolving signs from the INTERNAL term orientation
//! can disagree with the printed orientation the checker actually sees.
//!
//! This module parses the linear form out of the printed strings and searches
//! the equality signs against a SOUND reconstruction of Carcara's acceptance
//! test:
//!   - each hypothesis `¬(clause literal)` normalizes to `e >= 0` / `e > 0`
//!     (inequality) or `e = 0` (equality), `e` in the `lhs - rhs` orientation;
//!   - inequality coefficients are applied in magnitude (Carcara fixes the
//!     inequality orientation, ignoring the printed sign), equalities signed;
//!   - the step is accepted iff the weighted sum eliminates every variable and
//!     leaves either a STRICTLY NEGATIVE constant, or zero with at least one
//!     nonzero-weighted strict inequality. Both are contradictions under the
//!     normalized hypotheses (and survive integer strengthening), so the check
//!     never false-accepts.
//!
//! Emission-only: this changes only the printed coefficients of an
//! already-decided UNSAT proof; it never affects a verdict, and it substitutes
//! a repaired vector only when the sound check accepts it.

use std::collections::BTreeMap;

use num_bigint::BigInt;
use num_rational::{BigRational, Rational64};
use num_traits::{One, Signed, Zero};

#[path = "la_generic_surface_audit.rs"]
mod surface_audit;
pub use surface_audit::{
    format_terms_alethe_with_overrides_and_canonical_bounded,
    format_terms_alethe_with_overrides_and_canonical_bounded_with_work,
    format_terms_alethe_with_overrides_bounded, printed_la_generic_certificate_is_valid_bounded,
};

/// A linear form over printed variable names plus a rational constant.
#[derive(Clone, Debug, Default)]
struct Lin {
    coeffs: BTreeMap<String, BigRational>,
    constant: BigRational,
}

impl Lin {
    fn constant(c: BigRational) -> Self {
        Self {
            coeffs: BTreeMap::new(),
            constant: c,
        }
    }

    fn var(name: String) -> Self {
        let mut coeffs = BTreeMap::new();
        coeffs.insert(name, BigRational::one());
        Self {
            coeffs,
            constant: BigRational::zero(),
        }
    }

    fn is_constant(&self) -> bool {
        self.coeffs.is_empty()
    }

    fn add_scaled(&mut self, other: &Lin, scale: &BigRational) {
        if scale.is_zero() {
            return;
        }
        self.constant += scale * &other.constant;
        for (v, c) in &other.coeffs {
            let entry = self
                .coeffs
                .entry(v.clone())
                .or_insert_with(BigRational::zero);
            *entry += scale * c;
            if entry.is_zero() {
                self.coeffs.remove(v);
            }
        }
    }

    fn scale(&mut self, s: &BigRational) {
        if s.is_one() {
            return;
        }
        self.constant *= s;
        if s.is_zero() {
            self.coeffs.clear();
            return;
        }
        for c in self.coeffs.values_mut() {
            *c *= s;
        }
    }

    fn negate(&mut self) {
        self.constant = -std::mem::take(&mut self.constant);
        for c in self.coeffs.values_mut() {
            *c = -std::mem::take(c);
        }
    }
}

/// Split the top-level whitespace-separated s-expression tokens/subforms of
/// `s` (an already-trimmed expression). `(f a b)` yields `["f", "a", "b"]`,
/// respecting nested parentheses; a bare atom yields the atom itself.
pub(crate) fn carcara_quoted_symbols_are_lexically_supported(s: &str) -> bool {
    #[derive(Clone, Copy, Eq, PartialEq)]
    enum Mode {
        Normal,
        QuotedSymbol,
        String,
    }

    let bytes = s.as_bytes();
    let mut mode = Mode::Normal;
    let mut index = 0usize;
    while index < bytes.len() {
        match (mode, bytes[index]) {
            (Mode::Normal, b'|') => mode = Mode::QuotedSymbol,
            (Mode::Normal, b'"') => mode = Mode::String,
            (Mode::Normal, b'\\') => return false,
            // Pinned Carcara follows SMT-LIB's quoted-symbol grammar and
            // rejects backslash outright; AY/Z3's `\|` / `\\` extension must
            // never be granted wire-rule authority.
            (Mode::QuotedSymbol, b'\\') => return false,
            (Mode::QuotedSymbol, b'|') => mode = Mode::Normal,
            (Mode::String, b'"') if bytes.get(index + 1) == Some(&b'"') => index += 1,
            (Mode::String, b'"') => mode = Mode::Normal,
            _ => {}
        }
        index += 1;
    }
    mode == Mode::Normal
}

fn split_sexpr(s: &str) -> Option<Vec<String>> {
    const MAX_FIELDS: usize = 100_000;
    const MAX_BYTES: usize = 1024 * 1024;
    let s = s.trim();
    if !carcara_quoted_symbols_are_lexically_supported(s) {
        return None;
    }
    if !s.starts_with('(') {
        let fields = crate::alethe_printer::split_smt_term_slices_bounded(s, 1, MAX_BYTES).ok()?;
        return (fields == [s]).then(|| vec![s.to_string()]);
    }
    let inner = s.strip_prefix('(')?.strip_suffix(')')?;
    crate::alethe_printer::split_smt_term_slices_bounded(inner, MAX_FIELDS, MAX_BYTES)
        .ok()
        .map(|fields| fields.into_iter().map(str::to_string).collect())
}

/// Parse a decimal / integer numeral token (`7.0`, `-5`, `45.0`) into a
/// rational, or `None` if it is not a numeral (i.e. a variable name).
fn parse_numeral(tok: &str) -> Option<BigRational> {
    let (neg, body) = match tok.strip_prefix('-') {
        Some(rest) => (true, rest),
        None => (false, tok),
    };
    if body.is_empty() || !body.as_bytes().first().is_some_and(u8::is_ascii_digit) {
        return None;
    }
    let val = if let Some(slash) = body.find('/') {
        let numerator = &body[..slash];
        let denominator = &body[slash + 1..];
        if numerator.len() > 1 && numerator.starts_with('0')
            || denominator.is_empty()
            || !numerator.bytes().all(|byte| byte.is_ascii_digit())
            || !denominator.bytes().all(|byte| byte.is_ascii_digit())
        {
            return None;
        }
        let numerator = numerator.parse::<BigInt>().ok()?;
        let denominator = denominator.parse::<BigInt>().ok()?;
        if denominator.is_zero() {
            return None;
        }
        BigRational::new(numerator, denominator)
    } else if let Some(dot) = body.find('.') {
        let int_part = &body[..dot];
        let frac_part = &body[dot + 1..];
        if int_part.is_empty()
            || int_part.len() > 1 && int_part.starts_with('0')
            || !int_part.chars().all(|c| c.is_ascii_digit())
            || !frac_part.chars().all(|c| c.is_ascii_digit())
        {
            return None;
        }
        let combined = format!("{int_part}{frac_part}");
        let numer: BigInt = combined.parse().ok()?;
        let denom = BigInt::from(10u32).pow(frac_part.len() as u32);
        BigRational::new(numer, denom)
    } else {
        if body.len() > 1 && body.starts_with('0') || !body.chars().all(|c| c.is_ascii_digit()) {
            return None;
        }
        BigRational::from(body.parse::<BigInt>().ok()?)
    };
    Some(if neg { -val } else { val })
}

/// Parse a printed arithmetic term string into a linear form. Any subterm the
/// grammar does not linearize (an uninterpreted application, `mod`, `select`,
/// …) becomes an opaque variable keyed by its exact printed string — matching
/// how an external checker treats it as an atom.
fn parse_lin(s: &str) -> Option<Lin> {
    let s = s.trim();
    if !s.starts_with('(') {
        return match parse_numeral(s) {
            Some(r) => Some(Lin::constant(r)),
            None if printed_atom_starts_like_carcara_number(s) => None,
            None if carcara_bare_linear_atom_is_supported(s) => Some(Lin::var(s.to_string())),
            None => None,
        };
    }
    let parts = split_sexpr(s)?;
    if parts.is_empty() {
        return None;
    }
    let op = parts[0].as_str();
    let args = &parts[1..];
    match op {
        "+" => {
            let mut acc = Lin::default();
            for a in args {
                acc.add_scaled(&parse_lin(a)?, &BigRational::one());
            }
            Some(acc)
        }
        "-" if args.len() == 1 => {
            let mut e = parse_lin(&args[0])?;
            e.negate();
            Some(e)
        }
        "-" if args.len() >= 2 => {
            let mut acc = parse_lin(&args[0])?;
            for a in &args[1..] {
                let mut sub = parse_lin(a)?;
                sub.negate();
                acc.add_scaled(&sub, &BigRational::one());
            }
            Some(acc)
        }
        "*" => {
            let mut const_part = BigRational::one();
            let mut non_const: Option<Lin> = None;
            for a in args {
                let sub = parse_lin(a)?;
                if sub.is_constant() {
                    const_part *= sub.constant;
                } else if non_const.is_none() {
                    non_const = Some(sub);
                } else {
                    // A product with two symbolic factors is outside linear
                    // arithmetic.  Do not treat it as an opaque variable:
                    // Carcara normalizes arithmetic applications and can
                    // reject a certificate that merely cancels the printed
                    // non-linear syntax as though it were an EUF atom.
                    return None;
                }
            }
            Some(match non_const {
                Some(mut e) => {
                    e.scale(&const_part);
                    e
                }
                None => Lin::constant(const_part),
            })
        }
        "/" if args.len() == 2 => {
            let mut num = parse_lin(&args[0])?;
            let den = parse_lin(&args[1])?;
            if den.is_constant() && !den.constant.is_zero() {
                let inv = BigRational::one() / den.constant;
                num.scale(&inv);
                Some(num)
            } else {
                Some(Lin::var(s.to_string()))
            }
        }
        _ => Some(Lin::var(s.to_string())),
    }
}

fn printed_atom_starts_like_carcara_number(atom: &str) -> bool {
    let bytes = atom.as_bytes();
    bytes.first().is_some_and(u8::is_ascii_digit)
        || matches!(bytes, [b'-', next, ..] if next.is_ascii_digit())
}

fn carcara_bare_linear_atom_is_supported(atom: &str) -> bool {
    if atom.starts_with('|') {
        return atom.ends_with('|') && atom.len() >= 2;
    }
    !matches!(atom.as_bytes().first(), Some(b':' | b'#' | b'"'))
        && !matches!(
            atom,
            "true"
                | "false"
                | "_"
                | "!"
                | "as"
                | "let"
                | "exists"
                | "forall"
                | "match"
                | "choice"
                | "lambda"
                | "cl"
                | "assume"
                | "step"
                | "anchor"
                | "declare-fun"
                | "declare-const"
                | "declare-sort"
                | "declare-datatype"
                | "declare-datatypes"
                | "par"
                | "define-fun"
                | "define-fun-rec"
                | "define-funs-rec"
                | "define-sort"
                | "assert"
                | "check-sat-assuming"
                | "set-logic"
                | "declare-rare-rule"
        )
}

/// Conservative Carcara-faithful term grammar for the authored-assume
/// arithmetic implication bridge.
///
/// The bridge needs only ordinary sums/subtractions and direct numeric
/// scaling.  In particular it deliberately rejects multiplication whose
/// coefficient is computed (`(* (+ 1 1) x)`) and opaque nonlinear products:
/// the former is interpreted differently by AY and Carcara, while the latter
/// is unnecessary for this narrow source-to-canonical normalization lane.
fn carcara_bridge_linear_term_supported(
    printed: &str,
    depth: usize,
    nodes_left: &mut usize,
) -> bool {
    const MAX_DEPTH: usize = 256;
    if depth > MAX_DEPTH {
        return false;
    }
    let Some(remaining) = nodes_left.checked_sub(1) else {
        return false;
    };
    *nodes_left = remaining;

    let printed = printed.trim();
    if printed.is_empty() {
        return false;
    }
    if !printed.starts_with('(') {
        return parse_numeral(printed).is_some()
            || (!printed_atom_starts_like_carcara_number(printed)
                && carcara_bare_linear_atom_is_supported(printed));
    }
    let Some(parts) = split_sexpr(printed) else {
        return false;
    };
    let Some((operator, operands)) = parts.split_first() else {
        return false;
    };
    let recurse = |operand: &str, nodes_left: &mut usize| {
        carcara_bridge_linear_term_supported(operand, depth + 1, nodes_left)
    };
    match operator.as_str() {
        "+" => operands.len() >= 2 && operands.iter().all(|operand| recurse(operand, nodes_left)),
        "-" => !operands.is_empty() && operands.iter().all(|operand| recurse(operand, nodes_left)),
        "*" => matches!(operands, [left, right]
            if (carcara_direct_fraction(left).is_some() && recurse(right, nodes_left))
                || (carcara_direct_fraction(right).is_some() && recurse(left, nodes_left))),
        "/" => carcara_direct_fraction(printed).is_some(),
        // Every other application is one opaque arithmetic atom in Carcara's
        // `LinearComb::from_term`; do not recurse into its arguments.
        _ => true,
    }
}

/// Parse exactly the direct numeric forms recognized by Carcara's
/// `Term::as_fraction`: a numeral, its unary negation, or `/` over two
/// signed numerals (optionally negated as a whole).
fn carcara_direct_fraction(printed: &str) -> Option<BigRational> {
    let printed = printed.trim();
    if let Some(value) = parse_numeral(printed) {
        return Some(value);
    }
    let parts = split_sexpr(printed)?;
    match parts.as_slice() {
        [minus, operand] if minus == "-" => {
            let inner = carcara_unsigned_fraction(operand)?;
            Some(-inner)
        }
        _ => carcara_unsigned_fraction(printed),
    }
}

fn carcara_unsigned_fraction(printed: &str) -> Option<BigRational> {
    if let Some(value) = parse_numeral(printed.trim()) {
        return Some(value);
    }
    let parts = split_sexpr(printed)?;
    let [operator, numerator, denominator] = parts.as_slice() else {
        return None;
    };
    if operator != "/" {
        return None;
    }
    let numerator = signed_numeral(numerator)?;
    let denominator = signed_numeral(denominator)?;
    (!denominator.is_zero()).then(|| numerator / denominator)
}

fn signed_numeral(printed: &str) -> Option<BigRational> {
    if let Some(value) = parse_numeral(printed.trim()) {
        return Some(value);
    }
    let parts = split_sexpr(printed)?;
    let [minus, operand] = parts.as_slice() else {
        return None;
    };
    (minus == "-")
        .then(|| parse_numeral(operand.trim()).map(std::ops::Neg::neg))
        .flatten()
}

fn carcara_bridge_comparison_supported(printed: &str) -> bool {
    if !surface_audit::printed_atom_is_bounded(printed) {
        return false;
    }
    let Some(parts) = split_sexpr(printed) else {
        return false;
    };
    let [operator, left, right] = parts.as_slice() else {
        return false;
    };
    if !matches!(operator.as_str(), "<" | "<=" | ">" | ">=") {
        return false;
    }
    let mut nodes_left = 100_000;
    carcara_bridge_linear_term_supported(left, 0, &mut nodes_left)
        && carcara_bridge_linear_term_supported(right, 0, &mut nodes_left)
}

/// Whether a complete printed clause literal has exactly the relation and
/// linear-term grammar consumed by pinned Carcara's `la_generic` rule.
///
/// This validates the full literal rather than an internally stripped atom:
/// a surface override may be keyed on the outer `not` node and therefore
/// replace both relation and polarity at once. Carcara accepts an unnegated
/// order comparison, or one `not` around an order comparison/equality. Its
/// linearizer recognizes only binary multiplication with a direct numeric
/// operand; computed coefficients and n-ary products remain opaque atoms.
pub(crate) fn carcara_printed_la_generic_literal_supported(printed: &str) -> bool {
    if !surface_audit::printed_atom_is_bounded(printed) {
        return false;
    }
    let Some(parts) = split_sexpr(printed) else {
        return false;
    };
    let (relation, negated) = match parts.as_slice() {
        [not, inner] if not == "not" => (inner.as_str(), true),
        _ => (printed.trim(), false),
    };
    let Some(parts) = split_sexpr(relation) else {
        return false;
    };
    let [operator, left, right] = parts.as_slice() else {
        return false;
    };
    if !(matches!(operator.as_str(), "<" | "<=" | ">" | ">=") || (negated && operator == "=")) {
        return false;
    }
    let mut nodes_left = 100_000;
    carcara_bridge_linear_term_supported(left, 0, &mut nodes_left)
        && carcara_bridge_linear_term_supported(right, 0, &mut nodes_left)
}

/// Whether Carcara can prove the exact implication `premise => conclusion`
/// with the checked two-row bridge
/// `(cl (not premise) conclusion) :rule la_generic :args (1 1)`.
///
/// This is intentionally narrower than general Farkas publication.  It is
/// used only to confine an exact authored arithmetic comparison to its own
/// `assume` before the rest of a proof returns to AY's canonical rendering.
#[must_use]
pub fn printed_la_generic_unit_implication_is_supported(premise: &str, conclusion: &str) -> bool {
    if !carcara_bridge_comparison_supported(premise)
        || !carcara_bridge_comparison_supported(conclusion)
    {
        return false;
    }
    let Some(premise_hypothesis) = hypothesis(premise, true) else {
        return false;
    };
    let Some(negated_conclusion_hypothesis) = hypothesis(conclusion, false) else {
        return false;
    };
    let coefficients = [Rational64::from_integer(1), Rational64::from_integer(1)];
    coeffs_valid(
        &[premise_hypothesis, negated_conclusion_hypothesis],
        &coefficients,
    )
}

/// Parse an exact printed arithmetic constant using the same linear grammar
/// used to validate emitted `la_generic` steps.
pub(crate) fn parse_numeric_constant(s: &str) -> Option<BigRational> {
    let parsed = parse_lin(s)?;
    parsed.is_constant().then_some(parsed.constant)
}

/// The normalized hypothesis for one conflict literal (`printed` atom asserted
/// with truth value `value`): `(e, strict, is_equality)` with the hypothesis
/// equivalent to `e >= 0` / `e > 0` / `e = 0`, `e` in `lhs - rhs` orientation.
/// `None` for a disequality or a non-arithmetic / unparseable atom.
fn hypothesis(printed: &str, value: bool) -> Option<(Lin, bool, bool)> {
    let mut s = printed.trim().to_string();
    let clause_has_outer_not = value;
    let mut value = value;
    let mut printed_nots = 0usize;
    // Strip leading `(not ...)`, flipping polarity.
    loop {
        let parts = split_sexpr(&s)?;
        if parts.len() == 2 && parts[0] == "not" {
            printed_nots += 1;
            if printed_nots + usize::from(clause_has_outer_not) > 1 {
                return None;
            }
            s = parts[1].clone();
            value = !value;
        } else {
            break;
        }
    }
    let parts = split_sexpr(&s)?;
    if parts.len() != 3 {
        return None;
    }
    let pred = parts[0].as_str();
    let lhs = parse_lin(&parts[1])?;
    let rhs = parse_lin(&parts[2])?;
    let l_minus_r = {
        let mut e = lhs.clone();
        e.add_scaled(&rhs, &BigRational::from(BigInt::from(-1)));
        e
    };
    let r_minus_l = {
        let mut e = rhs;
        e.add_scaled(&lhs, &BigRational::from(BigInt::from(-1)));
        e
    };
    match (pred, value) {
        ("=", true) => Some((l_minus_r, false, true)),
        ("<=", true) | (">", false) => Some((r_minus_l, false, false)),
        ("<", true) | (">=", false) => Some((r_minus_l, true, false)),
        (">=", true) | ("<", false) => Some((l_minus_r, false, false)),
        (">", true) | ("<=", false) => Some((l_minus_r, true, false)),
        _ => None,
    }
}

fn to_big(r: &Rational64) -> BigRational {
    BigRational::new(BigInt::from(*r.numer()), BigInt::from(*r.denom()))
}

/// SOUND reconstruction of Carcara's `la_generic` acceptance test over the
/// printed hypotheses for the given signed coefficient vector.
fn coeffs_valid(hyps: &[(Lin, bool, bool)], coeffs: &[Rational64]) -> bool {
    if hyps.len() != coeffs.len() {
        return false;
    }
    let mut sum = Lin::default();
    let mut has_strict = false;
    for ((expr, strict, is_eq), &c) in hyps.iter().zip(coeffs.iter()) {
        let scale = if *is_eq { c } else { c.abs() };
        if scale.is_zero() {
            continue;
        }
        has_strict |= *strict;
        sum.add_scaled(expr, &to_big(&scale));
    }
    sum.coeffs.is_empty()
        && (sum.constant < BigRational::zero() || (sum.constant.is_zero() && has_strict))
}

/// Return whether a printed literal has a directly checkable linear-arithmetic
/// surface shape for `la_generic`.
///
/// This applies the same parser used for final printed-certificate replay and
/// rejects nonlinear products, disequalities, and excess leading negations.
#[must_use]
pub fn printed_linear_arithmetic_literal_is_supported(printed: &str) -> bool {
    surface_audit::printed_atom_is_bounded(printed)
        && (hypothesis(printed, false).is_some() || hypothesis(printed, true).is_some())
}

/// Choose the coefficient vector to PRINT for an Alethe `la_generic` step whose
/// clause literals print as `printed_atoms` (`(printed_atom, truth_value)`,
/// matching how the printer reconstructs the conflict). `existing` is the
/// signs-from-internal-orientation candidate; it is kept byte-identical when an
/// external checker already accepts it. Otherwise the equality signs are
/// repaired (inequalities emitted in magnitude) so the checker accepts, using
/// `magnitudes` (the non-negative Farkas coefficients). Falls back to
/// `existing` when the atoms cannot be parsed, there are too many equalities to
/// enumerate, or no sign choice validates — so the result never regresses a
/// currently-valid certificate and never fabricates a "fixed" invalid one.
#[must_use]
pub(crate) fn resolve_printed_la_generic_coefficients(
    printed_atoms: &[(String, bool)],
    existing: &[Rational64],
    magnitudes: &[Rational64],
) -> Vec<Rational64> {
    let existing = existing.to_vec();
    if printed_atoms.len() != existing.len() || magnitudes.len() != existing.len() {
        return existing;
    }
    let mut hyps: Vec<(Lin, bool, bool)> = Vec::with_capacity(printed_atoms.len());
    for (atom, value) in printed_atoms {
        match hypothesis(atom, *value) {
            Some(h) => hyps.push(h),
            None => return existing, // unparseable / disequality: keep current behavior
        }
    }
    if coeffs_valid(&hyps, &existing) {
        return existing;
    }
    let eq_indices: Vec<usize> = hyps
        .iter()
        .enumerate()
        .filter_map(|(i, (_e, _s, is_eq))| if *is_eq { Some(i) } else { None })
        .collect();
    if eq_indices.len() > 16 {
        return existing;
    }
    let base: Vec<Rational64> = magnitudes.iter().map(|c| c.abs()).collect();
    for mask in 0u32..(1u32 << eq_indices.len()) {
        let mut candidate = base.clone();
        for (bit, &ei) in eq_indices.iter().enumerate() {
            if mask & (1u32 << bit) != 0 {
                candidate[ei] = -candidate[ei];
            }
        }
        if coeffs_valid(&hyps, &candidate) {
            return candidate;
        }
    }
    existing
}

#[cfg(test)]
#[path = "la_generic_signs_tests.rs"]
mod la_generic_signs_tests;

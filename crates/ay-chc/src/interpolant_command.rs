// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `(get-interpolant A B)` / `(compute-interpolant A B)` command support.
//!
//! Computes a Craig interpolant for a pair of formulas `(A, B)` whose
//! conjunction is unsatisfiable, using the LIA/LRA Farkas machinery in
//! [`crate::farkas`]. The result `I` satisfies:
//!
//! - `A => I`            (validated by SMT: `UNSAT(A /\ !I)`)
//! - `I /\ B` is UNSAT   (validated by SMT)
//! - `vars(I)` are shared between `A` and `B`
//!
//! Soundness comes first: the underlying [`crate::farkas::compute_interpolant`]
//! only returns a candidate after discharging both Craig obligations through a
//! real SMT check, and this module re-validates the candidate independently
//! before returning it. Any formula outside the supported fragment, or any case
//! where no validated interpolant can be produced, yields
//! [`InterpolantError::Unsupported`] — never a wrong interpolant.

use ay_frontend::{Constant, Term};

use crate::farkas::compute_interpolant;
use crate::interpolant_validation::{
    collect_conjuncts_for_interpolation, is_valid_interpolant_with_check_sat,
};
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar};
use ay_core::kani_compat::DetHashSet as FxHashSet;

/// Outcome of an interpolation request.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InterpolantError {
    /// The requested interpolation is outside the supported fragment, or no
    /// sound interpolant could be produced (e.g. `A /\ B` is satisfiable, the
    /// formulas contain non-linear / non-arithmetic constructs we do not yet
    /// interpolate, or validation failed). The CLI surfaces this as
    /// `unsupported` rather than guessing an answer.
    Unsupported(String),
}

impl std::fmt::Display for InterpolantError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Unsupported(msg) => write!(f, "{msg}"),
        }
    }
}

/// Sort resolver for free symbols appearing in the interpolation formulas.
///
/// Callers (the CLI) supply declared sorts from the elaboration context so the
/// SMT validation of the candidate interpolant uses the correct theory (Int vs
/// Real). Symbols without a declared sort fall back to `Int`, the default
/// numeric sort for the LIA interpolation fragment.
pub trait SortResolver {
    /// Return the declared [`ChcSort`] of `name`, if known.
    fn sort_of(&self, name: &str) -> Option<ChcSort>;
}

impl<F> SortResolver for F
where
    F: Fn(&str) -> Option<ChcSort>,
{
    fn sort_of(&self, name: &str) -> Option<ChcSort> {
        self(name)
    }
}

/// Compute a validated Craig interpolant for the formula pair `(a, b)`.
///
/// `a` and `b` are the parsed SMT-LIB formula terms from
/// `(get-interpolant A B)`. `sorts` resolves the declared sort of each free
/// symbol so the candidate interpolant is validated in the right arithmetic
/// theory.
///
/// On success the returned [`ChcExpr`] renders to SMT-LIB via its `Display`
/// impl. On failure the caller should emit `unsupported`.
///
/// # Soundness
///
/// The returned interpolant has been validated by SMT for both Craig
/// obligations (`A => I` and `UNSAT(I /\ B)`) and uses only shared variables.
/// Returning [`InterpolantError::Unsupported`] is always sound: it makes no
/// claim about `(A, B)`.
pub fn compute_smt_interpolant<R: SortResolver>(
    a: &Term,
    b: &Term,
    sorts: &R,
) -> Result<ChcExpr, InterpolantError> {
    let a_expr = term_to_chc(a, sorts).ok_or_else(|| {
        InterpolantError::Unsupported(
            "interpolant: formula A is outside the supported LIA/LRA fragment".to_string(),
        )
    })?;
    let b_expr = term_to_chc(b, sorts).ok_or_else(|| {
        InterpolantError::Unsupported(
            "interpolant: formula B is outside the supported LIA/LRA fragment".to_string(),
        )
    })?;

    // Split each formula into a conjunction of atoms. Numeric equalities are
    // expanded into a pair of inequalities so the Farkas generator can
    // eliminate variables (handled by collect_conjuncts_for_interpolation).
    let mut a_constraints: Vec<ChcExpr> = Vec::new();
    collect_conjuncts_for_interpolation(&a_expr, &mut a_constraints);
    let mut b_constraints: Vec<ChcExpr> = Vec::new();
    collect_conjuncts_for_interpolation(&b_expr, &mut b_constraints);

    // Shared variables: those occurring in both A and B. The interpolant must
    // range only over these.
    let a_vars: FxHashSet<String> = a_expr.vars().into_iter().map(|v| v.name).collect();
    let b_vars: FxHashSet<String> = b_expr.vars().into_iter().map(|v| v.name).collect();
    let shared_vars: FxHashSet<String> = a_vars.intersection(&b_vars).cloned().collect();

    // The Farkas machinery REQUIRES A /\ B to be UNSAT. Verify this up front so
    // a satisfiable pair is reported as unsupported instead of silently
    // returning a vacuous/garbage candidate.
    if !pair_is_unsat(&a_expr, &b_expr) {
        return Err(InterpolantError::Unsupported(
            "interpolant: A /\\ B is not unsatisfiable (or could not be decided); \
             no Craig interpolant exists"
                .to_string(),
        ));
    }

    let candidate =
        compute_interpolant(&a_constraints, &b_constraints, &shared_vars).ok_or_else(|| {
            InterpolantError::Unsupported(
                "interpolant: no validated Craig interpolant found for this pair \
                 (unsupported fragment or generator could not derive one)"
                    .to_string(),
            )
        })?;

    // Independent re-validation of both Craig obligations before returning.
    // compute_interpolant already validates internally; this is a defensive
    // second check so a returned interpolant is never unsound.
    if !revalidate(&a_expr, &b_expr, &candidate, &shared_vars) {
        return Err(InterpolantError::Unsupported(
            "interpolant: candidate failed Craig re-validation".to_string(),
        ));
    }

    Ok(candidate)
}

/// Verify `A /\ B` is unsatisfiable, conservatively: only `true` on a definite
/// UNSAT verdict from the SMT context. `Sat`/`Unknown` both return `false`.
fn pair_is_unsat(a: &ChcExpr, b: &ChcExpr) -> bool {
    let timeout = std::time::Duration::from_secs(5);
    let query = ChcExpr::and(a.clone(), b.clone());
    crate::interpolant_validation::is_unsat_result(&crate::engine_utils::check_sat_with_timeout(
        &query, timeout,
    ))
}

fn revalidate(
    a: &ChcExpr,
    b: &ChcExpr,
    interpolant: &ChcExpr,
    shared_vars: &FxHashSet<String>,
) -> bool {
    let timeout = std::time::Duration::from_secs(5);
    is_valid_interpolant_with_check_sat(a, b, interpolant, shared_vars, |query| {
        crate::engine_utils::check_sat_with_timeout(query, timeout)
    })
}

/// Convert a parsed SMT-LIB [`Term`] into a [`ChcExpr`] over the supported
/// interpolation fragment (Bool / LIA / LRA atoms).
///
/// Returns `None` for any construct outside that fragment (quantifiers, let,
/// arrays, bitvectors, datatypes, strings, lambdas, etc.), so the caller can
/// soundly report the request as unsupported.
fn term_to_chc<R: SortResolver>(term: &Term, sorts: &R) -> Option<ChcExpr> {
    match term {
        Term::Const(c) => const_to_chc(c),
        Term::Symbol(name) => match name.as_str() {
            "true" => Some(ChcExpr::Bool(true)),
            "false" => Some(ChcExpr::Bool(false)),
            _ => {
                let sort = sorts.sort_of(name).unwrap_or(ChcSort::Int);
                Some(ChcExpr::var(ChcVar::new(name.clone(), sort)))
            }
        },
        Term::App(name, args) => app_to_chc(name, args, sorts),
        // Annotated terms `(! t :named n)` are transparent for our purposes.
        Term::Annotated(inner, _) => term_to_chc(inner, sorts),
        // Everything else (let, quantifiers, lambdas, indexed/qualified apps) is
        // outside the supported interpolation fragment.
        _ => None,
    }
}

fn const_to_chc(c: &Constant) -> Option<ChcExpr> {
    match c {
        Constant::True => Some(ChcExpr::Bool(true)),
        Constant::False => Some(ChcExpr::Bool(false)),
        Constant::Numeral(n) => n.parse::<i128>().ok().map(ChcExpr::Int),
        Constant::Decimal(d) => decimal_to_real(d),
        // Hexadecimal/Binary (bitvectors) and Strings are not in the LIA/LRA
        // interpolation fragment.
        _ => None,
    }
}

/// Parse an SMT-LIB decimal literal (e.g. `3.5`) into a reduced rational `Real`.
///
/// The numerator/denominator are reduced by their GCD so downstream linear
/// parsing (which expects normalized rationals) recognizes the literal — e.g.
/// `1.0` becomes `Real(1, 1)` rather than `Real(10, 10)`.
fn decimal_to_real(d: &str) -> Option<ChcExpr> {
    let (int_part, frac_part) = match d.split_once('.') {
        Some((i, f)) => (i, f),
        None => (d, ""),
    };
    let combined = format!("{int_part}{frac_part}");
    let numer: i64 = combined.parse().ok()?;
    let scale = frac_part.len() as u32;
    let denom: i64 = 10i64.checked_pow(scale)?;
    let g = gcd_i64(numer.unsigned_abs(), denom.unsigned_abs()).max(1) as i64;
    Some(ChcExpr::Real(numer / g, denom / g))
}

fn gcd_i64(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

fn app_to_chc<R: SortResolver>(name: &str, args: &[Term], sorts: &R) -> Option<ChcExpr> {
    // Convert all arguments first; bail if any argument is unsupported.
    let conv = |a: &Term| term_to_chc(a, sorts);

    // n-ary boolean connectives.
    match name {
        "and" => return all(args, conv).map(ChcExpr::and_vec),
        "or" => return all(args, conv).map(ChcExpr::or_vec),
        "not" if args.len() == 1 => return conv(&args[0]).map(ChcExpr::not),
        "=>" | "implies" => {
            let parts = all(args, conv)?;
            return fold_right(parts, ChcExpr::implies);
        }
        _ => {}
    }

    // Binary / chainable comparison and arithmetic operators.
    if let Some(op) = binary_op(name) {
        let parts = all(args, conv)?;
        return build_op_chain(op, parts);
    }

    // Unary negation `(- x)`.
    if name == "-" && args.len() == 1 {
        return conv(&args[0]).map(ChcExpr::neg);
    }

    // `ite` over the arithmetic/boolean fragment.
    if name == "ite" && args.len() == 3 {
        let c = conv(&args[0])?;
        let t = conv(&args[1])?;
        let e = conv(&args[2])?;
        return Some(ChcExpr::ite(c, t, e));
    }

    None
}

/// Map a comparison / arithmetic operator name to its [`ChcOp`].
fn binary_op(name: &str) -> Option<ChcOp> {
    Some(match name {
        "=" => ChcOp::Eq,
        "distinct" => ChcOp::Ne,
        "<" => ChcOp::Lt,
        "<=" => ChcOp::Le,
        ">" => ChcOp::Gt,
        ">=" => ChcOp::Ge,
        "+" => ChcOp::Add,
        "-" => ChcOp::Sub,
        "*" => ChcOp::Mul,
        "div" => ChcOp::Div,
        "mod" => ChcOp::Mod,
        _ => return None,
    })
}

/// Build a chained operator application.
///
/// - Comparisons (`<`, `<=`, `=`, ...) over `n` args are the conjunction of the
///   pairwise relations: `(< a b c)` ⇒ `(and (< a b) (< b c))`.
/// - Arithmetic (`+`, `-`, `*`) over `n` args is the left-associated fold.
fn build_op_chain(op: ChcOp, parts: Vec<ChcExpr>) -> Option<ChcExpr> {
    if parts.len() < 2 {
        return None;
    }
    match op {
        ChcOp::Eq | ChcOp::Ne | ChcOp::Lt | ChcOp::Le | ChcOp::Gt | ChcOp::Ge => {
            let mut conj: Vec<ChcExpr> = Vec::with_capacity(parts.len() - 1);
            for w in parts.windows(2) {
                conj.push(ChcExpr::Op(
                    op,
                    vec![
                        std::sync::Arc::new(w[0].clone()),
                        std::sync::Arc::new(w[1].clone()),
                    ],
                ));
            }
            Some(ChcExpr::and_vec(conj))
        }
        ChcOp::Add | ChcOp::Sub | ChcOp::Mul | ChcOp::Div | ChcOp::Mod => {
            let mut iter = parts.into_iter();
            let mut acc = iter.next()?;
            for next in iter {
                acc = ChcExpr::Op(
                    op,
                    vec![std::sync::Arc::new(acc), std::sync::Arc::new(next)],
                );
            }
            Some(acc)
        }
        _ => None,
    }
}

/// Right-fold a non-empty list with a binary combiner (used for `=>`).
fn fold_right(parts: Vec<ChcExpr>, f: impl Fn(ChcExpr, ChcExpr) -> ChcExpr) -> Option<ChcExpr> {
    let mut iter = parts.into_iter().rev();
    let mut acc = iter.next()?;
    for prev in iter {
        acc = f(prev, acc);
    }
    Some(acc)
}

/// Convert every term in `args`, returning `None` if any conversion fails.
fn all(args: &[Term], conv: impl Fn(&Term) -> Option<ChcExpr>) -> Option<Vec<ChcExpr>> {
    args.iter().map(conv).collect()
}

#[cfg(test)]
#[path = "interpolant_command_tests.rs"]
mod tests;

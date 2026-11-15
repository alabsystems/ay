// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! FP support classification and assertion partitioning.

// #8529: Use deterministic hash sets in all builds.
use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::{Constant, TermData};
use ay_core::{Sort, TermId, TermStore};

/// Result of checking for unsupported FP operations.
pub(super) enum FpSupportStatus {
    /// All operations are fully supported by bit-blasting.
    FullySupported,
    /// Only fp.to_real is unsupported — can use the two-phase solve path.
    OnlyToReal,
    /// Other unsupported operations exist — must return Unknown.
    Unsupported,
}

/// Result of attempting to bitblast a Tseitin-mapped term as an FP predicate.
pub(super) enum FpPredicateResult {
    /// Successfully bitblasted — returns the CNF literal linking to the result.
    Bitblasted(i32),
    /// Not an FP predicate (boolean connective, non-FP equality, etc.) — skip.
    NotFpPredicate,
    /// Unrecognized FP predicate — formula must return Unknown to prevent free
    /// SAT variables causing false-SAT (#6189).
    Unsupported,
}

/// Check if a term is a BV constant.
pub(super) fn is_bv_const(terms: &TermStore, term: TermId) -> bool {
    matches!(terms.get(term), TermData::Const(Constant::BitVec { .. }))
}

/// Check if a term is a *ground* Real/Int value: a numeric literal, or such
/// literals combined with `+ - * /`. This mirrors the FP solver's
/// `eval_ground_rational` so that `(_ to_fp eb sb) rm <real>` is only marked
/// supported when the decompose path can actually pin the constant value
/// (otherwise the FP solver would fail closed to Unknown anyway).
pub(super) fn is_ground_rational(terms: &TermStore, term: TermId) -> bool {
    match terms.get(term) {
        TermData::Const(Constant::Rational(_)) | TermData::Const(Constant::Int(_)) => true,
        TermData::App(sym, args) => {
            matches!(sym.name(), "+" | "-" | "*" | "/")
                && !args.is_empty()
                && args.iter().all(|&a| is_ground_rational(terms, a))
        }
        _ => false,
    }
}

/// Check if a `to_fp` application is supported.
///
/// Supported variants:
/// - 1 arg (BV reinterpretation): BV arg, constant or variable
/// - 2 args (rm, FP): always supported (FP-to-FP precision conversion)
/// - 2 args (rm, BV): BV arg, constant or variable (signed BV-to-FP)
/// - 3 args (BV, BV, BV): all must be constants (same as fp constructor)
pub(super) fn is_to_fp_supported(terms: &TermStore, args: &[TermId]) -> bool {
    match args.len() {
        1 => matches!(terms.sort(args[0]), Sort::BitVec(_)),
        2 => {
            let arg_sort = terms.sort(args[1]);
            match arg_sort {
                Sort::FloatingPoint(..) | Sort::BitVec(_) => true,
                // Real/Int literal-to-FP rounding: only ground rational
                // expressions are supported (the decompose path rounds the exact
                // constant value into the target format).
                Sort::Real | Sort::Int => is_ground_rational(terms, args[1]),
                _ => false,
            }
        }
        3 => args.iter().all(|&a| is_bv_const(terms, a)),
        _ => false,
    }
}

/// Check if a `to_fp_unsigned` application is supported.
///
/// Supported: 2 args (rm, BV), constant or variable.
pub(super) fn is_to_fp_unsigned_supported(terms: &TermStore, args: &[TermId]) -> bool {
    args.len() == 2 && matches!(terms.sort(args[1]), Sort::BitVec(_))
}

/// Whether the bit-blaster encodes the rounding-mode term `term`: a literal
/// mode, a declared constant (three bits of its own), or an `ite` over such
/// terms (see `ay-theories/fp/src/rm.rs`). A rounding mode computed by a user
/// function has no encoding.
fn is_encoded_rounding_mode(terms: &TermStore, term: TermId) -> bool {
    if !crate::executor::rm_domain::is_rm_sort(terms.sort(term)) {
        return false;
    }
    if ay_fp::rewriter::rounding_mode_literal(terms, term).is_some() {
        return true;
    }
    match terms.get(term) {
        TermData::Var(..) => true,
        TermData::Ite(_, t, e) => {
            is_encoded_rounding_mode(terms, *t) && is_encoded_rounding_mode(terms, *e)
        }
        TermData::App(sym, args) if args.is_empty() && terms.is_declared_function(sym.name()) => {
            true
        }
        TermData::App(ay_core::Symbol::Named(name), args)
            if name == "ite" && args.len() == 3 && !terms.is_declared_function(name) =>
        {
            is_encoded_rounding_mode(terms, args[1]) && is_encoded_rounding_mode(terms, args[2])
        }
        _ => false,
    }
}

/// Check a single FP application for support status.
///
/// Returns `Some(Unsupported)` for unsupported operations, `None` to continue.
/// Sets `has_to_real` when fp.to_real is encountered.
fn check_fp_app_support(
    terms: &TermStore,
    name: &str,
    args: &[TermId],
    has_to_real: &mut bool,
) -> Option<FpSupportStatus> {
    match name {
        "to_fp" if !is_to_fp_supported(terms, args) => Some(FpSupportStatus::Unsupported),
        "to_fp_unsigned" if !is_to_fp_unsigned_supported(terms, args) => {
            Some(FpSupportStatus::Unsupported)
        }
        "fp.to_real" => {
            *has_to_real = true;
            None
        }
        // fp.rem is fully bit-blasted at every precision via bounded modular
        // reduction (ay-theories/fp `rem_modular_reduce`), so no size guard.
        "fp.rem" => None,
        _ => None,
    }
}

/// Check the assertion terms for unsupported FP arithmetic operations.
///
/// Walks the term DAG from the given roots. Operations with complete
/// bit-blasting are allowed through (#3586):
///   fp.add, fp.sub, fp.mul, fp.div, fp.sqrt, fp.fma, fp.roundToIntegral,
///   fp.rem, to_fp (constant or variable BV), to_fp_unsigned (constant or variable BV),
///   fp.to_ubv, fp.to_sbv, fp.to_ieee_bv
/// Operations still incomplete:
///   fp.to_real (crosses FP/Real theory boundary) → OnlyToReal
///   fp.rem on Float64+ (barrel-shifter overflow) → Unsupported
pub(super) fn check_fp_support(terms: &TermStore, roots: &[TermId]) -> FpSupportStatus {
    let mut visited = HashSet::default();
    let mut stack: Vec<TermId> = roots.to_vec();
    let mut has_to_real = false;

    while let Some(term) = stack.pop() {
        if !visited.insert(term) {
            continue;
        }
        // Symbolic rounding modes are encoded as three bits (declared
        // constants and `ite`s over modes); their equalities are bit-blasted
        // predicates, never free Tseitin atoms (false-SAT #6189). A mode the
        // bit-blaster cannot encode fails the solve closed: `unknown`, never
        // a guess.
        if ay_fp::rewriter::is_rounding_mode_sort(terms.sort(term))
            && !is_encoded_rounding_mode(terms, term)
        {
            return FpSupportStatus::Unsupported;
        }
        match terms.get(term) {
            TermData::App(sym, args) => {
                if let Some(status) =
                    check_fp_app_support(terms, sym.name(), args, &mut has_to_real)
                {
                    return status;
                }
                stack.extend_from_slice(args);
            }
            TermData::Not(inner) => {
                stack.push(*inner);
            }
            TermData::Ite(c, t, e) => {
                stack.push(*c);
                stack.push(*t);
                stack.push(*e);
            }
            TermData::Let(bindings, body) => {
                for (_, val) in bindings {
                    stack.push(*val);
                }
                stack.push(*body);
            }
            TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
                stack.push(*body);
            }
            _ => {}
        }
    }
    if has_to_real {
        FpSupportStatus::OnlyToReal
    } else {
        FpSupportStatus::FullySupported
    }
}

/// Check if a single term (transitively) contains fp.to_real.
pub(super) fn term_contains_fp_to_real(terms: &TermStore, root: TermId) -> bool {
    let mut visited = HashSet::default();
    let mut stack = vec![root];
    while let Some(term) = stack.pop() {
        if !visited.insert(term) {
            continue;
        }
        match terms.get(term) {
            TermData::App(sym, args) => {
                if sym.name() == "fp.to_real" {
                    return true;
                }
                stack.extend_from_slice(args);
            }
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, t, e) => {
                stack.push(*c);
                stack.push(*t);
                stack.push(*e);
            }
            TermData::Let(bindings, body) => {
                for (_, val) in bindings {
                    stack.push(*val);
                }
                stack.push(*body);
            }
            TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
                stack.push(*body);
            }
            _ => {}
        }
    }
    false
}

/// Check if an assertion is a pure FP assertion (no fp.to_real, no Real variables).
///
/// Pure FP assertions (containing fp.eq, fp.isNaN, etc.) are handled entirely
/// by the FP SAT solver and should NOT be included in the mixed subproblem.
pub(super) fn is_pure_fp_assertion(terms: &TermStore, root: TermId) -> bool {
    let mut visited = HashSet::default();
    let mut stack = vec![root];
    let mut has_fp = false;
    let mut has_real_or_to_real = false;

    while let Some(term) = stack.pop() {
        if !visited.insert(term) {
            continue;
        }
        let sort = terms.sort(term);
        if matches!(sort, Sort::Real) && !matches!(terms.get(term), TermData::Const(_)) {
            has_real_or_to_real = true;
        }
        match terms.get(term) {
            TermData::App(sym, args) => {
                let name = sym.name();
                if name == "fp.to_real" {
                    has_real_or_to_real = true;
                }
                if name.starts_with("fp.") || name == "to_fp" || name == "to_fp_unsigned" {
                    has_fp = true;
                }
                stack.extend_from_slice(args);
            }
            TermData::Var(_, _) => {
                if matches!(sort, Sort::FloatingPoint(..)) {
                    has_fp = true;
                }
            }
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, t, e) => {
                stack.push(*c);
                stack.push(*t);
                stack.push(*e);
            }
            TermData::Let(bindings, body) => {
                for (_, val) in bindings {
                    stack.push(*val);
                }
                stack.push(*body);
            }
            TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
                stack.push(*body);
            }
            _ => {}
        }
    }
    has_fp && !has_real_or_to_real
}

/// Partition assertions into FP-only and mixed (containing fp.to_real).
pub(super) fn partition_fp_assertions(
    terms: &TermStore,
    assertions: &[TermId],
) -> (Vec<TermId>, Vec<TermId>) {
    let mut fp_only = Vec::new();
    let mut mixed = Vec::new();
    for &a in assertions {
        if term_contains_fp_to_real(terms, a) {
            mixed.push(a);
        } else {
            fp_only.push(a);
        }
    }
    (fp_only, mixed)
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! FP-to-Real model extraction, site collection, and blocking-clause helpers.
//!
//! Term rewriting functions (variable substitution and model-value substitution)
//! live in sibling `to_real_rewrite.rs`.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermData;
use ay_core::{CnfClause, Sort, TermId, TermStore};
use ay_euf::EufModel;
use ay_fp::FpModel;
use ay_lra::LraModel;

use crate::executor_types::SolveResult;

pub(super) use super::to_real_rewrite::{
    rewrite_fp_to_real_for_model, rewrite_fp_to_real_with_vars,
};

/// A site where `fp.to_real` is applied to an FP term in the mixed assertions.
pub(super) struct FpToRealSite {
    /// The FP argument term inside `fp.to_real`.
    pub(super) arg: TermId,
}

/// Cached FP encoding: base CNF clauses and metadata for refinement loop.
pub(super) struct FpEncoding {
    /// Base CNF clauses (Tseitin + FP bit-blast + linking).
    pub(super) base_clauses: Vec<CnfClause>,
    /// Tseitin mapping for model extraction.
    pub(super) tseitin_result: ay_core::TseitinResult,
    /// Term-to-FP decomposition for model extraction and blocking clauses.
    pub(super) term_to_fp: HashMap<TermId, ay_fp::FpDecomposed>,
    /// Variable offset between Tseitin and FP namespaces.
    pub(super) var_offset: i32,
    /// Total variable count (Tseitin + FP).
    pub(super) total_vars: usize,
    /// True when the encoder could not represent some uninterpreted structure
    /// (see the `congruence` module). The encoding is still a relaxation, so
    /// `unsat` transfers, but every `sat` must degrade to `unknown`.
    pub(super) congruence_incomplete: bool,
}

/// Result of solving a rewritten mixed subproblem.
///
/// Captures the solve result plus theory models from the mixed solve,
/// which are needed to populate the final merged model with Real and UF values.
pub(super) struct MixedSubproblemResult {
    pub(super) result: SolveResult,
    pub(super) lra_model: Option<LraModel>,
    pub(super) euf_model: Option<EufModel>,
}

/// Refinement loop step result: what to do after trying a mixed subproblem.
pub(super) enum FpRefinementStep {
    /// Mixed subproblem is SAT — final model has been built.
    Sat,
    /// Mixed subproblem is Unknown — give up.
    Unknown,
    /// Mixed subproblem is UNSAT — add blocking clause and retry.
    Block,
}

/// Build an LRA model by evaluating fp.to_real terms from the FP model.
///
/// Walks the mixed assertions looking for Real variables equated to fp.to_real
/// results, and also directly evaluates fp.to_real subterms to provide values
/// for the model evaluator. Returns an LRA model with Real variable assignments.
pub(super) fn build_lra_model_from_fp_to_real(
    terms: &TermStore,
    fp_model: &FpModel,
    mixed_assertions: &[TermId],
) -> LraModel {
    let mut values = HashMap::default();

    for &assertion in mixed_assertions {
        collect_fp_to_real_values(terms, fp_model, assertion, &mut values);
    }

    LraModel { values }
}

/// Recursively collect fp.to_real evaluations and Real variable assignments.
fn collect_fp_to_real_values(
    terms: &TermStore,
    fp_model: &FpModel,
    term: TermId,
    values: &mut HashMap<TermId, num_rational::BigRational>,
) {
    match terms.get(term) {
        TermData::App(sym, args) => {
            match sym.name() {
                // Pattern: (= var (fp.to_real x)) or (= (fp.to_real x) var)
                "=" if args.len() == 2 => {
                    let sort0 = terms.sort(args[0]);
                    let sort1 = terms.sort(args[1]);
                    if matches!(sort0, Sort::Real) || matches!(sort1, Sort::Real) {
                        if let Some(val) = try_eval_fp_to_real(terms, fp_model, args[0]) {
                            values.insert(args[0], val.clone());
                            if matches!(terms.get(args[1]), TermData::Var(..)) {
                                values.insert(args[1], val);
                            }
                        }
                        if let Some(val) = try_eval_fp_to_real(terms, fp_model, args[1]) {
                            values.insert(args[1], val.clone());
                            if matches!(terms.get(args[0]), TermData::Var(..)) {
                                values.insert(args[0], val);
                            }
                        }
                    }
                }
                // fp.to_real directly in comparison context: (> (fp.to_real x) 1.0)
                "fp.to_real" if args.len() == 1 => {
                    if let Some(val) = try_eval_fp_to_real(terms, fp_model, term) {
                        values.insert(term, val);
                    }
                }
                _ => {}
            }
            for &arg in args {
                collect_fp_to_real_values(terms, fp_model, arg, values);
            }
        }
        TermData::Not(inner) => {
            collect_fp_to_real_values(terms, fp_model, *inner, values);
        }
        TermData::Ite(c, t, e) => {
            collect_fp_to_real_values(terms, fp_model, *c, values);
            collect_fp_to_real_values(terms, fp_model, *t, values);
            collect_fp_to_real_values(terms, fp_model, *e, values);
        }
        TermData::Let(bindings, body) => {
            for (_, val) in bindings {
                collect_fp_to_real_values(terms, fp_model, *val, values);
            }
            collect_fp_to_real_values(terms, fp_model, *body, values);
        }
        _ => {}
    }
}

/// Try to evaluate a term as fp.to_real(arg) using the FP model.
fn try_eval_fp_to_real(
    terms: &TermStore,
    fp_model: &FpModel,
    term: TermId,
) -> Option<num_rational::BigRational> {
    if let TermData::App(sym, args) = terms.get(term) {
        if sym.name() == "fp.to_real" && args.len() == 1 {
            if let Some(fp_val) = fp_model.values.get(&args[0]) {
                return fp_val.to_rational();
            }
        }
    }
    None
}

/// Collect all distinct `fp.to_real` application sites from the given terms.
pub(super) fn collect_fp_to_real_sites(terms: &TermStore, roots: &[TermId]) -> Vec<FpToRealSite> {
    let mut visited = HashSet::default();
    let mut sites = Vec::new();
    let mut seen_apps = HashSet::default();
    let mut stack: Vec<TermId> = roots.to_vec();

    while let Some(term) = stack.pop() {
        if !visited.insert(term) {
            continue;
        }
        match terms.get(term) {
            TermData::App(sym, args) => {
                if sym.name() == "fp.to_real" && args.len() == 1 && seen_apps.insert(term) {
                    sites.push(FpToRealSite { arg: args[0] });
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
    sites
}

/// Extract target f64 values for fp.to_real sites by structural analysis.
///
/// Scans assertions for patterns like `(= (fp.to_real arg) constant)` where
/// the constant is a numeric literal (Int or Rational). Populates `targets`
/// with FP arg TermId → f64 target value. Also handles the transitive pattern
/// `(= r (fp.to_real arg))` + `(= r constant)` when `r` is used in both.
pub(super) fn extract_fp_to_real_targets(
    terms: &TermStore,
    assertion: TermId,
    targets: &mut HashMap<TermId, f64>,
) {
    match terms.get(assertion) {
        TermData::App(sym, args) if sym.name() == "=" && args.len() == 2 => {
            let lhs = args[0];
            let rhs = args[1];
            // Pattern: (= (fp.to_real arg) constant) or (= constant (fp.to_real arg))
            if let Some((fp_arg, val)) = match_fp_to_real_eq_const(terms, lhs, rhs) {
                targets.insert(fp_arg, val);
            } else if let Some((fp_arg, val)) = match_fp_to_real_eq_const(terms, rhs, lhs) {
                targets.insert(fp_arg, val);
            }
        }
        _ => {}
    }
}

/// Match `(fp.to_real arg)` on one side and a numeric constant on the other.
fn match_fp_to_real_eq_const(
    terms: &TermStore,
    maybe_fp_to_real: TermId,
    maybe_const: TermId,
) -> Option<(TermId, f64)> {
    // Check if left side is fp.to_real(arg)
    let fp_arg = match terms.get(maybe_fp_to_real) {
        TermData::App(sym, args) if sym.name() == "fp.to_real" && args.len() == 1 => args[0],
        _ => return None,
    };
    // Check if right side is a numeric constant
    let val = term_to_f64(terms, maybe_const)?;
    Some((fp_arg, val))
}

/// Try to convert a term to an f64 constant value.
pub(super) fn term_to_f64(terms: &TermStore, term: TermId) -> Option<f64> {
    use ay_core::term::Constant;
    use num_traits::ToPrimitive;
    match terms.get(term) {
        TermData::Const(Constant::Int(n)) => n.to_f64(),
        TermData::Const(Constant::Rational(r)) => {
            let numer = r.0.numer().to_f64()?;
            let denom = r.0.denom().to_f64()?;
            if denom == 0.0 {
                None
            } else {
                Some(numer / denom)
            }
        }
        // Handle (/ num denom) pattern
        TermData::App(sym, args) if sym.name() == "/" && args.len() == 2 => {
            let n = term_to_f64(terms, args[0])?;
            let d = term_to_f64(terms, args[1])?;
            if d == 0.0 {
                None
            } else {
                Some(n / d)
            }
        }
        // Handle (- x) negation
        TermData::App(sym, args) if sym.name() == "-" && args.len() == 1 => {
            let v = term_to_f64(terms, args[0])?;
            Some(-v)
        }
        _ => None,
    }
}

/// Convert a BigRational to f64 (lossy).
pub(super) fn rational_to_f64(r: &num_rational::BigRational) -> f64 {
    use num_traits::ToPrimitive;
    let numer = r.numer().to_f64().unwrap_or(0.0);
    let denom = r.denom().to_f64().unwrap_or(1.0);
    if denom == 0.0 {
        if numer > 0.0 {
            f64::INFINITY
        } else if numer < 0.0 {
            f64::NEG_INFINITY
        } else {
            0.0
        }
    } else {
        numer / denom
    }
}

// Re-exported here so existing `use to_real::{offset_cnf_lit, ...}` imports continue to work.
pub(super) use super::blocking::{
    build_fp_target_unit_clauses, choose_blocking_clause, offset_cnf_lit,
};

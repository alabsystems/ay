// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! AY Strings - String theory solver
//!
//! Implements word equations and regular expression constraints using the
//! normal form algorithm from Liang et al. (CAV 2014).
//!
//! Module decomposition follows CVC5's string solver architecture:
//! - `state`: Equivalence class tracking with union-find and trail-based backtracking.
//! - `normal_form`: Normal form data structure with dependency tracking.
//! - `base`: EQC initialization and constant conflict detection.
//! - `core`: Word equation solving via normal forms.
//! - `infer`: Inference collection and conversion to DPLL(T) results.

#![forbid(unsafe_code)]
#![warn(missing_docs)]
#![warn(clippy::all)]

mod arith_entail;
mod base;
mod core;
/// Shared SMT-LIB string operation evaluation (#5813).
///
/// Pure functions for `str.at`, `str.substr`, `str.replace`, `str.indexof`,
/// `str.to_int`, `str.from_int`. Used by both the theory solver and the
/// DPLL model evaluator.
pub mod eval;
mod infer;
mod normal_form;
mod regexp;
mod skolem;
mod solver_state;
mod state;
mod state_query;
pub mod term_regex;
mod theory_impl;
#[cfg(kani)]
mod verification;
/// Bounded Nielsen-transform word-equation solver (Track A3 M1).
///
/// A standalone decision procedure for conjunctions of word equations over
/// variables + literals, used by the DPLL executor as a validated pre-pass.
pub mod we_regex;
pub mod word_eq;

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::{TermId, TermStore};
use ay_core::{
    Sort, StringLemma, StringLemmaKind, TheoryLit, TheoryPropagation, TheoryResult, TheorySolver,
};

use base::BaseSolver;
use core::CoreSolver;
use infer::InferenceManager;
use regexp::{MatchResult, RegExpSolver, RegexWorkBudget};
use skolem::SkolemCache;
use state::SolverState;

// Test-only override so unit tests can exercise the NF-engine closures
// without mutating process-global environment state (the env reads below are
// cached in `OnceLock`s, so `set_var` in one test would leak into every other
// test in the same process).
#[cfg(test)]
thread_local! {
    pub(crate) static STR_NF_TEST_OVERRIDE: std::cell::Cell<bool> =
        const { std::cell::Cell::new(false) };
}

/// Strings NF-engine increment master switch (`--str-nf`, default OFF).
///
/// Gates the ranked NF-engine closures from
/// the development design notes:
///   1. deq-pass reduction awareness,
///   2. prefix/suffix component-transfer `N_UNIFY`,
///   3. de-serialized lemma emission,
///   4. eager len-fact registration for reduction skolems,
///   5. trusted post-string-lemma UNSAT acceptance — QUARANTINED, see
///      [`NF_CLOSURES_REQUIRING_EXPLICIT_OPT_IN`],
///   6. negated constant-needle `str.contains` as an exact complemented
///      `Σ* w Σ*` membership in the witness-construction lanes.
///
/// Default OFF keeps the solve pipeline byte-identical to pre-NF behavior.
pub fn str_nf_enabled() -> bool {
    #[cfg(test)]
    if STR_NF_TEST_OVERRIDE.with(|c| c.get()) {
        return true;
    }
    static V: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *V.get_or_init(|| ay_core::misc_cli_flags().str_nf)
}

/// Closures that `--str-nf` alone must NOT enable, because they are known
/// to be UNSOUND on the current tree. Reaching them requires naming them
/// EXPLICITLY in `--str-nf-closures` (for debugging / repair work only).
///
/// * **5** — "trusted post-string-lemma UNSAT acceptance". Measured
///   WRONG-UNSAT witness on current main:
///   `QF_SLIA/non-incremental__QF_SLIA__20180523-Reynolds__kaluza__sat__small__bettermatch1.readable.smt2`
///   (SMT-LIB `kaluza/sat/`; z3 4.16 answers `sat`) returns `unsat` under
///   `--str-nf --str-nf-closures 5`, and under closure 5 alone. Only ONE
///   string lemma is lowered on that file — a `LengthSplit`, which lowers to
///   the tautology `[eq, ¬eq]` and therefore cannot turn a satisfiable clause
///   set unsatisfiable. The propositional UNSAT must therefore rest on a
///   theory conflict clause that is NOT a consequence of the original formula,
///   i.e. closure 5's second premise ("no distrusted conflict was ever turned
///   into a clause") does not hold here: the blanket post-string-lemma
///   downgrade that closure 5 removes is load-bearing for soundness, not only
///   for completeness. Fail closed until the escaping conflict is identified.
const NF_CLOSURES_REQUIRING_EXPLICIT_OPT_IN: &[u8] = &[5];

/// Per-closure sub-flag for A/B attribution under the `--str-nf` master
/// switch. `--str-nf-closures 1,3` enables only closures 1 and 3; unset (or
/// unparsable) enables every closure EXCEPT those in
/// [`NF_CLOSURES_REQUIRING_EXPLICIT_OPT_IN`]. Always `false` when the master
/// switch is off.
pub fn str_nf_closure_enabled(n: u8) -> bool {
    if !str_nf_enabled() {
        return false;
    }
    static SET: std::sync::OnceLock<Option<Vec<u8>>> = std::sync::OnceLock::new();
    let set = SET.get_or_init(|| {
        let raw = ay_core::misc_cli_flags().str_nf_closures.as_deref()?;
        Some(
            raw.split(',')
                .filter_map(|s| s.trim().parse::<u8>().ok())
                .collect(),
        )
    });
    match set {
        Some(subset) => subset.contains(&n),
        None => !NF_CLOSURES_REQUIRING_EXPLICIT_OPT_IN.contains(&n),
    }
}

/// Whether a regex term is GROUND and built exclusively from constructs the
/// regex evaluator handles totally (extf wave 2). When this returns true,
/// `RegExpSolver::evaluate` never returns `None` on any input string, so
/// ground evaluation of `str.replace_re` / `str.replace_re_all` over this
/// regex always succeeds — the precondition for the partial regex-replace
/// reductions.
///
/// Conservative whitelist mirroring the evaluator's total arms; anything
/// else (re.comp, re.diff, re.loop, symbolic `str.to_re`, ...) keeps the
/// previous incomplete/Unknown behavior.
pub fn regex_ground_evaluable(terms: &TermStore, re_term: TermId) -> bool {
    use ay_core::term::{Constant, TermData};
    let TermData::App(sym, args) = terms.get(re_term) else {
        return false;
    };
    let is_const_str = |t: TermId| matches!(terms.get(t), TermData::Const(Constant::String(_)));
    match sym.name() {
        "re.none" | "re.all" | "re.allchar" => args.is_empty(),
        "re.range" => args.len() == 2 && args.iter().all(|&a| is_const_str(a)),
        "str.to_re" | "str.to.re" => args.len() == 1 && is_const_str(args[0]),
        "re.++" | "re.union" | "re.inter" => {
            !args.is_empty() && args.iter().all(|&a| regex_ground_evaluable(terms, a))
        }
        "re.*" | "re.+" | "re.opt" => args.len() == 1 && regex_ground_evaluable(terms, args[0]),
        _ => false,
    }
}

/// Ground evaluation of `str.replace_re(s, r, t)`.
///
/// Returns `Some(result)` when the regex `r` is structurally evaluable,
/// `None` if the regex contains unresolvable constructs.
///
/// Exposed for DPLL-level ground evaluation (#3890, #4025).
pub fn ground_eval_replace_re(terms: &TermStore, s: &str, r: TermId, t: &str) -> Option<String> {
    let mut budget = RegexWorkBudget::unlimited();
    ground_eval_replace_re_with_budget(terms, s, r, t, &mut budget).unwrap_or_default()
}

/// Ground evaluation of `str.replace_re` with a cooperative matcher-work cap.
///
/// `Ok(None)` means the regex is not ground-evaluable. `Err` means the cap was
/// exhausted; callers must treat that as a resource abort, not as a semantic
/// regex answer.
pub fn ground_eval_replace_re_with_work_limit(
    terms: &TermStore,
    s: &str,
    r: TermId,
    t: &str,
    work_limit: u64,
) -> Result<Option<String>, RegexWorkLimitExceeded> {
    let mut budget = RegexWorkBudget::limited(work_limit);
    ground_eval_replace_re_with_budget(terms, s, r, t, &mut budget)
}

fn ground_eval_replace_re_with_budget(
    terms: &TermStore,
    s: &str,
    r: TermId,
    t: &str,
    budget: &mut RegexWorkBudget,
) -> Result<Option<String>, RegexWorkLimitExceeded> {
    let result = match RegExpSolver::find_first_match_with_budget(terms, s, r, budget)? {
        MatchResult::Found(start, end) => {
            let mut result = s[..start].to_string();
            result.push_str(t);
            result.push_str(&s[end..]);
            Some(result)
        }
        MatchResult::NoMatch => Some(s.to_string()),
        MatchResult::Incomplete => None,
    };
    Ok(result)
}

/// Ground evaluation of `str.replace_re_all(s, r, t)`.
///
/// Returns `Some(result)` when the regex `r` is structurally evaluable,
/// `None` if the regex contains unresolvable constructs.
///
/// Exposed for DPLL-level ground evaluation (#3890, #4025).
pub fn ground_eval_replace_re_all(
    terms: &TermStore,
    s: &str,
    r: TermId,
    t: &str,
) -> Option<String> {
    let mut budget = RegexWorkBudget::unlimited();
    ground_eval_replace_re_all_with_budget(terms, s, r, t, &mut budget).unwrap_or_default()
}

/// Ground evaluation of `str.replace_re_all` with one matcher-work cap shared
/// by every candidate substring and every successive replacement.
///
/// `Ok(None)` means the regex is not ground-evaluable. `Err` means the cap was
/// exhausted and no partial replacement is returned.
pub fn ground_eval_replace_re_all_with_work_limit(
    terms: &TermStore,
    s: &str,
    r: TermId,
    t: &str,
    work_limit: u64,
) -> Result<Option<String>, RegexWorkLimitExceeded> {
    let mut budget = RegexWorkBudget::limited(work_limit);
    ground_eval_replace_re_all_with_budget(terms, s, r, t, &mut budget)
}

fn ground_eval_replace_re_all_with_budget(
    terms: &TermStore,
    s: &str,
    r: TermId,
    t: &str,
    budget: &mut RegexWorkBudget,
) -> Result<Option<String>, RegexWorkLimitExceeded> {
    let mut result = String::new();
    let mut remaining = s;

    loop {
        if remaining.is_empty() {
            // SMT-LIB 2.6: the empty string admits no decomposition with a
            // non-empty middle, so it is its own replacement. There is nothing
            // left to copy, so just stop. (An older version pushed `t` when ""
            // matched `r`, spuriously inserting the replacement and producing a
            // false-UNSAT — #strings-replace_re_all. That must stay fixed.)
            break;
        }

        // SMT-LIB 2.6 Unicode Strings, `str.replace_re_all`: the decomposition
        // `s = x ++ w ++ z` requires `w != ""`, so the matcher must look for the
        // leftmost, then shortest, NON-EMPTY match. Asking for a possibly-empty
        // match instead makes every nullable regex (`re.all`, `re.*`, `re.opt`,
        // ...) match empty at position 0, after which no replacement can ever
        // fire and the operator degenerates to the identity — a wrong-verdict
        // defect in both directions (#strings-replace_re_all-nullable).
        match RegExpSolver::find_first_nonempty_match_with_budget(terms, remaining, r, budget)? {
            MatchResult::Found(start, end) => {
                debug_assert!(end > start, "non-empty matcher returned an empty match");
                result.push_str(&remaining[..start]);
                result.push_str(t);
                // `end > start` guarantees progress, so the loop terminates.
                remaining = &remaining[end..];
            }
            MatchResult::NoMatch => {
                result.push_str(remaining);
                break;
            }
            MatchResult::Incomplete => return Ok(None),
        }
    }

    Ok(Some(result))
}

/// Error returned when a bounded ground regex operation spends its matcher
/// work allowance before producing a complete result.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RegexWorkLimitExceeded;

impl std::fmt::Display for RegexWorkLimitExceeded {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("regex evaluation work limit exceeded")
    }
}

impl std::error::Error for RegexWorkLimitExceeded {}

/// This thread's monotone regex-membership work counter. Memoised fallback
/// consultations cost one unit; exact translation and derivative evaluation
/// charge their deterministic structural work.
///
/// A budgeting caller (the W4 witness search) adds this to the term
/// evaluator's own node-visit clock so ONE number bounds both shapes of
/// evaluation cost — a deep `str.substr`/`str.to_int` nest (many cheap node
/// visits) and a single `str.in_re` atom over an industrial regex (one node
/// visit, substantial translation, derivative, or fallback work).
#[must_use]
pub fn regex_eval_work() -> u64 {
    regexp::eval_work()
}

/// Ground evaluation of `str.in_re(s, r)`.
///
/// Returns `Some(true/false)` when the regex `r` is structurally evaluable
/// against the concrete string `s`, `None` if the regex contains
/// unresolvable constructs (e.g., non-ground sub-terms).
///
/// Exposed for DPLL-level ground evaluation (#5995, #6006).
pub fn ground_eval_in_re(terms: &TermStore, s: &str, r: TermId) -> Option<bool> {
    RegExpSolver::evaluate(terms, s, r)
}

/// Ground evaluation of `str.in_re` with a cooperative matcher-work cap.
///
/// `Ok(None)` means the regex is not ground-evaluable. `Err` means the cap was
/// exhausted before a complete membership answer was produced.
pub fn ground_eval_in_re_with_work_limit(
    terms: &TermStore,
    s: &str,
    r: TermId,
    work_limit: u64,
) -> Result<Option<bool>, RegexWorkLimitExceeded> {
    RegExpSolver::evaluate_with_work_limit(terms, s, r, work_limit)
}

/// Result of draining and merging internal equalities.
///
/// When an internal equality has an empty explanation (no proof-forest reason),
/// silently dropping it causes the fix-point loop to converge prematurely (#4025).
/// Instead, the equality is converted to a SAT-level `EqualitySplit` lemma so
/// the DPLL solver decides the equality with a proper reason chain.
struct MergeResult {
    /// Whether any equalities were successfully merged into the EQC state.
    merged_any: bool,
    /// Equalities that could not be merged (empty explanation) converted to
    /// split lemmas. The `check()` loop emits these as `NeedStringLemma`.
    deferred_splits: Vec<StringLemma>,
}

/// String theory solver.
///
/// Orchestrates sub-solvers (base, core, regexp) through the inference manager.
/// The check pipeline runs: base → core → regexp → internal equality fixpoint.
pub struct StringSolver<'a> {
    /// Reference to the shared term store for inspecting term structure.
    terms: &'a TermStore,
    /// Shared solver state: EQCs, assertions, disequalities.
    state: SolverState,
    /// Base solver: EQC init and constant conflict detection.
    base: BaseSolver,
    /// Core solver: word equation reasoning via normal forms.
    core: CoreSolver,
    /// Regex solver: ground membership evaluation.
    regexp: RegExpSolver,
    /// Inference manager: collects conflicts/propagations.
    infer: InferenceManager,
    /// Skolem variable cache for split lemmas with push/pop support.
    skolems: SkolemCache,
    /// Pre-registered empty string TermId, preserved across reset().
    /// Without this, cycle detection and endpoint-empty inferences fail
    /// when the formula has no explicit `""` literal.
    pre_registered_empty: Option<TermId>,
    /// Whether cycle detection (I_CYCLE) fired in the current `check()` call.
    /// Conflicts after cycle-derived equalities are trustworthy (#3875).
    /// Reset at the start of each `check()`, set by `InferenceManager`.
    cycle_conflict_trustworthy: bool,
    // Per-theory runtime statistics (#4706)
    check_count: u64,
    conflict_count: u64,
    propagation_count: u64,
}

/// Model extracted from the string solver.
#[derive(Debug, Clone, Default)]
pub struct StringModel {
    /// Concrete assignments for string variables that are in EQCs with constants.
    pub values: HashMap<TermId, String>,
}

/// Warm state extracted from a `StringSolver` for cross-iteration preservation.
///
/// When the CEGAR loop needs to drop the theory solver (to release the term
/// store borrow for creating new skolem/split terms), this struct captures
/// statistics and reduced-term markers that should survive across iterations.
/// Without this, every CEGAR iteration restarts statistics from zero and must
/// re-apply reduced-term markers externally.
///
/// Part of #3762: preserve solver state across CEGAR iterations.
#[derive(Debug, Clone, Default)]
pub struct StringSolverWarmState {
    /// Cumulative theory check count across CEGAR iterations.
    pub check_count: u64,
    /// Cumulative theory conflict count across CEGAR iterations.
    pub conflict_count: u64,
    /// Cumulative theory propagation count across CEGAR iterations.
    pub propagation_count: u64,
    /// Reduced term IDs that should persist across iterations.
    /// These represent structural decisions about term handling that
    /// remain valid regardless of the current SAT model.
    reduced_terms: Vec<TermId>,
}

#[cfg(test)]
#[path = "lib_tests.rs"]
mod tests;

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

/// Strings NF-engine increment master switch (`AY_STR_NF=1`, default OFF).
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
    *V.get_or_init(|| matches!(std::env::var("AY_STR_NF").ok().as_deref(), Some("1")))
}

/// Closures that `AY_STR_NF=1` alone must NOT enable, because they are known
/// to be UNSOUND on the current tree. Reaching them requires naming them
/// EXPLICITLY in `AY_STR_NF_CLOSURES` (for debugging / repair work only).
///
/// * **5** — "trusted post-string-lemma UNSAT acceptance". Measured
///   WRONG-UNSAT witness on current main:
///   `QF_SLIA/non-incremental__QF_SLIA__20180523-Reynolds__kaluza__sat__small__bettermatch1.readable.smt2`
///   (SMT-LIB `kaluza/sat/`; z3 4.16 answers `sat`) returns `unsat` under
///   `AY_STR_NF=1 AY_STR_NF_CLOSURES=5`, and under closure 5 alone. Only ONE
///   string lemma is lowered on that file — a `LengthSplit`, which lowers to
///   the tautology `[eq, ¬eq]` and therefore cannot turn a satisfiable clause
///   set unsatisfiable. The propositional UNSAT must therefore rest on a
///   theory conflict clause that is NOT a consequence of the original formula,
///   i.e. closure 5's second premise ("no distrusted conflict was ever turned
///   into a clause") does not hold here: the blanket post-string-lemma
///   downgrade that closure 5 removes is load-bearing for soundness, not only
///   for completeness. Fail closed until the escaping conflict is identified.
const NF_CLOSURES_REQUIRING_EXPLICIT_OPT_IN: &[u8] = &[5];

/// Per-closure sub-flag for A/B attribution under the `AY_STR_NF=1` master
/// switch. `AY_STR_NF_CLOSURES=1,3` enables only closures 1 and 3; unset (or
/// unparsable) enables every closure EXCEPT those in
/// [`NF_CLOSURES_REQUIRING_EXPLICIT_OPT_IN`]. Always `false` when the master
/// switch is off.
pub fn str_nf_closure_enabled(n: u8) -> bool {
    if !str_nf_enabled() {
        return false;
    }
    static SET: std::sync::OnceLock<Option<Vec<u8>>> = std::sync::OnceLock::new();
    let set = SET.get_or_init(|| {
        let raw = std::env::var("AY_STR_NF_CLOSURES").ok()?;
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

impl<'a> StringSolver<'a> {
    /// Create a new string solver with a reference to the term store.
    pub fn new(terms: &'a TermStore) -> Self {
        Self {
            terms,
            state: SolverState::new(),
            base: BaseSolver::new(),
            core: CoreSolver::new(),
            regexp: RegExpSolver::new(),
            infer: InferenceManager::new(),
            skolems: SkolemCache::new(),
            pre_registered_empty: None,
            cycle_conflict_trustworthy: false,
            check_count: 0,
            conflict_count: 0,
            propagation_count: 0,
        }
    }

    /// Pre-register the empty string term so endpoint-empty inferences work
    /// even when the formula doesn't contain an explicit `""` literal.
    pub fn set_empty_string_id(&mut self, id: TermId) {
        self.pre_registered_empty = Some(id);
        self.state.set_empty_string_id(self.terms, id);
    }

    /// Mark a term as having been reduced via DPLL-level reduction lemmas.
    /// The core solver will skip these terms in `check_extf_reductions`.
    pub fn mark_reduced(&mut self, term: TermId) {
        self.core.mark_reduced(term);
    }

    /// Extract warm state for cross-iteration preservation (#3762).
    ///
    /// Captures statistics and reduced-term markers that should persist
    /// across CEGAR iterations. Call this before dropping the solver
    /// (e.g., before `DpllT::into_sat_state()`), then call
    /// `import_warm_state()` on the replacement solver.
    pub fn take_warm_state(&self) -> StringSolverWarmState {
        StringSolverWarmState {
            check_count: self.check_count,
            conflict_count: self.conflict_count,
            propagation_count: self.propagation_count,
            reduced_terms: self.core.reduced_term_ids(),
        }
    }

    /// Import warm state from a previous CEGAR iteration (#3762).
    ///
    /// Restores statistics and reduced-term markers that were extracted
    /// via `take_warm_state()`. This avoids losing cumulative statistics
    /// and re-registering reduced terms externally.
    pub fn import_warm_state(&mut self, state: &StringSolverWarmState) {
        self.check_count = state.check_count;
        self.conflict_count = state.conflict_count;
        self.propagation_count = state.propagation_count;
        for &tid in &state.reduced_terms {
            self.core.mark_reduced(tid);
        }
    }

    /// Extract a concrete model for string variables.
    ///
    /// Only variables in EQCs with known constants are assigned. Variables in
    /// non-constant EQCs remain unassigned and are handled conservatively by
    /// the caller.
    /// Whether the last conflict from `check()` came from ground evaluation
    /// (constant conflicts, extf predicate/reduction checks) rather than
    /// NF-dependent reasoning. Ground conflicts are always trustworthy;
    /// NF-dependent conflicts may be spurious due to incomplete normal form
    /// computation (#6275).
    ///
    /// Only meaningful after `check()` returned `TheoryResult::Unsat`.
    pub fn is_ground_conflict(&self) -> bool {
        self.infer.is_ground_conflict()
    }

    /// Whether the conflict follows from cycle detection (I_CYCLE) inferences.
    /// Cycle-derived equalities (e.g., x = str.++(y,x) → y = "") are sound,
    /// so subsequent NF-based conflicts are trustworthy (#3875).
    ///
    /// Only meaningful after `check()` returned `TheoryResult::Unsat`.
    pub fn is_cycle_based_conflict(&self) -> bool {
        self.cycle_conflict_trustworthy
    }

    /// Extract a string model mapping variables to their resolved constant values.
    pub fn extract_model(&self) -> StringModel {
        let mut values = HashMap::default();
        for rep in self.state.eqc_representatives() {
            let Some(constant) = self.state.get_constant(&rep) else {
                continue;
            };
            let Some(members) = self.state.eqc_members(rep) else {
                continue;
            };
            for &member in members {
                if *self.terms.sort(member) == Sort::String
                    && matches!(self.terms.get(member), ay_core::term::TermData::Var(_, _))
                {
                    values.insert(member, constant.to_string());
                }
            }
        }
        StringModel { values }
    }

    /// When N-O propagates an integer equality where one side is `str.len(x)`
    /// and the other resolves to 0, infer `x = ""` by merging x with the empty
    /// string. This bridges the gap between LIA-derived length facts and
    /// string-level emptiness — the SAT-level bridge axiom
    /// `[NOT(str.len(x)=0), x=""]` cannot fire in the CEGAR architecture
    /// because the LIA-derived equality is not propagated as a SAT literal.
    fn infer_empty_from_zero_length(&mut self, lhs: TermId, rhs: TermId, reason: &[TheoryLit]) {
        // Identify which side is str.len(var) and which is the integer constant.
        let (len_term, const_term) = match (
            self.state.get_str_len_arg(self.terms, lhs),
            self.state.get_str_len_arg(self.terms, rhs),
        ) {
            (Some(_), None) => (lhs, rhs),
            (None, Some(_)) => (rhs, lhs),
            _ => return,
        };

        // Check if const_term resolves to 0.
        let is_zero = self
            .state
            .resolve_int_constant(self.terms, const_term)
            .is_some_and(|n| n == 0);
        if !is_zero {
            return;
        }

        // Get the string variable from str.len(var).
        let Some(str_var) = self.state.get_str_len_arg(self.terms, len_term) else {
            return;
        };

        // Use the cached empty string (registered during CEGAR init).
        let Some(empty) = self.state.empty_string_id() else {
            return;
        };

        // Ensure str_var is registered (it might not be if only seen inside str.len).
        self.state.register_term(self.terms, str_var);

        if self.state.find(str_var) != self.state.find(empty) {
            let _ = self.state.merge_with_explanation(str_var, empty, reason);
        }
    }

    /// Drain internal equalities from the inference engine and merge them
    /// into the local EQC state.
    ///
    /// Equalities with non-empty explanations are merged normally. Equalities
    /// with empty explanations are converted to SAT-level `EqualitySplit`
    /// lemmas instead of being silently dropped (#4025). This prevents
    /// premature fix-point convergence: the DPLL solver decides the equality
    /// with a proper reason chain, providing the explanation provenance that
    /// the proof forest was missing.
    fn merge_internal_equalities(&mut self) -> MergeResult {
        let mut merged_any = false;
        let mut deferred_splits = Vec::new();
        let internal_equalities = self.infer.drain_internal_equalities();
        for eq in internal_equalities {
            self.state.register_term(self.terms, eq.lhs);
            self.state.register_term(self.terms, eq.rhs);

            if self.state.find(eq.lhs) != self.state.find(eq.rhs) {
                // Soundness guard (#4057): reject internal equalities
                // with empty explanations. A merge with an empty explanation
                // creates a proof-forest edge with no reasons, causing all
                // downstream explain() calls through that edge to return
                // incomplete results.
                //
                // Instead of silently dropping (#4025), convert to a
                // SAT-level EqualitySplit so the DPLL solver decides the
                // equality. If DPLL assigns true, the equality comes back
                // via assert_literal with a proper SAT-level reason. If
                // false, the disequality is decided. Either way, the
                // fix-point loop no longer converges prematurely.
                if eq.explanation.is_empty() {
                    deferred_splits.push(StringLemma {
                        kind: StringLemmaKind::EqualitySplit,
                        x: eq.lhs,
                        y: eq.rhs,
                        char_offset: 0,
                        start_offset: 0,
                        reason: vec![],
                    });
                    continue;
                }
                let _ = self
                    .state
                    .merge_with_explanation(eq.lhs, eq.rhs, &eq.explanation);
                merged_any = true;
            }
        }
        MergeResult {
            merged_any,
            deferred_splits,
        }
    }
}

#[cfg(test)]
#[path = "lib_tests.rs"]
mod tests;

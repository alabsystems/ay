// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Core solver: word equation solving via normal forms.
//!
//! Implements the algorithm from Liang et al., "A DPLL(T) Theory Solver for
//! a Theory of Strings and Regular Expressions", CAV 2014.
//!
//! The CVC5 strategy pipeline executes these steps in order:
//! 1. `check_cycles` — detect containment cycles (x = t·x·u implies conflict
//!    if t or u is non-empty).
//! 2. `check_flat_forms` — lightweight pre-check using flattened concat terms.
//! 3. `check_normal_forms_eq_prop` — propagation-only NF equality (buffers splits).
//! 4. `check_extf_eval_effort1` — post-NF extf evaluation pass.
//! 5. `check_normal_forms_eq` — emit one buffered split lemma.
//! 6. `check_normal_forms_deq` — disequality checking via normal forms.
//!
//! Reference: `reference/cvc5/src/theory/strings/core_solver.h`
//! Reference: `reference/cvc5/src/theory/strings/core_solver.cpp`

use crate::arith_entail::ArithEntail;
use crate::infer::{InferenceKind, InferenceManager};
use crate::normal_form::NormalForm;
use crate::regexp::{MatchResult, RegExpSolver};
use crate::skolem::SkolemCache;
use crate::state::SolverState;
// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Constant, TermData, TermId, TermStore};
use ay_core::{Sort, StringLemma, StringLemmaKind, Symbol, TheoryLit};
use num_bigint::BigInt;
use std::sync::LazyLock;

mod cycles;
mod explanation;
mod extf_contains;
mod extf_effort1;
mod extf_effort1_helpers;
mod extf_eval;
mod extf_eval_effort1;
mod extf_eval_entailment;
mod extf_pass;
mod extf_pass_int;
mod extf_pass_reductions;
mod flat_forms;
mod nf_deq_process;
mod nf_disequality;
mod nf_equality;
mod nf_equality_simpleq;
mod normal_forms;
#[cfg(test)]
mod tests;

/// Cached debug flag: checked once at process startup instead of 20× per check().
/// Also enabled by `AY_DEBUG_THEORY=1` umbrella.
static DEBUG_STRING_CORE: LazyLock<bool> =
    LazyLock::new(|| ay_core::debug_channel_active(ay_core::DebugChannel::StringCore));

/// Result of a normal form comparison.
///
/// Distinguishes "no conflict, fully resolved" from "no conflict, but
/// bailed out on unresolved variable components".
#[derive(Debug)]
enum NfCheckResult {
    /// A conflict was found and added to the inference manager.
    Conflict,
    /// No conflict; all components were fully resolved.
    Ok,
    /// No conflict, but the comparison bailed out on a variable component
    /// that couldn't be resolved without split lemmas.
    Incomplete,
    /// A split lemma is needed to make progress. The caller must add this
    /// lemma clause to the SAT solver and re-run.
    NeedLemma(StringLemma),
}

#[derive(Copy, Clone, Debug)]
enum IntRelation {
    Lt,
    Le,
    Gt,
    Ge,
}

/// Argument key for extended-function substitution caching.
///
/// During effort-1 evaluation, extf applications are resolved per-argument
/// using the EQC representative or its constant value. This key type
/// identifies each resolved argument for deduplication.
#[derive(Clone, Debug, Eq, PartialEq, Hash, PartialOrd, Ord)]
enum ExtfArgKey {
    Rep(TermId),
    StrConst(String),
    IntConst(BigInt),
}

/// Composite key for deduplicating extended-function evaluations.
///
/// Two extf applications with the same symbol and resolved argument keys
/// will produce identical results, so only the first needs evaluation.
#[derive(Clone, Debug, Eq, PartialEq, Hash, PartialOrd, Ord)]
struct ExtfSubstKey {
    symbol: String,
    args: Vec<ExtfArgKey>,
}

/// A recorded `str.contains` fact from the assertion set.
///
/// Used by the contains-overlap checker to detect conflicts between
/// overlapping containment assertions and known string constants.
#[derive(Clone, Copy, Debug)]
struct ContainsFact {
    haystack: TermId,
    needle: TermId,
    lit: TheoryLit,
}

/// Core solver: word equation reasoning via normal forms.
#[derive(Debug, Default)]
pub(crate) struct CoreSolver {
    /// Computed normal forms, keyed by EQC representative.
    normal_forms: HashMap<TermId, NormalForm>,
    /// Flat forms: for each concat term, its flattened component list
    /// (EQC representatives with empties dropped). Computed during cycle check.
    ///
    /// Reference: CVC5 `d_flat_form` in `core_solver.h:589`
    flat_forms: HashMap<TermId, Vec<TermId>>,
    /// Map from canonical NF term vectors to the first EQC with that NF.
    /// Used in `check_normal_forms_eq_prop` to detect identical NFs across
    /// different EQCs and merge them (free propagation).
    ///
    /// Reference: CVC5 `nf_to_eqc` in `core_solver.cpp:562`
    nf_to_eqc: HashMap<Vec<TermId>, TermId>,
    /// Whether the last `check()` was incomplete (unresolved variables).
    ///
    /// Set when NF comparison bails out due to variable components that
    /// cannot be resolved without split lemmas. When true, the solver
    /// cannot soundly claim SAT — should return Unknown instead.
    incomplete: bool,
    /// A pending string split lemma request from `process_simple_neq`.
    ///
    /// Set when NF comparison identifies a split point (Cases 6-9 of CVC5's
    /// processSimpleNEq). The caller retrieves this via `take_pending_lemma()`
    /// and converts it to `TheoryResult::NeedStringLemma`.
    pending_lemma: Option<StringLemma>,
    /// Buffered split lemmas from the propagation-only NF equality pass.
    /// CVC5 stores these in `d_pinfers` and picks the best one in
    /// `checkNormalFormsEq`. This two-phase approach allows extf eval
    /// effort 1 to run between propagation and splitting.
    ///
    /// Reference: CVC5 `d_pinfers` in `core_solver.h:638`
    buffered_lemmas: Vec<StringLemma>,
    /// Terms that have been reduced via DPLL-level reduction lemmas
    /// (e.g., str.substr → word equation + arithmetic). These should NOT
    /// trigger `incomplete` in `check_extf_reductions` because their
    /// semantics are fully captured by the reduction axioms.
    ///
    /// Reference: CVC5 purification in `theory_strings_preprocess.cpp`
    reduced_terms: HashSet<TermId>,
    /// ADDITIONAL pending lemmas queued behind `pending_lemma` (NF-engine
    /// closure 3, `--str-nf`): distinct extra buffered NF split lemmas and
    /// extra dynamic reduction requests discovered in the same check round.
    /// Drained by the executor via `take_pending_string_lemmas` so a skolem
    /// web reduces in 1-2 CEGAR rounds instead of one round per lemma.
    /// Always empty when the closure is disabled.
    extra_lemmas: Vec<StringLemma>,
}

impl CoreSolver {
    // Keep recursive string/int resolution within the default Rust test-thread
    // stack budget; deeper chains degrade to `None`/Unknown instead of aborting.
    const MAX_RESOLVE_DEPTH: usize = 16;

    /// Maximum digit count for the on-demand `str.to_int` digit-decomposition
    /// reduction (extf wave 2). Bounds the number of per-length cases and
    /// digit skolems; longer strings fall back to `incomplete` (Unknown)
    /// exactly as before the reduction existed.
    const MAX_TO_INT_DIGITS: usize = 16;

    /// Budget for `str.replace_all` / regex-replace one-step reductions per
    /// solve (extf wave 2). Each reduction step recurses on a fresh
    /// `replace_all(suf, t, u)` application; this cap bounds the total chain
    /// so an unsatisfiable recursion falls back to `incomplete` (Unknown)
    /// instead of unrolling forever. Counted over already-reduced
    /// replace-family terms, which persist across CEGAR iterations via the
    /// warm-state reduced set.
    const MAX_REPLACE_ALL_STEPS: usize = 32;

    /// Cap on ADDITIONAL lemmas batched behind the primary one in a single
    /// check round (NF-engine closure 3). Bounds the per-round clause burst
    /// so a wide skolem web cannot flood the SAT solver in one iteration.
    const MAX_EXTRA_LEMMAS: usize = 8;

    /// Create a new core solver.
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Mark a term as having been reduced via DPLL-level reduction lemmas.
    /// Reduced terms are skipped by `check_extf_reductions` (they don't
    /// trigger the `incomplete` flag) because their semantics are captured
    /// by word equations and arithmetic constraints in the SAT encoding.
    pub(crate) fn mark_reduced(&mut self, term: TermId) {
        self.reduced_terms.insert(term);
    }

    /// Return a snapshot of all reduced term IDs for cross-iteration
    /// state preservation (#3762).
    pub(crate) fn reduced_term_ids(&self) -> Vec<TermId> {
        self.reduced_terms.iter().copied().collect()
    }

    /// Find a concrete upper bound for `len(s)` among the currently asserted
    /// literals, returning the bound and the literal justifying it.
    ///
    /// Only SYNTACTIC matches are used (`(str.len s)` with argument exactly
    /// `s` against an Int literal) so the returned literal alone justifies
    /// the bound — EQC-derived bounds would need merge explanations in the
    /// guard. Handled shapes (both argument orders, both polarities of the
    /// standard comparison symbols):
    /// - `len(s) = k` (positive) → bound `k`
    /// - `len(s) <= k`, `len(s) < k`, `k >= len(s)`, `k > len(s)` (positive)
    /// - negated lower bounds, e.g. `¬(len(s) >= k)` → bound `k-1`.
    ///
    /// Returns the SMALLEST bound found that is `<= MAX_TO_INT_DIGITS`.
    fn find_concrete_len_upper_bound(
        terms: &TermStore,
        state: &SolverState,
        s: TermId,
    ) -> Option<(usize, TheoryLit)> {
        let mut best: Option<(usize, TheoryLit)> = None;
        let consider = |bound: BigInt, lit: TheoryLit, best: &mut Option<(usize, TheoryLit)>| {
            let Ok(bound) = usize::try_from(bound) else {
                return;
            };
            if bound > Self::MAX_TO_INT_DIGITS {
                return;
            }
            if best.as_ref().is_none_or(|(b, _)| bound < *b) {
                *best = Some((bound, lit));
            }
        };
        for &lit in state.assertions() {
            let (atom, pol) = Self::atom_and_polarity(terms, lit);
            let TermData::App(Symbol::Named(rel), args) = terms.get(atom) else {
                continue;
            };
            if args.len() != 2 {
                continue;
            }
            let is_len_of_s = |t: TermId| {
                matches!(
                    terms.get(t),
                    TermData::App(Symbol::Named(n), a)
                        if n == "str.len" && a.len() == 1 && a[0] == s
                )
            };
            let int_const = |t: TermId| match terms.get(t) {
                TermData::Const(Constant::Int(k)) => Some(k.clone()),
                _ => None,
            };
            for (len_side, const_side, len_on_left) in
                [(args[0], args[1], true), (args[1], args[0], false)]
            {
                if !is_len_of_s(len_side) {
                    continue;
                }
                let Some(k) = int_const(const_side) else {
                    continue;
                };
                if k.sign() == num_bigint::Sign::Minus {
                    continue;
                }
                // Normalize to "len(s) REL k" and apply the polarity.
                // upper: len <= k. strict-upper: len < k (bound k-1).
                let bound = match (rel.as_str(), len_on_left, pol) {
                    ("=", _, true) => Some(k),
                    ("<=", true, true) | (">=", false, true) => Some(k),
                    ("<", true, true) | (">", false, true) => Some(k - 1),
                    // Negated lower bounds are upper bounds:
                    // ¬(len >= k) ⇔ len < k ; ¬(k <= len) ⇔ len < k
                    (">=", true, false) | ("<=", false, false) => Some(k - 1),
                    // ¬(len > k) ⇔ len <= k ; ¬(k < len) ⇔ len <= k
                    (">", true, false) | ("<", false, false) => Some(k),
                    _ => None,
                };
                if let Some(b) = bound {
                    if b.sign() != num_bigint::Sign::Minus {
                        consider(b, lit, &mut best);
                    }
                }
            }
        }
        best
    }

    /// Count already-reduced replace-family applications (used as the
    /// recursion budget for the `str.replace_all` one-step reduction).
    fn reduced_replace_all_steps(&self, terms: &TermStore) -> usize {
        self.reduced_terms
            .iter()
            .filter(|&&t| {
                matches!(
                    terms.get(t),
                    TermData::App(Symbol::Named(n), a)
                        if a.len() == 3 && (n == "str.replace_all" || n == "str.replace_re_all")
                )
            })
            .count()
    }

    /// Request an on-demand reduction lemma for a runtime extf term.
    ///
    /// Symbolic `str.substr` terms are no longer eagerly preregistered when
    /// their bounds are non-constant (#4057). When one of those terms blocks
    /// theory progress, request the same reduction axiom on demand instead of
    /// latching `Unknown` forever.
    fn request_dynamic_extf_lemma(
        &mut self,
        terms: &TermStore,
        state: &SolverState,
        term: TermId,
    ) -> bool {
        // Closure 3 (`--str-nf`, sub-flag 3): with a lemma already pending,
        // the pre-closure path stopped here — one dynamic reduction lemma per
        // check, so a 5-substr web needed ~10 CEGAR rounds. Under the closure
        // the request is still built and QUEUED (bounded), so the executor
        // lowers the whole reduction batch in one iteration. Each reduction
        // axiom is universally valid on its own (see reductions.rs), so
        // batching cannot change any answer — only the round count.
        if self.pending_lemma.is_some() {
            if !crate::str_nf_closure_enabled(3)
                || self.extra_lemmas.len() >= Self::MAX_EXTRA_LEMMAS
            {
                return true;
            }
            let Some(extra) = Self::build_dynamic_extf_lemma(terms, state, self, term) else {
                return false;
            };
            if self.pending_lemma.as_ref() != Some(&extra) && !self.extra_lemmas.contains(&extra) {
                self.extra_lemmas.push(extra);
            }
            return true;
        }
        let Some(lemma) = Self::build_dynamic_extf_lemma(terms, state, self, term) else {
            return false;
        };
        self.pending_lemma = Some(lemma);
        true
    }

    /// Build the dynamic reduction lemma for `term`, if one applies.
    ///
    /// Split out of `request_dynamic_extf_lemma` so closure 3 can queue
    /// ADDITIONAL requests behind an already-pending one without duplicating
    /// the per-symbol axiom selection.
    fn build_dynamic_extf_lemma(
        terms: &TermStore,
        state: &SolverState,
        core: &Self,
        term: TermId,
    ) -> Option<StringLemma> {
        let TermData::App(Symbol::Named(name), args) = terms.get(term) else {
            return None;
        };
        if name == "str.substr" && args.len() == 3 {
            return Some(StringLemma {
                kind: StringLemmaKind::SubstrReduction,
                x: term,
                y: term,
                char_offset: 0,
                start_offset: 0,
                reason: Vec::new(),
            });
        }
        // CAP-2: symbolic str.indexof blocks progress the same way symbolic
        // str.substr does. Request the first-occurrence reduction axiom on
        // demand instead of latching `incomplete` (Unknown) forever.
        if name == "str.indexof" && args.len() == 3 {
            return Some(StringLemma {
                kind: StringLemmaKind::IndexofReduction,
                x: term,
                y: term,
                char_offset: 0,
                start_offset: 0,
                reason: Vec::new(),
            });
        }
        // CAP-2 follow-on: symbolic str.replace gets the first-occurrence
        // replacement axiom on demand.
        if name == "str.replace" && args.len() == 3 {
            return Some(StringLemma {
                kind: StringLemmaKind::ReplaceReduction,
                x: term,
                y: term,
                char_offset: 0,
                start_offset: 0,
                reason: Vec::new(),
            });
        }
        // Extf wave 2: str.to_int digit decomposition. Requires a concrete
        // upper bound on len(arg) from an asserted literal; the bound is
        // carried in char_offset and the literal guards every emitted case
        // clause. No bound → fall through to incomplete (Unknown), exactly
        // as before.
        if (name == "str.to_int" || name == "str.to.int") && args.len() == 1 {
            let (bound, guard_lit) = Self::find_concrete_len_upper_bound(terms, state, args[0])?;
            return Some(StringLemma {
                kind: StringLemmaKind::ToIntReduction,
                x: term,
                y: term,
                char_offset: bound,
                start_offset: 0,
                reason: vec![guard_lit],
            });
        }
        // Extf wave 2: str.from_int via the mutual to_int definition plus a
        // canonical-decimal regex. Universally valid — no bound needed.
        if (name == "str.from_int" || name == "int.to.str") && args.len() == 1 {
            return Some(StringLemma {
                kind: StringLemmaKind::FromIntReduction,
                x: term,
                y: term,
                char_offset: 0,
                start_offset: 0,
                reason: Vec::new(),
            });
        }
        // Extf wave 2: str.replace_all one-step first-match reduction. The
        // step recurses on a fresh replace_all(suf, t, u) application, so a
        // budget bounds the total chain; past it, fall through to incomplete
        // (Unknown) — never hang, never guess.
        if name == "str.replace_all" && args.len() == 3 {
            if core.reduced_replace_all_steps(terms) >= Self::MAX_REPLACE_ALL_STEPS {
                return None;
            }
            return Some(StringLemma {
                kind: StringLemmaKind::ReplaceAllReduction,
                x: term,
                y: term,
                char_offset: 0,
                start_offset: 0,
                reason: Vec::new(),
            });
        }
        // Extf wave 2 Part B: regex replace partial reductions. Only for
        // GROUND engine-evaluable regexes — the reduction relies on ground
        // evaluation for the exact first-match semantics once the haystack
        // resolves; anything else keeps the incomplete/Unknown behavior.
        if (name == "str.replace_re" || name == "str.replace_re_all")
            && args.len() == 3
            && crate::regex_ground_evaluable(terms, args[1])
        {
            let kind = if name == "str.replace_re" {
                StringLemmaKind::ReplaceReReduction
            } else {
                StringLemmaKind::ReplaceReAllReduction
            };
            return Some(StringLemma {
                kind,
                x: term,
                y: term,
                char_offset: 0,
                start_offset: 0,
                reason: Vec::new(),
            });
        }
        None
    }

    /// Handle an int-valued extf application that could not be evaluated.
    ///
    /// Ordered fallback (CAP-2):
    /// 1. Already reduced via a DPLL-level reduction lemma → its semantics are
    ///    fully captured by the emitted axioms; nothing to do.
    /// 2. A dynamic reduction lemma is available (str.indexof) → request it so
    ///    the executor lowers the exact semantics instead of giving up.
    /// 3. Otherwise latch `incomplete` so the solver reports Unknown rather
    ///    than an unsound SAT.
    fn note_unreduced_int_app(&mut self, terms: &TermStore, state: &SolverState, term: TermId) {
        if self.reduced_terms.contains(&term) {
            return;
        }
        if self.request_dynamic_extf_lemma(terms, state, term) {
            return;
        }
        if *DEBUG_STRING_CORE {
            eprintln!(
                "[STRING_CORE] note_unreduced_int_app latches incomplete: {:?} = {:?}",
                term,
                terms.get(term)
            );
        }
        self.incomplete = true;
    }

    /// Run the core solver pipeline.
    ///
    /// Returns `true` if a conflict was found (caller should stop).
    /// Sets `self.incomplete` if the solver couldn't fully resolve all
    /// string equalities (e.g., unresolved variables without split lemmas).
    ///
    /// `skolems` is used to deduplicate split lemma requests: when multiple
    /// EQC pairs in the same check round would request the same split (e.g.,
    /// EmptySplit on x), only the first request is emitted.
    pub(crate) fn check(
        &mut self,
        terms: &TermStore,
        state: &SolverState,
        infer: &mut InferenceManager,
        skolems: &mut SkolemCache,
    ) -> bool {
        self.pending_lemma = None;

        if *DEBUG_STRING_CORE {
            // Dump term store for a range of IDs to understand numbering.
            for i in 0..terms.len().min(30) {
                let tid = TermId(i as u32);
                let tdata = terms.get(tid);
                if !matches!(
                    tdata,
                    TermData::Const(Constant::Bool(true)) | TermData::Const(Constant::Bool(false))
                ) {
                    eprintln!("[STRING_CORE] term {tid:?} = {tdata:?}");
                }
            }
            // Dump all assertions with their term data.
            for &lit in state.assertions() {
                let (atom, pol) = Self::atom_and_polarity(terms, lit);
                let tdata = terms.get(atom);
                eprintln!("[STRING_CORE] check() assertion: {atom:?} pol={pol} term={tdata:?}");
            }
            // Dump all string-sorted EQC constants for tracing false conflicts.
            let mut eqc_info = Vec::new();
            for &lit in state.assertions() {
                let (atom, _pol) = Self::atom_and_polarity(terms, lit);
                if let TermData::App(_sym, args) = terms.get(atom) {
                    for &arg in args {
                        if *terms.sort(arg) == Sort::String {
                            let s = Self::resolve_string_term(terms, state, arg, 0);
                            if s.is_some() {
                                eqc_info.push(format!("{arg:?}={s:?}"));
                            }
                        }
                    }
                }
            }
            if !eqc_info.is_empty() {
                eprintln!(
                    "[STRING_CORE] check() resolved strings: {}",
                    eqc_info.join(", ")
                );
            }
        }

        // Step 1: Check for containment cycles.
        if self.check_cycles(terms, state, infer) {
            if *DEBUG_STRING_CORE {
                eprintln!("[STRING_CORE] conflict from check_cycles");
            }
            return true;
        }

        // Step 1b: Check flat forms (lightweight pre-NF conflict detection).
        // Flat forms are single-level flattened concat representations — cheaper
        // than full normal forms. Can detect conflicts and infer equalities early.
        // Reference: CVC5 CHECK_FLAT_FORMS in strategy.cpp:138
        self.build_flat_forms(terms, state);
        if self.check_flat_forms(terms, state, infer) {
            if *DEBUG_STRING_CORE {
                eprintln!("[STRING_CORE] conflict from check_flat_forms");
            }
            return true;
        }

        // Step 1c: Regex length-set disjointness. When an asserted-true
        // `str.in_re(x, R)` has a FINITE accepted-length set L(R) and `x`'s
        // length is a known concrete value not in L(R), the membership is
        // unsatisfiable. Runs BEFORE the per-value membership-violation check so
        // the STRONG general clause `¬in_re(x,R) ∨ ¬(len(x)=n)` is learned —
        // this closes the whole `len=n` branch at once, instead of letting the
        // SAT layer enumerate (and individually refute) every candidate string
        // of the excluded length. Sound: L(R) is the exact set of lengths any
        // R-accepted string can have.
        if self.check_regex_length_disjoint(terms, state, infer) {
            if *DEBUG_STRING_CORE {
                eprintln!("[STRING_CORE] conflict from check_regex_length_disjoint");
            }
            return true;
        }

        // Step 1d: Ground regex-membership violations. Must run before the
        // extf passes so a violated `str.in_re(s, R)` (e.g. the SAT solver
        // branched on `s = ""` against a non-nullable regex) is refuted with
        // the membership literal in the explanation, forcing the SAT solver to
        // abandon that string assignment. Otherwise the downstream str.at /
        // str.to_int reductions refute the model with a clause that omits the
        // membership literal and the implied length bound is never enforced.
        if self.check_regex_membership_violations(terms, state, infer) {
            if *DEBUG_STRING_CORE {
                eprintln!("[STRING_CORE] conflict from check_regex_membership_violations");
            }
            return true;
        }

        // Step 2: Evaluate extf predicates when arguments resolve to constants.
        if self.check_extf_predicates(terms, state, infer) {
            if *DEBUG_STRING_CORE {
                eprintln!("[STRING_CORE] conflict from check_extf_predicates");
            }
            return true;
        }

        // Step 2b: Evaluate value-returning extf applications and check for
        // conflicts with EQC constants (e.g., str.at("hello",0) in EQC with "e").
        if self.check_extf_reductions(terms, state, infer) {
            if *DEBUG_STRING_CORE {
                eprintln!("[STRING_CORE] conflict from check_extf_reductions");
            }
            return true;
        }
        // NOTE (CAP-2): a pending reduction lemma (substr/indexof/replace) is
        // NOT returned here. The cheap ground/entailment conflict passes below
        // (int reductions, NF propagation, extf eval effort 1) must run first
        // so a same-round refutation (e.g. `str.replace(x, x, z) = c` with
        // `z != c`) is reported as UNSAT instead of deferring to a reduction
        // lemma round. The lemma is surfaced right before the split-lemma
        // passes, which could otherwise overwrite `pending_lemma`.
        if *DEBUG_STRING_CORE && self.incomplete {
            eprintln!("[STRING_CORE] incomplete after check_extf_reductions");
        }

        // Step 2c: Evaluate integer-valued string functions (str.to_int,
        // str.indexof, str.to_code) and check against asserted integer
        // equalities.
        // NOTE: Only check non-length int reductions to avoid false conflicts
        // when EQC state is stale (e.g., x in EQC with "abc" from prior CEGAR
        // iteration but len(x)=1 asserted). str.len is handled by the LIA
        // solver and length axiom infrastructure.
        if self.check_extf_int_reductions(terms, state, infer) {
            if *DEBUG_STRING_CORE {
                eprintln!("[STRING_CORE] conflict from check_extf_int_reductions");
            }
            return true;
        }
        if *DEBUG_STRING_CORE && self.incomplete {
            eprintln!("[STRING_CORE] incomplete after check_extf_int_reductions");
        }

        // Step 2d: Simplify concat terms where all but one child is empty.
        // When str.++(c1, c2, ...) has exactly one non-empty child `c_k`,
        // infer str.++(c1, ..., cn) = c_k. This breaks mutual NF dependency
        // cycles that arise after I_CYCLE infers extras="" (#3850).
        let singleton_eqs_before = infer.internal_equality_count();
        if self.simplify_singleton_concats(terms, state, infer) {
            if *DEBUG_STRING_CORE {
                eprintln!("[STRING_CORE] conflict from simplify_singleton_concats");
            }
            return true;
        }
        // If the singleton-concat pass queued new equalities, stop this round
        // BEFORE the NF passes so the caller's internal-fact loop merges them
        // first (#3850 cases 130/135). Every queued equality has
        // find(lhs) != find(rhs), so the merge always makes progress. Without
        // this, `check_normal_forms_deq` sees `x` and `str.++(x, y)` (y = "")
        // in different EQCs with identical NFs and reports an NF-dependent
        // conflict whose explanation misses the y = "" premise — a conflict
        // the SLIA adapter must fail-closed downgrade to Unknown (#6261).
        // After the merge, the same contradiction surfaces as a same-EQC
        // disequality violation: unconditionally sound (#3875) and explained
        // through the proof forest with the merge reasons included.
        if infer.internal_equality_count() > singleton_eqs_before {
            if *DEBUG_STRING_CORE {
                eprintln!(
                    "[STRING_CORE] simplify_singleton_concats queued equalities — deferring NF passes to merge first"
                );
            }
            return false;
        }

        // Step 3: Compute normal forms for all EQCs.
        self.compute_normal_forms(terms, state);

        // Step 4: NF equality — propagation only (CVC5 CHECK_NORMAL_FORMS_EQ_PROP).
        // Detects conflicts, infers internal equalities from identical NFs
        // across EQCs, and buffers split lemmas for later emission.
        // Reference: CVC5 strategy.cpp:142
        match self.check_normal_forms_eq_prop(terms, state, infer, skolems) {
            NfCheckResult::Conflict => {
                if *DEBUG_STRING_CORE {
                    eprintln!("[STRING_CORE] conflict from check_normal_forms_eq_prop");
                }
                return true;
            }
            NfCheckResult::Incomplete => {
                self.incomplete = true;
                if *DEBUG_STRING_CORE {
                    eprintln!("[STRING_CORE] incomplete from check_normal_forms_eq_prop");
                }
            }
            NfCheckResult::Ok => {}
            NfCheckResult::NeedLemma(_) => unreachable!("prop phase buffers lemmas"),
        }

        // Step 4b: Re-evaluate extf terms using NF-derived substitutions.
        // Running this BEFORE emitting split lemmas allows extf reduction
        // to resolve things cheaply, avoiding unnecessary splits.
        // Reference: CVC5 strategy.cpp:144
        if self.check_extf_eval_effort1(terms, state, infer) {
            if *DEBUG_STRING_CORE {
                eprintln!("[STRING_CORE] conflict from check_extf_eval_effort1");
            }
            return true;
        }

        // CAP-2: a pending dynamic reduction lemma (substr / indexof /
        // replace) requested by the extf passes above is NOT returned early:
        // the split/disequality passes below both detect conflicts (e.g. the
        // z != c refutation after a `replace(x, x, z) -> z` unify merge) and
        // may overwrite `pending_lemma` with a split — either outcome makes
        // progress, and the reduction is re-requested on the next round if
        // still blocking. The caller collects whatever lemma survives via
        // `take_pending_lemma()`.

        // Step 4c: NF equality — emit one buffered split lemma (CVC5 CHECK_NORMAL_FORMS_EQ).
        // If the prop phase buffered a split candidate and extf eval didn't
        // resolve it, emit the split now.
        // Reference: CVC5 strategy.cpp:143
        match self.check_normal_forms_eq() {
            NfCheckResult::NeedLemma(lemma) => {
                self.pending_lemma = Some(lemma);
                return false;
            }
            NfCheckResult::Ok => {}
            NfCheckResult::Conflict | NfCheckResult::Incomplete => {}
        }

        // Step 5: Check normal form disequalities (#4070).
        match self.check_normal_forms_deq(terms, state, infer, skolems) {
            NfCheckResult::Conflict => {
                if *DEBUG_STRING_CORE {
                    eprintln!("[STRING_CORE] conflict from check_normal_forms_deq");
                }
                return true;
            }
            NfCheckResult::NeedLemma(lemma) => {
                self.pending_lemma = Some(lemma);
                return false;
            }
            NfCheckResult::Incomplete => {
                self.incomplete = true;
                if *DEBUG_STRING_CORE {
                    eprintln!("[STRING_CORE] incomplete from check_normal_forms_deq");
                }
            }
            NfCheckResult::Ok => {}
        }

        false
    }

    /// Get the normal form for an EQC representative.
    #[cfg(test)]
    pub(crate) fn get_normal_form(&self, rep: &TermId) -> Option<&NormalForm> {
        self.normal_forms.get(rep)
    }

    /// Whether the last check was incomplete due to unresolved variables.
    pub(crate) fn is_incomplete(&self) -> bool {
        self.incomplete
    }

    /// Take a pending string split lemma request, if any.
    pub(crate) fn take_pending_lemma(&mut self) -> Option<StringLemma> {
        self.pending_lemma.take()
    }

    /// Take the ADDITIONAL lemmas batched behind the primary one
    /// (NF-engine closure 3). Always empty when the closure is disabled.
    pub(crate) fn take_extra_lemmas(&mut self) -> Vec<StringLemma> {
        std::mem::take(&mut self.extra_lemmas)
    }

    /// Clear computed state for a new check round.
    pub(crate) fn clear(&mut self) {
        self.normal_forms.clear();
        self.flat_forms.clear();
        self.nf_to_eqc.clear();
        self.incomplete = false;
        self.pending_lemma = None;
        self.buffered_lemmas.clear();
        // Closure 3: batched extras are per-round. They are drained by the
        // executor immediately after the round that produced them returns
        // `NeedStringLemma`; anything still here belongs to a superseded
        // round and must not leak into the next one.
        self.extra_lemmas.clear();
    }
}

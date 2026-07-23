// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! QF_SLIA solving pipeline: combined Strings + EUF + LIA theory.
//!
//! Split from `strings.rs` for code health (#7006, #5970).
//! The pure QF_S solver remains in `strings.rs`; shared helpers
//! (decomposition, bounded-var detection, alphabet, candidates)
//! are in `strings_analysis.rs`.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Constant, Symbol, TermData};
use ay_core::{Sort, StringLemma, TermId};

use crate::combined_solvers::StringsLiaSolver;
use crate::executor_types::{Result, SolveResult};

use super::super::mod_div_elim::eliminate_int_mod_div_by_constant;
use super::super::Executor;
use super::skolem_cache::ExecutorSkolemCache;
use super::strings_analysis::{MAX_CONSECUTIVE_DUPLICATE_LEMMAS, MAX_PIVOT_CANDIDATES};
use super::{debug_auflia_enabled, MAX_SPLITS_LIA, MAX_STRING_LEMMA_ITERATIONS};

impl Executor {
    /// Is `pivot` provably constrained so that every character of any
    /// satisfying value comes from the formula's constant alphabet?
    ///
    /// Soundness of the pivot-enumeration `all_unsat → UNSAT` shortcut depends
    /// on the enumerated candidate set (strings over the constant alphabet)
    /// covering *every* possible satisfying value of the pivot. That holds only
    /// when the pivot is forced into the alphabet by a word equation against a
    /// constant, e.g. `(= (str.++ ... pivot ...) "abc")` or `(= pivot "abc")`:
    /// each pivot character must then equal some character of a constant.
    ///
    /// For an UNGROUNDED pivot (e.g. only `len(x)=1 ∧ x != "a"`), a satisfying
    /// value can use a character outside the alphabet (`x = "b"`), so an
    /// alphabet-restricted enumeration that finds every candidate UNSAT does
    /// NOT prove UNSAT (#927). In that case the caller must fall through to the
    /// sound CEGAR loop instead of emitting a spurious UNSAT.
    ///
    /// This is a conservative, sound check: it only returns `true` when the
    /// pivot appears as an operand of a `str.++` whose other side is a string
    /// constant, or is directly equated to a string constant. Returning `false`
    /// never causes unsoundness — it only forgoes the fast-UNSAT shortcut.
    fn pivot_alphabet_grounded(&self, pivot: TermId) -> bool {
        self.ctx.assertions.iter().any(|&assertion| {
            let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(assertion) else {
                return false;
            };
            if name != "=" || args.len() != 2 {
                return false;
            }
            // Identify a (concat-or-var) side paired with a string constant.
            let (other, is_const_rhs) =
                match (self.ctx.terms.get(args[0]), self.ctx.terms.get(args[1])) {
                    (_, TermData::Const(Constant::String(_))) => (args[0], true),
                    (TermData::Const(Constant::String(_)), _) => (args[1], true),
                    _ => (args[0], false),
                };
            if !is_const_rhs {
                return false;
            }
            match self.ctx.terms.get(other) {
                // (= pivot "const")
                TermData::Var(..) => other == pivot,
                // (= (str.++ ... pivot ...) "const")
                TermData::App(Symbol::Named(op), cargs) if op == "str.++" => {
                    cargs.iter().any(|&a| a == pivot)
                }
                _ => false,
            }
        })
    }

    pub(super) fn explicit_string_assignments(
        &self,
        assertions: &[TermId],
    ) -> HashMap<TermId, String> {
        let mut assignments = HashMap::default();

        for &assertion in assertions {
            let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(assertion) else {
                continue;
            };
            if name != "=" || args.len() != 2 {
                continue;
            }

            let lhs = args[0];
            let rhs = args[1];
            match (self.ctx.terms.get(lhs), self.ctx.terms.get(rhs)) {
                (TermData::Var(_, _), TermData::Const(Constant::String(value)))
                    if *self.ctx.terms.sort(lhs) == Sort::String =>
                {
                    assignments.insert(lhs, value.clone());
                }
                (TermData::Const(Constant::String(value)), TermData::Var(_, _))
                    if *self.ctx.terms.sort(rhs) == Sort::String =>
                {
                    assignments.insert(rhs, value.clone());
                }
                _ => {}
            }
        }

        assignments
    }

    /// Eagerly propagate string constants through concatenation equations (#7464).
    ///
    /// Given a set of known variable → constant assignments (from both
    /// original assertions and pivot assumptions), scan for concatenation
    /// equalities like `(= (str.++ x y) "abc")`. When all but one operand
    /// are known constants, derive the remaining operand's value and add
    /// a new equality term `(= unknown_var "remainder")` to the result.
    ///
    /// This improves completeness for multi-variable pivot enumeration by
    /// giving the inner CEGAR loop the derived assignments upfront, avoiding
    /// stalls when the string solver tries wrong splits first.
    fn propagate_concat_constants(
        &mut self,
        assertions: &[TermId],
        assumptions: &[TermId],
    ) -> Vec<TermId> {
        let mut known = self.explicit_string_assignments(assertions);
        known.extend(self.explicit_string_assignments(assumptions));
        if known.is_empty() {
            return Vec::new();
        }

        let mut derived = Vec::new();
        let all_terms: Vec<TermId> = assertions
            .iter()
            .chain(assumptions.iter())
            .copied()
            .collect();

        // Fixed-point: derived values may enable further propagation.
        let mut changed = true;
        while changed {
            changed = false;
            for &term in &all_terms {
                let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(term) else {
                    continue;
                };
                if name != "=" || args.len() != 2 {
                    continue;
                }
                let lhs = args[0];
                let rhs = args[1];
                // Match (= (str.++ ...) "constant") or (= "constant" (str.++ ...))
                let (concat_term, target_str) =
                    match (self.ctx.terms.get(lhs), self.ctx.terms.get(rhs)) {
                        (
                            TermData::App(Symbol::Named(n), _),
                            TermData::Const(Constant::String(s)),
                        ) if n == "str.++" => (lhs, s.clone()),
                        (
                            TermData::Const(Constant::String(s)),
                            TermData::App(Symbol::Named(n), _),
                        ) if n == "str.++" => (rhs, s.clone()),
                        _ => continue,
                    };
                let TermData::App(_, concat_args) = self.ctx.terms.get(concat_term) else {
                    continue;
                };
                let concat_args: Vec<TermId> = concat_args.clone();
                // Check which concat args are known and which are unknown.
                // Count unknown operands: we can only derive a value when
                // exactly one operand is unknown.
                let mut unknown_idx = None;
                let mut all_known_except_one = true;
                for (idx, &arg) in concat_args.iter().enumerate() {
                    if known.contains_key(&arg) {
                        // Known from explicit assignment or prior derivation
                    } else if matches!(
                        self.ctx.terms.get(arg),
                        TermData::Const(Constant::String(_))
                    ) {
                        // Known string constant
                    } else if unknown_idx.is_none() {
                        unknown_idx = Some(idx);
                    } else {
                        all_known_except_one = false;
                        break;
                    }
                }
                if !all_known_except_one {
                    continue;
                }
                let Some(unk_idx) = unknown_idx else {
                    continue; // All known — no new derivation needed.
                };
                // Already derived for this variable.
                let unknown_var = concat_args[unk_idx];
                if known.contains_key(&unknown_var) {
                    continue;
                }
                // Compute prefix before and suffix after the unknown.
                let target_chars: Vec<char> = target_str.chars().collect();
                let mut prefix_chars = 0usize;
                for (idx, &arg) in concat_args.iter().enumerate() {
                    if idx == unk_idx {
                        break;
                    }
                    if let Some(val) = known.get(&arg) {
                        prefix_chars += val.chars().count();
                    } else if let TermData::Const(Constant::String(s)) = self.ctx.terms.get(arg) {
                        prefix_chars += s.chars().count();
                    }
                }
                let mut suffix_chars = 0usize;
                for &arg in concat_args.iter().skip(unk_idx + 1) {
                    if let Some(val) = known.get(&arg) {
                        suffix_chars += val.chars().count();
                    } else if let TermData::Const(Constant::String(s)) = self.ctx.terms.get(arg) {
                        suffix_chars += s.chars().count();
                    }
                }
                let remaining = target_chars.len().checked_sub(prefix_chars + suffix_chars);
                let Some(remaining_len) = remaining else {
                    continue; // Length mismatch — UNSAT will be detected by the solver.
                };
                if prefix_chars + remaining_len > target_chars.len() {
                    continue;
                }
                let derived_val: String = target_chars[prefix_chars..prefix_chars + remaining_len]
                    .iter()
                    .collect();
                // Verify the variable is a string sort variable.
                if !matches!(self.ctx.terms.get(unknown_var), TermData::Var(..))
                    || *self.ctx.terms.sort(unknown_var) != Sort::String
                {
                    continue;
                }
                let str_term = self.ctx.terms.mk_string(derived_val.clone());
                let eq = self.ctx.terms.mk_eq(unknown_var, str_term);
                derived.push(eq);
                known.insert(unknown_var, derived_val);
                changed = true;
            }
        }
        derived
    }

    /// Try minimal prefix/suffix overlap-merge witnesses for unbounded
    /// variables constrained only by `str.prefixof`/`str.suffixof`.
    ///
    /// Returns `Ok(Some(Sat))` only when a candidate is found AND fully model
    /// validated by the inner assumption solve (so no unsound SAT can escape).
    /// Returns `Ok(None)` when no eligible witness applies or none validated,
    /// letting the caller fall through to the normal pipeline. A candidate that
    /// solves to UNSAT does not let us conclude global UNSAT (other witnesses or
    /// non-minimal models may satisfy), so UNSAT candidates are skipped.
    pub(super) fn try_prefix_suffix_witnesses(&mut self) -> Result<Option<SolveResult>> {
        let witnesses = self.detect_prefix_suffix_witnesses();
        self.try_string_var_witnesses(witnesses)
    }

    /// Try positive `contains`/`prefixof`/`suffixof` witnesses over a
    /// partially-grounded `str.++` (see `detect_concat_predicate_witnesses`).
    ///
    /// Same soundness contract as [`Self::try_prefix_suffix_witnesses`]: every
    /// candidate is fully model-validated before SAT is trusted, so an
    /// over-eager guess falls through to the normal pipeline rather than
    /// escaping as a wrong SAT.
    pub(super) fn try_concat_predicate_witnesses(&mut self) -> Result<Option<SolveResult>> {
        let witnesses = self.detect_concat_predicate_witnesses();
        self.try_string_var_witnesses(witnesses)
    }

    /// Try each `(var, candidate values)` witness as a hard assumption,
    /// returning `Ok(Some(Sat))` only when a candidate is found AND fully
    /// model validated by the inner assumption solve (so no unsound SAT can
    /// escape). Returns `Ok(None)` when no eligible witness applies or none
    /// validated, letting the caller fall through to the normal pipeline. A
    /// candidate that solves to UNSAT does not let us conclude global UNSAT
    /// (other witnesses or non-minimal models may satisfy), so UNSAT
    /// candidates are skipped.
    pub(super) fn try_string_var_witnesses(
        &mut self,
        witnesses: Vec<super::strings_analysis::PrefixSuffixWitness>,
    ) -> Result<Option<SolveResult>> {
        if witnesses.is_empty() {
            return Ok(None);
        }

        // Pre-create candidate equality terms before borrowing DpllT (one var at
        // a time keeps the candidate set small; multiple eligible vars are rare).
        let assertions_snapshot = self.ctx.assertions.clone();
        let saved_deadline = self.solve_deadline.get();
        let saved_last_model = self.last_model.clone();
        let saved_last_result = self.last_result.clone();
        let saved_last_unknown_reason = self.last_unknown_reason;
        let saved_last_model_validated = self.last_model_validated;
        let saved_last_validation_stats = self.last_validation_stats.clone();
        let saved_last_assumption_core = self.last_assumption_core.clone();
        let saved_bypass_taut = self.bypass_string_tautology_guard;
        let saved_slia_accepted = self.slia_accepted_unknown;
        let saved_skip_model_eval = self.skip_model_eval;

        for witness in &witnesses {
            let candidate_eqs: Vec<TermId> = witness
                .candidates
                .iter()
                .map(|s| {
                    let str_term = self.ctx.terms.mk_string(s.clone());
                    self.ctx.terms.mk_eq(witness.var, str_term)
                })
                .collect();

            self.pivot_enum_depth += 1;
            for (i, &eq_term) in candidate_eqs.iter().enumerate() {
                if self.should_abort_theory_loop() {
                    self.pivot_enum_depth -= 1;
                    self.restore_witness_state(
                        saved_deadline,
                        &saved_last_model,
                        &saved_last_result,
                        saved_last_unknown_reason,
                        saved_last_model_validated,
                        &saved_last_validation_stats,
                        &saved_last_assumption_core,
                        saved_bypass_taut,
                        saved_slia_accepted,
                        saved_skip_model_eval,
                    );
                    return Ok(Some(SolveResult::Unknown));
                }

                self.restore_witness_state(
                    saved_deadline,
                    &saved_last_model,
                    &saved_last_result,
                    saved_last_unknown_reason,
                    saved_last_model_validated,
                    &saved_last_validation_stats,
                    &saved_last_assumption_core,
                    saved_bypass_taut,
                    saved_slia_accepted,
                    saved_skip_model_eval,
                );

                let candidate_deadline =
                    ay_core::time::Instant::now() + std::time::Duration::from_secs(2);
                self.solve_deadline.set(Some(match saved_deadline {
                    Some(dl) => dl.min(candidate_deadline),
                    None => candidate_deadline,
                }));

                let assumptions = vec![eq_term];
                let result = match self
                    .solve_strings_lia_with_assumptions(&assertions_snapshot, &assumptions)
                {
                    Ok(SolveResult::Sat) => {
                        self.last_result = Some(SolveResult::Sat);
                        match self.finalize_sat_model_validation()? {
                            SolveResult::Sat => {
                                self.finalize_sat_assumption_validation(&assumptions)
                            }
                            other => Ok(other),
                        }
                    }
                    other => other,
                };

                if let Ok(SolveResult::Sat) = result {
                    self.merge_explicit_string_assignments_into_model(&assumptions);
                    // Materialize witnesses for the OTHER string variables at
                    // the OUTER level before accepting. The inner
                    // `finalize_sat_model_validation` above ran with
                    // `pivot_enum_depth > 0`, where
                    // `materialize_string_witnesses` is a guarded no-op — so a
                    // sibling variable constrained only through its `str.len`
                    // LIA proxy (e.g. `(str.prefixof "xyz" s0)` deciding s0 by
                    // witness while `(= (str.len s1) 2)` pins s1's length)
                    // stayed unassigned and the printed model defaulted it to
                    // `""`, violating the length assertion. `ctx.assertions`
                    // was already restored to the outer set by
                    // `with_isolated_incremental_state`, so running the
                    // materializer here at depth 0 completes and strictly
                    // re-validates the full user-level model. On failure the
                    // candidate is REJECTED (loop restores state and tries the
                    // next candidate / falls through to the normal pipeline) —
                    // never accepted with an invalid model.
                    self.pivot_enum_depth -= 1;
                    let full_model_ok = self.materialize_string_witnesses();
                    if full_model_ok {
                        if debug_auflia_enabled() {
                            safe_eprintln!(
                                "[SLIA] prefix/suffix witness: var={:?} candidate {} '{}' → SAT (validated)",
                                witness.var,
                                i,
                                witness.candidates[i]
                            );
                        }
                        self.solve_deadline.set(saved_deadline);
                        return Ok(Some(SolveResult::Sat));
                    }
                    self.pivot_enum_depth += 1;
                    if debug_auflia_enabled() {
                        safe_eprintln!(
                            "[SLIA] prefix/suffix witness: var={:?} candidate {} '{}' rejected — \
                             sibling string vars could not be materialized into a valid model",
                            witness.var,
                            i,
                            witness.candidates[i]
                        );
                    }
                }
            }
            self.pivot_enum_depth -= 1;
        }

        // No witness validated — restore state and fall through.
        self.restore_witness_state(
            saved_deadline,
            &saved_last_model,
            &saved_last_result,
            saved_last_unknown_reason,
            saved_last_model_validated,
            &saved_last_validation_stats,
            &saved_last_assumption_core,
            saved_bypass_taut,
            saved_slia_accepted,
            saved_skip_model_eval,
        );
        Ok(None)
    }

    /// P2 (`AY_STR_P2=1`): guess-and-VALIDATE model search for formulas whose
    /// string variables are constrained only negatively (see
    /// [`Self::detect_negative_only_witnesses`] for the eligibility rules).
    ///
    /// Builds a small set of JOINT concrete assignments over ALL string
    /// variables of the formula:
    ///   - eligible (negative-only) variables get fresh-out-of-alphabet-char
    ///     candidates from the detector (`"c"`, `""`, `"cc"`, `"ccc"`);
    ///   - every other string variable gets the string CONSTANTS it is
    ///     directly equated to anywhere in the formula (either polarity,
    ///     capped) plus `""` — e.g. the pyex `(= key "connection")` idiom
    ///     needs `key = "connection"` in the positive decode and `""` in the
    ///     negative one.
    ///
    /// Each joint assignment is checked by the FULL model-validation battery
    /// (`finalize_sat_model_validation` — the same definitive-evaluation
    /// chokepoint every string SAT passes). SOUNDNESS: a guess is accepted
    /// only when the validated model genuinely satisfies every original
    /// assertion, so no wrong SAT can escape; a failed guess restores the
    /// saved solver state and falls through to the normal pipeline; UNSAT is
    /// NEVER concluded from failed guesses. This pass therefore only finds
    /// models that already exist — it cannot flip any verdict.
    ///
    /// Why guess-and-validate instead of assumption re-solving: the inner
    /// assumption solve runs at `pivot_enum_depth > 0` where every witness
    /// pre-pass is disabled, and the raw CEGAR pipeline latches `incomplete`
    /// on the very negative predicates this pass targets. Direct evaluation
    /// under a TOTAL assignment has no such incompleteness.
    fn try_negative_only_model_guesses(&mut self) -> Result<Option<SolveResult>> {
        const GUESS_CAP: usize = 48;
        const CONST_CANDS_PER_VAR: usize = 3;

        let witnesses = self.detect_negative_only_witnesses();
        if witnesses.is_empty() {
            return Ok(None);
        }

        // Collect ALL string variables of the formula plus, per variable, the
        // string constants it is directly equated to anywhere (any polarity).
        let mut var_order: Vec<TermId> = Vec::new();
        let mut var_seen: HashSet<TermId> = HashSet::default();
        let mut eq_consts: HashMap<TermId, Vec<String>> = HashMap::default();
        {
            let mut stack: Vec<TermId> = self.ctx.assertions.clone();
            let mut visited: HashSet<TermId> = HashSet::default();
            while let Some(t) = stack.pop() {
                if !visited.insert(t) {
                    continue;
                }
                match self.ctx.terms.get(t) {
                    TermData::Var(..) if *self.ctx.terms.sort(t) == Sort::String => {
                        if var_seen.insert(t) {
                            var_order.push(t);
                        }
                    }
                    TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
                        for (a, b) in [(args[0], args[1]), (args[1], args[0])] {
                            if matches!(self.ctx.terms.get(a), TermData::Var(..))
                                && *self.ctx.terms.sort(a) == Sort::String
                            {
                                if let TermData::Const(Constant::String(s)) = self.ctx.terms.get(b)
                                {
                                    let list = eq_consts.entry(a).or_default();
                                    if list.len() < CONST_CANDS_PER_VAR && !list.contains(s) {
                                        list.push(s.clone());
                                    }
                                }
                            }
                        }
                        stack.extend(args.iter().copied());
                    }
                    TermData::App(_, args) => stack.extend(args.iter().copied()),
                    TermData::Not(i) => stack.push(*i),
                    TermData::Ite(c, a, b) => {
                        stack.push(*c);
                        stack.push(*a);
                        stack.push(*b);
                    }
                    TermData::Let(bindings, body) => {
                        for (_, v) in bindings {
                            stack.push(*v);
                        }
                        stack.push(*body);
                    }
                    _ => {}
                }
            }
        }
        var_order.sort_unstable_by_key(|t| t.0);

        // Per-variable candidate lists (joint search space).
        let witness_cands: HashMap<TermId, Vec<String>> = witnesses
            .into_iter()
            .map(|w| (w.var, w.candidates))
            .collect();
        let mut cand_lists: Vec<(TermId, Vec<String>)> = Vec::with_capacity(var_order.len());
        for &v in &var_order {
            let cands = if let Some(c) = witness_cands.get(&v) {
                c.clone()
            } else {
                let mut c = eq_consts.get(&v).cloned().unwrap_or_default();
                if !c.contains(&String::new()) {
                    c.push(String::new());
                }
                c
            };
            cand_lists.push((v, cands));
        }
        if cand_lists.is_empty() {
            return Ok(None);
        }
        // Keep the joint product bounded: bail when it cannot be covered
        // meaningfully (many unconstrained vars still yields 1 combo each).
        let mut combos: usize = 1;
        for (_, c) in &cand_lists {
            combos = combos.saturating_mul(c.len().max(1));
            if combos > GUESS_CAP * 8 {
                return Ok(None);
            }
        }

        // Save every field the validation pipeline mutates, so failed guesses
        // leave no trace (mirrors `try_string_var_witnesses`).
        let saved_last_model = self.last_model.clone();
        let saved_last_result = self.last_result.clone();
        let saved_last_unknown_reason = self.last_unknown_reason;
        let saved_last_model_validated = self.last_model_validated;
        let saved_last_validation_stats = self.last_validation_stats.clone();
        let saved_last_assumption_core = self.last_assumption_core.clone();
        let saved_skip_model_eval = self.skip_model_eval;

        // Odometer over the joint candidate space, capped at GUESS_CAP tries.
        let mut idx = vec![0usize; cand_lists.len()];
        let mut tries = 0usize;
        'outer: loop {
            if tries >= GUESS_CAP || self.should_abort_theory_loop() {
                break;
            }
            tries += 1;

            let mut values: HashMap<TermId, String> = HashMap::default();
            for (slot, (v, cands)) in cand_lists.iter().enumerate() {
                let val = cands.get(idx[slot]).cloned().unwrap_or_default();
                values.insert(*v, val);
            }

            self.last_model = Some(super::super::model::Model {
                sat_model: Vec::new(),
                term_to_var: HashMap::default(),
                bool_overrides: HashMap::default(),
                euf_model: None,
                array_model: None,
                lra_model: None,
                lia_model: None,
                bv_model: None,
                fp_model: None,
                string_model: Some(ay_strings::StringModel { values }),
                seq_model: None,
                completed_values: HashMap::default(),
                dt_ground: HashMap::default(),
                dt_pins: HashMap::default(),
            });
            self.last_result = Some(SolveResult::Sat);
            self.last_model_validated = false;
            match self.finalize_sat_model_validation() {
                Ok(SolveResult::Sat) => {
                    if debug_auflia_enabled() {
                        safe_eprintln!(
                            "[SLIA] P2 negative-only model guess validated on try {tries}"
                        );
                    }
                    return Ok(Some(SolveResult::Sat));
                }
                _ => {
                    // Restore and advance the odometer.
                    self.last_model = saved_last_model.clone();
                    self.last_result = saved_last_result.clone();
                    self.last_unknown_reason = saved_last_unknown_reason;
                    self.last_model_validated = saved_last_model_validated;
                    self.last_validation_stats = saved_last_validation_stats.clone();
                    self.last_assumption_core = saved_last_assumption_core.clone();
                    self.skip_model_eval = saved_skip_model_eval;
                }
            }

            // Advance odometer (least-significant slot first).
            let mut pos = 0usize;
            loop {
                if pos >= cand_lists.len() {
                    break 'outer;
                }
                idx[pos] += 1;
                if idx[pos] < cand_lists[pos].1.len().max(1) {
                    break;
                }
                idx[pos] = 0;
                pos += 1;
            }
        }

        // No guess validated — state already restored; fall through.
        Ok(None)
    }

    /// Restore per-solve executor state mutated by an inner assumption solve.
    /// `pub(super)`: also used by the word-equation pre-pass (sibling module).
    #[allow(clippy::too_many_arguments)]
    pub(super) fn restore_witness_state(
        &mut self,
        deadline: Option<ay_core::time::Instant>,
        last_model: &Option<super::super::model::Model>,
        last_result: &Option<SolveResult>,
        last_unknown_reason: Option<crate::executor_types::UnknownReason>,
        last_model_validated: bool,
        last_validation_stats: &Option<super::super::model::ValidationStats>,
        last_assumption_core: &Option<Vec<TermId>>,
        bypass_taut: bool,
        slia_accepted: bool,
        skip_model_eval: bool,
    ) {
        self.solve_deadline.set(deadline);
        self.last_model = last_model.clone();
        self.last_result = last_result.clone();
        self.last_unknown_reason = last_unknown_reason;
        self.last_model_validated = last_model_validated;
        self.last_validation_stats = last_validation_stats.clone();
        self.last_assumption_core = last_assumption_core.clone();
        self.bypass_string_tautology_guard = bypass_taut;
        self.slia_accepted_unknown = slia_accepted;
        self.skip_model_eval = skip_model_eval;
    }

    /// Build explicit length bound assertion terms from detected bounds.
    ///
    /// For each `LengthBound`, creates:
    /// - `(= (str.len var) N)` when lower == upper (exact length)
    /// - `(>= (str.len var) lower)` when lower > 0 (lower bound only)
    /// - `(<= (str.len var) upper)` (upper bound only)
    ///
    /// These terms are injected as hard assumptions into the inner pivot
    /// enumeration solver to enforce cross-variable length coherence (#7464).
    fn build_length_bound_assertions(
        &mut self,
        bounds: &[super::strings_analysis::LengthBound],
    ) -> Vec<TermId> {
        let mut assertions = Vec::new();
        for bound in bounds {
            let strlen_term =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("str.len"), vec![bound.var], Sort::Int);
            if bound.lower == bound.upper {
                // Exact length: (= (str.len var) N)
                let len_const = self.ctx.terms.mk_int(num_bigint::BigInt::from(bound.lower));
                let eq = self.ctx.terms.mk_eq(strlen_term, len_const);
                assertions.push(eq);
            } else {
                // Range: inject both bounds
                if bound.lower > 0 {
                    let lo_const = self.ctx.terms.mk_int(num_bigint::BigInt::from(bound.lower));
                    let ge = self.ctx.terms.mk_ge(strlen_term, lo_const);
                    assertions.push(ge);
                }
                let hi_const = self.ctx.terms.mk_int(num_bigint::BigInt::from(bound.upper));
                let le = self.ctx.terms.mk_le(strlen_term, hi_const);
                assertions.push(le);
            }
        }
        assertions
    }

    fn model_respects_detected_string_bounds(
        &self,
        bounds: &[super::strings_analysis::LengthBound],
        assumptions: &[TermId],
    ) -> bool {
        if bounds.is_empty() {
            return true;
        }

        let mut observed_values = self
            .last_model
            .as_ref()
            .and_then(|model| model.string_model.as_ref())
            .map(|string_model| string_model.values.clone())
            .unwrap_or_default();
        observed_values.extend(self.explicit_string_assignments(assumptions));

        bounds.iter().all(|bound| {
            observed_values.get(&bound.var).is_none_or(|value| {
                let len = value.chars().count();
                len >= bound.lower && len <= bound.upper
            })
        })
    }

    pub(super) fn merge_explicit_string_assignments_into_model(&mut self, assertions: &[TermId]) {
        let assignments = self.explicit_string_assignments(assertions);
        if assignments.is_empty() {
            return;
        }

        if let Some(model) = self.last_model.as_mut() {
            let string_model = model
                .string_model
                .get_or_insert_with(ay_strings::StringModel::default);
            string_model.values.extend(assignments);
        }
    }

    /// Solve QF_SLIA using combined Strings + EUF + LIA theory.
    ///
    /// Injects str.len axioms (non-negativity, zero-length ↔ empty string,
    /// concat length decomposition) as additional assertions, then runs
    /// the `StringsLiaSolver` combined theory with branch-and-bound for
    /// integer arithmetic.
    /// Collect `(= (str.to_int t) -1)` axioms for every `(str.to_int t)` term
    /// (reachable from the assertions) whose argument is PROVABLY non-numeric:
    /// a non-digit string literal, or a `str.++` concat with a literal operand
    /// that contains a non-digit character. Such a string can never denote a
    /// digit sequence, so `str.to_int` is `-1` (SMT-LIB). Sound — it only states
    /// a fact that holds in every model. (#bug22 wrong-sat)
    pub(in crate::executor) fn collect_str_to_int_nonnumeric_axioms(&mut self) -> Vec<TermId> {
        let mut to_int_terms: Vec<TermId> = Vec::new();
        let mut seen: HashSet<TermId> = HashSet::default();
        let assertions = self.ctx.assertions.clone();
        for &a in &assertions {
            self.collect_nonnumeric_str_to_int_terms(a, &mut to_int_terms, &mut seen);
        }
        to_int_terms.sort_unstable_by_key(|t| t.0);
        to_int_terms.dedup();
        let neg_one = self.ctx.terms.mk_int(num_bigint::BigInt::from(-1));
        to_int_terms
            .into_iter()
            .map(|t| self.ctx.terms.mk_eq(t, neg_one))
            .collect()
    }

    /// Walk `term`, collecting every `(str.to_int arg)` whose `arg` is provably
    /// non-numeric (`str_arg_forces_nonnumeric`).
    fn collect_nonnumeric_str_to_int_terms(
        &self,
        term: TermId,
        out: &mut Vec<TermId>,
        seen: &mut HashSet<TermId>,
    ) {
        if !seen.insert(term) {
            return;
        }
        match self.ctx.terms.get(term).clone() {
            TermData::App(sym, args) => {
                if (sym.name() == "str.to_int" || sym.name() == "str.to.int")
                    && args.len() == 1
                    && self.str_arg_forces_nonnumeric(args[0])
                {
                    out.push(term);
                }
                for arg in args {
                    self.collect_nonnumeric_str_to_int_terms(arg, out, seen);
                }
            }
            TermData::Not(inner) => self.collect_nonnumeric_str_to_int_terms(inner, out, seen),
            TermData::Ite(c, t, e) => {
                self.collect_nonnumeric_str_to_int_terms(c, out, seen);
                self.collect_nonnumeric_str_to_int_terms(t, out, seen);
                self.collect_nonnumeric_str_to_int_terms(e, out, seen);
            }
            _ => {}
        }
    }

    /// True when `t` provably denotes a NON-numeric string (so `str.to_int` is
    /// `-1`): a non-digit / empty string literal, or a `str.++` with a literal
    /// operand containing a non-digit character (which is preserved into the
    /// result regardless of the other, possibly symbolic, operands).
    fn str_arg_forces_nonnumeric(&self, t: TermId) -> bool {
        let literal_has_nondigit = |s: &str| -> bool { s.chars().any(|c| !c.is_ascii_digit()) };
        match self.ctx.terms.get(t) {
            TermData::Const(Constant::String(s)) => s.is_empty() || literal_has_nondigit(s),
            TermData::App(sym, args) if sym.name() == "str.++" => args.iter().any(|&a| {
                matches!(self.ctx.terms.get(a),
                    TermData::Const(Constant::String(s)) if literal_has_nondigit(s))
            }),
            // `str.replace x "" r` = `r ++ x` (the empty pattern always matches
            // at position 0, so `r` is always inserted), hence non-numeric when
            // `r` is a literal containing a non-digit. (A non-empty pattern may
            // not occur, so only the empty-pattern case is unconditional.)
            TermData::App(sym, args) if sym.name() == "str.replace" && args.len() == 3 => {
                matches!(self.ctx.terms.get(args[1]),
                    TermData::Const(Constant::String(p)) if p.is_empty())
                    && matches!(self.ctx.terms.get(args[2]),
                        TermData::Const(Constant::String(r)) if literal_has_nondigit(r))
            }
            _ => false,
        }
    }

    /// A1 — `str.to_int` digit pinning. For a string term `x` constrained by
    /// BOTH a constant `(= (str.to_int x) K)` and a constant `(= (str.len x) L)`,
    /// SMT-LIB fixes `x` uniquely: `to_int(x)=K>=0 ∧ len(x)=L` holds iff `x` is
    /// `decimal(K)` left-padded with `'0'` to length `L`, and is UNSAT when `K`
    /// has more than `L` decimal digits (z3-confirmed zt0/zt1/zt2b/zt7/zlen0;
    /// control m4 stays sat). Both are VALID theorems, so emitting them can only
    /// enable correct UNSATs, never flip a genuine SAT. Guarded by the two source
    /// atoms so it is sound even when they appear nested (not top-level true):
    ///   - `numdigits(K) <= L`: `(=> (and atomK atomL) (= x zeropad(K,L)))`
    ///   - `numdigits(K)  > L`: `(not (and atomK atomL))`
    /// `K < 0` is skipped (K=-1 is the empty/non-numeric witness case; K<-1 is
    /// already refuted by the `to_int >= -1` range axiom). `L > 10_000` is skipped
    /// (allocation guard; sound fall-through to unknown).
    pub(in crate::executor) fn collect_str_to_int_digit_pin_axioms(&mut self) -> Vec<TermId> {
        const PAIR_CAP: usize = 256;
        const MAX_LEN: i64 = 10_000;
        let mut toint_atoms: Vec<(TermId, num_bigint::BigInt, TermId)> = Vec::new();
        let mut len_atoms: Vec<(TermId, i64, TermId)> = Vec::new();
        let mut seen: HashSet<TermId> = HashSet::default();
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            match self.ctx.terms.get(t).clone() {
                TermData::App(sym, args) => {
                    if sym.name() == "=" && args.len() == 2 {
                        // Try both operand orders; a `(= <op> <const>)` atom.
                        for (a, b) in [(args[0], args[1]), (args[1], args[0])] {
                            if let TermData::App(inner, iargs) = self.ctx.terms.get(a).clone() {
                                if iargs.len() != 1 {
                                    continue;
                                }
                                let iname = inner.name();
                                if iname == "str.to_int" || iname == "str.to.int" {
                                    if let TermData::Const(Constant::Int(k)) = self.ctx.terms.get(b)
                                    {
                                        if toint_atoms.len() < PAIR_CAP {
                                            toint_atoms.push((iargs[0], k.clone(), t));
                                        }
                                    }
                                } else if iname == "str.len" {
                                    if let TermData::Const(Constant::Int(l)) = self.ctx.terms.get(b)
                                    {
                                        if let Ok(lv) = i64::try_from(l) {
                                            if lv >= 0 && len_atoms.len() < PAIR_CAP {
                                                len_atoms.push((iargs[0], lv, t));
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                    for &a in &args {
                        stack.push(a);
                    }
                }
                TermData::Not(inner) => stack.push(inner),
                TermData::Ite(c, th, el) => {
                    stack.push(c);
                    stack.push(th);
                    stack.push(el);
                }
                TermData::Let(bindings, body) => {
                    for (_, v) in &bindings {
                        stack.push(*v);
                    }
                    stack.push(body);
                }
                _ => {}
            }
        }
        let zero = num_bigint::BigInt::from(0);
        let mut axioms: Vec<TermId> = Vec::new();
        for (x, k, atom_k) in &toint_atoms {
            if *k < zero {
                continue; // K<0 handled by the range axiom / witness pass
            }
            let digits = k.to_string(); // K>=0 => no sign; 0 => "0" (numdigits(0)=1)
            for (lx, l, atom_l) in &len_atoms {
                if lx != x || *l > MAX_LEN {
                    continue;
                }
                let l_usize = *l as usize;
                let prem = self.ctx.terms.mk_and(vec![*atom_k, *atom_l]);
                if digits.len() > l_usize {
                    // numdigits(K) > L: the pair is unsatisfiable.
                    axioms.push(self.ctx.terms.mk_not(prem));
                } else {
                    let pad = l_usize - digits.len();
                    let mut s = String::with_capacity(l_usize);
                    for _ in 0..pad {
                        s.push('0');
                    }
                    s.push_str(&digits);
                    let lit = self.ctx.terms.mk_string(s);
                    let eq = self.ctx.terms.mk_eq(*x, lit);
                    axioms.push(self.ctx.terms.mk_implies(prem, eq));
                }
            }
        }
        axioms
    }

    /// A2 — `str.to_code` constant inversion. For each atom
    /// `(= (str.to_code x) K)` with a constant `K ∈ [0, 196607]`, the codepoint
    /// value uniquely determines the single-character string, so emit
    /// `(=> atom (= x char(K)))` — a VALID theorem by injectivity of codepoints
    /// (z3-confirmed g2a/zt5; control g2ctl stays sat). `K` outside `[0,196607]`
    /// is already handled by the existing `to_code ∈ [-1,196607]` range axiom.
    /// SURROGATE guard: `K ∈ [0xD800, 0xDFFF]` has no Rust `char`, so it is
    /// skipped (sound fall-through to unknown; z3 reports such K as sat — a
    /// completeness, not soundness, gap).
    pub(in crate::executor) fn collect_str_to_code_inversion_axioms(&mut self) -> Vec<TermId> {
        const PAIR_CAP: usize = 256;
        let mut atoms: Vec<(TermId, i64, TermId)> = Vec::new();
        let mut seen: HashSet<TermId> = HashSet::default();
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            match self.ctx.terms.get(t).clone() {
                TermData::App(sym, args) => {
                    if sym.name() == "=" && args.len() == 2 {
                        for (a, b) in [(args[0], args[1]), (args[1], args[0])] {
                            if let TermData::App(inner, iargs) = self.ctx.terms.get(a).clone() {
                                if iargs.len() == 1
                                    && (inner.name() == "str.to_code"
                                        || inner.name() == "str.to.code")
                                {
                                    if let TermData::Const(Constant::Int(k)) = self.ctx.terms.get(b)
                                    {
                                        if let Ok(kv) = i64::try_from(k) {
                                            if atoms.len() < PAIR_CAP {
                                                atoms.push((iargs[0], kv, t));
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                    for &a in &args {
                        stack.push(a);
                    }
                }
                TermData::Not(inner) => stack.push(inner),
                TermData::Ite(c, th, el) => {
                    stack.push(c);
                    stack.push(th);
                    stack.push(el);
                }
                TermData::Let(bindings, body) => {
                    for (_, v) in &bindings {
                        stack.push(*v);
                    }
                    stack.push(body);
                }
                _ => {}
            }
        }
        let mut axioms: Vec<TermId> = Vec::new();
        for (x, k, atom) in atoms {
            if !(0..=196_607).contains(&k) {
                continue; // out-of-range: refuted by the to_code range axiom
            }
            // char::from_u32 returns None for surrogates [0xD800,0xDFFF] and for
            // out-of-Unicode values — surrogate case fail-closes to unknown.
            let Some(ch) = u32::try_from(k).ok().and_then(char::from_u32) else {
                continue;
            };
            let lit = self.ctx.terms.mk_string(ch.to_string());
            let eq = self.ctx.terms.mk_eq(x, lit);
            axioms.push(self.ctx.terms.mk_implies(atom, eq));
        }
        axioms
    }

    /// Collect `(= (str.indexof s n i) -1)` for every `str.indexof` whose
    /// haystack `s` and needle `n` both resolve to concrete string constants and
    /// where the (non-empty) needle is NOT a substring of the haystack
    /// (#str-indexof-absent-needle).
    ///
    /// Sound for EVERY offset `i`: a needle absent from the haystack has no
    /// occurrence at any position, so `str.indexof` is `-1` independent of where
    /// the search starts. This is a logical consequence (it only ADDS a forced
    /// equality and can never refute a real model), so it can at worst turn a
    /// spurious SAT into a sound verdict — never a wrong UNSAT.
    ///
    /// The empty needle is excluded: `(str.indexof s "" i)` is `i` (clamped),
    /// not `-1`, so the absence shortcut does not apply.
    pub(in crate::executor) fn collect_str_indexof_absent_needle_axioms(&mut self) -> Vec<TermId> {
        // Map every term fixed to a single string constant by the top-level
        // equality closure to that concrete value. Built by union-find over the
        // string-equality graph (the same closure `collect_top_level_ground_string_terms`
        // computes), so a variable reachable to a literal only through a chain of
        // variable=variable edges (e.g. `(= v "cba") (= v t)` ⊢ `t = "cba"`) is
        // resolved. A component with conflicting literals is dropped (unsat by
        // those equalities; we never emit on it).
        let mut value_map: HashMap<TermId, String> = HashMap::default();
        {
            let mut eq_graph: HashMap<TermId, Vec<TermId>> = HashMap::default();
            let mut eq_nodes: HashSet<TermId> = HashSet::default();
            let mut stack: Vec<TermId> = self.ctx.assertions.clone();
            while let Some(term) = stack.pop() {
                match self.ctx.terms.get(term).clone() {
                    TermData::App(Symbol::Named(name), args) if name == "and" => {
                        for arg in args {
                            stack.push(arg);
                        }
                    }
                    TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
                        let (l, r) = (args[0], args[1]);
                        if *self.ctx.terms.sort(l) == Sort::String
                            && *self.ctx.terms.sort(r) == Sort::String
                        {
                            eq_graph.entry(l).or_default().push(r);
                            eq_graph.entry(r).or_default().push(l);
                            eq_nodes.insert(l);
                            eq_nodes.insert(r);
                        }
                    }
                    _ => {}
                }
            }
            let mut visited: HashSet<TermId> = HashSet::default();
            for &root in &eq_nodes {
                if !visited.insert(root) {
                    continue;
                }
                let mut component = Vec::new();
                let mut cstack = vec![root];
                let mut unique_constant: Option<String> = None;
                let mut conflicting = false;
                while let Some(cur) = cstack.pop() {
                    component.push(cur);
                    if let TermData::Const(Constant::String(s)) = self.ctx.terms.get(cur) {
                        match &unique_constant {
                            Some(existing) if existing != s => conflicting = true,
                            None => unique_constant = Some(s.clone()),
                            _ => {}
                        }
                    }
                    if let Some(neighbors) = eq_graph.get(&cur) {
                        for &next in neighbors {
                            if visited.insert(next) {
                                cstack.push(next);
                            }
                        }
                    }
                }
                if let (Some(val), false) = (unique_constant, conflicting) {
                    for t in component {
                        value_map.insert(t, val.clone());
                    }
                }
            }
        }

        // Resolve a string term to its concrete value when determined: a literal
        // resolves to itself; any term in a single-constant equality component
        // resolves to that constant.
        let resolve = |exec: &Executor, t: TermId| -> Option<String> {
            match exec.ctx.terms.get(t) {
                TermData::Const(Constant::String(s)) => Some(s.clone()),
                _ => value_map.get(&t).cloned(),
            }
        };

        // Collect every str.indexof term, plus every `(str.from_int X)`
        // term (indexed by its argument), reachable from the assertions.
        let mut indexofs: Vec<(TermId, TermId, TermId)> = Vec::new();
        let mut from_int_of: HashMap<TermId, Vec<TermId>> = HashMap::default();
        let mut seen: HashSet<TermId> = HashSet::default();
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }
            match self.ctx.terms.get(term).clone() {
                TermData::App(sym, args) => {
                    if sym.name() == "str.indexof" && args.len() == 3 && seen.insert(term) {
                        indexofs.push((term, args[0], args[1]));
                    } else if sym.name() == "str.from_int" && args.len() == 1 {
                        from_int_of.entry(args[0]).or_default().push(term);
                    }
                    for arg in args {
                        stack.push(arg);
                    }
                }
                TermData::Not(inner) => stack.push(inner),
                TermData::Ite(c, t, e) => {
                    stack.push(c);
                    stack.push(t);
                    stack.push(e);
                }
                TermData::Let(bindings, body) => {
                    for (_, v) in bindings {
                        stack.push(v);
                    }
                    stack.push(body);
                }
                _ => {}
            }
        }

        let neg_one = self.ctx.terms.mk_int(num_bigint::BigInt::from(-1));
        let empty_str = self.ctx.terms.mk_string(String::new());
        let mut axioms = Vec::new();
        for (idx_term, s, n) in indexofs {
            let (Some(hay), Some(needle)) = (resolve(self, s), resolve(self, n)) else {
                continue;
            };
            // Empty needle is matched at every position (result is the offset,
            // not -1) — the absence shortcut does not apply.
            if needle.is_empty() {
                continue;
            }
            if !hay.contains(needle.as_str()) {
                axioms.push(self.ctx.terms.mk_eq(idx_term, neg_one));
                // Bridge the determined `-1` through any `(str.from_int idx)`
                // consumer: `str.from_int` of a negative integer is the empty
                // string `""` (SMT-LIB), and `idx = -1 < 0` here. The combined
                // string/EUF/LIA solver does not substitute the LIA-determined
                // value back into the opaque `str.from_int` term, so without this
                // bridge a consumer like `(str.is_digit (str.from_int idx))`
                // stays a free Boolean and the instance is spuriously SAT. Sound:
                // `(= (str.from_int idx) "")` is a logical consequence of
                // `idx = -1` and only ADDS a forced equality.
                if let Some(consumers) = from_int_of.get(&idx_term) {
                    for &fi in consumers {
                        axioms.push(self.ctx.terms.mk_eq(fi, empty_str));
                    }
                }
            }
        }
        axioms
    }

    pub(in crate::executor) fn solve_strings_lia(&mut self) -> Result<SolveResult> {
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }
        // Closure 5 bookkeeping is per-solve: a previous solve's
        // context-dependent lemma must not disqualify this one, and vice
        // versa. Reset before any lemma of this solve is lowered.
        self.string_lemma_kinds_all_valid = true;

        if debug_auflia_enabled() {
            safe_eprintln!(
                "[SLIA] === solve_strings_lia ENTER depth={} ===",
                self.pivot_enum_depth
            );
        }
        // Constant-fold ground string operations (#4057 design). When all
        // arguments to a string op are constants (e.g., str.substr("hello",1,3)),
        // evaluate eagerly and replace with the result. This eliminates ground
        // computation from the formula before routing to QF_S or SLIA pipeline.
        {
            let _original_len = self.ctx.assertions.len();
            let folded = self.fold_ground_string_ops(&self.ctx.assertions.clone());
            // Early UNSAT: if any assertion folds to false
            if folded.iter().any(|&t| {
                matches!(
                    self.ctx.terms.get(t),
                    TermData::Const(Constant::Bool(false))
                )
            }) {
                return Ok(SolveResult::unsat());
            }
            // Remove trivially-true assertions
            let non_trivial: Vec<TermId> = folded
                .iter()
                .copied()
                .filter(|&t| {
                    !matches!(self.ctx.terms.get(t), TermData::Const(Constant::Bool(true)))
                })
                .collect();
            // Early SAT: all assertions folded to true. Mark as validated
            // (not skip_model_eval) so finalize_sat_model_validation is not
            // called and the postcondition in check_sat is satisfied (#8456).
            if non_trivial.is_empty() {
                self.last_model = Some(super::super::model::Model {
                    sat_model: Vec::new(),
                    term_to_var: HashMap::default(),
                    bool_overrides: HashMap::default(),
                    euf_model: None,
                    array_model: None,
                    lra_model: None,
                    lia_model: None,
                    bv_model: None,
                    fp_model: None,
                    string_model: None,
                    seq_model: None,
                    completed_values: HashMap::default(),
                    dt_ground: HashMap::default(),
                    dt_pins: HashMap::default(),
                });
                self.last_model_validated = true;
                return Ok(SolveResult::Sat);
            }
            self.ctx.assertions = non_trivial;
        }

        if self.has_exact_string_length_contradiction(&self.ctx.assertions) {
            return Ok(SolveResult::unsat());
        }

        // Concat-needle contains/prefix/suffix refutation (#str-concat-needle):
        // a positively-asserted `str.contains`/`str.prefixof`/`str.suffixof`
        // over a constant haystack whose pattern is a `str.++` with constant
        // leaves too long for, or absent from, the haystack is structurally
        // UNSAT regardless of the free leaves. Decide it precisely here rather
        // than relying on the fail-closed model-validation fallback.
        if self.has_unsatisfiable_positive_concat_predicate(&self.ctx.assertions) {
            return Ok(SolveResult::unsat());
        }

        // Soundness guard (#3598): if the user assertions contain no arithmetic
        // constraints and no string-int bridge operators, solve via the pure
        // string path even under QF_SLIA.
        //
        // Many benchmarks declare QF_SLIA but are purely string equations.
        // Routing those to the SLIA pipeline can introduce false UNSAT from
        // arithmetic-side interactions that are irrelevant to the formula.
        let needs_slia = self.ctx.assertions.iter().any(|&a| {
            crate::term_helpers::contains_arithmetic_ops(&self.ctx.terms, a)
                || crate::term_helpers::contains_string_ops(&self.ctx.terms, a)
        });
        if !needs_slia {
            // LANE SELECTION, traced: a QF_SLIA-declared window with no
            // arithmetic and no string→Int bridge is handed to the PURE-STRING
            // lane, which runs a SHORTER witness cascade than this one (no
            // pinned-length placement, no P2, no replace_all, no pivot
            // enumeration). A file that emits no `[W4]`/`[W6]`/`[W7]` line
            // under `--debug auflia` while declaring QF_SLIA is almost always
            // here, not on some third path. See `solve_strings`.
            if debug_auflia_enabled() {
                safe_eprintln!(
                    "[SLIA] lane: pure-string window ({} assertion(s), no arith / no str-int bridge) -> QF_S lane",
                    self.ctx.assertions.len()
                );
            }
            return self.solve_strings();
        }

        // The equation subset is sound independently of the arithmetic atoms.
        // Keep this exact refutation before the SLIA witness cascade; resource
        // limits, proof mode, and re-entrant solves all fail open internally.
        if self.pivot_enum_depth == 0 {
            if let Some(result) = self.try_word_eq_constant_propagation()? {
                return Ok(result);
            }
        }

        // Prefix/suffix witness pre-pass.
        //
        // A variable constrained only by `str.prefixof(p, z)` and
        // `str.suffixof(s, z)` (constant p, s) with no upper length bound is
        // unbounded, so pivot enumeration cannot fire and the unguided CEGAR
        // loop stalls (it repeatedly guesses z = p, which is too short). The
        // minimal models are the overlap-merges of p and s. We *try* each merge
        // as a hard assumption and only trust SAT after full model validation,
        // so a wrong guess is harmless (falls through to the normal pipeline).
        if self.pivot_enum_depth == 0 {
            if let Some(result) = self.try_prefix_suffix_witnesses()? {
                return Ok(result);
            }
        }

        // Positive contains/prefixof/suffixof over a partially-grounded concat
        // witness pre-pass (QF_SLIA completeness). When a positive
        // `str.contains`/`str.prefixof`/`str.suffixof` over `(str.++ ... )`
        // cannot be ground-evaluated, construct a concrete witness for the free
        // component(s) that makes the predicate true (e.g. set the free operand
        // to the needle, or to the boundary-spanning remainder). Each witness is
        // tried as a hard assumption and only trusted after full model
        // validation, so a wrong guess falls through to the normal pipeline and
        // genuinely-UNSAT cases stay UNSAT. Only positive predicates are
        // eligible — negations never trigger witness construction.
        if self.pivot_enum_depth == 0 {
            if let Some(result) = self.try_concat_predicate_witnesses()? {
                return Ok(result);
            }
        }

        // #ssl-residue B: pinned-length placement witness pre-pass. When
        // `(= (str.len x) N)` pins a concrete length and positional anchors
        // (substr-window equality, indexof-at-0 equality, positive contains)
        // constrain `x`, enumerate the O(N × #anchors) placement fillings and
        // try each as a hard assumption. SAT is accepted ONLY after full model
        // validation, so a wrong guess falls through to the normal pipeline
        // and UNSAT is unaffected.
        if self.pivot_enum_depth == 0 {
            let placement_witnesses = self.detect_pinned_length_placement_witnesses();
            if let Some(result) = self.try_string_var_witnesses(placement_witnesses)? {
                return Ok(result);
            }
        }

        // P2 (`AY_STR_P2=1`): negative-only constrained variable model-guess
        // pre-pass. A variable whose polarity-decoded content constraints are
        // all NEGATIVE (`¬contains(x, c)`, `x != c`, `substr-of-x != c`, plus
        // length atoms) has trivial models over a character outside the
        // formula alphabet, but the unguided loop latches `incomplete` on the
        // unresolved negative predicates (pyex/Reynolds CAV'17 idiom).
        // Candidate JOINT assignments are checked directly by the full
        // model-validation battery — SAT can only escape validated, and a
        // failed guess restores state and falls through, so soundness is
        // unaffected (UNSAT is never concluded here).
        if self.pivot_enum_depth == 0 && super::strings_preregister::str_p2_enabled() {
            if let Some(result) = self.try_negative_only_model_guesses()? {
                return Ok(result);
            }
        }

        // W4 (default ON, `AY_STR_W4=0` kill switch): length-indexed PER-POSITION
        // character witness synthesizer — the measured RANK-1 sat-side lever
        // (70 of the 92 sat misses are the per-position family, and 58 of them
        // never build a model at all, so every model-construction path is
        // unreachable for them). Runs the forced-literal closure, derives each
        // variable's length, intersects the per-position character
        // pins/exclusions by concrete evaluation, and repairs a JOINT
        // assignment over all coupled variables. Every candidate rides the
        // existing gates unchanged (full model-validation battery, then a
        // pinned-assumption re-solve with model + assumption + materializer
        // validation); a failed synthesis falls through and NEVER concludes
        // UNSAT. See `strings_w4.rs`.
        if self.pivot_enum_depth == 0 && super::strings_w4::str_w4_enabled() {
            if let Some(result) = self.try_per_position_witnesses()? {
                return Ok(result);
            }
        }

        // Ground replace_all inverse-image witness pre-pass (extf wave 2).
        // `(= (str.replace_all v t u) c)` with ground t/u/c and a bare
        // variable haystack: try `v = replace_all(c, u, t)` and `v = c` as
        // hard assumptions with full model validation. The one-step
        // ReplaceAllReduction CEGAR recursion handles the general case but
        // can burn its unroll budget diving the contains-branch first; this
        // decides the common ground-result shape directly. Wrong guesses
        // fall through to the normal pipeline (never wrong, never UNSAT
        // from a failed candidate).
        if self.pivot_enum_depth == 0 {
            let replace_all_witnesses = self.detect_replace_all_witnesses();
            if let Some(result) = self.try_string_var_witnesses(replace_all_witnesses)? {
                return Ok(result);
            }
        }

        // Bounded regex-membership × length decision (TARGET strings_regex_len).
        // A string variable constrained by `(str.in_re x R)` together with a
        // derivable finite length window has a finite, enumerable solution set
        // over the regex's accepted alphabet. Decide UNSAT (no accepted string
        // of the required length) or SAT (validated concrete witness). Fails
        // closed to fall-through otherwise — never wrong.
        if self.pivot_enum_depth == 0 {
            if let Some(result) = self.try_regex_length_witnesses()? {
                return Ok(result);
            }
        }

        // Concat-equals-constant single-free-variable witness (TARGET
        // strings_regex_len S2): `(str.++ x "b") = "aab"` ⇒ x = "aa". The derived
        // value is fully model-validated before SAT is trusted.
        if self.pivot_enum_depth == 0 {
            if let Some(result) = self.try_concat_constant_witnesses()? {
                return Ok(result);
            }
        }

        // Nielsen word-equation decision (Track A3 M1): symbolic word
        // equations like `x ++ "ab" = "a" ++ y`, with exact `str.len`
        // facts as pruning. SAT only after full model validation; UNSAT
        // only from exhaustive Nielsen closure of the equation subset.
        if self.pivot_enum_depth == 0 {
            if let Some(result) = self.try_word_equation_nielsen()? {
                return Ok(result);
            }
        }

        // W1b for the variables whose derivative search converges within a
        // cheap work budget — after the exact UNSAT deciders, before W6.
        if self.pivot_enum_depth == 0 {
            if let Some(result) = self.try_regex_construct_witnesses_cheap()? {
                return Ok(result);
            }
        }

        // W1b regex witness CONSTRUCTION (split out of the regex×length
        // pre-pass so it runs after every EXACT pass). It only produces SAT
        // candidates, so charging its derivative product search to formulas
        // the exact passes already decide is pure overhead; the candidates,
        // the pinning and the full model validation are unchanged.
        if self.pivot_enum_depth == 0 {
            if let Some(result) = self.try_regex_construct_witnesses()? {
                return Ok(result);
            }
        }

        // W6 (default ON, `AY_STR_W6=0` kill switch): regex-driven joint word
        // construction — the LAST witness pre-pass, deliberately.
        //
        // The per-position synthesizer's targeting gate declines
        // regex+length-only formulas (that class belongs to S1/W1b/W2), so this
        // is a SEPARATE pre-pass rather than a relaxation of that gate: every
        // variable is assigned a word of its own membership language and the
        // JOINT assignment is validated by the same full battery. A rejected
        // candidate restores state and falls through; UNSAT is never concluded.
        //
        // It runs LAST because its candidates can be hundreds of characters
        // long and validating one against an industrial regex chain is not
        // cheap: placed earlier it spent the budget of files the passes below
        // already decide (measured: `regexlengths/regex-lengths-00276-28`
        // sat -> unknown). Only formulas nothing else decides reach it.
        // See `strings_w6.rs`.
        if self.pivot_enum_depth == 0 && super::strings_w6::str_w6_enabled() {
            if let Some(result) = self.try_regex_word_witnesses()? {
                return Ok(result);
            }
        }

        // W7 (default ON, `AY_STR_W7=0` kill switch): chain-definition search, multi-atom
        // placement search, and the distinct-witness enumerator — the LAST
        // witness pre-pass, with its own budget.
        //
        // Ordering is load-bearing, not cosmetic: W6 measured that running a
        // later pass's moves BEFORE an earlier pass's cost 24 pyex
        // `httplib2-entry-disposition` conversions outright, by displacing the
        // earlier candidates on ties and exhausting the solve budget. W7 is
        // therefore appended after every other witness pass, and only formulas
        // nothing else decides ever reach it. See `strings_w7.rs`.
        if self.pivot_enum_depth == 0 && super::strings_w7::str_w7_enabled() {
            if let Some(result) = self.try_w7_witnesses()? {
                return Ok(result);
            }
        }

        // Pivot-bounded word equation pre-pass (#3826).
        //
        // For benchmarks with a short bounded string variable (e.g., len(A) <= 2),
        // enumerate candidate values for that variable and try each as an extra
        // assertion. This converts an expensive CEGAR loop with many NeedStringLemma
        // rounds into a small bounded search over concrete variable assignments.
        //
        // The re-entry guard prevents infinite recursion when the inner call
        // to solve_strings_lia triggers pivot detection again.
        if self.pivot_enum_depth == 0 {
            let pivot_bounds = self.detect_bounded_string_vars();
            // Multi-variable bounded formulas are handled by injecting ALL
            // detected length bounds as hard assumptions into the inner solver
            // (#7464). This ensures cross-variable length coherence — the inner
            // solver cannot produce a model that satisfies one variable's
            // candidate while violating another variable's length constraint.
            if !pivot_bounds.is_empty() {
                if let Some(pivot) = pivot_bounds
                    .iter()
                    .min_by_key(|b| b.upper.saturating_sub(b.lower))
                {
                    let alphabet = self.collect_alphabet();
                    if !alphabet.is_empty() {
                        let (candidates, candidates_exhaustive) =
                            Self::generate_candidates(&alphabet, pivot.lower, pivot.upper);
                        if !candidates.is_empty() && candidates.len() <= MAX_PIVOT_CANDIDATES {
                            let pivot_var = pivot.var;
                            if debug_auflia_enabled() {
                                safe_eprintln!(
                                    "[SLIA] Pivot enum: var={:?}, len=[{}..={}], {} candidates",
                                    pivot_var,
                                    pivot.lower,
                                    pivot.upper,
                                    candidates.len()
                                );
                            }
                            // Pre-create equality terms for all candidates (before DpllT borrow).
                            let candidate_eqs: Vec<TermId> = candidates
                                .iter()
                                .map(|s| {
                                    let str_term = self.ctx.terms.mk_string(s.clone());
                                    self.ctx.terms.mk_eq(pivot_var, str_term)
                                })
                                .collect();

                            // Build explicit length bound assertions for ALL
                            // bounded variables (#7464). The inner solver's
                            // CEGAR loop may terminate early without enforcing
                            // cross-variable length coherence. Injecting these
                            // as hard assumptions ensures every candidate solve
                            // respects all detected length bounds, preventing
                            // false SAT on multi-variable formulas.
                            let length_bound_assumptions =
                                self.build_length_bound_assertions(&pivot_bounds);

                            self.pivot_enum_depth += 1;
                            // Budget: 2 seconds per candidate, but respect any
                            // existing deadline from the API layer.
                            let saved_deadline = self.solve_deadline.get();
                            let assertions_snapshot = self.ctx.assertions.clone();
                            let mut all_unsat = true;

                            // Save executor state that may be corrupted between
                            // pivot candidate iterations (#7464). Each inner
                            // solve_strings_lia_with_assumptions call mutates
                            // model, result, and per-solve flags. Without
                            // save/restore, a failed candidate's state leaks
                            // into subsequent candidates, causing false UNSAT
                            // or Unknown on formulas that should be SAT.
                            let saved_last_model = self.last_model.clone();
                            let saved_last_result = self.last_result.clone();
                            let saved_last_unknown_reason = self.last_unknown_reason;
                            let saved_last_model_validated = self.last_model_validated;
                            let saved_last_validation_stats = self.last_validation_stats.clone();
                            let saved_last_assumption_core = self.last_assumption_core.clone();
                            let saved_bypass_taut = self.bypass_string_tautology_guard;
                            let saved_slia_accepted = self.slia_accepted_unknown;
                            let saved_skip_model_eval = self.skip_model_eval;

                            for (i, &eq_term) in candidate_eqs.iter().enumerate() {
                                if self.should_abort_theory_loop() {
                                    self.pivot_enum_depth -= 1;
                                    self.solve_deadline.set(saved_deadline);
                                    // Restore state on abort.
                                    self.last_model = saved_last_model;
                                    self.last_result = saved_last_result;
                                    self.last_unknown_reason = saved_last_unknown_reason;
                                    self.last_model_validated = saved_last_model_validated;
                                    self.last_validation_stats = saved_last_validation_stats;
                                    self.last_assumption_core = saved_last_assumption_core;
                                    self.bypass_string_tautology_guard = saved_bypass_taut;
                                    self.slia_accepted_unknown = saved_slia_accepted;
                                    self.skip_model_eval = saved_skip_model_eval;
                                    return Ok(SolveResult::Unknown);
                                }

                                // Restore per-solve state before each candidate
                                // (#7464) to prevent state corruption between
                                // iterations. The inner solver mutates these
                                // fields; without restoration a prior candidate's
                                // UNSAT/Unknown state poisons the next one.
                                self.last_model = saved_last_model.clone();
                                self.last_result = saved_last_result.clone();
                                self.last_unknown_reason = saved_last_unknown_reason;
                                self.last_model_validated = saved_last_model_validated;
                                self.last_validation_stats = saved_last_validation_stats.clone();
                                self.last_assumption_core = saved_last_assumption_core.clone();
                                self.bypass_string_tautology_guard = saved_bypass_taut;
                                self.slia_accepted_unknown = saved_slia_accepted;
                                self.skip_model_eval = saved_skip_model_eval;

                                // Set per-candidate deadline: min(2s from now, existing deadline).
                                let candidate_deadline = ay_core::time::Instant::now()
                                    + std::time::Duration::from_secs(2);
                                self.solve_deadline.set(Some(match saved_deadline {
                                    Some(dl) => dl.min(candidate_deadline),
                                    None => candidate_deadline,
                                }));
                                // Combine pivot candidate with all length
                                // bound constraints so the inner solver sees
                                // every cross-variable length requirement.
                                let mut assumptions =
                                    Vec::with_capacity(1 + length_bound_assumptions.len());
                                assumptions.push(eq_term);
                                assumptions.extend_from_slice(&length_bound_assumptions);
                                // Eagerly propagate constant assignments through
                                // concatenation equations (#7464). When the pivot
                                // candidate sets `x = "a"` and we have
                                // `(str.++ x y) = "abc"`, this derives `y = "bc"`
                                // and injects it as an assumption. Without this,
                                // the CEGAR loop may try wrong splits first and
                                // stall, returning Unknown instead of SAT.
                                let propagated = self
                                    .propagate_concat_constants(&assertions_snapshot, &assumptions);
                                assumptions.extend(propagated);
                                let result = match self.solve_strings_lia_with_assumptions(
                                    &assertions_snapshot,
                                    &assumptions,
                                ) {
                                    Ok(SolveResult::Sat) => {
                                        self.last_result = Some(SolveResult::Sat);
                                        match self.finalize_sat_model_validation()? {
                                            SolveResult::Sat => self
                                                .finalize_sat_assumption_validation(&assumptions),
                                            other => Ok(other),
                                        }
                                    }
                                    other => other,
                                };
                                match result {
                                    Ok(SolveResult::Sat) => {
                                        // Defense-in-depth: the assumption
                                        // solve already downgraded any SAT
                                        // whose concrete strings violate the
                                        // scoped length bounds. Re-check here
                                        // against the pre-pass bounds because
                                        // this SAT result will be trusted
                                        // immediately by the outer solver.
                                        let model_ok = self.model_respects_detected_string_bounds(
                                            &pivot_bounds,
                                            &assumptions,
                                        );
                                        if model_ok {
                                            // The inner solver may omit
                                            // assumption-driven assignments
                                            // from the extracted string model.
                                            self.merge_explicit_string_assignments_into_model(
                                                &assumptions,
                                            );
                                            if debug_auflia_enabled() {
                                                safe_eprintln!(
                                                "[SLIA] Pivot enum: candidate {} '{}' → SAT (model verified)",
                                                i,
                                                candidates[i]
                                            );
                                            }
                                            self.pivot_enum_depth -= 1;
                                            self.solve_deadline.set(saved_deadline);
                                            return Ok(SolveResult::Sat);
                                        }
                                        // Model violates a length bound —
                                        // inner solver was unsound. Treat as
                                        // Unknown and try next candidate.
                                        if debug_auflia_enabled() {
                                            safe_eprintln!(
                                            "[SLIA] Pivot enum: candidate {} '{}' → SAT but model violates length bounds",
                                            i,
                                            candidates[i]
                                        );
                                        }
                                        all_unsat = false;
                                    }
                                    Ok(SolveResult::Unsat(_)) => {
                                        if debug_auflia_enabled() {
                                            safe_eprintln!(
                                                "[SLIA] Pivot enum: candidate {} '{}' → UNSAT",
                                                i,
                                                candidates[i]
                                            );
                                        }
                                    }
                                    Ok(SolveResult::Unknown) | Err(_) => {
                                        all_unsat = false;
                                        if debug_auflia_enabled() {
                                            safe_eprintln!(
                                            "[SLIA] Pivot enum: candidate {} '{}' → Unknown/Error",
                                            i,
                                            candidates[i]
                                        );
                                        }
                                    }
                                }
                            }
                            self.pivot_enum_depth -= 1;
                            self.solve_deadline.set(saved_deadline);
                            // If ALL candidates returned UNSAT, the formula is
                            // UNSAT only when the enumerated candidate set
                            // provably covers EVERY satisfying value of the
                            // pivot (#927). Two conditions are required:
                            //
                            // 1. `candidates_exhaustive`: the enumeration was
                            //    not truncated at MAX_PIVOT_CANDIDATES. A
                            //    truncated set can skip the witness (e.g. pivot
                            //    y="efg" at index 237 of 343 over a 7-char
                            //    alphabet), so its all-UNSAT says nothing.
                            //
                            // 2. `pivot_alphabet_grounded`: the pivot's
                            //    characters are forced into the constant
                            //    alphabet by a word equation. Otherwise a
                            //    satisfying value can use a character outside
                            //    the alphabet (e.g. `len(x)=1 ∧ x!="a"` is SAT
                            //    via x="b"), which the alphabet-restricted
                            //    enumeration never tries.
                            //
                            // If either fails, concluding UNSAT would be a
                            // spurious wrong-unsat; fall through to the sound
                            // CEGAR loop instead.
                            if all_unsat
                                && candidates_exhaustive
                                && self.pivot_alphabet_grounded(pivot_var)
                            {
                                return Ok(SolveResult::unsat());
                            }
                            // Enumeration truncated, ungrounded pivot, or some
                            // candidate was not UNSAT: fall through to the
                            // normal CEGAR loop for final determination.
                        }
                    }
                }
            }
        }

        // Step 1: Collect str.len terms and inject length axioms.
        let str_len_axioms = self.collect_str_len_axioms();

        // Step 2: Preprocess (same as solve_auf_lia).
        let mod_elim = eliminate_int_mod_div_by_constant(&mut self.ctx.terms, &self.ctx.assertions);
        let mut preprocessed = mod_elim.constraints;
        preprocessed.extend(mod_elim.rewritten);
        preprocessed.extend(str_len_axioms);

        // `str.to_int` of a provably-non-numeric string is -1 (SMT-LIB: -1 unless
        // the whole string is digits). A concat with a literal operand that
        // contains a non-digit character can NEVER be a digit string, so assert
        // `(= (str.to_int t) -1)` for it. Without this fact the LIA solver could
        // not refute e.g. `(>= (str.to_int (str.++ s "ce")) 0)` — a wrong-SAT
        // (#bug22).
        let to_int_axioms = self.collect_str_to_int_nonnumeric_axioms();
        preprocessed.extend(to_int_axioms);

        // A1: `str.to_int(x)=K ∧ str.len(x)=L` (both constant) pins `x` to the
        // unique zero-padded decimal of K, or refutes the pair when K has more
        // digits than L. Valid theorems (z3-confirmed) — only enables correct
        // UNSATs (g1b/g1c/g1e/zt1/zt2/zt7).
        let to_int_pin_axioms = self.collect_str_to_int_digit_pin_axioms();
        preprocessed.extend(to_int_pin_axioms);

        // A2: `str.to_code(x)=K` (constant K in range, non-surrogate) pins `x` to
        // the unique single-character string `char(K)`. Valid theorem (g2a/zt5).
        let to_code_axioms = self.collect_str_to_code_inversion_axioms();
        preprocessed.extend(to_code_axioms);

        // `str.indexof` of a needle absent from a fully-determined haystack is -1
        // for EVERY offset (#str-indexof-absent-needle). When both the haystack
        // `s` and needle `n` resolve to concrete strings (directly or via the
        // top-level equality closure) and `n` is non-empty and is NOT a substring
        // of `s`, there is no occurrence at any position, so `(str.indexof s n i)`
        // = -1 regardless of `i`. Without this the symbolic-offset case leaves the
        // result unconstrained and `(str.is_digit (str.from_int (str.indexof ...)))`
        // is wrongly satisfiable (a false-SAT). Sound: a needle absent from the
        // haystack is found at no position, independent of the search start.
        let indexof_absent_axioms = self.collect_str_indexof_absent_needle_axioms();
        preprocessed.extend(indexof_absent_axioms);

        // Relational lemmas linking str.prefixof/str.suffixof/str.replace/
        // str.indexof to str.contains (#string-predicate-propagation). These are
        // the SAME valid-theorem axioms `solve_strings` emits for pure QF_S; a
        // QF_SLIA instance (an indexof/Int comparison, a length constraint, ...)
        // routes HERE instead, so it must get them too. Sound by construction —
        // each is a universally-valid fact, so it only derives more (correct)
        // UNSATs, never flips a verdict.
        let predicate_relation_axioms =
            self.string_predicate_relation_axioms(&self.ctx.assertions.clone());
        preprocessed.extend(predicate_relation_axioms);

        // Exact overlap reduction (#4055): when positive prefix/suffix-style
        // constraints and a concrete length uniquely determine a string, assert
        // the resolved equality eagerly (e.g., "ab" prefix + "bc" suffix + len=3
        // implies x = "abc").
        let overlap_equalities = self.preregister_overlap_constant_equalities(&preprocessed);
        preprocessed.extend(overlap_equalities);

        // Pre-register eager str.contains decompositions (Phase 2, #3402).
        let mut skolem_cache = ExecutorSkolemCache::new();
        let mut decomposed_vars = HashSet::default();
        let mut contains_decomposed_vars = HashSet::default();
        let contains_decomps = self.preregister_contains_decompositions(
            &preprocessed,
            &mut skolem_cache,
            &mut decomposed_vars,
            &mut contains_decomposed_vars,
        );
        let contains_reduced_term_ids = self.collect_decomposition_concat_terms(&contains_decomps);
        // Collect length axioms from decomposition terms (#3850): decompositions
        // introduce new str.len and str.++ terms that weren't in the original
        // formula. Without their length axioms, LIA can't derive the arithmetic
        // contradictions needed for soundness (e.g., len(x) = len(sk) + 2*len(x) + len(sk2)).
        let decomp_len_axioms = self.collect_str_len_axioms_from_roots(&contains_decomps);
        preprocessed.extend(contains_decomps);
        preprocessed.extend(decomp_len_axioms);

        // #4057: solve in two effort passes. First expose only light
        // substr/str.at reductions plus contains decompositions. If that
        // still returns unknown, add replace reductions in a second pass.
        let (effort1_reductions, effort1_reduced_term_ids) = self.preregister_extf_reductions(
            &preprocessed,
            &mut skolem_cache,
            &mut decomposed_vars,
            true,
            false,
            false,
        );
        let effort1_len_axioms = self.collect_str_len_axioms_from_roots(&effort1_reductions);
        let contains_from_effort1 = self.preregister_contains_decompositions(
            &effort1_reductions,
            &mut skolem_cache,
            &mut decomposed_vars,
            &mut contains_decomposed_vars,
        );
        let contains_from_effort1_reduced_term_ids =
            self.collect_decomposition_concat_terms(&contains_from_effort1);
        let decomp_len_axioms_2 = self.collect_str_len_axioms_from_roots(&contains_from_effort1);

        let mut preprocessed_pass0 = preprocessed.clone();
        preprocessed_pass0.extend(effort1_reductions);
        preprocessed_pass0.extend(effort1_len_axioms);
        preprocessed_pass0.extend(contains_from_effort1);
        preprocessed_pass0.extend(decomp_len_axioms_2);

        let mut preregistered_reduced_term_ids_pass0 = effort1_reduced_term_ids;
        preregistered_reduced_term_ids_pass0.extend(contains_reduced_term_ids.iter().copied());
        preregistered_reduced_term_ids_pass0
            .extend(contains_from_effort1_reduced_term_ids.iter().copied());
        preregistered_reduced_term_ids_pass0.sort_unstable();
        preregistered_reduced_term_ids_pass0.dedup();

        let pass0_result = self.solve_strings_lia_preprocessed(
            &preprocessed_pass0,
            &preregistered_reduced_term_ids_pass0,
            &mut skolem_cache,
        );

        // Escalation passes. `cur_assertions`/`cur_reduced` carry the growing
        // preprocessed set across passes so each escalation builds on the
        // previous one (pass 1: replace reductions, #4057; pass 2: the P2
        // symbolic substr/indexof reductions, `AY_STR_P2=1` only).
        let mut cur_assertions = preprocessed_pass0;
        let mut cur_reduced = preregistered_reduced_term_ids_pass0;
        let mut result = pass0_result;

        if let Ok(SolveResult::Unknown) = result {
            // Only build replace reductions after the light pass stalls.
            // Precomputing effort-2 terms up front reintroduces the heavy
            // path into pass 0 and defeats the #4057 split-pipeline intent.
            let (effort2_reductions, effort2_reduced_term_ids) = self.preregister_extf_reductions(
                &cur_assertions,
                &mut skolem_cache,
                &mut decomposed_vars,
                false,
                true,
                false,
            );
            if !effort2_reductions.is_empty() {
                if debug_auflia_enabled() {
                    safe_eprintln!(
                        "[SLIA] pass 0 returned Unknown; escalating with replace preregistration"
                    );
                }

                let effort2_len_axioms =
                    self.collect_str_len_axioms_from_roots(&effort2_reductions);
                let contains_from_effort2 = self.preregister_contains_decompositions(
                    &effort2_reductions,
                    &mut skolem_cache,
                    &mut decomposed_vars,
                    &mut contains_decomposed_vars,
                );
                let contains_from_effort2_reduced_term_ids =
                    self.collect_decomposition_concat_terms(&contains_from_effort2);
                let decomp_len_axioms_3 =
                    self.collect_str_len_axioms_from_roots(&contains_from_effort2);

                cur_assertions.extend(effort2_reductions);
                cur_assertions.extend(effort2_len_axioms);
                cur_assertions.extend(contains_from_effort2);
                cur_assertions.extend(decomp_len_axioms_3);

                cur_reduced.extend(effort2_reduced_term_ids);
                cur_reduced.extend(contains_from_effort2_reduced_term_ids);
                cur_reduced.sort_unstable();
                cur_reduced.dedup();

                result = self.solve_strings_lia_preprocessed(
                    &cur_assertions,
                    &cur_reduced,
                    &mut skolem_cache,
                );
            }
        }

        // P2 escalation (default ON, `AY_STR_P2=0` kill switch): symbolic-bounds
        // `str.substr` + `str.indexof` first-occurrence reductions, only
        // AFTER the unchanged effort passes return Unknown — so anything the
        // default pipeline solves is decided identically first, and the P2
        // skolem web can only act on instances that were Unknown anyway. The
        // axioms are exact reductions (see reductions.rs), so UNSAT derived
        // with them is sound, and SAT still passes the full model-validation
        // battery.
        if super::strings_preregister::str_p2_enabled() {
            if let Ok(SolveResult::Unknown) = result {
                let (p2_reductions, p2_reduced_term_ids) = self.preregister_extf_reductions(
                    &cur_assertions,
                    &mut skolem_cache,
                    &mut decomposed_vars,
                    false,
                    false,
                    true,
                );
                if !p2_reductions.is_empty() {
                    if debug_auflia_enabled() {
                        safe_eprintln!(
                            "[SLIA] still Unknown; escalating with P2 symbolic substr/indexof reductions"
                        );
                    }

                    let p2_len_axioms = self.collect_str_len_axioms_from_roots(&p2_reductions);
                    let contains_from_p2 = self.preregister_contains_decompositions(
                        &p2_reductions,
                        &mut skolem_cache,
                        &mut decomposed_vars,
                        &mut contains_decomposed_vars,
                    );
                    let contains_from_p2_reduced_term_ids =
                        self.collect_decomposition_concat_terms(&contains_from_p2);
                    let p2_decomp_len_axioms =
                        self.collect_str_len_axioms_from_roots(&contains_from_p2);

                    cur_assertions.extend(p2_reductions);
                    cur_assertions.extend(p2_len_axioms);
                    cur_assertions.extend(contains_from_p2);
                    cur_assertions.extend(p2_decomp_len_axioms);

                    cur_reduced.extend(p2_reduced_term_ids);
                    cur_reduced.extend(contains_from_p2_reduced_term_ids);
                    cur_reduced.sort_unstable();
                    cur_reduced.dedup();

                    result = self.solve_strings_lia_preprocessed(
                        &cur_assertions,
                        &cur_reduced,
                        &mut skolem_cache,
                    );
                }
            }
        }

        // P3 escalation (default ON, `AY_STR_P3=0` kill switch): `str.to_int` /
        // `str.from_int` digit-string ↔ LIA coupling for NON-GROUND
        // arguments, again only after every earlier pass returned Unknown.
        // The axioms are universally valid SMT-LIB theorems (see
        // to_int_reductions.rs), so UNSAT derived with them is sound, and
        // SAT still passes the full model-validation battery. P3 is gated
        // independently of P2, but builds on the P2 substrate: symbolic
        // substr reductions give LIA the exact length windows of the
        // strings feeding to_int (`str.at` lowers to a substr). When the P2
        // gate is off, the P3 pass collects that same package here first.
        if super::strings_preregister::str_p3_enabled() {
            if let Ok(SolveResult::Unknown) = result {
                if !super::strings_preregister::str_p2_enabled() {
                    let (p2_reductions, p2_reduced_term_ids) = self.preregister_extf_reductions(
                        &cur_assertions,
                        &mut skolem_cache,
                        &mut decomposed_vars,
                        false,
                        false,
                        true,
                    );
                    if !p2_reductions.is_empty() {
                        let p2_len_axioms = self.collect_str_len_axioms_from_roots(&p2_reductions);
                        let contains_from_p2 = self.preregister_contains_decompositions(
                            &p2_reductions,
                            &mut skolem_cache,
                            &mut decomposed_vars,
                            &mut contains_decomposed_vars,
                        );
                        let contains_from_p2_reduced_term_ids =
                            self.collect_decomposition_concat_terms(&contains_from_p2);
                        let p2_decomp_len_axioms =
                            self.collect_str_len_axioms_from_roots(&contains_from_p2);

                        cur_assertions.extend(p2_reductions);
                        cur_assertions.extend(p2_len_axioms);
                        cur_assertions.extend(contains_from_p2);
                        cur_assertions.extend(p2_decomp_len_axioms);

                        cur_reduced.extend(p2_reduced_term_ids);
                        cur_reduced.extend(contains_from_p2_reduced_term_ids);
                    }
                }

                let (p3_reductions, p3_reduced_term_ids) =
                    self.preregister_to_int_reductions(&cur_assertions, &mut skolem_cache);
                if !p3_reductions.is_empty() {
                    if debug_auflia_enabled() {
                        safe_eprintln!(
                            "[SLIA] still Unknown; escalating with P3 to_int/from_int digit-string reductions"
                        );
                    }

                    let p3_len_axioms = self.collect_str_len_axioms_from_roots(&p3_reductions);
                    let contains_from_p3 = self.preregister_contains_decompositions(
                        &p3_reductions,
                        &mut skolem_cache,
                        &mut decomposed_vars,
                        &mut contains_decomposed_vars,
                    );
                    let contains_from_p3_reduced_term_ids =
                        self.collect_decomposition_concat_terms(&contains_from_p3);
                    let p3_decomp_len_axioms =
                        self.collect_str_len_axioms_from_roots(&contains_from_p3);

                    cur_assertions.extend(p3_reductions);
                    cur_assertions.extend(p3_len_axioms);
                    cur_assertions.extend(contains_from_p3);
                    cur_assertions.extend(p3_decomp_len_axioms);

                    cur_reduced.extend(p3_reduced_term_ids);
                    cur_reduced.extend(contains_from_p3_reduced_term_ids);
                    cur_reduced.sort_unstable();
                    cur_reduced.dedup();

                    result = self.solve_strings_lia_preprocessed(
                        &cur_assertions,
                        &cur_reduced,
                        &mut skolem_cache,
                    );
                }
            }
        }
        if debug_auflia_enabled() {
            safe_eprintln!(
                "[SLIA] === solve_strings_lia EXIT depth={}: {:?} ===",
                self.pivot_enum_depth,
                result
            );
        }
        if matches!(result, Ok(SolveResult::Sat)) {
            // The split-loop validates the temporary preprocessed assertion
            // window. Force the outer check_sat path to validate the restored
            // original QF_SLIA assertions before any SAT escapes (#8779).
            self.last_model_validated = false;
            self.last_validation_stats = None;
        }
        result
    }

    /// Solve QF_SLIA under assumptions (#7656).
    ///
    /// This reuses [`Self::solve_strings_lia`] by temporarily appending
    /// assumptions to the active assertion set, ensuring str.len/string
    /// axioms are generated from both assertions and assumptions.
    ///
    /// Uses `with_isolated_incremental_state` to prevent assumption-scoped
    /// clauses from leaking into the persistent SAT solver (#7656).
    pub(in crate::executor) fn solve_strings_lia_with_assumptions(
        &mut self,
        assertions: &[TermId],
        assumptions: &[TermId],
    ) -> Result<SolveResult> {
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }

        let mut scoped_assertions = Vec::with_capacity(assertions.len() + assumptions.len());
        scoped_assertions.extend(assertions.iter().copied());
        scoped_assertions.extend(assumptions.iter().copied());
        let scoped_bounds = self.detect_bounded_string_vars_in(&scoped_assertions);

        let result = self.with_isolated_incremental_state(Some(scoped_assertions), |exec| {
            exec.solve_strings_lia()
        });

        match result {
            Ok(SolveResult::Unsat(_)) => {
                // Keep assumption-core behavior consistent even without minimal core extraction.
                self.last_assumption_core = Some(assumptions.to_vec());
                Ok(SolveResult::unsat())
            }
            Ok(SolveResult::Sat) => {
                if !self.model_respects_detected_string_bounds(&scoped_bounds, assumptions) {
                    if debug_auflia_enabled() {
                        safe_eprintln!(
                            "[SLIA] assumption solve produced SAT with concrete string violating detected length bounds; downgrading to Unknown"
                        );
                    }
                    self.last_model = None;
                    self.last_assumption_core = None;
                    return Ok(SolveResult::Unknown);
                }
                self.merge_explicit_string_assignments_into_model(assumptions);
                self.last_assumption_core = None;
                Ok(SolveResult::Sat)
            }
            Ok(SolveResult::Unknown) => {
                self.last_assumption_core = None;
                Ok(SolveResult::Unknown)
            }
            Err(err) => {
                self.last_assumption_core = None;
                Err(err)
            }
        }
    }

    fn solve_strings_lia_preprocessed(
        &mut self,
        assertions: &[TermId],
        preregistered_reduced_term_ids: &[TermId],
        skolem_cache: &mut ExecutorSkolemCache,
    ) -> Result<SolveResult> {
        // Pre-create integer constants for values 0..max_string_len so the
        // N-O bridge's int_const_terms map has entries for LIA-derived values
        // like str.len(y) = 3 that do not appear literally in the formula.
        let mut max_len = 0usize;
        let mut stack: Vec<TermId> = assertions.to_vec();
        let mut visited = HashSet::default();
        while let Some(tid) = stack.pop() {
            if !visited.insert(tid) {
                continue;
            }
            match self.ctx.terms.get(tid) {
                TermData::Const(Constant::String(s)) => {
                    max_len = max_len.max(s.len());
                }
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                TermData::Let(bindings, body) => {
                    for (_, value) in bindings.iter() {
                        stack.push(*value);
                    }
                    stack.push(*body);
                }
                _ => {}
            }
        }
        for i in 0..=max_len {
            let _pre_intern = self.ctx.terms.mk_int(num_bigint::BigInt::from(i));
        }

        let mut emitted_dynamic_len_axioms: HashSet<TermId> = assertions.iter().copied().collect();
        let mut last_lemma: Option<StringLemma> = None;
        let mut duplicate_streak = 0usize;
        let mut dynamic_reduced_term_ids: Vec<TermId> = Vec::new();
        // #3762: String solver warm state preserved across CEGAR iterations.
        // Statistics and reduced-term markers survive theory recreation in
        // the non-persistent eager arm.
        let mut string_warm_state: Option<ay_strings::StringSolverWarmState> = None;
        let saved_assertions = std::mem::replace(&mut self.ctx.assertions, assertions.to_vec());
        let saved_assertion_len = saved_assertions.len();

        // Clear the persistent SAT solver before each SLIA solve (#6688).
        // SLIA uses preprocessed temporary assertions (mod/div elimination,
        // str.len axioms, pivot candidates) that change between calls —
        // especially during pivot enumeration. Reusing a persistent solver
        // across calls with different assertion sets causes false UNSAT from
        // accumulated learned clauses. The legacy macro always created a
        // fresh SAT solver per call; this preserves that semantic.
        //
        // #3762: Before dropping, extract high-quality learned clauses,
        // VSIDS activities, and phase hints into SatWarmState. The pipeline
        // setup macro imports these into the fresh solver to avoid cold-start.
        if let Some(ref mut state) = self.incr_theory_state {
            if let Some(ref sat) = state.lia_persistent_sat {
                state.sat_warm_state = Some(crate::SatWarmState::extract(sat));
            }
            state.lia_persistent_sat = None;
            state.encoded_assertions.clear();
        }

        let result = solve_incremental_split_loop_pipeline!(self,
            tag: "SLIA",
            persistent_sat_field: lia_persistent_sat,
            create_theory: {
                let empty_id = self.ctx.terms.mk_string(String::new());
                let mut theory = StringsLiaSolver::new(&self.ctx.terms);
                theory.set_empty_string_id(empty_id);
                // #3762: Import warm state from previous iteration if available.
                // Restores cumulative statistics and reduced terms from prior
                // iterations, avoiding re-registration overhead.
                if let Some(ref ws) = string_warm_state {
                    theory.import_string_warm_state(ws);
                }
                for &tid in preregistered_reduced_term_ids {
                    theory.mark_reduced(tid);
                }
                for &tid in &dynamic_reduced_term_ids {
                    theory.mark_reduced(tid);
                }
                theory
            },
            extract_models: |theory| {
                use crate::executor::theories::solve_harness::TheoryModels;
                let (euf, lia, string_model) = theory.extract_all_models();
                TheoryModels {
                    euf: Some(euf),
                    lia,
                    string: Some(string_model),
                    ..TheoryModels::default()
                }
            },
            max_splits: MAX_SPLITS_LIA,
            pre_theory_import: |theory, lc, hc, ds| {
                theory.import_learned_state(std::mem::take(lc), std::mem::take(hc));
                theory.import_dioph_state(std::mem::take(ds));
            },
            post_theory_export: |theory| {
                // #3762: Capture string solver warm state before drop.
                string_warm_state = Some(theory.take_string_warm_state());
                let (lc, hc) = theory.take_learned_state();
                let ds = theory.take_dioph_state();
                (lc, hc, ds)
            },
            eager_extension: true,
            disable_preprocess: true,
            pre_iter_check: |_s| self.should_abort_theory_loop(),
            // Strings increment P3 (default ON, `AY_STR_P3=0` kill switch — the killed
            // lane keeps the conservative escalate-to-Unknown): opt into the
            // #6812 verify-before-accept relaxation for post-split UNSAT.
            // The full_str_int family refutes propositionally+LIA after
            // expression splits, and without this opt-in the derived UNSAT
            // was ALWAYS discarded in the SLIA lane. Sound and
            // non-optimistic: the UNSAT is accepted only when a FRESH
            // isolated UF+LIA solve of the CURRENT assertion set (original
            // preprocessed assertions + valid preregistered axioms, no
            // learned/split clauses) independently re-derives Unsat — and a
            // UF+LIA refutation of a relaxation (string operators as free
            // functions, congruence only) is a fortiori a Strings+LIA
            // refutation. Anything else (Sat/Unknown/failure) keeps the
            // escalate-to-Unknown behavior.
            verify_unsat_after_splits: super::strings_preregister::str_p3_enabled(),
            max_string_lemma_requests: MAX_STRING_LEMMA_ITERATIONS,
            handle_string_lemma: |lemma, negations| {
                if last_lemma.as_ref() == Some(&lemma) {
                    duplicate_streak += 1;
                } else {
                    duplicate_streak = 0;
                }
                let stall = duplicate_streak >= MAX_CONSECUTIVE_DUPLICATE_LEMMAS;
                if stall && debug_auflia_enabled() {
                    safe_eprintln!(
                        "[SLIA] duplicate-streak {} for {:?} lemma (x={:?}, y={:?}, off={}) — stalled",
                        duplicate_streak + 1,
                        lemma.kind,
                        lemma.x,
                        lemma.y,
                        lemma.char_offset,
                    );
                }
                last_lemma = Some(lemma.clone());

                if stall {
                    (Vec::new(), true)
                } else {
                    let mut clauses = self.create_string_lemma_clauses(&lemma, skolem_cache);

                    for tid in self.string_lemma_reduced_terms(&lemma, skolem_cache) {
                        if !dynamic_reduced_term_ids.contains(&tid) {
                            dynamic_reduced_term_ids.push(tid);
                        }
                    }

                    let new_roots: Vec<TermId> = clauses
                        .iter()
                        .flat_map(|clause| clause.iter().copied())
                        .collect();
                    let dynamic_len_axioms =
                        self.collect_str_len_axioms_from_roots(&new_roots);
                    for axiom in dynamic_len_axioms {
                        if emitted_dynamic_len_axioms.insert(axiom) {
                            clauses.extend(self.lower_dynamic_axiom_to_clauses(axiom));
                        }
                    }

                    if self.produce_proofs_enabled() {
                        for clause in &clauses {
                            for &atom in clause {
                                negations.note_fresh_term(atom);
                            }
                        }
                    }

                    if debug_auflia_enabled() {
                        safe_eprintln!(
                            "[SLIA] string {:?} lemma (x={:?}, y={:?}, off={}, {} clauses)",
                            lemma.kind,
                            lemma.x,
                            lemma.y,
                            lemma.char_offset,
                            clauses.len()
                        );
                    }

                    (clauses, false)
                }
            }
        );

        self.ctx.assertions = saved_assertions;
        debug_assert!(
            self.ctx.assertions.len() == saved_assertion_len,
            "BUG: solve_strings_lia_preprocessed: assertion count {} != saved {saved_assertion_len} after restore",
            self.ctx.assertions.len()
        );
        result
    }
}

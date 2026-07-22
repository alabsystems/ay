// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Materialize concrete witness strings for under-constrained string
//! variables in a QF_S / QF_SLIA SAT model (#str-witness).
//!
//! Root cause this addresses: `(str.len x)` is bridged to a LIA integer
//! proxy. The LIA solver assigns the proxy (e.g. `len_x = 5`), but the
//! string model leaves `x` unassigned, so the printed model defaults `x`
//! to `""` — a value whose length (0) violates the proxy (5). Nothing in
//! the original pipeline materializes a concrete string of the proxy
//! length, and the string-level model validation could not contradict an
//! *unassigned* variable (it evaluated to `Unknown`, which fell through to
//! SAT-fallback).
//!
//! This module closes the gap: for every string variable whose model value
//! is missing (or whose existing value does not satisfy its length /
//! prefix / suffix / char-at / equality constraints), it builds a concrete
//! witness string of the required length with the forced positions pinned
//! and all free positions filled with a default character. The witness is
//! then re-validated by full substitution: if ANY assertion is definitively
//! `false` under the materialized model, the materialization is abandoned
//! (the caller fails closed and degrades SAT to Unknown). The whole point
//! is: after this fix, no `sat` may print a model that violates the
//! assertions.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Constant, Symbol, TermData};
use ay_core::{Sort, TermId};
use ay_strings::we_regex::WeRegex;
use num_bigint::BigInt;

use super::string_witness::{str_witness_w2, MAX_WITNESS_REGEXES, WITNESS_SEARCH_MAX_LEN};
use super::{EvalValue, Executor, Model};

/// Default fill character for free positions in a materialized witness.
const FILL_CHAR: char = 'a';

/// Maximum length of a witness string we are willing to materialize.
///
/// Guards against a pathological proxy length (e.g. a huge integer from an
/// unconstrained `str.len` lower bound) allocating an enormous string. If a
/// required length exceeds this, we decline to materialize that variable and
/// the caller fails closed (Unknown) rather than emitting a possibly-invalid
/// or memory-hostile model.
const MAX_WITNESS_LEN: usize = 1 << 16;

/// A hard `str.indexof` constraint on a variable being materialized (CAP-2):
/// `(= (str.indexof v needle offset) result)` with literal needle / offset /
/// result. `result: None` encodes `-1` (no occurrence at or after `offset`).
struct IndexofConstraint {
    /// Literal non-empty needle.
    needle: String,
    /// Literal non-negative search offset (characters).
    offset: usize,
    /// `Some(r)`: first occurrence at character position `r` (`r >= offset`);
    /// `None`: no occurrence at or after `offset` (`-1`).
    result: Option<usize>,
}

/// Per-variable accumulated string constraints derived from the assertions.
#[derive(Default)]
struct StringVarConstraints {
    /// Exact required length, if pinned (from `str.len` proxy / equalities).
    required_len: Option<usize>,
    /// Forced characters at specific 0-based positions.
    forced: HashMap<usize, char>,
    /// Constant prefixes the witness must start with (`str.prefixof c v`).
    prefixes: Vec<String>,
    /// Constant suffixes the witness must end with (`str.suffixof c v`).
    suffixes: Vec<String>,
    /// Constant substrings the witness must contain (`str.contains v c`).
    contains: Vec<String>,
    /// Constant substrings the witness must NOT contain, from a HARD
    /// `(not (str.contains v c))` conjunct (NF-engine closure 6,
    /// `AY_STR_NF=1`; the vector stays EMPTY when the flag is off, so every
    /// check below is a no-op and the flags-off materializer is
    /// byte-identical).
    ///
    /// EXACTNESS: `¬str.contains(v, c)` says exactly "no window of `v` equals
    /// `c`", which is the windowed-disequality form of the increment spec and
    /// is checked here literally by `!value.contains(c)`. Both the check and
    /// the fill-character search below are therefore an exact rendering of the
    /// asserted literal, not an approximation of it.
    forbidden: Vec<String>,
    /// Hard `str.indexof` results (`(= (str.indexof v "w" k) r)` literals).
    indexofs: Vec<IndexofConstraint>,
    /// Hard `str.to_int` results (`(= (str.to_int v) N)` literals, extf
    /// wave 2). `N >= 0` forces `v` to be the all-digit string of the
    /// required length whose decimal value is `N` (leading zeros pad);
    /// `N = -1` forces `v` to NOT be a nonempty all-digit string.
    to_ints: Vec<BigInt>,
    /// A fully pinned value (from `(= v const)`), if present.
    pinned: Option<String>,
    /// HARD regex memberships the witness must satisfy (W2,
    /// default ON, `AY_STR_WITNESS=0` kill switch — the vector stays EMPTY when the flag
    /// is off, so every check below is a no-op and the flags-off materializer
    /// is byte-identical). A negative membership `x ∉ R` is carried EXACTLY as
    /// `Comp(R)`, so both polarities constrain the witness.
    regexes: Vec<WeRegex>,
}

/// SMT-LIB `str.to_int` on a concrete character vector: the non-negative
/// decimal value when `chars` is a nonempty all-ASCII-digit string
/// (leading zeros allowed and contributing), otherwise `-1`.
fn eval_to_int_chars(chars: &[char]) -> BigInt {
    if chars.is_empty() || !chars.iter().all(|c| c.is_ascii_digit()) {
        return BigInt::from(-1);
    }
    let s: String = chars.iter().collect();
    s.parse::<BigInt>().unwrap_or_else(|_| BigInt::from(-1))
}

/// SMT-LIB `str.indexof` on concrete character vectors: position of the first
/// occurrence of `needle` in `hay` at or after `offset`, or `None` for `-1`.
/// Matches SMT-LIB 2.6 semantics for non-empty needles (the collector never
/// records empty needles).
fn eval_indexof_chars(hay: &[char], needle: &[char], offset: usize) -> Option<usize> {
    if offset > hay.len() || needle.is_empty() || needle.len() > hay.len() - offset {
        return None;
    }
    (offset..=(hay.len() - needle.len())).find(|&start| {
        needle
            .iter()
            .enumerate()
            .all(|(i, &ch)| hay[start + i] == ch)
    })
}

impl Executor {
    /// Materialize concrete witness strings for under-constrained string
    /// variables, then strictly re-validate the resulting model.
    ///
    /// Returns `true` when the model is consistent (either no materialization
    /// was needed, or every materialized witness satisfies all assertions by
    /// full substitution). Returns `false` when a required witness could not
    /// be constructed consistently — the caller MUST fail closed (degrade SAT
    /// to Unknown) in that case. Never produces a model that violates an
    /// assertion.
    ///
    /// Only string variables are touched; all other theory model values are
    /// left untouched.
    pub(in crate::executor) fn materialize_string_witnesses(&mut self) -> bool {
        // Only materialize at the OUTER validation level, where
        // `self.ctx.assertions` is the restored set of ORIGINAL user
        // assertions. Inner solves (pivot enumeration, prefix/suffix
        // witnesses) run with `pivot_enum_depth > 0` and a *preprocessed*
        // assertion window that contains decomposition skolems
        // (`sk_pfx_suf_*`, contains-skolems, str.len axioms). Those skolem
        // string variables are determined by the witness but are not part of
        // the user model, so trying to materialize against that window would
        // spuriously fail closed. The inner SAT result still propagates: after
        // it, `solve_strings_lia` resets `last_model_validated = false`, so the
        // outer `check_sat_guarded` re-runs this materialization against the
        // clean original assertions. Soundness is unaffected — the outer pass
        // is the authoritative one.
        if self.pivot_enum_depth != 0 {
            return true;
        }
        // Only relevant when there is a model and at least one string var.
        let Some(model) = self.last_model.as_ref() else {
            return true;
        };

        // Collect the string variables that actually appear in the formula.
        let string_vars = self.collect_string_variables();
        if string_vars.is_empty() {
            return true;
        }

        // Snapshot existing concrete string values (if any).
        let mut existing: HashMap<TermId, String> = model
            .string_model
            .as_ref()
            .map(|sm| sm.values.clone())
            .unwrap_or_default();

        // Gather per-variable constraints from the (flattened) assertions.
        let assertions = self.flatten_assertion_conjunctions();
        let mut constraints: HashMap<TermId, StringVarConstraints> = HashMap::default();
        for &var in &string_vars {
            constraints.insert(var, StringVarConstraints::default());
        }
        for &assertion in &assertions {
            self.collect_string_constraints(assertion, true, &mut constraints);
        }

        // Resolve the required length for each variable from the model's
        // `(str.len var)` proxy. This is authoritative: it is the same value
        // the model printer would report for `(str.len var)`.
        let len_proxies = self.collect_str_len_terms(&string_vars);

        // Build/repair witnesses. Track which variables we (re)assigned so we
        // only commit if the strict re-validation succeeds.
        let mut materialized: HashMap<TermId, String> = HashMap::default();
        let mut any_change = false;

        for &var in &string_vars {
            let cons = constraints.get(&var).expect("constraints seeded for var");

            // If the variable already has a concrete value from the solver's
            // string model, that value is AUTHORITATIVE: it came from the
            // variable's equivalence class (e.g. `x = y ++ z` resolved to a
            // constant). We only rebuild it when it violates a HARD constraint
            // — an explicit `(= (str.len v) N)` length pin, a forced char-at, a
            // prefix/suffix, or a required substring. We deliberately do NOT
            // second-guess a solver-assigned value with the `str.len` proxy /
            // bound heuristic, which can lag the actual EQC length.
            if let Some(current) = existing.get(&var) {
                if Self::value_satisfies_constraints(current, cons.required_len, cons) {
                    continue;
                }
            }

            // Determine the required length: prefer an explicit length pin,
            // else the model's str.len proxy value, else the existing value's
            // length, else 0.
            let required_len = self.resolve_required_length(var, cons, &len_proxies, &existing);

            // A fully-pinned value (from `(= v const)`) is authoritative; if
            // it conflicts with the required length, fail closed.
            if let Some(pinned) = &cons.pinned {
                if let Some(rl) = required_len {
                    if pinned.chars().count() != rl {
                        return false;
                    }
                }
                materialized.insert(var, pinned.clone());
                existing.insert(var, pinned.clone());
                any_change = true;
                continue;
            }

            let Some(rl) = required_len else {
                // W2: no length information, but a LANGUAGE constraint — the
                // empty-string completion below would pin `""`, which any
                // non-nullable regex refutes. Construct the shortest accepted
                // string instead. Still only a candidate: the strict
                // substitution re-validation below decides.
                if !cons.regexes.is_empty() {
                    if let Some(w) = ay_strings::we_regex::find_witness_bounded(
                        &cons.regexes,
                        None,
                        WITNESS_SEARCH_MAX_LEN,
                    ) {
                        if Self::value_satisfies_constraints(&w, None, cons) {
                            materialized.insert(var, w.clone());
                            existing.insert(var, w);
                            any_change = true;
                        }
                    }
                }
                // No length information at all and the variable is otherwise
                // unconstrained at the string level: leave it for the
                // empty-string completion pass below (which only runs when some
                // OTHER variable was actually materialized).
                continue;
            };

            if rl > MAX_WITNESS_LEN {
                // Refuse to allocate a pathologically large witness; fail
                // closed so we never emit an invalid (too-short) model.
                return false;
            }

            match Self::build_witness(rl, cons) {
                Some(witness) => {
                    materialized.insert(var, witness.clone());
                    existing.insert(var, witness);
                    any_change = true;
                }
                None => {
                    // Constraints are internally inconsistent (e.g. a forced
                    // char outside the required length, or overlapping
                    // prefix/suffix that disagree). Fail closed.
                    return false;
                }
            }
        }

        // Return early ONLY when no witness was built AND every user string
        // variable already has a concrete value in the string model. If some
        // user variable is missing, the trial model is INCOMPLETE: string
        // assertions mentioning it evaluate to Unknown and the downstream
        // observation path would accept them via the SAT solver's own
        // assignment (circular), letting an invalid model slip through (e.g.
        // `(or (str.< "" "") (str.prefixof (str.++ "b" s) "a"))` with `s`
        // unconstrained at the collector level — nothing materializes, yet the
        // printed model `s = ""` falsifies the formula). In that case we must
        // still run the empty-string completion pass + strict re-validation
        // below (#str-incomplete-model-gate).
        let any_missing = string_vars.iter().any(|v| !existing.contains_key(v));
        if !any_change && !any_missing {
            return true;
        }

        // Empty-string completion pass (#str-allconcat-prefixof).
        //
        // We are about to strictly re-validate the trial model by full
        // substitution. That check only refutes a witness when every operand of
        // a string predicate resolves to a concrete value — an Unknown operand
        // is tolerated (it may legitimately depend on a skolem). But a USER
        // string variable that survived the loop above is genuinely
        // unconstrained at the string level, so the model PRINTER reports it as
        // the empty string. If we leave it unassigned, a string predicate whose
        // operand is a concat MENTIONING such a variable evaluates to Unknown
        // and the (would-be invalid) witness slips through — the all-concat
        // `str.prefixof`/`str.suffixof`/`str.contains` wrong-SAT hole. Example:
        // `(str.prefixof "aba" (str.++ s1 s1 s2 "ba"))` with `s1="ba"` (forced
        // by `(str.prefixof "ba" s1)`) and `s2` unconstrained: the haystack is
        // `"bababa"`, which "aba" does not prefix, but the unassigned `s2` left
        // the haystack Unknown.
        //
        // Pin each such variable to "" — its printer default — so the trial
        // model is COMPLETE over user string variables and the re-validation
        // evaluates every concat to a concrete string. This runs whenever a
        // real witness was built (`any_change`) OR some user string variable
        // is missing from the model (`any_missing`); formulas whose variables
        // are all already concretely assigned keep their original
        // delegated-evidence validation path. Sound: "" is the value the model
        // already prints for these variables and satisfies their (empty)
        // string-shape constraints, so committing it can only turn a would-be
        // wrong-SAT into Unknown, never the reverse.
        for &var in &string_vars {
            if existing.contains_key(&var) {
                continue;
            }
            materialized.insert(var, String::new());
            existing.insert(var, String::new());
        }

        // Commit the materialized values into a *trial* model and strictly
        // re-validate by full substitution. We never trust SAT-fallback for
        // these freshly-concrete strings.
        self.commit_string_values(&materialized);

        if self.materialized_model_satisfies_assertions(&assertions) {
            true
        } else {
            // The witness did not satisfy every assertion under substitution.
            // Roll back the materialized values (so we do not leave an invalid
            // model around) and signal the caller to fail closed.
            self.rollback_string_values(&materialized);
            false
        }
    }

    /// Collect the USER-declared string-sorted variables that appear in the
    /// assertions.
    ///
    /// Crucially, we EXCLUDE internal skolem variables (e.g. `sk_pfx_suf_*`,
    /// contains/substr skolems) introduced by the string solver's
    /// decomposition reductions. Those are not user symbols and get-model
    /// never prints them; materializing them to a default value would make the
    /// *derived* decomposition lemmas (e.g. `(= z (str.++ "a" sk))`) evaluate
    /// to a concrete-false, spuriously rejecting an otherwise-valid witness.
    /// By leaving skolems unassigned, those lemmas evaluate to `Unknown` and
    /// the strict re-validation only gates on the (now-concrete) user-level
    /// constraints. A variable counts as user-declared when its name resolves
    /// to a nullary symbol in the frontend symbol table — the same predicate
    /// get-model uses to decide what to print.
    pub(in crate::executor) fn collect_string_variables(&self) -> Vec<TermId> {
        let mut out: Vec<TermId> = Vec::new();
        let mut seen: HashSet<TermId> = HashSet::default();
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        let mut visited: HashSet<TermId> = HashSet::default();
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            match self.ctx.terms.get(t) {
                TermData::Var(name, _) if *self.ctx.terms.sort(t) == Sort::String => {
                    let user_declared = self
                        .ctx
                        .symbol_info_by_identity(name)
                        .is_some_and(|info| info.arg_sorts.is_empty());
                    if user_declared && seen.insert(t) {
                        out.push(t);
                    }
                }
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, th, e) => {
                    stack.push(*c);
                    stack.push(*th);
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
        out
    }

    /// For each string variable, find the `(str.len var)` term in the store
    /// (if one exists) so its model value can be read as the required length.
    fn collect_str_len_terms(&self, vars: &[TermId]) -> HashMap<TermId, TermId> {
        let var_set: HashSet<TermId> = vars.iter().copied().collect();
        let mut out: HashMap<TermId, TermId> = HashMap::default();
        let mut seen: HashSet<TermId> = HashSet::default();
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            match self.ctx.terms.get(t) {
                TermData::App(Symbol::Named(name), args) => {
                    if name == "str.len" && args.len() == 1 && var_set.contains(&args[0]) {
                        out.entry(args[0]).or_insert(t);
                    }
                    stack.extend(args.iter().copied());
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, th, e) => {
                    stack.push(*c);
                    stack.push(*th);
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
        out
    }

    /// Resolve the required length for a string variable.
    ///
    /// Priority:
    /// 1. An explicit length pin collected from the assertions
    ///    (`(= (str.len v) N)`), via `required_len`.
    /// 2. The model's value for the `(str.len v)` proxy term.
    /// 3. The longest constant prefix/suffix/contains/forced-char extent
    ///    (a string satisfying those must be at least that long).
    /// 4. The existing value's length, if any.
    fn resolve_required_length(
        &self,
        var: TermId,
        cons: &StringVarConstraints,
        len_proxies: &HashMap<TermId, TermId>,
        existing: &HashMap<TermId, String>,
    ) -> Option<usize> {
        if let Some(rl) = cons.required_len {
            return Some(rl);
        }
        if let Some(&len_term) = len_proxies.get(&var) {
            // 1. The LIA/EUF model's value for the `(str.len v)` proxy term.
            //    This is authoritative: the combined Strings+LIA solver
            //    assigns the proxy a concrete integer (e.g. when
            //    `(= (str.len x) (str.len y))` forces len(y)=len(x)=3, the
            //    proxy for `(str.len y)` is 3 even though no literal bound on
            //    `(str.len y)` appears). `evaluate_term` cannot reach it
            //    because `(str.len v)` is an App whose string arg is
            //    unassigned, so we read the proxy directly.
            if let Some(n) = self.str_len_proxy_value(len_term) {
                return Some(n);
            }
            // 2. Fall back to int-bound extraction from the assertions,
            //    mirroring how the model printer resolves `(str.len v)` when no
            //    theory model value is present.
            if let Some(n) = self.extract_int_from_assertion_bounds(len_term) {
                if n.sign() != num_bigint::Sign::Minus {
                    if let Ok(n) = usize::try_from(n) {
                        return Some(n);
                    }
                }
            }
        }
        // Minimal length implied by string-shape constraints.
        let mut min_len = 0usize;
        for p in &cons.prefixes {
            min_len = min_len.max(p.chars().count());
        }
        for s in &cons.suffixes {
            min_len = min_len.max(s.chars().count());
        }
        for c in &cons.contains {
            min_len = min_len.max(c.chars().count());
        }
        for io in &cons.indexofs {
            if let Some(r) = io.result {
                min_len = min_len.max(r + io.needle.chars().count());
            }
        }
        for n in &cons.to_ints {
            // A non-negative to_int pins at least the decimal's width
            // (leading zeros may pad beyond it).
            if n.sign() != num_bigint::Sign::Minus {
                min_len = min_len.max(n.to_string().chars().count());
            }
        }
        if let Some(max_pos) = cons.forced.keys().max() {
            min_len = min_len.max(max_pos + 1);
        }
        if min_len > 0 {
            return Some(min_len);
        }
        existing.get(&var).map(|v| v.chars().count())
    }

    /// Read the combined solver's integer value for a `(str.len v)` proxy
    /// term directly from the LIA/EUF model. Returns `Some(n)` only for a
    /// non-negative value that fits in `usize`.
    ///
    /// The `str.len` bridge registers each `(str.len v)` term as an integer
    /// proxy in the LIA solver; the EUF combiner mirrors integer-sorted shared
    /// terms into its own value maps. Either may hold the assigned length.
    fn str_len_proxy_value(&self, len_term: TermId) -> Option<usize> {
        let model = self.last_model.as_ref()?;
        let try_int = |n: &BigInt| -> Option<usize> {
            if n.sign() == num_bigint::Sign::Minus {
                return None;
            }
            usize::try_from(n.clone()).ok()
        };
        if let Some(lia) = model.lia_model.as_ref() {
            if let Some(n) = lia.values.get(&len_term) {
                if let Some(u) = try_int(n) {
                    return Some(u);
                }
            }
        }
        if let Some(euf) = model.euf_model.as_ref() {
            if let Some(n) = euf.int_values.get(&len_term) {
                if let Some(u) = try_int(n) {
                    return Some(u);
                }
            }
            if let Some(s) = euf.term_values.get(&len_term) {
                if let Ok(n) = s.parse::<BigInt>() {
                    if let Some(u) = try_int(&n) {
                        return Some(u);
                    }
                }
            }
        }
        None
    }

    /// Whether an existing concrete value already satisfies the variable's
    /// length and forced-character constraints (so it need not be rebuilt).
    fn value_satisfies_constraints(
        value: &str,
        required_len: Option<usize>,
        cons: &StringVarConstraints,
    ) -> bool {
        let chars: Vec<char> = value.chars().collect();
        if let Some(rl) = required_len {
            if chars.len() != rl {
                return false;
            }
        }
        for (&pos, &ch) in &cons.forced {
            if chars.get(pos) != Some(&ch) {
                return false;
            }
        }
        for p in &cons.prefixes {
            if !value.starts_with(p.as_str()) {
                return false;
            }
        }
        for s in &cons.suffixes {
            if !value.ends_with(s.as_str()) {
                return false;
            }
        }
        for c in &cons.contains {
            if !value.contains(c.as_str()) {
                return false;
            }
        }
        // NF-engine closure 6: hard `(not (str.contains v c))` conjuncts. The
        // check is the literal negation of the predicate, so it is exact.
        for c in &cons.forbidden {
            if value.contains(c.as_str()) {
                return false;
            }
        }
        for io in &cons.indexofs {
            let needle: Vec<char> = io.needle.chars().collect();
            if eval_indexof_chars(&chars, &needle, io.offset) != io.result {
                return false;
            }
        }
        for n in &cons.to_ints {
            if eval_to_int_chars(&chars) != *n {
                return false;
            }
        }
        // W2: hard regex memberships. `matches` returns `None` when its
        // derivative size cap trips — that is "no information", so it must NOT
        // reject (rejecting on unknown could discard a value that is in fact
        // fine, costing a conversion; accepting on unknown is safe because the
        // strict substitution re-validation still runs).
        for r in &cons.regexes {
            if r.matches(value) == Some(false) {
                return false;
            }
        }
        true
    }

    /// Build a concrete witness of `required_len` characters that satisfies
    /// the forced positions, prefixes, suffixes, and (best-effort) contains
    /// constraints. Returns `None` when the constraints are inconsistent with
    /// the required length or with each other.
    fn build_witness(required_len: usize, cons: &StringVarConstraints) -> Option<String> {
        let mut buf: Vec<Option<char>> = vec![None; required_len];

        let pin = |pos: usize, ch: char, buf: &mut Vec<Option<char>>| -> bool {
            if pos >= buf.len() {
                return false;
            }
            match buf[pos] {
                Some(existing) if existing != ch => false,
                _ => {
                    buf[pos] = Some(ch);
                    true
                }
            }
        };

        // Forced char-at constraints.
        for (&pos, &ch) in &cons.forced {
            if !pin(pos, ch, &mut buf) {
                return None;
            }
        }
        // Non-negative to_int results pin EVERY position (extf wave 2):
        // `(= (str.to_int v) N)` with `N >= 0` forces `v` to be the
        // zero-padded decimal of N at the required length. A decimal wider
        // than the required length is inconsistent — fail closed. `N = -1`
        // pins nothing (the non-digit fill below plus strict re-validation
        // handle it).
        for n in &cons.to_ints {
            if n.sign() == num_bigint::Sign::Minus {
                continue;
            }
            let dec = n.to_string();
            let dec_chars: Vec<char> = dec.chars().collect();
            if dec_chars.len() > required_len {
                return None;
            }
            let pad = required_len - dec_chars.len();
            for pos in 0..pad {
                if !pin(pos, '0', &mut buf) {
                    return None;
                }
            }
            for (i, &ch) in dec_chars.iter().enumerate() {
                if !pin(pad + i, ch, &mut buf) {
                    return None;
                }
            }
        }
        // Positive indexof results pin the needle at the result position
        // (CAP-2): `(= (str.indexof v "w" k) r)` with `r >= 0` forces
        // `v[r..r+|w|) = w`. The leftmost requirement (no earlier occurrence
        // in `[k, r)`) is handled by the fill-character search below plus the
        // strict re-validation.
        for io in &cons.indexofs {
            let Some(r) = io.result else { continue };
            for (i, ch) in io.needle.chars().enumerate() {
                if !pin(r + i, ch, &mut buf) {
                    return None;
                }
            }
        }
        // Prefixes pin positions from the front.
        for p in &cons.prefixes {
            let pchars: Vec<char> = p.chars().collect();
            if pchars.len() > required_len {
                return None;
            }
            for (i, &ch) in pchars.iter().enumerate() {
                if !pin(i, ch, &mut buf) {
                    return None;
                }
            }
        }
        // Suffixes pin positions from the back.
        for s in &cons.suffixes {
            let schars: Vec<char> = s.chars().collect();
            if schars.len() > required_len {
                return None;
            }
            let start = required_len - schars.len();
            for (i, &ch) in schars.iter().enumerate() {
                if !pin(start + i, ch, &mut buf) {
                    return None;
                }
            }
        }
        // Contains: place each required substring into a window of free (or
        // matching) positions. Best-effort — if it cannot be placed without
        // clobbering a forced position, leave it out and rely on strict
        // re-validation to reject an inconsistent witness.
        for c in &cons.contains {
            let cchars: Vec<char> = c.chars().collect();
            if cchars.is_empty() || cchars.len() > required_len {
                continue;
            }
            // Already present?
            if Self::window_present(&buf, &cchars) {
                continue;
            }
            let mut placed = false;
            for start in 0..=(required_len - cchars.len()) {
                if Self::window_compatible(&buf, start, &cchars) {
                    for (i, &ch) in cchars.iter().enumerate() {
                        buf[start + i] = Some(ch);
                    }
                    placed = true;
                    break;
                }
            }
            let _ = placed; // Inconsistency caught by strict re-validation.
        }

        // Fill free positions. The default fill character can accidentally
        // create an EARLIER occurrence of an indexof/contains needle (e.g.
        // needle "a" with FILL_CHAR 'a'), so when indexof constraints are
        // present, try a few candidate fill characters and keep the first
        // whose completed witness satisfies every recorded constraint. If
        // none does, fall back to the default fill — the strict substitution
        // re-validation remains the soundness gate either way.
        let complete =
            |fill: char| -> String { buf.iter().map(|slot| slot.unwrap_or(fill)).collect() };
        // W2: a language-constrained variable can NEVER be satisfied by a
        // uniform fill unless the pad letter happens to be in the language, so
        // construct the witness from the regex derivatives instead. Only
        // accepted when it satisfies EVERY other recorded constraint too;
        // otherwise the pre-existing fill path runs unchanged.
        if !cons.regexes.is_empty() {
            if let Some(w) = ay_strings::we_regex::find_witness_bounded(
                &cons.regexes,
                Some(required_len),
                required_len,
            ) {
                if Self::value_satisfies_constraints(&w, Some(required_len), cons) {
                    return Some(w);
                }
            }
        }
        if !cons.indexofs.is_empty() || !cons.to_ints.is_empty() || !cons.forbidden.is_empty() {
            // NF-engine closure 6 widens this candidate fill set: the default
            // `FILL_CHAR` may itself BE the forbidden needle (the pyex idiom
            // `¬contains(x, ",")` is fine, but `¬contains(x, "a")` is not), and
            // a uniform fill of a single character can only ever create the
            // needle when the needle is a repetition of that character. Trying
            // a handful of distinct letters therefore covers every single-char
            // and same-char-repetition needle; anything else falls through to
            // the pre-existing default fill, where the strict substitution
            // re-validation remains the gate. Each candidate is accepted only
            // after `value_satisfies_constraints` — which now enforces
            // `forbidden` exactly — so no unchecked value can escape.
            for fill in ['a', 'b', 'c', 'd', 'e'] {
                let candidate = complete(fill);
                if Self::value_satisfies_constraints(&candidate, Some(required_len), cons) {
                    return Some(candidate);
                }
            }
        }
        Some(complete(FILL_CHAR))
    }

    /// Whether the (partially-filled) buffer, once defaulted, already contains
    /// the substring `needle`. Only definite (`Some`) slots count as matches;
    /// `None` slots are treated as wildcards that do NOT count toward a
    /// guaranteed presence, so this returns true only when `needle` is fully
    /// pinned somewhere.
    fn window_present(buf: &[Option<char>], needle: &[char]) -> bool {
        if needle.is_empty() || needle.len() > buf.len() {
            return false;
        }
        (0..=(buf.len() - needle.len())).any(|start| {
            needle
                .iter()
                .enumerate()
                .all(|(i, &ch)| buf[start + i] == Some(ch))
        })
    }

    /// Whether `needle` can be written at `start` without overwriting any
    /// already-pinned slot that disagrees.
    fn window_compatible(buf: &[Option<char>], start: usize, needle: &[char]) -> bool {
        needle
            .iter()
            .enumerate()
            .all(|(i, &ch)| match buf[start + i] {
                Some(existing) => existing == ch,
                None => true,
            })
    }

    /// Collect HARD string constraints — those that must hold in every model
    /// of the formula — for the variables we plan to materialize.
    ///
    /// Only top-level conjuncts are hard: we descend exclusively through
    /// `and` (the formula is already FlattenAnd-split, but defensive
    /// recursion costs nothing). We deliberately do NOT descend into `or`,
    /// `=>`, `xor`, or `ite` branches — a constraint that only holds in one
    /// disjunct is NOT a guaranteed property of the witness, and treating it
    /// as such would pin a variable to a value (e.g. `(= x "")` inside the
    /// `str.len` bridge axiom `(or (= x "") (not (= (str.len x) 0)))`) that
    /// the rest of the formula forbids. The strict substitution re-validation
    /// remains the soundness gate; this collector only supplies *correct*
    /// hints so the witness is built right the first time.
    ///
    /// `positive` only ever reaches here as `true` for a hard conjunct;
    /// a single leading `not` is handled (so `(not (str.prefixof ...))` does
    /// not get mis-collected as a positive prefix).
    fn collect_string_constraints(
        &self,
        term: TermId,
        positive: bool,
        out: &mut HashMap<TermId, StringVarConstraints>,
    ) {
        match self.ctx.terms.get(term) {
            TermData::Not(inner) => {
                // A negated conjunct: flip polarity. We only collect *positive*
                // shape constraints, so a negated predicate contributes nothing
                // (handled by the `positive` guards below).
                self.collect_string_constraints(*inner, !positive, out);
            }
            TermData::App(Symbol::Named(name), args) => {
                // `str.in_re` is the ONE predicate collected in BOTH polarities
                // (W2): `WeRegex::comp` is exact over the full SMT-LIB
                // alphabet, so a hard `(not (str.in_re v R))` conjunct
                // constrains the witness just as precisely as the positive
                // form. Checked before the `positive` guard below for that
                // reason.
                if str_witness_w2()
                    && matches!(name.as_str(), "str.in_re" | "str.in.re")
                    && args.len() == 2
                {
                    self.collect_regex_membership(args[0], args[1], positive, out);
                    return;
                }
                // NF-engine closure 6 (`AY_STR_NF=1`): a hard NEGATED
                // `str.contains(v, c)` with a CONSTANT needle is the second
                // predicate collected in the negative polarity. Like
                // `str.in_re`, its negation is EXACTLY representable here (a
                // forbidden substring), so it must be checked BEFORE the
                // `positive` guard below discards negated predicates.
                if ay_strings::str_nf_closure_enabled(6)
                    && !positive
                    && name == "str.contains"
                    && args.len() == 2
                {
                    if let (TermData::Var(..), TermData::Const(Constant::String(c))) =
                        (self.ctx.terms.get(args[0]), self.ctx.terms.get(args[1]))
                    {
                        // The empty needle is a tautological `contains`, so its
                        // negation is unsatisfiable; recording it would make
                        // every candidate fail. Leave it to the strict
                        // re-validation, which rejects the assertion outright.
                        if !c.is_empty() {
                            if let Some(cons) = out.get_mut(&args[0]) {
                                cons.forbidden.push(c.clone());
                            }
                        }
                    }
                    return;
                }
                if !positive {
                    // Negated string predicates do not pin a forced shape we
                    // can exploit; rely on free-position defaults + strict
                    // re-validation instead.
                    return;
                }
                match name.as_str() {
                    "and" => {
                        // Hard conjunction: every conjunct is a hard constraint.
                        for &arg in args {
                            self.collect_string_constraints(arg, true, out);
                        }
                    }
                    "str.prefixof" if args.len() == 2 => {
                        if let (TermData::Const(Constant::String(c)), TermData::Var(..)) =
                            (self.ctx.terms.get(args[0]), self.ctx.terms.get(args[1]))
                        {
                            if let Some(cons) = out.get_mut(&args[1]) {
                                cons.prefixes.push(c.clone());
                            }
                        }
                    }
                    "str.suffixof" if args.len() == 2 => {
                        if let (TermData::Const(Constant::String(c)), TermData::Var(..)) =
                            (self.ctx.terms.get(args[0]), self.ctx.terms.get(args[1]))
                        {
                            if let Some(cons) = out.get_mut(&args[1]) {
                                cons.suffixes.push(c.clone());
                            }
                        }
                    }
                    "str.contains" if args.len() == 2 => {
                        if let (TermData::Var(..), TermData::Const(Constant::String(c))) =
                            (self.ctx.terms.get(args[0]), self.ctx.terms.get(args[1]))
                        {
                            if let Some(cons) = out.get_mut(&args[0]) {
                                cons.contains.push(c.clone());
                            }
                        }
                    }
                    "=" if args.len() == 2 => {
                        self.collect_equality_constraints(args[0], args[1], out);
                    }
                    // `or` / `=>` / `xor` / `ite`: NOT hard — do not descend.
                    _ => {}
                }
            }
            _ => {}
        }
    }

    /// Record a HARD `str.in_re` membership on a bare string variable (W2).
    ///
    /// `positive == false` records the EXACT complement, so `(not (str.in_re v
    /// R))` is as binding as the positive form. A subject that is not a plain
    /// variable we are materializing, or a regex `translate_we_regex` cannot
    /// render exactly, is skipped — dropping a constraint only makes the
    /// witness more likely to be rejected by the strict re-validation, never
    /// less.
    fn collect_regex_membership(
        &self,
        subject: TermId,
        regex: TermId,
        positive: bool,
        out: &mut HashMap<TermId, StringVarConstraints>,
    ) {
        if !matches!(self.ctx.terms.get(subject), TermData::Var(..)) {
            return;
        }
        let Some(cons) = out.get_mut(&subject) else {
            return;
        };
        if cons.regexes.len() >= MAX_WITNESS_REGEXES {
            return;
        }
        let Some(r) = self.translate_we_regex(regex, 0) else {
            return;
        };
        cons.regexes
            .push(if positive { r } else { WeRegex::comp(r) });
    }

    /// Handle `(= a b)` where one side is a string variable we are
    /// materializing: pin exact values, lengths, or forced-char positions.
    fn collect_equality_constraints(
        &self,
        a: TermId,
        b: TermId,
        out: &mut HashMap<TermId, StringVarConstraints>,
    ) {
        // (= (str.len v) N) -> exact length pin.
        for (lhs, rhs) in [(a, b), (b, a)] {
            if let TermData::App(Symbol::Named(name), largs) = self.ctx.terms.get(lhs) {
                if name == "str.len" && largs.len() == 1 {
                    let var = largs[0];
                    if out.contains_key(&var) {
                        if let TermData::Const(Constant::Int(n)) = self.ctx.terms.get(rhs) {
                            if n.sign() != num_bigint::Sign::Minus {
                                if let Ok(len) = usize::try_from(n.clone()) {
                                    out.get_mut(&var).unwrap().required_len = Some(len);
                                }
                            }
                        }
                    }
                }
            }
        }

        // (= v "const") -> fully pinned value.
        for (lhs, rhs) in [(a, b), (b, a)] {
            if let (TermData::Var(..), TermData::Const(Constant::String(s))) =
                (self.ctx.terms.get(lhs), self.ctx.terms.get(rhs))
            {
                if *self.ctx.terms.sort(lhs) == Sort::String && out.contains_key(&lhs) {
                    let cons = out.get_mut(&lhs).unwrap();
                    cons.pinned = Some(s.clone());
                    cons.required_len = Some(s.chars().count());
                }
            }
        }

        // (= (str.indexof v "w" k) r) -> indexof constraint (CAP-2): literal
        // needle, offset, and result. Only recorded when every piece is a
        // literal; anything symbolic is left to the theory solvers.
        for (lhs, rhs) in [(a, b), (b, a)] {
            if let TermData::App(Symbol::Named(name), largs) = self.ctx.terms.get(lhs) {
                if name == "str.indexof" && largs.len() == 3 {
                    let var = largs[0];
                    if out.contains_key(&var) {
                        if let (
                            TermData::Const(Constant::String(needle)),
                            TermData::Const(Constant::Int(off)),
                            TermData::Const(Constant::Int(res)),
                        ) = (
                            self.ctx.terms.get(largs[1]),
                            self.ctx.terms.get(largs[2]),
                            self.ctx.terms.get(rhs),
                        ) {
                            let needle = needle.clone();
                            let offset = usize::try_from(off.clone()).ok();
                            let result = if *res == BigInt::from(-1) {
                                Some(None)
                            } else {
                                usize::try_from(res.clone()).ok().map(Some)
                            };
                            if let (false, Some(offset), Some(result)) =
                                (needle.is_empty(), offset, result)
                            {
                                // A positive result before the offset can never
                                // hold; skip (strict re-validation rejects).
                                let consistent = match result {
                                    Some(r) => r >= offset,
                                    None => true,
                                };
                                if consistent {
                                    out.get_mut(&var).unwrap().indexofs.push(IndexofConstraint {
                                        needle,
                                        offset,
                                        result,
                                    });
                                }
                            }
                        }
                    }
                }
            }
        }

        // (= (str.to_int v) N) -> to_int constraint (extf wave 2): literal
        // result only; anything symbolic is left to the theory solvers.
        for (lhs, rhs) in [(a, b), (b, a)] {
            if let TermData::App(Symbol::Named(name), largs) = self.ctx.terms.get(lhs) {
                if (name == "str.to_int" || name == "str.to.int") && largs.len() == 1 {
                    let var = largs[0];
                    if out.contains_key(&var) {
                        if let TermData::Const(Constant::Int(res)) = self.ctx.terms.get(rhs) {
                            // to_int can only be -1 or non-negative; anything
                            // else is theory-level UNSAT, not a witness hint.
                            if *res >= BigInt::from(-1) {
                                out.get_mut(&var).unwrap().to_ints.push(res.clone());
                            }
                        }
                    }
                }
            }
        }

        // (= (str.at v i) "c") -> forced char at position i.
        for (lhs, rhs) in [(a, b), (b, a)] {
            if let TermData::App(Symbol::Named(name), largs) = self.ctx.terms.get(lhs) {
                if name == "str.at" && largs.len() == 2 {
                    let var = largs[0];
                    if out.contains_key(&var) {
                        if let (
                            TermData::Const(Constant::Int(idx)),
                            TermData::Const(Constant::String(ch)),
                        ) = (self.ctx.terms.get(largs[1]), self.ctx.terms.get(rhs))
                        {
                            if idx.sign() != num_bigint::Sign::Minus {
                                if let Ok(pos) = usize::try_from(idx.clone()) {
                                    let mut chars = ch.chars();
                                    if let (Some(c), None) = (chars.next(), chars.next()) {
                                        out.get_mut(&var).unwrap().forced.insert(pos, c);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    /// Commit materialized string values into the current model's
    /// `string_model`, creating it if necessary.
    fn commit_string_values(&mut self, values: &HashMap<TermId, String>) {
        if let Some(model) = self.last_model.as_mut() {
            let sm = model
                .string_model
                .get_or_insert_with(ay_strings::StringModel::default);
            for (&var, val) in values {
                sm.values.insert(var, val.clone());
            }
        }
    }

    /// Remove the given materialized values again (rollback on failed
    /// strict re-validation).
    fn rollback_string_values(&mut self, values: &HashMap<TermId, String>) {
        if let Some(model) = self.last_model.as_mut() {
            if let Some(sm) = model.string_model.as_mut() {
                for var in values.keys() {
                    sm.values.remove(var);
                }
            }
        }
    }

    /// Strict re-validation: every assertion must evaluate to `Bool(true)`
    /// under the now-concrete model, OR be genuinely undetermined for a
    /// non-string reason. Any assertion that evaluates to a definitive
    /// `Bool(false)` invalidates the materialization.
    ///
    /// This deliberately does NOT consult SAT-fallback: the freshly-concrete
    /// strings make string predicates authoritative, so a `false` here is a
    /// real violation, not a model-extraction gap.
    fn materialized_model_satisfies_assertions(&self, assertions: &[TermId]) -> bool {
        let Some(model) = self.last_model.as_ref() else {
            return false;
        };
        for &assertion in assertions {
            match self.evaluate_term(model, assertion) {
                EvalValue::Bool(true) => {}
                EvalValue::Bool(false) => return false,
                // Unknown: the assertion mixes in something we cannot fully
                // evaluate (e.g. an uninterpreted function over the string).
                // We do not block on it — the surrounding pipeline's
                // verify_model_strict / observation handling remains in force.
                // But if the assertion is a *purely string* predicate over our
                // now-concrete variables it should have resolved; treat an
                // Unknown purely-string assertion conservatively as a failure
                // so we never emit a model we could not confirm.
                _ => {
                    if self.assertion_is_pure_string_over_known(model, assertion) {
                        return false;
                    }
                }
            }
        }
        true
    }

    /// Whether `assertion` is a string predicate whose every string operand
    /// resolves to a concrete value in the current model. If so, an Unknown
    /// evaluation is suspicious (we expected resolution) and we fail closed.
    fn assertion_is_pure_string_over_known(&self, model: &Model, assertion: TermId) -> bool {
        // Only consider top-level string predicates; deeper Boolean structure
        // is handled by the surrounding pipeline.
        let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(assertion) else {
            return false;
        };
        if !matches!(
            name.as_str(),
            "str.prefixof" | "str.suffixof" | "str.contains" | "str.<" | "str.<=" | "str.in_re"
        ) {
            return false;
        }
        // Every string-sorted argument must resolve to a concrete string.
        args.iter().all(|&arg| {
            if *self.ctx.terms.sort(arg) == Sort::String {
                matches!(self.evaluate_term(model, arg), EvalValue::String(_))
            } else {
                true
            }
        })
    }
}

#[cfg(test)]
#[path = "string_materialize_tests.rs"]
mod tests;

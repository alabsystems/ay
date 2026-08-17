// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Strings increment P3: `str.to_int` / `str.from_int` digit-string ↔ LIA
//! coupling for NON-GROUND arguments (default ON, `--dpll-no-str-p3` kill switch).
//!
//! SMT-LIB semantics being encoded (the ONLY source of truth for every axiom
//! below): `(str.to_int s)` returns the non-negative decimal value of `s`
//! when `s` is a NONEMPTY sequence of digit characters `0x30..0x39` ONLY —
//! no sign, no leading `'+'`, no whitespace — and `-1` otherwise. Leading
//! zeros are allowed and contribute nothing: `to_int("00042") = 42`.
//! `(str.from_int n)` returns the canonical (shortest, no-leading-zero)
//! decimal string for `n >= 0` (`from_int(0) = "0"`) and `""` for `n < 0`.
//!
//! Every emitted formula is a UNIVERSALLY VALID theorem of that semantics,
//! so the package is a conservative extension: UNSAT derived with it stays
//! sound, and SAT still passes the definitive model-validation chokepoint
//! (the applications are marked reduced, so the strings core no longer
//! latches `incomplete` on them — their semantics live in the axioms plus
//! ground evaluation once arguments resolve).
//!
//! Detection is TERM-LEVEL (`TermData::App` symbol names), never textual —
//! the full_str_int corpus writes `( str.to_int` with an interior space, so
//! any string-based feature grep would miss it (census gotcha,
//! the development design notes).

// #8529: Use deterministic hash sets in all builds.
use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::{Constant, Symbol, TermData};
use ay_core::{Sort, TermId};
use num_bigint::BigInt;

use super::super::super::Executor;
use super::super::skolem_cache::ExecutorSkolemCache;
use super::super::strings_eval::{ground_eval_int_term, ground_eval_string_term};

// Test-only override so unit tests can exercise the P3 path without mutating
// process-global environment state (mirrors `STR_P2_TEST_OVERRIDE`).
#[cfg(test)]
thread_local! {
    pub(in crate::executor) static STR_P3_TEST_OVERRIDE: std::cell::Cell<bool> =
        const { std::cell::Cell::new(false) };
}

/// Strings increment P3 master switch (default ON, `--dpll-no-str-p3` kill switch).
///
/// Gates the eager NON-GROUND `str.to_int` / `str.from_int` digit-string
/// reasoning package (range, all-digits ↔ non-negative, decimal magnitude ↔
/// length coupling, `-1` propagation from non-digit witnesses, `from_int`
/// canonical-form + roundtrip axioms), wired as one more escalation pass in
/// `solve_strings_lia` after the P2 pass. `--dpll-no-str-p3` keeps the solve
/// pipeline byte-identical to pre-P3 behavior. P3 is gated independently of
/// `--dpll-no-str-p2` (its escalation pass collects the P2 reduction package itself
/// when the P2 gate is off — the substr length windows are what let LIA see
/// through `str.at`-shaped to_int arguments).
pub(in crate::executor) fn str_p3_enabled() -> bool {
    #[cfg(test)]
    if STR_P3_TEST_OVERRIDE.with(|c| c.get()) {
        return true;
    }
    // DEFAULT-ON since the measured sweep: 37/52 full_str_int + 12 in the P2
    // families = 49 conversions, every one z3-agreeing; 396-file solved
    // QF_S/QF_SLIA regression sweep with 0 losses (which is also the measured
    // answer to the verify-before-accept re-solve cost); 500-case differential
    // + pin-model fuzz clean. `--dpll-no-str-p3` is the kill switch.
    static V: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *V.get_or_init(|| !ay_core::theory_disable_flags().no_str_p3)
}

/// Largest digit count L for which the per-length magnitude coupling clauses
/// are instantiated (`10^L` fits comfortably in LIA; matches the strings
/// core's `MAX_TO_INT_DIGITS` on-demand bound). Strings longer than this keep
/// only the generic range/nonempty facts — sound fall-through, never a guess.
const P3_MAGNITUDE_DIGIT_CAP: usize = 16;

impl Executor {
    /// Strings increment P3: pre-register digit-string ↔ LIA coupling axioms
    /// for every NON-GROUND `str.to_int` / `str.from_int` application
    /// reachable from `assertions`.
    ///
    /// Returns `(reduction_axioms, reduced_term_ids)` exactly like
    /// [`Self::preregister_extf_reductions`]; the caller appends the axioms
    /// to the escalation assertion set and marks the ids reduced so the
    /// strings core stops latching `incomplete` on the applications.
    ///
    /// Axioms per `t = (str.to_int s)` (with `len_s = (str.len s)`):
    ///
    /// 1. Range: `t >= -1`. SMT-LIB: `t` is either `-1` (non-digit-string
    ///    case) or the value of a digit string, which is `>= 0`.
    /// 2. Nonempty: `t <= -1 ∨ len_s >= 1`. SMT-LIB: `""` is not a NONEMPTY
    ///    digit sequence, so `to_int("") = -1`; hence `t >= 0` forces `s`
    ///    nonempty.
    /// 3. All-digits ↔ non-negative (both directions, via the digit regex
    ///    `[0-9]+`): `t <= -1 ∨ s ∈ [0-9]+` and `s ∈ [0-9]+ → t >= 0`.
    ///    SMT-LIB: `t >= 0` holds IFF `s` is a nonempty all-digit string —
    ///    exactly membership in `(re.+ (re.range "0" "9"))`. No sign and no
    ///    leading `'+'` are ever accepted, so the digit class alone is exact.
    /// 4. Magnitude upper bound, for `L` in `0..=CAP`:
    ///    `len_s > L ∨ t <= 10^L - 1`. SMT-LIB: if `len(s) <= L` then either
    ///    `t = -1 <= 10^L - 1`, or `s` is all digits of length `k <= L` and
    ///    its decimal value is `< 10^k <= 10^L` (leading zeros only shrink
    ///    the value, so this holds for zero-padded forms too).
    /// 5. Magnitude lower bound for no-leading-zero forms, `L` in `1..=CAP`:
    ///    `t <= -1 ∨ (str.prefixof "0" s) ∨ len_s < L ∨ t >= 10^(L-1)`.
    ///    SMT-LIB: `t >= 0` makes `s` nonempty all-digits; if additionally
    ///    `s` does not start with `'0'`, its first digit is in `1..=9`, so
    ///    `t >= 1·10^(len_s - 1) >= 10^(L-1)` whenever `len_s >= L`. (The
    ///    census's "no-leading-zero forms" half of the magnitude coupling;
    ///    `to_int("00042") = 42` shows why the guard is required.)
    /// 6. `-1` propagation from non-digit witnesses: for every ALREADY
    ///    PRESENT atom `(str.prefixof c s)` / `(str.suffixof c s)` /
    ///    `(str.contains s c)` whose constant `c` contains a non-digit
    ///    character: `atom → t = -1`. SMT-LIB: the atom (when true) embeds
    ///    `c` — hence a non-digit character — inside `s`, so `s` is not an
    ///    all-digit string and `to_int(s) = -1`. Only existing atoms are
    ///    used, so no fresh predicate is ever introduced by this rule (the
    ///    ubiquitous full_str_int idiom `(str.prefixof "-" x)` guarding
    ///    `(str.to_int x)` is exactly this shape).
    ///
    /// Axioms per `r = (str.from_int n)`:
    ///
    /// 7. Negative: `n >= 0 ∨ r = ""`. SMT-LIB definition.
    /// 8. Roundtrip: `n < 0 ∨ (str.to_int r) = n`. SMT-LIB: for `n >= 0`,
    ///    `r` is the canonical decimal of `n` — nonempty, all digits — and
    ///    `to_int` of a canonical decimal is its value `n`. The minted
    ///    `to_int(r)` application is fed back into the to_int loop above, so
    ///    it receives the full coupling package and is marked reduced.
    /// 9. Nonempty: `n < 0 ∨ len_r >= 1` (canonical decimals are nonempty,
    ///    `from_int(0) = "0"`).
    /// 10. Zero: `n ≠ 0 ∨ r = "0"` (SMT-LIB pins the zero case exactly).
    /// 11. No leading zero: `n < 1 ∨ ¬(str.prefixof "0" r)`. SMT-LIB: for
    ///     `n >= 1` the canonical decimal starts with a digit in `1..=9`.
    /// 12. Digit-count coupling, for `L` in `1..=CAP`:
    ///     - `n < 0 ∨ n >= 10^L ∨ len_r <= L` (a value below `10^L` prints
    ///       in at most `L` digits; `n = 0` prints as one digit `<= L`);
    ///     - `n < 10^L ∨ len_r >= L + 1` (a value at or above `10^L` needs
    ///       at least `L+1` digits).
    /// 13. NF bridge: `r = sk` for a cached fresh string skolem, plus the
    ///     `lengthPositive` bridges — same pattern as the P2
    ///     `replace_re` reduction: gives the application's EQC a plain
    ///     string variable so normal-form computation does not bail
    ///     (Incomplete) on an opaque extf component.
    ///
    /// Internal guard atoms minted here (`str.prefixof "0" _`) are marked
    /// reduced exactly like the P2 indexof guards: they are enforced by
    /// ground predicate evaluation once values resolve plus the
    /// model-validation chokepoint, and marking them keeps the extf pass
    /// from latching `incomplete` on them. Marking can only LOSE pruning
    /// power, never soundness: every clause here is valid under the real
    /// semantics, so adding it (however weakly its atoms are enforced)
    /// never excludes a real model.
    pub(in crate::executor) fn preregister_to_int_reductions(
        &mut self,
        assertions: &[TermId],
        skolem_cache: &mut ExecutorSkolemCache,
    ) -> (Vec<TermId>, Vec<TermId>) {
        let mut reductions: Vec<TermId> = Vec::new();
        let mut reduced_term_ids: Vec<TermId> = Vec::new();

        // ------------------------------------------------------------------
        // Collection (term-level DFS — never textual; census gotcha).
        // ------------------------------------------------------------------
        let mut stack: Vec<TermId> = assertions.to_vec();
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut seen_to_int: HashSet<TermId> = HashSet::default();
        let mut seen_from_int: HashSet<TermId> = HashSet::default();
        let mut to_int_terms: Vec<(TermId, TermId)> = Vec::new(); // (t, s)
        let mut from_int_terms: Vec<(TermId, TermId)> = Vec::new(); // (r, n)
                                                                    // (witness_atom, haystack): positive occurrence of the atom proves a
                                                                    // non-digit character inside the haystack (rule 6).
        let mut nondigit_witness_atoms: Vec<(TermId, TermId)> = Vec::new();

        let literal_has_nondigit = |s: &str| s.chars().any(|c| !c.is_ascii_digit());

        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }
            match self.ctx.terms.get(term) {
                TermData::App(Symbol::Named(name), args) => {
                    if (name == "str.to_int" || name == "str.to.int")
                        && args.len() == 1
                        && seen_to_int.insert(term)
                    {
                        // Ground applications fold via Wave 0 /
                        // ground_eval_int_term — nothing to couple.
                        if ground_eval_int_term(&self.ctx.terms, term).is_none() {
                            to_int_terms.push((term, args[0]));
                        }
                    } else if (name == "str.from_int" || name == "int.to.str")
                        && args.len() == 1
                        && seen_from_int.insert(term)
                    {
                        if ground_eval_string_term(&self.ctx.terms, term).is_none() {
                            from_int_terms.push((term, args[0]));
                        }
                    } else if (name == "str.prefixof" || name == "str.suffixof") && args.len() == 2
                    {
                        // (str.prefixof c x) / (str.suffixof c x): c = needle,
                        // x = haystack. A true atom with a non-digit-bearing
                        // constant needle witnesses a non-digit char in x.
                        if matches!(
                            self.ctx.terms.get(args[0]),
                            TermData::Const(Constant::String(c)) if literal_has_nondigit(c)
                        ) {
                            nondigit_witness_atoms.push((term, args[1]));
                        }
                    } else if name == "str.contains" && args.len() == 2 {
                        // (str.contains x c): x = haystack, c = needle.
                        if matches!(
                            self.ctx.terms.get(args[1]),
                            TermData::Const(Constant::String(c)) if literal_has_nondigit(c)
                        ) {
                            nondigit_witness_atoms.push((term, args[0]));
                        }
                    }
                    let args_copy: Vec<TermId> = args.clone();
                    for arg in args_copy {
                        stack.push(arg);
                    }
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                TermData::Let(bindings, body) => {
                    let binding_vals: Vec<TermId> = bindings.iter().map(|(_, v)| *v).collect();
                    let body_id = *body;
                    for val in binding_vals {
                        stack.push(val);
                    }
                    stack.push(body_id);
                }
                _ => {}
            }
        }

        if to_int_terms.is_empty() && from_int_terms.is_empty() {
            return (reductions, reduced_term_ids);
        }

        // ------------------------------------------------------------------
        // from_int axioms first: rule 8 mints `to_int(r)` applications that
        // must join the to_int loop below (deduped through `seen_to_int`).
        // ------------------------------------------------------------------
        for &(r, n) in &from_int_terms {
            reduced_term_ids.push(r);

            let zero = self.ctx.terms.mk_int(BigInt::from(0));
            let one = self.ctx.terms.mk_int(BigInt::from(1));
            let empty = self.ctx.terms.mk_string(String::new());
            let n_lt_0 = self.ctx.terms.mk_lt(n, zero);
            let n_ge_0 = self.ctx.terms.mk_ge(n, zero);
            let len_r = self
                .ctx
                .terms
                .mk_app(Symbol::named("str.len"), vec![r], Sort::Int);

            // Rule 7: from_int of a negative is "".
            let r_eq_empty = self.ctx.terms.mk_eq(r, empty);
            reductions.push(self.ctx.terms.mk_or(vec![n_ge_0, r_eq_empty]));

            // Rule 8: roundtrip to_int(from_int(n)) = n for n >= 0.
            let to_int_r = self
                .ctx
                .terms
                .mk_app(Symbol::named("str.to_int"), vec![r], Sort::Int);
            let roundtrip = self.ctx.terms.mk_eq(to_int_r, n);
            reductions.push(self.ctx.terms.mk_or(vec![n_lt_0, roundtrip]));
            // Feed the minted application into the to_int loop below so it
            // gets the full coupling package and the reduced marker.
            if seen_to_int.insert(to_int_r)
                && ground_eval_int_term(&self.ctx.terms, to_int_r).is_none()
            {
                to_int_terms.push((to_int_r, r));
            }

            // Rule 9: canonical decimals are nonempty for n >= 0.
            let len_r_ge_1 = self.ctx.terms.mk_ge(len_r, one);
            reductions.push(self.ctx.terms.mk_or(vec![n_lt_0, len_r_ge_1]));

            // Rule 10: from_int(0) = "0".
            let n_eq_0 = self.ctx.terms.mk_eq(n, zero);
            let not_n_eq_0 = self.ctx.terms.mk_not(n_eq_0);
            let zero_str = self.ctx.terms.mk_string("0".to_string());
            let r_eq_zero_str = self.ctx.terms.mk_eq(r, zero_str);
            reductions.push(self.ctx.terms.mk_or(vec![not_n_eq_0, r_eq_zero_str]));

            // Rule 11: no leading zero for n >= 1.
            let n_lt_1 = self.ctx.terms.mk_lt(n, one);
            let zero_str2 = self.ctx.terms.mk_string("0".to_string());
            let prefix0_r = self.ctx.terms.mk_app(
                Symbol::named("str.prefixof"),
                vec![zero_str2, r],
                Sort::Bool,
            );
            // Internal guard atom (same treatment as the P2 indexof guards).
            reduced_term_ids.push(prefix0_r);
            let not_prefix0_r = self.ctx.terms.mk_not(prefix0_r);
            reductions.push(self.ctx.terms.mk_or(vec![n_lt_1, not_prefix0_r]));

            // Rule 12: digit-count coupling per candidate length L.
            for l in 1..=P3_MAGNITUDE_DIGIT_CAP {
                let pow10_l = BigInt::from(10u32).pow(l as u32);
                let pow_term = self.ctx.terms.mk_int(pow10_l);
                let l_term = self.ctx.terms.mk_int(BigInt::from(l));
                // 0 <= n < 10^L → len(r) <= L.
                let n_ge_pow = self.ctx.terms.mk_ge(n, pow_term);
                let len_le_l = self.ctx.terms.mk_le(len_r, l_term);
                reductions.push(self.ctx.terms.mk_or(vec![n_lt_0, n_ge_pow, len_le_l]));
                // n >= 10^L → len(r) >= L + 1.
                let n_lt_pow = self.ctx.terms.mk_lt(n, pow_term);
                let l_plus_1 = self.ctx.terms.mk_int(BigInt::from(l + 1));
                let len_ge_l1 = self.ctx.terms.mk_ge(len_r, l_plus_1);
                reductions.push(self.ctx.terms.mk_or(vec![n_lt_pow, len_ge_l1]));
            }

            // Rule 13: NF bridge to a plain string variable + lengthPositive.
            let rsk = skolem_cache.from_int_result(&mut self.ctx.terms, r);
            let bridge = self.ctx.terms.mk_eq(r, rsk);
            reductions.push(bridge);
            let len_rsk = self
                .ctx
                .terms
                .mk_app(Symbol::named("str.len"), vec![rsk], Sort::Int);
            let zero_lp = self.ctx.terms.mk_int(BigInt::from(0));
            reductions.push(self.ctx.terms.mk_ge(len_rsk, zero_lp));
            let len_eq_zero = self.ctx.terms.mk_eq(len_rsk, zero_lp);
            let empty_lp = self.ctx.terms.mk_string(String::new());
            let rsk_eq_empty = self.ctx.terms.mk_eq(rsk, empty_lp);
            reductions.push(self.ctx.terms.mk_implies(len_eq_zero, rsk_eq_empty));
            reductions.push(self.ctx.terms.mk_implies(rsk_eq_empty, len_eq_zero));
        }

        // ------------------------------------------------------------------
        // to_int axioms (including roundtrip-minted applications).
        // ------------------------------------------------------------------
        for &(t, s) in &to_int_terms {
            reduced_term_ids.push(t);

            let neg_one = self.ctx.terms.mk_int(BigInt::from(-1));
            let len_s = self
                .ctx
                .terms
                .mk_app(Symbol::named("str.len"), vec![s], Sort::Int);
            let t_le_neg1 = self.ctx.terms.mk_le(t, neg_one);

            // Rule 1: range.
            reductions.push(self.ctx.terms.mk_ge(t, neg_one));

            // Rule 2: t >= 0 → s nonempty.
            let one = self.ctx.terms.mk_int(BigInt::from(1));
            let len_ge_1 = self.ctx.terms.mk_ge(len_s, one);
            reductions.push(self.ctx.terms.mk_or(vec![t_le_neg1, len_ge_1]));

            // Rule 3: all-digits ↔ non-negative, via s ∈ (re.+ (re.range "0" "9")).
            let zero_ch = self.ctx.terms.mk_string("0".to_string());
            let nine_ch = self.ctx.terms.mk_string("9".to_string());
            let re_digit = self.ctx.terms.mk_app(
                Symbol::named("re.range"),
                vec![zero_ch, nine_ch],
                Sort::RegLan,
            );
            let re_digits_plus =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("re.+"), vec![re_digit], Sort::RegLan);
            let membership = self.ctx.terms.mk_app(
                Symbol::named("str.in_re"),
                vec![s, re_digits_plus],
                Sort::Bool,
            );
            reductions.push(self.ctx.terms.mk_or(vec![t_le_neg1, membership]));
            let not_membership = self.ctx.terms.mk_not(membership);
            let zero_t = self.ctx.terms.mk_int(BigInt::from(0));
            let t_ge_0 = self.ctx.terms.mk_ge(t, zero_t);
            reductions.push(self.ctx.terms.mk_or(vec![not_membership, t_ge_0]));

            // Rule 5's leading-zero guard atom, shared across all L.
            let zero_str = self.ctx.terms.mk_string("0".to_string());
            let prefix0_s =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("str.prefixof"), vec![zero_str, s], Sort::Bool);
            // Internal guard atom (see doc comment).
            reduced_term_ids.push(prefix0_s);

            for l in 0..=P3_MAGNITUDE_DIGIT_CAP {
                let pow10_l = BigInt::from(10u32).pow(l as u32);
                // Rule 4: len(s) <= L → t <= 10^L - 1.
                let l_term = self.ctx.terms.mk_int(BigInt::from(l));
                let len_gt_l = self.ctx.terms.mk_gt(len_s, l_term);
                let pow_minus_1 = self.ctx.terms.mk_int(&pow10_l - BigInt::from(1));
                let t_le_pow = self.ctx.terms.mk_le(t, pow_minus_1);
                reductions.push(self.ctx.terms.mk_or(vec![len_gt_l, t_le_pow]));

                // Rule 5: no-leading-zero lower bound (L >= 1 only).
                if l >= 1 {
                    let pow10_lm1 = BigInt::from(10u32).pow((l - 1) as u32);
                    let l_term2 = self.ctx.terms.mk_int(BigInt::from(l));
                    let len_lt_l = self.ctx.terms.mk_lt(len_s, l_term2);
                    let pow_lm1_term = self.ctx.terms.mk_int(pow10_lm1);
                    let t_ge_pow = self.ctx.terms.mk_ge(t, pow_lm1_term);
                    reductions.push(
                        self.ctx
                            .terms
                            .mk_or(vec![t_le_neg1, prefix0_s, len_lt_l, t_ge_pow]),
                    );
                }
            }

            // Rule 6: -1 propagation from existing non-digit witness atoms.
            let t_eq_neg1 = self.ctx.terms.mk_eq(t, neg_one);
            for &(atom, hay) in &nondigit_witness_atoms {
                if hay != s {
                    continue;
                }
                let not_atom = self.ctx.terms.mk_not(atom);
                reductions.push(self.ctx.terms.mk_or(vec![not_atom, t_eq_neg1]));
            }
        }

        (reductions, reduced_term_ids)
    }
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! W6 — digit/arithmetic-aware and regex-word witness moves
//! (default ON, `AY_STR_W6=0` kill switch).
//!
//! ## The measured gap W6 closes
//!
//! W4 ([`super::strings_w4`]) converted 31 of the 92 sat-side strings misses by
//! hill-climbing ONE CHARACTER POSITION per violated atom; W5
//! ([`super::strings_w5`]) converted 31 of the remaining 58 by searching WHERE a
//! needle lands. The W5 report characterised the 27-file residue as three
//! distinct shapes, and W6 attacks the two with concrete leads:
//!
//! * **(A) 11 `full_str_int` files.** `str.to_int` over `str.substr`/`str.at`
//!   windows, plus linear arithmetic over `str.len`, and (on the `add_binary`
//!   family) `(str.in_re v (re.+ (re.range "0" "1")))`. W4/W5 both propose
//!   characters from the FORMULA ALPHABET or a fresh out-of-alphabet letter —
//!   and `str.to_int` of anything that is not a digit string is `-1`, so every
//!   proposal is refuted by the very atom it was meant to repair. The repair
//!   must propose DIGIT STRINGS satisfying the numeric constraint.
//! * **(B) 9 regex-driven files** (4 slog, 4 stringfuzz, 1 Norn). The W4
//!   targeting gate declines regex+length-only formulas outright, and the slog
//!   `stranger_*_sink` chains hide everything behind a DISJUNCTION, so the
//!   forced-literal closure sees none of it. W6 adds a separate, last-resort
//!   pre-pass that builds a word of each membership language directly.
//!
//! Shape (C) — 7 kaluza/PyEx/Kepler/Leetcode files whose plateau is wider than
//! one atom — was attempted (a wider sideways-move tolerance) and MEASURED to
//! convert nothing while letting the climb wander out of W5's basin; the
//! widening is not shipped and W4's calibration is kept exactly.
//!
//! ## What W6 adds (all four ride W4's loop and W4's scoring unchanged)
//!
//! 1. **Numeric window fills** — when a violated atom READS a window of the
//!    target numerically (`str.to_int` anywhere in its tree, or a digit-class
//!    `str.in_re`), propose decimal texts for that window: length-preserving
//!    patterns (`10…0`, `0…0`, `9…9`) and the decimals of the integer constants
//!    the atom itself mentions (and their ±1 neighbours — the `≤ 255` / `< 2`
//!    bounds of this family are all met by a boundary value).
//! 2. **Regex word fills** — a violated `(str.in_re W R)` over a window `W` of
//!    the target is repaired by OVERWRITING the window with a word of `R`,
//!    obtained from `translate_we_regex` + a structural shortest-word walk
//!    ([`w6_shortest_word`]) and from `find_witness_bounded` at the window's
//!    current length. Both are re-checked with `WeRegex::matches` before use.
//! 3. **Generalised length nudges** — W4's length arm only matches an atom
//!    whose immediate child is `(str.len W)` compared against an integer
//!    literal. This family writes `(>= (+ (str.len a) (- (- 1) 1)) 0)`, so the
//!    arm never fires. W6 instead nudges the length of EVERY window of the
//!    target the atom mentions, by ±1/±2, and lets W4's violation count decide.
//! 4. **Negative window pins** — `(not (= W "c"))` for a window `W` (the
//!    `str.at`-rewritten-to-`str.substr` spelling this family uses for
//!    "no leading zero") is declined by every W4 arm (its `(= W lit)` arm is
//!    `pol`-positive only) and by every W5 arm (both sides must be windows).
//!    W6 changes the window's content away from the literal, preferring a
//!    DIGIT for a numerically-read variable.
//!
//! 5. **A regex-word pre-pass** ([`Executor::try_regex_word_witnesses`]) for
//!    shape (B): a word per variable from its own membership language, built
//!    STRUCTURALLY over the regex TERM ([`Executor::w6_term_word`]) rather than
//!    by the derivative BFS — the stringfuzz `regexsmall`/`regexlengths` chains
//!    exceed `translate_we_regex`'s node cap and need 30-80 character words —
//!    plus the slog `str.++`-chain construction, which plants a membership's
//!    required literal in the chain's FREE operand and resolves the chain's
//!    disjunctions by choosing an alternative. It runs LAST, after every other
//!    witness pre-pass, so it can only spend budget on formulas nothing else
//!    decides.
//!
//! Plus one calibration widening, flag-gated so W5-only runs are byte-identical:
//! more scored repairs per round (W6 proposes a value per atom, not a
//! character). W6's per-atom moves are consulted ONLY where BOTH W4 and W5
//! decline — the same discipline by which W5 is consulted only where W4
//! declines — so W5's own conversions are untouched.
//!
//! ## Soundness contract (inherited from W4/W5, NOT weakened)
//!
//! W6 only ever proposes CANDIDATE assignments, scored by W4's
//! definitive-violation count and accepted only by W4's single exit,
//! [`Executor::finalize_sat_model_validation`]. Specifically:
//!
//! * **No inner solve.** W6 never pins a candidate as an assumption and
//!   re-solves (the route W4 measured leaking a refutation into the outer
//!   verdict — a wrong `unsat` on `kaluza/sat/small/bettermatch1`).
//! * **Memo discipline.** Every evaluation epoch stays inside W4's
//!   `w4_memo_reset` brackets; W6 adds no epoch of its own — it is called from
//!   inside `w4_repair_var`'s already-bracketed atom loop, and its own pre-pass
//!   brackets each trial model exactly as `w4_validate_candidates` does.
//! * **A failed construction never justifies UNSAT.** W6's only outcomes are
//!   "a validated model" or "nothing".
//! * **No guard removed.** W4's targeting gate is not relaxed; W6 only ADDS
//!   evidence kinds to it under `AY_STR_W6=1`, exactly as W5 did.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Constant, Symbol, TermData, TermId};
use ay_core::Sort;
use ay_strings::we_regex::{find_witness_bounded, WeRegex};

use crate::executor_types::{Result, SolveResult};

use super::super::model::{EvalValue, Model};
use super::super::Executor;
use super::strings_w4::{w4_memo_reset, w4_trial_model, MAX_W4_LEN};

/// Master switch (default ON, `AY_STR_W6=0` kill switch → byte-identical to W5-only).
pub(in crate::executor) fn str_w6_enabled() -> bool {
    static V: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    // DEFAULT-ON: 16 of the last 27 sat-side misses convert, ALL 16 confirmed
    // by AY's own fail-closed `--self-check` (not z3); +17 decided on the
    // 600-file sweep with 0 losses and 0 soundness flips; flags-off identity
    // measured 600/600. AY_STR_W6=0 is the kill switch.
    *V.get_or_init(|| !matches!(std::env::var("AY_STR_W6").ok().as_deref(), Some("0")))
}

/// Windows of the target one violated atom may be repaired through.
const MAX_W6_WINDOWS: usize = 8;

/// Integer constants harvested from one atom as numeric targets.
const MAX_W6_INTS: usize = 8;

/// Candidate values one violated atom may propose.
const MAX_W6_CANDIDATES: usize = 28;

/// Longest decimal text W6 will write into a window.
const MAX_W6_NUM_LEN: usize = 12;

/// Repairs scored per round under W6 (W4's own cap is 10 — calibrated for a
/// one-atom plateau, and W6 proposes a wider neighbourhood per atom).
pub(super) const MAX_W6_REPAIRS: usize = 28;

/// Node budget for the per-atom window walk. The pyex deep-chain atoms are
/// thousands of nodes and the walk EVALUATES each string subterm, so an
/// over-generous budget exhausts the solve budget outright (measured: 24 lost
/// `httplib2-entry-disposition` conversions at 2048).
const MAX_W6_WALK_BUDGET: usize = 384;

/// Longest regex word W6 will write into a window.
const MAX_W6_REGEX_LEN: usize = 32;

/// Search depth for the derivative BFS when a structural shortest word is not
/// available (or is the wrong length).
const MAX_W6_WITNESS_DEPTH: usize = 12;

/// String variables the regex-word pre-pass will handle jointly.
const MAX_W6_VARS: usize = 48;

/// Joint candidates the regex-word pre-pass hands to validation.
const MAX_W6_WORD_CANDIDATES: usize = 16;

/// Candidate cap for the EARLY W6 shortcut ([`Executor::try_w6_early_shortcut`]),
/// which runs ahead of the Nielsen exhaust and so must bound its own
/// validation cost. The SAT targets decide on the first one or two candidates
/// (the shortest concat needle-plant / reps=0 skeleton word); anything beyond
/// the cap is left to the late W6 pass, which validates the full set.
const MAX_W6_EARLY_VALIDATIONS: usize = 8;

/// Longest word the regex-word pre-pass will build. Much larger than
/// [`MAX_W4_LEN`]: this is a WHOLE-VARIABLE value, and the stringfuzz
/// `regexlengths` family pins `(<= 51 (str.len var0))` on a 50-way `re.++`.
const MAX_W6_WORD_LEN: usize = 512;

/// Star/plus repetition counts tried when building a regex word. Growing the
/// repetition is the only way to satisfy a LENGTH LOWER BOUND on a membership
/// whose shortest word is too short.
const W6_WORD_REPS: [usize; 6] = [0, 1, 2, 3, 6, 12];

/// String variables `try_per_position_witnesses` handles jointly under W6
/// (W4's own cap is 8; the `lib_int-ipaddress` family declares 9). A work
/// bound only — a bigger set is simply more repair work, never a soundness
/// question, since every candidate still rides the full validation battery.
pub(super) const MAX_W6_SYNTH_VARS: usize = 12;

/// Needles harvested from a membership regex for the concat construction.
const MAX_W6_SLOG_NEEDLES: usize = 4;

/// Propagation rounds for the concat chain. Each round advances the chain by
/// ONE level (the trial model is rebuilt per round), and the slog chains are
/// ~10 definitions deep.
const MAX_W6_PROPAGATE_ROUNDS: usize = 24;

/// Defining equations followed by the concat construction.
const MAX_W6_DEFS: usize = 64;

/// Length cap for a PROPAGATED chain value. Much larger than
/// [`MAX_W6_WORD_LEN`]: the slog `stranger_*_sink` chains concatenate a dozen
/// ~100-character HTML literals, so the sink variable's value runs to a few
/// thousand characters — refusing to record it left the sink at `""` and every
/// candidate was refuted by its own defining equation.
const MAX_W6_CHAIN_LEN: usize = 8192;

impl Executor {
    // ───────────────────────── repair moves (in W4's loop) ─────────────────

    /// The repair candidates W4's and W5's arms structurally cannot express.
    ///
    /// Unlike `w4_repair_atom`/`w5_repair_atom` this returns a LIST: the
    /// numeric family's constraint is a VALUE, not a character, and the right
    /// value is chosen by W4's violation count, not by this function.
    ///
    /// `numeric` is the set of variables some entailed atom reads numerically
    /// (`str.to_int` over a window rooted at the variable, or a digit-class
    /// `str.in_re`) — for those, filler characters must be DIGITS or every
    /// proposal is refuted by the `str.to_int = -1` atom it was meant to fix.
    pub(super) fn w6_repair_candidates(
        &self,
        model: &Model,
        atom: TermId,
        pol: bool,
        target: TermId,
        cur: &[char],
        numeric: bool,
        fresh: char,
    ) -> Vec<Vec<char>> {
        let mut out: Vec<Vec<char>> = Vec::new();
        // CHEAP DISPATCH FIRST. The window walk below evaluates every string
        // subterm of the atom, and the pyex deep-chain atoms are thousands of
        // nodes inside W5's 48-placement search — running it on atoms W6 has no
        // move for cost 24 `httplib2-entry-disposition` conversions outright.
        // W6 only ever has something to say about a NUMERICALLY-read variable,
        // a membership, or a negative window pin.
        let head = match self.ctx.terms.get(atom) {
            TermData::App(Symbol::Named(n), a) => Some((n.as_str(), a.len())),
            _ => None,
        };
        let targeted = numeric
            || matches!(head, Some(("str.in_re" | "str.in.re", 2)))
            || (!pol && matches!(head, Some(("=", 2))) && self.w6_has_string_const(atom));
        if !targeted {
            return out;
        }
        let windows = self.w6_windows(model, atom, target);
        if windows.is_empty() {
            return out;
        }

        // (2) regex word fills for a violated positive membership.
        self.w6_regex_fills(model, atom, pol, target, cur, &mut out);

        // (4) negative window pin: `(not (= W "c"))`.
        self.w6_negative_pin_fills(model, atom, pol, target, cur, numeric, fresh, &mut out);

        let reads_num = numeric || self.w6_reads_numerically(atom);
        let ints = self.w6_int_constants(atom);
        let fill = if reads_num { '0' } else { fresh };

        for &(origin, have) in &windows {
            // (1) numeric window fills.
            if reads_num {
                for text in w6_digit_texts(have, &ints) {
                    let chars: Vec<char> = text.chars().collect();
                    w6_push_window(cur, origin, have, &chars, &mut out);
                }
            }
            // (3) generalised length nudges.
            for delta in [1i64, -1, 2, -2, 3, -3] {
                let want = match usize::try_from(have as i64 + delta) {
                    Ok(w) if w <= MAX_W4_LEN => w,
                    _ => continue,
                };
                let Some(body) = w6_resize_body(cur, origin, have, want, fill) else {
                    continue;
                };
                w6_push_window(cur, origin, have, &body, &mut out);
            }
        }
        out.truncate(MAX_W6_CANDIDATES);
        out
    }

    /// Overwrite a window with a word of the membership regex it violates.
    fn w6_regex_fills(
        &self,
        model: &Model,
        atom: TermId,
        pol: bool,
        target: TermId,
        cur: &[char],
        out: &mut Vec<Vec<char>>,
    ) {
        if !pol {
            return;
        }
        let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(atom) else {
            return;
        };
        if (name != "str.in_re" && name != "str.in.re") || args.len() != 2 {
            return;
        }
        let Some(origin) = self.w4_origin(model, args[0], target, 0) else {
            return;
        };
        let Some(cur_val) = self.w4_eval_string(model, args[0]) else {
            return;
        };
        let have = cur_val.chars().count();
        let Some(regex) = self.translate_we_regex(args[1], 0) else {
            return;
        };
        let mut words: Vec<String> = Vec::new();
        if let Some(w) = w6_shortest_word(&regex, 0) {
            words.push(w);
        }
        // A word of the window's CURRENT length keeps every length atom the
        // climb has already satisfied.
        for len in [have, have + 1] {
            if len <= MAX_W6_REGEX_LEN {
                if let Some(w) = find_witness_bounded(
                    std::slice::from_ref(&regex),
                    Some(len),
                    len.max(MAX_W6_WITNESS_DEPTH),
                ) {
                    words.push(w);
                }
            }
        }
        for w in words {
            if w.chars().count() > MAX_W6_REGEX_LEN {
                continue;
            }
            // Re-check: a structural shortest word is only used when the exact
            // matcher confirms it (`None` = size cap tripped = no information).
            if regex.matches(&w) != Some(true) {
                continue;
            }
            let chars: Vec<char> = w.chars().collect();
            w6_push_window(cur, origin, have, &chars, out);
        }
    }

    /// `(not (= W "c"))` for a window `W` of the target: move the window's
    /// content off the literal. W4's `(= W lit)` arm is positive-only and W5's
    /// coupling arm needs windows on BOTH sides, so nothing else covers it.
    #[allow(clippy::too_many_arguments)]
    fn w6_negative_pin_fills(
        &self,
        model: &Model,
        atom: TermId,
        pol: bool,
        target: TermId,
        cur: &[char],
        numeric: bool,
        fresh: char,
        out: &mut Vec<Vec<char>>,
    ) {
        if pol {
            return;
        }
        let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(atom) else {
            return;
        };
        if name != "=" || args.len() != 2 {
            return;
        }
        for (lhs, rhs) in [(args[0], args[1]), (args[1], args[0])] {
            let Some(lit) = self.w4_string_const(rhs) else {
                continue;
            };
            if *self.ctx.terms.sort(lhs) != Sort::String {
                continue;
            }
            let Some(origin) = self.w4_origin(model, lhs, target, 0) else {
                continue;
            };
            let Some(have_s) = self.w4_eval_string(model, lhs) else {
                continue;
            };
            if have_s != lit {
                continue; // already different — nothing to repair.
            }
            let have = have_s.chars().count();
            let banned: char = lit.chars().next().unwrap_or(fresh);
            let choices: [char; 4] = if numeric {
                ['1', '2', '9', '0']
            } else {
                [fresh, 'a', 'b', 'z']
            };
            for ch in choices {
                if ch == banned {
                    continue;
                }
                let mut body: Vec<char> = have_s.chars().collect();
                if body.is_empty() {
                    body.push(ch);
                } else {
                    body[0] = ch;
                }
                w6_push_window(cur, origin, have, &body, out);
            }
        }
    }

    // ───────────────────────────── analysis ───────────────────────────────

    /// Every window of `target` (`str.substr`/`str.at` chain, or `target`
    /// itself) that `atom` mentions, as `(origin, length)` under the current
    /// trial model.
    fn w6_windows(&self, model: &Model, atom: TermId, target: TermId) -> Vec<(usize, usize)> {
        let mut out: Vec<(usize, usize)> = Vec::new();
        let mut seen: HashSet<(usize, usize)> = HashSet::default();
        let mut stack: Vec<(TermId, usize)> = vec![(atom, 0)];
        let mut budget = MAX_W6_WALK_BUDGET;
        while let Some((t, depth)) = stack.pop() {
            if depth > 64 || budget == 0 {
                continue;
            }
            budget -= 1;
            if *self.ctx.terms.sort(t) == Sort::String && self.w4_window_root(t, target, 0) {
                if let (Some(o), Some(s)) = (
                    self.w4_origin(model, t, target, 0),
                    self.w4_eval_string(model, t),
                ) {
                    let key = (o, s.chars().count());
                    if seen.insert(key) && out.len() < MAX_W6_WINDOWS {
                        out.push(key);
                    }
                }
            }
            match self.ctx.terms.get(t) {
                TermData::App(_, args) => {
                    for &a in args {
                        stack.push((a, depth + 1));
                    }
                }
                TermData::Not(inner) => stack.push((*inner, depth + 1)),
                TermData::Ite(c, a, b) => {
                    stack.push((*c, depth + 1));
                    stack.push((*a, depth + 1));
                    stack.push((*b, depth + 1));
                }
                _ => {}
            }
        }
        out.sort_unstable();
        out
    }

    /// Whether a binary `=` atom has a string constant on one side (the
    /// negative-window-pin shape), tested WITHOUT walking the tree.
    fn w6_has_string_const(&self, atom: TermId) -> bool {
        let TermData::App(Symbol::Named(_), args) = self.ctx.terms.get(atom) else {
            return false;
        };
        args.len() == 2
            && args
                .iter()
                .any(|&a| matches!(self.ctx.terms.get(a), TermData::Const(Constant::String(_))))
    }

    /// Whether `atom` reads a string numerically (`str.to_int`).
    fn w6_reads_numerically(&self, atom: TermId) -> bool {
        self.w6_tree_has(atom, &|exec, t| {
            matches!(exec.ctx.terms.get(t),
                TermData::App(Symbol::Named(f), a) if f == "str.to_int" && a.len() == 1)
        })
    }

    /// Integer constants occurring in `atom`, smallest-magnitude first.
    fn w6_int_constants(&self, atom: TermId) -> Vec<i64> {
        let mut out: Vec<i64> = Vec::new();
        let mut seen: HashSet<i64> = HashSet::default();
        let mut stack: Vec<(TermId, usize)> = vec![(atom, 0)];
        let mut budget = MAX_W6_WALK_BUDGET;
        while let Some((t, depth)) = stack.pop() {
            if depth > 64 || budget == 0 {
                continue;
            }
            budget -= 1;
            match self.ctx.terms.get(t) {
                TermData::Const(Constant::Int(n)) => {
                    if let Ok(v) = i64::try_from(n.clone()) {
                        if seen.insert(v) {
                            out.push(v);
                        }
                    }
                }
                TermData::App(_, args) => {
                    for &a in args {
                        stack.push((a, depth + 1));
                    }
                }
                TermData::Not(inner) => stack.push((*inner, depth + 1)),
                TermData::Ite(c, a, b) => {
                    stack.push((*c, depth + 1));
                    stack.push((*a, depth + 1));
                    stack.push((*b, depth + 1));
                }
                _ => {}
            }
        }
        out.sort_by_key(|v| v.abs());
        out.truncate(MAX_W6_INTS);
        out
    }

    /// Bounded predicate walk over a term tree.
    fn w6_tree_has(&self, root: TermId, pred: &dyn Fn(&Self, TermId) -> bool) -> bool {
        let mut stack: Vec<(TermId, usize)> = vec![(root, 0)];
        let mut budget = MAX_W6_WALK_BUDGET;
        while let Some((t, depth)) = stack.pop() {
            if depth > 64 || budget == 0 {
                continue;
            }
            budget -= 1;
            if pred(self, t) {
                return true;
            }
            match self.ctx.terms.get(t) {
                TermData::App(_, args) => {
                    for &a in args {
                        stack.push((a, depth + 1));
                    }
                }
                TermData::Not(inner) => stack.push((*inner, depth + 1)),
                TermData::Ite(c, a, b) => {
                    stack.push((*c, depth + 1));
                    stack.push((*a, depth + 1));
                    stack.push((*b, depth + 1));
                }
                _ => {}
            }
        }
        false
    }

    /// The variables some entailed atom reads NUMERICALLY: `str.to_int` over a
    /// window rooted at the variable, or a membership in a digit-only class.
    /// Computed ONCE per synthesis (the walk is syntactic, no model needed).
    pub(super) fn w6_numeric_vars(
        &self,
        vars: &[TermId],
        atoms: &[(TermId, bool)],
    ) -> HashSet<TermId> {
        let mut out: HashSet<TermId> = HashSet::default();
        for &var in vars {
            let hit = atoms.iter().any(|&(t, _)| {
                self.w6_tree_has(t, &|exec, s| match exec.ctx.terms.get(s) {
                    TermData::App(Symbol::Named(f), a) if f == "str.to_int" && a.len() == 1 => {
                        exec.w4_window_root(a[0], var, 0)
                    }
                    TermData::App(Symbol::Named(f), a)
                        if (f == "str.in_re" || f == "str.in.re") && a.len() == 2 =>
                    {
                        exec.w4_window_root(a[0], var, 0) && exec.w6_digit_class(a[1], 0)
                    }
                    _ => false,
                })
            });
            if hit {
                out.insert(var);
            }
        }
        out
    }

    /// Whether a regex term denotes a language over DIGITS only (syntactic and
    /// conservative — used only to pick filler characters).
    fn w6_digit_class(&self, t: TermId, depth: usize) -> bool {
        if depth > 16 {
            return false;
        }
        let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(t) else {
            return false;
        };
        match name.as_str() {
            "re.range" if args.len() == 2 => [args[0], args[1]].into_iter().all(|a| {
                self.w4_string_const(a)
                    .is_some_and(|s| s.chars().all(|c| c.is_ascii_digit()))
            }),
            "str.to_re" | "str.to.re" if args.len() == 1 => self
                .w4_string_const(args[0])
                .is_some_and(|s| !s.is_empty() && s.chars().all(|c| c.is_ascii_digit())),
            "re.*" | "re.+" | "re.opt" if args.len() == 1 => {
                self.w6_digit_class(args[0], depth + 1)
            }
            "re.++" | "re.union" | "re.inter" if !args.is_empty() => {
                args.iter().all(|&a| self.w6_digit_class(a, depth + 1))
            }
            _ => false,
        }
    }

    // ───────────────────────────── targeting gate ─────────────────────────

    /// W6's extension of the W4/W5 targeting gate. A `str.to_int` read of a
    /// window, or a membership whose haystack is a window, PINS CHARACTERS just
    /// as surely as `(= (str.at v 0) "c")` does — but carries no string
    /// constant next to a window, so neither W4's nor W5's gate can see it.
    ///
    /// This ADDS evidence kinds under `AY_STR_W6=1`; it does not weaken the
    /// existing gate (with the flag off the predicate is never consulted).
    pub(super) fn w6_is_positional_atom(&self, term: TermId) -> bool {
        let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(term) else {
            return false;
        };
        match name.as_str() {
            "str.in_re" | "str.in.re" if args.len() == 2 => {
                matches!(self.ctx.terms.get(args[0]), TermData::Var(..))
                    || matches!(self.ctx.terms.get(args[0]),
                        TermData::App(Symbol::Named(f), a)
                            if (f == "str.substr" && a.len() == 3) || (f == "str.at" && a.len() == 2))
            }
            _ => self.w6_reads_numerically(term),
        }
    }

    // ─────────────────────── regex-word pre-pass (shape B) ────────────────

    /// Regex-driven joint word construction: assign every string variable a
    /// word of its own membership language (shortest, or a bounded derivative
    /// witness) and validate the joint assignment.
    ///
    /// This is the class the W4 targeting gate deliberately declines (regex +
    /// length only formulas belong to S1/W1b/W2), so W6 does NOT reach it by
    /// widening that gate — it is a separate, separately-gated pre-pass with
    /// the same construct-and-validate contract, and it runs only when the
    /// formula is regex-driven and W4's own pass has already declined.
    pub(in crate::executor) fn try_regex_word_witnesses(&mut self) -> Result<Option<SolveResult>> {
        if !str_w6_enabled() || self.pivot_enum_depth != 0 {
            return Ok(None);
        }
        let vars = self.collect_string_variables();
        if vars.is_empty() || vars.len() > MAX_W6_VARS {
            if super::debug_auflia_enabled() {
                safe_eprintln!(
                    "[W6] declined: {} string var(s), joint work bound {MAX_W6_VARS}",
                    vars.len()
                );
            }
            return Ok(None);
        }
        let memberships = self.w6_collect_memberships();
        if memberships.is_empty() {
            if super::debug_auflia_enabled() {
                safe_eprintln!("[W6] declined: no regex membership to build a word from");
            }
            return Ok(None);
        }

        // Per-variable word pool: words of the memberships whose haystack is
        // exactly the variable (structural shortest at several star repetition
        // counts — the only way to meet a LENGTH LOWER BOUND — plus the exact
        // derivative witness), and the empty string.
        let mut pools: Vec<(TermId, Vec<String>)> = Vec::with_capacity(vars.len());
        for &var in &vars {
            let mut pool: Vec<String> = Vec::new();
            let mut regexes: Vec<WeRegex> = Vec::new();
            for &(hay, re, pol) in &memberships {
                if hay != var || !pol {
                    continue;
                }
                // Term-level word construction: no `WeRegex` size cap (the
                // stringfuzz `regexsmall` chains blow past it), and linear
                // rather than the derivative BFS's exponential.
                for reps in W6_WORD_REPS {
                    if let Some(w) = self.w6_term_word(re, reps, 0) {
                        w6_push_word(w, &mut pool);
                    }
                }
                if let Some(r) = self.translate_we_regex(re, 0) {
                    regexes.push(r);
                }
            }
            if !regexes.is_empty() {
                if let Some(w) = find_witness_bounded(&regexes, None, MAX_W6_WITNESS_DEPTH) {
                    w6_push_word(w, &mut pool);
                }
            }
            w6_push_word(String::new(), &mut pool);
            pool.sort_by_key(|s| s.chars().count());
            pools.push((var, pool));
        }

        let depth = pools.iter().map(|(_, p)| p.len()).max().unwrap_or(0);
        if depth == 0 {
            return Ok(None);
        }
        let mut candidates: Vec<HashMap<TermId, String>> = Vec::new();
        for idx in 0..depth.min(MAX_W6_WORD_CANDIDATES) {
            let mut assign: HashMap<TermId, String> = HashMap::default();
            for (var, pool) in &pools {
                let pick = pool.get(idx).or_else(|| pool.last());
                assign.insert(*var, pick.cloned().unwrap_or_default());
            }
            w6_push_candidate(assign, &mut candidates);
        }
        // The `str.++`-chain construction (slog `stranger_*_sink`): a membership
        // `x ∈ .*"/evil".*` on a variable that a DISJUNCTION equates to a
        // partially-ground concat `x_11 = sigmaStar_5 ++ "/Default.htm"`. The
        // needle goes into the concat's FREE operand and the membership
        // variable takes the concat's value.
        self.w6_concat_candidates(&vars, &memberships, &mut candidates);
        if candidates.is_empty() {
            return Ok(None);
        }
        if super::debug_auflia_enabled() {
            safe_eprintln!(
                "[W6] regex-word pre-pass: {} joint candidate(s) over {} var(s)",
                candidates.len(),
                vars.len()
            );
            for (i, c) in candidates.iter().enumerate() {
                let mut shown: Vec<String> = c
                    .iter()
                    .map(|(k, v)| format!("{}={:?}", k.index(), v))
                    .collect();
                shown.sort();
                safe_eprintln!("[W6]   cand {i}: {shown:?}");
            }
        }
        self.w4_validate_candidates(&candidates)
    }

    /// Early W6 shortcut, hoisted ahead of the per-variable witness passes
    /// (W1b, the cheap W1b probe, W4). Two structurally-narrow generators whose
    /// targets those passes decide either far more slowly or catastrophically:
    ///
    /// 1. The slog `stranger_*_sink` `str.++`-chain construction
    ///    ([`Self::w6_concat_candidates`]): a positive membership
    ///    `x ∈ .*"needle".*` on a variable a DISJUNCTION equates to a
    ///    partially-ground concat (`(or (= x_16 (str.++ σ "/Default.htm")) …)`),
    ///    decided by planting the needle in the concat's free operand. W1b/W4
    ///    can only synthesize `x` in ISOLATION, so all three run a full doomed
    ///    search and only the LATE W6 pass then decides it — after ~20 ms of
    ///    declined work (`slog_stranger_2825_sink`, 5.9x slower than z3).
    ///
    /// 2. The pure regex-membership fragment ([`Self::w6_pure_membership_shape`]):
    ///    a variable constrained ONLY by `str.in_re`, no `str.++`/`str.len`
    ///    coupling. Its witness is a linear word of the positive membership's
    ///    term skeleton (`w6_term_word`), but the downstream w1b derivative BFS
    ///    is slow on the complement-heavy intersection of the NEGATED
    ///    memberships (`automatark-lu/instance08792`, ~30 ms) and W4's
    ///    per-position search on the same shape is CATASTROPHIC (measured 12 s
    ///    before W6 finally decides in 1.8 ms). Constructing the skeleton word
    ///    here decides it in ~1 ms.
    ///
    /// The general W6 word-pool build must stay LATE (moving it early displaces
    /// 24 pyex conversions on ties), so generator 2 is gated to the pure
    /// fragment — which has no `str.++`/`str.len` and so is disjoint from the
    /// pyex regex+length / word-equation families whose w1b/w4 conversions must
    /// be preserved. Construct-and-validate, identical to the late W6 pass:
    /// [`Self::w4_validate_candidates`] pins each candidate and re-solves under
    /// the FULL model validation, so this emits only a validated SAT model and
    /// otherwise declines — verdict-preserving by construction. Gated by
    /// `str_w6_enabled()` so `AY_STR_W6=0` stays byte-identical.
    pub(in crate::executor) fn try_w6_early_shortcut(&mut self) -> Result<Option<SolveResult>> {
        if !str_w6_enabled() || self.pivot_enum_depth != 0 {
            return Ok(None);
        }
        let vars = self.collect_string_variables();
        if vars.is_empty() || vars.len() > MAX_W6_VARS {
            return Ok(None);
        }
        let memberships = self.w6_collect_memberships();
        if memberships.is_empty() {
            return Ok(None);
        }
        let mut candidates: Vec<HashMap<TermId, String>> = Vec::new();
        self.w6_concat_candidates(&vars, &memberships, &mut candidates);
        if self.w6_pure_membership_shape() {
            self.w6_pure_membership_candidates(&vars, &memberships, &mut candidates);
        }
        if candidates.is_empty() {
            return Ok(None);
        }
        // Running ahead of Nielsen, this pass must be a bounded FAST PATH: the
        // targets decide on the shortest few candidates (concat needle-plants
        // and reps=0 skeleton words, both ordered first), so cap the validation
        // storm. Anything not decided within the cap declines and is retried by
        // the late W6 pass (full candidate set) unchanged — no capability lost.
        candidates.truncate(MAX_W6_EARLY_VALIDATIONS);
        if super::debug_auflia_enabled() {
            safe_eprintln!(
                "[W6] early shortcut: {} joint candidate(s) over {} var(s)",
                candidates.len(),
                vars.len()
            );
        }
        self.w4_validate_candidates(&candidates)
    }

    /// True when EVERY string constraint in the assertion set is a `str.in_re`
    /// membership or an (in)equality — the pure regex-membership fragment. No
    /// `str.++`, `str.len`, `str.at`, `str.substr`, or any other string
    /// operation couples the variables, so each variable's witness is exactly a
    /// word of its own memberships. This is the fragment where the length-
    /// indexed W4 search and the complement-heavy w1b derivative BFS are both
    /// far slower than a linear skeleton word.
    ///
    /// The fragment is deliberately NARROW: every top-level assertion (after
    /// `and`-splitting) must be a DIRECT literal over a string VARIABLE `v` —
    /// `(str.in_re v R)`, or a `v == const` / `v != const` (dis)equality (the
    /// polarity `not` wrapping either) — and at least one must be a membership.
    /// This admits the automatark pure-membership targets (`instance12580`,
    /// whose `(not (str.in_re x (str.to_re c)))` conjunct is rewritten to
    /// `(not (= x c))` before this runs; `instance08792`) but rejects
    /// * membership+length / word-equation files (a coupling `str.len` /
    ///   `str.++` appears as a conjunct or inside the haystack), keeping the
    ///   pyex families' w1b/w4 conversions untouched; and, crucially,
    /// * BOOLEAN COMBINATIONS of memberships such as the sygus-qgen
    ///   `(and (not (= (str.in_re x R1) (str.in_re x R2))) …)` — where the `=`
    ///   is Bool≡Bool over two memberships, not `var == const`, so it is
    ///   rejected. Their SAT is built ONLY by Nielsen's complement-based
    ///   materializer, which must therefore NOT be declined or shortcut.
    ///
    /// The regex ARGUMENT of a membership is not inspected (it is a regex, not a
    /// coupling term); a blown budget declines conservatively.
    pub(in crate::executor) fn w6_pure_membership_shape(&self) -> bool {
        let mut stack: Vec<TermId> = self.ctx.assertions.to_vec();
        let mut budget = 20_000usize;
        let mut saw_membership = false;
        while let Some(t) = stack.pop() {
            if budget == 0 {
                return false;
            }
            budget -= 1;
            // Negation is a dedicated `TermData::Not`, not an `App`.
            let body = match self.ctx.terms.get(t) {
                TermData::Not(inner) => *inner,
                TermData::App(sym, args) if sym.name() == "and" => {
                    stack.extend(args.iter().copied());
                    continue;
                }
                TermData::App(sym, args) if sym.name() == "true" && args.is_empty() => continue,
                TermData::Const(Constant::Bool(true)) => continue,
                _ => t,
            };
            match self.w6_var_literal_kind(body) {
                Some(true) => saw_membership = true,
                Some(false) => {}
                None => return false,
            }
        }
        saw_membership
    }

    /// Classify a candidate literal body over a string VARIABLE:
    /// * `Some(true)`  — `(str.in_re v R)`, a membership;
    /// * `Some(false)` — `(= v c)` / `(distinct v c)` between a string variable
    ///   and a string CONSTANT (either argument order);
    /// * `None`        — anything else (a coupling term, a Bool≡Bool equality
    ///   of two memberships, a variable≡variable equality, …).
    fn w6_var_literal_kind(&self, t: TermId) -> Option<bool> {
        let TermData::App(sym, args) = self.ctx.terms.get(t) else {
            return None;
        };
        let is_str_var = |a: TermId| {
            matches!(self.ctx.terms.get(a), TermData::Var(..))
                && *self.ctx.terms.sort(a) == Sort::String
        };
        let is_str_const =
            |a: TermId| matches!(self.ctx.terms.get(a), TermData::Const(Constant::String(_)));
        match sym.name() {
            "str.in_re" | "str.in.re" if args.len() == 2 && is_str_var(args[0]) => Some(true),
            "=" | "distinct" if args.len() == 2 => {
                let var_const = |a: TermId, b: TermId| is_str_var(a) && is_str_const(b);
                (var_const(args[0], args[1]) || var_const(args[1], args[0])).then_some(false)
            }
            _ => None,
        }
    }

    /// Per-variable structural witness pool for the pure regex-membership
    /// fragment: for each variable, a LINEAR skeleton word of every positive
    /// `str.in_re` whose haystack is that variable (`w6_term_word` at several
    /// star-repetition counts) and the empty string.
    ///
    /// Deliberately does NOT run the derivative-BFS witness search
    /// (`find_witness_bounded`) the late W6 word-pool uses: this pass runs
    /// AHEAD of the Nielsen exhaust, so it must never start a doomed
    /// complement-heavy product-derivative search — on the pure-membership
    /// UNSAT `automatark-lu/instance13338` that BFS runs for ~5 s before
    /// declining, work the Nielsen emptiness check settles in ~15 ms. The
    /// linear skeleton word is exactly the witness for the SAT targets
    /// (`instance08792`/`instance12580`: a `str.to_re`/`re.*` concatenation);
    /// anything whose witness needs the BFS declines here and is picked up by
    /// the late W6 pass unchanged.
    ///
    /// A SAT-side candidate generator only — every candidate is pinned and
    /// revalidated against the FULL assertion set (including the negated
    /// memberships and any disequations) by the caller, so a word that happens
    /// to violate a negative membership simply fails validation and is
    /// discarded.
    fn w6_pure_membership_candidates(
        &self,
        vars: &[TermId],
        memberships: &[(TermId, TermId, bool)],
        out: &mut Vec<HashMap<TermId, String>>,
    ) {
        let mut pools: Vec<(TermId, Vec<String>)> = Vec::with_capacity(vars.len());
        for &var in vars {
            let mut pool: Vec<String> = Vec::new();
            for &(hay, re, pol) in memberships {
                if hay != var || !pol {
                    continue;
                }
                for reps in W6_WORD_REPS {
                    if let Some(w) = self.w6_term_word(re, reps, 0) {
                        w6_push_word(w, &mut pool);
                    }
                }
            }
            w6_push_word(String::new(), &mut pool);
            pool.sort_by_key(|s| s.chars().count());
            pools.push((var, pool));
        }
        let depth = pools.iter().map(|(_, p)| p.len()).max().unwrap_or(0);
        for idx in 0..depth.min(MAX_W6_WORD_CANDIDATES) {
            let mut assign: HashMap<TermId, String> = HashMap::default();
            for (var, pool) in &pools {
                let pick = pool.get(idx).or_else(|| pool.last());
                assign.insert(*var, pick.cloned().unwrap_or_default());
            }
            w6_push_candidate(assign, out);
        }
    }

    /// A word of the regex TERM `t`, with every `re.*`/`re.+` body repeated
    /// `reps` times (`re.+` at least once).
    ///
    /// Works on the TERM, not on [`WeRegex`], for two measured reasons: the
    /// stringfuzz `regexsmall`/`regexlengths` families exceed
    /// `translate_we_regex`'s node-size cap outright, and their words are 30-80
    /// characters long — far past what the derivative BFS can reach. The walk
    /// is linear in the regex.
    ///
    /// This is a HEURISTIC generator, never an oracle: `re.inter` takes the
    /// first branch's word and `re.comp` declines, so a returned word is only a
    /// CANDIDATE. Every candidate is decided by `finalize_sat_model_validation`
    /// — AY's own definitive evaluator — before any verdict is emitted.
    fn w6_term_word(&self, t: TermId, reps: usize, depth: usize) -> Option<String> {
        if depth > 64 {
            return None;
        }
        let TermData::App(sym, args) = self.ctx.terms.get(t) else {
            return None;
        };
        let cap =
            |s: String| -> Option<String> { (s.chars().count() <= MAX_W6_WORD_LEN).then_some(s) };
        let out = match sym.name() {
            "re.none" => return None,
            "re.all" if args.is_empty() => String::new(),
            "re.allchar" if args.is_empty() => "a".to_string(),
            "re.range" if args.len() == 2 => {
                let lo = self.w4_string_const(args[0])?;
                if lo.chars().count() != 1 {
                    return None;
                }
                lo
            }
            "str.to_re" | "str.to.re" if args.len() == 1 => self.w4_string_const(args[0])?,
            "re.++" if !args.is_empty() => {
                let mut out = String::new();
                for &a in args {
                    out.push_str(&self.w6_term_word(a, reps, depth + 1)?);
                    if out.chars().count() > MAX_W6_WORD_LEN {
                        return None;
                    }
                }
                out
            }
            // The shortest branch: a union is satisfied by any one of them, and
            // a shorter word keeps more length atoms reachable.
            "re.union" if !args.is_empty() => args
                .iter()
                .filter_map(|&a| self.w6_term_word(a, reps, depth + 1))
                .min_by_key(|s| s.chars().count())?,
            // Not exact for intersection — a candidate only, decided by the
            // validation battery like every other W6 proposal.
            "re.inter" if !args.is_empty() => args
                .iter()
                .find_map(|&a| self.w6_term_word(a, reps, depth + 1))?,
            "re.*" if args.len() == 1 => {
                let body = self.w6_term_word(args[0], reps, depth + 1)?;
                cap(body.repeat(reps))?
            }
            "re.+" if args.len() == 1 => {
                let body = self.w6_term_word(args[0], reps, depth + 1)?;
                cap(body.repeat(reps.max(1)))?
            }
            "re.opt" if args.len() == 1 => {
                if reps == 0 {
                    String::new()
                } else {
                    self.w6_term_word(args[0], reps, depth + 1)?
                }
            }
            "re.loop" if args.len() == 1 => {
                let Symbol::Indexed(_, indices) = sym else {
                    return None;
                };
                if indices.len() != 2 || indices[0] > indices[1] {
                    return None;
                }
                let n = usize::try_from(indices[0]).ok()?.max(1);
                let body = self.w6_term_word(args[0], reps, depth + 1)?;
                cap(body.repeat(n))?
            }
            _ => return None,
        };
        cap(out)
    }

    /// The `str.++`-chain construction behind the slog `stranger_*_sink`
    /// family: `x_16` carries a membership `.*"/evil".*`, a DISJUNCTION (so
    /// nothing is entailed) equates it to one of several partially-ground
    /// concats `x_11 = sigmaStar_5 ++ "/Default.htm"`, and the witness is
    /// "put the needle in the free operand, then copy the concat's value".
    ///
    /// The concat values are computed by AY's own evaluator over a trial model
    /// — not by a bespoke concatenation — so the propagation cannot disagree
    /// with the validation that follows.
    fn w6_concat_candidates(
        &self,
        vars: &[TermId],
        memberships: &[(TermId, TermId, bool)],
        out: &mut Vec<HashMap<TermId, String>>,
    ) {
        let defs = self.w6_var_defs();
        let choices = self.w6_var_choices();
        if super::debug_auflia_enabled() {
            safe_eprintln!(
                "[W6] concat: {} def(s), {} choice(s), {} assertion(s)",
                defs.len(),
                choices.len(),
                self.ctx.assertions.len()
            );
        }
        if defs.is_empty() {
            return;
        }
        let defined: HashSet<TermId> = defs.iter().map(|&(v, _)| v).collect();
        let chosen: HashSet<TermId> = choices.iter().map(|(v, _)| *v).collect();

        // The needles a positive membership REQUIRES to occur.
        let mut needles: Vec<String> = Vec::new();
        for &(_, re, pol) in memberships {
            if !pol {
                continue;
            }
            for lit in self.w6_regex_literals(re) {
                if !lit.is_empty()
                    && lit.chars().count() <= MAX_W6_WORD_LEN
                    && !needles.contains(&lit)
                    && needles.len() < MAX_W6_SLOG_NEEDLES
                {
                    needles.push(lit);
                }
            }
        }
        if needles.is_empty() {
            return;
        }

        // FREE OPERANDS: variables the chain reads but nothing defines or
        // constrains — the only places a needle can be planted.
        let free_ops: Vec<TermId> = vars
            .iter()
            .copied()
            .filter(|v| {
                !defined.contains(v)
                    && !chosen.contains(v)
                    && (defs.iter().any(|&(_, rhs)| self.w4_mentions(rhs, *v, 0))
                        || memberships
                            .iter()
                            .any(|&(h, _, _)| self.w4_mentions(h, *v, 0)))
            })
            .collect();
        // Variables carrying a positive membership that NOTHING defines: a
        // disjunction is free to equate them to any of the chain's values.
        let open_membership: Vec<TermId> = memberships
            .iter()
            .filter(|&&(hay, _, pol)| {
                pol && !defined.contains(&hay) && !chosen.contains(&hay) && vars.contains(&hay)
            })
            .map(|&(hay, _, _)| hay)
            .collect();
        if free_ops.is_empty() && open_membership.is_empty() {
            return;
        }

        let max_choice = choices
            .iter()
            .map(|(_, c)| c.len())
            .max()
            .unwrap_or(1)
            .max(1);
        for needle in &needles {
            for choice_idx in 0..max_choice.min(3) {
                // Seed: needle into every free operand, everything else empty,
                // disjunctive variables at `choice_idx`.
                let mut base: HashMap<TermId, String> = HashMap::default();
                for &v in vars {
                    base.insert(v, String::new());
                }
                for &v in &free_ops {
                    base.insert(v, needle.clone());
                }
                self.w6_propagate(&defs, &choices, choice_idx, &mut base);
                w6_push_candidate(base.clone(), out);
                if open_membership.is_empty() {
                    continue;
                }
                // Each chain value is a candidate for the open membership
                // variables (the slog `(or (= x_16 x_11) …)` shape).
                let mut targets: Vec<String> = defs
                    .iter()
                    .filter_map(|&(v, _)| base.get(&v).cloned())
                    .collect();
                targets.push(needle.clone());
                for value in targets {
                    let mut assign = base.clone();
                    for &m in &open_membership {
                        assign.insert(m, value.clone());
                    }
                    self.w6_propagate(&defs, &choices, choice_idx, &mut assign);
                    w6_push_candidate(assign, out);
                    if out.len() >= MAX_W6_WORD_CANDIDATES * 3 {
                        return;
                    }
                }
            }
        }
    }

    /// Recompute every DEFINED variable from its right-hand side and every
    /// DISJUNCTIVE variable from its `choice_idx`-th alternative, to a small
    /// fixpoint. Bracketed by the memo reset the shared `evaluate_term` cache
    /// requires (`#eval-memo`) — the trial model changes on every round.
    fn w6_propagate(
        &self,
        defs: &[(TermId, TermId)],
        choices: &[(TermId, Vec<TermId>)],
        choice_idx: usize,
        assign: &mut HashMap<TermId, String>,
    ) {
        for _round in 0..MAX_W6_PROPAGATE_ROUNDS {
            let mut changed = false;
            let model = w4_trial_model(assign);
            w4_memo_reset();
            for (var, alts) in choices {
                let Some(&alt) = alts.get(choice_idx).or_else(|| alts.first()) else {
                    continue;
                };
                if let Some(v) = self.w4_eval_string(&model, alt) {
                    if v.chars().count() <= MAX_W6_CHAIN_LEN && assign.get(var) != Some(&v) {
                        assign.insert(*var, v);
                        changed = true;
                    }
                }
            }
            for &(var, rhs) in defs {
                if let Some(v) = self.w4_eval_string(&model, rhs) {
                    if v.chars().count() <= MAX_W6_CHAIN_LEN && assign.get(&var) != Some(&v) {
                        assign.insert(var, v);
                        changed = true;
                    }
                }
            }
            w4_memo_reset();
            if !changed {
                break;
            }
        }
    }

    /// Top-level `(or (= v e1) (= v e2) …)` alternatives for a single variable
    /// `v` — the slog family's only disjunction, and the reason nothing in the
    /// chain is ENTAILED (so the forced-literal closure sees none of it).
    fn w6_var_choices(&self) -> Vec<(TermId, Vec<TermId>)> {
        let mut out: Vec<(TermId, Vec<TermId>)> = Vec::new();
        for &t in &self.ctx.assertions {
            if out.len() >= MAX_W6_DEFS {
                break;
            }
            let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(t) else {
                continue;
            };
            if name != "or" || args.len() < 2 {
                continue;
            }
            // Both sides of a disjunct can be string VARIABLES
            // (`(or (= x_20 sigmaStar_1) (= x_20 x_17))`), so the subject
            // cannot be read off the first disjunct's argument order — it is
            // the variable common to EVERY disjunct. Measured: orienting on
            // `args[0]` dropped the disjunction on slog `stranger_3210`/`5030`,
            // the construction then planted the needle in the disjunction's own
            // subject, and every candidate was refuted by that `or`.
            let mut common: Option<Vec<TermId>> = None;
            let mut sides: Vec<(TermId, TermId)> = Vec::new();
            let mut ok = true;
            for &d in args {
                let TermData::App(Symbol::Named(eq), eargs) = self.ctx.terms.get(d) else {
                    ok = false;
                    break;
                };
                if eq != "=" || eargs.len() != 2 {
                    ok = false;
                    break;
                }
                let is_svar = |t: TermId| {
                    matches!(self.ctx.terms.get(t), TermData::Var(..))
                        && *self.ctx.terms.sort(t) == Sort::String
                };
                let here: Vec<TermId> = [eargs[0], eargs[1]]
                    .into_iter()
                    .filter(|&t| is_svar(t))
                    .collect();
                if here.is_empty() {
                    ok = false;
                    break;
                }
                common = Some(match common {
                    None => here,
                    Some(prev) => prev.into_iter().filter(|t| here.contains(t)).collect(),
                });
                sides.push((eargs[0], eargs[1]));
                if common.as_ref().is_some_and(Vec::is_empty) {
                    ok = false;
                    break;
                }
            }
            let Some(mut common) = common.filter(|_| ok) else {
                continue;
            };
            common.sort_by_key(|t| t.index());
            let Some(&v) = common.first() else { continue };
            let alts: Vec<TermId> = sides
                .iter()
                .map(|&(l, r)| if l == v { r } else { l })
                .collect();
            if !out.iter().any(|(u, _)| *u == v) {
                out.push((v, alts));
            }
        }
        out
    }

    /// Top-level `(= var rhs)` definitions of string variables.
    fn w6_var_defs(&self) -> Vec<(TermId, TermId)> {
        let mut out: Vec<(TermId, TermId)> = Vec::new();
        let mut seen: HashSet<TermId> = HashSet::default();
        for &t in &self.ctx.assertions {
            if out.len() >= MAX_W6_DEFS {
                break;
            }
            let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(t) else {
                continue;
            };
            if name != "=" || args.len() != 2 {
                continue;
            }
            for (lhs, rhs) in [(args[0], args[1]), (args[1], args[0])] {
                if !matches!(self.ctx.terms.get(lhs), TermData::Var(..))
                    || *self.ctx.terms.sort(lhs) != Sort::String
                    || matches!(self.ctx.terms.get(rhs), TermData::Var(..))
                {
                    continue;
                }
                if seen.insert(lhs) {
                    out.push((lhs, rhs));
                }
            }
        }
        out
    }

    /// The `str.to_re` literals of a regex term — the words a membership
    /// REQUIRES to occur.
    fn w6_regex_literals(&self, re: TermId) -> Vec<String> {
        let mut out: Vec<String> = Vec::new();
        let mut stack: Vec<(TermId, usize)> = vec![(re, 0)];
        let mut budget = 2048usize;
        while let Some((t, depth)) = stack.pop() {
            if depth > 64 || budget == 0 {
                continue;
            }
            budget -= 1;
            let TermData::App(sym, args) = self.ctx.terms.get(t) else {
                continue;
            };
            if (sym.name() == "str.to_re" || sym.name() == "str.to.re") && args.len() == 1 {
                if let Some(s) = self.w4_string_const(args[0]) {
                    if !out.contains(&s) {
                        out.push(s);
                    }
                }
                continue;
            }
            for &a in args {
                stack.push((a, depth + 1));
            }
        }
        // Longest first: the most constraining needle is the most likely to be
        // the one the membership is really about.
        out.sort_by(|a, b| b.chars().count().cmp(&a.chars().count()).then(a.cmp(b)));
        out
    }

    /// Positive/negative `str.in_re` atoms visible in the assertion set, as
    /// `(haystack, regex, polarity)`.
    fn w6_collect_memberships(&self) -> Vec<(TermId, TermId, bool)> {
        let mut out: Vec<(TermId, TermId, bool)> = Vec::new();
        let mut seen: HashSet<(TermId, bool)> = HashSet::default();
        let mut stack: Vec<(TermId, bool, usize)> =
            self.ctx.assertions.iter().map(|&t| (t, true, 0)).collect();
        let mut budget = 8192usize;
        while let Some((t, pol, depth)) = stack.pop() {
            if depth > 64 || budget == 0 || out.len() >= 64 {
                continue;
            }
            budget -= 1;
            match self.ctx.terms.get(t) {
                TermData::Not(inner) => stack.push((*inner, !pol, depth + 1)),
                TermData::App(Symbol::Named(name), args) => {
                    if (name == "str.in_re" || name == "str.in.re") && args.len() == 2 {
                        if seen.insert((t, pol)) {
                            out.push((args[0], args[1], pol));
                        }
                    } else if name == "and" || name == "or" || name == "not" {
                        for &a in args {
                            stack.push((a, if name == "not" { !pol } else { pol }, depth + 1));
                        }
                    }
                }
                _ => {}
            }
        }
        out
    }
}

// ───────────────────────────── free helpers ───────────────────────────────

/// Add a word to a per-variable pool (deduplicated, length-capped).
fn w6_push_word(w: String, pool: &mut Vec<String>) {
    if w.chars().count() <= MAX_W6_WORD_LEN && !pool.contains(&w) {
        pool.push(w);
    }
}

/// Add a joint assignment to the candidate list (deduplicated).
fn w6_push_candidate(assign: HashMap<TermId, String>, out: &mut Vec<HashMap<TermId, String>>) {
    if out
        .iter()
        .any(|c| c.len() == assign.len() && c.iter().all(|(k, v)| assign.get(k) == Some(v)))
    {
        return;
    }
    out.push(assign);
}

/// Decimal texts worth writing into a window of `have` characters.
fn w6_digit_texts(have: usize, ints: &[i64]) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    let push = |s: String, out: &mut Vec<String>| {
        if s.chars().count() <= MAX_W6_NUM_LEN && !out.contains(&s) {
            out.push(s);
        }
    };
    if have > 0 && have <= MAX_W6_NUM_LEN {
        // Leading-nonzero of the CURRENT length: this family's
        // `(not (= (str.at W 0) "0"))` atoms make it the useful shape.
        let mut lead = String::from("1");
        lead.push_str(&"0".repeat(have - 1));
        push(lead, &mut out);
        push("0".repeat(have), &mut out);
        push("9".repeat(have), &mut out);
    }
    // Boundary values of the atom's own constants (`<= 255`, `< 2`, `= -1`).
    for &k in ints {
        for v in [k, k - 1, k + 1] {
            if (0..=99_999).contains(&v) {
                push(v.to_string(), &mut out);
            }
        }
    }
    for v in [0i64, 1, 2, 10] {
        push(v.to_string(), &mut out);
    }
    out
}

/// The window `[origin, origin+have)` of `cur`, resized to `want` characters by
/// padding with `fill` or truncating from its tail.
fn w6_resize_body(
    cur: &[char],
    origin: usize,
    have: usize,
    want: usize,
    fill: char,
) -> Option<Vec<char>> {
    if origin > cur.len() || want > MAX_W4_LEN {
        return None;
    }
    let end = origin.checked_add(have)?.min(cur.len());
    let mut body: Vec<char> = cur[origin.min(end)..end].to_vec();
    match want.cmp(&body.len()) {
        std::cmp::Ordering::Greater => {
            while body.len() < want {
                body.push(fill);
            }
        }
        std::cmp::Ordering::Less => body.truncate(want),
        std::cmp::Ordering::Equal => return None,
    }
    Some(body)
}

/// Replace `cur`'s window `[origin, origin+have)` with `body`, appending the
/// candidate when it is new and in range.
fn w6_push_window(
    cur: &[char],
    origin: usize,
    have: usize,
    body: &[char],
    out: &mut Vec<Vec<char>>,
) {
    if out.len() >= MAX_W6_CANDIDATES || origin > cur.len() {
        return;
    }
    let Some(end) = origin.checked_add(have) else {
        return;
    };
    let end = end.min(cur.len());
    let mut next: Vec<char> = Vec::with_capacity(cur.len() + body.len());
    next.extend_from_slice(&cur[..origin]);
    next.extend_from_slice(body);
    next.extend_from_slice(&cur[end..]);
    if next.len() > MAX_W4_LEN || next == cur {
        return;
    }
    if !out.contains(&next) {
        out.push(next);
    }
}

/// A SHORTEST word of `r`, built structurally (linear, unlike the derivative
/// BFS which is exponential in the word's length and cannot reach the 50-way
/// `re.++` chains of the stringfuzz `regexsmall` family).
///
/// `None` for the constructs where "shortest" is not structural (`Inter`,
/// `Comp`) — those keep using the exact derivative search. Every returned word
/// is re-checked by `WeRegex::matches` at the call site before use, so this is
/// a HEURISTIC generator, never an oracle.
pub(super) fn w6_shortest_word(r: &WeRegex, depth: usize) -> Option<String> {
    if depth > 64 {
        return None;
    }
    match r {
        WeRegex::None => None,
        WeRegex::Eps | WeRegex::All | WeRegex::Star(_) => Some(String::new()),
        WeRegex::Lit(s) => Some(s.clone()),
        WeRegex::AnyChar => Some("a".to_string()),
        WeRegex::Range(lo, _) => Some(lo.to_string()),
        WeRegex::Concat(parts) => {
            let mut out = String::new();
            for p in parts {
                out.push_str(&w6_shortest_word(p, depth + 1)?);
                if out.chars().count() > MAX_W4_LEN {
                    return None;
                }
            }
            Some(out)
        }
        WeRegex::Union(parts) => parts
            .iter()
            .filter_map(|p| w6_shortest_word(p, depth + 1))
            .min_by_key(|s| s.chars().count()),
        WeRegex::Loop(inner, lo, _) => {
            let body = w6_shortest_word(inner, depth + 1)?;
            let n = usize::try_from(*lo).ok()?;
            if body.chars().count().checked_mul(n)? > MAX_W4_LEN {
                return None;
            }
            Some(body.repeat(n))
        }
        WeRegex::Inter(_) | WeRegex::Comp(_) => None,
    }
}

/// A trial model over a candidate assignment, bracketed by the memo reset the
/// shared `evaluate_term` cache requires (`#eval-memo`).
#[allow(dead_code)]
pub(super) fn w6_trial(assign: &HashMap<TermId, String>) -> Model {
    w4_memo_reset();
    w4_trial_model(assign)
}

/// Evaluate a term to a definite boolean, or `None`.
#[allow(dead_code)]
pub(super) fn w6_eval_bool(exec: &Executor, model: &Model, t: TermId) -> Option<bool> {
    match exec.evaluate_term(model, t) {
        EvalValue::Bool(b) => Some(b),
        _ => None,
    }
}

#[cfg(test)]
#[path = "strings_w6_tests.rs"]
mod tests;

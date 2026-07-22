// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! W4 — length-indexed per-position character witness synthesizer
//! (`AY_STR_W4=1`, default OFF).
//!
//! ## Why
//!
//! The measured sat-side strings wall (the development design notes
//! construction.md`, "PREMISE CORRECTED BY MEASUREMENT") is dominated by the
//! *per-position* family: 70 of the 92 sat misses (61 PyEx/Reynolds, 5
//! `full_str_int`, 3 Leetcode, 1 Kepler) carry no `str.in_re` at all. They pin
//! and forbid individual CHARACTERS of a string variable — directly
//! (`(= (str.at v 0) " ")`) or through `str.substr`/`str.indexof` windows over
//! it — and 58 of the 92 return Unknown during THEORY CHECK, so no SAT model
//! is ever built and every model-construction path (W1–W3) is unreachable.
//!
//! W4 therefore runs as a depth-0 PRE-PASS, next to the other validated
//! witness pre-passes (`try_regex_length_witnesses`,
//! `try_word_equation_nielsen`, the P2 negative-only guess pass), and
//! synthesizes candidate values directly from the unit-propagated constraint
//! set.
//!
//! ## Algorithm (census RANK 1)
//!
//! (a) run the existing forced-literal closure
//!     ([`Executor::forced_literal_closure_ext`], with the PyEx integer-encoded
//!     Boolean idiom decoded) to collect the ENTAILED atom set;
//! (b) per target string variable derive a seed length (explicit `str.len`
//!     pin, harvested equality constant, or the shape minimum implied by the
//!     required literals);
//! (c) build the per-position character set by CONCRETE EVALUATION: every
//!     entailed atom is evaluated under the current candidate assignment, and
//!     each definitively-violated atom is mapped back to the position(s) of
//!     the target variable it constrains (`str.at` equalities/disequalities,
//!     prefix/suffix literals, `str.contains` couplings, `str.len` pins,
//!     `str.substr`/`str.at` windows via ORIGIN tracking, `str.to_int` digit
//!     requirements);
//! (d) pick a character per position — the pinned character when the atom
//!     forces one, otherwise a character outside the formula alphabet (which
//!     cannot create a forbidden occurrence), then an alphabet member, then a
//!     class representative;
//! (e) JOINT construction: all coupled variables are repaired together in the
//!     same assignment and validated ONCE (the W1–W3 finding: single-variable
//!     pins get refuted by the rest of the formula).
//!
//! ## Soundness contract
//!
//! Everything here only ever produces a CANDIDATE assignment. Nothing in this
//! module decides a verdict:
//!
//! * a candidate is accepted only when the FULL model-validation battery
//!   ([`Executor::finalize_sat_model_validation`] — the same definitive-
//!   evaluation chokepoint every string SAT passes, used exactly as the P2
//!   negative-only guess pass uses it) confirms it;
//! * a failed candidate restores every saved solver field and falls through to
//!   the normal pipeline;
//! * UNSAT is NEVER concluded here — a failed synthesis means "not found",
//!   never "no witness exists".
//!
//! So W4 can only convert a would-be Unknown into a gate-validated SAT, or
//! cost bounded time. No gate is weakened and no verdict logic is touched.
//!
//! ## Where W4 stops, and who takes over
//!
//! Step (d) edits ONE CHARACTER POSITION per violated atom, which requires
//! [`Executor::w4_origin`] to name that position. `w4_origin` walks
//! `str.substr`/`str.at` only, so a violated atom whose haystack is rooted at
//! `str.++`/`str.replace`, or that is keyed on an `str.indexof` RESULT, yields
//! no edit at all and the climb plateaus. That measured residue is
//! [`super::strings_w5`]'s (`AY_STR_W5=1`, default OFF), which searches WHERE
//! the needle lands and hands the rest back to the loop below.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Constant, Symbol, TermData, TermId};
use ay_core::Sort;

use crate::executor_types::{Result, SolveResult};

use super::super::model::{EvalValue, Model};
use super::super::Executor;

/// Master switch (`AY_STR_W4=1`, default OFF → byte-identical pipeline).
pub(in crate::executor) fn str_w4_enabled() -> bool {
    static V: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    // DEFAULT-ON: 31/92 sat-side conversions (26 attributable to W4), 29 of
    // 31 models z3-PINNED, 0 disagreements, 0 regressions on a 404-file solved
    // sweep, 2x500 differential+pin-model fuzz clean. AY_STR_W4=0 kills it.
    *V.get_or_init(|| !matches!(std::env::var("AY_STR_W4").ok().as_deref(), Some("0")))
}

/// Longest witness W4 will synthesize (characters). Bounds work, not
/// soundness: a longer witness simply is not attempted.
pub(super) const MAX_W4_LEN: usize = 40;

/// Maximum number of string variables handled jointly.
const MAX_W4_VARS: usize = 8;

/// Maximum entailed atoms carried into the repair loop.
const MAX_W4_ATOMS: usize = 512;

/// Maximum entailed atoms scored per variable.
const MAX_W4_VAR_ATOMS: usize = 256;

/// Repair rounds per variable per pass.
const MAX_W4_ROUNDS: usize = 32;

/// Outer joint passes over all variables.
const MAX_W4_PASSES: usize = 4;

/// Distinct seed assignments attempted.
const MAX_W4_SEEDS: usize = 10;

/// Repair candidates collected per round before scoring.
const MAX_W4_REPAIRS: usize = 10;

/// Self-consistent joint assignments handed to validation.
const MAX_W4_CANDIDATES: usize = 6;

/// Per-variable seed values.
const MAX_W4_SEED_POOL: usize = 10;

/// Drop the shared evaluation memo (`#eval-memo`).
///
/// `Executor::evaluate_term` caches results keyed by `TermId` ALONE, which is
/// only sound while the model is immutable — an enclosing `EvalMemoSession`
/// makes that cache live. W4 evaluates against a TRIAL model that changes on
/// every repair step, so a value it computes must never outlive the trial
/// model that produced it. Every W4 evaluation epoch is therefore bracketed by
/// this reset.
///
/// This is not a theoretical concern: without it, W4 flipped the already-solved
/// `20230329-denghang/instance55083` from `sat` to `unknown` even on a run
/// where it produced NO candidate at all — its trial-model values had poisoned
/// the memo the real validation then read.
pub(super) fn w4_memo_reset() {
    crate::executor::model::eval_memo_clear();
}

impl Executor {
    /// W4 pre-pass: synthesize per-position character witnesses for the
    /// formula's string variables and validate them jointly. See module docs.
    ///
    /// Returns `Ok(Some(Sat))` only for a fully validated model, `Ok(None)`
    /// otherwise (never `Unsat`).
    pub(in crate::executor) fn try_per_position_witnesses(
        &mut self,
    ) -> Result<Option<SolveResult>> {
        if !str_w4_enabled() || self.pivot_enum_depth != 0 {
            return Ok(None);
        }
        let vars = self.collect_string_variables();
        // W6 (`AY_STR_W6=1`) raises the joint-variable work bound: the
        // `full_str_int` `lib_int-ipaddress` family declares 9 variables and
        // W4's cap of 8 declines it before any synthesis happens. A work bound
        // only — every candidate still rides the full validation battery.
        let var_cap = if super::strings_w6::str_w6_enabled() {
            super::strings_w6::MAX_W6_SYNTH_VARS
        } else {
            MAX_W4_VARS
        };
        if vars.is_empty() || vars.len() > var_cap {
            return Ok(None);
        }

        // (a) entailed atom set from the unit-propagated closure, with the
        // PyEx integer-encoded Boolean idiom decoded.
        let (forced_true, forced_false) = self.forced_literal_closure_ext(true);
        let atoms = self.w4_collect_atoms(&forced_true, &forced_false);
        if atoms.is_empty() {
            return Ok(None);
        }
        // TARGETING GATE. W4 is a PER-POSITION synthesizer: it only ever makes
        // progress when some entailed atom pins or forbids a character at a
        // resolvable position. A formula constrained purely by regex membership
        // and length (`str.in_re x R` + `(< 20 (str.len x))`) offers nothing to
        // repair — that family is owned by the regex machinery (S1 / W1b / W2)
        // — so W4 must not spend the solve's budget on it. Measured: without
        // this gate W4 ran its full synthesis on `20230329-denghang/
        // instance55083` (3 atoms, all regex/length) and the already-solved
        // file degraded sat → unknown.
        //
        // W5 (`AY_STR_W5=1`) widens the evidence to `str.indexof` equalities
        // and character-window couplings (`(= (str.at s i) (str.at s j))`,
        // which reaches here rewritten to `str.substr`): both pin positions
        // while carrying no string constant on either side, so W4's own gate
        // cannot see them. See `strings_w5.rs`.
        // W6 (`AY_STR_W6=1`) adds two more evidence kinds: a `str.to_int` read
        // of a window (the `full_str_int` family pins DIGITS at every position
        // it reads, and carries no string constant at all) and a membership
        // whose haystack is a window. Both ADD to the gate; nothing is removed.
        let w5 = super::strings_w5::str_w5_enabled();
        let w6 = super::strings_w6::str_w6_enabled();
        if !atoms.iter().any(|&(t, _)| {
            self.w4_is_positional_atom(t)
                || (w5 && self.w5_is_positional_atom(t))
                || (w6 && self.w6_is_positional_atom(t))
        }) {
            if super::debug_auflia_enabled() {
                safe_eprintln!(
                    "[W4] targeting gate declined: {} entailed atom(s), none positional",
                    atoms.len()
                );
            }
            return Ok(None);
        }

        let alphabet = self.collect_alphabet();
        let fresh = w4_fresh_char(&alphabet);
        let var_atoms: Vec<(TermId, Vec<(TermId, bool)>)> = vars
            .iter()
            .map(|&v| (v, self.w4_atoms_mentioning(&atoms, v)))
            .collect();
        // Which variables are read NUMERICALLY (W6). Computed once: the walk is
        // syntactic, and the repair loop consults it thousands of times.
        let numeric: HashSet<TermId> = if w6 {
            self.w6_numeric_vars(&vars, &atoms)
        } else {
            HashSet::default()
        };

        // (b) per-variable seed pools.
        let pools = self.w4_seed_pools(&vars, &atoms, fresh);
        let pool_len = pools.iter().map(|(_, p)| p.len()).max().unwrap_or(0);
        if pool_len == 0 {
            return Ok(None);
        }

        // (c)-(e) synthesize joint assignments; keep the self-consistent ones.
        let mut candidates: Vec<HashMap<TermId, String>> = Vec::new();
        for seed_idx in 0..pool_len.min(MAX_W4_SEEDS) {
            if self.should_abort_theory_loop() {
                break;
            }
            let mut assign: HashMap<TermId, String> = HashMap::default();
            for (var, pool) in &pools {
                let pick = pool.get(seed_idx).or_else(|| pool.last());
                assign.insert(*var, pick.cloned().unwrap_or_default());
            }
            self.w4_synthesize(&var_atoms, &mut assign, &alphabet, &numeric, fresh);
            let mut viol = self.w4_violations(&atoms, &assign);
            // W5 (`AY_STR_W5=1`): the per-character climb plateaus whenever a
            // violated atom's haystack is rooted at `str.++`/`str.replace` or
            // keyed on an `str.indexof` result — `w4_origin` cannot name a
            // position, so no edit is emitted. Search WHERE the needle lands
            // instead, filling the remainder with this same per-position logic.
            let plateau = viol;
            if viol != 0 && w5 {
                self.w5_placement_search(
                    &var_atoms,
                    &atoms,
                    &mut assign,
                    &alphabet,
                    &numeric,
                    fresh,
                );
                viol = self.w4_violations(&atoms, &assign);
            }
            if super::debug_auflia_enabled() {
                let mut shown: Vec<String> = assign.values().map(|s| format!("{s:?}")).collect();
                shown.sort();
                let w5_note = if w5 && plateau != 0 {
                    format!(" (W5 placement search: {plateau} -> {viol})")
                } else {
                    String::new()
                };
                safe_eprintln!("[W4] seed {seed_idx}: violations={viol}{w5_note} {shown:?}");
            }
            if viol != 0 {
                continue;
            }
            if !candidates.iter().any(|c| w4_same(c, &assign)) {
                candidates.push(assign);
                if candidates.len() >= MAX_W4_CANDIDATES {
                    break;
                }
            }
        }
        if candidates.is_empty() {
            return Ok(None);
        }
        if super::debug_auflia_enabled() {
            safe_eprintln!(
                "[W4] {} self-consistent joint candidate(s) over {} var(s)",
                candidates.len(),
                vars.len()
            );
        }

        self.w4_validate_candidates(&candidates)
    }

    // ─────────────────────────── constraint harvest ───────────────────────

    /// Filter the closure lists down to ATOMS worth evaluating: string/int
    /// predicates and equalities. Boolean connectives are dropped (their
    /// conjuncts are already in the closure).
    fn w4_collect_atoms(
        &self,
        forced_true: &[TermId],
        forced_false: &[TermId],
    ) -> Vec<(TermId, bool)> {
        let mut out: Vec<(TermId, bool)> = Vec::new();
        let mut seen: HashSet<(TermId, bool)> = HashSet::default();
        for (list, pol) in [(forced_true, true), (forced_false, false)] {
            for &t in list {
                if out.len() >= MAX_W4_ATOMS {
                    break;
                }
                let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(t) else {
                    continue;
                };
                if args.is_empty() {
                    continue;
                }
                let interesting = matches!(
                    name.as_str(),
                    "=" | "distinct"
                        | "<"
                        | "<="
                        | ">"
                        | ">="
                        | "str.contains"
                        | "str.prefixof"
                        | "str.suffixof"
                        | "str.in_re"
                        | "str.in.re"
                        | "str.<"
                        | "str.<="
                );
                if !interesting {
                    continue;
                }
                if seen.insert((t, pol)) {
                    out.push((t, pol));
                }
            }
        }
        out
    }

    /// Whether an entailed atom constrains a CHARACTER POSITION (as opposed
    /// to only a length or a language membership) — the evidence W4 needs to
    /// have anything to synthesize.
    fn w4_is_positional_atom(&self, term: TermId) -> bool {
        let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(term) else {
            return false;
        };
        match name.as_str() {
            "str.contains" | "str.prefixof" | "str.suffixof" => args.len() == 2,
            "=" if args.len() == 2 => {
                [(args[0], args[1]), (args[1], args[0])]
                    .into_iter()
                    .any(|(lhs, rhs)| {
                        if self.w4_string_const(rhs).is_none() {
                            return false;
                        }
                        match self.ctx.terms.get(lhs) {
                            // A whole-value pin on a bare string variable.
                            TermData::Var(..) => *self.ctx.terms.sort(lhs) == Sort::String,
                            TermData::App(Symbol::Named(f), fargs) => {
                                (f == "str.at" && fargs.len() == 2)
                                    || (f == "str.substr" && fargs.len() == 3)
                            }
                            _ => false,
                        }
                    })
            }
            _ => false,
        }
    }

    /// The subset of `atoms` whose term tree mentions `var`.
    fn w4_atoms_mentioning(&self, atoms: &[(TermId, bool)], var: TermId) -> Vec<(TermId, bool)> {
        let mut out = Vec::new();
        for &(t, pol) in atoms {
            if out.len() >= MAX_W4_VAR_ATOMS {
                break;
            }
            if self.w4_mentions(t, var, 0) {
                out.push((t, pol));
            }
        }
        out
    }

    pub(super) fn w4_mentions(&self, term: TermId, var: TermId, depth: usize) -> bool {
        if term == var {
            return true;
        }
        if depth > 64 {
            return false;
        }
        match self.ctx.terms.get(term) {
            TermData::App(_, args) => args.iter().any(|&a| self.w4_mentions(a, var, depth + 1)),
            TermData::Not(inner) => self.w4_mentions(*inner, var, depth + 1),
            TermData::Ite(c, a, b) => {
                self.w4_mentions(*c, var, depth + 1)
                    || self.w4_mentions(*a, var, depth + 1)
                    || self.w4_mentions(*b, var, depth + 1)
            }
            TermData::Let(bindings, body) => {
                bindings
                    .iter()
                    .any(|(_, v)| self.w4_mentions(*v, var, depth + 1))
                    || self.w4_mentions(*body, var, depth + 1)
            }
            _ => false,
        }
    }

    /// Per-variable seed values, ordered best-first:
    /// an entailed `(= v "lit")` pin (alone — it is the only legal value),
    /// otherwise harvested equality constants, the required-literal packing,
    /// and uniform pads of a fresh / class-representative character.
    fn w4_seed_pools(
        &self,
        vars: &[TermId],
        atoms: &[(TermId, bool)],
        fresh: char,
    ) -> Vec<(TermId, Vec<String>)> {
        let mut out: Vec<(TermId, Vec<String>)> = Vec::with_capacity(vars.len());
        for &var in vars {
            let mut pinned: Option<String> = None;
            let mut eq_consts: Vec<String> = Vec::new();
            let mut required: Vec<String> = Vec::new();
            let mut prefix: Option<String> = None;
            let mut exact_len: Option<usize> = None;
            for &(t, pol) in atoms {
                let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(t) else {
                    continue;
                };
                match name.as_str() {
                    "=" if args.len() == 2 => {
                        for (lhs, rhs) in [(args[0], args[1]), (args[1], args[0])] {
                            let Some(s) = self.w4_string_const(rhs) else {
                                continue;
                            };
                            if lhs == var {
                                if pol {
                                    pinned = Some(s.clone());
                                } else if eq_consts.len() < 3 && !eq_consts.contains(&s) {
                                    eq_consts.push(s.clone());
                                }
                            }
                            // `(= (str.len v) N)` exact length pin.
                            if let TermData::App(Symbol::Named(f), fargs) = self.ctx.terms.get(lhs)
                            {
                                if f == "str.len" && fargs.len() == 1 && fargs[0] == var && pol {
                                    if let TermData::Const(Constant::Int(n)) =
                                        self.ctx.terms.get(rhs)
                                    {
                                        if let Ok(n) = usize::try_from(n.clone()) {
                                            if n <= MAX_W4_LEN {
                                                exact_len = Some(n);
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                    // A positive `contains` over a SUBSTRING window of `var`
                    // implies `var` itself contains the literal.
                    "str.contains" if args.len() == 2 && pol => {
                        if self.w4_window_root(args[0], var, 0) && required.len() < 4 {
                            if let Some(s) = self.w4_string_const(args[1]) {
                                if !s.is_empty() && !required.contains(&s) {
                                    required.push(s);
                                }
                            }
                        }
                    }
                    "str.prefixof" if args.len() == 2 && pol => {
                        if args[1] == var {
                            if let Some(s) = self.w4_string_const(args[0]) {
                                prefix = Some(s);
                            }
                        } else if self.w4_window_root(args[1], var, 0) && required.len() < 4 {
                            if let Some(s) = self.w4_string_const(args[0]) {
                                if !s.is_empty() && !required.contains(&s) {
                                    required.push(s);
                                }
                            }
                        }
                    }
                    _ => {}
                }
            }

            if let Some(p) = pinned {
                out.push((var, vec![p]));
                continue;
            }

            let mut pool: Vec<String> = Vec::new();
            let push = |s: String, pool: &mut Vec<String>| {
                if s.chars().count() <= MAX_W4_LEN
                    && !pool.contains(&s)
                    && pool.len() < MAX_W4_SEED_POOL
                {
                    pool.push(s);
                }
            };
            if let Some(n) = exact_len {
                push(std::iter::repeat_n(fresh, n).collect(), &mut pool);
            }
            for c in &eq_consts {
                push(c.clone(), &mut pool);
            }
            // Required-literal packing: prefix ++ literals (both orders),
            // optionally padded with the fresh character.
            let pre = prefix.clone().unwrap_or_default();
            if !required.is_empty() || !pre.is_empty() {
                let fwd: String = required.concat();
                let mut rev: Vec<String> = required.clone();
                rev.reverse();
                let bwd: String = rev.concat();
                for body in [fwd, bwd] {
                    for pad in 0..2 {
                        let padding: String = std::iter::repeat_n(fresh, pad).collect();
                        push(format!("{pre}{body}{padding}"), &mut pool);
                    }
                }
            }
            for n in 0..4 {
                push(std::iter::repeat_n(fresh, n).collect(), &mut pool);
            }
            push("a".to_string(), &mut pool);
            out.push((var, pool));
        }
        out
    }

    /// Whether `term` is a SUBSTRING window rooted at `var`
    /// (`v`, `str.substr(W, ..)`, `str.at(W, ..)`). Such a window's value is
    /// always a substring of `var`'s value.
    pub(super) fn w4_window_root(&self, term: TermId, var: TermId, depth: usize) -> bool {
        if term == var {
            return true;
        }
        if depth > 32 {
            return false;
        }
        let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(term) else {
            return false;
        };
        match name.as_str() {
            "str.substr" if args.len() == 3 => self.w4_window_root(args[0], var, depth + 1),
            "str.at" if args.len() == 2 => self.w4_window_root(args[0], var, depth + 1),
            _ => false,
        }
    }

    // ───────────────────────────── synthesis ──────────────────────────────

    /// Joint repair: sweep every variable until no assignment changes or the
    /// entailed atom set is satisfied.
    pub(super) fn w4_synthesize(
        &mut self,
        var_atoms: &[(TermId, Vec<(TermId, bool)>)],
        assign: &mut HashMap<TermId, String>,
        alphabet: &[char],
        numeric: &HashSet<TermId>,
        fresh: char,
    ) {
        for _pass in 0..MAX_W4_PASSES {
            let mut changed = false;
            for (var, atoms) in var_atoms {
                if atoms.is_empty() {
                    continue;
                }
                let before = assign.get(var).cloned().unwrap_or_default();
                self.w4_repair_var(*var, atoms, assign, alphabet, numeric, fresh);
                if assign.get(var).map(String::as_str) != Some(before.as_str()) {
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
    }

    /// Hill-climbing per-position repair of a single variable's value against
    /// the entailed atoms mentioning it.
    #[allow(clippy::too_many_arguments)]
    fn w4_repair_var(
        &mut self,
        var: TermId,
        atoms: &[(TermId, bool)],
        assign: &mut HashMap<TermId, String>,
        alphabet: &[char],
        numeric: &HashSet<TermId>,
        fresh: char,
    ) {
        let mut best = assign.get(&var).cloned().unwrap_or_default();
        let mut best_score = self.w4_violations(atoms, assign);
        let mut stall = 0usize;
        let w5 = super::strings_w5::str_w5_enabled();
        let w6 = super::strings_w6::str_w6_enabled();
        // W6 proposes a WIDER neighbourhood per atom (a value, not a
        // character), so it needs a bigger scored-repair budget and a wider
        // sideways tolerance; W5-only runs keep W4's calibration exactly.
        let repair_cap = if w6 {
            super::strings_w6::MAX_W6_REPAIRS
        } else {
            MAX_W4_REPAIRS
        };
        // W4's sideways tolerance is KEPT under W6: widening it to 5 was
        // measured to be a pure cost (it converted nothing in the residue and
        // let the climb wander out of W5's basin).
        let stall_cap = 2usize;
        let is_numeric = numeric.contains(&var);
        for _round in 0..MAX_W4_ROUNDS {
            if best_score == 0 || self.should_abort_theory_loop() {
                break;
            }
            let model = w4_trial_model(assign);
            w4_memo_reset();
            let cur: Vec<char> = best.chars().collect();
            let mut repairs: Vec<String> = Vec::new();
            for &(atom, pol) in atoms {
                if repairs.len() >= repair_cap {
                    break;
                }
                if !matches!(self.evaluate_term(&model, atom), EvalValue::Bool(v) if v != pol) {
                    continue;
                }
                // W5 supplies the two positional repairs W4's arms structurally
                // cannot express (`str.indexof` landing, character-window
                // coupling). Consulted ONLY where W4 declines, so W4-only runs
                // are unchanged.
                let repaired = self
                    .w4_repair_atom(&model, atom, pol, var, &cur, alphabet, fresh)
                    .or_else(|| {
                        w5.then(|| {
                            self.w5_repair_atom(&model, atom, pol, var, &cur, alphabet, fresh)
                        })
                        .flatten()
                    });
                let Some(next) = repaired else {
                    // W6's move classes (numeric window fills, regex word
                    // fills, generalised length nudges, negative window pins)
                    // return a LIST — the `full_str_int` family's constraint is
                    // a VALUE, not a character. Consulted ONLY where BOTH W4
                    // and W5 decline, exactly as W5 is consulted only where W4
                    // declines. MEASURED: running W6 first instead cost 24
                    // pyex `httplib2-entry-disposition` conversions (W5's own
                    // family) — its candidates displaced W5's on ties and its
                    // per-atom tree walk exhausted the solve budget.
                    if w6 {
                        for cand in self
                            .w6_repair_candidates(&model, atom, pol, var, &cur, is_numeric, fresh)
                        {
                            if repairs.len() >= repair_cap {
                                break;
                            }
                            let next: String = cand.into_iter().collect();
                            if next.chars().count() <= MAX_W4_LEN
                                && next != best
                                && !repairs.contains(&next)
                            {
                                repairs.push(next);
                            }
                        }
                    }
                    continue;
                };
                let next: String = next.into_iter().collect();
                if next.chars().count() <= MAX_W4_LEN && next != best && !repairs.contains(&next) {
                    repairs.push(next);
                }
            }
            w4_memo_reset();
            if repairs.is_empty() {
                break;
            }
            let mut round_best: Option<(String, usize)> = None;
            for cand in repairs {
                assign.insert(var, cand.clone());
                let score = self.w4_violations(atoms, assign);
                if round_best.as_ref().is_none_or(|(_, s)| score < *s) {
                    round_best = Some((cand, score));
                }
            }
            let Some((cand, score)) = round_best else {
                break;
            };
            if score < best_score {
                best = cand;
                best_score = score;
                stall = 0;
            } else {
                // Sideways move to escape a plateau, bounded.
                best = cand;
                best_score = score;
                stall += 1;
                if stall >= stall_cap {
                    break;
                }
            }
            assign.insert(var, best.clone());
        }
        assign.insert(var, best);
    }

    /// Number of entailed atoms DEFINITIVELY violated by `assign`.
    /// Atoms the evaluator cannot decide are not counted (they are decided by
    /// the real validation gate later).
    pub(super) fn w4_violations(
        &self,
        atoms: &[(TermId, bool)],
        assign: &HashMap<TermId, String>,
    ) -> usize {
        let model = w4_trial_model(assign);
        w4_memo_reset();
        let n = atoms
            .iter()
            .filter(|&&(t, pol)| matches!(self.evaluate_term(&model, t), EvalValue::Bool(v) if v != pol))
            .count();
        w4_memo_reset();
        n
    }

    /// Map a violated entailed atom back to a per-position edit of `target`.
    ///
    /// Returns the repaired character vector, or `None` when the atom does not
    /// constrain a resolvable position of `target`.
    fn w4_repair_atom(
        &self,
        model: &Model,
        atom: TermId,
        pol: bool,
        target: TermId,
        cur: &[char],
        alphabet: &[char],
        fresh: char,
    ) -> Option<Vec<char>> {
        let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(atom) else {
            return None;
        };
        match name.as_str() {
            "=" if args.len() == 2 => {
                for (lhs, rhs) in [(args[0], args[1]), (args[1], args[0])] {
                    // `(= (str.at W I) "c")` — pin / unpin one position.
                    if let TermData::App(Symbol::Named(f), fargs) = self.ctx.terms.get(lhs) {
                        if f == "str.at" && fargs.len() == 2 {
                            if let Some(ch) = self
                                .w4_string_const(rhs)
                                .filter(|s| s.chars().count() == 1)
                                .and_then(|s| s.chars().next())
                            {
                                let origin = self.w4_origin(model, fargs[0], target, 0)?;
                                let idx = self.w4_eval_index(model, fargs[1])?;
                                let pos = origin.checked_add(idx)?;
                                return w4_set_char(cur, pos, ch, pol, alphabet, fresh);
                            }
                        }
                        // `(= (str.len W) N)` — grow / shrink the window's tail.
                        if f == "str.len" && fargs.len() == 1 {
                            let TermData::Const(Constant::Int(n)) = self.ctx.terms.get(rhs) else {
                                continue;
                            };
                            let want = usize::try_from(n.clone()).ok()?;
                            let origin = self.w4_origin(model, fargs[0], target, 0)?;
                            let have = self.w4_eval_string(model, fargs[0])?.chars().count();
                            if pol {
                                return w4_resize_window(cur, origin, have, want, fresh);
                            }
                            let bump = if have == 0 { 1 } else { have + 1 };
                            return w4_resize_window(cur, origin, have, bump, fresh);
                        }
                    }
                    // `(= W "lit")` — overwrite the window with the literal.
                    if pol {
                        if let Some(lit) = self.w4_string_const(rhs) {
                            if *self.ctx.terms.sort(lhs) == Sort::String {
                                let origin = self.w4_origin(model, lhs, target, 0)?;
                                let have = self.w4_eval_string(model, lhs)?.chars().count();
                                let lit: Vec<char> = lit.chars().collect();
                                let resized = w4_resize_window(cur, origin, have, lit.len(), fresh)
                                    .unwrap_or_else(|| cur.to_vec());
                                return w4_overwrite(&resized, origin, &lit);
                            }
                        }
                    }
                }
                None
            }
            "str.contains" if args.len() == 2 => {
                let needle = self.w4_eval_string(model, args[1])?;
                if needle.is_empty() {
                    return None;
                }
                let origin = self.w4_origin(model, args[0], target, 0)?;
                let window = self.w4_eval_string(model, args[0])?;
                let needle_chars: Vec<char> = needle.chars().collect();
                if pol {
                    // Make the needle occur at the start of the window.
                    let have = window.chars().count();
                    let base = if have < needle_chars.len() {
                        w4_resize_window(cur, origin, have, needle_chars.len(), fresh)?
                    } else {
                        cur.to_vec()
                    };
                    w4_overwrite(&base, origin, &needle_chars)
                } else {
                    // Break the first occurrence inside the window.
                    let win: Vec<char> = window.chars().collect();
                    let at = (0..=win.len().saturating_sub(needle_chars.len())).find(|&s| {
                        win.len() >= s + needle_chars.len()
                            && win[s..s + needle_chars.len()] == needle_chars[..]
                    })?;
                    let pos = origin + at;
                    let mut excluded: HashSet<char> = HashSet::default();
                    excluded.insert(needle_chars[0]);
                    let ch = w4_pick_char(&excluded, alphabet, fresh);
                    w4_set_char(cur, pos, ch, true, alphabet, fresh)
                }
            }
            "str.prefixof" if args.len() == 2 && pol => {
                let lit: Vec<char> = self.w4_eval_string(model, args[0])?.chars().collect();
                let origin = self.w4_origin(model, args[1], target, 0)?;
                let have = self.w4_eval_string(model, args[1])?.chars().count();
                let base = if have < lit.len() {
                    w4_resize_window(cur, origin, have, lit.len(), fresh)?
                } else {
                    cur.to_vec()
                };
                w4_overwrite(&base, origin, &lit)
            }
            "str.suffixof" if args.len() == 2 && pol => {
                let lit: Vec<char> = self.w4_eval_string(model, args[0])?.chars().collect();
                let origin = self.w4_origin(model, args[1], target, 0)?;
                let have = self.w4_eval_string(model, args[1])?.chars().count();
                let (base, have) = if have < lit.len() {
                    (
                        w4_resize_window(cur, origin, have, lit.len(), fresh)?,
                        lit.len(),
                    )
                } else {
                    (cur.to_vec(), have)
                };
                let start = origin + have.checked_sub(lit.len())?;
                w4_overwrite(&base, start, &lit)
            }
            // `(<= (str.len W) N)` and friends: nudge the window's length.
            "<" | "<=" | ">" | ">=" if args.len() == 2 => {
                for (side, other) in [(args[0], args[1]), (args[1], args[0])] {
                    let TermData::App(Symbol::Named(f), fargs) = self.ctx.terms.get(side) else {
                        continue;
                    };
                    if f != "str.len" || fargs.len() != 1 {
                        continue;
                    }
                    let TermData::Const(Constant::Int(n)) = self.ctx.terms.get(other) else {
                        continue;
                    };
                    let bound = usize::try_from(n.clone()).ok()?;
                    let origin = self.w4_origin(model, fargs[0], target, 0)?;
                    let have = self.w4_eval_string(model, fargs[0])?.chars().count();
                    // Move one step toward the bound; the loop re-evaluates.
                    let want = if have > bound {
                        bound
                    } else {
                        bound.saturating_add(1).min(MAX_W4_LEN)
                    };
                    return w4_resize_window(cur, origin, have, want, fresh);
                }
                None
            }
            _ => None,
        }
    }

    // ───────────────────────────── evaluation ─────────────────────────────

    /// Start offset of `term`'s value inside `target`'s value, when `term` is a
    /// `str.substr` / `str.at` window rooted at `target`. `None` when the term
    /// is not such a window or the window is degenerate under the current
    /// assignment.
    pub(super) fn w4_origin(
        &self,
        model: &Model,
        term: TermId,
        target: TermId,
        depth: usize,
    ) -> Option<usize> {
        if term == target {
            return Some(0);
        }
        if depth > 32 {
            return None;
        }
        let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(term) else {
            return None;
        };
        match name.as_str() {
            "str.substr" if args.len() == 3 => {
                let base = self.w4_origin(model, args[0], target, depth + 1)?;
                let base_len = self.w4_eval_string(model, args[0])?.chars().count();
                let offset = self.w4_eval_index(model, args[1])?;
                if offset > base_len {
                    return None;
                }
                base.checked_add(offset)
            }
            "str.at" if args.len() == 2 => {
                let base = self.w4_origin(model, args[0], target, depth + 1)?;
                let base_len = self.w4_eval_string(model, args[0])?.chars().count();
                let offset = self.w4_eval_index(model, args[1])?;
                if offset >= base_len {
                    return None;
                }
                base.checked_add(offset)
            }
            _ => None,
        }
    }

    pub(super) fn w4_eval_string(&self, model: &Model, term: TermId) -> Option<String> {
        match self.evaluate_term(model, term) {
            EvalValue::String(s) => Some(s),
            _ => None,
        }
    }

    /// A non-negative integer index, as `usize`.
    pub(super) fn w4_eval_index(&self, model: &Model, term: TermId) -> Option<usize> {
        match self.evaluate_term(model, term) {
            EvalValue::Rational(r) if r.is_integer() => usize::try_from(r.to_integer())
                .ok()
                .filter(|&n| n <= MAX_W4_LEN),
            _ => None,
        }
    }

    pub(super) fn w4_string_const(&self, term: TermId) -> Option<String> {
        match self.ctx.terms.get(term) {
            TermData::Const(Constant::String(s)) => Some(s.clone()),
            _ => None,
        }
    }

    // ───────────────────────────── validation ─────────────────────────────

    /// Validate joint candidates through the FULL model-validation battery —
    /// `finalize_sat_model_validation`, the same definitive-evaluation
    /// chokepoint every string SAT passes and the exact gate the P2
    /// negative-only guess pass uses. A rejection restores all saved state and
    /// falls through; UNSAT is never concluded.
    ///
    /// A *pinned-assumption re-solve* variant (build `x = "…"` for the whole
    /// joint assignment, re-solve, then model + assumption + materializer
    /// validation, mirroring `try_string_var_witnesses`) was built and
    /// MEASURED: it converted one file FEWER (32 vs 33 over the 92 sat misses)
    /// and produced a wrong `unsat` on
    /// `kaluza/sat/small/bettermatch1.readable.smt2` — the inner assumption
    /// solve refutes the pinned candidate and that refutation leaks past the
    /// full `restore_witness_state` into the outer verdict (the leak is NOT in
    /// `ctx.assertions`, which the trace shows unchanged, and `--self-check`
    /// downgrades the answer to `unknown`, so it is an unproven unsat). That is
    /// a latent hazard of the shared inner-assumption-solve machinery, not
    /// something W4 may work around, so the route is not shipped: W4 never runs
    /// an inner solve.
    pub(super) fn w4_validate_candidates(
        &mut self,
        candidates: &[HashMap<TermId, String>],
    ) -> Result<Option<SolveResult>> {
        // Save EVERY per-solve field the validation pipeline mutates — the
        // exact set `restore_witness_state` (shared with the other validated
        // witness pre-passes) covers, so a failed candidate leaves no trace
        // that could influence the verdict.
        let saved_deadline = self.solve_deadline.get();
        // The validation battery injects completion axioms / repairs into the
        // assertion view; a REJECTED candidate must not leave them behind
        // (they were derived for that candidate, and the normal pipeline that
        // runs after this pass must see exactly the assertion set it would
        // have seen without W4).
        let saved_assertions = self.ctx.assertions.clone();
        let saved_last_model = self.last_model.clone();
        let saved_last_result = self.last_result.clone();
        let saved_last_unknown_reason = self.last_unknown_reason;
        let saved_last_model_validated = self.last_model_validated;
        let saved_last_validation_stats = self.last_validation_stats.clone();
        let saved_last_assumption_core = self.last_assumption_core.clone();
        let saved_bypass_taut = self.bypass_string_tautology_guard;
        let saved_slia_accepted = self.slia_accepted_unknown;
        let saved_skip_model_eval = self.skip_model_eval;

        let restore = |exec: &mut Self| {
            exec.ctx.assertions = saved_assertions.clone();
            exec.restore_witness_state(
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
        };

        for cand in candidates {
            if self.should_abort_theory_loop() {
                restore(self);
                return Ok(None);
            }
            w4_memo_reset();
            self.last_model = Some(w4_trial_model(cand));
            self.last_result = Some(SolveResult::Sat);
            self.last_model_validated = false;
            if let Ok(SolveResult::Sat) = self.finalize_sat_model_validation() {
                if super::debug_auflia_enabled() {
                    safe_eprintln!(
                        "[W4] joint per-position witness validated by the full model battery"
                    );
                }
                return Ok(Some(SolveResult::Sat));
            }
            restore(self);
            w4_memo_reset();
        }

        restore(self);
        w4_memo_reset();
        Ok(None)
    }
}

// ───────────────────────────── free helpers ───────────────────────────────

/// A trial model carrying ONLY the candidate string assignment — the same
/// shape the P2 negative-only guess pass hands to the validation battery.
pub(super) fn w4_trial_model(assign: &HashMap<TermId, String>) -> Model {
    Model {
        sat_model: Vec::new(),
        term_to_var: HashMap::default(),
        bool_overrides: HashMap::default(),
        euf_model: None,
        array_model: None,
        lra_model: None,
        lia_model: None,
        bv_model: None,
        fp_model: None,
        string_model: Some(ay_strings::StringModel {
            values: assign.clone(),
        }),
        seq_model: None,
        completed_values: HashMap::default(),
        dt_ground: HashMap::default(),
        dt_pins: HashMap::default(),
    }
}

fn w4_same(a: &HashMap<TermId, String>, b: &HashMap<TermId, String>) -> bool {
    a.len() == b.len() && a.iter().all(|(k, v)| b.get(k) == Some(v))
}

/// A character OUTSIDE the formula's constant alphabet when one exists: it can
/// never create a forbidden literal occurrence, which is what the negative
/// per-position family needs.
fn w4_fresh_char(alphabet: &[char]) -> char {
    ('a'..='z')
        .chain('A'..='Z')
        .chain('0'..='9')
        .find(|c| !alphabet.contains(c))
        .unwrap_or('a')
}

/// Pick a character avoiding `excluded`, preferring the fresh character, then
/// a printable non-whitespace alphabet member, then class representatives.
pub(super) fn w4_pick_char(excluded: &HashSet<char>, alphabet: &[char], fresh: char) -> char {
    if !excluded.contains(&fresh) {
        return fresh;
    }
    for &c in alphabet {
        if !c.is_whitespace() && !c.is_control() && !excluded.contains(&c) {
            return c;
        }
    }
    for c in ['a', 'b', 'z', '0', '1'] {
        if !excluded.contains(&c) {
            return c;
        }
    }
    fresh
}

/// Set (`want == true`) or clear (`want == false`) character `ch` at `pos`.
/// Positions one past the end are appended; further out fails.
pub(super) fn w4_set_char(
    cur: &[char],
    pos: usize,
    ch: char,
    want: bool,
    alphabet: &[char],
    fresh: char,
) -> Option<Vec<char>> {
    if pos > MAX_W4_LEN {
        return None;
    }
    let mut out = cur.to_vec();
    if want {
        while out.len() < pos {
            out.push(fresh);
        }
        if out.len() == pos {
            out.push(ch);
        } else {
            out[pos] = ch;
        }
        return Some(out);
    }
    if pos >= out.len() || out[pos] != ch {
        return None;
    }
    let mut excluded: HashSet<char> = HashSet::default();
    excluded.insert(ch);
    out[pos] = w4_pick_char(&excluded, alphabet, fresh);
    Some(out)
}

/// Overwrite `lit` at `start`, extending with the last character if needed.
fn w4_overwrite(cur: &[char], start: usize, lit: &[char]) -> Option<Vec<char>> {
    if start + lit.len() > MAX_W4_LEN {
        return None;
    }
    let mut out = cur.to_vec();
    for (i, &ch) in lit.iter().enumerate() {
        let pos = start + i;
        if pos < out.len() {
            out[pos] = ch;
        } else {
            out.push(ch);
        }
    }
    Some(out)
}

/// Resize a window `[origin, origin + have)` inside `cur` to `want`
/// characters, inserting fresh padding or deleting from the window's tail.
fn w4_resize_window(
    cur: &[char],
    origin: usize,
    have: usize,
    want: usize,
    fresh: char,
) -> Option<Vec<char>> {
    if want > MAX_W4_LEN || origin > cur.len() {
        return None;
    }
    let end = origin.checked_add(have)?.min(cur.len());
    let mut out: Vec<char> = cur[..end].to_vec();
    match want.cmp(&have) {
        std::cmp::Ordering::Greater => {
            for _ in 0..(want - have) {
                out.push(fresh);
            }
        }
        std::cmp::Ordering::Less => {
            let drop = have - want;
            if out.len() < drop {
                return None;
            }
            out.truncate(out.len() - drop);
        }
        std::cmp::Ordering::Equal => return None,
    }
    out.extend_from_slice(&cur[end..]);
    if out.len() > MAX_W4_LEN {
        return None;
    }
    Some(out)
}

#[cfg(test)]
#[path = "strings_w4_tests.rs"]
mod tests;

// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! W5 — position-aware witness search (default ON, `AY_STR_W5=0` kill switch).
//!
//! ## The measured gap W5 closes
//!
//! W4 ([`super::strings_w4`], default ON) converted 31 of the 92 sat-side
//! strings misses by hill-climbing ONE CHARACTER POSITION per violated atom.
//! Its report named the residue precisely:
//!
//! > the ~60 remaining misses need the repair loop to reason about WHERE
//! > `indexof` lands, which one-edit-per-atom hill climbing cannot search.
//!
//! Instrumenting the residue confirms the mechanism exactly. On the dominant
//! family (PyEx `httplib2-entry-disposition`, 30 of the 58 residual files) W4
//! reaches a joint assignment with a SINGLE definitively-violated atom, e.g.
//! `value1 = "b\t=K"` with
//!
//! ```text
//! (str.contains (str.++ (str.replace (str.substr TAIL 0 (+ (str.indexof TAIL "K" 0) 1)) "K" "k")
//!                       (str.substr TAIL (+ (str.indexof TAIL "K" 0) 1) ...))
//!               "L")
//! ```
//!
//! still false, where `TAIL = (str.substr value1 (+ (str.indexof value1 "=" 0) 1) …)`.
//! [`Executor::w4_repair_atom`] asks [`Executor::w4_origin`] for the position
//! this atom constrains; `w4_origin` only walks `str.substr`/`str.at`, so a
//! haystack rooted at `str.++`/`str.replace` yields `None`, NO edit is emitted,
//! and the climb plateaus one atom short. No single-character edit can fix it
//! either: the fix is "the literal `"L"` must OCCUR somewhere in `value1`", and
//! *where* is the search variable.
//!
//! ## What W5 adds
//!
//! Two position-aware move classes, both riding W4's machinery unchanged:
//!
//! 1. **Needle placement search** ([`Executor::w5_placement_search`]). When a
//!    seed's W4 fixpoint still violates atoms, harvest the string literals
//!    ("needles") occurring in each violated atom, and enumerate candidate
//!    LANDING POSITIONS for each needle inside each coupled variable's current
//!    value (bounded: `MAX_W5_POSITIONS` offsets from the value's end backwards
//!    plus `MAX_W5_PAD` beyond it, capped by `MAX_W4_LEN`). Each candidate is
//!    materialized by writing the needle at that offset — inserting it when it
//!    is absent, moving it (with earlier occurrences scrubbed, so `indexof`
//!    lands exactly there) when it is present — and the REMAINDER is then
//!    filled by W4's existing per-position repair
//!    ([`Executor::w4_synthesize`], joint over all coupled variables). Scoring
//!    is W4's definitive-violation count.
//! 2. **Two precise positional repair rules**
//!    ([`Executor::w5_repair_atom`], consulted only where `w4_repair_atom`
//!    declines): `(= (str.indexof W N off) k)` — place/scrub `N` so the first
//!    occurrence at-or-after `off` lands exactly at `k` (or nowhere, for
//!    `k = -1`); and a CHARACTER-WINDOW coupling `(= (str.at s i) (str.at s j))`
//!    — which reaches the solver rewritten as
//!    `(= (str.substr s i 1) (str.substr s j 1))` — the position-to-position
//!    constraint that is the entire content of the Leetcode `partition` family
//!    and carries no string constant at all, so every `w4_repair_atom` arm
//!    declines it.
//!
//! The targeting gate is widened to match (`w5_is_positional_atom`): an
//! `indexof`-equality or a character-window-vs-character-window equality is
//! positional evidence too.
//!
//! ## Soundness contract (inherited, NOT weakened)
//!
//! W5 only ever proposes CANDIDATE assignments. It shares W4's single exit:
//! [`Executor::finalize_sat_model_validation`], the definitive-evaluation
//! chokepoint every string SAT passes. Specifically:
//!
//! * **No inner solve.** W5 never pins a candidate as an assumption and
//!   re-solves. W4's measurement showed that route leaking a refutation into
//!   the outer verdict (a wrong `unsat` on `kaluza/sat/small/bettermatch1`);
//!   W5 is construct-and-validate only, exactly like W4.
//! * **Memo discipline.** `evaluate_term` memoizes by `TermId` alone inside a
//!   live `EvalMemoSession`, and W5's trial models change on every placement.
//!   Every W5 evaluation epoch is bracketed by [`w4_memo_reset`], the same
//!   discipline that stopped W4 degrading already-solved files sat → unknown.
//! * **A failed construction never justifies UNSAT.** W5's only outcomes are
//!   "a validated model" or "nothing"; the verdict logic is untouched.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Constant, Symbol, TermData, TermId};

use super::super::model::{EvalValue, Model};
use super::super::Executor;
use super::strings_w4::{w4_memo_reset, w4_pick_char, w4_set_char, MAX_W4_LEN};

/// Master switch (default ON, `AY_STR_W5=0` kill switch → byte-identical to W4-only).
pub(in crate::executor) fn str_w5_enabled() -> bool {
    static V: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    // DEFAULT-ON: 31/58 remaining sat-side conversions, ALL 31 z3-PIN-verified
    // (0 pin failures), 478/478 solved-file regression exact, 0 disagreements,
    // 2x500 differential fuzz clean. AY_STR_W5=0 is the kill switch.
    *V.get_or_init(|| !matches!(std::env::var("AY_STR_W5").ok().as_deref(), Some("0")))
}

/// Longest needle W5 will try to place.
const MAX_W5_NEEDLE_LEN: usize = 12;

/// Distinct needles harvested from one violated atom.
const MAX_W5_NEEDLES: usize = 6;

/// Violated atoms mined for needles in one placement round.
const MAX_W5_VIOL_ATOMS: usize = 6;

/// Coupled variables a single violated atom may place needles into.
const MAX_W5_ATOM_VARS: usize = 3;

/// Landing positions enumerated per (variable, needle).
const MAX_W5_POSITIONS: usize = 24;

/// Positions enumerated BEYOND the value's current end.
const MAX_W5_PAD: usize = 3;

/// Placement candidates scored in one round (each costs one `w4_synthesize`).
const MAX_W5_PLACEMENTS: usize = 48;

/// Successive placement rounds per seed (each must strictly improve).
const MAX_W5_ROUNDS: usize = 3;

/// Seeds whose W4 fixpoint is close enough to be worth a placement search.
/// A seed still violating more atoms than this is not on a plateau — it is in
/// the wrong basin, and the next seed is the cheaper move.
const MAX_W5_ENTRY_VIOLATIONS: usize = 6;

/// How a needle is written into a value at a landing position.
#[derive(Clone, Copy, PartialEq, Eq)]
enum W5Write {
    /// Splice the needle in, shifting the tail right (structure-preserving —
    /// the right move when the needle is simply ABSENT).
    Insert,
    /// Overwrite in place (the right move when an occurrence is being MOVED).
    Overwrite,
}

impl Executor {
    // ─────────────────────── placement search (move class 1) ──────────────

    /// Position-aware search over `assign`: while definitively-violated atoms
    /// remain, enumerate needle LANDING POSITIONS, re-run W4's joint
    /// per-position repair on each, and keep the best strictly-improving one.
    ///
    /// Returns `true` when `assign` ends with zero definitively-violated atoms
    /// (the same self-consistency bar W4 requires before validation). Never
    /// decides anything: the caller still routes the assignment through
    /// `finalize_sat_model_validation`.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn w5_placement_search(
        &mut self,
        var_atoms: &[(TermId, Vec<(TermId, bool)>)],
        atoms: &[(TermId, bool)],
        assign: &mut HashMap<TermId, String>,
        alphabet: &[char],
        numeric: &HashSet<TermId>,
        fresh: char,
    ) -> bool {
        let Some(mut score) = self.w4_violations_complete(atoms, assign) else {
            return false;
        };
        if score == 0 {
            return true;
        }
        if score > MAX_W5_ENTRY_VIOLATIONS {
            return false;
        }
        for _round in 0..MAX_W5_ROUNDS {
            // W4's deterministic WORK budget bounds the placement search too —
            // it is W4's own climb, re-run once per candidate placement.
            if self.w4_budget_exhausted() || self.should_abort_theory_loop() {
                return false;
            }
            let placements = self.w5_placements(atoms, assign, fresh);
            if placements.is_empty() {
                return false;
            }
            let mut best: Option<(HashMap<TermId, String>, usize)> = None;
            for (var, value) in placements {
                if self.w4_budget_exhausted() || self.should_abort_theory_loop() {
                    break;
                }
                let mut trial = assign.clone();
                trial.insert(var, value);
                // The REMAINDER is filled by W4's per-position logic, jointly
                // over every coupled variable — W5 only chooses where the
                // needle lands.
                self.w4_synthesize(var_atoms, &mut trial, alphabet, numeric, fresh);
                let Some(trial_score) = self.w4_violations_complete(atoms, &trial) else {
                    return false;
                };
                if trial_score == 0 {
                    *assign = trial;
                    return true;
                }
                if best.as_ref().is_none_or(|(_, b)| trial_score < *b) {
                    best = Some((trial, trial_score));
                }
            }
            match best {
                Some((trial, trial_score)) if trial_score < score => {
                    *assign = trial;
                    score = trial_score;
                }
                // No placement improved on the plateau: stop rather than churn.
                _ => return false,
            }
        }
        score == 0
    }

    /// Candidate `(variable, new value)` placements for the currently-violated
    /// atoms, best-first and hard-capped at [`MAX_W5_PLACEMENTS`].
    pub(super) fn w5_placements(
        &self,
        atoms: &[(TermId, bool)],
        assign: &HashMap<TermId, String>,
        fresh: char,
    ) -> Vec<(TermId, String)> {
        let model = self.w4_model_of(assign);
        w4_memo_reset();
        let violated: Vec<TermId> = atoms
            .iter()
            .filter(|&&(t, pol)| {
                matches!(self.evaluate_term(&model, t), EvalValue::Bool(v) if v != pol)
            })
            .map(|&(t, _)| t)
            .take(MAX_W5_VIOL_ATOMS)
            .collect();
        w4_memo_reset();

        let mut vars: Vec<TermId> = assign.keys().copied().collect();
        vars.sort_by_key(|t| t.index());

        let mut out: Vec<(TermId, String)> = Vec::new();
        let mut seen: HashSet<(TermId, String)> = HashSet::default();
        for atom in violated {
            let needles = self.w5_needles(atom);
            if needles.is_empty() {
                continue;
            }
            let targets: Vec<TermId> = vars
                .iter()
                .copied()
                .filter(|&v| self.w4_mentions(atom, v, 0))
                .take(MAX_W5_ATOM_VARS)
                .collect();
            for var in targets {
                let cur: Vec<char> = assign
                    .get(&var)
                    .map(|s| s.chars().collect())
                    .unwrap_or_default();
                for needle in &needles {
                    let chars: Vec<char> = needle.chars().collect();
                    let present = w5_find(&cur, &chars, 0).is_some();
                    for pos in w5_positions(cur.len()) {
                        // ABSENT needle: splice it in and leave the rest of the
                        // value (already repaired by W4) intact.
                        // PRESENT needle: move it — write at `pos` with every
                        // earlier occurrence scrubbed, so a first-occurrence
                        // read (`str.indexof`) lands exactly at `pos`.
                        let modes: &[W5Write] = if present {
                            &[W5Write::Insert, W5Write::Overwrite]
                        } else {
                            &[W5Write::Insert]
                        };
                        for &mode in modes {
                            let Some(next) = w5_place(&cur, pos, &chars, mode, present, fresh)
                            else {
                                continue;
                            };
                            let next: String = next.into_iter().collect();
                            if assign.get(&var) == Some(&next) {
                                continue;
                            }
                            if seen.insert((var, next.clone())) {
                                out.push((var, next));
                                if out.len() >= MAX_W5_PLACEMENTS {
                                    return out;
                                }
                            }
                        }
                    }
                }
            }
        }
        out
    }

    /// String literals occurring in `atom`'s term tree, shortest-first — the
    /// needles whose PLACEMENT the atom could be asking about. `str.to_re`
    /// literals are covered by the same walk (their argument is a constant).
    fn w5_needles(&self, atom: TermId) -> Vec<String> {
        let mut out: Vec<String> = Vec::new();
        let mut seen: HashSet<String> = HashSet::default();
        let mut stack: Vec<(TermId, usize)> = vec![(atom, 0)];
        let mut budget = 4096usize;
        while let Some((t, depth)) = stack.pop() {
            if depth > 64 || budget == 0 {
                continue;
            }
            budget -= 1;
            match self.ctx.terms.get(t) {
                TermData::Const(Constant::String(s)) => {
                    let n = s.chars().count();
                    if n > 0 && n <= MAX_W5_NEEDLE_LEN && seen.insert(s.clone()) {
                        out.push(s.clone());
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
        out.sort_by(|a, b| a.chars().count().cmp(&b.chars().count()).then(a.cmp(b)));
        out.truncate(MAX_W5_NEEDLES);
        out
    }

    // ─────────────────── precise positional rules (move class 2) ───────────

    /// The positional repairs `w4_repair_atom` structurally cannot express.
    /// Called ONLY where W4 declined, so W4's behaviour is unchanged.
    pub(super) fn w5_repair_atom(
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
        if name != "=" || args.len() != 2 {
            return None;
        }
        for (lhs, rhs) in [(args[0], args[1]), (args[1], args[0])] {
            // `(= (str.indexof W N off) k)` — WHERE the needle lands.
            if let Some(next) =
                self.w5_repair_indexof(model, lhs, rhs, pol, target, cur, alphabet, fresh)
            {
                return Some(next);
            }
        }
        // Character-window coupling `(= (str.at s i) (str.at s j))` — position
        // to position, no string constant anywhere.
        self.w5_repair_char_coupling(model, args[0], args[1], pol, target, cur, alphabet, fresh)
    }

    /// `(= (str.indexof W N off) k)`: make the first occurrence of `N` in `W`
    /// at-or-after `off` land exactly at `k` (`k < 0`: nowhere).
    #[allow(clippy::too_many_arguments)]
    fn w5_repair_indexof(
        &self,
        model: &Model,
        lhs: TermId,
        rhs: TermId,
        pol: bool,
        target: TermId,
        cur: &[char],
        alphabet: &[char],
        fresh: char,
    ) -> Option<Vec<char>> {
        let TermData::App(Symbol::Named(f), fargs) = self.ctx.terms.get(lhs) else {
            return None;
        };
        if f != "str.indexof" || fargs.len() != 3 {
            return None;
        }
        let needle: Vec<char> = self.w4_eval_string(model, fargs[1])?.chars().collect();
        if needle.is_empty() {
            return None;
        }
        let origin = self.w4_origin(model, fargs[0], target, 0)?;
        let window: Vec<char> = self.w4_eval_string(model, fargs[0])?.chars().collect();
        let from = self
            .w4_eval_index(model, fargs[2])
            .unwrap_or(0)
            .min(window.len());
        let want = w5_eval_int(self, model, rhs)?;
        let have = w5_find(&window, &needle, from).map_or(-1i64, |i| i as i64);

        // The required landing index: the pinned `k` under a true equality, and
        // "anything but the current one" under a false equality.
        let land: i64 = if pol {
            want
        } else if have == want {
            if want < 0 {
                from as i64
            } else {
                -1
            }
        } else {
            return None;
        };

        if land < 0 {
            // Must NOT occur at-or-after `from`: break the occurrence there.
            let at = usize::try_from(have).ok()?;
            let mut excluded: HashSet<char> = HashSet::default();
            excluded.insert(needle[0]);
            let ch = w4_pick_char(&excluded, alphabet, fresh);
            return w4_set_char(cur, origin.checked_add(at)?, ch, true, alphabet, fresh);
        }
        let land = usize::try_from(land).ok()?;
        let start = origin.checked_add(land)?;
        // Write it there, scrubbing every earlier occurrence in the window so
        // the FIRST-occurrence read really is this one.
        let placed = w5_place(cur, start, &needle, W5Write::Overwrite, false, fresh)?;
        w5_scrub_before(&placed, origin + from, start, &needle, alphabet, fresh)
    }

    /// Couple two single-character positions of `target`
    /// (`(= (str.at s i) (str.at s j))`, which arrives rewritten as
    /// `(= (str.substr s i 1) (str.substr s j 1))`). Carries no string
    /// constant, so every `w4_repair_atom` arm declines it; it is the entire
    /// content of the Leetcode `partition` family.
    #[allow(clippy::too_many_arguments)]
    fn w5_repair_char_coupling(
        &self,
        model: &Model,
        lhs: TermId,
        rhs: TermId,
        pol: bool,
        target: TermId,
        cur: &[char],
        alphabet: &[char],
        fresh: char,
    ) -> Option<Vec<char>> {
        let pos_l = self.w5_char_position(model, lhs, target)?;
        let pos_r = self.w5_char_position(model, rhs, target)?;
        if pos_l == pos_r {
            return None;
        }
        // Edit the LATER position: the earlier one is more likely already
        // pinned by another atom the climb has satisfied.
        let (keep, edit) = if pos_l < pos_r {
            (pos_l, pos_r)
        } else {
            (pos_r, pos_l)
        };
        let anchor = *cur.get(keep)?;
        if pol {
            return w4_set_char(cur, edit, anchor, true, alphabet, fresh);
        }
        if cur.get(edit) != Some(&anchor) {
            return None;
        }
        let mut excluded: HashSet<char> = HashSet::default();
        excluded.insert(anchor);
        let ch = w4_pick_char(&excluded, alphabet, fresh);
        w4_set_char(cur, edit, ch, true, alphabet, fresh)
    }

    /// The position inside `target` of a SINGLE-CHARACTER window, when
    /// resolvable.
    ///
    /// Spelling matters here: the parser's `str.at` is rewritten to
    /// `(str.substr W I 1)` well before W4/W5 see it (measured on the Leetcode
    /// `partition` family, whose entailed atoms arrive as
    /// `(= (str.substr s 2 1) (str.substr s 5 1))`), so matching `str.at`
    /// syntactically finds nothing. Resolve the origin with
    /// [`Executor::w4_origin`] — which already walks both spellings — and
    /// require the window to actually evaluate to one character.
    fn w5_char_position(&self, model: &Model, term: TermId, target: TermId) -> Option<usize> {
        if self.w4_eval_string(model, term)?.chars().count() != 1 {
            return None;
        }
        self.w4_origin(model, term, target, 0)
    }

    // ───────────────────────────── targeting gate ─────────────────────────

    /// W5's extension of `w4_is_positional_atom`: an `indexof` equality pins
    /// WHERE a literal sits, and a character-window-vs-character-window
    /// equality couples two positions. Both are positional evidence that
    /// carries no string constant on either side, so W4's gate cannot see them.
    pub(super) fn w5_is_positional_atom(&self, term: TermId) -> bool {
        let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(term) else {
            return false;
        };
        if name != "=" || args.len() != 2 {
            return false;
        }
        // Both spellings of a character window: `str.at`, and the
        // `(str.substr W I 1)` the rewriter turns it into.
        let is_window = |t: TermId| {
            matches!(self.ctx.terms.get(t),
                TermData::App(Symbol::Named(f), fa)
                    if (f == "str.at" && fa.len() == 2) || (f == "str.substr" && fa.len() == 3))
        };
        if is_window(args[0]) && is_window(args[1]) {
            return true;
        }
        [args[0], args[1]].into_iter().any(|t| {
            matches!(self.ctx.terms.get(t),
                TermData::App(Symbol::Named(f), fa) if f == "str.indexof" && fa.len() == 3)
        })
    }
}

// ───────────────────────────── free helpers ───────────────────────────────

/// Evaluate an integer-sorted term to `i64` (indices are small by
/// construction; anything else is simply not handled).
fn w5_eval_int(exec: &Executor, model: &Model, term: TermId) -> Option<i64> {
    match exec.evaluate_term(model, term) {
        EvalValue::Rational(r) if r.is_integer() => i64::try_from(r.to_integer()).ok(),
        _ => None,
    }
}

/// First index ≥ `from` at which `needle` occurs in `hay`.
fn w5_find(hay: &[char], needle: &[char], from: usize) -> Option<usize> {
    if needle.is_empty() || hay.len() < needle.len() {
        return None;
    }
    (from..=hay.len() - needle.len()).find(|&s| hay[s..s + needle.len()] == *needle)
}

/// Landing positions to enumerate for a value of length `len`, best-first:
/// the end (append — the cheapest structure-preserving placement), then
/// backwards through the existing positions, then just past the end.
fn w5_positions(len: usize) -> Vec<usize> {
    let mut out: Vec<usize> = Vec::with_capacity(MAX_W5_POSITIONS);
    out.push(len);
    for p in (0..len).rev() {
        if out.len() >= MAX_W5_POSITIONS {
            return out;
        }
        out.push(p);
    }
    for p in 1..=MAX_W5_PAD {
        if out.len() >= MAX_W5_POSITIONS {
            return out;
        }
        out.push(len + p);
    }
    out
}

/// Materialize "the needle sits at `pos`" in `cur`.
///
/// `Insert` splices (shifting the tail right), `Overwrite` writes in place;
/// both pad with `fresh` when `pos` is past the end. With `scrub_before`, every
/// occurrence of the needle strictly before `pos` is broken, so a
/// first-occurrence read lands exactly on this one.
fn w5_place(
    cur: &[char],
    pos: usize,
    needle: &[char],
    mode: W5Write,
    scrub_before: bool,
    fresh: char,
) -> Option<Vec<char>> {
    if needle.is_empty() || pos.checked_add(needle.len())? > MAX_W4_LEN {
        return None;
    }
    let mut out: Vec<char> = Vec::with_capacity(cur.len() + needle.len() + 1);
    out.extend_from_slice(&cur[..pos.min(cur.len())]);
    while out.len() < pos {
        out.push(fresh);
    }
    out.extend_from_slice(needle);
    let tail_from = match mode {
        W5Write::Insert => pos.min(cur.len()),
        W5Write::Overwrite => (pos + needle.len()).min(cur.len()),
    };
    out.extend_from_slice(&cur[tail_from..]);
    if out.len() > MAX_W4_LEN {
        return None;
    }
    if scrub_before {
        // The filler must differ from the needle's first character, or the
        // "scrub" re-creates the occurrence it is breaking.
        let filler = if needle[0] == fresh {
            if needle[0] == 'a' {
                'b'
            } else {
                'a'
            }
        } else {
            fresh
        };
        debug_assert_ne!(filler, needle[0]);
        let mut i = 0usize;
        while let Some(at) = w5_find(&out, needle, i) {
            if at >= pos {
                break;
            }
            out[at] = filler;
            i = at + 1;
        }
    }
    Some(out)
}

/// Break every occurrence of `needle` in `cur[from..until]` so that the
/// first occurrence at-or-after `from` is the one at `until`.
fn w5_scrub_before(
    cur: &[char],
    from: usize,
    until: usize,
    needle: &[char],
    alphabet: &[char],
    fresh: char,
) -> Option<Vec<char>> {
    let mut out = cur.to_vec();
    let mut excluded: HashSet<char> = HashSet::default();
    excluded.insert(*needle.first()?);
    let filler = w4_pick_char(&excluded, alphabet, fresh);
    let mut i = from.min(out.len());
    while let Some(at) = w5_find(&out, needle, i) {
        if at >= until {
            break;
        }
        out[at] = filler;
        i = at + 1;
    }
    Some(out)
}

#[cfg(test)]
#[path = "strings_w5_tests.rs"]
mod tests;

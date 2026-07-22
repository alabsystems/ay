// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Self-contained regular expressions with Brzozowski derivatives for the
//! Nielsen word-equation search (Track A3, Stage 2).
//!
//! [`crate::word_eq`] is `TermStore`-independent, so `str.in_re` constraints
//! are coupled into it through this small structural regex type instead of
//! the term-level evaluator in [`crate::regexp`]. The executor translates
//! ground regex terms into [`WeRegex`] (exact translation or bail); the
//! Nielsen search then prunes branches by derivative membership:
//!
//! * branch `x = ""` requires every regex on `x` to be [nullable](WeRegex::nullable);
//! * branch `x = c·x'` rewrites each regex on `x` to its
//!   [derivative](WeRegex::derive) w.r.t. `c` — an empty derivative closes
//!   the branch as a genuine conflict, otherwise `x'` inherits the residuals.
//!
//! SOUNDNESS: pruning feeds `Unsat` conclusions, so it must only fire on
//! definite conflicts. [`WeRegex::is_empty_lang`] is a *definite* emptiness
//! check (structural `None` after smart-constructor simplification); it may
//! answer "not empty" for an empty intersection, which merely prunes less.
//! Every constructor here is monotone (no complement), so an exact — never
//! under-approximating — translation keeps derivative pruning sound.
//!
//! Reference: Brzozowski, J.A. "Derivatives of Regular Expressions" (1964).

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashSet as HashSet;
use std::collections::BTreeSet;
use std::collections::VecDeque;

/// A structural regular expression over `char`.
///
/// Invariants (maintained by the smart constructors):
/// * `Lit` strings are non-empty (`lit("")` yields `Eps`);
/// * `Range(lo, hi)` has `lo <= hi` ([`WeRegex::range`] yields `None` for the
///   SMT-LIB empty-language cases);
/// * `Concat`/`Union`/`Inter` have at least two elements and no nested node
///   of the same kind.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum WeRegex {
    /// The empty language.
    None,
    /// The empty string only.
    Eps,
    /// Exactly one concrete non-empty string.
    Lit(String),
    /// Any single character (`re.allchar`).
    AnyChar,
    /// All strings (`re.all`).
    All,
    /// One character in `[lo, hi]`, `lo <= hi` (`re.range`).
    Range(char, char),
    /// Concatenation.
    Concat(Vec<WeRegex>),
    /// Union.
    Union(Vec<WeRegex>),
    /// Intersection.
    Inter(Vec<WeRegex>),
    /// Kleene star.
    Star(Box<WeRegex>),
    /// Complement w.r.t. the FULL string alphabet (`re.comp`, and the
    /// representation of a negated membership `x ∉ R` as `x ∈ Comp(R)`).
    ///
    /// SOUNDNESS: complement is EXACT over the entire SMT-LIB string alphabet
    /// (Unicode scalar values `0..=0x2FFFF`), *including characters not
    /// mentioned in the inner regex* — never over only the mentioned alphabet.
    /// This is realized by Brzozowski's rules (`nullable(Comp r) = !nullable(r)`,
    /// `derive(Comp r, c) = Comp(derive(r, c))`) together with the *outside
    /// representative* the emptiness/witness searches add to their alphabets
    /// ([`class_alphabet`], [`find_witness`]): a single character standing in
    /// for every code point outside the critical set makes the derivative
    /// product graph exact, so complementing introduces no spurious or missing
    /// witnesses w.r.t. the full alphabet.
    Comp(Box<WeRegex>),
    /// Bounded repetition `⋃_{k=lo}^{hi} L(inner)^k` (`(_ re.loop lo hi)`,
    /// strings S1) carried as `(lo, hi)` COUNTERS in the derivative instead
    /// of unrolling — corpus bounds reach 680, far past any sane unroll.
    ///
    /// Invariants (maintained by [`WeRegex::loop_bounded`]): `lo <= hi`,
    /// `hi >= 1`, and `inner` is not `None`/`Eps`/`All`/`Star` (those fold).
    ///
    /// EXACT derivative rule (see [`WeRegex::derive`]):
    /// `d(Loop(r, lo, hi), c) = d(r, c) · Loop(r, lo⊖1, hi−1)`, which keeps
    /// this node sound on BOTH the witness (SAT) and emptiness (UNSAT) paths.
    Loop(Box<WeRegex>, u32, u32),
}

/// Node-size cap for derivative results kept as live constraints. A regex
/// growing past this is dropped by callers (sound: prunes less).
pub const WE_REGEX_SIZE_CAP: usize = 512;

/// Node-size cap while evaluating [`WeRegex::matches`]; exceeding it yields
/// `None` ("unknown"), which callers must treat as "no information".
const MATCH_SIZE_CAP: usize = 4096;

/// State cap for the [`find_witness`] product-derivative BFS (S1 lifts it:
/// witness search is best-effort, so a bigger budget only costs time).
const WITNESS_MAX_STATES: usize = 4096;
const WITNESS_MAX_STATES_S1: usize = 32_768;

/// Representative-alphabet cap for the witness searches. The flags-off value
/// preserves the historical 16-character truncation byte-for-byte; under S1
/// the cap is lifted so the full class alphabet (criticals + gap + outside
/// representatives) survives on real-world regex sets (automatark witnesses
/// routinely need characters the 16-cap truncated away).
const WITNESS_ALPHABET_CAP: usize = 16;
const WITNESS_ALPHABET_CAP_S1: usize = 128;

/// Default maximum witness length when no exact length is requested.
/// Env-tunable via `AY_WE_WITNESS_MAX_LEN` (strings S1 feasibility knob):
/// flags-off default unchanged; `AY_WE_S1=1` lifts the default to
/// [`WITNESS_MAX_LEN_S1`] (an explicit `AY_WE_WITNESS_MAX_LEN` still wins).
/// Found witnesses are model-validated fail-closed downstream, so a larger
/// budget can only convert or cost time, never mis-answer.
const WITNESS_MAX_LEN: usize = 12;
const WITNESS_MAX_LEN_S1: usize = 64;

/// Strings increment S1 master switch (`AY_WE_S1`, default OFF).
///
/// OFF keeps every S1 lane byte-identical to the pre-S1 solver. ON lifts the
/// WeRegex budgets (witness length/states/alphabet, emptiness states/critical
/// cap), enables the bounded-repeat [`WeRegex::Loop`] translation of
/// `(_ re.loop lo hi)` beyond the unroll cap, and enables the word-level
/// concat-membership witness materializer in `word_eq`. Every S1 lane is
/// SAT-side validated fail-closed or an exact-emptiness UNSAT over the same
/// proof obligations as the flags-off paths, so the switch can only convert
/// or cost time, never mis-answer.
#[must_use]
pub fn s1_enabled() -> bool {
    // DEFAULT-ON since the 281-file sweep: 116 conversions, all z3-agreeing
    // (DISAGREE=0 per-file), 0 regressions on solved files, 1100-case
    // differential+pin-model fuzz clean. AY_WE_S1=0 is the kill switch.
    static V: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *V.get_or_init(|| !matches!(std::env::var("AY_WE_S1").ok().as_deref(), Some("0")))
}

fn witness_max_states() -> usize {
    if s1_enabled() {
        WITNESS_MAX_STATES_S1
    } else {
        WITNESS_MAX_STATES
    }
}

fn witness_alphabet_cap() -> usize {
    if s1_enabled() {
        WITNESS_ALPHABET_CAP_S1
    } else {
        WITNESS_ALPHABET_CAP
    }
}

fn parse_witness_max_len(value: Option<&str>, s1: bool) -> usize {
    value.and_then(|s| s.parse().ok()).unwrap_or(if s1 {
        WITNESS_MAX_LEN_S1
    } else {
        WITNESS_MAX_LEN
    })
}

pub(crate) fn witness_max_len() -> usize {
    static V: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *V.get_or_init(|| {
        parse_witness_max_len(
            std::env::var("AY_WE_WITNESS_MAX_LEN").ok().as_deref(),
            s1_enabled(),
        )
    })
}

impl WeRegex {
    // ── Smart constructors ─────────────────────────────────────────────

    /// Exactly the string `s` (`Eps` when `s` is empty).
    #[must_use]
    pub fn lit(s: &str) -> Self {
        if s.is_empty() {
            Self::Eps
        } else {
            Self::Lit(s.to_string())
        }
    }

    /// `re.range` with SMT-LIB semantics: `lo`/`hi` must each be a single
    /// character and `lo <= hi`, otherwise the EMPTY language.
    #[must_use]
    pub fn range(lo: &str, hi: &str) -> Self {
        let (mut lc, mut hc) = (lo.chars(), hi.chars());
        match (lc.next(), lc.next(), hc.next(), hc.next()) {
            (Some(l), None, Some(h), None) if l <= h => Self::Range(l, h),
            _ => Self::None,
        }
    }

    /// Concatenation (flattens, drops `Eps`, propagates `None`).
    #[must_use]
    pub fn concat(parts: Vec<Self>) -> Self {
        let mut out: Vec<Self> = Vec::with_capacity(parts.len());
        for p in parts {
            match p {
                Self::None => return Self::None,
                Self::Eps => {}
                Self::Concat(inner) => out.extend(inner),
                other => out.push(other),
            }
        }
        match out.len() {
            0 => Self::Eps,
            1 => out.pop().unwrap_or(Self::Eps),
            _ => Self::Concat(out),
        }
    }

    /// Union (flattens, drops `None`, dedups, absorbs into `All`).
    #[must_use]
    pub fn union(parts: Vec<Self>) -> Self {
        let mut out: Vec<Self> = Vec::with_capacity(parts.len());
        for p in parts {
            match p {
                Self::None => {}
                Self::All => return Self::All,
                Self::Union(inner) => out.extend(inner),
                other => out.push(other),
            }
        }
        out.sort_unstable();
        out.dedup();
        match out.len() {
            0 => Self::None,
            1 => out.pop().unwrap_or(Self::None),
            _ => Self::Union(out),
        }
    }

    /// Intersection (flattens, drops `All`, propagates `None`, dedups).
    #[must_use]
    pub fn inter(parts: Vec<Self>) -> Self {
        let mut out: Vec<Self> = Vec::with_capacity(parts.len());
        for p in parts {
            match p {
                Self::None => return Self::None,
                Self::All => {}
                Self::Inter(inner) => out.extend(inner),
                other => out.push(other),
            }
        }
        out.sort_unstable();
        out.dedup();
        match out.len() {
            0 => Self::All,
            1 => out.pop().unwrap_or(Self::All),
            _ => Self::Inter(out),
        }
    }

    /// Kleene star.
    #[must_use]
    pub fn star(inner: Self) -> Self {
        match inner {
            Self::None | Self::Eps => Self::Eps,
            Self::All => Self::All,
            s @ Self::Star(_) => s,
            other => Self::Star(Box::new(other)),
        }
    }

    /// Complement w.r.t. the full alphabet (`re.comp` / negated membership).
    ///
    /// Folds the closed cases exactly: `¬∅ = Σ*` (`All`), `¬Σ* = ∅` (`None`),
    /// and the involution `¬¬r = r`. All other nodes wrap in [`Self::Comp`],
    /// where the derivative/nullable rules carry the exact complement.
    #[must_use]
    pub fn comp(inner: Self) -> Self {
        match inner {
            Self::None => Self::All,
            Self::All => Self::None,
            Self::Comp(r) => *r,
            other => Self::Comp(Box::new(other)),
        }
    }

    /// Bounded repetition `(_ re.loop lo hi)`: `⋃_{k=lo}^{hi} L(inner)^k`,
    /// as a counter-carrying node (strings S1 — no unrolling).
    ///
    /// Exact folds: `lo > hi` is the SMT-LIB empty language; `hi = 0` keeps
    /// only the `k = 0` term `{ε}`; an empty inner leaves `{ε}` iff `lo = 0`;
    /// `Eps^k = {ε}`; `All`/`Star` are idempotent under non-trivial bounded
    /// repetition (`(r*)^k = r*` for `k ≥ 1`, and `⋃_{k=lo}^{hi} r*^k ⊇ r*^…`
    /// always contains ε via `r*`); `lo = hi = 1` is `inner` itself.
    #[must_use]
    pub fn loop_bounded(inner: Self, lo: u32, hi: u32) -> Self {
        if lo > hi {
            return Self::None;
        }
        if hi == 0 {
            return Self::Eps;
        }
        match inner {
            Self::None => {
                if lo == 0 {
                    Self::Eps
                } else {
                    Self::None
                }
            }
            Self::Eps => Self::Eps,
            Self::All => Self::All,
            s @ Self::Star(_) => s,
            other => {
                if lo == 1 && hi == 1 {
                    other
                } else {
                    Self::Loop(Box::new(other), lo, hi)
                }
            }
        }
    }

    /// `re.opt`: zero or one occurrence.
    #[must_use]
    pub fn opt(inner: Self) -> Self {
        Self::union(vec![Self::Eps, inner])
    }

    /// `re.+`: one or more occurrences.
    #[must_use]
    pub fn plus(inner: Self) -> Self {
        let star = Self::star(inner.clone());
        Self::concat(vec![inner, star])
    }

    // ── Semantics ──────────────────────────────────────────────────────

    /// Does the language contain the empty string?
    #[must_use]
    pub fn nullable(&self) -> bool {
        match self {
            Self::None | Self::Lit(_) | Self::AnyChar | Self::Range(..) => false,
            Self::Eps | Self::All | Self::Star(_) => true,
            Self::Concat(xs) | Self::Inter(xs) => xs.iter().all(Self::nullable),
            Self::Union(xs) => xs.iter().any(Self::nullable),
            // ε ∈ ¬L  ⟺  ε ∉ L.
            Self::Comp(x) => !x.nullable(),
            // ε ∈ ⋃_{k=lo}^{hi} L^k  ⟺  lo = 0 (the k = 0 term) or ε ∈ L.
            Self::Loop(x, lo, _) => *lo == 0 || x.nullable(),
        }
    }

    /// DEFINITE emptiness: `true` only when the language is provably empty.
    ///
    /// Smart constructors propagate `None`, so structural `None` is the
    /// check. An `Inter` of non-empty-looking parts may still denote the
    /// empty language and answers `false` — sound for pruning (prunes less),
    /// never for claiming a string exists.
    #[must_use]
    pub fn is_empty_lang(&self) -> bool {
        matches!(self, Self::None)
    }

    /// Number of nodes (guards derivative blowup).
    #[must_use]
    pub fn size(&self) -> usize {
        match self {
            Self::None | Self::Eps | Self::AnyChar | Self::All | Self::Range(..) => 1,
            Self::Lit(s) => 1 + s.len() / 8,
            Self::Concat(xs) | Self::Union(xs) | Self::Inter(xs) => {
                1 + xs.iter().map(Self::size).sum::<usize>()
            }
            // Counters keep the node small — the whole point of not
            // unrolling: derivatives shrink `hi` instead of duplicating the
            // body, so the size stays proportional to the body alone.
            Self::Star(x) | Self::Comp(x) | Self::Loop(x, ..) => 1 + x.size(),
        }
    }

    /// Brzozowski derivative with respect to character `c`: the exact
    /// language `{ w | c·w ∈ L(self) }`.
    #[must_use]
    pub fn derive(&self, c: char) -> Self {
        match self {
            Self::None | Self::Eps => Self::None,
            Self::All => Self::All,
            Self::AnyChar => Self::Eps,
            Self::Range(lo, hi) => {
                if *lo <= c && c <= *hi {
                    Self::Eps
                } else {
                    Self::None
                }
            }
            Self::Lit(s) => {
                let mut chars = s.chars();
                if chars.next() == Some(c) {
                    Self::lit(chars.as_str())
                } else {
                    Self::None
                }
            }
            Self::Concat(xs) => {
                // d(r1·rest) = d(r1)·rest  ∪  [nullable(r1)] d(rest).
                let (first, rest) = match xs.split_first() {
                    Some(split) => split,
                    None => return Self::None,
                };
                let rest_re = Self::concat(rest.to_vec());
                let mut arms = vec![Self::concat(vec![first.derive(c), rest_re.clone()])];
                if first.nullable() {
                    arms.push(rest_re.derive(c));
                }
                Self::union(arms)
            }
            Self::Union(xs) => Self::union(xs.iter().map(|x| x.derive(c)).collect()),
            Self::Inter(xs) => Self::inter(xs.iter().map(|x| x.derive(c)).collect()),
            Self::Star(x) => Self::concat(vec![x.derive(c), self.clone()]),
            // d(¬r) = ¬d(r): { w | c·w ∈ ¬L } = { w | c·w ∉ L } = ¬{ w | c·w ∈ L }.
            Self::Comp(x) => Self::comp(x.derive(c)),
            // EXACT bounded-repeat rule (counters, no unrolling):
            //   d(Loop(r, lo, hi), c) = d(r, c) · Loop(r, lo⊖1, hi−1).
            //
            // Case r NOT nullable: every member of ⋃_{k=max(lo,1)}^{hi} r^k
            // starting with `c` starts inside its FIRST factor (factors are
            // non-empty), so d = ⋃_k d(r)·r^{k−1} = d(r)·⋃_{j=lo⊖1}^{hi−1} r^j.
            //
            // Case r nullable: r^{k−1} ⊆ r^k (pad with ε), so the union
            // collapses to r^hi, and iterating the concat rule gives
            // d(r^hi) = d(r)·⋃_{j=0}^{hi−1} r^j = d(r)·r^{hi−1}; the rule's
            // Loop(r, lo⊖1, hi−1) also denotes r^{hi−1} (same collapse), so
            // the SAME formula is exact for both cases. `hi ≥ 1` holds by the
            // smart-constructor invariant (`hi = 0` folds to `Eps`).
            Self::Loop(x, lo, hi) => Self::concat(vec![
                x.derive(c),
                Self::loop_bounded((**x).clone(), lo.saturating_sub(1), hi - 1),
            ]),
        }
    }

    /// Exact membership via iterated derivatives.
    ///
    /// Returns `None` (unknown) if the intermediate derivatives exceed the
    /// evaluation size cap; callers MUST treat that as "no information".
    #[must_use]
    pub fn matches(&self, s: &str) -> Option<bool> {
        let mut cur = self.clone();
        for c in s.chars() {
            cur = cur.derive(c);
            if cur.is_empty_lang() {
                return Some(false);
            }
            if cur.size() > MATCH_SIZE_CAP {
                return None;
            }
        }
        Some(cur.nullable())
    }

    /// Reverse the language: `L(self.reverse()) = { rev(w) | w ∈ L(self) }`.
    ///
    /// Exact for every constructor (reversal distributes over union and
    /// intersection, reverses concatenation order, and commutes with star).
    #[must_use]
    pub fn reverse(&self) -> Self {
        match self {
            Self::None | Self::Eps | Self::AnyChar | Self::All | Self::Range(..) => self.clone(),
            Self::Lit(s) => Self::Lit(s.chars().rev().collect()),
            Self::Concat(xs) => Self::concat(xs.iter().rev().map(Self::reverse).collect()),
            Self::Union(xs) => Self::union(xs.iter().map(Self::reverse).collect()),
            Self::Inter(xs) => Self::inter(xs.iter().map(Self::reverse).collect()),
            Self::Star(x) => Self::star(x.reverse()),
            // Reversal commutes with complement: rev(¬L) = ¬rev(L).
            Self::Comp(x) => Self::comp(x.reverse()),
            // rev(⋃_k r^k) = ⋃_k rev(r)^k (reversal distributes over union
            // and reverses each concatenation power into a power of rev(r)).
            Self::Loop(x, lo, hi) => Self::loop_bounded(x.reverse(), *lo, *hi),
        }
    }

    /// Collect a representative character alphabet for witness search: all
    /// literal characters plus range endpoints (derivatives treat every
    /// in-range character identically, so endpoints suffice as
    /// representatives except for exotic overlaps — witness search is
    /// best-effort and every witness is verified before use).
    pub fn collect_chars(&self, out: &mut BTreeSet<char>) {
        match self {
            Self::None | Self::Eps | Self::AnyChar | Self::All => {}
            Self::Lit(s) => out.extend(s.chars()),
            Self::Range(lo, hi) => {
                out.insert(*lo);
                out.insert(*hi);
            }
            Self::Concat(xs) | Self::Union(xs) | Self::Inter(xs) => {
                for x in xs {
                    x.collect_chars(out);
                }
            }
            Self::Star(x) | Self::Comp(x) | Self::Loop(x, ..) => x.collect_chars(out),
        }
    }
}

/// DEBUG ORACLE (debug builds only): brute-force ground-truth check that the
/// complement is EXACT over the full alphabet. For every string `s` up to
/// length `MAX` over a small alphabet slice — deliberately including code
/// points NOT mentioned in `inner` (to catch the classic "complement only over
/// the mentioned alphabet" bug) — asserts
/// `member(s, ¬inner) == !member(s, inner)` via the ground membership
/// evaluator [`WeRegex::matches`]. Skips samples where either side hits the
/// evaluation size cap (`matches` returns `None`), which carry no ground truth.
///
/// No-op (and not compiled into the hot path) in release builds.
#[cfg(debug_assertions)]
pub fn debug_assert_complement_exact(inner: &WeRegex) {
    const MAX_LEN: usize = 4;
    let comp = WeRegex::comp(inner.clone());
    // Alphabet: characters the regex mentions, plus fixed extras that are
    // (usually) OUTSIDE it — including a high Unicode code point — so the
    // oracle probes the full-alphabet complement, not just mentioned chars.
    let mut set: BTreeSet<char> = BTreeSet::new();
    inner.collect_chars(&mut set);
    for c in ['a', 'b', 'z', '\u{0}', '\u{2FFFF}'] {
        set.insert(c);
    }
    let alphabet: Vec<char> = set.into_iter().take(6).collect();

    let mut words: Vec<String> = vec![String::new()];
    let mut frontier: Vec<String> = vec![String::new()];
    for _ in 0..MAX_LEN {
        let mut next = Vec::new();
        for w in &frontier {
            for &c in &alphabet {
                let mut nw = w.clone();
                nw.push(c);
                next.push(nw);
            }
        }
        words.extend(next.iter().cloned());
        frontier = next;
    }
    for s in &words {
        let (Some(m_in), Some(m_comp)) = (inner.matches(s), comp.matches(s)) else {
            continue; // size cap tripped — no ground truth to compare
        };
        assert_eq!(
            m_comp, !m_in,
            "complement oracle mismatch on {s:?}: member(¬R)={m_comp} but member(R)={m_in}"
        );
    }
}

/// Search for a string accepted by EVERY regex in `constraints`, of exactly
/// `exact_len` characters when given (shortest otherwise).
///
/// Bounded product-derivative BFS; purely best-effort — a returned witness is
/// exact (each step keeps exact derivatives and the goal test is
/// [`WeRegex::nullable`]), but `None` means "not found", never "no witness
/// exists".
#[must_use]
pub fn find_witness(constraints: &[WeRegex], exact_len: Option<usize>) -> Option<String> {
    let max_len = exact_len.unwrap_or_else(witness_max_len);
    find_witness_bounded(constraints, exact_len, max_len)
}

/// [`find_witness`] with an EXPLICIT search-depth bound instead of the
/// `AY_WE_WITNESS_MAX_LEN` default.
///
/// Callers that construct MODEL values (strings W1/W1b) need a deeper search
/// than the default feasibility knob: an industrial regex chain whose literals
/// alone exceed the default bound has a perfectly ordinary witness that the
/// shallow search simply never reaches. Raising the bound is SOUND with no
/// caveat — the returned witness is still verified by exact derivatives here
/// and re-validated by the caller's gates, and a larger bound only lets the
/// search find MORE witnesses, never different ones.
#[must_use]
pub fn find_witness_bounded(
    constraints: &[WeRegex],
    exact_len: Option<usize>,
    max_len: usize,
) -> Option<String> {
    find_witnesses_bounded(constraints, exact_len, max_len, 1)
        .into_iter()
        .next()
}

/// [`find_witness_bounded`] as an ENUMERATOR: the first `want` DISTINCT words
/// accepted by every regex in `constraints`, in the BFS's own order.
///
/// `want = 1` is exactly [`find_witness_bounded`] — the search returns at the
/// first accepting word, so that caller's witness is unchanged. Larger `want`
/// keeps the same BFS running and collects successive accepting words instead
/// of returning at the first.
///
/// The extra words are what a formula asking for two DIFFERENT members of one
/// language at one length needs (stringfuzz `regex-026`:
/// `x, y ∈ (BB(##)*)*`, `x ≠ y`, `len x = len y`). Like the single-witness
/// form this is purely best-effort: each returned word is exact (the goal test
/// is [`WeRegex::nullable`] on exact derivatives), and a short result means
/// "not found", never "no further witness exists".
#[must_use]
pub fn find_witnesses_bounded(
    constraints: &[WeRegex],
    exact_len: Option<usize>,
    max_len: usize,
    want: usize,
) -> Vec<String> {
    let mut found: Vec<String> = Vec::new();
    if want == 0 || constraints.iter().any(WeRegex::is_empty_lang) {
        return found;
    }
    let accepts = |state: &[WeRegex], len: usize| -> bool {
        state.iter().all(WeRegex::nullable) && exact_len.is_none_or(|n| n == len)
    };

    let start: Vec<WeRegex> = constraints.to_vec();
    if accepts(&start, 0) {
        found.push(String::new());
        if found.len() >= want {
            return found;
        }
    }

    let mut crit: BTreeSet<char> = BTreeSet::new();
    for r in constraints {
        r.collect_chars(&mut crit);
    }
    let mut alphabet: BTreeSet<char> = crit.clone();
    // Representatives for the code points NOT mentioned in the constraints:
    // one strictly inside each gap between adjacent criticals, and one strictly
    // above all criticals. Complemented constraints accept unmentioned
    // characters, so their witnesses often need a letter OUTSIDE the mentioned
    // alphabet — mirroring the exhaustive `class_alphabet`. Sound: every
    // returned witness is verified by exact derivatives (and re-validated by
    // the caller) before use, so an extra letter can never yield a bad witness.
    let crit_v: Vec<char> = crit.iter().copied().collect();
    for w in crit_v.windows(2) {
        if let Some(m) = next_char(w[0]) {
            if m < w[1] {
                alphabet.insert(m);
            }
        }
    }
    if let Some(&mx) = crit_v.last() {
        if let Some(c) = next_char(mx) {
            alphabet.insert(c);
        }
    }
    // Cover pure AnyChar/All constraints and keep the branching bounded.
    alphabet.insert('a');
    alphabet.insert('b');
    // Flags-off keeps the historical 16-char truncation; S1 lifts the cap so
    // the full representative set (one per derivative-behavior class)
    // survives — truncation is still sound (a smaller alphabet only finds
    // fewer witnesses, and every witness is verified before use).
    let alphabet: Vec<char> = alphabet.into_iter().take(witness_alphabet_cap()).collect();

    // States are deduplicated per depth: with an exact length target, a
    // revisited regex state at a DIFFERENT depth can still reach the goal.
    let mut seen: HashSet<(usize, Vec<WeRegex>)> = HashSet::default();
    let mut frontier: VecDeque<(Vec<WeRegex>, String)> = VecDeque::new();
    seen.insert((0, start.clone()));
    frontier.push_back((start, String::new()));
    let mut popped = 0usize;

    let max_states = witness_max_states();
    while let Some((state, prefix)) = frontier.pop_front() {
        popped += 1;
        if popped > max_states {
            return found;
        }
        let depth = prefix.chars().count();
        if depth >= max_len {
            continue;
        }
        for &c in &alphabet {
            let next: Vec<WeRegex> = state.iter().map(|r| r.derive(c)).collect();
            if next.iter().any(|r| r.is_empty_lang()) {
                continue;
            }
            if next.iter().map(WeRegex::size).sum::<usize>() > MATCH_SIZE_CAP {
                continue;
            }
            let mut word = prefix.clone();
            word.push(c);
            let hit = accepts(&next, depth + 1);
            if hit {
                if !found.contains(&word) {
                    found.push(word.clone());
                }
                // `want = 1` returns here, exactly as the single-witness search
                // always did — same BFS, same first word.
                if found.len() >= want {
                    return found;
                }
            }
            // An accepted word can still be the prefix of a longer accepted
            // one, so the state is enqueued whether or not it was a hit.
            if seen.insert((depth + 1, next.clone())) {
                frontier.push_back((next, word));
            }
        }
    }
    found
}

/// State cap for the [`concat_membership_definitely_empty`] product search.
/// S1 lifts it: the cap only gates how much exploration may be spent on a
/// PROOF — tripping it always answers "not proven empty", so a bigger budget
/// can only produce more (still exact) UNSAT certificates.
const EMPTINESS_MAX_STATES: usize = 4096;
const EMPTINESS_MAX_STATES_S1: usize = 32_768;
/// Critical-character cap for the exhaustive class alphabet. S1 lifts it
/// (automatark regex sets routinely exceed 24 criticals); the class-alphabet
/// exactness argument is cap-independent — the cap only bounds work.
const EMPTINESS_MAX_CRITICAL: usize = 24;
const EMPTINESS_MAX_CRITICAL_S1: usize = 64;

fn emptiness_max_states() -> usize {
    if s1_enabled() {
        EMPTINESS_MAX_STATES_S1
    } else {
        EMPTINESS_MAX_STATES
    }
}

fn emptiness_max_critical() -> usize {
    if s1_enabled() {
        EMPTINESS_MAX_CRITICAL_S1
    } else {
        EMPTINESS_MAX_CRITICAL
    }
}

/// The next Unicode scalar value after `c`, if any.
fn next_char(c: char) -> Option<char> {
    let mut u = c as u32 + 1;
    loop {
        match char::from_u32(u) {
            Some(n) => return Some(n),
            None if u < char::MAX as u32 => u += 1, // skip the surrogate gap
            None => return None,
        }
    }
}

/// An EXHAUSTIVE class alphabet for the given regexes: one representative per
/// derivative-behavior equivalence class of `char`.
///
/// The atoms that distinguish characters are `Lit` first-characters and
/// `Range` bounds (every derivative's atoms are sub-atoms of the originals —
/// this includes `Loop`, whose derivative `d(r)·Loop(r, lo⊖1, hi−1)` only
/// shrinks counters and never introduces new atoms; `Comp` likewise commutes
/// with `derive` without touching atoms), so the critical set = all `Lit`
/// characters + all `Range` endpoints. Every character strictly between two
/// adjacent criticals behaves identically (no `Range` bound can straddle the
/// gap), as does every character outside the critical span — chars BELOW the
/// least critical and chars ABOVE the greatest critical form one shared
/// class (both are outside every `Range` and equal to no `Lit` char), so the
/// single above-max representative covers both regions and the complement
/// stays exact over the full alphabet. Returns `None` (caller must NOT
/// conclude emptiness) when the critical set is too large or a
/// representative cannot be built.
fn class_alphabet(regexes: &[&WeRegex]) -> Option<Vec<char>> {
    let mut critical: BTreeSet<char> = BTreeSet::new();
    for r in regexes {
        r.collect_chars(&mut critical);
    }
    if critical.len() > emptiness_max_critical() {
        return None;
    }
    let crit: Vec<char> = critical.iter().copied().collect();
    let mut reps: Vec<char> = crit.clone();
    // One representative inside each gap between adjacent criticals.
    for w in crit.windows(2) {
        if let Some(m) = next_char(w[0]) {
            if m < w[1] {
                reps.push(m);
            }
        }
    }
    // One representative OUTSIDE all criticals (behaves uniformly for every
    // atom). Missing it could hide an accepting path — so give up if none.
    match crit.last() {
        None => reps.push('a'),
        Some(&max) => {
            let c = next_char(max)?;
            reps.push(c)
        }
    }
    Some(reps)
}

/// DEFINITE emptiness of a concatenation-membership system:
///
/// ```text
///   { (u_1, …, u_n) | u_i ∈ ⋂ parts[i]  ∧  u_1·…·u_n ∈ ⋂ targets }  =  ∅ ?
/// ```
///
/// Returns `true` ONLY when the full product-derivative graph over an
/// exhaustive class alphabet (see [`class_alphabet`]) is explored without
/// reaching an accepting state and without tripping any resource cap —
/// a proof of emptiness, safe to use as a branch-closing conflict. Returns
/// `false` on acceptance, cap exhaustion, or an unrepresentable alphabet
/// (never claims emptiness it cannot prove).
#[must_use]
pub fn concat_membership_definitely_empty(parts: &[Vec<WeRegex>], targets: &[WeRegex]) -> bool {
    // A part or target that is DEFINITELY the empty language empties the set.
    if parts.iter().any(|p| p.iter().any(WeRegex::is_empty_lang))
        || targets.iter().any(WeRegex::is_empty_lang)
    {
        return true;
    }
    let all_refs: Vec<&WeRegex> = parts.iter().flatten().chain(targets.iter()).collect();
    let Some(alphabet) = class_alphabet(&all_refs) else {
        return false;
    };

    // Product state: which part we are inside, its residual constraints, and
    // the residual target constraints.
    type St = (usize, Vec<WeRegex>, Vec<WeRegex>);
    let start: St = (
        0,
        parts.first().cloned().unwrap_or_default(),
        targets.to_vec(),
    );
    let mut seen: HashSet<St> = HashSet::default();
    let mut frontier: VecDeque<St> = VecDeque::new();
    seen.insert(start.clone());
    frontier.push_back(start);
    let mut popped = 0usize;

    let max_states = emptiness_max_states();
    while let Some((idx, part, target)) = frontier.pop_front() {
        popped += 1;
        if popped > max_states {
            return false; // budget exhausted — NOT a proof of emptiness
        }
        if idx == parts.len() {
            if target.iter().all(WeRegex::nullable) {
                return false; // accepting: the set is non-empty
            }
            continue; // past the last part: no transitions
        }
        // ε-transition: end the current part (u_idx complete) when its
        // residual accepts the empty remainder.
        if part.iter().all(WeRegex::nullable) {
            let next: St = (
                idx + 1,
                parts.get(idx + 1).cloned().unwrap_or_default(),
                target.clone(),
            );
            if seen.insert(next.clone()) {
                frontier.push_back(next);
            }
        }
        // Character transitions extend the current part.
        for &c in &alphabet {
            let np: Vec<WeRegex> = part.iter().map(|r| r.derive(c)).collect();
            if np.iter().any(WeRegex::is_empty_lang) {
                continue;
            }
            let nt: Vec<WeRegex> = target.iter().map(|r| r.derive(c)).collect();
            if nt.iter().any(WeRegex::is_empty_lang) {
                continue;
            }
            let total: usize = np.iter().chain(nt.iter()).map(WeRegex::size).sum();
            if total > MATCH_SIZE_CAP {
                return false; // residual blowup — cannot certify emptiness
            }
            let next: St = (idx, np, nt);
            if seen.insert(next.clone()) {
                frontier.push_back(next);
            }
        }
    }
    true // graph exhausted, no accepting state: definitely empty
}

/// Best-effort WITNESS search for the concatenation-membership system of
/// [`concat_membership_definitely_empty`]: find strings `(u_1, …, u_n)` with
/// `u_i ∈ ⋂ parts[i]` and `u_1·…·u_n ∈ ⋂ targets` (strings S1).
///
/// Bounded product-derivative BFS over the representative class alphabet
/// (criticals + gap representatives + the outside representative, truncated
/// to the witness cap when oversized — truncation only finds fewer
/// witnesses). A returned split is exact by construction: every character
/// step keeps exact derivatives of both the current part's residuals and the
/// target residuals, a part boundary is taken only when the part's residual
/// is nullable, and acceptance requires every target residual nullable.
/// `None` means "not found", NEVER "no witness exists". Callers MUST still
/// re-validate downstream (the shared witness contract of [`find_witness`]);
/// this function never participates in Unsat conclusions.
#[must_use]
pub fn concat_membership_witness(
    parts: &[Vec<WeRegex>],
    targets: &[WeRegex],
    max_total_len: usize,
) -> Option<Vec<String>> {
    if parts.iter().any(|p| p.iter().any(WeRegex::is_empty_lang))
        || targets.iter().any(WeRegex::is_empty_lang)
    {
        return None;
    }
    if parts.is_empty() {
        return if targets.iter().all(WeRegex::nullable) {
            Some(Vec::new())
        } else {
            None
        };
    }

    // Representative alphabet (same construction as `find_witness`).
    let mut crit: BTreeSet<char> = BTreeSet::new();
    for r in parts.iter().flatten().chain(targets.iter()) {
        r.collect_chars(&mut crit);
    }
    let mut alphabet: BTreeSet<char> = crit.clone();
    let crit_v: Vec<char> = crit.iter().copied().collect();
    for w in crit_v.windows(2) {
        if let Some(m) = next_char(w[0]) {
            if m < w[1] {
                alphabet.insert(m);
            }
        }
    }
    if let Some(&mx) = crit_v.last() {
        if let Some(c) = next_char(mx) {
            alphabet.insert(c);
        }
    }
    alphabet.insert('a');
    alphabet.insert('b');
    let alphabet: Vec<char> = alphabet.into_iter().take(witness_alphabet_cap()).collect();

    // Product state: (part index, current part residuals, target residuals).
    // The witness-in-progress rides alongside (it is NOT part of the state
    // identity — the first arrival at a state is the shortest, which is all
    // a best-effort search needs).
    type St = (usize, Vec<WeRegex>, Vec<WeRegex>);
    let start: St = (
        0,
        parts.first().cloned().unwrap_or_default(),
        targets.to_vec(),
    );
    let mut seen: HashSet<St> = HashSet::default();
    let mut frontier: VecDeque<(St, Vec<String>)> = VecDeque::new();
    seen.insert(start.clone());
    frontier.push_back((start, vec![String::new()]));
    let max_states = witness_max_states();
    let mut popped = 0usize;

    while let Some(((idx, part, target), built)) = frontier.pop_front() {
        popped += 1;
        if popped > max_states {
            return None;
        }
        // ε-transition: close the current part when its residual accepts.
        if part.iter().all(WeRegex::nullable) {
            if idx + 1 == parts.len() {
                if target.iter().all(WeRegex::nullable) {
                    return Some(built); // accepting: full split found
                }
            } else {
                let next: St = (
                    idx + 1,
                    parts.get(idx + 1).cloned().unwrap_or_default(),
                    target.clone(),
                );
                if seen.insert(next.clone()) {
                    let mut nb = built.clone();
                    nb.push(String::new());
                    frontier.push_back((next, nb));
                }
            }
        }
        // Character transitions extend the current part.
        let total_len: usize = built.iter().map(|s| s.chars().count()).sum();
        if total_len >= max_total_len {
            continue;
        }
        for &c in &alphabet {
            let np: Vec<WeRegex> = part.iter().map(|r| r.derive(c)).collect();
            if np.iter().any(WeRegex::is_empty_lang) {
                continue;
            }
            let nt: Vec<WeRegex> = target.iter().map(|r| r.derive(c)).collect();
            if nt.iter().any(WeRegex::is_empty_lang) {
                continue;
            }
            let total: usize = np.iter().chain(nt.iter()).map(WeRegex::size).sum();
            if total > MATCH_SIZE_CAP {
                continue; // residual blowup: skip (best-effort)
            }
            let next: St = (idx, np, nt);
            if seen.insert(next.clone()) {
                let mut nb = built.clone();
                if let Some(last) = nb.last_mut() {
                    last.push(c);
                }
                frontier.push_back((next, nb));
            }
        }
    }
    None
}

// ── Length residues (Stage 3d) ──────────────────────────────────────────

/// Maximum modulus for regex-derived length residues (fits a `u64` bitmask).
pub const LEN_RESIDUE_MAX_MODULUS: usize = 64;

/// Node-visit budget for [`WeRegex::length_residues`] (guards nested-star
/// closure blowup; exceeding it yields `None` — no information).
const LEN_RESIDUE_BUDGET: usize = 2048;

fn gcd64(a: u64, b: u64) -> u64 {
    let (mut a, mut b) = (a, b);
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

/// Fold `g` into the running modulus `acc` by lcm, keeping
/// `acc ≤ LEN_RESIDUE_MAX_MODULUS` (factors that would exceed the cap are
/// skipped — sound: a smaller modulus derives weaker, still-entailed facts).
fn lcm_into_capped(acc: &mut u64, g: u64) {
    if g < 2 {
        return;
    }
    let d = gcd64(*acc, g);
    let l = (*acc / d).saturating_mul(g);
    if l <= LEN_RESIDUE_MAX_MODULUS as u64 {
        *acc = l;
    }
}

/// The residue bitmask with every bit `0..m` set.
fn full_mask(m: usize) -> u64 {
    if m >= 64 {
        u64::MAX
    } else {
        (1u64 << m) - 1
    }
}

/// Sumset of two residue bitmasks modulo `m`:
/// `{ (i + j) mod m : i ∈ a, j ∈ b }`.
fn sumset_mod(a: u64, b: u64, m: usize) -> u64 {
    let mut out = 0u64;
    for i in 0..m {
        if a & (1u64 << i) == 0 {
            continue;
        }
        for j in 0..m {
            if b & (1u64 << j) != 0 {
                out |= 1u64 << ((i + j) % m);
            }
        }
    }
    out
}

impl WeRegex {
    /// A PROVEN length congruence `(offset, gcd)`: every `w ∈ L(self)` has
    /// `|w| ≡ offset (mod gcd)` — `gcd == 0` means `|w| == offset` exactly.
    /// Returns `None` only for a language PROVEN empty (vacuously true).
    ///
    /// Soundness by structural induction:
    /// * `Eps`/`Lit`/`AnyChar`/`Range` have one exact length; `All` admits
    ///   every length (`(0, 1)` — the trivial congruence).
    /// * `Concat`: offsets add, moduli combine by gcd (a sum of terms
    ///   `≡ oᵢ (mod gᵢ)` is `≡ Σoᵢ (mod gcd(gᵢ))`).
    /// * `Union`: both arms must satisfy the result, so the modulus also
    ///   absorbs the offset difference (`o₁ ≡ o₂ (mod gcd(g₁,g₂,|o₁-o₂|))`).
    /// * `Inter`: any member satisfies EVERY part's congruence, so any one
    ///   part's pair is sound — keep the strongest-looking one.
    /// * `Star`: a sum of `k ≥ 0` terms each `≡ o (mod g)` is
    ///   `≡ 0 (mod gcd(o, g))`.
    fn len_pair(&self) -> Option<(u64, u64)> {
        match self {
            Self::None => None,
            Self::Eps => Some((0, 0)),
            Self::Lit(s) => Some((s.chars().count() as u64, 0)),
            Self::AnyChar | Self::Range(..) => Some((1, 0)),
            Self::All => Some((0, 1)),
            Self::Concat(xs) => {
                let mut o = 0u64;
                let mut g = 0u64;
                for x in xs {
                    let (xo, xg) = x.len_pair()?; // empty part ⇒ empty concat
                    o = o.saturating_add(xo);
                    g = gcd64(g, xg);
                }
                Some((o, g))
            }
            Self::Union(xs) => {
                let mut acc: Option<(u64, u64)> = None;
                for x in xs {
                    // A proven-empty arm contributes no strings: skip it.
                    let Some((xo, xg)) = x.len_pair() else {
                        continue;
                    };
                    acc = Some(match acc {
                        None => (xo, xg),
                        Some((o, g)) => (o.min(xo), gcd64(gcd64(g, xg), o.abs_diff(xo))),
                    });
                }
                acc
            }
            Self::Inter(xs) => {
                let mut best: Option<(u64, u64)> = None;
                for x in xs {
                    let p = x.len_pair()?; // empty part ⇒ empty intersection
                    best = Some(match best {
                        None => p,
                        Some(b) => {
                            // Prefer exact (g = 0), then the larger modulus.
                            if b.1 != 0 && (p.1 == 0 || p.1 > b.1) {
                                p
                            } else {
                                b
                            }
                        }
                    });
                }
                best
            }
            Self::Star(x) => match x.len_pair() {
                None => Some((0, 0)), // star of the empty language is {ε}
                Some((o, g)) => Some((0, gcd64(o, g))),
            },
            // ⋃_{k=lo}^{hi} L^k: a sum of k terms each ≡ o (mod g) is
            // ≡ k·o (mod g). For lo = hi that is exactly (lo·o, g); for
            // lo < hi fold the k-indexed family with the Union rule — the
            // offsets k·o differ by multiples of o, so every member is
            // ≡ lo·o (mod gcd(g, o)). Offsets that overflow u64 fall back to
            // the trivial (always-true) congruence (0, 1).
            Self::Loop(x, lo, hi) => match x.len_pair() {
                // Inner proven empty: only the k = 0 term (`{ε}` iff lo = 0,
                // but a Loop with an empty inner and lo ≥ 1 is folded to
                // `None` by the constructor — defensive).
                None => {
                    if *lo == 0 {
                        Some((0, 0))
                    } else {
                        None
                    }
                }
                Some((o, g)) => match o.checked_mul(u64::from(*lo)) {
                    None => Some((0, 1)),
                    Some(base) => {
                        if lo == hi {
                            Some((base, g))
                        } else {
                            Some((base, gcd64(g, o)))
                        }
                    }
                },
            },
            // A complement admits (nearly) every length; the only sound proven
            // congruence is the trivial one. NEVER `None`, which would falsely
            // assert emptiness (a complement is empty only for `¬Σ*`, already
            // folded to `None` by the `comp` constructor).
            Self::Comp(_) => Some((0, 1)),
        }
    }

    /// Collect candidate residue moduli: the congruence modulus each `Star`
    /// subterm PROVES for its own members (`gcd(o, g)` of the inner pair),
    /// folded into `acc` by capped lcm. Heuristic only — the final residue
    /// set is recomputed exactly by [`WeRegex::residues_mod`].
    fn collect_residue_moduli(&self, acc: &mut u64) {
        match self {
            Self::None | Self::Eps | Self::Lit(_) | Self::AnyChar | Self::All | Self::Range(..) => {
            }
            Self::Concat(xs) | Self::Union(xs) | Self::Inter(xs) => {
                for x in xs {
                    x.collect_residue_moduli(acc);
                }
            }
            Self::Star(x) => {
                if let Some((o, g)) = x.len_pair() {
                    lcm_into_capped(acc, gcd64(o, g));
                }
                x.collect_residue_moduli(acc);
            }
            // A bounded repeat with lo < hi varies its length in steps
            // related to the inner offset — same candidate modulus as Star
            // (heuristic only; the residue set is recomputed exactly).
            Self::Loop(x, lo, hi) => {
                if lo < hi {
                    if let Some((o, g)) = x.len_pair() {
                        lcm_into_capped(acc, gcd64(o, g));
                    }
                }
                x.collect_residue_moduli(acc);
            }
            // No usable modulus from a complement; recurse only to surface any
            // `Star` moduli nested inside (harmless — heuristic candidates).
            Self::Comp(x) => x.collect_residue_moduli(acc),
        }
    }

    /// An over-approximation of `{ |w| mod m : w ∈ L(self) }` as a bitmask
    /// (bit `r` set ⇔ residue `r` possible), or `None` when the node-visit
    /// budget is exhausted (callers MUST treat that as "no information").
    ///
    /// Exact for every constructor except `Inter` (residue-set intersection
    /// over-approximates the intersection language's residues — sound: never
    /// misses a member's residue). An empty result mask therefore PROVES the
    /// language empty.
    fn residues_mod(&self, m: usize, budget: &mut usize) -> Option<u64> {
        if *budget == 0 {
            return None;
        }
        *budget -= 1;
        Some(match self {
            Self::None => 0,
            Self::Eps => 1,
            Self::Lit(s) => 1u64 << (s.chars().count() % m),
            Self::AnyChar | Self::Range(..) => 1u64 << (1 % m),
            Self::All => full_mask(m),
            Self::Concat(xs) => {
                let mut acc = 1u64; // {0}
                for x in xs {
                    let rx = x.residues_mod(m, budget)?;
                    acc = sumset_mod(acc, rx, m);
                    if acc == 0 {
                        break;
                    }
                }
                acc
            }
            Self::Union(xs) => {
                let mut acc = 0u64;
                for x in xs {
                    acc |= x.residues_mod(m, budget)?;
                }
                acc
            }
            Self::Inter(xs) => {
                let mut acc = full_mask(m);
                for x in xs {
                    acc &= x.residues_mod(m, budget)?;
                }
                acc
            }
            Self::Star(x) => {
                let rx = x.residues_mod(m, budget)?;
                // Closure of {0} under adding rx (residues of L^k for all
                // k ≥ 0). Monotone over ≤ 64 bits, so it terminates; each
                // round is charged against the budget.
                let mut acc = 1u64;
                loop {
                    if *budget == 0 {
                        return None;
                    }
                    *budget -= 1;
                    let next = acc | sumset_mod(acc, rx, m);
                    if next == acc {
                        break;
                    }
                    acc = next;
                }
                acc
            }
            // ⋃_{k=lo}^{hi} L^k: residues of the k-th power are the k-fold
            // sumset; union the powers from lo through hi. Exact given exact
            // inner residues (like Concat/Union); each round is charged
            // against the budget so huge bounds degrade to `None` (no
            // information) instead of stalling.
            Self::Loop(x, lo, hi) => {
                let rx = x.residues_mod(m, budget)?;
                let mut power = 1u64; // residues of L^0 = {ε}: {0}
                for _ in 0..*lo {
                    if *budget == 0 {
                        return None;
                    }
                    *budget -= 1;
                    power = sumset_mod(power, rx, m);
                    if power == 0 {
                        break; // inner admits no length: powers stay empty
                    }
                }
                let mut acc = power;
                for _ in *lo..*hi {
                    if *budget == 0 {
                        return None;
                    }
                    *budget -= 1;
                    if power == 0 {
                        break;
                    }
                    power = sumset_mod(power, rx, m);
                    let next = acc | power;
                    if next == acc {
                        // Fixpoint: every later power is contained in acc.
                        // (P_{k+1} = P_k ⊕ rx; with P_k ⊆ acc = ⋃_{j≤k} P_j,
                        // P_{k+1} ⊆ ⋃_{j≤k} P_{j+1} ⊆ acc by induction.)
                        break;
                    }
                    acc = next;
                }
                acc
            }
            // Residues of a complement are not the complement of the residue
            // set (a residue can hold both members and non-members), so the
            // only SOUND over-approximation is "every residue possible".
            Self::Comp(_) => full_mask(m),
        })
    }

    /// Regex-derived length residues: `Some((m, mask))` with `2 ≤ m ≤ 64`
    /// PROVES every `w ∈ L(self)` has `|w| mod m` set in `mask`. An empty
    /// mask proves the language itself empty. Returns `None` when nothing
    /// beyond the trivial full residue set is derivable (conservative — a
    /// `None` contributes no pruning information).
    #[must_use]
    pub fn length_residues(&self) -> Option<(usize, u64)> {
        let mut m: u64 = 1;
        if let Some((_, g)) = self.len_pair() {
            lcm_into_capped(&mut m, g);
        }
        self.collect_residue_moduli(&mut m);
        if m < 2 {
            return None;
        }
        let m = m as usize;
        let mut budget = LEN_RESIDUE_BUDGET;
        let mask = self.residues_mod(m, &mut budget)?;
        if mask == full_mask(m) {
            return None; // no information
        }
        Some((m, mask))
    }
}

/// An EXACT regex for the length window `lo ≤ |w| ≤ hi` (`hi = None` means
/// unbounded), or `None` when the window is too large to materialize.
/// `hi < lo` yields the empty language.
#[must_use]
pub fn len_interval_regex(lo: usize, hi: Option<usize>) -> Option<WeRegex> {
    const LEN_REGEX_CAP: usize = 16;
    // S1: render the window as a bounded-repeat COUNTER node — exact for any
    // representable bounds, no materialized `Σ?` chain, no 16-length cap.
    if s1_enabled() {
        let lo32 = u32::try_from(lo).ok()?;
        return Some(match hi {
            Some(h) if h < lo => WeRegex::None,
            Some(h) => {
                let h32 = u32::try_from(h).ok()?;
                WeRegex::loop_bounded(WeRegex::AnyChar, lo32, h32)
            }
            None if lo == 0 => WeRegex::All,
            None => WeRegex::concat(vec![
                WeRegex::loop_bounded(WeRegex::AnyChar, lo32, lo32),
                WeRegex::All,
            ]),
        });
    }
    if lo > LEN_REGEX_CAP {
        return None;
    }
    match hi {
        Some(h) if h < lo => Some(WeRegex::None),
        Some(h) => {
            if h > LEN_REGEX_CAP {
                return None;
            }
            let mut parts: Vec<WeRegex> = Vec::with_capacity(h);
            for _ in 0..lo {
                parts.push(WeRegex::AnyChar);
            }
            for _ in lo..h {
                parts.push(WeRegex::opt(WeRegex::AnyChar));
            }
            Some(WeRegex::concat(parts))
        }
        None => {
            if lo == 0 {
                return Some(WeRegex::All);
            }
            let mut parts: Vec<WeRegex> = Vec::with_capacity(lo + 1);
            for _ in 0..lo {
                parts.push(WeRegex::AnyChar);
            }
            parts.push(WeRegex::All);
            Some(WeRegex::concat(parts))
        }
    }
}

#[cfg(test)]
#[path = "we_regex_tests.rs"]
mod tests;

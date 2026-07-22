// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Differential fuzz harness for the proof checker's INDEPENDENT ground
//! string/regex evaluator (`ay-proof/src/checker/string_ground.rs`, the
//! validator behind `TheoryLemmaKind::StringGroundEval` /
//! Alethe `:rule string_ground_eval`).
//!
//! WHY. That evaluator is the last line of defense for self-certified UNSAT on
//! ground QF_S / QF_SLIA refutations: if it says a clause is a tautology when
//! it is not, AY emits a WRONG, self-certified `unsat`. It shares no code with
//! the solver, so "the solver agrees with itself" proves nothing about it.
//!
//! WHAT THIS DOES. Random GROUND instances are evaluated by up to four
//! independently written implementations and every pair is compared:
//!
//! | # | implementation                              | crate                       |
//! |---|---------------------------------------------|-----------------------------|
//! | 1 | proof checker (memoized interval matcher)   | `ay-proof` (under test)     |
//! | 2 | `WeRegex::matches` (Brzozowski derivatives) | `ay-strings::we_regex`      |
//! | 3 | `ground_eval_in_re` (recursive descent)     | `ay-strings::regexp`        |
//! | 4 | SPEC MODEL (boolean reachability matrices)  | this file                   |
//!
//! Implementation 4 is written here directly from the SMT-LIB 2.6 Unicode
//! strings theory and uses a third algorithm shape (bottom-up boolean matrix
//! product/closure over all substring intervals) so it can ADJUDICATE a
//! disagreement between the other three rather than merely observe it.
//!
//! For the `str.*` operations the same pattern holds with
//! `ay-strings::eval::*` (the solver's shared ground-folding functions) as the
//! second implementation and a spec model here as the third.
//!
//! HOW THE CHECKER IS PROBED. `string_ground.rs` exposes exactly one public
//! predicate: `recognize_string_ground_eval(terms, clause) -> bool`, "this
//! clause has a ground literal that evaluates to TRUE". That is enough for a
//! three-valued read of any ground literal `L`:
//!
//! * `TRUE`    when the clause `[L, ⊥]` is recognized;
//! * `FALSE`   when the clause `[¬L, ⊥]` is recognized;
//! * `UNKNOWN` when neither is (the evaluator failed closed).
//!
//! `⊥` is the ground-false literal `(str.in_re "a" re.none)`, present only to
//! satisfy the validator's "clause must mention string/regex content" hygiene
//! gate for arithmetic-only literals. It can never make a probe read `TRUE`.
//!
//! RE-RUNNING. `cargo test -p ay-proof --test string_ground_diff_fuzz`, or at
//! scale via `scripts/fuzz/string_ground_diff_fuzz.sh`. Knobs:
//!
//! * `AY_SGF_SEED`  — PRNG seed (default 20260721). Fully deterministic.
//! * `AY_SGF_CASES` — cases per lane (default 1500; the script uses 10000).

#![allow(clippy::print_stdout)]

use ay_core::{Sort, Symbol, TermId, TermStore};
use ay_proof::recognize_string_ground_eval;
use ay_strings::we_regex::WeRegex;
use num_bigint::BigInt;

// ---------------------------------------------------------------------------
// Deterministic PRNG (SplitMix64) — no external dev-dependency, reproducible
// from the printed seed on any machine.
// ---------------------------------------------------------------------------

struct Rng(u64);

impl Rng {
    const fn new(seed: u64) -> Self {
        Self(seed)
    }

    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    fn below(&mut self, n: usize) -> usize {
        assert!(n > 0);
        (self.next_u64() % n as u64) as usize
    }

    fn pick<'a, T>(&mut self, xs: &'a [T]) -> &'a T {
        &xs[self.below(xs.len())]
    }

    fn chance(&mut self, num: usize, den: usize) -> bool {
        self.below(den) < num
    }
}

fn env_u64(key: &str, default: u64) -> u64 {
    std::env::var(key)
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(default)
}

/// Subject/literal alphabet. Deliberately mixes ASCII letters, digits, the NUL
/// code point, a Latin-1 code point and a high BMP code point so char-index vs.
/// byte-index confusions in any implementation show up as a disagreement.
const ALPHABET: &[char] = &['a', 'b', 'c', '0', '9', '\u{0}', '\u{e9}', '\u{2fff}'];

// ---------------------------------------------------------------------------
// Three-valued probe of the checker
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Tri {
    True,
    False,
    Unknown,
}

impl Tri {
    const fn from_bool(b: bool) -> Self {
        if b {
            Self::True
        } else {
            Self::False
        }
    }
}

/// The ground-FALSE string literal used to satisfy the validator's
/// string-content hygiene gate: `(str.in_re "a" re.none)`.
fn hygiene_false_literal(terms: &mut TermStore) -> TermId {
    let a = terms.mk_string("a".to_string());
    let none = terms.mk_app(Symbol::named("re.none"), [], Sort::RegLan);
    terms.mk_app(Symbol::named("str.in_re"), [a, none], Sort::Bool)
}

/// Read the checker's verdict on a single ground Bool literal.
fn probe(terms: &mut TermStore, lit: TermId, hygiene: TermId) -> Tri {
    let neg = terms.mk_not_raw(lit);
    if recognize_string_ground_eval(terms, &[lit, hygiene]) {
        Tri::True
    } else if recognize_string_ground_eval(terms, &[neg, hygiene]) {
        Tri::False
    } else {
        Tri::Unknown
    }
}

// ---------------------------------------------------------------------------
// Regex AST — one generator, four materializations
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
enum Re {
    None,
    All,
    AllChar,
    /// `(re.range lo hi)` — endpoints are arbitrary strings so the SMT-LIB
    /// "not a singleton ⇒ empty language" corner is exercised.
    Range(String, String),
    /// `(str.to_re t)`.
    Str(String),
    Concat(Vec<Re>),
    Union(Vec<Re>),
    Inter(Vec<Re>),
    Star(Box<Re>),
    Plus(Box<Re>),
    Opt(Box<Re>),
    Comp(Box<Re>),
    Diff(Vec<Re>),
    /// `((_ re.loop lo hi) r)`.
    Loop(Box<Re>, u32, u32),
    /// `((_ re.^ n) r)`.
    Pow(Box<Re>, u32),
}

fn gen_string(rng: &mut Rng, max_len: usize) -> String {
    let n = rng.below(max_len + 1);
    (0..n).map(|_| *rng.pick(ALPHABET)).collect()
}

fn gen_re(rng: &mut Rng, depth: usize) -> Re {
    // Leaves only at depth 0; otherwise a leaf with probability 1/4.
    if depth == 0 || rng.chance(1, 4) {
        return match rng.below(10) {
            0 => Re::None,
            1 => Re::All,
            2 | 3 => Re::AllChar,
            4 | 5 => {
                // Mostly well-formed singleton ranges, sometimes the SMT-LIB
                // empty-language corners (non-singleton endpoint, lo > hi).
                let (lo, hi) = if rng.chance(1, 6) {
                    (gen_string(rng, 2), gen_string(rng, 2))
                } else {
                    let a = *rng.pick(ALPHABET);
                    let b = *rng.pick(ALPHABET);
                    (a.to_string(), b.to_string())
                };
                Re::Range(lo, hi)
            }
            _ => Re::Str(gen_string(rng, 2)),
        };
    }
    let arity = |rng: &mut Rng| 1 + rng.below(3);
    match rng.below(13) {
        0 | 1 => Re::Concat((0..arity(rng)).map(|_| gen_re(rng, depth - 1)).collect()),
        2 | 3 => Re::Union((0..arity(rng)).map(|_| gen_re(rng, depth - 1)).collect()),
        4 => Re::Inter((0..=arity(rng)).map(|_| gen_re(rng, depth - 1)).collect()),
        5 | 6 => Re::Star(Box::new(gen_re(rng, depth - 1))),
        7 => Re::Plus(Box::new(gen_re(rng, depth - 1))),
        8 => Re::Opt(Box::new(gen_re(rng, depth - 1))),
        9 => Re::Comp(Box::new(gen_re(rng, depth - 1))),
        10 => Re::Diff(
            (0..2 + rng.below(2))
                .map(|_| gen_re(rng, depth - 1))
                .collect(),
        ),
        11 => {
            let lo = gen_bound(rng);
            // `lo > hi` (the SMT-LIB empty language) reached deliberately.
            let hi = gen_bound(rng);
            Re::Loop(Box::new(gen_re(rng, depth - 1)), lo, hi)
        }
        _ => Re::Pow(Box::new(gen_re(rng, depth - 1)), gen_bound(rng)),
    }
}

/// Repetition bounds: mostly small, but regularly LARGER than any subject.
/// The checker caps `hi` at the subject length before unrolling, which is the
/// exact place a bounded-repeat evaluator goes wrong on nullable bodies.
fn gen_bound(rng: &mut Rng) -> u32 {
    if rng.chance(1, 5) {
        (5 + rng.below(36)) as u32
    } else {
        rng.below(5) as u32
    }
}

/// Node count, used to keep a case affordable for the exponential oracles.
fn re_size(re: &Re) -> usize {
    match re {
        Re::None | Re::All | Re::AllChar | Re::Range(..) | Re::Str(_) => 1,
        Re::Concat(xs) | Re::Union(xs) | Re::Inter(xs) | Re::Diff(xs) => {
            1 + xs.iter().map(re_size).sum::<usize>()
        }
        Re::Star(x) | Re::Plus(x) | Re::Opt(x) | Re::Comp(x) | Re::Loop(x, ..) | Re::Pow(x, _) => {
            1 + re_size(x)
        }
    }
}

/// Materialization 1: a `TermStore` term (read by the checker and by
/// `ay_strings::ground_eval_in_re`).
fn re_term(terms: &mut TermStore, re: &Re) -> TermId {
    let nary = |terms: &mut TermStore, name: &str, xs: &[Re]| {
        let args: Vec<TermId> = xs.iter().map(|x| re_term(terms, x)).collect();
        terms.mk_app(Symbol::named(name), args, Sort::RegLan)
    };
    match re {
        Re::None => terms.mk_app(Symbol::named("re.none"), [], Sort::RegLan),
        Re::All => terms.mk_app(Symbol::named("re.all"), [], Sort::RegLan),
        Re::AllChar => terms.mk_app(Symbol::named("re.allchar"), [], Sort::RegLan),
        Re::Range(lo, hi) => {
            let l = terms.mk_string(lo.clone());
            let h = terms.mk_string(hi.clone());
            terms.mk_app(Symbol::named("re.range"), [l, h], Sort::RegLan)
        }
        Re::Str(s) => {
            let c = terms.mk_string(s.clone());
            terms.mk_app(Symbol::named("str.to_re"), [c], Sort::RegLan)
        }
        Re::Concat(xs) => nary(terms, "re.++", xs),
        Re::Union(xs) => nary(terms, "re.union", xs),
        Re::Inter(xs) => nary(terms, "re.inter", xs),
        Re::Diff(xs) => nary(terms, "re.diff", xs),
        Re::Star(x) => {
            let a = re_term(terms, x);
            terms.mk_app(Symbol::named("re.*"), [a], Sort::RegLan)
        }
        Re::Plus(x) => {
            let a = re_term(terms, x);
            terms.mk_app(Symbol::named("re.+"), [a], Sort::RegLan)
        }
        Re::Opt(x) => {
            let a = re_term(terms, x);
            terms.mk_app(Symbol::named("re.opt"), [a], Sort::RegLan)
        }
        Re::Comp(x) => {
            let a = re_term(terms, x);
            terms.mk_app(Symbol::named("re.comp"), [a], Sort::RegLan)
        }
        Re::Loop(x, lo, hi) => {
            let a = re_term(terms, x);
            terms.mk_app(
                Symbol::indexed("re.loop", vec![*lo, *hi]),
                [a],
                Sort::RegLan,
            )
        }
        Re::Pow(x, n) => {
            let a = re_term(terms, x);
            terms.mk_app(Symbol::indexed("re.^", vec![*n]), [a], Sort::RegLan)
        }
    }
}

/// Materialization 2: a [`WeRegex`] for the derivative matcher.
///
/// `re.diff` has no `WeRegex` node; it is encoded by its DEFINITION,
/// `L(r₀ \ r₁ \ … ) = L(r₀) ∩ ¬L(r₁) ∩ …`, which is exact.
fn re_we(re: &Re) -> WeRegex {
    match re {
        Re::None => WeRegex::None,
        Re::All => WeRegex::All,
        Re::AllChar => WeRegex::AnyChar,
        Re::Range(lo, hi) => WeRegex::range(lo, hi),
        Re::Str(s) => WeRegex::lit(s),
        Re::Concat(xs) => WeRegex::concat(xs.iter().map(re_we).collect()),
        Re::Union(xs) => WeRegex::union(xs.iter().map(re_we).collect()),
        Re::Inter(xs) => WeRegex::inter(xs.iter().map(re_we).collect()),
        Re::Diff(xs) => {
            let mut parts = vec![re_we(&xs[0])];
            for x in &xs[1..] {
                parts.push(WeRegex::comp(re_we(x)));
            }
            WeRegex::inter(parts)
        }
        Re::Star(x) => WeRegex::star(re_we(x)),
        Re::Plus(x) => WeRegex::plus(re_we(x)),
        Re::Opt(x) => WeRegex::opt(re_we(x)),
        Re::Comp(x) => WeRegex::comp(re_we(x)),
        Re::Loop(x, lo, hi) => WeRegex::loop_bounded(re_we(x), *lo, *hi),
        Re::Pow(x, n) => WeRegex::loop_bounded(re_we(x), *n, *n),
    }
}

// ---------------------------------------------------------------------------
// Materialization 3: the SPEC MODEL — boolean interval matrices
// ---------------------------------------------------------------------------

/// `M[i][j]` = "the substring `s[i..j]` is in the language", for
/// `0 ≤ i ≤ j ≤ |s|`. Every SMT-LIB regex constructor becomes one closed
/// boolean-matrix operation, which is a different algorithm from both the
/// checker's top-down memoized recursion and the derivative matcher.
#[derive(Clone)]
struct Mat {
    n: usize,
    bits: Vec<bool>,
}

impl Mat {
    fn empty(n: usize) -> Self {
        Self {
            n,
            bits: vec![false; (n + 1) * (n + 1)],
        }
    }

    fn identity(n: usize) -> Self {
        let mut m = Self::empty(n);
        for i in 0..=n {
            m.set(i, i, true);
        }
        m
    }

    /// Σ* — every interval, since `s[i..j]` is always a string.
    fn universal(n: usize) -> Self {
        let mut m = Self::empty(n);
        for i in 0..=n {
            for j in i..=n {
                m.set(i, j, true);
            }
        }
        m
    }

    const fn idx(&self, i: usize, j: usize) -> usize {
        i * (self.n + 1) + j
    }

    fn get(&self, i: usize, j: usize) -> bool {
        self.bits[self.idx(i, j)]
    }

    fn set(&mut self, i: usize, j: usize, v: bool) {
        let k = self.idx(i, j);
        self.bits[k] = v;
    }

    /// Boolean matrix product: concatenation of languages.
    fn mul(&self, other: &Self) -> Self {
        let n = self.n;
        let mut out = Self::empty(n);
        for i in 0..=n {
            for k in i..=n {
                if !self.get(i, k) {
                    continue;
                }
                for j in k..=n {
                    if other.get(k, j) {
                        out.set(i, j, true);
                    }
                }
            }
        }
        out
    }

    fn or(&self, other: &Self) -> Self {
        let mut out = self.clone();
        for (o, &b) in out.bits.iter_mut().zip(other.bits.iter()) {
            *o |= b;
        }
        out
    }

    fn and(&self, other: &Self) -> Self {
        let mut out = self.clone();
        for (o, &b) in out.bits.iter_mut().zip(other.bits.iter()) {
            *o &= b;
        }
        out
    }

    /// Complement w.r.t. the FULL alphabet: every interval not in `self`.
    fn not(&self) -> Self {
        let mut out = Self::empty(self.n);
        for i in 0..=self.n {
            for j in i..=self.n {
                out.set(i, j, !self.get(i, j));
            }
        }
        out
    }

    /// Reflexive-transitive closure: Kleene star.
    fn star(&self) -> Self {
        let mut acc = Self::identity(self.n);
        loop {
            let next = acc.or(&acc.mul(self));
            if next.bits == acc.bits {
                return acc;
            }
            acc = next;
        }
    }

    fn pow(&self, k: u32) -> Self {
        let mut acc = Self::identity(self.n);
        for _ in 0..k {
            acc = acc.mul(self);
        }
        acc
    }
}

fn spec_matrix(re: &Re, s: &[char]) -> Mat {
    let n = s.len();
    match re {
        Re::None => Mat::empty(n),
        Re::All => Mat::universal(n),
        Re::AllChar => {
            let mut m = Mat::empty(n);
            for i in 0..n {
                m.set(i, i + 1, true);
            }
            m
        }
        // SMT-LIB 2.6, Unicode strings theory: `(re.range l u)` denotes
        // `{ c | l ≤ c ≤ u }` when `l` and `u` are singleton strings, and the
        // EMPTY language otherwise (including `l > u`).
        Re::Range(lo, hi) => {
            let mut m = Mat::empty(n);
            let l: Vec<char> = lo.chars().collect();
            let u: Vec<char> = hi.chars().collect();
            if l.len() == 1 && u.len() == 1 && l[0] <= u[0] {
                for i in 0..n {
                    if l[0] <= s[i] && s[i] <= u[0] {
                        m.set(i, i + 1, true);
                    }
                }
            }
            m
        }
        Re::Str(t) => {
            let t: Vec<char> = t.chars().collect();
            let mut m = Mat::empty(n);
            for i in 0..=n {
                let j = i + t.len();
                if j <= n && s[i..j] == t[..] {
                    m.set(i, j, true);
                }
            }
            m
        }
        Re::Concat(xs) => {
            let mut acc = Mat::identity(n);
            for x in xs {
                acc = acc.mul(&spec_matrix(x, s));
            }
            acc
        }
        Re::Union(xs) => {
            let mut acc = Mat::empty(n);
            for x in xs {
                acc = acc.or(&spec_matrix(x, s));
            }
            acc
        }
        Re::Inter(xs) => {
            let mut acc = Mat::universal(n);
            for x in xs {
                acc = acc.and(&spec_matrix(x, s));
            }
            acc
        }
        // `:left-assoc` difference: (r0 \ r1) \ r2 = r0 ∩ ¬r1 ∩ ¬r2.
        Re::Diff(xs) => {
            let mut acc = spec_matrix(&xs[0], s);
            for x in &xs[1..] {
                acc = acc.and(&spec_matrix(x, s).not());
            }
            acc
        }
        Re::Star(x) => spec_matrix(x, s).star(),
        Re::Plus(x) => {
            let m = spec_matrix(x, s);
            m.mul(&m.star())
        }
        Re::Opt(x) => spec_matrix(x, s).or(&Mat::identity(n)),
        Re::Comp(x) => spec_matrix(x, s).not(),
        // `⋃_{k=lo}^{hi} L^k`, empty when `lo > hi`.
        Re::Loop(x, lo, hi) => {
            let mut acc = Mat::empty(n);
            if lo <= hi {
                let m = spec_matrix(x, s);
                let mut p = Mat::identity(n);
                for k in 0..=*hi {
                    if k >= *lo {
                        acc = acc.or(&p);
                    }
                    if k == *hi {
                        break;
                    }
                    p = p.mul(&m);
                }
            }
            acc
        }
        Re::Pow(x, k) => spec_matrix(x, s).pow(*k),
    }
}

fn spec_in_re(re: &Re, s: &[char]) -> bool {
    let m = spec_matrix(re, s);
    m.get(0, s.len())
}

// ---------------------------------------------------------------------------
// Disagreement bookkeeping
// ---------------------------------------------------------------------------

#[derive(Default)]
struct Stats {
    cases: usize,
    checker_known: usize,
    we_known: usize,
    solver_known: usize,
    /// Cases where the SPEC says the literal is TRUE. A lane in which almost
    /// every instance is false would be near-worthless for wrong-UNSAT hunting
    /// (the dangerous direction is the checker answering TRUE), so this ratio
    /// is reported and floor-checked.
    positive: usize,
    /// SMT-LIB under-specified instances (`div`/`mod` by zero) — the checker
    /// must fail closed on these, and they are counted, not compared.
    underspecified: usize,
    disagreements: Vec<String>,
}

impl Stats {
    fn record(&mut self, msg: String) {
        if self.disagreements.len() < 20 {
            self.disagreements.push(msg);
        }
    }

    fn finish(&self, lane: &str, seed: u64, oracles: &[(&str, usize)]) {
        let oracle_report: Vec<String> = oracles
            .iter()
            .map(|(n, v)| format!("{n}-decided={v}"))
            .collect();
        println!(
            "[{lane}] seed={seed} cases={} checker-decided={} spec-true-atoms={} \
             under-specified={} {} disagreements={}",
            self.cases,
            self.checker_known,
            self.positive,
            self.underspecified,
            oracle_report.join(" "),
            self.disagreements.len()
        );
        assert!(
            self.disagreements.is_empty(),
            "[{lane}] {} DISAGREEMENT(S) (seed={seed}); first {}:\n{}",
            self.disagreements.len(),
            self.disagreements.len().min(20),
            self.disagreements.join("\n")
        );
    }
}

/// Names of the regex operators occurring in `re`, for coverage accounting.
fn re_ops(re: &Re, out: &mut std::collections::BTreeMap<&'static str, usize>) {
    let (name, kids): (&str, Vec<&Re>) = match re {
        Re::None => ("re.none", vec![]),
        Re::All => ("re.all", vec![]),
        Re::AllChar => ("re.allchar", vec![]),
        Re::Range(..) => ("re.range", vec![]),
        Re::Str(_) => ("str.to_re", vec![]),
        Re::Concat(xs) => ("re.++", xs.iter().collect()),
        Re::Union(xs) => ("re.union", xs.iter().collect()),
        Re::Inter(xs) => ("re.inter", xs.iter().collect()),
        Re::Diff(xs) => ("re.diff", xs.iter().collect()),
        Re::Star(x) => ("re.*", vec![x]),
        Re::Plus(x) => ("re.+", vec![x]),
        Re::Opt(x) => ("re.opt", vec![x]),
        Re::Comp(x) => ("re.comp", vec![x]),
        Re::Loop(x, ..) => ("re.loop", vec![x]),
        Re::Pow(x, _) => ("re.^", vec![x]),
    };
    *out.entry(name).or_default() += 1;
    for k in kids {
        re_ops(k, out);
    }
}

// ---------------------------------------------------------------------------
// Lane 1: regex membership
// ---------------------------------------------------------------------------

#[test]
fn regex_membership_differential_fuzz() {
    let seed = env_u64("AY_SGF_SEED", 20_260_721);
    let cases = env_u64("AY_SGF_CASES", 1500) as usize;
    let mut rng = Rng::new(seed);
    let mut st = Stats::default();
    let mut per_op: std::collections::BTreeMap<&'static str, usize> =
        std::collections::BTreeMap::new();

    let mut generated = 0usize;
    while generated < cases {
        let depth = 1 + rng.below(4);
        let re = gen_re(&mut rng, depth);
        if re_size(&re) > 12 {
            continue; // keep the exponential oracles affordable
        }
        // Bias hard toward subjects the regex can plausibly accept: a lane in
        // which every membership is FALSE would never exercise the dangerous
        // direction (the checker wrongly answering TRUE). `find_witness` is a
        // best-effort derivative search, so this only shifts the distribution.
        let subject: String = if rng.chance(1, 2) {
            ay_strings::we_regex::find_witness(&[re_we(&re)], None)
                .unwrap_or_else(|| gen_string(&mut rng, 5))
        } else {
            gen_string(&mut rng, 5)
        };
        let chars: Vec<char> = subject.chars().collect();
        if chars.len() > 8 {
            continue; // keep the exponential oracles affordable
        }
        generated += 1;
        st.cases += 1;
        re_ops(&re, &mut per_op);

        // 4: spec model (ground truth for adjudication).
        let spec = spec_in_re(&re, &chars);
        if spec {
            st.positive += 1;
        }

        // 1: the checker under test.
        let mut terms = TermStore::new();
        let hygiene = hygiene_false_literal(&mut terms);
        let r_term = re_term(&mut terms, &re);
        // Half the subjects are reached through a `str.++` of constants, so the
        // checker's recursive value evaluation feeds the regex matcher rather
        // than a bare literal.
        let s_term = if chars.len() >= 2 && rng.chance(1, 2) {
            let cut = 1 + rng.below(chars.len() - 1);
            let a = terms.mk_string(chars[..cut].iter().collect::<String>());
            let b = terms.mk_string(chars[cut..].iter().collect::<String>());
            terms.mk_app(Symbol::named("str.++"), [a, b], Sort::String)
        } else {
            terms.mk_string(subject.clone())
        };
        let lit = terms.mk_app(Symbol::named("str.in_re"), [s_term, r_term], Sort::Bool);
        let checker = probe(&mut terms, lit, hygiene);

        // 2: Brzozowski derivatives.
        let we = re_we(&re).matches(&subject);

        // 3: solver-side recursive descent.
        let solver = ay_strings::ground_eval_in_re(&terms, &subject, r_term);

        if checker != Tri::Unknown {
            st.checker_known += 1;
        }
        if we.is_some() {
            st.we_known += 1;
        }
        if solver.is_some() {
            st.solver_known += 1;
        }

        let mut bad = Vec::new();
        if checker != Tri::Unknown && checker != Tri::from_bool(spec) {
            bad.push(format!("CHECKER={checker:?} vs SPEC={spec}"));
        }
        if let Some(w) = we {
            if w != spec {
                bad.push(format!("WEREGEX={w} vs SPEC={spec}"));
            }
        }
        if let Some(v) = solver {
            if v != spec {
                bad.push(format!("SOLVER_REGEXP={v} vs SPEC={spec}"));
            }
        }
        if !bad.is_empty() {
            st.record(format!(
                "  case #{generated}: str.in_re {subject:?} {re:?}\n    {}",
                bad.join("\n    ")
            ));
        }
    }
    println!("[regex] operator occurrences across all generated regexes:");
    for (name, count) in &per_op {
        println!("[regex]   {name:<12} {count}");
    }
    assert_eq!(
        per_op.len(),
        15,
        "every regex operator must be exercised; saw {:?}",
        per_op.keys().collect::<Vec<_>>()
    );
    st.finish(
        "regex",
        seed,
        &[
            ("derivative-oracle", st.we_known),
            ("solver-oracle", st.solver_known),
        ],
    );
    assert!(
        st.positive * 5 >= st.cases,
        "too few TRUE memberships ({} of {}) — the lane would not exercise the \
         wrong-UNSAT direction",
        st.positive,
        st.cases
    );
}

// ---------------------------------------------------------------------------
// Lane 2: string / integer operations
// ---------------------------------------------------------------------------

/// SMT-LIB 2.6 `str.<`: the lexicographic order induced by the code-point
/// order, with a proper prefix strictly below its extensions.
fn spec_lt(a: &[char], b: &[char]) -> bool {
    for (x, y) in a.iter().zip(b.iter()) {
        if x != y {
            return x < y;
        }
    }
    a.len() < b.len()
}

fn spec_find(hay: &[char], needle: &[char], from: usize) -> Option<usize> {
    if from > hay.len() {
        return None;
    }
    if needle.is_empty() {
        return Some(from);
    }
    (from..=hay.len().checked_sub(needle.len())?).find(|&i| hay[i..i + needle.len()] == needle[..])
}

/// The value an operation is expected to produce, as a term-comparable literal.
#[derive(Debug, Clone, PartialEq, Eq)]
enum SpecVal {
    S(Vec<char>),
    I(BigInt),
    B(bool),
    /// SMT-LIB leaves the value UNDER-SPECIFIED (`div`/`mod` by zero): the
    /// checker must fail closed, and any concrete answer would be a bug.
    Undefined,
}

fn to_i64_opt(n: &BigInt) -> Option<i64> {
    i64::try_from(n).ok()
}

/// The spec model for the `str.*` / arithmetic operations, written from the
/// SMT-LIB 2.6 Unicode strings theory and the Ints theory.
fn spec_op(op: &Op) -> SpecVal {
    match op {
        Op::Concat(parts) => SpecVal::S(parts.iter().flat_map(|p| p.chars()).collect()),
        Op::Len(s) => SpecVal::I(BigInt::from(s.chars().count())),
        // `(str.at s n)` = the singleton at n when 0 ≤ n < |s|, else "".
        Op::At(s, i) => {
            let c: Vec<char> = s.chars().collect();
            let idx = to_i64_opt(i).filter(|&v| v >= 0).map(|v| v as u128);
            SpecVal::S(match idx {
                Some(v) if v < c.len() as u128 => vec![c[v as usize]],
                _ => Vec::new(),
            })
        }
        // `(str.substr s m n)` = the longest prefix of length ≤ n of the suffix
        // of s starting at m, when 0 ≤ m < |s| and 0 < n; else "".
        Op::Substr(s, i, n) => {
            let c: Vec<char> = s.chars().collect();
            let start = to_i64_opt(i).filter(|&v| v >= 0).map(|v| v as u128);
            let (Some(start), true) = (start, *n > BigInt::from(0)) else {
                return SpecVal::S(Vec::new());
            };
            if start >= c.len() as u128 {
                return SpecVal::S(Vec::new());
            }
            let start = start as usize;
            // `n` may be astronomically large; it only ever CLAMPS to |s|.
            let want =
                to_i64_opt(n).map_or(c.len() - start, |v| usize::min(v as usize, c.len() - start));
            SpecVal::S(c[start..start + want].to_vec())
        }
        Op::Contains(s, t) => SpecVal::B(
            spec_find(
                &s.chars().collect::<Vec<_>>(),
                &t.chars().collect::<Vec<_>>(),
                0,
            )
            .is_some(),
        ),
        Op::PrefixOf(t, s) => {
            let t: Vec<char> = t.chars().collect();
            let s: Vec<char> = s.chars().collect();
            SpecVal::B(s.len() >= t.len() && s[..t.len()] == t[..])
        }
        Op::SuffixOf(t, s) => {
            let t: Vec<char> = t.chars().collect();
            let s: Vec<char> = s.chars().collect();
            SpecVal::B(s.len() >= t.len() && s[s.len() - t.len()..] == t[..])
        }
        // `(str.indexof s t i)` = the least n ≥ i with t occurring at n, when
        // 0 ≤ i ≤ |s| and such an n exists; −1 otherwise.
        Op::IndexOf(s, t, i) => {
            let s: Vec<char> = s.chars().collect();
            let t: Vec<char> = t.chars().collect();
            let minus_one = SpecVal::I(BigInt::from(-1));
            let Some(start) = to_i64_opt(i).filter(|&v| v >= 0).map(|v| v as u128) else {
                return minus_one;
            };
            if start > s.len() as u128 {
                return minus_one;
            }
            spec_find(&s, &t, start as usize).map_or(minus_one, |p| SpecVal::I(BigInt::from(p)))
        }
        // `(str.replace s t u)`: first occurrence; `t = ""` prepends u.
        Op::Replace(s, t, u) => {
            let s: Vec<char> = s.chars().collect();
            let t: Vec<char> = t.chars().collect();
            let u: Vec<char> = u.chars().collect();
            if t.is_empty() {
                let mut out = u;
                out.extend_from_slice(&s);
                return SpecVal::S(out);
            }
            SpecVal::S(spec_find(&s, &t, 0).map_or(s.clone(), |p| {
                let mut out = s[..p].to_vec();
                out.extend_from_slice(&u);
                out.extend_from_slice(&s[p + t.len()..]);
                out
            }))
        }
        // `(str.replace_all s t u)`: leftmost non-overlapping; `t = ""` is s.
        Op::ReplaceAll(s, t, u) => {
            let s: Vec<char> = s.chars().collect();
            let t: Vec<char> = t.chars().collect();
            let u: Vec<char> = u.chars().collect();
            if t.is_empty() {
                return SpecVal::S(s);
            }
            let mut out = Vec::new();
            let mut pos = 0usize;
            while let Some(hit) = spec_find(&s, &t, pos) {
                out.extend_from_slice(&s[pos..hit]);
                out.extend_from_slice(&u);
                pos = hit + t.len();
            }
            out.extend_from_slice(&s[pos..]);
            SpecVal::S(out)
        }
        Op::ToCode(s) => {
            let c: Vec<char> = s.chars().collect();
            SpecVal::I(if c.len() == 1 {
                BigInt::from(c[0] as u32)
            } else {
                BigInt::from(-1)
            })
        }
        // `(str.from_code n)` = the singleton with code point n when
        // 0 ≤ n ≤ 0x2FFFF, else "".
        Op::FromCode(n) => {
            let v = to_i64_opt(n);
            match v {
                Some(v) if (0..=196_607).contains(&v) => match char::from_u32(v as u32) {
                    Some(c) => SpecVal::S(vec![c]),
                    // Surrogate code points are inside the SMT-LIB alphabet but
                    // are NOT representable in AY's `String`; no implementation
                    // can answer, so this case is skipped by the generator.
                    None => SpecVal::Undefined,
                },
                _ => SpecVal::S(Vec::new()),
            }
        }
        Op::ToInt(s) => {
            let c: Vec<char> = s.chars().collect();
            SpecVal::I(if c.is_empty() || !c.iter().all(char::is_ascii_digit) {
                BigInt::from(-1)
            } else {
                c.iter().collect::<String>().parse::<BigInt>().unwrap()
            })
        }
        Op::FromInt(n) => SpecVal::S(if *n < BigInt::from(0) {
            Vec::new()
        } else {
            n.to_string().chars().collect()
        }),
        Op::IsDigit(s) => {
            let c: Vec<char> = s.chars().collect();
            SpecVal::B(c.len() == 1 && c[0].is_ascii_digit())
        }
        Op::Lt(a, b) => SpecVal::B(spec_lt(
            &a.chars().collect::<Vec<_>>(),
            &b.chars().collect::<Vec<_>>(),
        )),
        Op::Le(a, b) => {
            let x: Vec<char> = a.chars().collect();
            let y: Vec<char> = b.chars().collect();
            SpecVal::B(x == y || spec_lt(&x, &y))
        }
        // SMT-LIB Ints: `div`/`mod` are EUCLIDEAN — `a = b·q + r`, `0 ≤ r < |b|`
        // — and totally UNDER-SPECIFIED when `b = 0`.
        Op::Div(a, b) | Op::Mod(a, b) => {
            if *b == BigInt::from(0) {
                return SpecVal::Undefined;
            }
            let mut q = a / b;
            let mut r = a - &q * b;
            if r < BigInt::from(0) {
                if *b > BigInt::from(0) {
                    q -= 1;
                } else {
                    q += 1;
                }
                r = a - &q * b;
            }
            SpecVal::I(if matches!(op, Op::Div(..)) { q } else { r })
        }
    }
}

#[derive(Debug, Clone)]
enum Op {
    Concat(Vec<String>),
    Len(String),
    At(String, BigInt),
    Substr(String, BigInt, BigInt),
    Contains(String, String),
    PrefixOf(String, String),
    SuffixOf(String, String),
    IndexOf(String, String, BigInt),
    Replace(String, String, String),
    ReplaceAll(String, String, String),
    ToCode(String),
    FromCode(BigInt),
    ToInt(String),
    FromInt(BigInt),
    IsDigit(String),
    Lt(String, String),
    Le(String, String),
    Div(BigInt, BigInt),
    Mod(BigInt, BigInt),
}

impl Op {
    const fn name(&self) -> &'static str {
        match self {
            Self::Concat(_) => "str.++",
            Self::Len(_) => "str.len",
            Self::At(..) => "str.at",
            Self::Substr(..) => "str.substr",
            Self::Contains(..) => "str.contains",
            Self::PrefixOf(..) => "str.prefixof",
            Self::SuffixOf(..) => "str.suffixof",
            Self::IndexOf(..) => "str.indexof",
            Self::Replace(..) => "str.replace",
            Self::ReplaceAll(..) => "str.replace_all",
            Self::ToCode(_) => "str.to_code",
            Self::FromCode(_) => "str.from_code",
            Self::ToInt(_) => "str.to_int",
            Self::FromInt(_) => "str.from_int",
            Self::IsDigit(_) => "str.is_digit",
            Self::Lt(..) => "str.<",
            Self::Le(..) => "str.<=",
            Self::Div(..) => "div",
            Self::Mod(..) => "mod",
        }
    }
}

/// Independently-written solver-side value, where `ay-strings` exposes one.
/// `None` means the solver has no shared implementation for this operation.
fn solver_op(op: &Op) -> Option<SpecVal> {
    use ay_strings::eval as se;
    Some(match op {
        Op::At(s, i) => SpecVal::S(se::eval_str_at(s, i)?.chars().collect()),
        Op::Substr(s, i, n) => SpecVal::S(se::eval_str_substr(s, i, n)?.chars().collect()),
        Op::IndexOf(s, t, i) => SpecVal::I(se::eval_str_indexof(s, t, i)?),
        Op::Replace(s, t, u) => SpecVal::S(se::eval_str_replace(s, t, u).chars().collect()),
        Op::ReplaceAll(s, t, u) => SpecVal::S(se::eval_str_replace_all(s, t, u).chars().collect()),
        Op::ToCode(s) => SpecVal::I(se::eval_str_to_code(s)),
        Op::FromCode(n) => SpecVal::S(se::eval_str_from_code(n).chars().collect()),
        Op::ToInt(s) => SpecVal::I(se::eval_str_to_int(s)),
        Op::FromInt(n) => SpecVal::S(se::eval_str_from_int(n).chars().collect()),
        Op::IsDigit(s) => SpecVal::B(se::eval_str_is_digit(s)),
        _ => return None,
    })
}

/// Build the operation term in the store.
fn op_term(terms: &mut TermStore, op: &Op) -> TermId {
    let s = |terms: &mut TermStore, x: &String| terms.mk_string(x.clone());
    let i = |terms: &mut TermStore, x: &BigInt| terms.mk_int(x.clone());
    match op {
        Op::Concat(parts) => {
            let args: Vec<TermId> = parts.iter().map(|p| s(terms, p)).collect();
            terms.mk_app(Symbol::named("str.++"), args, Sort::String)
        }
        Op::Len(x) => {
            let a = s(terms, x);
            terms.mk_app(Symbol::named("str.len"), [a], Sort::Int)
        }
        Op::At(x, n) => {
            let (a, b) = (s(terms, x), i(terms, n));
            terms.mk_app(Symbol::named("str.at"), [a, b], Sort::String)
        }
        Op::Substr(x, m, n) => {
            let (a, b, c) = (s(terms, x), i(terms, m), i(terms, n));
            terms.mk_app(Symbol::named("str.substr"), [a, b, c], Sort::String)
        }
        Op::Contains(x, y) => {
            let (a, b) = (s(terms, x), s(terms, y));
            terms.mk_app(Symbol::named("str.contains"), [a, b], Sort::Bool)
        }
        Op::PrefixOf(x, y) => {
            let (a, b) = (s(terms, x), s(terms, y));
            terms.mk_app(Symbol::named("str.prefixof"), [a, b], Sort::Bool)
        }
        Op::SuffixOf(x, y) => {
            let (a, b) = (s(terms, x), s(terms, y));
            terms.mk_app(Symbol::named("str.suffixof"), [a, b], Sort::Bool)
        }
        Op::IndexOf(x, y, n) => {
            let (a, b, c) = (s(terms, x), s(terms, y), i(terms, n));
            terms.mk_app(Symbol::named("str.indexof"), [a, b, c], Sort::Int)
        }
        Op::Replace(x, y, z) => {
            let (a, b, c) = (s(terms, x), s(terms, y), s(terms, z));
            terms.mk_app(Symbol::named("str.replace"), [a, b, c], Sort::String)
        }
        Op::ReplaceAll(x, y, z) => {
            let (a, b, c) = (s(terms, x), s(terms, y), s(terms, z));
            terms.mk_app(Symbol::named("str.replace_all"), [a, b, c], Sort::String)
        }
        Op::ToCode(x) => {
            let a = s(terms, x);
            terms.mk_app(Symbol::named("str.to_code"), [a], Sort::Int)
        }
        Op::FromCode(n) => {
            let a = i(terms, n);
            terms.mk_app(Symbol::named("str.from_code"), [a], Sort::String)
        }
        Op::ToInt(x) => {
            let a = s(terms, x);
            terms.mk_app(Symbol::named("str.to_int"), [a], Sort::Int)
        }
        Op::FromInt(n) => {
            let a = i(terms, n);
            terms.mk_app(Symbol::named("str.from_int"), [a], Sort::String)
        }
        Op::IsDigit(x) => {
            let a = s(terms, x);
            terms.mk_app(Symbol::named("str.is_digit"), [a], Sort::Bool)
        }
        Op::Lt(x, y) => {
            let (a, b) = (s(terms, x), s(terms, y));
            terms.mk_app(Symbol::named("str.<"), [a, b], Sort::Bool)
        }
        Op::Le(x, y) => {
            let (a, b) = (s(terms, x), s(terms, y));
            terms.mk_app(Symbol::named("str.<="), [a, b], Sort::Bool)
        }
        Op::Div(x, y) => {
            let (a, b) = (i(terms, x), i(terms, y));
            terms.mk_app(Symbol::named("div"), [a, b], Sort::Int)
        }
        Op::Mod(x, y) => {
            let (a, b) = (i(terms, x), i(terms, y));
            terms.mk_app(Symbol::named("mod"), [a, b], Sort::Int)
        }
    }
}

/// Read the checker's verdict on "`op` equals `want`".
fn probe_value(terms: &mut TermStore, term: TermId, want: &SpecVal, hygiene: TermId) -> Tri {
    let lit = match want {
        SpecVal::B(b) => {
            let c = terms.mk_bool(*b);
            terms.mk_app(Symbol::named("="), [term, c], Sort::Bool)
        }
        SpecVal::I(n) => {
            let c = terms.mk_int(n.clone());
            terms.mk_app(Symbol::named("="), [term, c], Sort::Bool)
        }
        SpecVal::S(s) => {
            let c = terms.mk_string(s.iter().collect::<String>());
            terms.mk_app(Symbol::named("="), [term, c], Sort::Bool)
        }
        SpecVal::Undefined => return Tri::Unknown,
    };
    probe(terms, lit, hygiene)
}

/// Integer generator: small values, boundary values, and values that overflow
/// `usize`/`i64` (the out-of-range index corner SMT-LIB still defines).
fn gen_int(rng: &mut Rng) -> BigInt {
    match rng.below(13) {
        0 => BigInt::from(-1),
        1 => BigInt::from(0),
        2 => BigInt::from(1),
        3 => BigInt::from(2),
        4 => BigInt::from(-(rng.below(9) as i64) - 1),
        5 => BigInt::from(rng.below(9) as i64),
        6 => BigInt::from(48 + rng.below(12) as i64), // near ASCII digits
        7 => BigInt::from(196_606 + rng.below(4) as i64), // SMT-LIB alphabet edge
        8 => BigInt::from(u64::MAX) * BigInt::from(u64::MAX), // > usize::MAX
        9 => -(BigInt::from(u64::MAX) * BigInt::from(u64::MAX)),
        10 => BigInt::from(i64::MAX) + BigInt::from(1), // > i64::MAX, <= usize::MAX
        // usize::MAX and its neighbours: representable, but `start + len`
        // overflows — the shape that panicked in the solver's `eval_substr`.
        11 => BigInt::from(usize::MAX as u64) - BigInt::from(rng.below(3) as i64),
        _ => BigInt::from(rng.below(30) as i64) - 10,
    }
}

fn gen_op(rng: &mut Rng) -> Op {
    let s = |rng: &mut Rng| gen_string(rng, 4);
    let t = |rng: &mut Rng| gen_string(rng, 2); // needles: often "" or 1 char
    match rng.below(19) {
        0 => Op::Concat((0..=rng.below(2)).map(|_| s(rng)).collect()),
        1 => Op::Len(s(rng)),
        2 => Op::At(s(rng), gen_int(rng)),
        3 => Op::Substr(s(rng), gen_int(rng), gen_int(rng)),
        4 => Op::Contains(s(rng), t(rng)),
        5 => Op::PrefixOf(t(rng), s(rng)),
        6 => Op::SuffixOf(t(rng), s(rng)),
        7 => Op::IndexOf(s(rng), t(rng), gen_int(rng)),
        8 => Op::Replace(s(rng), t(rng), t(rng)),
        9 => Op::ReplaceAll(s(rng), t(rng), t(rng)),
        10 => Op::ToCode(t(rng)),
        11 => Op::FromCode(gen_int(rng)),
        // Digit-heavy strings so `str.to_int` sees leading zeros and long runs.
        12 => Op::ToInt(if rng.chance(1, 2) {
            (0..=rng.below(3))
                .map(|_| *rng.pick(&['0', '1', '9']))
                .collect()
        } else {
            s(rng)
        }),
        13 => Op::FromInt(gen_int(rng)),
        14 => Op::IsDigit(t(rng)),
        15 => Op::Lt(s(rng), s(rng)),
        16 => Op::Le(s(rng), s(rng)),
        17 => Op::Div(gen_int(rng), gen_int(rng)),
        _ => Op::Mod(gen_int(rng), gen_int(rng)),
    }
}

#[test]
fn string_ops_differential_fuzz() {
    let seed = env_u64("AY_SGF_SEED", 20_260_721).wrapping_add(0x5EED);
    let cases = env_u64("AY_SGF_CASES", 1500) as usize;
    let mut rng = Rng::new(seed);
    let mut st = Stats::default();
    let mut per_op: std::collections::BTreeMap<&'static str, (usize, usize)> =
        std::collections::BTreeMap::new();

    for case in 0..cases {
        let op = gen_op(&mut rng);
        let spec = spec_op(&op);
        st.cases += 1;

        let mut terms = TermStore::new();
        let hygiene = hygiene_false_literal(&mut terms);
        let term = op_term(&mut terms, &op);

        // Oracle B: the solver's shared ground-folding functions.
        let solver = solver_op(&op);
        if let Some(sv) = &solver {
            st.solver_known += 1;
            if *sv != spec && spec != SpecVal::Undefined {
                st.record(format!(
                    "  case #{case}: {} {op:?}\n    SOLVER_EVAL={sv:?} vs SPEC={spec:?}",
                    op.name()
                ));
            }
        }

        let entry = per_op.entry(op.name()).or_default();
        entry.0 += 1;

        match &spec {
            // Under-specified: the checker must NOT commit to any value.
            SpecVal::Undefined => {
                st.underspecified += 1;
                for candidate in [
                    SpecVal::I(BigInt::from(0)),
                    SpecVal::I(BigInt::from(1)),
                    SpecVal::I(BigInt::from(-1)),
                    SpecVal::S(Vec::new()),
                ] {
                    let verdict = probe_value(&mut terms, term, &candidate, hygiene);
                    if verdict == Tri::True {
                        st.record(format!(
                            "  case #{case}: {} {op:?}\n    CHECKER committed to \
                             {candidate:?} for an SMT-LIB UNDER-SPECIFIED term",
                            op.name()
                        ));
                    }
                }
            }
            want => {
                if *want == SpecVal::B(true) {
                    st.positive += 1;
                }
                let verdict = probe_value(&mut terms, term, want, hygiene);
                match verdict {
                    Tri::True => {
                        st.checker_known += 1;
                        entry.1 += 1;
                    }
                    Tri::Unknown => {}
                    Tri::False => {
                        st.checker_known += 1;
                        // Recover what the checker DID produce, when we can.
                        let alt = solver.as_ref().filter(|sv| **sv != *want).map_or_else(
                            String::new,
                            |sv| {
                                let v = probe_value(&mut terms, term, sv, hygiene);
                                format!(" (checker-vs-solver-value: {v:?})")
                            },
                        );
                        st.record(format!(
                            "  case #{case}: {} {op:?}\n    CHECKER says NOT EQUAL to \
                             SPEC={want:?}{alt}",
                            op.name()
                        ));
                    }
                }
            }
        }
    }

    println!("[ops] per-operator (generated, checker-confirmed):");
    for (name, (made, ok)) in &per_op {
        println!("[ops]   {name:<18} generated={made:<6} checker-confirmed={ok}");
    }
    assert_eq!(per_op.len(), 19, "every operation must be exercised");
    st.finish("ops", seed, &[("solver-oracle", st.solver_known)]);
}

// ---------------------------------------------------------------------------
// Lane 3: Boolean connectives over ground string atoms
// ---------------------------------------------------------------------------
//
// The validator does not only fold `str.*`: it folds the whole propositional
// skeleton (`and`/`or`/`not`/`xor`/`=>`/`=`/`distinct`/`ite`) around the
// string atoms, and a clause is certified from ONE literal's value. A wrong
// n-ary connective (`=>` is `:right-assoc`, `xor` and `=` are chainable) turns
// a false clause into a certified tautology just as surely as a wrong
// `str.substr` does.

/// Build a random ground Boolean term together with its SMT-LIB truth value.
fn gen_formula(rng: &mut Rng, terms: &mut TermStore, depth: usize) -> (TermId, bool) {
    if depth == 0 || rng.chance(1, 3) {
        // Atom: a ground string/regex predicate whose value the spec model
        // knows independently of the checker.
        let op = loop {
            let op = gen_op(rng);
            if matches!(spec_op(&op), SpecVal::B(_)) {
                break op;
            }
        };
        let SpecVal::B(v) = spec_op(&op) else {
            unreachable!("filtered to Bool-valued operations")
        };
        return (op_term(terms, &op), v);
    }
    let arity = 2 + rng.below(2);
    let mut kids = Vec::with_capacity(arity);
    for _ in 0..arity {
        kids.push(gen_formula(rng, terms, depth - 1));
    }
    let args: Vec<TermId> = kids.iter().map(|(t, _)| *t).collect();
    let vals: Vec<bool> = kids.iter().map(|(_, v)| *v).collect();
    match rng.below(8) {
        0 => (
            terms.mk_app(Symbol::named("and"), args, Sort::Bool),
            vals.iter().all(|&v| v),
        ),
        1 => (
            terms.mk_app(Symbol::named("or"), args, Sort::Bool),
            vals.iter().any(|&v| v),
        ),
        // `xor` is `:left-assoc`, so the n-ary form is parity.
        2 => (
            terms.mk_app(Symbol::named("xor"), args, Sort::Bool),
            vals.iter().fold(false, |a, &v| a ^ v),
        ),
        // `=>` is `:right-assoc`: (=> a b c) = (=> a (=> b c)).
        3 => {
            let mut acc = *vals.last().expect("arity >= 2");
            for &v in vals[..vals.len() - 1].iter().rev() {
                acc = !v || acc;
            }
            (terms.mk_app(Symbol::named("=>"), args, Sort::Bool), acc)
        }
        // `=` is `:chainable`: all arguments equal.
        4 => (
            terms.mk_app(Symbol::named("="), args, Sort::Bool),
            vals.iter().all(|&v| v == vals[0]),
        ),
        // `distinct` is `:pairwise`.
        5 => {
            let mut all_diff = true;
            for i in 0..vals.len() {
                for j in (i + 1)..vals.len() {
                    if vals[i] == vals[j] {
                        all_diff = false;
                    }
                }
            }
            (
                terms.mk_app(Symbol::named("distinct"), args, Sort::Bool),
                all_diff,
            )
        }
        6 => {
            let t = terms.mk_not_raw(args[0]);
            (t, !vals[0])
        }
        _ => {
            let (c, t, e) = (args[0], args[1], args[args.len() - 1]);
            let v = if vals[0] {
                vals[1]
            } else {
                vals[vals.len() - 1]
            };
            (terms.mk_ite_raw(c, t, e), v)
        }
    }
}

#[test]
fn boolean_skeleton_differential_fuzz() {
    let seed = env_u64("AY_SGF_SEED", 20_260_721).wrapping_add(0xB001);
    let cases = env_u64("AY_SGF_CASES", 1500) as usize;
    let mut rng = Rng::new(seed);
    let mut st = Stats::default();

    for case in 0..cases {
        let mut terms = TermStore::new();
        let hygiene = hygiene_false_literal(&mut terms);
        let depth = 1 + rng.below(3);
        let (lit, want) = gen_formula(&mut rng, &mut terms, depth);
        st.cases += 1;
        if want {
            st.positive += 1;
        }
        let verdict = probe(&mut terms, lit, hygiene);
        if verdict != Tri::Unknown {
            st.checker_known += 1;
        }
        if verdict != Tri::Unknown && verdict != Tri::from_bool(want) {
            st.record(format!(
                "  case #{case}: CHECKER={verdict:?} vs SPEC={want} on ground formula \
                 term {lit:?}"
            ));
        }
    }
    st.finish("bool", seed, &[]);
}

// ---------------------------------------------------------------------------
// Targeted regression pins for the corners the random lanes are thin on
// ---------------------------------------------------------------------------

/// `(str.substr s m n)` with an `n` far beyond `usize`: SMT-LIB says the length
/// bound merely CLAMPS to `|s| − m`, so the answer is the whole suffix.
#[test]
fn substr_with_astronomical_length_returns_the_whole_suffix() {
    let mut terms = TermStore::new();
    let hygiene = hygiene_false_literal(&mut terms);
    let huge = BigInt::from(u64::MAX) * BigInt::from(u64::MAX);
    let op = Op::Substr("abc".to_string(), BigInt::from(1), huge);
    assert_eq!(spec_op(&op), SpecVal::S(vec!['b', 'c']));
    let term = op_term(&mut terms, &op);
    let verdict = probe_value(&mut terms, term, &SpecVal::S(vec!['b', 'c']), hygiene);
    assert_ne!(
        verdict,
        Tri::False,
        "checker must not claim (str.substr \"abc\" 1 <huge>) differs from \"bc\""
    );
    // And it must never certify the WRONG answer.
    let wrong = probe_value(&mut terms, term, &SpecVal::S(Vec::new()), hygiene);
    assert_ne!(
        wrong,
        Tri::True,
        "checker must not certify (str.substr \"abc\" 1 <huge>) = \"\""
    );
}

/// `(div a 0)` / `(mod a 0)` are under-specified in SMT-LIB; the checker must
/// fail closed rather than pick a value.
#[test]
fn division_by_zero_is_never_certified() {
    for op in [
        Op::Div(BigInt::from(7), BigInt::from(0)),
        Op::Mod(BigInt::from(7), BigInt::from(0)),
        Op::Div(BigInt::from(-7), BigInt::from(0)),
        Op::Mod(BigInt::from(0), BigInt::from(0)),
    ] {
        let mut terms = TermStore::new();
        let hygiene = hygiene_false_literal(&mut terms);
        let term = op_term(&mut terms, &op);
        for k in -3i64..=3 {
            let verdict = probe_value(&mut terms, term, &SpecVal::I(BigInt::from(k)), hygiene);
            assert_eq!(
                verdict,
                Tri::Unknown,
                "{op:?} must be UNKNOWN to the checker, got {verdict:?} for value {k}"
            );
        }
    }
}

/// The hygiene literal itself must be ground-FALSE, or every probe above is
/// vacuous.
#[test]
fn hygiene_literal_is_ground_false() {
    let mut terms = TermStore::new();
    let hygiene = hygiene_false_literal(&mut terms);
    assert!(!recognize_string_ground_eval(&terms, &[hygiene]));
    let neg = terms.mk_not_raw(hygiene);
    assert!(recognize_string_ground_eval(&terms, &[neg]));
}

/// The spec model must agree with hand-computed SMT-LIB semantics on a few
/// anchors, so a bug in the ADJUDICATOR does not silently pass the fuzz lanes.
#[test]
fn spec_model_anchors() {
    let s: Vec<char> = "aab".chars().collect();
    // `(re.++ (re.* (str.to_re "a")) (str.to_re "b"))` matches "aab".
    let re = Re::Concat(vec![
        Re::Star(Box::new(Re::Str("a".to_string()))),
        Re::Str("b".to_string()),
    ]);
    assert!(spec_in_re(&re, &s));
    // `re.comp` is complement over the FULL alphabet.
    assert!(!spec_in_re(&Re::Comp(Box::new(re.clone())), &s));
    // `((_ re.loop 2 2) re.allchar)` matches exactly the 2-char strings.
    let two = Re::Loop(Box::new(Re::AllChar), 2, 2);
    assert!(!spec_in_re(&two, &s));
    assert!(spec_in_re(&two, &"ab".chars().collect::<Vec<_>>()));
    // `lo > hi` is the empty language.
    assert!(!spec_in_re(&Re::Loop(Box::new(Re::AllChar), 3, 1), &[]));
    // `re.+` over a nullable body accepts "".
    assert!(spec_in_re(
        &Re::Plus(Box::new(Re::Opt(Box::new(Re::AllChar)))),
        &[]
    ));
    // `(re.range "b" "a")` is empty; `(re.range "ab" "c")` is empty.
    assert!(!spec_in_re(
        &Re::Range("b".to_string(), "a".to_string()),
        &"a".chars().collect::<Vec<_>>()
    ));
    assert!(!spec_in_re(
        &Re::Range("ab".to_string(), "c".to_string()),
        &"b".chars().collect::<Vec<_>>()
    ));
    // `(_ re.^ 0)` is `{""}`.
    assert!(spec_in_re(&Re::Pow(Box::new(Re::AllChar), 0), &[]));
    assert!(!spec_in_re(&Re::Pow(Box::new(Re::AllChar), 0), &s));
}

/// Code points ABOVE the SMT-LIB alphabet (`> 0x2FFFF`). AY's `\u{...}` reader
/// accepts up to `0x10FFFF`, so such a `String` constant is reachable — but it
/// is not a value of the theory's `String` sort, so the CHECKER must refuse to
/// evaluate `str.to_code` on it rather than commit to a code point the solver
/// (`eval_str_to_code`, which answers `-1`) would never agree with.
#[test]
fn out_of_alphabet_code_point_is_not_certified() {
    let big = '\u{30000}'; // 196608 = one past the SMT-LIB alphabet
    let s = big.to_string();
    assert_eq!(
        ay_strings::eval::eval_str_to_code(&s),
        BigInt::from(-1),
        "solver-side convention for an out-of-alphabet character"
    );
    let mut terms = TermStore::new();
    let hygiene = hygiene_false_literal(&mut terms);
    let term = op_term(&mut terms, &Op::ToCode(s));
    for cand in [BigInt::from(196_608), BigInt::from(-1), BigInt::from(0)] {
        let v = probe_value(&mut terms, term, &SpecVal::I(cand.clone()), hygiene);
        assert_eq!(
            v,
            Tri::Unknown,
            "checker must fail closed on (str.to_code \"\\u{{30000}}\"), not \
             certify it equals {cand}"
        );
    }
}

/// `str.from_code` of a SURROGATE code point: inside the SMT-LIB alphabet, but
/// not representable in AY's `String`. The checker must fail closed (the solver
/// answers `""`, which the standard does not license).
#[test]
fn surrogate_from_code_is_not_certified() {
    let mut terms = TermStore::new();
    let hygiene = hygiene_false_literal(&mut terms);
    let term = op_term(&mut terms, &Op::FromCode(BigInt::from(0xD800)));
    for cand in [SpecVal::S(Vec::new()), SpecVal::S(vec!['a'])] {
        let v = probe_value(&mut terms, term, &cand, hygiene);
        assert_eq!(v, Tri::Unknown, "checker must fail closed on {cand:?}");
    }
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Strict semantic validation for `TheoryLemmaKind::StringGroundEval`.
//!
//! A `StringGroundEval` lemma claims: "this clause contains a literal that is
//! GROUND — every leaf is a string/integer/Boolean constant or a regular
//! expression built only from constants — and evaluates to `true` under the
//! SMT-LIB Unicode-string semantics." A clause with a literal that is true
//! under every interpretation is a tautology, hence a valid theory lemma.
//!
//! The overwhelmingly common instance is the QF_S "sink" shape: preprocessing
//! propagates `(= literal_5 "/mod/forum/")` into `(str.in_re literal_5 R)`,
//! and the refutation reduces to "the CONSTANT `/mod/forum/` is not in the
//! language of the ground regex `R`". That is a decidable, closed-form fact,
//! so a proof checker can confirm it outright instead of trusting the solver.
//!
//! INDEPENDENCE. This evaluator is deliberately a SEPARATE implementation from
//! the solver-side one (`ay-theories/strings` `RegexSolver::evaluate` /
//! `WeRegex`). A checker that called the solver's evaluator would only confirm
//! that the solver agrees with itself. The semantics are mirrored from the
//! SMT-LIB 2.6 Unicode strings theory; the algorithms (memoized interval
//! matcher over a `char` vector vs. the solver's recursive slice backtracker)
//! are not shared.
//!
//! FAIL-CLOSED. Every partial function returns `None` — never a guess — when
//! a term is non-ground, uses an operator this evaluator does not implement,
//! is under-specified by SMT-LIB (`(div x 0)`), or the work budget runs out.
//! `None` propagates to a rejected lemma, never to an accepted one.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet};
use ay_core::{Constant, ProofId, Sort, Symbol, TermData, TermId, TermStore};
use num_bigint::BigInt;
use num_traits::{Signed, ToPrimitive, Zero};

use super::ProofCheckError;

/// Work budget for one clause validation: each memo miss in the regex matcher
/// and each term evaluation costs one unit. Exhaustion fails closed.
///
/// Sized so a pathological regex cannot turn proof classification into a
/// second-scale cost: the matcher is `O(|R| · n²)` memoized, so realistic
/// QF_S/QF_SLIA instances finish in thousands of units.
const EVAL_BUDGET: u64 = 4_000_000;

/// A fully evaluated ground value.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Val {
    Bool(bool),
    Int(BigInt),
    Str(Vec<char>),
}

impl Val {
    fn as_bool(&self) -> Option<bool> {
        match self {
            Self::Bool(b) => Some(*b),
            _ => None,
        }
    }
    fn as_int(&self) -> Option<&BigInt> {
        match self {
            Self::Int(i) => Some(i),
            _ => None,
        }
    }
    fn as_str(&self) -> Option<&[char]> {
        match self {
            Self::Str(s) => Some(s),
            _ => None,
        }
    }
}

/// Validate a `TheoryLemmaKind::StringGroundEval` lemma in strict mode.
pub(crate) fn validate_string_ground_eval(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    if clause.is_empty() {
        return Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: "string_ground_eval clause must be non-empty".to_string(),
        });
    }
    for &lit in clause {
        if !matches!(terms.sort(lit), Sort::Bool) {
            return Err(ProofCheckError::InvalidTheoryLemma {
                step: step_id,
                reason: format!(
                    "string_ground_eval literal has non-Bool sort {:?}; lemma \
                     clauses must be propositional",
                    terms.sort(lit)
                ),
            });
        }
    }
    if clause_has_true_ground_literal(terms, clause) {
        return Ok(());
    }
    Err(ProofCheckError::InvalidTheoryLemma {
        step: step_id,
        reason: "string_ground_eval clause has no literal that the independent \
                 ground string/regex evaluator proves TRUE; rejecting in \
                 fail-closed mode"
            .to_string(),
    })
}

/// Recognize a clause the strict `StringGroundEval` validator will accept:
/// non-empty, propositional, mentioning string/regex content, and carrying at
/// least one ground literal that evaluates to `true`.
///
/// This is the EXACT precondition of [`validate_string_ground_eval`] (plus the
/// string-content hygiene gate), so the proof classifier in `ay-dpll` can only
/// assign the kind to lemmas strict mode will then accept — no
/// classifier/checker drift. Evaluation logic lives ONLY in this module.
#[must_use]
pub fn recognize_string_ground_eval(terms: &TermStore, clause: &[TermId]) -> bool {
    if clause.is_empty() {
        return false;
    }
    if clause
        .iter()
        .any(|&lit| !matches!(terms.sort(lit), Sort::Bool))
    {
        return false;
    }
    // Hygiene: a clause with no string/regex content is not a string lemma,
    // even if some Boolean literal happens to fold to `true`. Keeping the kind
    // honest means the rule name in the exported proof means what it says.
    if !mentions_string_or_regex(terms, clause) {
        return false;
    }
    clause_has_true_ground_literal(terms, clause)
}

fn clause_has_true_ground_literal(terms: &TermStore, clause: &[TermId]) -> bool {
    let mut eval = GroundEval::new(terms);
    clause
        .iter()
        .any(|&lit| eval.eval(lit).and_then(|v| v.as_bool()) == Some(true))
}

fn mentions_string_or_regex(terms: &TermStore, clause: &[TermId]) -> bool {
    let mut stack: Vec<TermId> = clause.to_vec();
    let mut visited: DetHashSet<TermId> = DetHashSet::default();
    while let Some(t) = stack.pop() {
        if !visited.insert(t) {
            continue;
        }
        if matches!(terms.sort(t), Sort::String | Sort::RegLan) {
            return true;
        }
        stack.extend(terms.children(t));
    }
    false
}

// ---------------------------------------------------------------------------
// Ground term evaluation
// ---------------------------------------------------------------------------

struct GroundEval<'a> {
    terms: &'a TermStore,
    budget: u64,
    /// Memo for `(regex, start, end)` interval membership.
    re_memo: HashMap<(TermId, usize, usize), bool>,
    /// Memo for `(loop-node, lo, hi, start, end)` bounded repetition.
    loop_memo: HashMap<(TermId, u64, u64, usize, usize), bool>,
    /// Memo for whole-term evaluation.
    val_memo: HashMap<TermId, Option<Val>>,
    /// The string currently being matched, as code points.
    subject: Vec<char>,
}

impl<'a> GroundEval<'a> {
    fn new(terms: &'a TermStore) -> Self {
        Self {
            terms,
            budget: EVAL_BUDGET,
            re_memo: HashMap::default(),
            loop_memo: HashMap::default(),
            val_memo: HashMap::default(),
            subject: Vec::new(),
        }
    }

    fn spend(&mut self) -> Option<()> {
        if self.budget == 0 {
            return None;
        }
        self.budget -= 1;
        Some(())
    }

    fn eval(&mut self, term: TermId) -> Option<Val> {
        if let Some(cached) = self.val_memo.get(&term) {
            return cached.clone();
        }
        self.spend()?;
        let result = self.eval_uncached(term);
        self.val_memo.insert(term, result.clone());
        result
    }

    fn eval_uncached(&mut self, term: TermId) -> Option<Val> {
        match self.terms.get(term) {
            TermData::Const(Constant::Bool(b)) => Some(Val::Bool(*b)),
            TermData::Const(Constant::Int(i)) => Some(Val::Int(i.clone())),
            TermData::Const(Constant::String(s)) => Some(Val::Str(s.chars().collect())),
            TermData::Not(inner) => {
                let inner = *inner;
                Some(Val::Bool(!self.eval(inner)?.as_bool()?))
            }
            TermData::Ite(c, t, e) => {
                let (c, t, e) = (*c, *t, *e);
                if self.eval(c)?.as_bool()? {
                    self.eval(t)
                } else {
                    self.eval(e)
                }
            }
            TermData::App(sym, args) => {
                let args = args.clone();
                let sym = sym.clone();
                self.eval_app(&sym, &args)
            }
            _ => None,
        }
    }

    #[allow(clippy::too_many_lines)]
    fn eval_app(&mut self, sym: &Symbol, args: &[TermId]) -> Option<Val> {
        let name = sym.name();
        match (name, args.len()) {
            // ---- Boolean connectives ----
            ("and", _) if !args.is_empty() => {
                for &a in args {
                    if !self.eval(a)?.as_bool()? {
                        return Some(Val::Bool(false));
                    }
                }
                Some(Val::Bool(true))
            }
            ("or", _) if !args.is_empty() => {
                for &a in args {
                    if self.eval(a)?.as_bool()? {
                        return Some(Val::Bool(true));
                    }
                }
                Some(Val::Bool(false))
            }
            ("xor", _) if !args.is_empty() => {
                let mut acc = false;
                for &a in args {
                    acc ^= self.eval(a)?.as_bool()?;
                }
                Some(Val::Bool(acc))
            }
            ("not", 1) => Some(Val::Bool(!self.eval(args[0])?.as_bool()?)),
            ("=>", _) if args.len() >= 2 => {
                // Right-associative implication chain.
                let mut vals = Vec::with_capacity(args.len());
                for &a in args {
                    vals.push(self.eval(a)?.as_bool()?);
                }
                let mut acc = *vals.last().expect("non-empty");
                for &v in vals[..vals.len() - 1].iter().rev() {
                    acc = !v || acc;
                }
                Some(Val::Bool(acc))
            }

            // ---- equality / distinct (any evaluable sort) ----
            ("=", _) if args.len() >= 2 => {
                let first = self.eval(args[0])?;
                for &a in &args[1..] {
                    if self.eval(a)? != first {
                        return Some(Val::Bool(false));
                    }
                }
                Some(Val::Bool(true))
            }
            ("distinct", _) if args.len() >= 2 => {
                let mut vals = Vec::with_capacity(args.len());
                for &a in args {
                    vals.push(self.eval(a)?);
                }
                for i in 0..vals.len() {
                    for j in (i + 1)..vals.len() {
                        if vals[i] == vals[j] {
                            return Some(Val::Bool(false));
                        }
                    }
                }
                Some(Val::Bool(true))
            }

            // ---- integer arithmetic ----
            ("+", _) if !args.is_empty() => {
                let mut acc = BigInt::from(0u8);
                for &a in args {
                    acc += self.eval(a)?.as_int()?;
                }
                Some(Val::Int(acc))
            }
            ("*", _) if !args.is_empty() => {
                let mut acc = BigInt::from(1u8);
                for &a in args {
                    acc *= self.eval(a)?.as_int()?;
                }
                Some(Val::Int(acc))
            }
            ("-", 1) => Some(Val::Int(-self.eval(args[0])?.as_int()?.clone())),
            ("-", _) if args.len() >= 2 => {
                let mut acc = self.eval(args[0])?.as_int()?.clone();
                for &a in &args[1..] {
                    acc -= self.eval(a)?.as_int()?;
                }
                Some(Val::Int(acc))
            }
            ("abs", 1) => Some(Val::Int(self.eval(args[0])?.as_int()?.abs())),
            ("div", 2) | ("mod", 2) => {
                let a = self.eval(args[0])?.as_int()?.clone();
                let b = self.eval(args[1])?.as_int()?.clone();
                if b.is_zero() {
                    // Under-specified in SMT-LIB: fail closed.
                    return None;
                }
                // Euclidean division: `a = b*q + r` with `0 <= r < |b|`.
                let mut q = &a / &b;
                let mut r = &a - &q * &b;
                if r.is_negative() {
                    if b.is_positive() {
                        q -= 1;
                    } else {
                        q += 1;
                    }
                    r = &a - &q * &b;
                }
                Some(Val::Int(if name == "div" { q } else { r }))
            }
            ("<" | "<=" | ">" | ">=", 2) => {
                let a = self.eval(args[0])?;
                let b = self.eval(args[1])?;
                // SMT-LIB comparisons here are integer-only (Real constants
                // are not a `Val` variant, so they fail closed above).
                let (a, b) = (a.as_int()?, b.as_int()?);
                Some(Val::Bool(match name {
                    "<" => a < b,
                    "<=" => a <= b,
                    ">" => a > b,
                    _ => a >= b,
                }))
            }

            // ---- string operations (SMT-LIB 2.6 Unicode strings) ----
            ("str.++", _) if !args.is_empty() => {
                let mut acc: Vec<char> = Vec::new();
                for &a in args {
                    acc.extend_from_slice(self.eval(a)?.as_str()?);
                }
                Some(Val::Str(acc))
            }
            ("str.len", 1) => Some(Val::Int(BigInt::from(self.eval(args[0])?.as_str()?.len()))),
            ("str.at", 2) => {
                let s = self.eval(args[0])?.as_str()?.to_vec();
                let i = self.eval(args[1])?.as_int()?.clone();
                let idx = i.to_usize();
                Some(Val::Str(match idx {
                    Some(i) if i < s.len() => vec![s[i]],
                    _ => Vec::new(),
                }))
            }
            ("str.substr", 3) => {
                let s = self.eval(args[0])?.as_str()?.to_vec();
                let i = self.eval(args[1])?.as_int()?.clone();
                let n = self.eval(args[2])?.as_int()?.clone();
                // SMT-LIB 2.6 Unicode strings: `(str.substr s m n)` is the
                // unique `w` with `s = u·w·v`, `|u| = m` and
                // `|w| = min(n, |s| - m)` when `0 <= m < |s|` and `0 < n`;
                // otherwise the empty string.
                if !n.is_positive() {
                    return Some(Val::Str(Vec::new()));
                }
                // `i` outside `usize` is either negative or `>= |s|` (no string
                // is longer than `usize::MAX`); both give the empty string.
                let Some(i) = i.to_usize() else {
                    return Some(Val::Str(Vec::new()));
                };
                if i >= s.len() {
                    return Some(Val::Str(Vec::new()));
                }
                // `n` is only ever a CLAMP (`min(n, |s| - m)`), so an `n` too
                // large for `usize` selects the whole suffix. Reading it as
                // "unrepresentable, answer the empty string" was a WRONG value
                // — and a wrong value on this path is a wrong self-certified
                // UNSAT (#string-ground-substr-huge-length).
                let avail = s.len() - i;
                let take = n.to_usize().map_or(avail, |n| usize::min(n, avail));
                Some(Val::Str(s[i..i + take].to_vec()))
            }
            ("str.contains", 2) => {
                let s = self.eval(args[0])?.as_str()?.to_vec();
                let t = self.eval(args[1])?.as_str()?.to_vec();
                Some(Val::Bool(find_sub(&s, &t, 0).is_some()))
            }
            ("str.prefixof", 2) => {
                let t = self.eval(args[0])?.as_str()?.to_vec();
                let s = self.eval(args[1])?.as_str()?.to_vec();
                Some(Val::Bool(s.len() >= t.len() && s[..t.len()] == t[..]))
            }
            ("str.suffixof", 2) => {
                let t = self.eval(args[0])?.as_str()?.to_vec();
                let s = self.eval(args[1])?.as_str()?.to_vec();
                Some(Val::Bool(
                    s.len() >= t.len() && s[s.len() - t.len()..] == t[..],
                ))
            }
            ("str.indexof", 3) => {
                let s = self.eval(args[0])?.as_str()?.to_vec();
                let t = self.eval(args[1])?.as_str()?.to_vec();
                let i = self.eval(args[2])?.as_int()?.clone();
                let minus_one = || Val::Int(BigInt::from(-1i8));
                let Some(start) = i.to_usize() else {
                    return Some(minus_one());
                };
                if start > s.len() {
                    return Some(minus_one());
                }
                Some(match find_sub(&s, &t, start) {
                    Some(pos) => Val::Int(BigInt::from(pos)),
                    None => minus_one(),
                })
            }
            ("str.replace", 3) => {
                let s = self.eval(args[0])?.as_str()?.to_vec();
                let t = self.eval(args[1])?.as_str()?.to_vec();
                let u = self.eval(args[2])?.as_str()?.to_vec();
                if t.is_empty() {
                    let mut out = u;
                    out.extend_from_slice(&s);
                    return Some(Val::Str(out));
                }
                Some(Val::Str(match find_sub(&s, &t, 0) {
                    Some(pos) => {
                        let mut out = s[..pos].to_vec();
                        out.extend_from_slice(&u);
                        out.extend_from_slice(&s[pos + t.len()..]);
                        out
                    }
                    None => s,
                }))
            }
            ("str.replace_all", 3) => {
                let s = self.eval(args[0])?.as_str()?.to_vec();
                let t = self.eval(args[1])?.as_str()?.to_vec();
                let u = self.eval(args[2])?.as_str()?.to_vec();
                if t.is_empty() {
                    return Some(Val::Str(s));
                }
                let mut out: Vec<char> = Vec::new();
                let mut pos = 0usize;
                while let Some(hit) = find_sub(&s, &t, pos) {
                    out.extend_from_slice(&s[pos..hit]);
                    out.extend_from_slice(&u);
                    pos = hit + t.len();
                    self.spend()?;
                }
                out.extend_from_slice(&s[pos..]);
                Some(Val::Str(out))
            }
            ("str.to_code" | "str.to.code", 1) => {
                let s = self.eval(args[0])?.as_str()?.to_vec();
                if s.len() != 1 {
                    return Some(Val::Int(BigInt::from(-1i8)));
                }
                // The SMT-LIB Unicode alphabet is exactly the code points
                // `0 .. 0x2FFFF`. AY's `\u{...}` reader is more permissive than
                // the standard and can mint a `String` constant holding a HIGHER
                // code point; such a constant is not a value of sort `String`,
                // so this evaluator has no defined answer and must not guess.
                // (It used to return the raw code point while the solver's
                // `eval_str_to_code` returns `-1` — a silent semantic split on
                // the certification path.) Same policy as `str.from_code`
                // below, which already fails closed on an unrepresentable code
                // point.
                if s[0] as u32 > 0x0002_FFFF {
                    return None;
                }
                Some(Val::Int(BigInt::from(s[0] as u32)))
            }
            ("str.from_code" | "str.from.code", 1) => {
                let n = self.eval(args[0])?.as_int()?.clone();
                let Some(n) = n.to_u32() else {
                    return Some(Val::Str(Vec::new()));
                };
                if n > 0x0002_FFFF {
                    return Some(Val::Str(Vec::new()));
                }
                // A code point inside the SMT-LIB alphabet that Rust cannot
                // represent as a `char` (surrogate range) is not something this
                // evaluator will guess about.
                let c = char::from_u32(n)?;
                Some(Val::Str(vec![c]))
            }
            ("str.to_int" | "str.to.int", 1) => {
                let s = self.eval(args[0])?.as_str()?.to_vec();
                if s.is_empty() || !s.iter().all(char::is_ascii_digit) {
                    return Some(Val::Int(BigInt::from(-1i8)));
                }
                let digits: String = s.iter().collect();
                Some(Val::Int(digits.parse::<BigInt>().ok()?))
            }
            ("str.from_int" | "str.from.int", 1) => {
                let n = self.eval(args[0])?.as_int()?.clone();
                if n.is_negative() {
                    return Some(Val::Str(Vec::new()));
                }
                Some(Val::Str(n.to_string().chars().collect()))
            }
            ("str.is_digit" | "str.is.digit", 1) => {
                let s = self.eval(args[0])?.as_str()?.to_vec();
                Some(Val::Bool(s.len() == 1 && s[0].is_ascii_digit()))
            }
            ("str.<", 2) => {
                let a = self.eval(args[0])?.as_str()?.to_vec();
                let b = self.eval(args[1])?.as_str()?.to_vec();
                Some(Val::Bool(lex_lt(&a, &b)))
            }
            ("str.<=", 2) => {
                let a = self.eval(args[0])?.as_str()?.to_vec();
                let b = self.eval(args[1])?.as_str()?.to_vec();
                Some(Val::Bool(a == b || lex_lt(&a, &b)))
            }

            // ---- regular-expression membership ----
            ("str.in_re" | "str.in.re", 2) => {
                let s = self.eval(args[0])?.as_str()?.to_vec();
                let saved = std::mem::replace(&mut self.subject, s);
                // Memo tables are keyed by interval into `subject`; a new
                // subject invalidates them.
                let saved_re = std::mem::take(&mut self.re_memo);
                let saved_loop = std::mem::take(&mut self.loop_memo);
                let end = self.subject.len();
                let result = self.re_match(args[1], 0, end);
                self.subject = saved;
                self.re_memo = saved_re;
                self.loop_memo = saved_loop;
                Some(Val::Bool(result?))
            }

            _ => None,
        }
    }

    // -----------------------------------------------------------------------
    // Regex membership: does `subject[i..j]` belong to the language of `r`?
    // -----------------------------------------------------------------------

    fn re_match(&mut self, r: TermId, i: usize, j: usize) -> Option<bool> {
        if let Some(&cached) = self.re_memo.get(&(r, i, j)) {
            return Some(cached);
        }
        self.spend()?;
        let result = self.re_match_uncached(r, i, j)?;
        self.re_memo.insert((r, i, j), result);
        Some(result)
    }

    #[allow(clippy::too_many_lines)]
    fn re_match_uncached(&mut self, r: TermId, i: usize, j: usize) -> Option<bool> {
        let TermData::App(sym, args) = self.terms.get(r) else {
            return None;
        };
        let sym = sym.clone();
        let args = args.clone();
        let name = sym.name();
        match (name, args.len()) {
            ("re.none", 0) => Some(false),
            ("re.all", 0) => Some(true),
            ("re.allchar", 0) => Some(j == i + 1),
            ("re.range", 2) => {
                let lo = self.eval(args[0])?.as_str()?.to_vec();
                let hi = self.eval(args[1])?.as_str()?.to_vec();
                // `(re.range lo hi)` denotes the EMPTY language whenever an
                // endpoint is not a single character, or `lo > hi`.
                if lo.len() != 1 || hi.len() != 1 || lo[0] > hi[0] || j != i + 1 {
                    return Some(false);
                }
                let c = self.subject[i];
                Some(lo[0] <= c && c <= hi[0])
            }
            ("str.to_re" | "str.to.re", 1) => {
                let t = self.eval(args[0])?.as_str()?.to_vec();
                Some(self.subject[i..j] == t[..])
            }
            ("re.++", _) if !args.is_empty() => self.re_concat(r, &args, 0, i, j),
            ("re.union", _) if !args.is_empty() => {
                for &child in &args {
                    if self.re_match(child, i, j)? {
                        return Some(true);
                    }
                }
                Some(false)
            }
            ("re.inter", _) if !args.is_empty() => {
                for &child in &args {
                    if !self.re_match(child, i, j)? {
                        return Some(false);
                    }
                }
                Some(true)
            }
            ("re.*", 1) => self.re_star(args[0], i, j),
            ("re.+", 1) => {
                if i == j {
                    // `R+` accepts "" exactly when `R` does.
                    self.re_match(args[0], i, i)
                } else {
                    self.re_star(args[0], i, j)
                }
            }
            ("re.opt", 1) => {
                if i == j {
                    return Some(true);
                }
                self.re_match(args[0], i, j)
            }
            ("re.comp", 1) => Some(!self.re_match(args[0], i, j)?),
            ("re.diff", _) if args.len() >= 2 => {
                // `:left-assoc`: `(re.diff a b c)` == `a \ b \ c`.
                if !self.re_match(args[0], i, j)? {
                    return Some(false);
                }
                for &child in &args[1..] {
                    if self.re_match(child, i, j)? {
                        return Some(false);
                    }
                }
                Some(true)
            }
            ("re.loop", 1) => {
                let Symbol::Indexed(_, indices) = &sym else {
                    return None;
                };
                let [lo, hi] = indices[..] else {
                    return None;
                };
                self.re_loop(r, args[0], u64::from(lo), u64::from(hi), i, j)
            }
            ("re.^", 1) => {
                let Symbol::Indexed(_, indices) = &sym else {
                    return None;
                };
                let [n] = indices[..] else {
                    return None;
                };
                self.re_loop(r, args[0], u64::from(n), u64::from(n), i, j)
            }
            _ => None,
        }
    }

    /// `subject[i..j]` matches `args[k..]` concatenated.
    fn re_concat(
        &mut self,
        node: TermId,
        args: &[TermId],
        k: usize,
        i: usize,
        j: usize,
    ) -> Option<bool> {
        if k == args.len() {
            return Some(i == j);
        }
        if k == args.len() - 1 {
            return self.re_match(args[k], i, j);
        }
        // Memo key reuses the loop table's shape: (node, k, 0, i, j).
        let key = (node, k as u64, u64::MAX, i, j);
        if let Some(&cached) = self.loop_memo.get(&key) {
            return Some(cached);
        }
        self.spend()?;
        let mut result = false;
        for m in i..=j {
            if self.re_match(args[k], i, m)? && self.re_concat(node, args, k + 1, m, j)? {
                result = true;
                break;
            }
        }
        self.loop_memo.insert(key, result);
        Some(result)
    }

    /// `subject[i..j]` matches `R*`. Any decomposition can drop its empty
    /// pieces, so it suffices to search decompositions into NON-EMPTY pieces.
    fn re_star(&mut self, body: TermId, i: usize, j: usize) -> Option<bool> {
        if i == j {
            return Some(true);
        }
        let key = (body, u64::MAX, u64::MAX, i, j);
        if let Some(&cached) = self.loop_memo.get(&key) {
            return Some(cached);
        }
        self.spend()?;
        // Guard against a cyclic memo probe (a self-referential term store
        // entry cannot occur, but the recursion is easier to reason about with
        // the pending value pinned to `false` — an unsound `true` can never be
        // read back).
        self.loop_memo.insert(key, false);
        let mut result = false;
        for m in (i + 1)..=j {
            if self.re_match(body, i, m)? && self.re_star(body, m, j)? {
                result = true;
                break;
            }
        }
        self.loop_memo.insert(key, result);
        Some(result)
    }

    /// `subject[i..j]` matches `R` repeated between `lo` and `hi` times.
    fn re_loop(
        &mut self,
        node: TermId,
        body: TermId,
        lo: u64,
        hi: u64,
        i: usize,
        j: usize,
    ) -> Option<bool> {
        if lo > hi {
            // Empty language.
            return Some(false);
        }
        let n = (j - i) as u64;
        // `R` nullable? Membership of "" is position-independent.
        let nullable = self.re_match(body, i, i)?;
        let (lo, hi) = if nullable {
            // With "" in R, `R^k ⊆ R^(k+1)`, so the union over `lo..=hi` is
            // `R^hi`; and a word of length `n` needs at most `max(n, 1)`
            // non-empty factors, the rest padded with "".
            (0u64, hi.min(n.max(1)))
        } else {
            if lo > n {
                return Some(false);
            }
            (lo, hi.min(n))
        };
        self.re_loop_exact(node, body, lo, hi, i, j)
    }

    fn re_loop_exact(
        &mut self,
        node: TermId,
        body: TermId,
        lo: u64,
        hi: u64,
        i: usize,
        j: usize,
    ) -> Option<bool> {
        if lo == 0 && i == j {
            return Some(true);
        }
        if hi == 0 {
            return Some(false);
        }
        let key = (node, lo, hi, i, j);
        if let Some(&cached) = self.loop_memo.get(&key) {
            return Some(cached);
        }
        self.spend()?;
        self.loop_memo.insert(key, false);
        let mut result = false;
        for m in i..=j {
            if self.re_match(body, i, m)?
                && self.re_loop_exact(node, body, lo.saturating_sub(1), hi - 1, m, j)?
            {
                result = true;
                break;
            }
        }
        self.loop_memo.insert(key, result);
        Some(result)
    }
}

/// First index `>= from` at which `needle` occurs in `haystack`.
fn find_sub(haystack: &[char], needle: &[char], from: usize) -> Option<usize> {
    if needle.is_empty() {
        return (from <= haystack.len()).then_some(from);
    }
    if needle.len() > haystack.len() {
        return None;
    }
    (from..=haystack.len().saturating_sub(needle.len()))
        .find(|&start| haystack[start..start + needle.len()] == needle[..])
}

/// SMT-LIB `str.<`: lexicographic order on code points, with the proper prefix
/// ordering strictly below its extensions.
fn lex_lt(a: &[char], b: &[char]) -> bool {
    for (x, y) in a.iter().zip(b.iter()) {
        if x != y {
            return x < y;
        }
    }
    a.len() < b.len()
}

#[cfg(test)]
#[path = "string_ground_tests.rs"]
mod string_ground_tests;

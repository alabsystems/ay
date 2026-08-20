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
//!
//! NAME AUTHORITY. This evaluator recognizes an operator by its SPELLING, so
//! every spelling it interprets must be one `ay-frontend` GUARANTEES denotes
//! the native operator — a member of `RESERVED_OP_NAMES` (undeclarable) or of
//! the `MapTarget`/`DeclarationActivated` rows of
//! `EXCLUDED_DECLARABLE_OP_NAMES`, i.e. exactly
//! `ay_frontend::is_canonical_theory_operator_identity`. A spelling outside
//! that set is an ordinary user symbol: `(declare-fun <spelling> …)` succeeds
//! and the declaration keeps that exact surface name in the core term DAG, so
//! interpreting it here would certify a "ground tautology" about a function the
//! problem left uninterpreted.
//!
//! Four invented dotted spellings — `str.to.code`, `str.from.code`,
//! `str.from.int`, `str.is.digit` — were accepted here as aliases and were
//! exactly that hole. They are in NEITHER frontend table, no elaborator arm
//! produces them, and z3 5.0.0 rejects them ("unknown constant str.to.code"),
//! so the only way such an application can exist is a user declaration. They
//! are gone. The genuine SMT-LIB 2.5 dotted aliases this evaluator still
//! accepts (`str.to.int`, `str.to.re`, `str.in.re`) ARE reserved, so they stay.
//! `checker/name_authority_tests.rs` re-derives this condition mechanically
//! from these sources at test time and fails on any new unowned spelling.

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
pub(crate) const STRING_EVAL_WORK_LIMIT: usize = 4_000_000;

/// Aggregate `Vec<char>` payload that one ground-string validation may
/// allocate, including decoded constants, memoized-value clones, cached-value
/// returns, and operation scratch/output buffers. Every debit happens before
/// the corresponding allocation. The strict-authentication meter precharges
/// this exact shared constant before entering the evaluator.
pub(crate) const STRING_CHAR_ALLOCATION_LIMIT: usize = 16 * 1024 * 1024;

/// Aggregate bit-complexity work for arbitrary-precision integer operations.
/// This is separate from term/regex state work so the outer meter can debit
/// both fixed maxima before evaluation.
pub(crate) const STRING_NUMERIC_WORK_LIMIT: usize = 4_000_000;

/// Aggregate payload bits allocated by decoded, derived, memoized, and cached
/// `BigInt` values during one validation.
pub(crate) const STRING_NUMERIC_BIT_ALLOCATION_LIMIT: usize = 16 * 1024 * 1024;

const MAX_NUMERIC_VALUE_BITS: usize = 4096;
const MAX_NUMERIC_DECIMAL_DIGITS: usize = 1024;

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

/// The hygiene gate of [`recognize_string_ground_eval`], on its own.
///
/// Exported so a caller that classifies MANY sub-clauses of one conflict can
/// pay for the DAG walk once. It is exact rather than approximate, and it is
/// MONOTONE in the clause: the terms reachable from a sub-clause are a subset
/// of those reachable from the clause, so `false` here proves `false` for every
/// sub-clause, and skipping the recognizer on those sub-clauses cannot change
/// which lemma kind is inferred.
pub fn clause_mentions_string_or_regex(terms: &TermStore, clause: &[TermId]) -> bool {
    mentions_string_or_regex(terms, clause)
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
    string_chars_remaining: usize,
    numeric_work_remaining: usize,
    numeric_bits_remaining: usize,
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
            budget: STRING_EVAL_WORK_LIMIT as u64,
            string_chars_remaining: STRING_CHAR_ALLOCATION_LIMIT,
            numeric_work_remaining: STRING_NUMERIC_WORK_LIMIT,
            numeric_bits_remaining: STRING_NUMERIC_BIT_ALLOCATION_LIMIT,
            re_memo: HashMap::default(),
            loop_memo: HashMap::default(),
            val_memo: HashMap::default(),
            subject: Vec::new(),
        }
    }

    fn spend(&mut self) -> Option<()> {
        self.spend_work(1)
    }

    fn spend_work(&mut self, work: usize) -> Option<()> {
        let work = u64::try_from(work).ok()?;
        self.budget = self.budget.checked_sub(work)?;
        Some(())
    }

    fn reserve_string_chars(&mut self, chars: usize) -> Option<()> {
        self.string_chars_remaining = self.string_chars_remaining.checked_sub(chars)?;
        Some(())
    }

    fn bigint_bits(value: &BigInt) -> Option<usize> {
        usize::try_from(value.bits()).ok()
    }

    fn numeric_storage_bits(bits: usize) -> Option<usize> {
        if bits == 0 {
            return Some(0);
        }
        let limb_bits = usize::BITS as usize;
        bits.checked_add(limb_bits.checked_sub(1)?)?
            .checked_div(limb_bits)?
            .checked_mul(limb_bits)
    }

    fn reserve_numeric_bits(&mut self, bits: usize) -> Option<()> {
        if bits > MAX_NUMERIC_VALUE_BITS {
            return None;
        }
        let storage_bits = Self::numeric_storage_bits(bits)?;
        self.numeric_bits_remaining = self.numeric_bits_remaining.checked_sub(storage_bits)?;
        Some(())
    }

    fn reserve_numeric_intermediate_bits(&mut self, bits: usize) -> Option<()> {
        let storage_bits = Self::numeric_storage_bits(bits)?;
        self.numeric_bits_remaining = self.numeric_bits_remaining.checked_sub(storage_bits)?;
        Some(())
    }

    fn spend_numeric_work(&mut self, work: usize) -> Option<()> {
        self.numeric_work_remaining = self.numeric_work_remaining.checked_sub(work)?;
        Some(())
    }

    fn eval_int(&mut self, term: TermId) -> Option<BigInt> {
        match self.eval(term)? {
            Val::Int(value) => Some(value),
            _ => None,
        }
    }

    fn values_equal(&mut self, left: &Val, right: &Val) -> Option<bool> {
        match (left, right) {
            (Val::Str(left), Val::Str(right)) => {
                self.spend_work(left.len().max(right.len()))?;
            }
            (Val::Int(left), Val::Int(right)) => {
                let left = Self::bigint_bits(left)?;
                let right = Self::bigint_bits(right)?;
                self.spend_numeric_work(left.max(right).max(1))?;
            }
            _ => {}
        }
        Some(left == right)
    }

    fn add_int(&mut self, left: BigInt, right: &BigInt) -> Option<BigInt> {
        let left_bits = Self::bigint_bits(&left)?;
        let right_bits = Self::bigint_bits(right)?;
        let result_bits = left_bits.max(right_bits).checked_add(1)?;
        self.reserve_numeric_bits(result_bits)?;
        self.spend_numeric_work(left_bits.max(right_bits).max(1))?;
        Some(left + right)
    }

    fn sub_int(&mut self, left: BigInt, right: &BigInt) -> Option<BigInt> {
        let left_bits = Self::bigint_bits(&left)?;
        let right_bits = Self::bigint_bits(right)?;
        let result_bits = left_bits.max(right_bits).checked_add(1)?;
        self.reserve_numeric_bits(result_bits)?;
        self.spend_numeric_work(left_bits.max(right_bits).max(1))?;
        Some(left - right)
    }

    fn mul_int(&mut self, left: BigInt, right: &BigInt) -> Option<BigInt> {
        let left_bits = Self::bigint_bits(&left)?;
        let right_bits = Self::bigint_bits(right)?;
        let result_bits = left_bits.checked_add(right_bits)?;
        self.reserve_numeric_bits(result_bits)?;
        let work = left_bits.max(1).checked_mul(right_bits.max(1))?;
        self.spend_numeric_work(work)?;
        Some(left * right)
    }

    fn unary_int(&mut self, value: &BigInt) -> Option<()> {
        let bits = Self::bigint_bits(value)?;
        self.reserve_numeric_bits(bits)?;
        self.spend_numeric_work(bits.max(1))
    }

    fn precharge_division(&mut self, left: &BigInt, right: &BigInt) -> Option<()> {
        let left_bits = Self::bigint_bits(left)?;
        let right_bits = Self::bigint_bits(right)?;
        if left_bits > MAX_NUMERIC_VALUE_BITS || right_bits > MAX_NUMERIC_VALUE_BITS {
            return None;
        }
        let work = left_bits
            .max(1)
            .checked_mul(right_bits.max(1))?
            .checked_mul(8)?;
        self.spend_numeric_work(work)?;
        // Quotient, product, provisional/final remainders, and the possible
        // Euclidean-sign correction coexist transiently. Debit eight complete
        // operand-sized intermediates before any division/multiplication.
        let intermediate_bits = left_bits
            .checked_add(right_bits)?
            .checked_add(1)?
            .checked_mul(8)?;
        self.reserve_numeric_intermediate_bits(intermediate_bits)
    }

    fn clone_chars(&mut self, chars: &[char]) -> Option<Vec<char>> {
        self.reserve_string_chars(chars.len())?;
        Some(chars.to_vec())
    }

    fn eval_string(&mut self, term: TermId) -> Option<Vec<char>> {
        let value = self.eval(term)?;
        self.clone_chars(value.as_str()?)
    }

    /// Metered substring search. Each candidate window is charged for a full
    /// pattern comparison before the slice equality executes. The equality may
    /// short-circuit earlier, so this is conservative; it also closes the
    /// near-match case where one failed search previously performed
    /// `O(|haystack| * |needle|)` unchecked character comparisons.
    fn find_sub(
        &mut self,
        haystack: &[char],
        needle: &[char],
        from: usize,
    ) -> Option<Option<usize>> {
        if needle.is_empty() {
            return Some((from <= haystack.len()).then_some(from));
        }
        if needle.len() > haystack.len() {
            return Some(None);
        }
        let last = haystack.len().checked_sub(needle.len())?;
        if from > last {
            return Some(None);
        }
        for start in from..=last {
            self.spend_work(needle.len())?;
            if haystack[start..start + needle.len()] == needle[..] {
                return Some(Some(start));
            }
        }
        Some(None)
    }

    fn eval(&mut self, term: TermId) -> Option<Val> {
        if self.val_memo.contains_key(&term) {
            let cached_chars = self
                .val_memo
                .get(&term)
                .and_then(Option::as_ref)
                .and_then(Val::as_str)
                .map_or(0, <[char]>::len);
            let cached_numeric_bits = self
                .val_memo
                .get(&term)
                .and_then(Option::as_ref)
                .and_then(Val::as_int)
                .and_then(Self::bigint_bits)
                .unwrap_or(0);
            self.reserve_string_chars(cached_chars)?;
            self.reserve_numeric_bits(cached_numeric_bits)?;
            return self.val_memo.get(&term)?.clone();
        }
        self.spend()?;
        let result = self.eval_uncached(term);
        let memo_clone_chars = result
            .as_ref()
            .and_then(Val::as_str)
            .map_or(0, <[char]>::len);
        let memo_clone_numeric_bits = result
            .as_ref()
            .and_then(Val::as_int)
            .and_then(Self::bigint_bits)
            .unwrap_or(0);
        // Some integer-producing primitives (`str.len`, `str.indexof`, code
        // conversion) allocate only small results and need no operand prepass.
        // Charge every produced value here as a final backstop, then charge the
        // distinct retained memo clone below.
        self.reserve_numeric_bits(memo_clone_numeric_bits)?;
        self.reserve_string_chars(memo_clone_chars)?;
        self.reserve_numeric_bits(memo_clone_numeric_bits)?;
        self.val_memo.insert(term, result.clone());
        result
    }

    fn eval_uncached(&mut self, term: TermId) -> Option<Val> {
        match self.terms.get(term) {
            TermData::Const(Constant::Bool(b)) => Some(Val::Bool(*b)),
            TermData::Const(Constant::Int(i)) => {
                let bits = Self::bigint_bits(i)?;
                self.reserve_numeric_bits(bits)?;
                Some(Val::Int(i.clone()))
            }
            TermData::Const(Constant::String(s)) => {
                let chars = s.chars().count();
                self.reserve_string_chars(chars)?;
                Some(Val::Str(s.chars().collect()))
            }
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
        // Every operation evaluated here is a plain SMT-LIB symbol. An indexed
        // identifier with the same spelling is a different identity and must
        // not inherit the named builtin's semantics. Indexed regex repetition
        // is handled separately by `re_match_uncached` below.
        let Symbol::Named(name) = sym else {
            return None;
        };
        let name = name.as_str();
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
                    let value = self.eval(a)?;
                    if !self.values_equal(&value, &first)? {
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
                        if self.values_equal(&vals[i], &vals[j])? {
                            return Some(Val::Bool(false));
                        }
                    }
                }
                Some(Val::Bool(true))
            }

            // ---- integer arithmetic ----
            ("+", _) if !args.is_empty() => {
                let mut acc = self.eval_int(args[0])?;
                for &a in &args[1..] {
                    let value = self.eval_int(a)?;
                    acc = self.add_int(acc, &value)?;
                }
                Some(Val::Int(acc))
            }
            ("*", _) if !args.is_empty() => {
                let mut acc = self.eval_int(args[0])?;
                for &a in &args[1..] {
                    let value = self.eval_int(a)?;
                    acc = self.mul_int(acc, &value)?;
                }
                Some(Val::Int(acc))
            }
            ("-", 1) => {
                let value = self.eval_int(args[0])?;
                self.unary_int(&value)?;
                Some(Val::Int(-value))
            }
            ("-", _) if args.len() >= 2 => {
                let mut acc = self.eval_int(args[0])?;
                for &a in &args[1..] {
                    let value = self.eval_int(a)?;
                    acc = self.sub_int(acc, &value)?;
                }
                Some(Val::Int(acc))
            }
            ("abs", 1) => {
                let value = self.eval_int(args[0])?;
                self.unary_int(&value)?;
                Some(Val::Int(value.abs()))
            }
            ("div", 2) | ("mod", 2) => {
                let a = self.eval_int(args[0])?;
                let b = self.eval_int(args[1])?;
                if b.is_zero() {
                    // Under-specified in SMT-LIB: fail closed.
                    return None;
                }
                self.precharge_division(&a, &b)?;
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
                let a = self.eval_int(args[0])?;
                let b = self.eval_int(args[1])?;
                // SMT-LIB comparisons here are integer-only (Real constants
                // are not a `Val` variant, so they fail closed above).
                let comparison_work = Self::bigint_bits(&a)?.max(Self::bigint_bits(&b)?).max(1);
                self.spend_numeric_work(comparison_work)?;
                Some(Val::Bool(match name {
                    "<" => a < b,
                    "<=" => a <= b,
                    ">" => a > b,
                    _ => a >= b,
                }))
            }

            // ---- string operations (SMT-LIB 2.6 Unicode strings) ----
            ("str.++", _) if !args.is_empty() => {
                let mut pieces = Vec::with_capacity(args.len());
                let mut output_chars = 0_usize;
                for &a in args {
                    let piece = self.eval(a)?;
                    output_chars = output_chars.checked_add(piece.as_str()?.len())?;
                    pieces.push(piece);
                }
                self.reserve_string_chars(output_chars)?;
                let mut acc = Vec::with_capacity(output_chars);
                for piece in &pieces {
                    acc.extend_from_slice(piece.as_str()?);
                }
                Some(Val::Str(acc))
            }
            ("str.len", 1) => Some(Val::Int(BigInt::from(self.eval(args[0])?.as_str()?.len()))),
            ("str.at", 2) => {
                let s = self.eval_string(args[0])?;
                let i = self.eval_int(args[1])?;
                let idx = i.to_usize();
                let out = match idx {
                    Some(i) if i < s.len() => {
                        self.reserve_string_chars(1)?;
                        vec![s[i]]
                    }
                    _ => Vec::new(),
                };
                Some(Val::Str(out))
            }
            ("str.substr", 3) => {
                let s = self.eval_string(args[0])?;
                let i = self.eval_int(args[1])?;
                let n = self.eval_int(args[2])?;
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
                self.reserve_string_chars(take)?;
                Some(Val::Str(s[i..i + take].to_vec()))
            }
            ("str.contains", 2) => {
                let s = self.eval_string(args[0])?;
                let t = self.eval_string(args[1])?;
                Some(Val::Bool(self.find_sub(&s, &t, 0)?.is_some()))
            }
            ("str.prefixof", 2) => {
                let t = self.eval_string(args[0])?;
                let s = self.eval_string(args[1])?;
                self.spend_work(t.len())?;
                Some(Val::Bool(s.len() >= t.len() && s[..t.len()] == t[..]))
            }
            ("str.suffixof", 2) => {
                let t = self.eval_string(args[0])?;
                let s = self.eval_string(args[1])?;
                self.spend_work(t.len())?;
                Some(Val::Bool(
                    s.len() >= t.len() && s[s.len() - t.len()..] == t[..],
                ))
            }
            ("str.indexof", 3) => {
                let s = self.eval_string(args[0])?;
                let t = self.eval_string(args[1])?;
                let i = self.eval_int(args[2])?;
                let minus_one = || Val::Int(BigInt::from(-1i8));
                let Some(start) = i.to_usize() else {
                    return Some(minus_one());
                };
                if start > s.len() {
                    return Some(minus_one());
                }
                Some(match self.find_sub(&s, &t, start)? {
                    Some(pos) => Val::Int(BigInt::from(pos)),
                    None => minus_one(),
                })
            }
            ("str.replace", 3) => {
                let s = self.eval_string(args[0])?;
                let t = self.eval_string(args[1])?;
                let u = self.eval_string(args[2])?;
                if t.is_empty() {
                    let output_chars = u.len().checked_add(s.len())?;
                    self.reserve_string_chars(output_chars)?;
                    let mut out = Vec::with_capacity(output_chars);
                    out.extend_from_slice(&u);
                    out.extend_from_slice(&s);
                    return Some(Val::Str(out));
                }
                Some(Val::Str(match self.find_sub(&s, &t, 0)? {
                    Some(pos) => {
                        let output_chars = s.len().checked_sub(t.len())?.checked_add(u.len())?;
                        self.reserve_string_chars(output_chars)?;
                        let mut out = Vec::with_capacity(output_chars);
                        out.extend_from_slice(&s[..pos]);
                        out.extend_from_slice(&u);
                        out.extend_from_slice(&s[pos + t.len()..]);
                        out
                    }
                    None => s,
                }))
            }
            ("str.replace_all", 3) => {
                let s = self.eval_string(args[0])?;
                let t = self.eval_string(args[1])?;
                let u = self.eval_string(args[2])?;
                if t.is_empty() {
                    return Some(Val::Str(s));
                }

                // Compute and debit the exact output length before allocating
                // or extending the result. In particular, |s| one-character
                // matches replaced by an |u|-character string require
                // |s|*|u| chars; growing a Vec incrementally before this check
                // allowed a tiny proof payload to allocate gigabytes.
                let mut output_chars = 0_usize;
                let mut pos = 0usize;
                while let Some(hit) = self.find_sub(&s, &t, pos)? {
                    output_chars = output_chars.checked_add(hit.checked_sub(pos)?)?;
                    output_chars = output_chars.checked_add(u.len())?;
                    pos = hit.checked_add(t.len())?;
                }
                output_chars = output_chars.checked_add(s.len().checked_sub(pos)?)?;
                self.reserve_string_chars(output_chars)?;

                let mut out = Vec::with_capacity(output_chars);
                pos = 0;
                while let Some(hit) = self.find_sub(&s, &t, pos)? {
                    out.extend_from_slice(&s[pos..hit]);
                    out.extend_from_slice(&u);
                    pos = hit + t.len();
                }
                out.extend_from_slice(&s[pos..]);
                Some(Val::Str(out))
            }
            ("str.to_code", 1) => {
                let s = self.eval_string(args[0])?;
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
            ("str.from_code", 1) => {
                let n = self.eval_int(args[0])?;
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
                self.reserve_string_chars(1)?;
                Some(Val::Str(vec![c]))
            }
            ("str.to_int" | "str.to.int", 1) => {
                let s = self.eval_string(args[0])?;
                self.spend_work(s.len())?;
                if s.is_empty() || !s.iter().all(char::is_ascii_digit) {
                    return Some(Val::Int(BigInt::from(-1i8)));
                }
                if s.len() > MAX_NUMERIC_DECIMAL_DIGITS {
                    return None;
                }
                let numeric_work = s.len().checked_mul(s.len())?;
                self.spend_numeric_work(numeric_work.max(1))?;
                let result_bits = s.len().checked_mul(4)?;
                self.reserve_numeric_bits(result_bits)?;
                // `collect::<String>` allocates another UTF-8 buffer before
                // BigInt parsing; debit its worst-case bytes as char units.
                self.reserve_string_chars(s.len())?;
                let digits: String = s.iter().collect();
                Some(Val::Int(digits.parse::<BigInt>().ok()?))
            }
            ("str.from_int", 1) => {
                let n = self.eval_int(args[0])?;
                if n.is_negative() {
                    return Some(Val::Str(Vec::new()));
                }
                let bits = Self::bigint_bits(&n)?;
                if bits > MAX_NUMERIC_VALUE_BITS {
                    return None;
                }
                self.spend_numeric_work(bits.max(1).checked_mul(bits.max(1))?)?;
                // A non-negative integer has at most one decimal digit per
                // binary bit (plus the zero case). Debit the formatting String
                // before `to_string`, then the exact Vec<char> below.
                let formatted_chars = bits.max(1);
                self.reserve_string_chars(formatted_chars)?;
                let digits = n.to_string();
                let chars = digits.chars().count();
                self.reserve_string_chars(chars)?;
                Some(Val::Str(digits.chars().collect()))
            }
            ("str.is_digit", 1) => {
                let s = self.eval_string(args[0])?;
                self.spend_work(1)?;
                Some(Val::Bool(s.len() == 1 && s[0].is_ascii_digit()))
            }
            ("str.<", 2) => {
                let a = self.eval_string(args[0])?;
                let b = self.eval_string(args[1])?;
                self.spend_work(a.len().min(b.len()).checked_add(1)?)?;
                Some(Val::Bool(lex_lt(&a, &b)))
            }
            ("str.<=", 2) => {
                let a = self.eval_string(args[0])?;
                let b = self.eval_string(args[1])?;
                let comparison_work = a.len().min(b.len()).checked_mul(2)?.checked_add(1)?;
                self.spend_work(comparison_work)?;
                Some(Val::Bool(a == b || lex_lt(&a, &b)))
            }

            // ---- regular-expression membership ----
            ("str.in_re" | "str.in.re", 2) => {
                let s = self.eval_string(args[0])?;
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

        // `re.^` and `re.loop` are the only indexed regex constructors this
        // checker implements. Do not let any other indexed identifier inherit
        // the semantics of a same-spelled named constructor.
        if let Symbol::Indexed(name, indices) = &sym {
            return match (name.as_str(), args.len()) {
                ("re.loop", 1) => {
                    let [lo, hi] = indices.as_slice() else {
                        return None;
                    };
                    self.re_loop(r, args[0], u64::from(*lo), u64::from(*hi), i, j)
                }
                ("re.^", 1) => {
                    let [n] = indices.as_slice() else {
                        return None;
                    };
                    self.re_loop(r, args[0], u64::from(*n), u64::from(*n), i, j)
                }
                _ => None,
            };
        }
        let Symbol::Named(name) = &sym else {
            return None;
        };
        let name = name.as_str();
        match (name, args.len()) {
            ("re.none", 0) => Some(false),
            ("re.all", 0) => Some(true),
            ("re.allchar", 0) => Some(j == i + 1),
            ("re.range", 2) => {
                let lo = self.eval_string(args[0])?;
                let hi = self.eval_string(args[1])?;
                // `(re.range lo hi)` denotes the EMPTY language whenever an
                // endpoint is not a single character, or `lo > hi`.
                if lo.len() != 1 || hi.len() != 1 || lo[0] > hi[0] || j != i + 1 {
                    return Some(false);
                }
                let c = self.subject[i];
                Some(lo[0] <= c && c <= hi[0])
            }
            ("str.to_re" | "str.to.re", 1) => {
                let t = self.eval_string(args[0])?;
                self.spend_work(t.len())?;
                Some(self.subject[i..j] == t[..])
            }
            ("re.++", _) if !args.is_empty() => self.re_concat(r, &args, 0, i, j),
            ("re.union", _) if !args.is_empty() => {
                for &child in &args {
                    self.spend()?;
                    if self.re_match(child, i, j)? {
                        return Some(true);
                    }
                }
                Some(false)
            }
            ("re.inter", _) if !args.is_empty() => {
                for &child in &args {
                    self.spend()?;
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
                    self.spend()?;
                    if self.re_match(child, i, j)? {
                        return Some(false);
                    }
                }
                Some(true)
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
            self.spend()?;
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
            self.spend()?;
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
            self.spend()?;
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

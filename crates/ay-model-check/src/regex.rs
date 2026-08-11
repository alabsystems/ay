// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Independent, fail-closed SMT-LIB regular-language membership.
//!
//! This is deliberately separate from the search-side `ay-strings` matcher.
//! Its interval algorithm mirrors the strict proof checker's audited
//! `StringGroundEval` semantics: a successful result is exact, while an
//! unsupported term, invalid Unicode alphabet value, depth overflow, or work
//! budget exhaustion is an error and therefore becomes `CannotConfirm` at the
//! model gate.

use ay_core::kani_compat::DetHashMap;
use ay_core::{Sort, Symbol, TermData, TermId, TermStore};

use crate::MAX_EVAL_DEPTH;

/// Each interval-matcher memo miss spends one unit.  The matcher is
/// `O(|R| * |s|^2)` after memoization; this cap prevents a hostile regex from
/// turning the model gate into an unbounded second solver.
const MATCH_BUDGET: u64 = 4_000_000;

/// Decide whether `subject` belongs to `regex`.
///
/// `eval_string` independently evaluates String-sorted leaves embedded in the
/// regex (`str.to_re` and `re.range` endpoints) against the candidate model.
/// The callback never evaluates a RegLan term: all regex structure is handled
/// here, independently of the solver.
pub(crate) fn matches(
    terms: &TermStore,
    subject: &str,
    regex: TermId,
    entry_depth: usize,
    eval_string: impl FnMut(TermId) -> Result<String, String>,
) -> Result<bool, String> {
    if !matches!(terms.sort(regex), Sort::RegLan) {
        return Err("str.in_re second argument is not RegLan-sorted".to_string());
    }
    let subject = checked_chars(subject)?;
    let end = subject.len();
    Matcher {
        terms,
        subject,
        eval_string,
        budget: MATCH_BUDGET,
        re_memo: DetHashMap::default(),
        loop_memo: DetHashMap::default(),
    }
    .re_match(regex, 0, end, entry_depth)
}

fn checked_chars(text: &str) -> Result<Vec<char>, String> {
    let chars: Vec<char> = text.chars().collect();
    if chars.iter().any(|&c| u32::from(c) > 0x0002_FFFF) {
        return Err("string contains a code point outside the SMT-LIB alphabet".to_string());
    }
    Ok(chars)
}

/// SMT-LIB 2.6 Unicode Strings `str.replace_re` (`all == false`) and
/// `str.replace_re_all` (`all == true`).
///
/// # The clause being implemented
///
/// Both operators are defined by decomposing the subject as `s = x ++ w ++ z`
/// with `w` in `[[r]]`, taking `|x|` minimal and *then* `|w|` minimal — i.e.
/// the leftmost, then shortest, match:
///
/// * `(str.replace_re s r t)` is `x ++ t ++ z` for that decomposition, and `s`
///   when no decomposition exists. Its clause is not recursive and therefore
///   carries **no** `w != ""` side condition.
/// * `(str.replace_re_all s r t)` is `x ++ t ++ (str.replace_re_all z r t)`,
///   where the decomposition additionally requires `w != ""` — the side
///   condition that makes the recursion well-founded — and `s` when no such
///   decomposition exists.
///
/// # The deliberately fail-closed shape: a nullable regex
///
/// When `r` accepts the empty word the two clauses come apart, and that is
/// exactly the corner this gate refuses to adjudicate:
///
/// * `str.replace_re` has no `w != ""` condition, so the minimal-`|x|`,
///   then-minimal-`|w|` decomposition is `x = w = ""` and the operator
///   degenerates to prepending `t`;
/// * `str.replace_re_all` must skip that empty match and look for the leftmost
///   shortest NON-empty one instead, otherwise it silently becomes the
///   identity.
///
/// Both readings have been read the other way in the past (AY's own search-side
/// evaluator carried each of those defects at some point), so a nullable `r`
/// returns `Err` here and the gate reports `CannotConfirm`. That costs
/// completeness — a genuine `sat` over a nullable regex stays `unknown` — and
/// costs nothing else: the gate never assumes an assertion it cannot compute.
///
/// When `r` is NOT nullable the ambiguity does not arise at all: `"" ∉ [[r]]`
/// means every decomposition already has `w != ""`, so the two clauses select
/// the identical match and this function is exact for both operators.
///
/// `op` names the operator for the error message.
pub(crate) fn replace(
    terms: &TermStore,
    op: &str,
    subject: &str,
    regex: TermId,
    replacement: &str,
    all: bool,
    entry_depth: usize,
    eval_string: impl FnMut(TermId) -> Result<String, String>,
) -> Result<String, String> {
    if !matches!(terms.sort(regex), Sort::RegLan) {
        return Err(format!("{op}: second argument is not RegLan-sorted"));
    }
    // The replacement is spliced in verbatim, so hold it to the same alphabet
    // the matcher enforces on the subject rather than emitting a value this
    // crate would refuse to read back.
    checked_chars(replacement)?;
    let mut matcher = Matcher {
        terms,
        subject: checked_chars(subject)?,
        eval_string,
        budget: MATCH_BUDGET,
        re_memo: DetHashMap::default(),
        loop_memo: DetHashMap::default(),
    };

    // Nullability is position-independent for every operator the matcher
    // supports, so probing the empty window at 0 decides it for the whole
    // subject (including the empty subject).
    if matcher.re_match(regex, 0, 0, entry_depth)? {
        return Err(format!(
            "{op}: the regex accepts the empty word, whose replacement semantics this gate \
             deliberately declines to adjudicate"
        ));
    }

    let len = matcher.subject.len();
    let mut out = String::new();
    let mut at = 0usize;
    while let Some((start, end)) = matcher.find_from(regex, at, entry_depth)? {
        out.extend(matcher.subject[at..start].iter());
        out.push_str(replacement);
        // `end > start >= at` guarantees progress, so the loop terminates.
        at = end;
        if !all {
            break;
        }
    }
    out.extend(matcher.subject[at..len].iter());
    Ok(out)
}

struct Matcher<'a, F> {
    terms: &'a TermStore,
    subject: Vec<char>,
    eval_string: F,
    budget: u64,
    /// `(regex, start, end) -> membership`.
    re_memo: DetHashMap<(TermId, usize, usize), bool>,
    /// Shared recursion memo.  The discriminator fields use the same disjoint
    /// sentinel scheme as the strict proof checker:
    ///
    /// * concat: `(node, child_index, u64::MAX, i, j)`;
    /// * star: `(body, u64::MAX, u64::MAX, i, j)`;
    /// * bounded repetition: `(node, lo, hi, i, j)`.
    loop_memo: DetHashMap<(TermId, u64, u64, usize, usize), bool>,
}

impl<F> Matcher<'_, F>
where
    F: FnMut(TermId) -> Result<String, String>,
{
    fn spend(&mut self) -> Result<(), String> {
        if self.budget == 0 {
            return Err("regular-language model check exhausted its work budget".to_string());
        }
        self.budget -= 1;
        Ok(())
    }

    fn check_depth(depth: usize) -> Result<(), String> {
        if depth > MAX_EVAL_DEPTH {
            Err(format!(
                "regular-language model check exceeded recursion depth {MAX_EVAL_DEPTH}"
            ))
        } else {
            Ok(())
        }
    }

    fn eval_chars(&mut self, term: TermId) -> Result<Vec<char>, String> {
        let text = (self.eval_string)(term)?;
        checked_chars(&text)
    }

    /// The leftmost, then shortest, NON-EMPTY match of `regex` inside
    /// `subject[from..]`, as a half-open char-index window.
    ///
    /// Scanning `start` outward-in and `end` inward-out realizes the SMT-LIB
    /// `|x|`-minimal-then-`|w|`-minimal choice directly: the first window that
    /// matches is the one the clause names. Every probe goes through the
    /// memoized [`Self::re_match`], so the whole scan shares one work budget
    /// and exhausting it fails closed rather than returning a partial answer.
    fn find_from(
        &mut self,
        regex: TermId,
        from: usize,
        depth: usize,
    ) -> Result<Option<(usize, usize)>, String> {
        let len = self.subject.len();
        for start in from..len {
            for end in (start + 1)..=len {
                if self.re_match(regex, start, end, depth + 1)? {
                    return Ok(Some((start, end)));
                }
            }
        }
        Ok(None)
    }

    fn re_match(
        &mut self,
        regex: TermId,
        start: usize,
        end: usize,
        depth: usize,
    ) -> Result<bool, String> {
        Self::check_depth(depth)?;
        if let Some(&cached) = self.re_memo.get(&(regex, start, end)) {
            return Ok(cached);
        }
        self.spend()?;
        let result = self.re_match_uncached(regex, start, end, depth)?;
        self.re_memo.insert((regex, start, end), result);
        Ok(result)
    }

    #[allow(clippy::too_many_lines)]
    fn re_match_uncached(
        &mut self,
        regex: TermId,
        start: usize,
        end: usize,
        depth: usize,
    ) -> Result<bool, String> {
        let TermData::App(symbol, args) = self.terms.get(regex) else {
            return Err("regular-language term is not an application".to_string());
        };
        let symbol = symbol.clone();
        let args = args.clone();
        match (symbol.name(), args.len()) {
            ("re.none", 0) => Ok(false),
            ("re.all", 0) => Ok(true),
            ("re.allchar", 0) => Ok(end == start + 1),
            ("re.range", 2) => {
                let lo = self.eval_chars(args[0])?;
                let hi = self.eval_chars(args[1])?;
                // SMT-LIB defines malformed/reversed ranges as the empty
                // language, rather than leaving their result unspecified.
                if lo.len() != 1 || hi.len() != 1 || lo[0] > hi[0] || end != start + 1 {
                    return Ok(false);
                }
                let c = self.subject[start];
                Ok(lo[0] <= c && c <= hi[0])
            }
            ("str.to_re" | "str.to.re", 1) => {
                let singleton = self.eval_chars(args[0])?;
                Ok(self.subject[start..end] == singleton[..])
            }
            ("re.++", n) if n > 0 => self.re_concat(regex, &args, 0, start, end, depth + 1),
            ("re.union", n) if n > 0 => {
                for child in args {
                    if self.re_match(child, start, end, depth + 1)? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            ("re.inter", n) if n > 0 => {
                for child in args {
                    if !self.re_match(child, start, end, depth + 1)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            ("re.*", 1) => self.re_star(args[0], start, end, depth + 1),
            ("re.+", 1) => {
                if start == end {
                    self.re_match(args[0], start, end, depth + 1)
                } else {
                    self.re_star(args[0], start, end, depth + 1)
                }
            }
            ("re.opt", 1) => {
                if start == end {
                    Ok(true)
                } else {
                    self.re_match(args[0], start, end, depth + 1)
                }
            }
            ("re.comp", 1) => Ok(!self.re_match(args[0], start, end, depth + 1)?),
            ("re.diff", n) if n >= 2 => {
                // `re.diff` is left-associative: `a \\ b \\ c`.
                if !self.re_match(args[0], start, end, depth + 1)? {
                    return Ok(false);
                }
                for child in &args[1..] {
                    if self.re_match(*child, start, end, depth + 1)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            ("re.loop", 1) => {
                let Symbol::Indexed(_, indices) = &symbol else {
                    return Err("re.loop is missing its repetition indices".to_string());
                };
                let [lo, hi] = indices.as_slice() else {
                    return Err("re.loop requires exactly two repetition indices".to_string());
                };
                self.re_loop(
                    regex,
                    args[0],
                    u64::from(*lo),
                    u64::from(*hi),
                    start,
                    end,
                    depth + 1,
                )
            }
            ("re.^", 1) => {
                let Symbol::Indexed(_, indices) = &symbol else {
                    return Err("re.^ is missing its repetition index".to_string());
                };
                let [count] = indices.as_slice() else {
                    return Err("re.^ requires exactly one repetition index".to_string());
                };
                let count = u64::from(*count);
                self.re_loop(regex, args[0], count, count, start, end, depth + 1)
            }
            (name, _) => Err(format!("unsupported regular-language operator {name}")),
        }
    }

    /// Match `args[index..]` concatenated against `subject[start..end]`.
    fn re_concat(
        &mut self,
        node: TermId,
        args: &[TermId],
        index: usize,
        start: usize,
        end: usize,
        depth: usize,
    ) -> Result<bool, String> {
        Self::check_depth(depth)?;
        if index == args.len() {
            return Ok(start == end);
        }
        if index == args.len() - 1 {
            return self.re_match(args[index], start, end, depth + 1);
        }
        let index = u64::try_from(index)
            .map_err(|_| "regex concatenation index exceeds u64".to_string())?;
        let key = (node, index, u64::MAX, start, end);
        if let Some(&cached) = self.loop_memo.get(&key) {
            return Ok(cached);
        }
        self.spend()?;
        let child_index = usize::try_from(index)
            .map_err(|_| "regex concatenation index exceeds usize".to_string())?;
        let mut result = false;
        for split in start..=end {
            if self.re_match(args[child_index], start, split, depth + 1)?
                && self.re_concat(node, args, child_index + 1, split, end, depth + 1)?
            {
                result = true;
                break;
            }
        }
        self.loop_memo.insert(key, result);
        Ok(result)
    }

    /// Match `body*`. Empty factors can always be removed, so non-empty words
    /// need only be searched as decompositions into non-empty factors.
    fn re_star(
        &mut self,
        body: TermId,
        start: usize,
        end: usize,
        depth: usize,
    ) -> Result<bool, String> {
        Self::check_depth(depth)?;
        if start == end {
            return Ok(true);
        }
        let key = (body, u64::MAX, u64::MAX, start, end);
        if let Some(&cached) = self.loop_memo.get(&key) {
            return Ok(cached);
        }
        self.spend()?;
        // A pending false is a conservative cycle guard: a malformed cyclic
        // term store can lose completeness but can never read back a false
        // positive.
        self.loop_memo.insert(key, false);
        let mut result = false;
        for split in (start + 1)..=end {
            if self.re_match(body, start, split, depth + 1)?
                && self.re_star(body, split, end, depth + 1)?
            {
                result = true;
                break;
            }
        }
        self.loop_memo.insert(key, result);
        Ok(result)
    }

    #[allow(clippy::too_many_arguments)]
    fn re_loop(
        &mut self,
        node: TermId,
        body: TermId,
        lo: u64,
        hi: u64,
        start: usize,
        end: usize,
        depth: usize,
    ) -> Result<bool, String> {
        Self::check_depth(depth)?;
        if lo > hi {
            return Ok(false);
        }
        let word_len = u64::try_from(end - start)
            .map_err(|_| "regex subject length exceeds u64".to_string())?;
        let nullable = self.re_match(body, start, start, depth + 1)?;
        let (lo, hi) = if nullable {
            (0, hi.min(word_len.max(1)))
        } else {
            if lo > word_len {
                return Ok(false);
            }
            (lo, hi.min(word_len))
        };
        self.re_loop_exact(node, body, lo, hi, start, end, depth + 1)
    }

    #[allow(clippy::too_many_arguments)]
    fn re_loop_exact(
        &mut self,
        node: TermId,
        body: TermId,
        lo: u64,
        hi: u64,
        start: usize,
        end: usize,
        depth: usize,
    ) -> Result<bool, String> {
        Self::check_depth(depth)?;
        if lo == 0 && start == end {
            return Ok(true);
        }
        if hi == 0 {
            return Ok(false);
        }
        let key = (node, lo, hi, start, end);
        if let Some(&cached) = self.loop_memo.get(&key) {
            return Ok(cached);
        }
        self.spend()?;
        self.loop_memo.insert(key, false);
        let mut result = false;
        for split in start..=end {
            if self.re_match(body, start, split, depth + 1)?
                && self.re_loop_exact(
                    node,
                    body,
                    lo.saturating_sub(1),
                    hi - 1,
                    split,
                    end,
                    depth + 1,
                )?
            {
                result = true;
                break;
            }
        }
        self.loop_memo.insert(key, result);
        Ok(result)
    }
}

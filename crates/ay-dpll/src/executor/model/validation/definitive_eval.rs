// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Definitive-evaluation oracles for model validation.
//!
//! A **definitive-false** observation is a violation that cannot be a
//! model-extraction gap: when an assertion's arguments are structurally
//! ground in the current model and the theory evaluator returns
//! `Bool(false)`, that assertion is genuinely violated by the model.
//!
//! Returning `SAT` for such a model is unsound. Prior to this module, the
//! observation pipeline in `observation.rs` had thirteen SAT-fallback
//! sites that accepted "evaluator disagrees with SAT model" as evidence
//! of a model-extraction gap rather than as a violation. That pattern is
//! safe for *incomplete* theories (strings, FP, seq) but turns into a
//! false-SAT bug for theories where evaluation is authoritative when the
//! arguments are ground (#8779, #8729).
//!
//! The `DefinitiveEval` trait centralizes the "is this observation
//! authoritative?" decision as a per-theory oracle. Each oracle answers
//! two questions:
//!
//! 1. `structurally_ground(model, term)` — are all arguments of `term`
//!    fully resolved to concrete values in `model`?
//! 2. `definitive_false(model, term)` — does `term` evaluate to a genuine
//!    false under the model, with no possible model-extraction gap?
//!
//! When any oracle returns `definitive_false = true` for an assertion,
//! the global gate in `pipeline::finalize_sat_model_validation` rejects
//! the SAT result (degrades to `Unknown`) regardless of any downstream
//! SAT-fallback that might otherwise have rescued it.
//!
//! **Why this is a global gate**, not a local patch per theory: the
//! observation pipeline dispatches by theory flags, so a polarity bug in
//! one branch (e.g., strings, #8779) was repeated in a sibling branch
//! (arrays, #8729). Centralizing "definitive-false" as a trait means a
//! new theory is added by implementing one trait object, and the gate
//! checks every oracle before accepting SAT. Fixes root cause of
//! #8785/#8729/#8745 as one subsystem change.

use ay_core::{
    term::{Constant, TermData},
    Sort, TermId,
};

use crate::executor::model::{EvalValue, Executor, Model, EVAL_STACK_RED_ZONE, EVAL_STACK_SIZE};
use crate::term_helpers::is_pure_arithmetic_term;

/// True if `term` is, or contains, an integer-returning string conversion
/// (`str.to_int`, `str.to_code`, `str.indexof`, `str.len`). The model evaluator
/// computes these exactly (`eval_string.rs`), so a bridge equality/comparison
/// `(= x <conv>)` / `(< x <conv>)` whose two sides resolve to differing concrete
/// integers is a genuine violation that the string theory left unpinned
/// (#str-int-conv). `str.len` is included so a GROUND length mismatch such as
/// `(= (str.len (str.substr (str.substr "ab" 2 2) 1 0)) 4)` (= `(= 0 4)`) is
/// refuted even when the formula also has array-sourced string content that
/// routes it away from the plain string path (#mix-WS). When the length argument
/// is unconstrained the evaluator returns Unknown, so genuine `(= (str.len s) k)`
/// SAT cases are never rejected. Bounded walk.
fn term_mentions_string_int_conversion(executor: &Executor, term: TermId) -> bool {
    use ay_core::kani_compat::DetHashSet as HashSet;
    let mut visited: HashSet<TermId> = HashSet::default();
    let mut stack = vec![term];
    let mut budget = 256u32;
    while let Some(t) = stack.pop() {
        if budget == 0 {
            break;
        }
        budget -= 1;
        if !visited.insert(t) {
            continue;
        }
        if let TermData::App(sym, args) = executor.ctx.terms.get(t) {
            if matches!(
                sym.name(),
                "str.to_int" | "str.to.int" | "str.to_code" | "str.indexof" | "str.len"
            ) {
                return true;
            }
            stack.extend(args.iter().copied());
        }
    }
    false
}

/// Per-theory oracle that answers "is this assertion's observation
/// authoritative?"
///
/// Implementations encode the specific evaluator semantics for their
/// theory — see [`StringOracle`] and [`ArrayOracle`] below.
pub(super) trait DefinitiveEval {
    /// Name for diagnostic logging.
    fn name(&self) -> &'static str;

    /// Returns `true` when `term` is a predicate the oracle can evaluate
    /// definitively under `model`. Short-circuits the polarity check for
    /// terms outside the oracle's scope.
    fn is_applicable(&self, executor: &Executor, model: &Model, term: TermId) -> bool;

    /// Returns `true` iff `term` is structurally ground under `model` AND
    /// evaluates to `Bool(false)`. A `true` return is **definitive**:
    /// the SAT model genuinely violates this assertion.
    fn definitive_false(&self, executor: &Executor, model: &Model, term: TermId) -> bool;
}

/// Strings oracle — generalizes `string_eval_is_definitive_false`
/// (previously private in `observation.rs`). Ground `str.in_re`,
/// `str.contains`, `str.prefixof`, `str.suffixof` with fully-resolved
/// string arguments are authoritative under the model (#8779).
///
/// Also detects two nested patterns that propagate string violations
/// through the term graph without entering ay's equality DAG:
///
/// 1. `(= String String)` where both sides evaluate to distinct concrete
///    strings. The model evaluator's string concatenation is exact, so a
///    string-equality whose sides resolve to different literals is a
///    genuine violation.
/// 2. `(and ... <str-atom> ...)` where any conjunct is definitively
///    false AND the `and` evaluates to `false`. Covers the Tseitin
///    pattern `(= b_x_14 (and (= x_14 (str.++ ...)) ...))` where the
///    enclosing `and` short-circuits the string conjunct.
/// 3. `(= Bool Bool)` or `(= b_x <body>)` where `<body>` is definitively
///    false due to a nested string violation and the two sides evaluate
///    to different truth values. This is the Tseitin definitional
///    equality pattern produced by QF_SLIA formulas.
pub(super) struct StringOracle;

impl StringOracle {
    /// Base cases: ground `str.in_re`, `str.contains`, `str.prefixof`,
    /// `str.suffixof` where evaluation disagrees with the asserted
    /// polarity.
    fn base_definitive_false(executor: &Executor, model: &Model, term: TermId) -> bool {
        let TermData::App(sym, args) = executor.ctx.terms.get(term) else {
            return false;
        };

        match sym.name() {
            "str.in_re" | "str.in.re" if args.len() == 2 => {
                let EvalValue::String(s) = executor.evaluate_term(model, args[0]) else {
                    return false;
                };
                matches!(
                    ay_strings::ground_eval_in_re(&executor.ctx.terms, &s, args[1]),
                    Some(false),
                )
            }
            "str.contains" if args.len() == 2 => {
                let sv = executor.evaluate_term(model, args[0]);
                let tv = executor.evaluate_term(model, args[1]);
                if let (EvalValue::String(s), EvalValue::String(t)) = (&sv, &tv) {
                    return !s.contains(t.as_str());
                }
                // The haystack resolves to a concrete constant but the needle
                // does not (it has unresolved variable leaves, e.g. a partially
                // grounded `str.++`). `contains` is still definitively false
                // when no possible value of the needle can be a substring of
                // the haystack. Two sound necessary conditions on the needle's
                // concat structure (see `concat_needle_refutes_contains`):
                //   - length: the sum of the EXACT lengths of the needle's
                //     constant leaves already exceeds the haystack length, OR
                //   - content: some constant leaf of the needle is itself not a
                //     substring of the haystack (a constant block appears
                //     contiguously, so it must occur contiguously in any
                //     substring match).
                // Variable leaves contribute >= 0 chars of unknown content, so
                // both checks under-approximate and never reject a satisfiable
                // case. Symmetric haystack-unknown / needle-known cases are not
                // refutable (an unbounded haystack can contain anything), so we
                // only fire when the haystack is a concrete constant (#str-concat-needle).
                if let EvalValue::String(haystack) = &sv {
                    return Self::concat_needle_refutes_contains(
                        executor, model, haystack, args[1],
                    );
                }
                false
            }
            "str.prefixof" if args.len() == 2 => {
                let sv = executor.evaluate_term(model, args[0]);
                let tv = executor.evaluate_term(model, args[1]);
                if let (EvalValue::String(s), EvalValue::String(t)) = (&sv, &tv) {
                    return !t.starts_with(s.as_str());
                }
                // `prefixof(p, x)`: p (= args[0]) must be a prefix of x.
                // (a) When x resolves to a constant but p does not, p is
                //     definitely NOT a prefix if its forced minimum length
                //     exceeds |x| (#str-concat-needle).
                if let EvalValue::String(t) = &tv {
                    if let Some(min_len) = Self::concat_min_len(executor, model, args[0]) {
                        if min_len > t.chars().count() {
                            return true;
                        }
                    }
                }
                // (b) When p resolves to a constant but x is a concat with a
                //     resolved LEADING constant block, x's value starts with
                //     that block; if p disagrees with it on the overlapping
                //     prefix, p cannot be a prefix of x (#str-concat-boundary).
                if let EvalValue::String(p) = &sv {
                    if Self::concat_boundary_conflicts(executor, model, p, args[1], true) {
                        return true;
                    }
                }
                false
            }
            "str.suffixof" if args.len() == 2 => {
                let sv = executor.evaluate_term(model, args[0]);
                let tv = executor.evaluate_term(model, args[1]);
                if let (EvalValue::String(s), EvalValue::String(t)) = (&sv, &tv) {
                    return !t.ends_with(s.as_str());
                }
                // Mirror of prefixof.
                // (a) `suffixof(p, x)` is false when p's forced minimum length
                //     exceeds |x| (#str-concat-needle).
                if let EvalValue::String(t) = &tv {
                    if let Some(min_len) = Self::concat_min_len(executor, model, args[0]) {
                        if min_len > t.chars().count() {
                            return true;
                        }
                    }
                }
                // (b) p constant, x a concat with a resolved TRAILING constant
                //     block: x ends with that block; if p disagrees on the
                //     overlapping suffix, p cannot be a suffix (#str-concat-boundary).
                if let EvalValue::String(p) = &sv {
                    if Self::concat_boundary_conflicts(executor, model, p, args[1], false) {
                        return true;
                    }
                }
                false
            }
            // `str.is_digit(s)` — authoritative when `s` resolves to a concrete
            // string. SMT-LIB semantics (`ay_strings::eval::eval_str_is_digit`,
            // the SAME function the model evaluator uses at
            // `eval_string.rs:196`): true iff `|s| = 1` and the char is in
            // '0'..'9'. So an asserted `(str.is_digit s)` whose ground `s` is
            // empty or multi-character (or a non-digit char) is DEFINITIVELY
            // false — ground `str.is_digit` is decidable, so this is a genuine
            // model violation, never an extraction gap. This closes the
            // `falsesat_isdigit_replace_fromcode` family (a monolithic
            // `(and (ite ...) (str.is_digit (str.replace ... (str.from_code ...) ...)))`
            // where the `str.replace`/`str.from_code` evaluate exactly to a
            // multi-char string): the enclosing-`and` recursion below now finds
            // this conjunct definitively false instead of returning Unknown and
            // letting the wrong witness through (#str-isdigit-ground).
            "str.is_digit" if args.len() == 1 => {
                match executor.evaluate_term(model, args[0]) {
                    EvalValue::String(s) => !ay_strings::eval::eval_str_is_digit(&s),
                    // Arg not ground-resolved to a concrete string: cannot
                    // refute (fail-closed — never claim a violation we cannot
                    // decide).
                    _ => false,
                }
            }
            // (= String String) — authoritative when both sides resolve
            // to concrete string literals. The model's str.++ evaluator
            // yields exact concatenations, so disagreement here cannot be
            // a model-extraction gap.
            //
            // When only ONE side resolves to a concrete constant and the other
            // is a partially-grounded `str.++`, the equality is still
            // definitively false when the concat's FORCED minimum length
            // (sum of its resolved constant leaves; free leaves contribute
            // >= 0) already exceeds the constant's length: no assignment to the
            // free leaves can shrink the concat below that bound, so the two
            // sides can never be equal. This refutes disjuncts like
            // `(= "b" (str.++ "abc" s))` (|RHS| >= 3 > |"b"| = 1) over a free
            // `s`, which the unguided CEGAR loop leaves unpinned — closing the
            // false-SAT hole on disjunctions of length-mismatched word
            // equations (#str-disjunction-len). Sound: a strict length
            // inequality between the two sides is a genuine inequality.
            "=" if args.len() == 2 && *executor.ctx.terms.sort(args[0]) == Sort::String => {
                let av = executor.evaluate_term(model, args[0]);
                let bv = executor.evaluate_term(model, args[1]);
                match (&av, &bv) {
                    (EvalValue::String(a), EvalValue::String(b)) => a != b,
                    // One side concrete, the other a (partial) concat: refute on
                    // a forced length-lower-bound that exceeds the constant.
                    (EvalValue::String(a), _) => Self::concat_min_len(executor, model, args[1])
                        .is_some_and(|min_len| min_len > a.chars().count()),
                    (_, EvalValue::String(b)) => Self::concat_min_len(executor, model, args[0])
                        .is_some_and(|min_len| min_len > b.chars().count()),
                    _ => false,
                }
            }
            // (= Int Int) where a side is a string->int conversion
            // (str.to_int / str.to_code / str.indexof). The model evaluator
            // resolves these exactly, so when both sides reduce to concrete
            // rationals that disagree, the model genuinely violates the
            // equality — the integer result was never pinned by the string
            // theory (#str-int-conv).
            "=" if args.len() == 2
                && *executor.ctx.terms.sort(args[0]) == Sort::Int
                && (term_mentions_string_int_conversion(executor, args[0])
                    || term_mentions_string_int_conversion(executor, args[1])) =>
            {
                let EvalValue::Rational(a) = executor.evaluate_term(model, args[0]) else {
                    return false;
                };
                let EvalValue::Rational(b) = executor.evaluate_term(model, args[1]) else {
                    return false;
                };
                a != b
            }
            // (>=/<=/>/< Int Int) where a side is a string->int conversion
            // (str.to_int / str.to_code / str.indexof). Generalizes the `=` case
            // above to the order relations: the evaluator resolves the conversion
            // exactly (e.g. str.substr with a negative offset -> "" -> str.to_int
            // = -1) and the comparison via eval_arith_cmp, so a concrete
            // Bool(false) is a genuine violation the string theory never pinned
            // (#str-lia-WS). If a side does not resolve to a concrete value the
            // evaluator returns a non-Bool and this is false (fail-closed).
            ">=" | "<=" | ">" | "<"
                if args.len() == 2
                    && (term_mentions_string_int_conversion(executor, args[0])
                        || term_mentions_string_int_conversion(executor, args[1])) =>
            {
                matches!(executor.evaluate_term(model, term), EvalValue::Bool(false))
            }
            _ => false,
        }
    }

    /// Flatten a `str.++` term into its leaf operands (recursing through
    /// nested concats), then evaluate each leaf under `model`. Returns the
    /// list of `(leaf_term, evaluated_value)` pairs. A non-concat term is
    /// returned as a single leaf. Bounded by the term DAG (no cycles).
    fn concat_leaves(executor: &Executor, term: TermId, out: &mut Vec<TermId>) {
        match executor.ctx.terms.get(term) {
            TermData::App(sym, args) if sym.name() == "str.++" => {
                for &arg in args {
                    Self::concat_leaves(executor, arg, out);
                }
            }
            _ => out.push(term),
        }
    }

    /// Forced minimum length of a (possibly concat) string term under
    /// `model`: the sum of the EXACT character counts of every leaf that
    /// resolves to a concrete string constant. Leaves that do not resolve
    /// (unbound variables, opaque sub-terms) contribute the sound lower
    /// bound of 0. Returns `None` only when the term itself is not a string
    /// term at all (no leaves), so callers can bail.
    ///
    /// This is a SOUND under-approximation: the true value's length is
    /// always `>= concat_min_len`, so a refutation derived from it can
    /// never reject a satisfiable model.
    fn concat_min_len(executor: &Executor, model: &Model, term: TermId) -> Option<usize> {
        if *executor.ctx.terms.sort(term) != Sort::String {
            return None;
        }
        let mut leaves = Vec::new();
        Self::concat_leaves(executor, term, &mut leaves);
        let mut min_len = 0usize;
        for leaf in leaves {
            if let EvalValue::String(s) = executor.evaluate_term(model, leaf) {
                min_len += s.chars().count();
            }
            // Unresolved leaf: contributes >= 0 chars; add nothing.
        }
        Some(min_len)
    }

    /// Decide whether a constant `pattern` definitively cannot be a
    /// prefix (`from_start = true`) or suffix (`from_start = false`) of the
    /// concat `target` because `target`'s value has a FORCED boundary block
    /// that disagrees with `pattern`.
    ///
    /// `target`'s leading (resp. trailing) maximal run of resolved constant
    /// leaves forms a block the value definitely starts (resp. ends) with —
    /// no assignment to the inner free leaves can change those fixed boundary
    /// characters. The pattern must agree with that block on their overlap:
    ///   - prefix: `pattern` and `lead` must share a common prefix up to
    ///     `min(|pattern|, |lead|)`; a mismatch there is a definitive refutation.
    ///   - suffix: symmetric, comparing from the right against `trail`.
    /// A match on the overlap is NOT a refutation (the rest is undetermined).
    /// This is SOUND: it only fires on characters whose value is fixed by a
    /// boundary constant leaf (#str-concat-boundary).
    fn concat_boundary_conflicts(
        executor: &Executor,
        model: &Model,
        pattern: &str,
        target: TermId,
        from_start: bool,
    ) -> bool {
        if *executor.ctx.terms.sort(target) != Sort::String {
            return false;
        }
        let mut leaves = Vec::new();
        Self::concat_leaves(executor, target, &mut leaves);
        if !from_start {
            leaves.reverse();
        }
        // Accumulate the forced boundary block from the relevant end, stopping
        // at the first unresolved leaf.
        let mut block: Vec<char> = Vec::new();
        for leaf in leaves {
            match executor.evaluate_term(model, leaf) {
                EvalValue::String(s) => {
                    let chars: Vec<char> = s.chars().collect();
                    if from_start {
                        block.extend(chars);
                    } else {
                        // Building the trailing block right-to-left: prepend.
                        let mut next = chars;
                        next.extend(block.drain(..));
                        block = next;
                    }
                }
                _ => break,
            }
        }
        if block.is_empty() {
            return false;
        }
        let pat: Vec<char> = pattern.chars().collect();
        let overlap = pat.len().min(block.len());
        if from_start {
            // Compare leading `overlap` chars.
            pat[..overlap] != block[..overlap]
        } else {
            // Compare trailing `overlap` chars.
            pat[pat.len() - overlap..] != block[block.len() - overlap..]
        }
    }

    /// Decide whether `str.contains(haystack, needle)` is DEFINITIVELY false
    /// when `haystack` is a concrete constant string but `needle` is a
    /// partially-grounded `str.++` (some leaves are unresolved variables).
    ///
    /// `contains(H, N)` requires `N` to be a contiguous substring of `H`.
    /// The needle's structure is summarized as a sequence of FORCED constant
    /// blocks (maximal runs of adjacent resolved leaves) separated by free
    /// gaps. Each gap has a known minimum length (the sum of the free leaves'
    /// resolved lower bounds; 0 by default) but unknown content. `N` can be a
    /// substring of `H` only if the blocks occur in `H` IN ORDER and
    /// non-overlapping, with at least the gap minimum number of characters
    /// between consecutive blocks (and before the first / after the last).
    /// [`Self::blocks_placeable`] tests this feasibility with a greedy
    /// leftmost placement (optimal for feasibility). When NO placement exists,
    /// `contains` is impossible regardless of how the free leaves are filled,
    /// so we refute.
    ///
    /// This is a SOUND under-approximation: free leaves are treated as
    /// arbitrarily-fillable wildcards (only their minimum length matters), so
    /// a `true` return is a genuine violation and a satisfiable case is never
    /// rejected. It subsumes the simpler length bound (min total length > |H|)
    /// and per-block substring checks, and additionally handles ORDERED block
    /// constraints (e.g. `s1 ++ "abc" ++ s2 ++ "b"` over `"abcd"`: "abc" can
    /// only sit at offset 0, leaving no room for a later "b").
    fn concat_needle_refutes_contains(
        executor: &Executor,
        model: &Model,
        haystack: &str,
        needle: TermId,
    ) -> bool {
        if *executor.ctx.terms.sort(needle) != Sort::String {
            return false;
        }
        let mut leaves = Vec::new();
        Self::concat_leaves(executor, needle, &mut leaves);

        // Build forced constant blocks and the minimum gap (in chars) that
        // precedes each block / trails the last one. `gaps[i]` is the minimum
        // number of free characters required immediately before `blocks[i]`;
        // `trailing_gap` is the minimum required after the last block.
        let mut blocks: Vec<String> = Vec::new();
        let mut gaps: Vec<usize> = Vec::new();
        let mut have_const_leaf = false;
        let mut cur_block = String::new();
        let mut pending_gap = 0usize;
        for leaf in &leaves {
            match executor.evaluate_term(model, *leaf) {
                EvalValue::String(s) => {
                    have_const_leaf = true;
                    cur_block.push_str(&s);
                }
                _ => {
                    // Free leaf: closes any open block. Its minimum length is
                    // unknown to the model evaluator (treated as 0), so the gap
                    // stays at the sound lower bound of 0.
                    if !cur_block.is_empty() {
                        blocks.push(std::mem::take(&mut cur_block));
                        gaps.push(pending_gap);
                        pending_gap = 0;
                    }
                }
            }
        }
        if !cur_block.is_empty() {
            blocks.push(cur_block);
            gaps.push(pending_gap);
            pending_gap = 0;
        }
        let trailing_gap = pending_gap;

        // An all-free needle (no constant block) is satisfiable — every
        // haystack contains the empty string — so never refute it.
        if !have_const_leaf || blocks.is_empty() {
            return false;
        }
        !Self::blocks_placeable(haystack, &blocks, &gaps, trailing_gap)
    }

    /// Can the forced constant `blocks` be placed IN ORDER, non-overlapping,
    /// inside `haystack`, with at least `gaps[i]` free chars before `blocks[i]`
    /// and `trailing_gap` free chars after the last block? Greedy leftmost
    /// placement: place each block at the earliest position at or after the
    /// running cursor (advanced by the required gap) where it occurs. This is
    /// optimal for feasibility — committing each block as early as possible
    /// never forecloses a placement of the remaining blocks.
    fn blocks_placeable(
        haystack: &str,
        blocks: &[String],
        gaps: &[usize],
        trailing_gap: usize,
    ) -> bool {
        let hay: Vec<char> = haystack.chars().collect();
        let hlen = hay.len();
        let mut cursor = 0usize; // earliest char index the next block may start at
        for (i, block) in blocks.iter().enumerate() {
            let bchars: Vec<char> = block.chars().collect();
            let blen = bchars.len();
            let mut start = cursor.saturating_add(gaps[i]);
            // Find the earliest occurrence of `block` at or after `start`.
            loop {
                if start + blen > hlen {
                    return false; // No room for this block.
                }
                if hay[start..start + blen] == bchars[..] {
                    break;
                }
                start += 1;
            }
            cursor = start + blen;
        }
        // Ensure the trailing gap fits within the haystack.
        cursor + trailing_gap <= hlen
    }

    /// Recursive check with bounded depth. Descends through `and`,
    /// `(= Bool Bool)`, and top-level `Not` to detect Tseitin-wrapped
    /// string violations.
    ///
    /// A `(= Bool Bool)` is definitive-false when the two sides evaluate
    /// to different truth values AND at least one side has a nested
    /// definitive string violation driving its `false` evaluation. For
    /// symmetry with `and`, we also check the simpler case where an
    /// `and` has a definitively-false conjunct and the whole `and`
    /// evaluates to `false` (confirming that conjunct is the cause).
    ///
    /// Depth is capped to prevent runaway recursion on pathological
    /// formulas. The 16-level bound comfortably covers Tseitin encoded
    /// QF_SLIA formulas from CVE corpus / Stranger benchmarks.
    fn recursive_definitive_false(
        executor: &Executor,
        model: &Model,
        term: TermId,
        depth: u32,
    ) -> bool {
        if depth == 0 {
            return false;
        }
        stacker::maybe_grow(EVAL_STACK_RED_ZONE, EVAL_STACK_SIZE, || {
            Self::recursive_definitive_false_inner(executor, model, term, depth)
        })
    }

    fn recursive_definitive_false_inner(
        executor: &Executor,
        model: &Model,
        term: TermId,
        depth: u32,
    ) -> bool {
        if Self::base_definitive_false(executor, model, term) {
            return true;
        }
        match executor.ctx.terms.get(term) {
            // (and c1 c2 ...) — if the `and` evaluates to false AND any
            // conjunct is definitively false, the violation is real.
            TermData::App(sym, args) if sym.name() == "and" && !args.is_empty() => {
                // Must be evaluating to false at the top.
                if !matches!(executor.evaluate_term(model, term), EvalValue::Bool(false)) {
                    return false;
                }
                args.iter()
                    .any(|&c| Self::recursive_definitive_false(executor, model, c, depth - 1))
            }
            // (or d1 d2 ...) — an asserted disjunction is definitively
            // violated when NO disjunct can possibly be true: every disjunct
            // either evaluates to a concrete `Bool(false)` or is itself a
            // nested definitive-false string violation (e.g. a `str.contains`
            // over a constant haystack with a refuted concat needle). This is
            // sound: if no branch can be true, the `or` cannot be true.
            // Without this descent the model evaluator returns `Unknown` for
            // the whole `or` (an unresolved concat-needle disjunct masks the
            // refuted branch), letting a false-SAT escape (#str-concat-needle).
            //
            // SCOPE GUARD: only fire when at least one disjunct's falsity is
            // driven by a STRING-specific definitive violation (a disjunct that
            // does NOT already evaluate to a concrete `Bool(false)` but is
            // refuted by `recursive_definitive_false`). An `or` whose disjuncts
            // all simply evaluate to `false` is a generic boolean fact handled
            // by the model evaluator and the theory oracles for those disjuncts
            // (e.g. arrays/BV); the string oracle must NOT claim it, or it would
            // steal those oracles' diagnostic path (#11936).
            TermData::App(sym, args) if sym.name() == "or" && !args.is_empty() => {
                let mut all_unsatisfiable = true;
                let mut string_driven = false;
                for &d in args {
                    if matches!(executor.evaluate_term(model, d), EvalValue::Bool(false)) {
                        continue;
                    }
                    if Self::recursive_definitive_false(executor, model, d, depth - 1) {
                        string_driven = true;
                    } else {
                        all_unsatisfiable = false;
                        break;
                    }
                }
                all_unsatisfiable && string_driven
            }
            // (= Bool Bool) — Tseitin definitional pattern
            // `(= b_x <body>)`. Definitive-false when the sides disagree
            // AND one of them is driven false by a nested string
            // violation.
            TermData::App(sym, args)
                if sym.name() == "="
                    && args.len() == 2
                    && *executor.ctx.terms.sort(args[0]) == Sort::Bool
                    && *executor.ctx.terms.sort(args[1]) == Sort::Bool =>
            {
                let lhs = args[0];
                let rhs = args[1];
                let lhs_val = executor.evaluate_term(model, lhs);
                let rhs_val = executor.evaluate_term(model, rhs);
                match (&lhs_val, &rhs_val) {
                    (EvalValue::Bool(false), EvalValue::Bool(true)) => {
                        Self::recursive_definitive_false(executor, model, lhs, depth - 1)
                    }
                    (EvalValue::Bool(true), EvalValue::Bool(false)) => {
                        Self::recursive_definitive_false(executor, model, rhs, depth - 1)
                    }
                    _ => false,
                }
            }
            // (not x) — if x is definitively-true by evaluating to true
            // AND a ground string predicate that evaluates to true with a
            // positive polarity, the `not` wrapper would be violated. We
            // don't handle this path here (simpler case: observation.rs
            // already covers negated string predicates).
            TermData::Not(_) => false,
            _ => false,
        }
    }
}

impl DefinitiveEval for StringOracle {
    fn name(&self) -> &'static str {
        "strings"
    }

    fn is_applicable(&self, executor: &Executor, _model: &Model, term: TermId) -> bool {
        match executor.ctx.terms.get(term) {
            TermData::App(sym, args) => match (sym.name(), args.len()) {
                ("str.in_re" | "str.in.re", 2)
                | ("str.contains", 2)
                | ("str.prefixof", 2)
                | ("str.suffixof", 2) => true,
                // (= String String) — applies when both operands carry
                // the String sort. (= Bool Bool) — Tseitin definitional
                // pattern; recursive_definitive_false descends into
                // nested string violations.
                ("=", 2) => {
                    let s = executor.ctx.terms.sort(args[0]);
                    *s == Sort::String
                        || *s == Sort::Bool
                        || (*s == Sort::Int
                            && (term_mentions_string_int_conversion(executor, args[0])
                                || term_mentions_string_int_conversion(executor, args[1])))
                }
                // (>=/<=/>/< Int Int) where a side is a string->int conversion
                // — the order-relation analog of the `=` case (#str-lia-WS).
                (">=" | "<=" | ">" | "<", 2)
                    if term_mentions_string_int_conversion(executor, args[0])
                        || term_mentions_string_int_conversion(executor, args[1]) =>
                {
                    true
                }
                // (and ...) / (or ...) applicable because
                // recursive_definitive_false handles nested string violations
                // inside them (an `or` is violated when every disjunct is
                // false / definitively-false).
                ("and" | "or", _) if !args.is_empty() => true,
                _ => false,
            },
            _ => false,
        }
    }

    fn definitive_false(&self, executor: &Executor, model: &Model, term: TermId) -> bool {
        Self::recursive_definitive_false(executor, model, term, 16)
    }
}

/// Arrays oracle — detects false-SAT models where the model evaluator
/// resolves `(= (select <store-chain> k) v)` or `(not (= (select a k)
/// (select b k)))` to `Bool(false)` with fully concrete arguments
/// (#8729).
///
/// **Definitive condition**: the assertion (or its negation under a
/// top-level `not`) is an equality whose sides are both numeric EvalValues
/// of the same theory (Rational/BigInt, BitVec, or Element). If the
/// evaluator returns `Bool(false)`, the model is violating the assertion
/// — no array-model gap can rescue it, because the evaluator already
/// resolved the store chain to a concrete value.
///
/// The array theory SAT-fallback in `observation.rs` currently accepts
/// such cases as "delegated" verification when a BV or array model is
/// present, allowing models like `a = b = const(0)` to validate
/// `(not (= (select a 0) (select b 0)))`. That is the polarity bug this
/// oracle closes.
pub(super) struct ArrayOracle;

impl ArrayOracle {
    fn is_concrete_theory_value(value: &EvalValue) -> bool {
        matches!(
            value,
            EvalValue::Rational(_)
                | EvalValue::BitVec { .. }
                | EvalValue::Element(_)
                | EvalValue::Bool(_)
        )
    }

    /// Check whether `term` is an equality/distinct predicate over fully
    /// resolved theory values under `model`.
    fn is_ground_predicate(executor: &Executor, model: &Model, term: TermId) -> bool {
        let TermData::App(sym, args) = executor.ctx.terms.get(term) else {
            return false;
        };

        match sym.name() {
            "=" if args.len() == 2 => {
                let lhs = executor.evaluate_term(model, args[0]);
                let rhs = executor.evaluate_term(model, args[1]);
                Self::is_concrete_theory_value(&lhs) && Self::is_concrete_theory_value(&rhs)
            }
            "distinct" if args.len() >= 2 => args
                .iter()
                .map(|&arg| executor.evaluate_term(model, arg))
                .all(|value| Self::is_concrete_theory_value(&value)),
            _ => false,
        }
    }

    /// Unwrap a single top-level negation. Returns the inner term and
    /// the negated-polarity flag. In ay-core, negation is represented by
    /// the dedicated `TermData::Not` variant rather than an `App("not",
    /// ...)` node.
    fn strip_top_not(executor: &Executor, term: TermId) -> (TermId, bool) {
        match executor.ctx.terms.get(term) {
            TermData::Not(inner) => (*inner, true),
            TermData::App(sym, args) if sym.name() == "not" && args.len() == 1 => (args[0], true),
            _ => (term, false),
        }
    }

    fn is_select_app(executor: &Executor, term: TermId) -> bool {
        matches!(
            executor.ctx.terms.get(term),
            TermData::App(sym, _) if sym.name() == "select"
        )
    }

    /// Check whether `term` is a direct array observation. The oracle is
    /// authoritative for assertions whose top-level atom compares a concrete
    /// array read, e.g. `(= (select A k) v)` or `(not (= (select A k)
    /// (select B k)))`.
    ///
    /// Do not classify arbitrary BV/Bool wrappers containing selects as
    /// definitive. QF_ABV try3/try5 benchmarks encode a whole control-flow
    /// formula as `#b1 = (bvand ... (ite (= (select ...) ...) #b1 #b0) ...)`;
    /// a false evaluation there can be a model-completion gap in a nested
    /// array read, not a proof that the candidate model violates the original
    /// formula.
    fn is_direct_array_observation(executor: &Executor, term: TermId) -> bool {
        let TermData::App(sym, args) = executor.ctx.terms.get(term) else {
            return false;
        };
        match sym.name() {
            "=" if args.len() == 2 => args.iter().any(|&arg| Self::is_select_app(executor, arg)),
            "distinct" if args.len() >= 2 => {
                args.iter().any(|&arg| Self::is_select_app(executor, arg))
            }
            _ => false,
        }
    }

    fn is_array_var(executor: &Executor, term: TermId) -> bool {
        matches!(executor.ctx.terms.get(term), TermData::Var(_, _))
            && matches!(executor.ctx.terms.sort(term), Sort::Array(_))
    }

    /// Recognize an equality between two array *variables*, e.g. `(= a_12 a_6)`.
    ///
    /// We deliberately restrict to variable-vs-variable equalities (not
    /// `var = store(...)` definitions). A store-definition assertion can
    /// normalize to "different" purely because the model's reconstruction of
    /// the defined variable is partial — that occurs even for genuinely-SAT
    /// formulas and must NOT be treated as a refutation. Two array variables,
    /// by contrast, each carry the array theory's OWN committed interpretation;
    /// if the theory asserts them equal while those interpretations provably
    /// differ at a concrete index, the candidate model is internally
    /// inconsistent (the store-congruence-over-arithmetic-index spurious-model
    /// pattern).
    fn array_var_equality(executor: &Executor, term: TermId) -> Option<(TermId, TermId)> {
        let TermData::App(sym, args) = executor.ctx.terms.get(term) else {
            return None;
        };
        if sym.name() != "=" || args.len() != 2 {
            return None;
        }
        if Self::is_array_var(executor, args[0]) && Self::is_array_var(executor, args[1]) {
            Some((args[0], args[1]))
        } else {
            None
        }
    }

    /// Model-free read-over-write refutation of a NEGATED equality
    /// `(not (= V (select (store A i v) j)))` (either argument order of the
    /// outer `=`). By McCarthy's select-over-store axiom,
    /// `(select (store A i v) j) = (ite (= i j) v (select A j))`, so the inner
    /// read is forced to `V` for EVERY model when BOTH:
    ///   * `v` is provably equal to `V` (here: both structurally the empty
    ///     sequence — the same-index branch yields `v = V`), AND
    ///   * the assertion set independently pins `(select A j) = V` via a
    ///     top-level `(= V (select A j))` / `(= (select A j) V)` with the SAME
    ///     base array `A` and index term `j` (the different-index branch yields
    ///     `select(A,j) = V`).
    /// Both branches of the `ite` then equal `V`, so the inner read equals `V`
    /// unconditionally and the negated equality is definitively false. This is
    /// the McCarthy refutation specialized to the empty-sequence element value
    /// that the numeric ArrayOracle skips (its `is_concrete_theory_value` does
    /// not cover `EvalValue::Seq`), closing the Seq-valued read-over-write
    /// wrong-SAT (#array-row-seq). Sound: every recognised case is unsat in
    /// SMT-LIB for ANY model, so it can only degrade a genuine SAT to Unknown,
    /// never flip a SAT to UNSAT.
    fn select_over_store_empty_row_violated(executor: &Executor, term: TermId) -> bool {
        let TermData::Not(inner) = executor.ctx.terms.get(term) else {
            return false;
        };
        let TermData::App(sym, args) = executor.ctx.terms.get(*inner) else {
            return false;
        };
        if sym.name() != "=" || args.len() != 2 {
            return false;
        }
        // Identify the (V, select-of-store) split (either order).
        let try_split = |v: TermId, sel: TermId| -> Option<(TermId, TermId, TermId, TermId)> {
            // sel must be `(select (store base i stored) j)`.
            let TermData::App(ssym, sargs) = executor.ctx.terms.get(sel) else {
                return None;
            };
            if ssym.name() != "select" || sargs.len() != 2 {
                return None;
            }
            let (store_term, j) = (sargs[0], sargs[1]);
            let TermData::App(stsym, stargs) = executor.ctx.terms.get(store_term) else {
                return None;
            };
            if stsym.name() != "store" || stargs.len() != 3 {
                return None;
            }
            let (base, _i, stored) = (stargs[0], stargs[1], stargs[2]);
            // The stored value must provably equal V (same-index branch). We
            // only recognise the empty-sequence case (both structurally empty),
            // which is what the numeric oracle cannot evaluate.
            if !(SeqOracle::seq_struct_empty(executor, v, 64)
                && SeqOracle::seq_struct_empty(executor, stored, 64))
            {
                return None;
            }
            Some((v, base, j, stored))
        };
        let Some((v, base, j, _stored)) =
            try_split(args[0], args[1]).or_else(|| try_split(args[1], args[0]))
        else {
            return false;
        };
        // The different-index branch requires an independent pin
        // `(select base j) = V` in the assertions (V structurally empty).
        for &a in &executor.ctx.assertions {
            let TermData::App(asym, aargs) = executor.ctx.terms.get(a) else {
                continue;
            };
            if asym.name() != "=" || aargs.len() != 2 {
                continue;
            }
            let pins = |sel: TermId, val: TermId| -> bool {
                let TermData::App(ssym, sargs) = executor.ctx.terms.get(sel) else {
                    return false;
                };
                ssym.name() == "select"
                    && sargs.len() == 2
                    && sargs[0] == base
                    && sargs[1] == j
                    && SeqOracle::seq_struct_empty(executor, val, 64)
            };
            // V is empty; require the pinned select value also structurally
            // empty so it matches V regardless of the concrete empty form.
            let _ = v;
            if pins(aargs[0], aargs[1]) || pins(aargs[1], aargs[0]) {
                return true;
            }
        }
        false
    }

    /// Decide a (possibly negated) array-variable equality against the model by
    /// fully reconstructing BOTH operands and comparing structurally.
    ///
    /// Returns `true` only when the assertion is definitively VIOLATED:
    /// * positive `(= A B)` where A and B provably differ, or
    /// * negated `(not (= A B))` where A and B are provably identical.
    ///
    /// `compare_array_var_definitions` yields `Some(_)` only when BOTH sides
    /// normalize fully (partial reconstruction yields `None`), so we never
    /// reject on incomplete evidence. Because the decision rests entirely on a
    /// *full* normalization of both operands, it is sound even with no active
    /// arithmetic model — e.g. QF_ABV `(= f g)` where `f = const(1)` and
    /// `g = const(2)` reconstruct to the distinct normal forms `(1, [])` and
    /// `(2, [])`, refuting equality by extensionality. We therefore do not gate
    /// this refutation on the presence of an LIA/LRA model; the
    /// `Some(_)`-only-on-full-normalization contract is what guarantees
    /// soundness, including for the store-congruence-over-arithmetic-index
    /// spurious-model pattern.
    ///
    /// We resolve each array variable through its definitional equality in the
    /// assertion set (`(= v <array-expr>)`) when the variable has no
    /// reconstructed `array_model` entry, since in QF_ABV with Int indices the
    /// const-array interpretation lives only in the assertions, not in a
    /// completed array model.
    fn array_var_equality_violated(executor: &Executor, model: &Model, term: TermId) -> bool {
        let (inner, negated) = Self::strip_top_not(executor, term);
        let Some((lhs, rhs)) = Self::array_var_equality(executor, inner) else {
            return false;
        };
        match executor.compare_array_var_definitions(model, lhs, rhs) {
            Some(true) => negated,   // (not (= A B)) violated when A == B
            Some(false) => !negated, // (= A B) violated when A != B
            None => false,           // partial reconstruction: not definitive
        }
    }

    /// Any equality between two Array-sorted terms (store chains included, not
    /// just variables), for the same-symbolic-base pointwise refutation.
    fn array_sorted_equality(executor: &Executor, term: TermId) -> Option<(TermId, TermId)> {
        let TermData::App(sym, args) = executor.ctx.terms.get(term) else {
            return None;
        };
        if sym.name() != "=" || args.len() != 2 {
            return None;
        }
        if matches!(executor.ctx.terms.sort(args[0]), Sort::Array(_))
            && matches!(executor.ctx.terms.sort(args[1]), Sort::Array(_))
        {
            Some((args[0], args[1]))
        } else {
            None
        }
    }

    /// The free-base-read pin of one positive asserted equality: `(= v (select
    /// ...))` (either orientation) where the select resolves through
    /// store-chain peeling + definitional equalities to an UNCONSTRAINED read
    /// `(base_var, index_key)` of a free base array, and the other operand
    /// evaluates to a concrete model value. Returns `(base, index_key,
    /// pinned_value)`.
    fn free_base_read_pin(
        executor: &Executor,
        model: &Model,
        eq_term: TermId,
    ) -> Option<(TermId, String, String)> {
        let TermData::App(sym, args) = executor.ctx.terms.get(eq_term) else {
            return None;
        };
        if sym.name() != "=" || args.len() != 2 {
            return None;
        }
        for (sel_side, val_side) in [(args[0], args[1]), (args[1], args[0])] {
            let Some((base, idx_key)) = executor.resolve_free_base_read(model, sel_side) else {
                continue;
            };
            let val = executor.evaluate_term(model, val_side);
            if matches!(val, EvalValue::Unknown) {
                continue;
            }
            let val_key = executor.format_eval_value(&val, val_side);
            return Some((base, idx_key, val_key));
        }
        None
    }

    /// Conflicting free-base-read pins (#qf-ax-swap-sf-false-sat): `term` is a
    /// positive top-level equality pinning a free base read `(base, i)` to a
    /// concrete value, and ANOTHER positive top-level assertion pins the SAME
    /// read to a DIFFERENT concrete value. `select(base, i)` denotes ONE value
    /// in any model, so no completion of the free base satisfies both — a
    /// definitive internal inconsistency of the candidate model (never a
    /// statement about formula satisfiability; enforcement downgrades SAT to
    /// Unknown, fail-closed).
    fn conflicting_free_base_read_pins_violated(
        executor: &Executor,
        model: &Model,
        term: TermId,
    ) -> bool {
        let (inner, negated) = Self::strip_top_not(executor, term);
        if negated {
            return false;
        }
        let Some((base, idx_key, val)) = Self::free_base_read_pin(executor, model, inner) else {
            return false;
        };
        for &other in &executor.ctx.assertions {
            if other == term {
                continue;
            }
            let (o_inner, o_negated) = Self::strip_top_not(executor, other);
            if o_negated {
                continue;
            }
            if let Some((o_base, o_idx, o_val)) = Self::free_base_read_pin(executor, model, o_inner)
            {
                if o_base == base && o_idx == idx_key && o_val != val {
                    tracing::debug!(
                        ?base,
                        idx = %idx_key,
                        v1 = %val,
                        v2 = %o_val,
                        "conflicting free-base-read pins: candidate model invalid \
                         (#qf-ax-swap-sf-false-sat)"
                    );
                    return true;
                }
            }
        }
        false
    }

    /// Same-symbolic-base store-chain refutation (#qf-ax-swap-false-sat): the
    /// SMT-COMP QF_AX swap/storeinv `_np_nf_` shape asserts `(not (= C1 C2))`
    /// where C1/C2 are nested store chains over one shared free base array.
    /// `compare_same_base_store_chains` compares them pointwise under the
    /// model with symbolic base reads, so a `Some(_)` verdict holds under
    /// EVERY completion of the free base — a definitive result with no
    /// SAT-model circularity. `Some(true)` refutes the negated equality;
    /// `Some(false)` refutes the positive one.
    fn store_chain_equality_violated(executor: &Executor, model: &Model, term: TermId) -> bool {
        let (inner, negated) = Self::strip_top_not(executor, term);
        let Some((lhs, rhs)) = Self::array_sorted_equality(executor, inner) else {
            return false;
        };
        match executor.compare_same_base_store_chains(model, lhs, rhs) {
            // (not (= C1 C2)) violated when C1 == C2 pointwise: equal reads
            // hold under EVERY completion, so the rejection is
            // completion-robust. This is the direction that kills the QF_AX
            // swap/storeinv false-SATs.
            Some(true) => negated,
            // Some(false) (chains differ at a written index) is NOT used to
            // reject a positive `(= C1 C2)`: the differing index/value reads
            // may be COMPLETION artifacts for otherwise-unconstrained
            // variables (the #8871 shadowed-store shape materializes i != j
            // even though choosing j = i satisfies the formula), so rejecting
            // would degrade genuinely-sat instances. The theory layer, not
            // the model gate, owns that arrangement split.
            _ => false,
        }
    }

    /// The cardinality of a FINITE array index sort, or `None` for infinite /
    /// too-large domains. Bool has 2 inhabitants; `(_ BitVec w)` has `2^w` (only
    /// for small `w`); an all-nullary (enum) datatype has one inhabitant per
    /// constructor. Used by the finite-index extensionality refutation below.
    fn finite_index_domain_size(executor: &Executor, index_sort: &Sort) -> Option<u64> {
        // Cap the enumerated domain so a wide BitVec index does not blow up.
        const MAX_FINITE_INDEX_DOMAIN: u64 = 256;
        match index_sort {
            Sort::Bool => Some(2),
            Sort::BitVec(bv) if bv.width >= 1 && bv.width <= 8 => Some(1u64 << bv.width),
            other => {
                let n = executor.enum_datatype_constructor_count(other)?;
                if (n as u64) <= MAX_FINITE_INDEX_DOMAIN && n >= 1 {
                    Some(n as u64)
                } else {
                    None
                }
            }
        }
    }

    /// Collect the model-evaluated `(index_value, element_value)` pairs for
    /// every `(select <arr> <idx>)` term ON `arr` that exists ANYWHERE in the
    /// term store, when both the index AND the element resolve to a concrete
    /// value under `model`. Pairs with an `Unknown` index or element are skipped
    /// (not definitive), and only the first value observed for each distinct
    /// index value is kept.
    ///
    /// Scanning the whole term store (rather than just the current assertion
    /// set) is deliberate: preprocessing/abstraction can replace `(select a k)`
    /// in the assertions with an opaque value variable, but the original select
    /// term still lives in the store and the model still evaluates it correctly
    /// (the array's interpretation is committed). The store is finite, so this
    /// is a bounded linear scan.
    pub(in crate::executor) fn concrete_select_pairs(
        executor: &Executor,
        model: &Model,
        arr: TermId,
    ) -> Vec<(EvalValue, EvalValue)> {
        let mut out: Vec<(EvalValue, EvalValue)> = Vec::new();
        for tid in executor.ctx.terms.term_ids() {
            let TermData::App(sym, args) = executor.ctx.terms.get(tid) else {
                continue;
            };
            if sym.name() != "select" || args.len() != 2 || args[0] != arr {
                continue;
            }
            let idx = args[1];
            let idx_val = executor.evaluate_term(model, idx);
            // The datatype-valued select itself usually evaluates to `Unknown`
            // (the bit-blaster never materializes a datatype value into the model
            // and the array layer carries no element for it). Its value is pinned
            // only by an asserted equality `(= (select arr idx) <ctor>)`, so fall
            // back to the same asserted-equality resolution that `(get-value ...)`
            // uses (`extract_value_from_asserted_equalities`).
            let elem_val = match executor.evaluate_term(model, tid) {
                EvalValue::Unknown => executor
                    .extract_value_from_asserted_equalities(model, tid)
                    .unwrap_or(EvalValue::Unknown),
                v => v,
            };
            if matches!(idx_val, EvalValue::Unknown) || matches!(elem_val, EvalValue::Unknown) {
                continue;
            }
            if !out.iter().any(|(i, _)| *i == idx_val) {
                out.push((idx_val, elem_val));
            }
        }
        out
    }

    /// Finite-index array extensionality, evaluated against the candidate model.
    ///
    /// For a (possibly negated) equality between two array *variables* whose
    /// index sort is a FINITE domain (Bool / small BitVec / enum datatype), the
    /// arrays are equal iff they agree at every index. We reconstruct each
    /// array's value at the indices pinned by `(select arr idx)` sub-terms in
    /// the assertions, evaluated under the model:
    ///
    /// * if the two arrays have concrete values at a SHARED index that DIFFER,
    ///   they are provably distinct → `(= a b)` is violated (any `(not (= a b))`
    ///   is satisfied);
    /// * if both arrays have a concrete value at EVERY index of the (finite)
    ///   domain and all agree, they are provably equal → `(not (= a b))` is
    ///   violated.
    ///
    /// This is exactly the extensionality axiom over a finite domain, decided by
    /// the model's own select valuations, so it is sound: it only refutes a
    /// candidate model that is internally inconsistent with array
    /// extensionality. Returns `true` only when the assertion is definitively
    /// VIOLATED. (#dt-array-bv-finite-index wrong-SAT — an `(Array (_ BitVec 1)
    /// C)` with both arrays' selects pinned to equal datatype constructors was
    /// wrongly SAT because the AUFBV bit-blasting path never reconciled the
    /// datatype-valued select congruence into the array-equality literal.)
    fn finite_index_array_equality_violated(
        executor: &Executor,
        model: &Model,
        term: TermId,
    ) -> bool {
        let (inner, negated) = Self::strip_top_not(executor, term);
        let Some((lhs, rhs)) = Self::array_var_equality(executor, inner) else {
            return false;
        };
        let Sort::Array(arr_sort) = executor.ctx.terms.sort(lhs).clone() else {
            return false;
        };
        let Some(domain_size) = Self::finite_index_domain_size(executor, &arr_sort.index_sort)
        else {
            return false;
        };

        let lhs_pairs = Self::concrete_select_pairs(executor, model, lhs);
        let rhs_pairs = Self::concrete_select_pairs(executor, model, rhs);

        // Any shared concrete index where the element values differ proves the
        // arrays are distinct — sound regardless of how much of the domain is
        // covered.
        for (li, lv) in &lhs_pairs {
            if let Some((_, rv)) = rhs_pairs.iter().find(|(ri, _)| ri == li) {
                if lv != rv {
                    // arrays provably DIFFER: `(= a b)` violated; `(not (= a b))` ok.
                    return !negated;
                }
            }
        }

        // Provably EQUAL only when BOTH arrays have a concrete value at EVERY
        // index of the finite domain and every shared index agrees (the loop
        // above already established no shared index disagrees). Full coverage of
        // the domain by both arrays means they agree everywhere.
        let lhs_covers_domain = (lhs_pairs.len() as u64) >= domain_size;
        let rhs_covers_domain = (rhs_pairs.len() as u64) >= domain_size;
        if lhs_covers_domain && rhs_covers_domain {
            // Every shared index agrees and both cover the whole domain ⇒ for
            // every domain index both arrays have a concrete value and they
            // match. arrays provably EQUAL: `(not (= a b))` violated.
            return negated;
        }

        false
    }
}

impl DefinitiveEval for ArrayOracle {
    fn name(&self) -> &'static str {
        "arrays"
    }

    fn is_applicable(&self, executor: &Executor, _model: &Model, term: TermId) -> bool {
        // Applicable when the (possibly negated) top-level directly observes a
        // select, OR when it is an equality between two array variables (handled
        // in `definitive_false`). Nested select occurrences inside BV/Bool
        // encodings remain on the normal incomplete-model path instead of being
        // treated as hard model violations.
        let (inner, _) = Self::strip_top_not(executor, term);
        Self::is_direct_array_observation(executor, inner)
            || Self::array_var_equality(executor, inner).is_some()
            || Self::array_sorted_equality(executor, inner).is_some()
            || Self::select_over_store_empty_row_violated(executor, term)
    }

    fn definitive_false(&self, executor: &Executor, model: &Model, term: TermId) -> bool {
        // Read-over-write refutation for Seq-valued (empty-element) arrays — the
        // numeric oracle's `is_concrete_theory_value` cannot evaluate Seq
        // selects, so this McCarthy specialization closes the gap (#array-row-seq).
        if Self::select_over_store_empty_row_violated(executor, term) {
            return true;
        }

        // Array-variable equality (e.g. `(= a_12 a_6)`): the store-congruence
        // over arithmetic indices spurious-model pattern surfaces as two array
        // variables the theory claims equal while their reconstructed
        // interpretations provably differ at a concrete index (or vice versa
        // for `(not (= A B))`). This is an internal inconsistency in the
        // candidate model and a hard refutation. Only fires when both operands
        // fully reconstruct (compare_array_models_normalized returns Some(_)),
        // so it does not disturb partial-extraction false positives or pure-EUF
        // array reasoning. No arithmetic model is required: full normalization
        // also refutes QF_ABV cases like `(= f g)` with `f = const(1)` and
        // `g = const(2)`, which are unequal by extensionality (#8729).
        if Self::array_var_equality_violated(executor, model, term) {
            return true;
        }

        // Same-symbolic-base store-chain pointwise refutation
        // (#qf-ax-swap-false-sat) — decides chain-vs-chain (dis)equalities the
        // variable-definition comparison above cannot reconstruct.
        if Self::store_chain_equality_violated(executor, model, term) {
            return true;
        }

        // Conflicting free-base-read pins (#qf-ax-swap-sf-false-sat): two
        // asserted select equalities that both bottom out in the SAME
        // unconstrained base-array read but pin it to two DIFFERENT concrete
        // values cannot both hold under ANY completion of the free base —
        // the candidate model is internally inconsistent. This is the swap
        // `_sf_` shape (`(= e1 (select chainA i))`, `(= e2 (select chainB i))`
        // where both chains shadow nothing at `i` and share one free base),
        // which the per-assertion ground evaluation cannot see because each
        // read alone is a coverage gap, not a violation.
        if Self::conflicting_free_base_read_pins_violated(executor, model, term) {
            return true;
        }

        // Finite-index extensionality over the model's select valuations: two
        // array variables over a finite index domain (Bool / small BitVec /
        // enum) whose pinned selects all agree across the whole domain are
        // provably equal, refuting `(not (= a b))`; a single disagreeing shared
        // index refutes `(= a b)`. Catches the AUFBV datatype-valued-array
        // wrong-SAT the bit-blaster could not reconcile (#dt-array-bv).
        if Self::finite_index_array_equality_violated(executor, model, term) {
            return true;
        }

        // Strip at most one top-level `not` so that `(not (= ...))` can
        // participate in definitive-eval. Polarity is tracked explicitly:
        // - Positive equality/distinct is definitive-false iff the ground
        //   predicate evaluates to Bool(false).
        // - Negated equality/distinct is definitive-false iff the ground
        //   predicate evaluates to Bool(true).
        let (inner, negated) = Self::strip_top_not(executor, term);
        if !Self::is_ground_predicate(executor, model, inner) {
            return false;
        }
        // The ground check above confirmed all predicate operands evaluate to
        // concrete theory values. Re-evaluate the predicate term itself to
        // determine true/false; the evaluator compares the concrete values
        // directly.
        if ay_core::misc_cli_flags().debug_strict_oracle {
            if let TermData::App(sym, args) = executor.ctx.terms.get(inner) {
                let vals: Vec<String> = args
                    .iter()
                    .map(|&a| format!("{:?}", executor.evaluate_term(model, a)))
                    .collect();
                eprintln!(
                    "[strict-oracle-dbg] inner={inner:?} sym={} negated={negated} arg_vals={vals:?} eval={:?}",
                    sym.name(),
                    executor.evaluate_term(model, inner)
                );
                // For select operands, also dump the array operand's
                // materialized interpretation (extraction diagnosis).
                for &a in args.iter() {
                    if let TermData::App(s2, sargs) = executor.ctx.terms.get(a) {
                        if s2.name() == "select" && sargs.len() == 2 {
                            let arr = sargs[0];
                            let interp = model
                                .array_model
                                .as_ref()
                                .and_then(|m| m.array_values.get(&arr));
                            eprintln!(
                                "[strict-oracle-dbg]   select arr={arr:?} idx_val={:?} interp={interp:?}",
                                executor.evaluate_term(model, sargs[1])
                            );
                        }
                    }
                }
            }
        }
        match executor.evaluate_term(model, inner) {
            EvalValue::Bool(v) => {
                if negated {
                    v
                } else {
                    !v
                }
            }
            _ => false,
        }
    }
}

/// Arithmetic oracle — detects false-SAT models for ground-evaluable Int/Real
/// atoms such as `(< t 0)`, `(<= t 0)`, or `(= x c)`.
///
/// The generic arithmetic observation path has a SAT-fallback for historical
/// LIA/LRA extraction gaps (#7654). That fallback is useful for diagnostics,
/// but it is not a consumer-facing proof that a counterexample is valid. When
/// the extracted arithmetic model evaluates both operands to concrete
/// rationals and the asserted atom is false, the observation is definitive:
/// the candidate model does not satisfy the original assertion. The public
/// solve result must therefore degrade to `Unknown` instead of escaping as a
/// trusted SAT/counterexample (#4399 in optimization_consumer).
pub(super) struct ArithmeticOracle;

impl ArithmeticOracle {
    fn has_arithmetic_model(model: &Model) -> bool {
        model.lia_model.is_some() || model.lra_model.is_some()
    }

    fn strip_top_not(executor: &Executor, term: TermId) -> TermId {
        match executor.ctx.terms.get(term) {
            TermData::Not(inner) => *inner,
            TermData::App(sym, args) if sym.name() == "not" && args.len() == 1 => args[0],
            _ => term,
        }
    }

    fn is_int_or_real(sort: &Sort) -> bool {
        matches!(sort, Sort::Int | Sort::Real)
    }

    fn arithmetic_atom_operands_are_concrete(
        executor: &Executor,
        model: &Model,
        term: TermId,
    ) -> bool {
        let inner = Self::strip_top_not(executor, term);
        let TermData::App(sym, args) = executor.ctx.terms.get(inner) else {
            return false;
        };
        if args.len() != 2 {
            return false;
        }

        let applicable = match sym.name() {
            "<" | "<=" | ">" | ">=" => args.iter().all(|&arg| {
                Self::is_int_or_real(executor.ctx.terms.sort(arg))
                    && is_pure_arithmetic_term(&executor.ctx.terms, arg)
            }),
            "=" | "distinct" => {
                Self::is_int_or_real(executor.ctx.terms.sort(args[0]))
                    && Self::is_int_or_real(executor.ctx.terms.sort(args[1]))
                    && is_pure_arithmetic_term(&executor.ctx.terms, args[0])
                    && is_pure_arithmetic_term(&executor.ctx.terms, args[1])
            }
            _ => false,
        };
        if !applicable {
            return false;
        }

        args.iter().all(|&arg| {
            matches!(
                executor.evaluate_term(model, arg),
                EvalValue::Rational(_) | EvalValue::Algebraic(_)
            )
        })
    }
}

impl DefinitiveEval for ArithmeticOracle {
    fn name(&self) -> &'static str {
        "arithmetic"
    }

    fn is_applicable(&self, executor: &Executor, model: &Model, term: TermId) -> bool {
        // NRA irrational-root witnesses (TARGET nra_irrational) need NO
        // suppression here: the model carries the exact algebraic value
        // (`EvalValue::Algebraic`), the evaluator computes with it exactly
        // (residue reduction + Sturm signs), and this oracle verifies the
        // atom like any other — `x*x = 2` evaluates to a definitive `true`
        // at `x = √2`, and a genuinely violated atom is still rejected.
        Self::has_arithmetic_model(model)
            && !executor.ite_false_may_be_model_extraction_gap(model, term)
            && Self::arithmetic_atom_operands_are_concrete(executor, model, term)
    }

    fn definitive_false(&self, executor: &Executor, model: &Model, term: TermId) -> bool {
        let rejected = self.is_applicable(executor, model, term)
            && matches!(executor.evaluate_term(model, term), EvalValue::Bool(false));
        if rejected && ay_core::misc_cli_flags().debug_arith_oracle {
            let inner = Self::strip_top_not(executor, term);
            if let TermData::App(_, args) = executor.ctx.terms.get(inner) {
                for &a in args.iter() {
                    eprintln!(
                        "[arith-oracle] arg={:?} eval={:?} lia={:?} euf_tv={:?} euf_iv={:?}",
                        executor.ctx.terms.get(a),
                        executor.evaluate_term(model, a),
                        model.lia_model.as_ref().and_then(|m| m.values.get(&a)),
                        model.euf_model.as_ref().and_then(|m| m.term_values.get(&a)),
                        model.euf_model.as_ref().and_then(|m| m.int_values.get(&a)),
                    );
                }
            }
        }
        rejected
    }
}

/// ITE-definition oracle — detects false-SAT models for combined EUF+LIA
/// assertions that *define* a UF application via an `ite`, e.g.
/// `(= (f x) (ite c a b))` over Int/Real.
///
/// In the combined Nelson–Oppen route the EUF and LIA sub-models can pick the
/// UF-app value and the ITE-branch values independently, and the generic
/// SAT-fallback for the "ite model-extraction gap"
/// ([`Executor::ite_false_may_be_model_extraction_gap`]) lets such an assertion
/// pass on SAT-evidence alone — without re-checking that the UF app actually
/// equals the selected branch. `ArithmeticOracle` deliberately skips it because
/// a UF application is not [`is_pure_arithmetic_term`]. When the produced model
/// makes the defining equality *concretely* `Bool(false)` (the UF-app value
/// disagrees with the ITE result under the model), the observation is
/// definitive: the candidate model violates the assertion, so the public SAT
/// verdict must degrade to `Unknown` (never UNSAT — this oracle only ever
/// demotes Sat→Unknown). Reproduces on the minimized `traffic.ec` k-induction
/// core `traffic_uflia_falsesat_min.smt2` (QF_UFLIA ite-chain false-SAT, P1):
/// z3/cvc5/yices2 all say `unsat`; AY used to say `sat`.
pub(super) struct IteDefinitionOracle;

impl IteDefinitionOracle {
    /// True when `term` involves BOTH an `ite` and an uninterpreted-function
    /// application — the ite-defines-a-UF-app shape, in either the direct
    /// `(= (f x) (ite c a b))` form or (the form the combined route actually
    /// produces, after lifting the `ite` to the top and distributing the
    /// defining equality into each branch) the
    /// `(ite c (= (f x) ..) (ite .. (= (f x) ..)))` form. Both `contains_*`
    /// walkers descend `not`/`let`/`ite`, so the let-wrapped repro is matched.
    ///
    /// Scoping to "ite + UF" keeps this oracle off pure arithmetic (handled by
    /// `ArithmeticOracle`) and off any ite-free assertion; the actual demotion
    /// is gated below on the term evaluating to a *concrete* `Bool(false)`.
    pub(super) fn is_ite_uf_definition(executor: &Executor, term: TermId) -> bool {
        executor.contains_ite_subterm(term) && executor.contains_uninterpreted_function_app(term)
    }
}

impl DefinitiveEval for IteDefinitionOracle {
    fn name(&self) -> &'static str {
        "ite_uf_definition"
    }

    fn is_applicable(&self, executor: &Executor, model: &Model, term: TermId) -> bool {
        // EUF-route only (pure-arith ITEs belong to ArithmeticOracle; arrays /
        // seq / string / fp are out of scope and fail the concreteness check
        // below via a non-`Bool` EvalValue anyway).
        model.euf_model.is_some() && Self::is_ite_uf_definition(executor, term)
    }

    fn definitive_false(&self, executor: &Executor, model: &Model, term: TermId) -> bool {
        // Fires ONLY when AY's own model makes the asserted `(= uf-app ite)`
        // concretely `Bool(false)` — i.e. the UF-app value and the ITE result
        // both resolve and disagree. A genuine SAT model assigns the UF app a
        // value consistent with its ITE definition (so the `=` is `Bool(true)`)
        // and is never demoted; an incompletely-evaluable model yields
        // `Unknown` (not `Bool(false)`) and is likewise never demoted.
        let rejected = self.is_applicable(executor, model, term)
            && matches!(executor.evaluate_term(model, term), EvalValue::Bool(false));
        if rejected && ay_core::misc_cli_flags().debug_strict_oracle {
            let (inner, negated) = match executor.ctx.terms.get(term) {
                TermData::Not(i) => (*i, true),
                _ => (term, false),
            };
            eprintln!("[ite-uf-oracle] REJECT term={term:?} negated={negated} inner={inner:?}");
            if let TermData::App(sym, args) = executor.ctx.terms.get(inner) {
                eprintln!("[ite-uf-oracle]   sym={} args={:?}", sym.name(), args);
                for &a in args.iter() {
                    eprintln!(
                        "[ite-uf-oracle]   arg {:?} = {:?} :: {}",
                        a,
                        executor.evaluate_term(model, a),
                        executor
                            .format_term(a)
                            .chars()
                            .take(600)
                            .collect::<String>()
                    );
                }
            }
            // Dump every Var / UF-app leaf value the evaluation depends on.
            {
                use ay_core::kani_compat::DetHashSet as DbgSet;
                let mut seen: DbgSet<TermId> = DbgSet::default();
                let mut stack = vec![inner];
                let mut leaves: Vec<TermId> = Vec::new();
                while let Some(t) = stack.pop() {
                    if !seen.insert(t) {
                        continue;
                    }
                    match executor.ctx.terms.get(t) {
                        TermData::Var(_, _) => leaves.push(t),
                        TermData::App(sym, args) => {
                            if !matches!(
                                sym.name(),
                                "+" | "-"
                                    | "*"
                                    | "<"
                                    | "<="
                                    | ">"
                                    | ">="
                                    | "="
                                    | "distinct"
                                    | "and"
                                    | "or"
                                    | "not"
                                    | "=>"
                                    | "ite"
                            ) {
                                leaves.push(t);
                            }
                            stack.extend(args.iter().copied());
                        }
                        TermData::Not(i) => stack.push(*i),
                        TermData::Ite(c, a, b) => {
                            stack.push(*c);
                            stack.push(*a);
                            stack.push(*b);
                        }
                        _ => {}
                    }
                }
                leaves.sort_unstable();
                for t in leaves {
                    eprintln!(
                        "[ite-uf-oracle]   leaf {:?} = {:?} :: {}",
                        t,
                        executor.evaluate_term(model, t),
                        executor
                            .format_term(t)
                            .chars()
                            .take(120)
                            .collect::<String>()
                    );
                }
                // SAT-vs-theory mismatch scan: every SAT-mapped Bool atom whose
                // SAT assignment disagrees with the model evaluation is an atom
                // the theory layer failed to enforce.
                let mut mapped: Vec<(&TermId, &u32)> = model.term_to_var.iter().collect();
                mapped.sort_unstable();
                for (&t, &v) in mapped {
                    let sat_val = model.sat_model.get(v as usize).copied();
                    let eval = executor.evaluate_term(model, t);
                    if let (Some(sv), EvalValue::Bool(ev)) = (sat_val, &eval) {
                        if sv != *ev {
                            eprintln!(
                                "[ite-uf-oracle]   MISMATCH atom {:?} sat={} eval={} :: {}",
                                t,
                                sv,
                                ev,
                                executor
                                    .format_term(t)
                                    .chars()
                                    .take(200)
                                    .collect::<String>()
                            );
                        }
                    }
                }
            }
        }
        rejected
    }
}

/// Integrality oracle — `(to_real x)` for an Int-sorted `x` must evaluate to an
/// integer-valued real. When `x` appears only under `to_real`, the LIRA solver
/// can drop x's integrality and assign `to_real(x)` a fractional value
/// (`(= (to_real x) 0.5)` -> a model with `to_real(x) = 1/2`), which no integer
/// `x` can satisfy. Such a model definitively violates the assertion
/// (#to-real-integrality). Only fires on a *non-integral* value, so a genuine
/// integer assignment is never demoted.
pub(super) struct IntegralityOracle;

impl IntegralityOracle {
    fn has_arithmetic_model(model: &Model) -> bool {
        model.lia_model.is_some() || model.lra_model.is_some()
    }

    /// True when `term` contains a `(to_real t)` (`t : Int`) whose model value
    /// is a non-integral rational.
    fn has_nonintegral_to_real(executor: &Executor, model: &Model, term: TermId) -> bool {
        use ay_core::kani_compat::DetHashSet as HashSet;
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack = vec![term];
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            match executor.ctx.terms.get(t) {
                TermData::App(sym, args) => {
                    if sym.name() == "to_real"
                        && args.len() == 1
                        && *executor.ctx.terms.sort(args[0]) == Sort::Int
                    {
                        if let EvalValue::Rational(r) = executor.evaluate_term(model, t) {
                            if !r.is_integer() {
                                return true;
                            }
                        }
                    }
                    stack.extend(args.iter().copied());
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, a, b) => {
                    stack.push(*c);
                    stack.push(*a);
                    stack.push(*b);
                }
                TermData::Let(bindings, body) => {
                    for (_, v) in bindings {
                        stack.push(*v);
                    }
                    stack.push(*body);
                }
                _ => {}
            }
        }
        false
    }
}

impl DefinitiveEval for IntegralityOracle {
    fn name(&self) -> &'static str {
        "integrality"
    }

    fn is_applicable(&self, _executor: &Executor, model: &Model, _term: TermId) -> bool {
        Self::has_arithmetic_model(model)
    }

    fn definitive_false(&self, executor: &Executor, model: &Model, term: TermId) -> bool {
        Self::has_nonintegral_to_real(executor, model, term)
    }
}

/// Datatype constructor-congruence oracle — a (possibly negated) equality or
/// `distinct` between two datatype-related operands is decided by resolving each
/// operand to a *fully ground* canonical value under the model and comparing.
///
/// Two distinct unsound paths motivate this oracle:
///
/// 1. **Pure QF_DT** lacks upward constructor congruence in the standalone
///    `DtSolver`, so a model with `a = b` but `(mk a) != (mk b)` asserted slips
///    through as a wrong SAT (#dt-congruence).
///
/// 2. **The eager DT+BV bit-blast route** (a datatype with a BitVector field)
///    drops datatype constructor/selector congruence (single-constructor
///    injectivity `mk x = mk y => x = y`, constructor distinctness, tester
///    semantics). The bit-blasted SAT encoding therefore finds models in which,
///    e.g., `(v x) = (v y)` holds yet the asserted `(not (= x y))` is *also*
///    "satisfied" — but the model AY extracts assigns x and y the SAME
///    constructor value, so the disequality is genuinely violated. The model
///    evaluator does not resolve selector/variable operands through the DT
///    model, so it returns Unknown and the assertion is skipped (#dt-bv-congruence).
///
/// Both are caught here: we resolve each operand of an `=`/`distinct` to a
/// canonical, fully-ground model-value string (the same canonicalization the
/// model printer uses). When BOTH operands resolve to ground values:
///   - equal strings  => the operands are model-equal,
///   - different strings => the operands are model-distinct (the canonical form
///     is injective: same value <=> same string).
/// Combined with the asserted polarity, this lets us demote SAT -> Unknown when
/// the model genuinely violates the (dis)equality. If EITHER operand fails to
/// resolve to a ground value (Unknown, or a string carrying an internal
/// placeholder), we return `false` (no demotion): a partial extraction is a
/// completeness gap, never a soundness violation. SOUNDNESS over completeness.
pub(super) struct DtOracle;

impl DtOracle {
    /// True if `term` has a datatype sort (stored internally as
    /// `Sort::Uninterpreted("<dt_name>")`; see term_analysis.rs / dt_axioms.rs).
    fn is_datatype_sorted(executor: &Executor, term: TermId) -> bool {
        let sort = executor.ctx.terms.sort(term);
        sort.is_datatype()
            || matches!(
                sort,
                Sort::Uninterpreted(ref s)
                    if executor.ctx.datatype_iter().any(|(dt, _)| dt == s.as_str())
            )
    }

    /// True if `term` is a constructor, selector, or tester application, or a
    /// datatype-sorted variable/constant — i.e. resolving it requires datatype
    /// reconstruction semantics that the BV bit-blast / pure-DT solver may not
    /// soundly capture.
    fn is_dt_related_operand(executor: &Executor, term: TermId) -> bool {
        if Self::is_datatype_sorted(executor, term) {
            return true;
        }
        if let TermData::App(sym, _) = executor.ctx.terms.get(term) {
            let name = sym.name();
            // Selector application: the head names a declared selector.
            if executor
                .ctx
                .ctor_selectors_iter()
                .any(|(_ctor, sels)| sels.iter().any(|sel| sel == name))
            {
                return true;
            }
            // Constructor or tester application.
            if executor.ctx.is_constructor(name).is_some()
                || name
                    .strip_prefix("is-")
                    .is_some_and(|c| executor.ctx.is_constructor(c).is_some())
            {
                return true;
            }
        }
        false
    }

    /// Reject canonical strings that carry an unresolved internal marker. A `?`
    /// is emitted by the printer when a selector value cannot be found; an `@`
    /// prefixes an internal equivalence-class representative (e.g. `@Color!0`).
    /// Either means the value is not fully ground, so it must NOT participate in
    /// a definitive-violation decision.
    fn is_ground_canonical(s: &str) -> bool {
        !s.contains('?') && !s.contains('@')
    }

    /// Resolve `term` to a fully-ground canonical model-value string, or `None`
    /// if it cannot be resolved to ground. The resulting strings are canonical:
    /// two operands resolving to the same model value produce byte-identical
    /// strings, and distinct ground values produce distinct strings.
    ///
    /// Bounded recursion depth guards against pathological nested datatype values
    /// (the parser already bounds term depth, but be defensive).
    fn resolve_ground(executor: &Executor, model: &Model, term: TermId) -> Option<String> {
        Self::resolve_ground_depth(executor, model, term, 0)
    }

    fn resolve_ground_depth(
        executor: &Executor,
        model: &Model,
        term: TermId,
        depth: u32,
    ) -> Option<String> {
        if depth >= 64 {
            return None;
        }
        // Total-datatype-model pin (#dt-total-model): the datatype
        // model-construction phase resolved this term to a concrete ground
        // constructor value; its canonical string IS the term's model value
        // (identical for every co-class term, distinct across distinct
        // values), so both the violation and the confirmation direction read
        // the same total assignment the evaluator and the printers use.
        if let Some(EvalValue::Element(canon)) = model.dt_pins.get(&term) {
            return Some(canon.clone());
        }
        // A constructor application `(Ctor a0 a1 ...)` is resolved structurally:
        // its head names the constructor and its arguments give the field values
        // directly. This is the authoritative form — `resolve_dt_value` is the
        // VARIABLE resolver (it scans for testers/selectors keyed by the operand
        // term-id) and mis-resolves a literal constructor application, so it must
        // NOT be used here. Resolving args recursively also canonicalizes nested
        // datatype literals (`(some16 (mk ...))`).
        if let TermData::App(sym, args) = executor.ctx.terms.get(term) {
            let name = sym.name();
            if executor.ctx.is_constructor(name).is_some() {
                let mut parts = Vec::with_capacity(args.len());
                for &arg in args {
                    parts.push(Self::resolve_ground_depth(executor, model, arg, depth + 1)?);
                }
                return Some(if parts.is_empty() {
                    name.to_string()
                } else {
                    format!("({} {})", name, parts.join(" "))
                });
            }
        }

        // A selector applied DIRECTLY to a constructor application,
        // `(sel_i (C a0 a1 ..)) -> a_i` (the SMT-LIB datatype selector axiom).
        // The elaboration-time selector fold reduces these, but a RECONSTRUCTED
        // validation assertion can carry an un-folded `(fld_params (Parser_mk
        // ..))` — the datatype const was substituted by its `Parser_mk(..)`
        // binding only after elaboration, so the fold never ran on it. Without
        // reducing it here the operand is treated as an unresolved selector
        // chain, `resolve_ground` returns None, and the #dt-bv-congruence guard
        // fail-closes a reflexively-true equality to `unknown`. Reduce to the
        // field and resolve that. (#selector-over-ctor-ground)
        if let TermData::App(sym, args) = executor.ctx.terms.get(term) {
            if args.len() == 1 {
                let sel_name = sym.name();
                let inner = args[0];
                if let TermData::App(inner_sym, inner_args) = executor.ctx.terms.get(inner) {
                    let inner_name = inner_sym.name();
                    if executor.ctx.is_constructor(inner_name).is_some() {
                        if let Some(selectors) = executor.ctx.constructor_selectors(inner_name) {
                            if let Some(idx) = selectors.iter().position(|s| s == sel_name) {
                                if let Some(&field) = inner_args.get(idx) {
                                    return Self::resolve_ground_depth(
                                        executor,
                                        model,
                                        field,
                                        depth + 1,
                                    );
                                }
                            }
                        }
                    }
                }
            }
        }
        // A datatype-sorted variable / selector-result. Resolve STRICTLY: the
        // constructor must be determined by a model-true tester (or be the sole
        // constructor), and every field must resolve to a REAL model value via
        // its selector application. We deliberately do NOT call `resolve_dt_value`
        // here: that printer helper fabricates DEFAULT field values (e.g. `#x00`)
        // for fields the theory model leaves unconstrained, which look ground but
        // are not. Trusting a fabricated default would let us demote a genuinely
        // SAT model (e.g. `s = (mk-val #x01)` whose field lives only in an
        // asserted equality the BV model never pinned). Returning `None` on any
        // unresolved field keeps the oracle conservative: SOUNDNESS demands we
        // never invent a value to drive a violation decision.
        if Self::is_datatype_sorted(executor, term) {
            // Committed ENUM value fast path (#enum-sat-lane): for an
            // all-nullary (enum) datatype sort, a committed EUF element that
            // IS one of the sort's constructor names is already the fully
            // ground canonical value — an enum constructor has no fields to
            // resolve, and the element is the model's OWN committed
            // interpretation (the same value `evaluate_term` and the printers
            // read; never a fabricated field default, which is what the
            // strict resolver below guards against). Byte-identical to the
            // constructor-application branch above, so canonical-string
            // comparisons are unaffected. Without this, `resolve_dt_var_strict`
            // re-derives every enum operand from asserted equalities/testers
            // by scanning all assertions and the whole term store —
            // O(assertions^2) on coloring-scale instances (observed: the
            // strict gate alone outlived a 150s budget on vlsat3_h92 while
            // validating an already-decoded 21k-atom model). Models whose
            // elements are internal representatives (`@Sort!n`) do not match
            // a constructor name and take the strict path exactly as before.
            if let Some(s) = Self::resolve_committed_enum_value(executor, model, term) {
                return Some(s);
            }
            return Self::resolve_dt_var_strict(executor, model, term, depth);
        }
        // Leaf-sorted operand (BV / Int / Real / Bool / ...). Prefer the
        // recursive evaluator, which is authoritative for constants and computed
        // terms. `lookup_term_value` indexes theory models by term-id and can
        // return a stale/unrelated value for shared constant nodes (e.g. a `#x5`
        // literal whose term-id collides with a bv_model entry), so it is used
        // ONLY as a fallback for terms the evaluator cannot reduce — namely
        // selector chains over datatype terms (`(counter s)`, `(ok_val (tag s))`).
        let val = match executor.evaluate_term(model, term) {
            EvalValue::Unknown => executor.lookup_term_value(model, term),
            v => v,
        };
        if matches!(val, EvalValue::Unknown) {
            return None;
        }
        let s = executor.format_eval_value(&val, term);
        Self::is_ground_canonical(&s).then_some(s)
    }

    /// Resolve an ALL-NULLARY (enum) datatype term through its committed EUF
    /// model element, accepting the element ONLY when it names one of the
    /// sort's constructors (then it is fully ground by itself — no fields).
    /// Returns `None` for non-enum sorts, missing entries, or internal
    /// representative elements, which keep the strict resolution path.
    fn resolve_committed_enum_value(
        executor: &Executor,
        model: &Model,
        term: TermId,
    ) -> Option<String> {
        let sort = executor.ctx.terms.sort(term);
        // `Some(k)` only for all-nullary datatypes (any field => None).
        executor.enum_datatype_constructor_count(sort)?;
        let sort_name = match sort {
            Sort::Uninterpreted(ref s) => s.as_str(),
            Sort::Datatype(ref dt) => dt.name.as_str(),
            _ => return None,
        };
        let val = model.euf_model.as_ref()?.term_values.get(&term)?;
        let (_, ctors) = executor
            .ctx
            .datatype_iter()
            .find(|(dt, _)| *dt == sort_name)?;
        ctors.iter().any(|c| c == val).then(|| val.clone())
    }

    /// Strictly resolve a datatype-sorted term `term` to a canonical constructor
    /// value, using only REAL model evidence (no fabricated defaults). Returns
    /// `None` if the constructor is ambiguous/undetermined or any field cannot be
    /// resolved to a real model value.
    fn resolve_dt_var_strict(
        executor: &Executor,
        model: &Model,
        term: TermId,
        depth: u32,
    ) -> Option<String> {
        let sort = executor.ctx.terms.sort(term);
        let sort_name = match sort {
            Sort::Uninterpreted(ref s) => s.clone(),
            Sort::Datatype(ref dt) => dt.name.clone(),
            _ => return None,
        };
        // (1) If `term` is asserted equal to a ground constructor application,
        // that application IS its value (a real, non-default binding). This
        // covers `(= s (mk-val #x01))`.
        if let Some(s) = Self::resolve_from_asserted_ctor_eq(executor, model, term, depth) {
            return Some(s);
        }
        // (2) Otherwise, determine the constructor from a model-true tester (or
        // the unique constructor) and resolve each field via its REAL selector
        // value.
        let constructors: Vec<String> = executor
            .ctx
            .datatype_iter()
            .find(|(dt, _)| *dt == sort_name)
            .map(|(_, ctors)| ctors.iter().map(|c| c.to_string()).collect())
            .unwrap_or_default();
        if constructors.is_empty() {
            return None;
        }
        let ctor = if constructors.len() == 1 {
            constructors[0].clone()
        } else {
            // Need an unambiguous model-true tester.
            let mut chosen: Option<String> = None;
            for c in &constructors {
                if Self::tester_true_in_model(executor, model, c, term) {
                    if chosen.is_some() {
                        return None; // ambiguous: multiple testers true
                    }
                    chosen = Some(c.clone());
                }
            }
            chosen?
        };
        let selectors = executor.ctx.constructor_selectors(&ctor).unwrap_or(&[]);
        if selectors.is_empty() {
            return Some(ctor);
        }
        let mut parts = Vec::with_capacity(selectors.len());
        for sel in selectors {
            // Find the selector application `(sel term)` in the term store.
            let sel_app = Self::find_selector_app(executor, sel, term)?;
            parts.push(Self::resolve_ground_depth(
                executor,
                model,
                sel_app,
                depth + 1,
            )?);
        }
        Some(format!("({} {})", ctor, parts.join(" ")))
    }

    /// If `term` is asserted (model-true) equal to a constructor application,
    /// return that application's canonical resolution.
    fn resolve_from_asserted_ctor_eq(
        executor: &Executor,
        model: &Model,
        term: TermId,
        depth: u32,
    ) -> Option<String> {
        for &assertion in &executor.ctx.assertions {
            let TermData::App(sym, args) = executor.ctx.terms.get(assertion) else {
                continue;
            };
            if sym.name() != "=" || args.len() != 2 {
                continue;
            }
            let eq_true = executor
                .term_value(&model.sat_model, &model.term_to_var, assertion)
                .unwrap_or(true);
            if !eq_true {
                continue;
            }
            let other = if args[0] == term {
                args[1]
            } else if args[1] == term {
                args[0]
            } else {
                continue;
            };
            if let TermData::App(osym, _) = executor.ctx.terms.get(other) {
                if executor.ctx.is_constructor(osym.name()).is_some() {
                    return Self::resolve_ground_depth(executor, model, other, depth + 1);
                }
            }
        }
        None
    }

    /// True if `(is-ctor term)` is assigned true in the model (asserted, or true
    /// in the SAT model).
    fn tester_true_in_model(executor: &Executor, model: &Model, ctor: &str, term: TermId) -> bool {
        let tester = format!("is-{ctor}");
        for idx in 0..executor.ctx.terms.len() {
            let tid = TermId(idx as u32);
            if let TermData::App(sym, args) = executor.ctx.terms.get(tid) {
                if sym.name() == tester && args.len() == 1 && args[0] == term {
                    if executor.ctx.assertions.contains(&tid) {
                        return true;
                    }
                    return executor.term_value(&model.sat_model, &model.term_to_var, tid)
                        == Some(true);
                }
            }
        }
        false
    }

    /// Find the selector application term `(sel arg)` in the term store.
    fn find_selector_app(executor: &Executor, sel: &str, arg: TermId) -> Option<TermId> {
        for idx in 0..executor.ctx.terms.len() {
            let tid = TermId(idx as u32);
            if let TermData::App(sym, args) = executor.ctx.terms.get(tid) {
                if sym.name() == sel && args.len() == 1 && args[0] == arg {
                    return Some(tid);
                }
            }
        }
        None
    }
}

impl DefinitiveEval for DtOracle {
    fn name(&self) -> &'static str {
        "datatype"
    }

    fn is_applicable(&self, executor: &Executor, _model: &Model, term: TermId) -> bool {
        let inner = match executor.ctx.terms.get(term) {
            TermData::Not(inner) => *inner,
            _ => term,
        };
        let TermData::App(sym, args) = executor.ctx.terms.get(inner) else {
            return false;
        };
        if !matches!(sym.name(), "=" | "distinct") || args.len() != 2 {
            return false;
        }
        // Fire when EITHER side is a datatype-related operand (constructor,
        // selector, tester, or datatype-sorted term). This subsumes the original
        // `(C ..) = (C ..)` syntactic case and additionally covers
        // variable/selector operands whose truth depends on DT reconstruction.
        Self::is_dt_related_operand(executor, args[0])
            || Self::is_dt_related_operand(executor, args[1])
    }

    fn definitive_false(&self, executor: &Executor, model: &Model, term: TermId) -> bool {
        let (inner, negated) = match executor.ctx.terms.get(term) {
            TermData::Not(i) => (*i, true),
            _ => (term, false),
        };
        let TermData::App(sym, args) = executor.ctx.terms.get(inner) else {
            return false;
        };
        if !matches!(sym.name(), "=" | "distinct") || args.len() != 2 {
            return false;
        }
        // Resolve both operands to fully-ground canonical values. If either is
        // unresolved, this is a completeness gap, not a violation -> no demotion.
        let (Some(lhs), Some(rhs)) = (
            Self::resolve_ground(executor, model, args[0]),
            Self::resolve_ground(executor, model, args[1]),
        ) else {
            return false;
        };
        // Canonical form is injective: equal strings <=> equal values.
        let operands_equal = lhs == rhs;
        // The assertion as written (after stripping the outer `not`) claims:
        //   `=`        : operands are equal
        //   `distinct` : operands are NOT equal
        let assertion_claims_equal = match sym.name() {
            "=" => !negated,
            "distinct" => negated,
            _ => return false,
        };
        // Violated when the model disagrees with the asserted polarity.
        assertion_claims_equal != operands_equal
    }
}

/// True if both operands of the (possibly negated) `=`/`distinct` atom `term`
/// resolve to fully-ground canonical datatype/leaf values under `model` (no
/// fabricated defaults). When this holds, the [`DtOracle`] has already had the
/// authoritative opportunity to flag a violation via the global strict gate, so
/// the model evaluator's Bool verdict for the atom can be trusted. When it does
/// NOT hold, the evaluator's verdict for a datatype-sort (dis)equality is read
/// off EUF element identity that the eager DT+BV bit-blast does not maintain, so
/// it must NOT be accepted as independent evidence (#dt-bv-congruence).
pub(crate) fn dt_equality_operands_fully_ground(
    executor: &Executor,
    model: &Model,
    term: TermId,
) -> bool {
    let inner = match executor.ctx.terms.get(term) {
        TermData::Not(i) => *i,
        _ => term,
    };
    let TermData::App(sym, args) = executor.ctx.terms.get(inner) else {
        return false;
    };
    if !matches!(sym.name(), "=" | "distinct") || args.len() != 2 {
        return false;
    }
    DtOracle::resolve_ground(executor, model, args[0]).is_some()
        && DtOracle::resolve_ground(executor, model, args[1]).is_some()
}

/// Reduce `(sel_i (C a0 a1 ..)) -> a_i` (the SMT-LIB selector axiom) repeatedly,
/// recursing into the selector argument first, and return the reduced term.
/// Leaves any term that is not a selector-over-constructor untouched.
pub(crate) fn reduce_selector_chain(executor: &Executor, term: TermId) -> TermId {
    let td = executor.ctx.terms.get(term).clone();
    if let TermData::App(sym, args) = td {
        if args.len() == 1 {
            let reduced_arg = reduce_selector_chain(executor, args[0]);
            let inner_td = executor.ctx.terms.get(reduced_arg).clone();
            if let TermData::App(inner_sym, inner_args) = inner_td {
                if executor.ctx.is_constructor(inner_sym.name()).is_some() {
                    if let Some(selectors) = executor.ctx.constructor_selectors(inner_sym.name()) {
                        if let Some(idx) = selectors.iter().position(|s| s.as_str() == sym.name()) {
                            if let Some(&field) = inner_args.get(idx) {
                                return field;
                            }
                        }
                    }
                }
            }
        }
    }
    term
}

/// Decide a datatype-sort `=`/`distinct` atom (possibly under a single `Not`)
/// purely by SELECTOR REDUCTION when both operands collapse to the SAME term —
/// a reflexively-true equality such as `(= X (fld_params (Parser_mk .. X ..)))`
/// produced when a datatype const is substituted by its `Ctor(..)` binding
/// AFTER elaboration. `resolve_ground` cannot confirm these when a field is an
/// `Array` (no canonical ground string), so the #dt-bv-congruence guard would
/// fail-close a trivially-true atom to `unknown`. Returns `Some(true)` when the
/// atom is SATISFIED, `Some(false)` when VIOLATED, and `None` when reduction
/// does not collapse the operands to one term (left to the existing path — we
/// never fabricate a difference). (#selector-over-ctor-ground)
pub(crate) fn dt_equality_decidable_by_reduction(
    executor: &Executor,
    term: TermId,
) -> Option<bool> {
    let (inner, negated) = match executor.ctx.terms.get(term) {
        TermData::Not(i) => (*i, true),
        _ => (term, false),
    };
    let TermData::App(sym, args) = executor.ctx.terms.get(inner) else {
        return None;
    };
    let claims_equal = match sym.name() {
        "=" => !negated,
        "distinct" => negated,
        _ => return None,
    };
    if args.len() != 2 {
        return None;
    }
    let (a, b) = (args[0], args[1]);
    let lhs = reduce_selector_chain(executor, a);
    let rhs = reduce_selector_chain(executor, b);
    // Same TermId, OR structurally identical terms (the store does not always
    // hash-cons, so a datatype round-trip like `(= X (fld_vec (Iter_mk X k)))`
    // reduces both sides to a structurally-equal-but-distinct `Slice_mk(..)`).
    // Structural identity is a SOUND witness of semantic equality — no model,
    // no array canonicalization, no fabricated defaults.
    if lhs == rhs || terms_structurally_equal(executor, lhs, rhs, 4000) {
        // Operands are provably equal; the atom is satisfied iff it claims so.
        Some(claims_equal)
    } else {
        None
    }
}

/// Decide a `=`/`distinct` between two datatype (or scalar) operands PURELY by
/// the datatype axioms — selector-over-constructor reduction, reflexivity, and
/// constructor injectivity/distinctness — with NO model and NO array
/// canonicalization. `Some(true)`/`Some(false)` are PROOFS (hold in every model);
/// `None` means "cannot decide syntactically" (never guessed). SOUND: it only
/// ever returns a value it can prove from the free datatype theory.
fn dt_reduced_eq(executor: &Executor, a: TermId, b: TermId, depth: u32) -> Option<bool> {
    if depth == 0 {
        return None;
    }
    let ra = reduce_selector_chain(executor, a);
    let rb = reduce_selector_chain(executor, b);
    if terms_structurally_equal(executor, ra, rb, 4000) {
        return Some(true); // reflexive: same value in every model
    }
    // One side an `ite`: `(= X (ite c T E))` = `(ite c (= X T) (= X E))`. If BOTH
    // branch-equalities decide to the SAME value, the equality has that value in
    // EVERY model regardless of the (model-determined) condition. SOUND,
    // branch-agnostic — confirms `= through ite` for conditional datatype values.
    for (p, q) in [(ra, rb), (rb, ra)] {
        if let TermData::Ite(_, t, e) = executor.ctx.terms.get(p) {
            match (
                dt_reduced_eq(executor, *t, q, depth - 1),
                dt_reduced_eq(executor, *e, q, depth - 1),
            ) {
                (Some(x), Some(y)) if x == y => return Some(x),
                _ => {}
            }
        }
    }
    // Both sides a constructor application? Then injectivity/distinctness decides.
    let (TermData::App(sa, aa), TermData::App(sb, ab)) =
        (executor.ctx.terms.get(ra), executor.ctx.terms.get(rb))
    else {
        return None;
    };
    let (Some((dta, ca)), Some((dtb, cb))) = (
        executor.ctx.is_constructor(sa.name()),
        executor.ctx.is_constructor(sb.name()),
    ) else {
        return None; // not both constructors — cannot decide syntactically
    };
    if dta != dtb {
        return None; // different datatypes: ill-typed comparison; stay safe
    }
    if ca != cb {
        return Some(false); // DISTINCT constructors of the same datatype
    }
    if aa.len() != ab.len() {
        return None;
    }
    // Same constructor: equal IFF every field is equal (injectivity). Only a
    // provable field DISequality yields `false`; a field we cannot decide leaves
    // the whole equality UNDECIDED (`None`) — never a fabricated `true`.
    let mut all_true = true;
    for (&x, &y) in aa.iter().zip(ab.iter()) {
        let fx = executor.ctx.terms.sort(x).clone();
        let field_eq = if fx == Sort::Bool {
            match (
                dt_axiom_bool(executor, x, depth - 1),
                dt_axiom_bool(executor, y, depth - 1),
            ) {
                (Some(bx), Some(by)) => Some(bx == by),
                _ => None,
            }
        } else {
            // Datatype, scalar and BV fields alike: `dt_reduced_eq` first
            // selector-reduces BOTH operands (so a field written as
            // `(sel_i (Ctor ..))` folds to the same term as its concrete
            // counterpart) and then decides by structural identity /
            // constructor axioms. Reflexive-after-reduction ⇒ Some(true); a
            // provable scalar difference stays None (never fabricated).
            dt_reduced_eq(executor, x, y, depth - 1)
        };
        match field_eq {
            Some(false) => return Some(false),
            Some(true) => {}
            None => all_true = false,
        }
    }
    if all_true {
        Some(true)
    } else {
        None
    }
}

/// Decide a Bool-sorted assertion PURELY by the datatype + Boolean axioms
/// (tester-over-constructor, selector-over-constructor, injectivity/distinctness,
/// and Boolean folding) — MODEL-INDEPENDENT. Returns `Some(true)` ONLY when the
/// assertion is a datatype TAUTOLOGY (holds in every model), `Some(false)` when
/// provably false, and `None` otherwise. This is what confirms ay's own injected
/// DT congruence / tester / selector axioms — e.g.
/// `(= (is-Ctor Y) (= Y (Ctor (sel1 Y) .. (seln Y))))` after `Y` is a
/// materialized constructor — WITHOUT consulting the model or canonicalizing a
/// datatype-carrying array, so it never fabricates a satisfaction. SOUND: a
/// `Some(true)` is a proof from the free datatype theory.
pub(crate) fn dt_axiom_bool(executor: &Executor, term: TermId, depth: u32) -> Option<bool> {
    if depth == 0 {
        return None;
    }
    match executor.ctx.terms.get(term) {
        TermData::Const(Constant::Bool(b)) => Some(*b),
        TermData::Not(inner) => dt_axiom_bool(executor, *inner, depth - 1).map(|b| !b),
        TermData::Ite(c, t, e) => match dt_axiom_bool(executor, *c, depth - 1) {
            Some(true) => dt_axiom_bool(executor, *t, depth - 1),
            Some(false) => dt_axiom_bool(executor, *e, depth - 1),
            None => {
                // Condition undecidable model-free: if BOTH branches decide to
                // the SAME Boolean value, the `ite` equals that value in EVERY
                // model regardless of the condition. SOUND (branch-agnostic).
                // This confirms the `= through ite` congruence axioms ay injects
                // for conditional datatype values.
                match (
                    dt_axiom_bool(executor, *t, depth - 1),
                    dt_axiom_bool(executor, *e, depth - 1),
                ) {
                    (Some(x), Some(y)) if x == y => Some(x),
                    _ => None,
                }
            }
        },
        TermData::App(sym, args) => match sym.name() {
            "and" => {
                let mut all_true = true;
                for &a in args {
                    match dt_axiom_bool(executor, a, depth - 1) {
                        Some(false) => return Some(false),
                        Some(true) => {}
                        None => all_true = false,
                    }
                }
                if all_true {
                    Some(true)
                } else {
                    None
                }
            }
            "or" => {
                let mut all_false = true;
                for &a in args {
                    match dt_axiom_bool(executor, a, depth - 1) {
                        Some(true) => return Some(true),
                        Some(false) => {}
                        None => all_false = false,
                    }
                }
                if all_false {
                    Some(false)
                } else {
                    None
                }
            }
            // Tester `(is-Ctor X)`: reduce X; when it folds to a constructor
            // application, the tester is decided by constructor-name identity.
            name if name
                .strip_prefix("is-")
                .is_some_and(|c| executor.ctx.is_constructor(c).is_some())
                && args.len() == 1 =>
            {
                let want = name.strip_prefix("is-").unwrap();
                let red = reduce_selector_chain(executor, args[0]);
                match executor.ctx.terms.get(red) {
                    TermData::App(isym, _) => executor
                        .ctx
                        .is_constructor(isym.name())
                        .map(|(_, cn)| cn == want),
                    _ => None,
                }
            }
            "=" if args.len() == 2 => {
                if *executor.ctx.terms.sort(args[0]) == Sort::Bool {
                    match (
                        dt_axiom_bool(executor, args[0], depth - 1),
                        dt_axiom_bool(executor, args[1], depth - 1),
                    ) {
                        (Some(x), Some(y)) => Some(x == y),
                        _ => None,
                    }
                } else {
                    dt_reduced_eq(executor, args[0], args[1], depth - 1)
                }
            }
            "distinct" if args.len() == 2 => {
                dt_reduced_eq(executor, args[0], args[1], depth - 1).map(|b| !b)
            }
            _ => None,
        },
        _ => None,
    }
}

/// Bounded structural (syntactic) equality of two terms: identical `TermData`
/// shape with recursively-equal children. SOUND witness that the two terms
/// denote the same value in EVERY model (reflexivity), independent of the model
/// / any theory. Returns `false` on depth exhaustion (never a false positive).
pub(crate) fn terms_structurally_equal(
    executor: &Executor,
    a: TermId,
    b: TermId,
    depth: u32,
) -> bool {
    if a == b {
        return true;
    }
    if depth == 0 {
        return false;
    }
    match (executor.ctx.terms.get(a), executor.ctx.terms.get(b)) {
        (TermData::Var(x, sx), TermData::Var(y, sy)) => x == y && sx == sy,
        (TermData::Const(cx), TermData::Const(cy)) => cx == cy,
        (TermData::App(sa, aa), TermData::App(sb, ab)) => {
            sa.name() == sb.name()
                && aa.len() == ab.len()
                && aa
                    .iter()
                    .zip(ab.iter())
                    .all(|(&x, &y)| terms_structurally_equal(executor, x, y, depth - 1))
        }
        (TermData::Not(x), TermData::Not(y)) => {
            terms_structurally_equal(executor, *x, *y, depth - 1)
        }
        (TermData::Ite(cx, tx, ex), TermData::Ite(cy, ty, ey)) => {
            terms_structurally_equal(executor, *cx, *cy, depth - 1)
                && terms_structurally_equal(executor, *tx, *ty, depth - 1)
                && terms_structurally_equal(executor, *ex, *ey, depth - 1)
        }
        _ => false,
    }
}

/// Datatype-field oracle — closes false-SAT models where a STRING / BV /
/// arithmetic / recognizer predicate is taken over a value reached through a
/// datatype SELECTOR (or a select-produced datatype value) whose field the
/// candidate model leaves unconstrained.
///
/// The top-level DT (dis)equality oracle ([`DtOracle`]) validates equalities
/// between datatype values, but it does NOT re-evaluate a predicate that reads a
/// datatype field and feeds it to another theory. Three concrete holes (all one
/// family: "a datatype value reached through a SELECT/SELECTOR is not
/// constrained, so AY accepts a self-contradicting model"):
///
/// * A `String`-typed selector value disconnected from the string theory:
///   `(= (str.++ (s d) "x") "yz")` is accepted with `(s d) = ""` even though
///   `"" ++ "x" = "x" != "yz"`. Also `(str.< (s d) (s d))` (irreflexive).
/// * A sole-constructor recognizer over a `select`-produced value:
///   `(not ((_ is c2) (select v6 0)))` where `c2` is the only constructor (the
///   recognizer is a tautology, so the negation is definitively false).
/// * A BV / Int field not propagated through a (possibly deep) selector chain:
///   `(not (= (ib (tm v0)) #x4))` with `v0 = (tnode (ileaf #x4))`, or
///   `(bvugt (mb m) #xf)` where `(mb m)` is a 4-bit field <= `#xf`.
///
/// The oracle re-evaluates the assertion through [`Executor::dt_mat_eval`],
/// which materializes every datatype selector/recognizer subterm against the
/// model's ACTUAL constructor assignment (defaulting an unconstrained field to
/// exactly the value the model printer presents). When that re-evaluation
/// yields `Bool(false)`, the candidate model genuinely falsifies the assertion
/// — a hard violation. It NEVER demotes on `Unknown`, so a model-extraction gap
/// is never mistaken for a violation (SOUNDNESS over completeness).
pub(super) struct DtFieldOracle;

impl DtFieldOracle {
    /// Maximum recursion depth for the materialized re-evaluator. Deep enough for
    /// realistic nested datatype field chains; bounds pathological recursion.
    const MAT_DEPTH: u32 = 64;
}

impl DefinitiveEval for DtFieldOracle {
    fn name(&self) -> &'static str {
        "datatype-field"
    }

    fn is_applicable(&self, executor: &Executor, _model: &Model, term: TermId) -> bool {
        // Fire whenever the assertion mentions a datatype selector application or
        // a recognizer over a datatype value. `dt_mat_eval` is responsible for the
        // soundness decision; this is only a cheap scope filter.
        executor.term_mentions_dt_field(term)
    }

    fn definitive_false(&self, executor: &Executor, model: &Model, term: TermId) -> bool {
        matches!(
            executor.dt_mat_eval(model, term, Self::MAT_DEPTH),
            EvalValue::Bool(false)
        )
    }
}

/// Sequence oracle — a (possibly negated) equality/`distinct`/membership atom
/// that mentions a `seq.*` operation is decided by the model evaluator
/// (`eval_seq` resolves seq.nth/len/++/at/contains/... over the committed seq
/// model). The QF_SEQ axiom layer fails to generate the seq.nth axioms when the
/// sequence is a *variable* equated to a unit/concat (#seq-nth-var), leaving the
/// integer result unconstrained and admitting a wrong SAT (e.g.
/// `a = (seq.unit 1) ∧ (seq.nth a 0) = 2`). When the evaluator reduces the
/// asserted atom to `Bool(false)` under the model, the model genuinely violates
/// it -> demote SAT to Unknown. (If a seq operand is unresolved the evaluator
/// returns a non-Bool value, so this never over-demotes a model-extraction gap.)
pub(super) struct SeqOracle;

impl SeqOracle {
    fn mentions_seq_op(executor: &Executor, term: TermId) -> bool {
        use ay_core::kani_compat::DetHashSet as HashSet;
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack = vec![term];
        let mut budget = 512u32;
        while let Some(t) = stack.pop() {
            if budget == 0 {
                break;
            }
            budget -= 1;
            if !visited.insert(t) {
                continue;
            }
            match executor.ctx.terms.get(t) {
                TermData::App(sym, args) => {
                    if sym.name().starts_with("seq.") {
                        return true;
                    }
                    stack.extend(args.iter().copied());
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, a, b) => {
                    stack.push(*c);
                    stack.push(*a);
                    stack.push(*b);
                }
                _ => {}
            }
        }
        false
    }

    /// Structurally (model-free) the empty sequence: `(as seq.empty ...)`, the
    /// empty string literal `""`, or a concat over only empty operands.
    fn seq_struct_empty(executor: &Executor, term: TermId, depth: u32) -> bool {
        if depth == 0 {
            return false;
        }
        match executor.ctx.terms.get(term) {
            TermData::App(sym, args) if sym.name() == "seq.empty" && args.is_empty() => true,
            TermData::App(sym, args)
                if matches!(sym.name(), "seq.++" | "str.++") && args.len() >= 2 =>
            {
                args.iter()
                    .all(|&a| Self::seq_struct_empty(executor, a, depth - 1))
            }
            TermData::Const(Constant::String(s)) => s.is_empty(),
            _ => false,
        }
    }

    /// Structurally (model-free) a seq/string term that PROVABLY has length >= 1
    /// for EVERY assignment: a `(seq.unit _)`, a non-empty string literal, or a
    /// concat with at least one such leaf. A bare variable, `seq.empty`, `""`, an
    /// opaque app, or a concat of only vars/empties is NOT provably non-empty
    /// (returns false — fail closed).
    fn seq_has_nonempty_leaf(executor: &Executor, term: TermId, depth: u32) -> bool {
        if depth == 0 {
            return false;
        }
        match executor.ctx.terms.get(term) {
            TermData::App(sym, args) if sym.name() == "seq.unit" && args.len() == 1 => true,
            TermData::Const(Constant::String(s)) => !s.is_empty(),
            TermData::App(sym, args)
                if matches!(sym.name(), "seq.++" | "str.++") && args.len() >= 2 =>
            {
                args.iter()
                    .any(|&a| Self::seq_has_nonempty_leaf(executor, a, depth - 1))
            }
            _ => false,
        }
    }

    /// Model-free refutation of a POSITIVE seq/string equality `(= a b)` where one
    /// side is structurally empty and the other structurally contains a
    /// provably-non-empty (length >= 1) leaf. Always sound: a concat containing a
    /// unit / non-empty literal has length >= 1, which can never equal the empty
    /// sequence's length 0, for ANY model. This catches `(= (seq.++ s (seq.unit
    /// x)) (as seq.empty ...))` under set-logic ALL routing where solve_seq_lia's
    /// length abstraction does not run (#seq-empty-WS). Matches only the bare `=`
    /// (the caller passes the raw assertion; a negated equality is a `Not`).
    fn structural_empty_vs_nonempty(executor: &Executor, term: TermId) -> bool {
        let TermData::App(sym, args) = executor.ctx.terms.get(term) else {
            return false;
        };
        if sym.name() != "=" || args.len() != 2 {
            return false;
        }
        const D: u32 = 64;
        let (a, b) = (args[0], args[1]);
        (Self::seq_struct_empty(executor, a, D) && Self::seq_has_nonempty_leaf(executor, b, D))
            || (Self::seq_struct_empty(executor, b, D)
                && Self::seq_has_nonempty_leaf(executor, a, D))
    }

    /// Model-free proof that `term` is the EMPTY sequence under the asserted
    /// constraints. Covers (in addition to `seq_struct_empty`) a
    /// `(seq.extract src off len)` whose result is empty for EVERY model:
    ///   * `src` is structurally empty (nothing to extract), OR
    ///   * the constraints force `off >= (seq.len src)` — a start offset at or
    ///     past the end yields the empty extract. The only forcing pattern we
    ///     recognise is a top-level asserted `(= (seq.unit off) (seq.unit
    ///     (seq.len src)))` (either argument order), which by seq.unit
    ///     injectivity entails `off = (seq.len src)`, hence `off >= len(src)`.
    /// All sound: every recognised case yields the empty sequence in SMT-LIB
    /// regardless of the (under-specified) model values (#seq-extract-empty-off).
    fn seq_extract_provably_empty(executor: &Executor, term: TermId) -> bool {
        let TermData::App(sym, args) = executor.ctx.terms.get(term) else {
            return false;
        };
        if sym.name() != "seq.extract" || args.len() != 3 {
            return false;
        }
        let (src, off, _len) = (args[0], args[1], args[2]);
        if Self::seq_struct_empty(executor, src, 64) {
            return true;
        }
        // Look for an asserted seq.unit injectivity equality linking `off` to
        // `(seq.len src)`.
        for &a in &executor.ctx.assertions {
            let TermData::App(esym, eargs) = executor.ctx.terms.get(a) else {
                continue;
            };
            if esym.name() != "=" || eargs.len() != 2 {
                continue;
            }
            let (Some(u0), Some(u1)) = (
                Self::seq_unit_arg(executor, eargs[0]),
                Self::seq_unit_arg(executor, eargs[1]),
            ) else {
                continue;
            };
            // {u0, u1} == {off, (seq.len src)} structurally.
            let is_off = |t: TermId| t == off;
            let is_len_src = |t: TermId| Self::is_seq_len_of(executor, t, src);
            if (is_off(u0) && is_len_src(u1)) || (is_off(u1) && is_len_src(u0)) {
                return true;
            }
        }
        false
    }

    /// If `term` is `(seq.unit e)`, return `Some(e)`.
    fn seq_unit_arg(executor: &Executor, term: TermId) -> Option<TermId> {
        match executor.ctx.terms.get(term) {
            TermData::App(sym, args) if sym.name() == "seq.unit" && args.len() == 1 => {
                Some(args[0])
            }
            _ => None,
        }
    }

    /// True when `term` is `(seq.len src)`.
    fn is_seq_len_of(executor: &Executor, term: TermId, src: TermId) -> bool {
        matches!(
            executor.ctx.terms.get(term),
            TermData::App(sym, args)
                if sym.name() == "seq.len" && args.len() == 1 && args[0] == src
        )
    }

    /// Model-free refutation of a NEGATED contains `(not (seq.contains H M))`
    /// where M is provably the empty sequence: `(seq.contains H empty)` is TRUE
    /// for every H (empty is a subsequence of everything), so the negation is
    /// definitively false. Sound — only fires when M is provably empty
    /// (#seq-contains-empty).
    fn structural_negated_contains_empty(executor: &Executor, term: TermId) -> bool {
        let TermData::Not(inner) = executor.ctx.terms.get(term) else {
            return false;
        };
        let TermData::App(sym, args) = executor.ctx.terms.get(*inner) else {
            return false;
        };
        if sym.name() != "seq.contains" || args.len() != 2 {
            return false;
        }
        let needle = args[1];
        Self::seq_struct_empty(executor, needle, 64)
            || Self::seq_extract_provably_empty(executor, needle)
    }
}

impl DefinitiveEval for SeqOracle {
    fn name(&self) -> &'static str {
        "sequences"
    }

    fn is_applicable(&self, executor: &Executor, _model: &Model, term: TermId) -> bool {
        let inner = match executor.ctx.terms.get(term) {
            TermData::Not(inner) => *inner,
            _ => term,
        };
        let TermData::App(sym, args) = executor.ctx.terms.get(inner) else {
            return false;
        };
        matches!(
            sym.name(),
            // Native seq predicates.
            "=" | "distinct"
                | "seq.contains"
                | "seq.prefixof"
                | "seq.suffixof"
                // Arithmetic comparisons over an integer-returning seq op
                // (seq.indexof / seq.len / seq.nth / seq.last_indexof). When the
                // seq operands resolve to concrete sequences the evaluator
                // computes the EXACT SMT-LIB result (e.g. seq.indexof of a
                // non-empty needle in an empty haystack = -1), so an asserted
                // bound that contradicts it (`(< 2 (seq.indexof empty [8] _))`)
                // evaluates to a definitive Bool(false) and is rejected
                // (#seq-indexof-arith-bound). If any seq operand is unresolved
                // the evaluator returns a non-Bool value, so this never
                // over-demotes a model-extraction gap.
                | "<" | "<=" | ">" | ">="
        ) && !args.is_empty()
            && Self::mentions_seq_op(executor, inner)
    }

    fn definitive_false(&self, executor: &Executor, model: &Model, term: TermId) -> bool {
        Self::structural_empty_vs_nonempty(executor, term)
            || Self::structural_negated_contains_empty(executor, term)
            || matches!(executor.evaluate_term(model, term), EvalValue::Bool(false))
    }
}

/// Whether `term`'s fully-EXPANDED tree (shared subterms counted once per
/// occurrence, i.e. the size the dt-tautology normalizer actually walks) stays
/// within `budget` nodes. Decrements `budget` while walking; `false` as soon as
/// it is exhausted. Cheap admission check for the #g4-dt-taut strict-gate guard.
fn term_tree_size_within(executor: &Executor, term: TermId, budget: &mut u32) -> bool {
    if *budget == 0 {
        return false;
    }
    *budget -= 1;
    match executor.ctx.terms.get(term) {
        TermData::App(_, args) => args
            .iter()
            .all(|&a| term_tree_size_within(executor, a, budget)),
        TermData::Not(x) => term_tree_size_within(executor, *x, budget),
        TermData::Ite(c, t, e) => {
            term_tree_size_within(executor, *c, budget)
                && term_tree_size_within(executor, *t, budget)
                && term_tree_size_within(executor, *e, budget)
        }
        TermData::Let(bindings, body) => {
            bindings
                .iter()
                .all(|(_, v)| term_tree_size_within(executor, *v, budget))
                && term_tree_size_within(executor, *body, budget)
        }
        _ => true,
    }
}

/// Apply every registered oracle. Returns `Some(name)` of the first
/// oracle that declares the assertion definitively violated, or `None`
/// if no oracle fires.
///
/// Caller must treat a `Some(_)` return as a hard violation and degrade
/// SAT to Unknown (soundness over completeness).
pub(crate) fn check_definitive_false(
    executor: &Executor,
    model: &Model,
    term: TermId,
) -> Option<&'static str> {
    // Order matters only for diagnostic clarity. Every oracle with
    // `is_applicable=true` and `definitive_false=true` is a valid
    // rejection. Stop at the first match.
    let oracles: &[&dyn DefinitiveEval] = &[
        &StringOracle,
        &ArrayOracle,
        &ArithmeticOracle,
        &IteDefinitionOracle,
        &IntegralityOracle,
        &DtOracle,
        &DtFieldOracle,
        &SeqOracle,
    ];
    for oracle in oracles {
        if oracle.is_applicable(executor, model, term)
            && oracle.definitive_false(executor, model, term)
        {
            // DATATYPE-MODEL EVALUATION-CONSISTENCY GUARDS (#g4-dt-consistency).
            // An oracle that demotes via the raw (decoupled) `evaluate_term`, or
            // via a `dt_mat_canonical` that cannot canonicalize a datatype-carrying
            // ARRAY, can OVER-DEMOTE a datatype assertion the candidate model
            // actually SATISFIES — because datatype-variable evaluation reads a
            // decoupled EUF element rather than the variable's constructor
            // definition, and injected DT-congruence/round-trip axioms are
            // tautologies the model satisfies. ay's own eager DT-axiom injection
            // (`dt_datatype_value_equality_congruence_axioms` / `dt_selector_axioms`)
            // makes such assertions ubiquitous; over-demoting them wrongly drops a
            // genuine Sat to Unknown. We SKIP the demotion ONLY on a POSITIVE proof
            // that the assertion holds — never suppressing a real violation:
            //
            // (1) The assertion is a datatype TAUTOLOGY provable from the free
            //     datatype + Boolean theory alone (tester/selector-over-
            //     constructor, injectivity/distinctness, Boolean folding) —
            //     MODEL-INDEPENDENT, no array canonicalization. This confirms
            //     ay's OWN injected DT congruence/tester/selector axioms
            //     (`(= (is-Ctor Y) (= Y (Ctor (sel_i Y)..)))` etc.). Honor only
            //     `Some(true)` (a proof the assertion holds in EVERY model); a
            //     `Some(false)` genuine violation is left to demote.
            if matches!(dt_axiom_bool(executor, term, 4000), Some(true)) {
                continue;
            }
            // (1b) The registry-aware tautology recognizer (#g4-dt-taut:
            //     ay-model-check's `norm::` normalizer + read-over-equality
            //     congruence) proves shapes the classic `dt_axiom_bool` cannot —
            //     notably the CONSTRUCTOR-CHARACTERIZATION disjunction
            //     `(or (= x (C (sel1 x) .. (selk x))) (not (is-C x)))` ay's DT
            //     axiom layer injects, which a per-term-inconsistent datatype
            //     reconstruction can wrongly evaluate false. MODEL-INDEPENDENT:
            //     `true` is a structural proof the assertion holds in EVERY
            //     model, so skipping the demotion can never admit a false SAT —
            //     it mirrors observation.rs's existing #g4-dt-taut delegation.
            //     Scoped to the datatype-field oracle: that is the only oracle
            //     whose materialized re-evaluation wrongly falsifies these
            //     injected DT axiom shapes, and the normalizer's structural key
            //     serialization is too costly to run on every huge non-DT
            //     rejection (e.g. `ite_uf_definition` on dt-carrying-array VCs).
            //     Scoping (both purely restrictive, so still fail-closed):
            //     * NOT on datatype-carrying-array problems — their
            //       `datatype-field` rejections are handled by the dedicated
            //       #g4-dt-defer machinery, and short-circuiting past the first
            //       rejection re-walks the whole assertion battery through the
            //       expensive materialized oracle on every strict re-verdict
            //       (measured 5s -> 90s+, deepening budget exhausted and a
            //       genuine sat degraded to unknown, on the g3 twin).
            //     * EXPANDED-TREE size bounded: the normalizer's structural
            //       keying expands the term DAG to a tree; the injected DT
            //       characterization axioms this guard exists for are tiny.
            if oracle.name() == "datatype-field"
                && !executor.problem_has_datatype_carrying_array()
                && term_tree_size_within(executor, term, &mut 4096u32)
                && executor.term_is_datatype_tautology(term)
            {
                continue;
            }
            // (2) The MATERIALIZED re-evaluation pins every DT boundary to its TRUE
            //     model constructor (`dt_constructor_of` — the unambiguous
            //     model-true tester's ctor, else `None` → Unknown, so it can NEVER
            //     fabricate a wrong constructor) and fails closed to Unknown on any
            //     extraction gap. A materialized `Bool(true)` is therefore a proof
            //     the assertion holds under the true model; skip only on that.
            //     `Bool(false)`/`Unknown` keep the demotion (fail-closed) — a
            //     genuine datatype violation materializes to `Bool(false)`.
            if executor.contains_datatype_term(term)
                && matches!(executor.dt_mat_eval(model, term, 64), EvalValue::Bool(true))
            {
                continue;
            }
            return Some(oracle.name());
        }
    }
    None
}

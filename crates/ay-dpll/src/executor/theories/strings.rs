// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! String theory solving for QF_S.
//!
//! Routes QF_S through `StringSolver` from `ay-strings` crate.
//! The QF_SLIA pipeline is in `strings_lia.rs`.
//! String analysis helpers (length bounds, alphabet, candidates) are in
//! `strings_analysis.rs`.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Constant, TermData};
use ay_core::{StringLemma, TermId, Tseitin};
use ay_sat::SatResult;
use ay_strings::StringSolver;

use crate::executor_types::{Result, SolveResult, UnknownReason};
use crate::DpllT;

use super::super::Executor;
use super::skolem_cache::ExecutorSkolemCache;
use super::strings_analysis::MAX_CONSECUTIVE_DUPLICATE_LEMMAS;
use super::{debug_auflia_enabled, MAX_STRING_LEMMA_ITERATIONS};

// String analysis helpers (collect_decomposition_concat_terms,
// detect_bounded_string_vars, collect_alphabet, generate_candidates,
// LengthBound, MAX_PIVOT_CANDIDATES) live in strings_analysis.rs.

impl Executor {
    /// Solve QF_S using the string theory solver.
    ///
    /// Uses step-based DPLL(T) with `StringSolver` for theory checking.
    /// The string solver detects constant conflicts (x = "a" ∧ x = "b"),
    /// containment cycles, and disequality violations.
    ///
    /// Uses `solve_step()` (lazy theory checking after full SAT assignment)
    /// instead of `solve_eager()` (eager theory propagation during BCP).
    /// This enables future split/lemma handling for Phase C variable reasoning.
    /// Generate `str.<` / `str.<=` lexicographic-order axioms over the atoms in
    /// `assertions`, to be appended before Tseitin so the SAT layer can refute
    /// order contradictions (`x < y ∧ y < x`, `x < y ∧ y < z ∧ z < x`,
    /// `x ≤ y ∧ y ≤ x ∧ x ≠ y`). Every axiom is a VALID fact about the strict
    /// total lexicographic order, so this is sound by construction — it can only
    /// prove more UNSATs, never change a verdict. Bounded: acts only over the
    /// distinct string operands appearing in order atoms, and skips the cubic
    /// transitivity rule once that set is large.
    fn string_order_axioms(&mut self, assertions: &[TermId]) -> Vec<TermId> {
        const TRANSITIVITY_OPERAND_CAP: usize = 12;
        // Bounds the O(n^2) antisymmetry/totality/relationship clauses. Kept
        // modest so a str.<-heavy instance cannot blow up preprocessing.
        const OPERAND_CAP: usize = 32;

        // Collect (is_strict, a, b) order atoms reachable from the assertions.
        let mut seen: HashSet<TermId> = HashSet::default();
        let mut stack: Vec<TermId> = assertions.to_vec();
        let mut strict_present = false;
        let mut non_strict_present = false;
        let mut operands: Vec<TermId> = Vec::new();
        let mut op_seen: HashSet<TermId> = HashSet::default();
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            match self.ctx.terms.get(t) {
                TermData::App(sym, args) => {
                    let name = sym.name();
                    if (name == "str.<" || name == "str.<=") && args.len() == 2 {
                        if name == "str.<" {
                            strict_present = true;
                        } else {
                            non_strict_present = true;
                        }
                        for t in [args[0], args[1]] {
                            if op_seen.insert(t) {
                                operands.push(t);
                            }
                        }
                    }
                    for &a in args {
                        stack.push(a);
                    }
                }
                // Recurse through boolean structure so an order atom under a
                // `not`/`ite` (e.g. `(not (str.<= x y))`) is still collected.
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, th, el) => {
                    stack.push(*c);
                    stack.push(*th);
                    stack.push(*el);
                }
                _ => {}
            }
        }
        if operands.is_empty() || operands.len() > OPERAND_CAP {
            return Vec::new();
        }

        let mk = |terms: &mut ay_core::TermStore, strict: bool, a: TermId, b: TermId| {
            let name = if strict { "str.<" } else { "str.<=" };
            terms.mk_app(ay_core::Symbol::named(name), [a, b], ay_core::Sort::Bool)
        };
        let mut axioms: Vec<TermId> = Vec::new();

        // Antisymmetry over each unordered pair.
        for i in 0..operands.len() {
            for j in (i + 1)..operands.len() {
                let (a, b) = (operands[i], operands[j]);
                if strict_present {
                    let ab = mk(&mut self.ctx.terms, true, a, b);
                    let ba = mk(&mut self.ctx.terms, true, b, a);
                    let both = self.ctx.terms.mk_and(vec![ab, ba]);
                    axioms.push(self.ctx.terms.mk_not(both));
                }
                if non_strict_present {
                    let ab = mk(&mut self.ctx.terms, false, a, b);
                    let ba = mk(&mut self.ctx.terms, false, b, a);
                    let both = self.ctx.terms.mk_and(vec![ab, ba]);
                    let eq = self.ctx.terms.mk_eq(a, b);
                    axioms.push(self.ctx.terms.mk_implies(both, eq));
                }
                // Totality `a ≤ b ∨ b ≤ a` and the strict/non-strict link
                // `a < b → a ≤ b`, `a ≤ b → (a < b ∨ a = b)`. All valid for the
                // strict total lexicographic order, so they only add correct
                // facts (they also let a str.<-only or str.<=-only problem reason
                // across the two relations).
                let le_ab = mk(&mut self.ctx.terms, false, a, b);
                let le_ba = mk(&mut self.ctx.terms, false, b, a);
                axioms.push(self.ctx.terms.mk_or(vec![le_ab, le_ba]));
                let eq = self.ctx.terms.mk_eq(a, b);
                for (p, q) in [(a, b), (b, a)] {
                    let lt = mk(&mut self.ctx.terms, true, p, q);
                    let le = mk(&mut self.ctx.terms, false, p, q);
                    axioms.push(self.ctx.terms.mk_implies(lt, le));
                    let lt2 = mk(&mut self.ctx.terms, true, p, q);
                    let le2 = mk(&mut self.ctx.terms, false, p, q);
                    let disj = self.ctx.terms.mk_or(vec![lt2, eq]);
                    axioms.push(self.ctx.terms.mk_implies(le2, disj));
                }
            }
        }

        // Transitivity of str.< over ordered triples (bounded).
        if strict_present && operands.len() <= TRANSITIVITY_OPERAND_CAP {
            for ai in 0..operands.len() {
                for bi in 0..operands.len() {
                    if bi == ai {
                        continue;
                    }
                    for ci in 0..operands.len() {
                        if ci == ai || ci == bi {
                            continue;
                        }
                        let (a, b, c) = (operands[ai], operands[bi], operands[ci]);
                        let ab = mk(&mut self.ctx.terms, true, a, b);
                        let bc = mk(&mut self.ctx.terms, true, b, c);
                        let ac = mk(&mut self.ctx.terms, true, a, c);
                        let prem = self.ctx.terms.mk_and(vec![ab, bc]);
                        axioms.push(self.ctx.terms.mk_implies(prem, ac));
                    }
                }
            }
        }
        axioms
    }

    /// Generate `str.prefixof`/`str.suffixof` ⟹ `str.contains` relational
    /// axioms: `(str.prefixof p x) ⟹ (str.contains x p)` and
    /// `(str.suffixof s x) ⟹ (str.contains x s)`. A prefix or suffix is a
    /// substring, so each is a VALID theorem — like [`Self::string_order_axioms`]
    /// this is sound by construction: it can only derive more (correct) UNSATs
    /// (e.g. refuting `prefixof p x ∧ ¬contains x p`), never flip a verdict. The
    /// constructed `(str.contains x p)` is hash-consed to any already-present
    /// occurrence (notably an asserted, possibly negated, `str.contains`), so the
    /// SAT layer links the new implication to it. Without these lemmas AY
    /// returned `unknown` where z3 proves `unsat` (#string-predicate-propagation).
    /// Bounded so a predicate-heavy instance cannot blow up preprocessing.
    pub(in crate::executor) fn string_predicate_relation_axioms(
        &mut self,
        assertions: &[TermId],
    ) -> Vec<TermId> {
        const RELATION_CAP: usize = 256;
        let mut seen: HashSet<TermId> = HashSet::default();
        let mut stack: Vec<TermId> = assertions.to_vec();
        // (predicate_term, haystack x, needle p) for `contains(x, p)`.
        let mut relations: Vec<(TermId, TermId, TermId)> = Vec::new();
        // (replace_term, haystack x, needle s) for the idempotence lemma
        // `¬contains(x,s) ⟹ (str.replace x s t) = x`.
        let mut replaces: Vec<(TermId, TermId, TermId)> = Vec::new();
        // (substr_term, haystack x) for the containment lemma
        // `contains(x, (str.substr x i len))` — a substring (or "") is always
        // contained. Covers `str.at` too (it lowers to `str.substr _ _ 1`).
        let mut substrs: Vec<(TermId, TermId)> = Vec::new();
        // (is_prefix, atom_term, small=args[0], big=args[1]) for prefixof /
        // suffixof TRANSITIVITY: `p⊑x ∧ x⊑y ⟹ p⊑y` (same relation). `is_prefix`
        // keeps prefixof and suffixof chains separate (each is transitive on its
        // own). Capped so a predicate-heavy instance cannot blow up the O(n²)
        // chain scan.
        const ORDER_ATOM_CAP: usize = 48;
        let mut order_atoms: Vec<(bool, TermId, TermId, TermId)> = Vec::new();
        // (prefixof_term, x, prefix_string) for `str.prefixof(p, x)` with a
        // CONSTANT prefix `p`. Used to force `x`'s leading characters.
        let mut const_prefix_atoms: Vec<(TermId, TermId, String)> = Vec::new();
        // (x, i, substr_term) for each single-character extraction
        // `str.substr(x, i, 1)` with a constant index `i` — the lowered form of
        // `str.at(x, i)` (the frontend rewrites `(str.at x i)` to it).
        let mut single_char_substrs: Vec<(TermId, usize, TermId)> = Vec::new();
        // (indexof_term, haystack s, needle n, offset_is_literal_zero) for each
        // `(str.indexof s n i)`. Used for the indexof↔contains coupling below.
        let mut indexofs: Vec<(TermId, TermId, TermId, bool)> = Vec::new();
        // (haystack, needle) pairs that already appear in a `str.contains` atom.
        // The indexof↔contains coupling is emitted ONLY for indexof terms whose
        // (s, n) matches one of these — so we never INTRODUCE a fresh contains
        // term. Introducing one would spuriously trigger the eager
        // contains-decomposition pre-pass and stall the indexof witness search on
        // indexof-only SAT problems (a completeness regression). Every measured
        // coupling gap has a contains atom already, so this loses no target win.
        let mut contains_pairs: HashSet<(TermId, TermId)> = HashSet::default();
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            match self.ctx.terms.get(t).clone() {
                TermData::App(sym, args) => {
                    let name = sym.name();
                    if (name == "str.prefixof" || name == "str.suffixof") && args.len() == 2 {
                        // `(str.prefixof p x)` / `(str.suffixof s x)`: args[0]=p/s
                        // (needle), args[1]=x (haystack). contains(x, needle).
                        if relations.len() < RELATION_CAP {
                            relations.push((t, args[1], args[0]));
                        }
                        if order_atoms.len() < ORDER_ATOM_CAP {
                            order_atoms.push((name == "str.prefixof", t, args[0], args[1]));
                        }
                        // Constant prefix: record it so the leading characters of
                        // `x` can be pinned (see the char-forcing axioms below).
                        if name == "str.prefixof" && const_prefix_atoms.len() < RELATION_CAP {
                            if let TermData::Const(Constant::String(p)) =
                                self.ctx.terms.get(args[0]).clone()
                            {
                                const_prefix_atoms.push((t, args[1], p));
                            }
                        }
                    } else if name == "str.replace" && args.len() == 3 {
                        // `(str.replace x s t)`: args[0]=x (haystack), args[1]=s
                        // (needle). If x does not contain s, replace is a no-op.
                        if replaces.len() < RELATION_CAP {
                            replaces.push((t, args[0], args[1]));
                        }
                    } else if name == "str.substr" && args.len() == 3 {
                        // `(str.substr x i len)`: args[0]=x (haystack). Its result
                        // is a contiguous piece of x (or "" for an out-of-range
                        // index / non-positive length), so x always contains it.
                        // `str.at` lowers to `(str.substr x i 1)`, so this also
                        // links `str.at` results to `contains`.
                        //
                        // P2 (`AY_STR_P2=1`) carve-out: substr terms with
                        // NON-CONSTANT bounds are now eagerly reduced
                        // (`x = pre ++ skt ++ suf` + exact length coupling), which
                        // subsumes this containment fact structurally. Emitting it
                        // anyway introduces a `contains(x, substr)` atom whose
                        // eager decomposition adds a SECOND, competing skolem
                        // concat for `x` and poisons normal-form computation
                        // (observed: Leetcode isNumber unsat → unknown). Skipping
                        // a VALID-but-redundant axiom is always sound.
                        let p2_reduced_symbolic_bounds =
                            super::strings_preregister::str_p2_enabled()
                                && !(matches!(
                                    self.ctx.terms.get(args[1]),
                                    TermData::Const(Constant::Int(_))
                                ) && matches!(
                                    self.ctx.terms.get(args[2]),
                                    TermData::Const(Constant::Int(_))
                                ));
                        if substrs.len() < RELATION_CAP && !p2_reduced_symbolic_bounds {
                            substrs.push((t, args[0]));
                        }
                        // Single-character extraction `str.substr(x, i, 1)` with a
                        // constant index `i`: the lowered `str.at(x, i)`. Record
                        // `(x, i, term)` so a constant prefix can pin it.
                        if single_char_substrs.len() < RELATION_CAP {
                            let idx = match self.ctx.terms.get(args[1]) {
                                TermData::Const(Constant::Int(n)) => usize::try_from(n).ok(),
                                _ => None,
                            };
                            let is_unit_len = matches!(
                                self.ctx.terms.get(args[2]),
                                TermData::Const(Constant::Int(n)) if usize::try_from(n).ok() == Some(1)
                            );
                            if let (Some(i), true) = (idx, is_unit_len) {
                                single_char_substrs.push((args[0], i, t));
                            }
                        }
                    } else if name == "str.contains" && args.len() == 2 {
                        // Record the (haystack, needle) so the indexof coupling
                        // can gate on an already-present contains atom.
                        contains_pairs.insert((args[0], args[1]));
                    } else if name == "str.indexof" && (args.len() == 2 || args.len() == 3) {
                        // `(str.indexof s n i)` (offset `i` defaults to 0 when the
                        // 2-arg form is used). Record `(term, s, n, offset==0)` for
                        // the indexof↔contains coupling axioms below.
                        if indexofs.len() < RELATION_CAP {
                            let offset_is_zero = if args.len() == 2 {
                                true
                            } else {
                                matches!(
                                    self.ctx.terms.get(args[2]),
                                    TermData::Const(Constant::Int(n)) if usize::try_from(n).ok() == Some(0)
                                )
                            };
                            indexofs.push((t, args[0], args[1], offset_is_zero));
                        }
                    }
                    for &a in &args {
                        stack.push(a);
                    }
                }
                TermData::Not(inner) => stack.push(inner),
                TermData::Ite(c, th, el) => {
                    stack.push(c);
                    stack.push(th);
                    stack.push(el);
                }
                TermData::Let(bindings, body) => {
                    for (_, v) in &bindings {
                        stack.push(*v);
                    }
                    stack.push(body);
                }
                _ => {}
            }
        }
        let mut axioms: Vec<TermId> = Vec::with_capacity(relations.len() + replaces.len());
        for (pred, hay, needle) in relations {
            let contains = self.ctx.terms.mk_app(
                ay_core::Symbol::named("str.contains"),
                [hay, needle],
                ay_core::Sort::Bool,
            );
            axioms.push(self.ctx.terms.mk_implies(pred, contains));
        }
        // Replace idempotence: `¬(str.contains x s) ⟹ (str.replace x s t) = x`.
        // Replacing the first occurrence of a needle that does not occur is a
        // no-op — a VALID theorem (SMT-LIB `str.replace`), so it only adds a
        // correct fact. (Empty `s` never triggers it: `contains(x,"")` is always
        // true, so `¬contains` is false and the implication is vacuous.)
        for (replace_term, hay, needle) in replaces {
            let contains = self.ctx.terms.mk_app(
                ay_core::Symbol::named("str.contains"),
                [hay, needle],
                ay_core::Sort::Bool,
            );
            let not_contains = self.ctx.terms.mk_not(contains);
            let eq = self.ctx.terms.mk_eq(replace_term, hay);
            axioms.push(self.ctx.terms.mk_implies(not_contains, eq));
        }
        // Substring containment: `contains(x, (str.substr x i len))`. A substring
        // (or the empty string for an out-of-range/degenerate slice) is always
        // contained in the source — a VALID unconditional theorem, so it only
        // adds a correct fact and can never flip a verdict's soundness. Closes
        // the `¬contains(x, str.at(x,i))`-with-nonempty-`at` unsat class that AY
        // otherwise leaves `unknown`. (empty `""` needle: contains(x,"") is
        // trivially true, so the axiom is a harmless tautology there.)
        for (substr_term, hay) in substrs {
            let contains = self.ctx.terms.mk_app(
                ay_core::Symbol::named("str.contains"),
                [hay, substr_term],
                ay_core::Sort::Bool,
            );
            axioms.push(contains);
        }
        // Prefix character determination (#4118, re-homed): a constant prefix
        // `str.prefixof(p, x)` forces `x[i] = p[i]` for every position `i` of
        // `p`. For each single-character extraction `str.substr(x, i, 1)` (the
        // lowered `str.at(x, i)`) already present in the formula, emit
        //   `str.prefixof(p, x) => str.substr(x, i, 1) = p[i]`.
        // This lets the string core solver refute a contradictory character
        // assignment — e.g. `str.prefixof "ab" x` with `(str.at x 0) = "c"` is
        // UNSAT because `x[0]` is forced to `"a"`. VALID by construction:
        // `prefixof(p, x)` guarantees `len(x) >= len(p)`, so position `i < len(p)`
        // is in bounds and `str.substr(x, i, 1)` is exactly the single character
        // `x[i] = p[i]`. Unlike the prefix DECOMPOSITION in
        // `preregister_contains_decompositions` (suppressed when a coexisting
        // `str.contains` claims `x`), this is an unconditional top-level axiom,
        // so the character link is never lost.
        for (pred, x, p) in &const_prefix_atoms {
            let p_chars: Vec<char> = p.chars().collect();
            for &(sx, i, substr_term) in &single_char_substrs {
                if sx != *x || i >= p_chars.len() {
                    continue;
                }
                let ch_str = self.ctx.terms.mk_string(p_chars[i].to_string());
                let ch_eq = self.ctx.terms.mk_eq(substr_term, ch_str);
                axioms.push(self.ctx.terms.mk_implies(*pred, ch_eq));
            }
        }
        // Prefixof / suffixof TRANSITIVITY (chain-matched): whenever both
        // `pred(a, b)` and `pred(b, c)` appear as atoms (same relation, middle
        // term `b` shared), emit `pred(a,b) ∧ pred(b,c) ⟹ pred(a,c)`. Both
        // `str.prefixof` and `str.suffixof` are transitive, so this is a VALID
        // fact — sound by construction (only proves more UNSATs). Chain-matched
        // (fires only when a real chain exists) so it emits few axioms; the O(n²)
        // scan is bounded by ORDER_ATOM_CAP.
        for i in 0..order_atoms.len() {
            for j in 0..order_atoms.len() {
                if i == j {
                    continue;
                }
                let (pi, ti, a, b) = order_atoms[i];
                let (pj, tj, b2, c) = order_atoms[j];
                if pi == pj && b == b2 {
                    let name = if pi { "str.prefixof" } else { "str.suffixof" };
                    let concl = self.ctx.terms.mk_app(
                        ay_core::Symbol::named(name),
                        [a, c],
                        ay_core::Sort::Bool,
                    );
                    let prem = self.ctx.terms.mk_and(vec![ti, tj]);
                    axioms.push(self.ctx.terms.mk_implies(prem, concl));
                }
            }
        }
        // indexof↔contains coupling. Two VALID theorem families (both z3-confirmed
        // over symbolic haystack/needle, a3_f1/a3_f2):
        //   (1) any offset i: `(str.indexof s n i) >= 0 ⟹ (str.contains s n)` — a
        //       found occurrence at/after any start is an occurrence.
        //   (2) offset LITERALLY 0 only: `(str.contains s n) ⟹ (str.indexof s n 0)
        //       >= 0` — offset 0 precedes every occurrence, so a present needle is
        //       found from 0. This is NOT valid for a nonzero offset (an occurrence
        //       before the offset makes indexof = -1 while contains is true — the
        //       twin a3_f2bad is SAT), so family (2) is emitted ONLY when the offset
        //       is the literal 0.
        // Sound by construction: each is universally valid, so it only derives more
        // (correct) UNSATs and never flips a real model. With the existing
        // `indexof >= -1` range axiom, (2) refutes `indexof(s,n,0) = -1 ∧ contains`.
        let zero = self.ctx.terms.mk_int(num_bigint::BigInt::from(0));
        for (indexof_term, hay, needle, offset_is_zero) in indexofs {
            // Gate on an already-present `str.contains(hay, needle)` atom so we
            // never introduce a fresh contains term (see contains_pairs above).
            if !contains_pairs.contains(&(hay, needle)) {
                continue;
            }
            let ge_zero = self.ctx.terms.mk_ge(indexof_term, zero);
            let contains = self.ctx.terms.mk_app(
                ay_core::Symbol::named("str.contains"),
                [hay, needle],
                ay_core::Sort::Bool,
            );
            // family (1): indexof >= 0 ⟹ contains (any offset).
            axioms.push(self.ctx.terms.mk_implies(ge_zero, contains));
            // family (2): contains ⟹ indexof >= 0 (offset 0 only).
            if offset_is_zero {
                axioms.push(self.ctx.terms.mk_implies(contains, ge_zero));
            }
        }
        axioms
    }

    pub(in crate::executor) fn solve_strings(&mut self) -> Result<SolveResult> {
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }

        use crate::SolveStepResult;

        let proof_enabled = self.produce_proofs_enabled();

        if proof_enabled {
            self.proof_tracker.set_theory("Strings");
            for (idx, &assertion) in self.ctx.assertions.iter().enumerate() {
                let _ = self
                    .proof_tracker
                    .add_assumption(assertion, Some(format!("h{idx}")));
            }
        }

        // Validation-gated witness pre-pass (QF_S completeness, #-strings).
        //
        // Shared with the QF_SLIA pipeline (`solve_strings_lia`): a variable
        // constrained only by `str.prefixof`/`str.suffixof`, or a positive
        // `str.contains`/`str.prefixof`/`str.suffixof` over a partially-grounded
        // `str.++`, has concrete minimal witnesses that the unguided CEGAR loop
        // does not find (it stalls on length splits and returns Unknown). We
        // *try* each candidate as a hard assumption and trust SAT ONLY after
        // full model + assumption validation, so a wrong guess is harmless: it
        // falls through to the normal pipeline, and a genuinely-UNSAT formula
        // can never be reported SAT (validation rejects it) nor UNSAT (UNSAT
        // candidates are skipped, never globally concluded). The depth guard
        // prevents re-entry: each witness solve recurses through the solver, and
        // the inner call must run the normal pipeline rather than re-detecting
        // witnesses.
        if self.pivot_enum_depth == 0 {
            if let Some(result) = self.try_prefix_suffix_witnesses()? {
                return Ok(result);
            }
            if let Some(result) = self.try_concat_predicate_witnesses()? {
                return Ok(result);
            }
            // Bounded regex-membership × length decision (TARGET strings_regex_len).
            if let Some(result) = self.try_regex_length_witnesses()? {
                return Ok(result);
            }
            // Concat-equals-constant single-free-variable witness (S2).
            if let Some(result) = self.try_concat_constant_witnesses()? {
                return Ok(result);
            }
            // Nielsen word-equation decision (Track A3 M1): symbolic word
            // equations like `x ++ "ab" = "a" ++ y`. SAT only after full
            // model validation; UNSAT only from exhaustive Nielsen closure.
            if let Some(result) = self.try_word_equation_nielsen()? {
                return Ok(result);
            }
            // W4 (`AY_STR_W4=1`, default off): length-indexed per-position
            // character witness synthesizer (see `strings_w4.rs`). Same
            // validated-candidate contract as the passes above — a failed
            // synthesis falls through and never concludes UNSAT.
            if super::strings_w4::str_w4_enabled() {
                if let Some(result) = self.try_per_position_witnesses()? {
                    return Ok(result);
                }
            }
            // W6 (`AY_STR_W6=1`, default off): regex-driven joint word
            // construction (see `strings_w6.rs`). Same validated-candidate
            // contract — a failed construction never concludes UNSAT.
            if super::strings_w6::str_w6_enabled() {
                if let Some(result) = self.try_regex_word_witnesses()? {
                    return Ok(result);
                }
            }
        }

        // Lift ITEs from equalities (same as EUF path)
        let mut lifted_assertions = self.ctx.terms.lift_arithmetic_ite_all(&self.ctx.assertions);
        lifted_assertions = self.fold_ground_string_ops(&lifted_assertions);
        if lifted_assertions.iter().any(|&term| {
            matches!(
                self.ctx.terms.get(term),
                TermData::Const(Constant::Bool(false))
            )
        }) {
            return Ok(SolveResult::unsat());
        }
        lifted_assertions.retain(|&term| {
            !matches!(
                self.ctx.terms.get(term),
                TermData::Const(Constant::Bool(true))
            )
        });
        // Concat-needle contains/prefix/suffix refutation (#str-concat-needle):
        // a positively-asserted `str.contains`/`str.prefixof`/`str.suffixof`
        // over a constant haystack whose pattern is a `str.++` with constant
        // leaves too long for, or absent from, the haystack is structurally
        // UNSAT regardless of the free leaves. Decide it precisely here so the
        // QF_S path returns `unsat` rather than relying on the fail-closed
        // model-validation fallback (which would only yield `unknown`).
        if self.has_unsatisfiable_positive_concat_predicate(&lifted_assertions) {
            return Ok(SolveResult::unsat());
        }

        if lifted_assertions.is_empty() {
            // All assertions folded to true after ITE-lifting and ground constant
            // folding. The formula is trivially satisfiable. Mark as validated
            // (not skip_model_eval) so finalize_sat_model_validation is not
            // called and the postcondition in check_sat is satisfied (#8456).
            self.last_model = Some(super::super::model::Model {
                sat_model: Vec::new(),
                term_to_var: HashMap::default(),
                bool_overrides: HashMap::default(),
                euf_model: None,
                array_model: None,
                lra_model: None,
                lia_model: None,
                bv_model: None,
                fp_model: None,
                string_model: None,
                seq_model: None,
                completed_values: HashMap::default(),
                dt_ground: HashMap::default(),
                dt_pins: HashMap::default(),
            });
            self.last_model_validated = true;
            return Ok(SolveResult::Sat);
        }

        // Pre-register eager str.contains decompositions (Phase 2, #3402).
        // Creates skolem decompositions before Tseitin so the SAT solver sees
        // them from iteration 0, avoiding the CoreSolver-recreated-each-iteration bug.
        let mut skolem_cache = ExecutorSkolemCache::new();
        let mut decomposed_vars = HashSet::default();
        let mut contains_decomposed_vars = HashSet::default();
        let contains_decomps = self.preregister_contains_decompositions(
            &lifted_assertions,
            &mut skolem_cache,
            &mut decomposed_vars,
            &mut contains_decomposed_vars,
        );
        let preregistered_reduced_term_ids =
            self.collect_decomposition_concat_terms(&contains_decomps);
        lifted_assertions.extend(contains_decomps);

        // `str.<` / `str.<=` order axioms (#str-order). These predicates are
        // otherwise uninterpreted for string variables, so `x < y ∧ y < x` came
        // back `unknown`. Instantiate the VALID lexicographic-order facts over the
        // atoms present so the SAT layer can refute order contradictions. Sound by
        // construction: every axiom is true of `str.<`, so adding it can only
        // derive more (correct) UNSATs, never flip a verdict.
        let order_axioms = self.string_order_axioms(&lifted_assertions);
        lifted_assertions.extend(order_axioms);
        // Relational lemmas linking str.prefixof/str.suffixof to str.contains —
        // same VALID-fact discipline (#string-predicate-propagation).
        let predicate_relation_axioms = self.string_predicate_relation_axioms(&lifted_assertions);
        lifted_assertions.extend(predicate_relation_axioms);

        // Run Tseitin transformation
        let tseitin = Tseitin::new(&self.ctx.terms);
        let tseitin_result = tseitin.transform_all(&lifted_assertions);

        // Tseitin non-vacuity: non-empty assertions must produce clauses (#4714)
        debug_assert!(
            lifted_assertions.is_empty() || !tseitin_result.clauses.is_empty(),
            "BUG: Tseitin produced 0 clauses from {} assertions in Strings",
            lifted_assertions.len()
        );

        let mut negations: HashMap<TermId, TermId> = HashMap::default();
        if proof_enabled {
            for &term in tseitin_result.var_to_term.values() {
                let not_term = self.ctx.terms.mk_not(term);
                negations.insert(term, not_term);
            }
        }

        // Reuse the preprocessing skolem cache across runtime lemmas.
        // Track last emitted lemma to detect consecutive non-progress loops (#3375, #3429).
        // Only stall when the SAME lemma is requested in consecutive iterations (no
        // intervening new lemmas changed the context). Previously this used a HashSet
        // which permanently marked lemmas, incorrectly treating re-requests after
        // intervening VarSplit/LengthSplit as duplicates.
        let mut last_lemma: Option<StringLemma> = None;
        let mut duplicate_streak = 0usize;
        let mut dynamic_reduced_term_ids: Vec<TermId> = Vec::new();

        let mut string_lemma_requests = 0usize;

        // #3762: Warm state preserved across CEGAR iterations.
        // Statistics and reduced-term markers survive solver recreation,
        // avoiding O(N) re-registration and cumulative statistic loss.
        let mut warm_state: Option<ay_strings::StringSolverWarmState>;

        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }

        // Create string solver and DPLL. Pre-register empty string so
        // endpoint-empty inferences work even when the formula has no
        // explicit "" literal.
        let empty_id = self.ctx.terms.mk_string(String::new());
        let mut theory = StringSolver::new(&self.ctx.terms);
        theory.set_empty_string_id(empty_id);
        for &tid in &preregistered_reduced_term_ids {
            theory.mark_reduced(tid);
        }
        for &tid in &dynamic_reduced_term_ids {
            theory.mark_reduced(tid);
        }
        let mut dpll = if proof_enabled {
            DpllT::from_tseitin_with_proof(&self.ctx.terms, &tseitin_result, theory)
        } else {
            DpllT::from_tseitin(&self.ctx.terms, &tseitin_result, theory)
        };
        dpll.set_proof_bookkeeping_budget(self.search_proof_bookkeeping_budget());
        self.apply_random_seed_to_dpll(&mut dpll);
        self.apply_progress_to_dpll(&mut dpll);
        dpll.set_max_learned_clauses(self.learned_clause_limit);
        dpll.set_max_clause_db_bytes(self.clause_db_bytes_limit);
        if let Some(seed) = self.random_seed {
            dpll.sat_solver_mut().set_random_seed(seed);
        }

        let mut step_result = if proof_enabled {
            dpll.solve_eager_step(Some((&mut self.proof_tracker, &negations)))?
        } else {
            dpll.solve_eager_step(None)?
        };
        let mut sat_reason = dpll.sat_unknown_reason();

        // Inner loop: handle string lemmas inline by preserving SAT state,
        // adding lemma clauses, and re-solving. All other results return
        // immediately (QF_S does not use arithmetic splits).
        loop {
            match step_result {
                SolveStepResult::Done(solve_result) => {
                    // Soundness guard (#6273): SAT-level UNSAT after adding
                    // string lemma clauses may be false.
                    if matches!(solve_result, SatResult::Unsat(_)) && string_lemma_requests > 0 {
                        collect_sat_stats!(self, dpll.sat_solver());
                        collect_observability_stats_from_dpll!(self, dpll);
                        Self::record_sat_unknown_reason(&mut self.last_unknown_reason, sat_reason);
                        self.last_unknown_reason = Some(UnknownReason::SplitLimit);
                        return Ok(SolveResult::Unknown);
                    }

                    let string_model = if matches!(solve_result, SatResult::Sat(_)) {
                        Some(dpll.theory_solver().extract_model())
                    } else {
                        None
                    };

                    // Collect statistics and SAT unknown reason (#4622)
                    collect_sat_stats!(self, dpll.sat_solver());
                    collect_observability_stats_from_dpll!(self, dpll);

                    if proof_enabled && matches!(solve_result, SatResult::Unsat(_)) {
                        self.last_clause_trace = dpll.take_clause_trace();
                        // Use the full DPLL mapping, not the initial Tseitin map:
                        // string lemmas can allocate fresh SAT vars mid-loop.
                        self.last_var_to_term = Some(dpll.clone_var_to_term_snapshot());
                        self.last_negations = Some(negations.clone());
                        self.last_clausification_proofs = None;
                        self.last_original_clause_theory_proofs = None;
                    }

                    Self::record_sat_unknown_reason(&mut self.last_unknown_reason, sat_reason);
                    return self.solve_and_store_model_full(
                        solve_result,
                        &tseitin_result,
                        None,
                        None,
                        None,
                        None,
                        None,
                        None,
                        string_model,
                        None,
                    );
                }
                // QF_S does not use arithmetic splits or model equalities.
                SolveStepResult::NeedBoundRefinements(_)
                | SolveStepResult::NeedSplit(_)
                | SolveStepResult::NeedDisequalitySplit(_)
                | SolveStepResult::NeedExpressionSplit(_)
                | SolveStepResult::NeedLemmas(_)
                | SolveStepResult::NeedModelEquality(_)
                | SolveStepResult::NeedModelEqualities(_) => {
                    return Ok(SolveResult::Unknown);
                }
                SolveStepResult::NeedStringLemma(lemma) => {
                    string_lemma_requests += 1;

                    // Safety net: detect CONSECUTIVE duplicate lemma requests (#3375, #3429).
                    // A lemma is only a stall if it's the same as the immediately preceding
                    // one (no intervening new lemma changed the context). Permanent dedup
                    // via HashSet incorrectly blocked re-requests that become productive
                    // after VarSplit/LengthSplit decomposition changes the SAT model.
                    if last_lemma.as_ref() == Some(&lemma) {
                        duplicate_streak += 1;
                    } else {
                        duplicate_streak = 0;
                    }
                    last_lemma = Some(lemma.clone());

                    // #3762: Capture warm state before dropping the theory solver.
                    // Statistics and reduced terms survive across CEGAR iterations.
                    warm_state = Some(dpll.theory_solver().take_warm_state());

                    // Preserve SAT progress while dropping the current theory/term borrow.
                    // After this point self.ctx.terms is no longer borrowed, so we can
                    // call &mut self methods and check abort/limits.
                    let sat_state = dpll.into_sat_state();

                    if self.should_abort_theory_loop() {
                        return Ok(SolveResult::Unknown);
                    }
                    if string_lemma_requests >= MAX_STRING_LEMMA_ITERATIONS {
                        self.last_unknown_reason = Some(UnknownReason::SplitLimit);
                        return Ok(SolveResult::Unknown);
                    }
                    if duplicate_streak >= MAX_CONSECUTIVE_DUPLICATE_LEMMAS {
                        if debug_auflia_enabled() {
                            safe_eprintln!(
                                "[QF_S] Lemma {}: duplicate-streak {} for {:?} lemma (x={:?}, y={:?}, off={}) — stalled, returning Unknown",
                                string_lemma_requests,
                                duplicate_streak + 1,
                                lemma.kind,
                                lemma.x,
                                lemma.y,
                                lemma.char_offset,
                            );
                        }
                        self.last_unknown_reason = Some(UnknownReason::SplitLimit);
                        return Ok(SolveResult::Unknown);
                    }
                    for tid in self.string_lemma_reduced_terms(&lemma, &mut skolem_cache) {
                        if !dynamic_reduced_term_ids.contains(&tid) {
                            dynamic_reduced_term_ids.push(tid);
                        }
                    }
                    let clauses = self.create_string_lemma_clauses(&lemma, &mut skolem_cache);
                    if proof_enabled {
                        for clause in &clauses {
                            for &atom in clause {
                                let not_atom = self.ctx.terms.mk_not(atom);
                                negations.insert(atom, not_atom);
                            }
                        }
                    }
                    if debug_auflia_enabled() {
                        safe_eprintln!(
                            "[QF_S] Lemma {}: string {:?} (x={:?}, y={:?}, off={}, {} clauses)",
                            string_lemma_requests,
                            lemma.kind,
                            lemma.x,
                            lemma.y,
                            lemma.char_offset,
                            clauses.len()
                        );
                    }
                    let empty_id = self.ctx.terms.mk_string(String::new());
                    let mut theory = StringSolver::new(&self.ctx.terms);
                    theory.set_empty_string_id(empty_id);
                    // #3762: Import warm state from previous iteration.
                    // This restores cumulative statistics and all reduced terms
                    // (both preregistered and dynamic) in one shot, avoiding
                    // the O(N) re-registration loops below.
                    if let Some(ref ws) = warm_state {
                        theory.import_warm_state(ws);
                    }
                    // Re-apply both preregistered and dynamic reduced terms.
                    // These may include terms not yet in warm_state (newly
                    // discovered in this iteration's lemma processing).
                    for &tid in &preregistered_reduced_term_ids {
                        theory.mark_reduced(tid);
                    }
                    for &tid in &dynamic_reduced_term_ids {
                        theory.mark_reduced(tid);
                    }
                    dpll = DpllT::from_sat_state(&self.ctx.terms, theory, sat_state);
                    // SAT solver settings (learned clause limit, clause DB
                    // bytes limit, random seed, preprocess flag) are preserved
                    // in the DpllSatState across iterations. Only
                    // set_preprocess_enabled(false) needs to be set on the
                    // first lemma iteration; subsequent iterations already have
                    // it disabled in the preserved SAT solver.
                    if string_lemma_requests == 1 {
                        self.apply_progress_to_dpll(&mut dpll);
                        dpll.set_max_learned_clauses(self.learned_clause_limit);
                        dpll.set_max_clause_db_bytes(self.clause_db_bytes_limit);
                        if let Some(seed) = self.random_seed {
                            dpll.sat_solver_mut().set_random_seed(seed);
                        }
                        // Skip BVE/probing/subsumption on incremental re-solves.
                        dpll.sat_solver_mut().set_preprocess_enabled(false);
                    }
                    for clause in &clauses {
                        if proof_enabled {
                            dpll.apply_string_lemma_with_proof_tracking(
                                clause,
                                &mut self.proof_tracker,
                            );
                        } else {
                            dpll.apply_string_lemma(clause);
                        }
                    }
                    step_result = if proof_enabled {
                        dpll.solve_eager_step(Some((&mut self.proof_tracker, &negations)))?
                    } else {
                        dpll.solve_eager_step(None)?
                    };
                    sat_reason = dpll.sat_unknown_reason();
                }
            }
        }
    }

    // QF_SLIA pipeline (solve_strings_lia, solve_strings_lia_with_assumptions,
    // solve_strings_lia_preprocessed) moved to strings_lia.rs (#7006).
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Strict semantic validation for `TheoryLemmaKind::RegexIntersectEmpty`.
//!
//! # The obligation
//!
//! A `RegexIntersectEmpty` lemma claims: "this clause contains a group of
//! literals `±(str.in_re t Rᵢ)` over ONE common string term `t`, all of whose
//! regexes are ground, and the intersection of the languages those literals
//! deny is EMPTY". Concretely, for a clause `C` and a literal group
//!
//! ```text
//!   (not (str.in_re t R₁)) … (not (str.in_re t Rₘ))   -- deny `t ∈ Rᵢ`
//!   (str.in_re t S₁)       … (str.in_re t Sₙ)         -- deny `t ∉ Sⱼ`
//! ```
//!
//! the group is jointly falsified exactly when
//! `t ∈ L(R₁) ∩ … ∩ L(Rₘ) ∩ ¬L(S₁) ∩ … ∩ ¬L(Sₙ)`. If that intersection is
//! empty no `t` falsifies the whole group, so at least one literal of `C` is
//! true under every interpretation — `C` is a tautology, hence a valid theory
//! lemma. Extra literals in `C` only weaken it, so a tautologous SUBSET
//! suffices.
//!
//! Unlike `StringGroundEval` the subject `t` here is SYMBOLIC: the fact is not
//! ground, so a ground evaluator cannot decide it. This is the certificate for
//! the regex-intersection-emptiness family (`automatark`-style refutations,
//! `x ∈ R₁ ∧ x ∈ R₂` with disjoint languages).
//!
//! # The certificate
//!
//! [`EmptinessCertificate`] is a derivative-product REACHABILITY ARGUMENT:
//!
//! * an ALPHABET PARTITION of the whole SMT-LIB code-point range
//!   `0 ..= 0x2FFFF` into blocks, each block a maximal run of code points that
//!   every atom of every constraint treats identically;
//! * the set of REACHABLE product states, each a vector of Brzozowski
//!   derivative residuals (one per constraint), state `0` being the start;
//! * for every state and every block, the TRANSITION taken on that block's
//!   representative — either the index of the successor state, or `dead` when
//!   some residual became the empty language.
//!
//! [`validate_certificate`] accepts it only when ALL of the following hold, and
//! it re-derives every one of them with this module's own code:
//!
//! 1. the blocks tile `0 ..= 0x2FFFF` exactly — contiguous, ordered, no gap and
//!    no overlap (a certificate over a partial alphabet proves nothing);
//! 2. every character set occurring anywhere in the constraints or in any
//!    listed state is a union of WHOLE blocks, so one representative really
//!    does speak for its entire block;
//! 3. state `0` is the translated constraint vector itself;
//! 4. states are pairwise distinct and none is ACCEPTING (a state is accepting
//!    when every residual is nullable — it would witness the empty word);
//! 5. every transition matches this module's own derivative, and every live
//!    transition's target is IN the listed set (closure).
//!
//! Given 1–5, every word over the full alphabet drives state `0` through listed
//! states only, and no listed state accepts — so no word is in the
//! intersection. Any gap in 1–5 ⇒ REJECT.
//!
//! # Independence
//!
//! This module shares NO code with the solver's emptiness search
//! (`ay-theories/strings` `we_regex.rs`: `WeRegex::derive`, `is_empty_lang`,
//! `class_alphabet`, `concat_membership_definitely_empty`). It is a separate
//! implementation with a different representation (hash-consed arena over
//! `u32` code-point INTERVAL SETS, versus the solver's plain recursive tree
//! over Rust `char` with `Lit`/`Range`/`AnyChar` atoms), a different alphabet
//! construction (a verified total partition of the code-point range, versus
//! the solver's "criticals + gap representatives + one above the maximum"), and
//! a separate normal form. A checker that called the solver's emptiness code
//! would only confirm that the solver agrees with itself.
//!
//! # Why the states are re-derived rather than transported
//!
//! The certificate is BUILT here (by [`build_certificate`]) and then validated
//! by the independent [`validate_certificate`], instead of being serialized by
//! the solver into the proof. Two reasons:
//!
//! * SIZE. A real `automatark` product graph reaches hundreds to thousands of
//!   states, each a vector of residual regexes of up to a few thousand nodes.
//!   Serializing that is tens of megabytes per refutation — the proof would be
//!   dominated by data no external tool would ever read.
//! * SOUNDNESS. Transported states would have to be matched against locally
//!   derived ones up to some normal form. Agreeing on a normal form is exactly
//!   the coupling this checker must not have: a checker that accepts the
//!   solver's node shapes is one normalization change away from accepting the
//!   solver's mistakes. Re-deriving costs the same asymptotic work and depends
//!   on nothing the solver produced.
//!
//! What the proof carries is therefore the CLAIM (the lemma kind and its
//! clause). Everything else is reconstructed and then independently checked;
//! the split between [`build_certificate`] and [`validate_certificate`] keeps
//! the search and the argument in separate code paths, so a bug in the search
//! cannot be laundered into an accepted lemma.
//!
//! # Fail-closed
//!
//! Every partial function returns `None`/`false` — never a guess — when a
//! regex leaf is non-ground, an operator is not implemented here, the subject
//! terms disagree, a budget runs out, or any check above fails. There is no
//! "assume valid" arm.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{Constant, ProofId, Sort, Symbol, TermData, TermId, TermStore};

use super::ProofCheckError;

/// Highest code point of the SMT-LIB 2.6 Unicode string alphabet.
///
/// SMT-LIB fixes the string alphabet at code points `0x0 ..= 0x2FFFF`. Every
/// character here is a raw `u32` code point, INCLUDING the surrogate range
/// `0xD800 ..= 0xDFFF` that Rust's `char` cannot represent — the solver works
/// over `char`, so this is a deliberately different (and strictly larger)
/// alphabet. That direction is safe: for every regex expression `E`,
/// `L_small(E) = L_big(E) ∩ Σ_small*` (by induction over the constructors,
/// complement included), so emptiness over the larger alphabet implies
/// emptiness over the smaller one.
const ALPHABET_HI: u32 = 0x2_FFFF;

/// Maximum number of alphabet blocks. Each block costs one transition per
/// state, so this bounds the branching factor. Exceeding it fails closed.
const MAX_BLOCKS: usize = 1024;

/// Maximum number of product states explored/validated. Exceeding it fails
/// closed (a certificate that does not fit is simply not accepted).
const MAX_STATES: usize = 20_000;

/// Maximum number of interned regex nodes. Exceeding it fails closed.
const MAX_NODES: usize = 2_000_000;

/// Maximum number of `(state, block)` transitions taken, counted across BOTH
/// the search and the validation pass. This is the real cost knob: the product
/// graph is `states × blocks` wide, and a lemma whose argument does not fit
/// simply does not certify. Exceeding it fails closed.
const MAX_TRANSITIONS: u64 = 400_000;

/// Maximum number of derivative computations (memo misses). Exceeding it fails
/// closed.
const MAX_DERIVE_STEPS: u64 = 8_000_000;

/// Maximum number of constraints (memberships) in one group.
const MAX_CONSTRAINTS: usize = 64;

/// Maximum regex term nodes translated per lemma (guards a pathological input).
const MAX_TRANSLATE_STEPS: u32 = 200_000;

/// Maximum `(_ re.loop lo hi)` bound accepted. Counters are carried, never
/// unrolled, so this only rejects absurd inputs.
const MAX_LOOP_BOUND: u32 = 100_000;

// ---------------------------------------------------------------------------
// Hash-consed regex arena
// ---------------------------------------------------------------------------

/// Interned regex node identifier.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct ReId(u32);

/// A regex node over `u32` code points.
///
/// Atoms are INTERVAL SETS (sorted, disjoint, non-adjacent, non-empty), not
/// single literals or single ranges: the whole point of the alphabet-partition
/// argument is that a character class is a set of code-point blocks, and
/// keeping that shape in the representation is what makes the block-alignment
/// invariant checkable at every construction site.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum Node {
    /// `∅` — the empty language.
    Nil,
    /// `{ε}` — the empty word only.
    Eps,
    /// One character drawn from a union of code-point intervals.
    Set(Vec<(u32, u32)>),
    /// Concatenation (≥ 2 operands, no nested `Cat`, no `Eps`, no `Nil`).
    Cat(Vec<ReId>),
    /// Union (≥ 2 operands, sorted+deduped, no nested `Alt`, no `Nil`).
    Alt(Vec<ReId>),
    /// Intersection (≥ 2 operands, sorted+deduped, no nested `And`, no `Σ*`).
    And(Vec<ReId>),
    /// Kleene star.
    Star(ReId),
    /// Complement w.r.t. `Σ*` over the FULL alphabet.
    Not(ReId),
    /// Bounded repetition `⋃_{k=lo}^{hi} body^k`, carried as counters.
    Rep(ReId, u32, u32),
}

/// Hash-consing arena with cached nullability.
struct Arena {
    nodes: Vec<Node>,
    index: HashMap<Node, ReId>,
    nullable: Vec<bool>,
    /// `d(node, block_index)` memo.
    deriv: HashMap<(ReId, u32), ReId>,
    nil: ReId,
    eps: ReId,
    all: ReId,
    /// The verified alphabet partition, once installed. `Set` nodes interned
    /// after installation must be unions of whole blocks.
    blocks: Vec<(u32, u32)>,
    /// Start of each block, for `O(log n)` block lookup.
    block_starts: Vec<u32>,
    /// Remaining derivative computations (memo misses).
    derive_budget: u64,
    /// Remaining `(state, block)` transitions, shared by the search and the
    /// validation pass.
    transition_budget: u64,
    /// Sticky failure flag. Set by any construction that violated an invariant
    /// or blew a budget; a poisoned arena can never produce an accepted
    /// certificate.
    poisoned: bool,
}

impl Arena {
    fn new() -> Self {
        let mut a = Self {
            nodes: Vec::new(),
            index: HashMap::default(),
            nullable: Vec::new(),
            deriv: HashMap::default(),
            nil: ReId(0),
            eps: ReId(0),
            all: ReId(0),
            blocks: Vec::new(),
            block_starts: Vec::new(),
            derive_budget: MAX_DERIVE_STEPS,
            transition_budget: MAX_TRANSITIONS,
            poisoned: false,
        };
        a.nil = a.intern(Node::Nil);
        a.eps = a.intern(Node::Eps);
        let full = a.intern(Node::Set(vec![(0, ALPHABET_HI)]));
        a.all = a.intern(Node::Star(full));
        a
    }

    fn poison(&mut self) -> ReId {
        self.poisoned = true;
        self.nil
    }

    fn intern(&mut self, node: Node) -> ReId {
        if let Some(&id) = self.index.get(&node) {
            return id;
        }
        if self.nodes.len() >= MAX_NODES {
            self.poisoned = true;
            // Return a already-interned node; the poison flag rejects anyway.
            return ReId(0);
        }
        // Block alignment is an INVARIANT, not an assumption: once the
        // partition is installed every character set must be a union of whole
        // blocks, otherwise one representative would not speak for its block.
        if let Node::Set(iv) = &node {
            if !self.block_starts.is_empty() && !self.set_is_block_aligned(iv) {
                self.poisoned = true;
            }
        }
        let id = ReId(u32::try_from(self.nodes.len()).unwrap_or(u32::MAX));
        let null = self.compute_nullable(&node);
        self.nodes.push(node.clone());
        self.nullable.push(null);
        self.index.insert(node, id);
        id
    }

    fn set_is_block_aligned(&self, iv: &[(u32, u32)]) -> bool {
        iv.iter().all(|&(lo, hi)| {
            let Some(i) = self.block_of(lo) else {
                return false;
            };
            let Some(j) = self.block_of(hi) else {
                return false;
            };
            self.blocks[i].0 == lo && self.blocks[j].1 == hi
        })
    }

    fn block_of(&self, c: u32) -> Option<usize> {
        if c > ALPHABET_HI || self.block_starts.is_empty() {
            return None;
        }
        let idx = self.block_starts.partition_point(|&s| s <= c);
        idx.checked_sub(1)
    }

    fn get(&self, id: ReId) -> &Node {
        &self.nodes[id.0 as usize]
    }

    fn is_nullable(&self, id: ReId) -> bool {
        self.nullable[id.0 as usize]
    }

    /// `ε ∈ L(node)?` — computed once, at interning time, from already-interned
    /// children (whose nullability is therefore already known).
    fn compute_nullable(&self, node: &Node) -> bool {
        match node {
            Node::Nil | Node::Set(_) => false,
            Node::Eps | Node::Star(_) => true,
            Node::Cat(xs) | Node::And(xs) => xs.iter().all(|&x| self.is_nullable(x)),
            Node::Alt(xs) => xs.iter().any(|&x| self.is_nullable(x)),
            Node::Not(x) => !self.is_nullable(*x),
            Node::Rep(x, lo, _) => *lo == 0 || self.is_nullable(*x),
        }
    }

    // ── Smart constructors ──────────────────────────────────────────────

    /// Normalize an interval list: drop empties, clamp to the alphabet, sort,
    /// merge overlapping/adjacent runs.
    fn mk_set(&mut self, mut iv: Vec<(u32, u32)>) -> ReId {
        iv.retain(|&(lo, hi)| lo <= hi && lo <= ALPHABET_HI);
        for e in &mut iv {
            e.1 = e.1.min(ALPHABET_HI);
        }
        if iv.is_empty() {
            return self.nil;
        }
        iv.sort_unstable();
        let mut merged: Vec<(u32, u32)> = Vec::with_capacity(iv.len());
        for (lo, hi) in iv {
            match merged.last_mut() {
                Some(last) if lo <= last.1.saturating_add(1) => last.1 = last.1.max(hi),
                _ => merged.push((lo, hi)),
            }
        }
        self.intern(Node::Set(merged))
    }

    fn set_union(a: &[(u32, u32)], b: &[(u32, u32)]) -> Vec<(u32, u32)> {
        let mut out: Vec<(u32, u32)> = a.to_vec();
        out.extend_from_slice(b);
        out
    }

    fn set_inter(a: &[(u32, u32)], b: &[(u32, u32)]) -> Vec<(u32, u32)> {
        let mut out = Vec::new();
        let (mut i, mut j) = (0usize, 0usize);
        while i < a.len() && j < b.len() {
            let lo = a[i].0.max(b[j].0);
            let hi = a[i].1.min(b[j].1);
            if lo <= hi {
                out.push((lo, hi));
            }
            if a[i].1 < b[j].1 {
                i += 1;
            } else {
                j += 1;
            }
        }
        out
    }

    fn mk_cat(&mut self, parts: Vec<ReId>) -> ReId {
        let mut out: Vec<ReId> = Vec::with_capacity(parts.len());
        for p in parts {
            if p == self.nil {
                return self.nil;
            }
            if p == self.eps {
                continue;
            }
            match self.get(p).clone() {
                Node::Cat(inner) => out.extend(inner),
                _ => out.push(p),
            }
        }
        match out.len() {
            0 => self.eps,
            1 => out[0],
            _ => self.intern(Node::Cat(out)),
        }
    }

    fn mk_alt(&mut self, parts: Vec<ReId>) -> ReId {
        let mut out: Vec<ReId> = Vec::with_capacity(parts.len());
        let mut set_acc: Option<Vec<(u32, u32)>> = None;
        // Worklist, not a plain loop: flattening a nested `Alt` can surface
        // further `Set`/`Alt` operands that still need folding.
        let mut work: Vec<ReId> = parts;
        while let Some(p) = work.pop() {
            if p == self.nil {
                continue;
            }
            if p == self.all {
                return self.all;
            }
            match self.get(p).clone() {
                Node::Alt(inner) => work.extend(inner),
                // `Set(S₁) ∪ Set(S₂) = Set(S₁ ∪ S₂)` — exact, and it is what
                // makes the product graph converge on real regex sets.
                Node::Set(iv) => {
                    set_acc = Some(match set_acc {
                        None => iv,
                        Some(prev) => Self::set_union(&prev, &iv),
                    });
                }
                _ => out.push(p),
            }
        }
        if let Some(iv) = set_acc {
            let s = self.mk_set(iv);
            if s != self.nil {
                out.push(s);
            }
        }
        out.sort_unstable();
        out.dedup();
        match out.len() {
            0 => self.nil,
            1 => out[0],
            _ => self.intern(Node::Alt(out)),
        }
    }

    fn mk_and(&mut self, parts: Vec<ReId>) -> ReId {
        let mut out: Vec<ReId> = Vec::with_capacity(parts.len());
        let mut set_acc: Option<Vec<(u32, u32)>> = None;
        let mut work: Vec<ReId> = parts;
        while let Some(p) = work.pop() {
            if p == self.nil {
                return self.nil;
            }
            if p == self.all {
                continue;
            }
            match self.get(p).clone() {
                Node::And(inner) => work.extend(inner),
                // `Set(S₁) ∩ Set(S₂) = Set(S₁ ∩ S₂)` — exact.
                Node::Set(iv) => {
                    set_acc = Some(match set_acc {
                        None => iv,
                        Some(prev) => Self::set_inter(&prev, &iv),
                    });
                }
                _ => out.push(p),
            }
        }
        if let Some(iv) = set_acc {
            let s = self.mk_set(iv);
            if s == self.nil {
                return self.nil;
            }
            out.push(s);
        }
        out.sort_unstable();
        out.dedup();
        match out.len() {
            0 => self.all,
            1 => out[0],
            _ => self.intern(Node::And(out)),
        }
    }

    fn mk_star(&mut self, inner: ReId) -> ReId {
        if inner == self.nil || inner == self.eps {
            return self.eps;
        }
        if inner == self.all {
            return self.all;
        }
        if matches!(self.get(inner), Node::Star(_)) {
            return inner;
        }
        self.intern(Node::Star(inner))
    }

    fn mk_not(&mut self, inner: ReId) -> ReId {
        if inner == self.nil {
            return self.all;
        }
        if inner == self.all {
            return self.nil;
        }
        if let Node::Not(x) = *self.get(inner) {
            return x;
        }
        self.intern(Node::Not(inner))
    }

    fn mk_rep(&mut self, inner: ReId, lo: u32, hi: u32) -> ReId {
        if lo > hi {
            return self.nil;
        }
        if hi == 0 || inner == self.eps {
            return self.eps;
        }
        if inner == self.nil {
            return if lo == 0 { self.eps } else { self.nil };
        }
        if inner == self.all || matches!(self.get(inner), Node::Star(_)) {
            // `(r*)^k = r*` for `k ≥ 1`, and the `k = 0` term `{ε}` is already
            // inside `r*`, so the whole bounded union collapses to `r*`.
            return inner;
        }
        if lo == 1 && hi == 1 {
            return inner;
        }
        self.intern(Node::Rep(inner, lo, hi))
    }

    // ── Brzozowski derivative ───────────────────────────────────────────

    /// `d_c(node)` for the representative of block `blk`.
    ///
    /// Memoized on `(node, blk)`. Every character in block `blk` yields the
    /// SAME derivative because every `Set` is a union of whole blocks (an
    /// invariant enforced at interning time and re-checked by
    /// [`validate_certificate`]) — that equivalence is the entire justification
    /// for exploring one representative per block instead of all `0x30000`
    /// code points.
    fn derive(&mut self, node: ReId, blk: u32) -> ReId {
        if let Some(&hit) = self.deriv.get(&(node, blk)) {
            return hit;
        }
        if self.poisoned {
            return self.nil;
        }
        match self.derive_budget.checked_sub(1) {
            Some(left) => self.derive_budget = left,
            None => return self.poison(),
        }
        let Some(&(rep, _)) = self.blocks.get(blk as usize) else {
            return self.poison();
        };
        let out = match self.get(node).clone() {
            Node::Nil | Node::Eps => self.nil,
            Node::Set(iv) => {
                if iv.iter().any(|&(lo, hi)| lo <= rep && rep <= hi) {
                    self.eps
                } else {
                    self.nil
                }
            }
            // d(r₁·rest) = d(r₁)·rest ∪ [nullable(r₁)] d(rest)
            Node::Cat(xs) => {
                let head = xs[0];
                let rest = self.mk_cat(xs[1..].to_vec());
                let d_head = self.derive(head, blk);
                let a = self.mk_cat(vec![d_head, rest]);
                if self.is_nullable(head) {
                    let b = self.derive(rest, blk);
                    self.mk_alt(vec![a, b])
                } else {
                    a
                }
            }
            Node::Alt(xs) => {
                let ds: Vec<ReId> = xs.iter().map(|&x| self.derive(x, blk)).collect();
                self.mk_alt(ds)
            }
            Node::And(xs) => {
                let ds: Vec<ReId> = xs.iter().map(|&x| self.derive(x, blk)).collect();
                self.mk_and(ds)
            }
            Node::Star(x) => {
                let d = self.derive(x, blk);
                self.mk_cat(vec![d, node])
            }
            // d(¬r) = ¬d(r)
            Node::Not(x) => {
                let d = self.derive(x, blk);
                self.mk_not(d)
            }
            // d(⋃_{k=lo}^{hi} r^k) = d(r) · ⋃_{k=lo⊖1}^{hi−1} r^k, exact for
            // both nullable and non-nullable `r` (`hi ≥ 1` by construction).
            Node::Rep(x, lo, hi) => {
                let d = self.derive(x, blk);
                let tail = self.mk_rep(x, lo.saturating_sub(1), hi - 1);
                self.mk_cat(vec![d, tail])
            }
        };
        self.deriv.insert((node, blk), out);
        out
    }

    /// Every code-point interval occurring anywhere under `root`.
    fn collect_intervals(&self, root: ReId, seen: &mut HashSet<ReId>, out: &mut Vec<(u32, u32)>) {
        if !seen.insert(root) {
            return;
        }
        match self.get(root).clone() {
            Node::Nil | Node::Eps => {}
            Node::Set(iv) => out.extend(iv),
            Node::Cat(xs) | Node::Alt(xs) | Node::And(xs) => {
                for x in xs {
                    self.collect_intervals(x, seen, out);
                }
            }
            Node::Star(x) | Node::Not(x) | Node::Rep(x, _, _) => {
                self.collect_intervals(x, seen, out);
            }
        }
    }

    /// Every `Set` node occurring anywhere under `root`, as interval lists.
    fn collect_sets(&self, root: ReId, seen: &mut HashSet<ReId>, out: &mut Vec<Vec<(u32, u32)>>) {
        if !seen.insert(root) {
            return;
        }
        match self.get(root).clone() {
            Node::Nil | Node::Eps => {}
            Node::Set(iv) => out.push(iv),
            Node::Cat(xs) | Node::Alt(xs) | Node::And(xs) => {
                for x in xs {
                    self.collect_sets(x, seen, out);
                }
            }
            Node::Star(x) | Node::Not(x) | Node::Rep(x, _, _) => {
                self.collect_sets(x, seen, out);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// SMT-LIB regex term → arena
// ---------------------------------------------------------------------------

struct Translator<'a> {
    terms: &'a TermStore,
    arena: Arena,
    memo: HashMap<TermId, Option<ReId>>,
    budget: u32,
}

impl<'a> Translator<'a> {
    fn new(terms: &'a TermStore) -> Self {
        Self {
            terms,
            arena: Arena::new(),
            memo: HashMap::default(),
            budget: MAX_TRANSLATE_STEPS,
        }
    }

    fn spend(&mut self) -> Option<()> {
        self.budget = self.budget.checked_sub(1)?;
        Some(())
    }

    /// A GROUND string constant, or `None`. Only literal constants count: a
    /// variable, an uninterpreted application, or any string operation makes
    /// the regex non-ground and the lemma unverifiable here.
    fn str_const(&self, t: TermId) -> Option<Vec<u32>> {
        match self.terms.get(t) {
            TermData::Const(Constant::String(s)) => {
                let cps: Vec<u32> = s.chars().map(|c| c as u32).collect();
                // A code point outside the SMT-LIB alphabet has no place in a
                // well-formed string constant. Rejecting is the fail-closed
                // move: silently clamping it away would shrink the language
                // and could turn a NON-empty intersection into a spurious
                // "empty" verdict.
                if cps.iter().any(|&c| c > ALPHABET_HI) {
                    return None;
                }
                Some(cps)
            }
            _ => None,
        }
    }

    /// Translate a ground `RegLan` term. EXACT or `None` — there is no
    /// approximating arm, in either direction.
    fn translate(&mut self, t: TermId) -> Option<ReId> {
        if let Some(&hit) = self.memo.get(&t) {
            return hit;
        }
        self.spend()?;
        let out = self.translate_uncached(t);
        self.memo.insert(t, out);
        out
    }

    #[allow(clippy::too_many_lines)]
    fn translate_uncached(&mut self, t: TermId) -> Option<ReId> {
        if !matches!(self.terms.sort(t), Sort::RegLan) {
            return None;
        }
        let TermData::App(sym, args) = self.terms.get(t) else {
            return None;
        };
        let sym = sym.clone();
        let args = args.clone();
        let name = sym.name().to_string();
        let out = match (name.as_str(), args.len()) {
            ("re.none", 0) => self.arena.nil,
            ("re.all", 0) => self.arena.all,
            ("re.allchar", 0) => self.arena.mk_set(vec![(0, ALPHABET_HI)]),
            ("re.range", 2) => {
                let lo = self.str_const(args[0])?;
                let hi = self.str_const(args[1])?;
                // SMT-LIB: `(re.range lo hi)` is the EMPTY language unless both
                // endpoints are single characters with `lo <= hi`.
                if lo.len() != 1 || hi.len() != 1 || lo[0] > hi[0] {
                    self.arena.nil
                } else {
                    self.arena.mk_set(vec![(lo[0], hi[0])])
                }
            }
            ("str.to_re" | "str.to.re", 1) => {
                let s = self.str_const(args[0])?;
                let parts: Vec<ReId> = s
                    .into_iter()
                    .map(|c| self.arena.mk_set(vec![(c, c)]))
                    .collect();
                self.arena.mk_cat(parts)
            }
            ("re.++", _) if !args.is_empty() => {
                let parts = self.translate_all(&args)?;
                self.arena.mk_cat(parts)
            }
            ("re.union", _) if !args.is_empty() => {
                let parts = self.translate_all(&args)?;
                self.arena.mk_alt(parts)
            }
            ("re.inter", _) if !args.is_empty() => {
                let parts = self.translate_all(&args)?;
                self.arena.mk_and(parts)
            }
            ("re.*", 1) => {
                let inner = self.translate(args[0])?;
                self.arena.mk_star(inner)
            }
            ("re.+", 1) => {
                let inner = self.translate(args[0])?;
                let star = self.arena.mk_star(inner);
                self.arena.mk_cat(vec![inner, star])
            }
            ("re.opt", 1) => {
                let inner = self.translate(args[0])?;
                let eps = self.arena.eps;
                self.arena.mk_alt(vec![eps, inner])
            }
            ("re.comp", 1) => {
                let inner = self.translate(args[0])?;
                self.arena.mk_not(inner)
            }
            // `:left-assoc`: `(re.diff a b c)` == `(a \ b) \ c`.
            ("re.diff", _) if args.len() >= 2 => {
                let parts = self.translate_all(&args)?;
                let mut acc = parts[0];
                for &p in &parts[1..] {
                    let np = self.arena.mk_not(p);
                    acc = self.arena.mk_and(vec![acc, np]);
                }
                acc
            }
            ("re.loop", 1) => {
                let Symbol::Indexed(_, indices) = &sym else {
                    return None;
                };
                let [lo, hi] = indices[..] else {
                    return None;
                };
                if lo > MAX_LOOP_BOUND || hi > MAX_LOOP_BOUND {
                    return None;
                }
                let inner = self.translate(args[0])?;
                self.arena.mk_rep(inner, lo, hi)
            }
            ("re.^", 1) => {
                let Symbol::Indexed(_, indices) = &sym else {
                    return None;
                };
                let [n] = indices[..] else {
                    return None;
                };
                if n > MAX_LOOP_BOUND {
                    return None;
                }
                let inner = self.translate(args[0])?;
                self.arena.mk_rep(inner, n, n)
            }
            _ => return None,
        };
        if self.arena.poisoned {
            return None;
        }
        Some(out)
    }

    fn translate_all(&mut self, args: &[TermId]) -> Option<Vec<ReId>> {
        args.iter().map(|&a| self.translate(a)).collect()
    }
}

// ---------------------------------------------------------------------------
// The certificate
// ---------------------------------------------------------------------------

/// Transition target: a listed state, or `Dead` when some residual of the
/// successor is the empty language (no word can continue through it).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Target {
    Dead,
    State(usize),
}

/// The derivative-product reachability argument. See the module docs.
struct EmptinessCertificate {
    /// Alphabet partition: ordered, contiguous, covering `0 ..= ALPHABET_HI`.
    blocks: Vec<(u32, u32)>,
    /// Reachable product states; `states[0]` is the start state. Each entry is
    /// one residual per constraint.
    states: Vec<Vec<ReId>>,
    /// `transitions[i][k]`: where state `i` goes on block `k`'s representative.
    transitions: Vec<Vec<Target>>,
}

/// Compute the alphabet partition induced by `roots`.
///
/// Every interval endpoint contributes a boundary: `lo` opens a block and
/// `hi + 1` opens the next. The resulting blocks tile `0 ..= ALPHABET_HI`, and
/// no interval endpoint falls strictly inside a block — so every atom either
/// contains a whole block or is disjoint from it, which is exactly what lets a
/// single representative stand for the block.
fn compute_blocks(arena: &Arena, roots: &[ReId]) -> Option<Vec<(u32, u32)>> {
    let mut endpoints: Vec<(u32, u32)> = Vec::new();
    let mut seen: HashSet<ReId> = HashSet::default();
    for &r in roots {
        arena.collect_intervals(r, &mut seen, &mut endpoints);
    }
    let mut bounds: Vec<u32> = vec![0];
    for (lo, hi) in endpoints {
        bounds.push(lo);
        if hi < ALPHABET_HI {
            bounds.push(hi + 1);
        }
    }
    bounds.retain(|&b| b <= ALPHABET_HI);
    bounds.sort_unstable();
    bounds.dedup();
    if bounds.len() > MAX_BLOCKS {
        return None;
    }
    let mut blocks: Vec<(u32, u32)> = Vec::with_capacity(bounds.len());
    for i in 0..bounds.len() {
        let lo = bounds[i];
        let hi = if i + 1 < bounds.len() {
            bounds[i + 1] - 1
        } else {
            ALPHABET_HI
        };
        blocks.push((lo, hi));
    }
    Some(blocks)
}

/// Search for a reachability argument proving `⋂ constraints = ∅`.
///
/// Returns `None` when the intersection is NOT empty (an accepting state was
/// reached) or when a budget ran out. The result is only a CANDIDATE: nothing
/// downstream trusts it until [`validate_certificate`] re-derives it.
fn build_certificate(arena: &mut Arena, constraints: &[ReId]) -> Option<EmptinessCertificate> {
    let blocks = arena.blocks.clone();
    if blocks.is_empty() {
        return None;
    }
    let nb = blocks.len();

    let start: Vec<ReId> = constraints.to_vec();
    if start.contains(&arena.nil) {
        // Some constraint is literally `∅`: still express it as a one-state
        // argument so the validator does the deciding, not this function.
        // A state containing `Nil` is non-accepting and every transition out of
        // it is dead, so the certificate validates.
        let transitions = vec![vec![Target::Dead; nb]];
        return Some(EmptinessCertificate {
            blocks,
            states: vec![start],
            transitions,
        });
    }

    let mut index: HashMap<Vec<ReId>, usize> = HashMap::default();
    let mut states: Vec<Vec<ReId>> = vec![start.clone()];
    let mut transitions: Vec<Vec<Target>> = Vec::new();
    index.insert(start, 0);

    let mut queue: usize = 0;
    while queue < states.len() {
        let state = states[queue].clone();
        if state.iter().all(|&r| arena.is_nullable(r)) {
            return None; // accepting: the intersection is NOT empty
        }
        let mut row: Vec<Target> = Vec::with_capacity(nb);
        for blk in 0..nb {
            // Budget exhaustion is not a proof.
            let left = arena.transition_budget.checked_sub(1)?;
            arena.transition_budget = left;
            let next: Vec<ReId> = state.iter().map(|&r| arena.derive(r, blk as u32)).collect();
            if arena.poisoned {
                return None;
            }
            if next.contains(&arena.nil) {
                row.push(Target::Dead);
                continue;
            }
            let id = match index.get(&next) {
                Some(&id) => id,
                None => {
                    if states.len() >= MAX_STATES {
                        return None;
                    }
                    let id = states.len();
                    index.insert(next.clone(), id);
                    states.push(next);
                    id
                }
            };
            row.push(Target::State(id));
        }
        transitions.push(row);
        queue += 1;
    }
    Some(EmptinessCertificate {
        blocks,
        states,
        transitions,
    })
}

/// INDEPENDENTLY verify that the certificate proves `⋂ constraints = ∅`.
///
/// This function does not trust a single field of `cert`. It re-derives every
/// transition with [`Arena::derive`], re-checks the alphabet partition against
/// the code-point range, re-checks block alignment of every character set
/// reachable from every listed state, re-checks non-acceptance, and re-checks
/// closure. It returns `true` only when the argument is complete.
fn validate_certificate(
    arena: &mut Arena,
    constraints: &[ReId],
    cert: &EmptinessCertificate,
) -> bool {
    if arena.poisoned {
        return false;
    }

    // (1) The alphabet partition must TILE the whole SMT-LIB code-point range.
    //     A certificate over a partial alphabet proves nothing: the missing
    //     characters are exactly where a witness could hide.
    if cert.blocks.is_empty() || cert.blocks.len() > MAX_BLOCKS {
        return false;
    }
    if cert.blocks[0].0 != 0 {
        return false;
    }
    if cert.blocks[cert.blocks.len() - 1].1 != ALPHABET_HI {
        return false;
    }
    for w in cert.blocks.windows(2) {
        if w[0].0 > w[0].1 || w[1].0 != w[0].1 + 1 {
            return false;
        }
    }
    // Install the certificate's OWN partition and discard every derivative the
    // search memoized: from here on this function derives only under the
    // partition it just verified, so nothing it concludes depends on how the
    // search was configured.
    arena.blocks = cert.blocks.clone();
    arena.block_starts = cert.blocks.iter().map(|&(lo, _)| lo).collect();
    arena.deriv.clear();
    arena.derive_budget = MAX_DERIVE_STEPS;

    // (2) Structural sanity of the state table.
    if cert.states.is_empty()
        || cert.states.len() > MAX_STATES
        || cert.states.len() != cert.transitions.len()
    {
        return false;
    }
    let width = constraints.len();
    if width == 0 || width > MAX_CONSTRAINTS {
        return false;
    }
    if cert.states.iter().any(|s| s.len() != width) {
        return false;
    }
    if cert
        .transitions
        .iter()
        .any(|r| r.len() != cert.blocks.len())
    {
        return false;
    }
    // States must be pairwise distinct, so "the listed set" is well defined and
    // a closure hit cannot be manufactured by listing a state twice.
    let mut distinct: HashSet<&Vec<ReId>> = HashSet::default();
    for s in &cert.states {
        if !distinct.insert(s) {
            return false;
        }
    }

    // (3) The start state must be the constraint vector itself.
    if cert.states[0] != constraints {
        return false;
    }

    // (4) Block alignment of every character set reachable from any listed
    //     state (and from the constraints). Without this a "representative"
    //     would not speak for its block and the search could step over a
    //     character class boundary unnoticed.
    let mut sets: Vec<Vec<(u32, u32)>> = Vec::new();
    let mut seen: HashSet<ReId> = HashSet::default();
    for &r in constraints {
        arena.collect_sets(r, &mut seen, &mut sets);
    }
    for state in &cert.states {
        for &r in state {
            arena.collect_sets(r, &mut seen, &mut sets);
        }
    }
    if sets.iter().any(|iv| !arena.set_is_block_aligned(iv)) {
        return false;
    }

    // (5) No listed state is ACCEPTING. An accepting state (every residual
    //     nullable) is a word in the intersection — the opposite of the claim.
    for state in &cert.states {
        if state.iter().all(|&r| arena.is_nullable(r)) {
            return false;
        }
    }

    // (6) Re-derive every transition and check CLOSURE. Every live successor
    //     must appear in the listed set; a dead successor must really be dead.
    // The validation pass gets its OWN transition allowance: re-deriving the
    // argument must not be starved by whatever the search already spent.
    arena.transition_budget = MAX_TRANSITIONS;
    for (i, state) in cert.states.iter().enumerate() {
        for (blk, &claimed) in cert.transitions[i].iter().enumerate() {
            match arena.transition_budget.checked_sub(1) {
                Some(left) => arena.transition_budget = left,
                None => return false,
            }
            let next: Vec<ReId> = state.iter().map(|&r| arena.derive(r, blk as u32)).collect();
            if arena.poisoned {
                return false;
            }
            let dead = next.contains(&arena.nil);
            match claimed {
                Target::Dead => {
                    if !dead {
                        return false;
                    }
                }
                Target::State(j) => {
                    if dead {
                        return false;
                    }
                    match cert.states.get(j) {
                        Some(listed) if *listed == next => {}
                        _ => return false,
                    }
                }
            }
        }
    }

    // Re-check the alignment invariant after the re-derivation: `derive` only
    // ever unions/intersects existing sets, so nothing should have gone out of
    // alignment — but the flag is sticky and consulted, never assumed.
    !arena.poisoned
}

// ---------------------------------------------------------------------------
// Clause-level entry points
// ---------------------------------------------------------------------------

/// A membership literal of the clause, in HYPOTHESIS polarity: the fact that
/// must hold of the subject for the literal to be FALSE.
struct Membership {
    subject: TermId,
    regex: TermId,
    /// `true`: the hypothesis is `subject ∈ regex` (clause literal was
    /// `(not (str.in_re …))`). `false`: the hypothesis is `subject ∉ regex`.
    positive: bool,
}

/// Decompose a clause literal into the membership hypothesis its falsity
/// asserts, or `None` when the literal is not a `str.in_re` over a String term.
fn as_membership(terms: &TermStore, lit: TermId) -> Option<Membership> {
    let (atom, positive) = match terms.get(lit) {
        TermData::Not(inner) => (*inner, true),
        _ => (lit, false),
    };
    let TermData::App(sym, args) = terms.get(atom) else {
        return None;
    };
    if sym.name() != "str.in_re" || args.len() != 2 {
        return None;
    }
    let (subject, regex) = (args[0], args[1]);
    if !matches!(terms.sort(subject), Sort::String) || !matches!(terms.sort(regex), Sort::RegLan) {
        return None;
    }
    Some(Membership {
        subject,
        regex,
        positive,
    })
}

/// Whether the clause carries a group of `str.in_re` literals over one common
/// subject whose jointly-denied intersection is provably EMPTY.
///
/// This is the EXACT precondition of [`validate_regex_intersect_empty`], so the
/// proof classifier in `ay-dpll` can only assign the kind to lemmas strict mode
/// will then accept — no classifier/checker drift. All decision logic lives
/// ONLY in this module.
#[must_use]
pub fn recognize_regex_intersect_empty(terms: &TermStore, clause: &[TermId]) -> bool {
    if clause.is_empty() {
        return false;
    }
    if clause
        .iter()
        .any(|&lit| !matches!(terms.sort(lit), Sort::Bool))
    {
        return false;
    }
    // Group memberships by subject term, preserving clause order so the search
    // is deterministic.
    let mut order: Vec<TermId> = Vec::new();
    let mut groups: HashMap<TermId, Vec<Membership>> = HashMap::default();
    for &lit in clause {
        let Some(m) = as_membership(terms, lit) else {
            continue;
        };
        let subject = m.subject;
        let entry = groups.entry(subject).or_insert_with(|| {
            order.push(subject);
            Vec::new()
        });
        if entry.len() < MAX_CONSTRAINTS {
            entry.push(m);
        }
    }
    for subject in order {
        let Some(group) = groups.get(&subject) else {
            continue;
        };
        if group.is_empty() {
            continue;
        }
        if group_intersection_is_empty(terms, group) {
            return true;
        }
    }
    false
}

/// Decide `⋂ group = ∅` for one subject's membership group: translate, install
/// the verified alphabet partition, search for a reachability argument, then
/// independently validate it. Every step fails closed.
fn group_intersection_is_empty(terms: &TermStore, group: &[Membership]) -> bool {
    let mut tr = Translator::new(terms);
    let mut constraints: Vec<ReId> = Vec::with_capacity(group.len());
    for m in group {
        // A membership this module cannot translate EXACTLY (non-ground leaf,
        // operator not implemented here, absurd bound) is DROPPED, not
        // approximated. Dropping a constraint only ENLARGES the intersection,
        // so proving the remainder empty still proves the whole group empty —
        // and the group's tautology argument only ever needs a subset of the
        // clause. Approximating a language in either direction would not be
        // sound, so there is no such arm.
        let Some(id) = tr.translate(m.regex) else {
            continue;
        };
        let id = if m.positive { id } else { tr.arena.mk_not(id) };
        constraints.push(id);
    }
    if constraints.is_empty() || tr.arena.poisoned {
        return false;
    }
    let mut arena = tr.arena;

    // Install the alphabet partition BEFORE any derivative is taken, so the
    // block-alignment invariant is enforced on every node built from here on.
    let Some(blocks) = compute_blocks(&arena, &constraints) else {
        return false;
    };
    arena.block_starts = blocks.iter().map(|&(lo, _)| lo).collect();
    arena.blocks = blocks;

    let Some(cert) = build_certificate(&mut arena, &constraints) else {
        return false;
    };
    validate_certificate(&mut arena, &constraints, &cert)
}

/// Validate a `TheoryLemmaKind::RegexIntersectEmpty` lemma in strict mode.
pub(crate) fn validate_regex_intersect_empty(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    if clause.is_empty() {
        return Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: "regex_intersect_empty clause must be non-empty".to_string(),
        });
    }
    for &lit in clause {
        if !matches!(terms.sort(lit), Sort::Bool) {
            return Err(ProofCheckError::InvalidTheoryLemma {
                step: step_id,
                reason: format!(
                    "regex_intersect_empty literal has non-Bool sort {:?}; lemma \
                     clauses must be propositional",
                    terms.sort(lit)
                ),
            });
        }
    }
    if recognize_regex_intersect_empty(terms, clause) {
        return Ok(());
    }
    Err(ProofCheckError::InvalidTheoryLemma {
        step: step_id,
        reason: "regex_intersect_empty clause has no str.in_re literal group over a \
                 common subject whose intersection the independent derivative-product \
                 checker proves EMPTY; rejecting in fail-closed mode"
            .to_string(),
    })
}

#[cfg(test)]
#[path = "regex_empty_tests.rs"]
mod regex_empty_tests;
